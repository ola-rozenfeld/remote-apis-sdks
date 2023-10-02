package client

import (
	"context"
	"fmt"
	"io"
	"os"
	"os/user"
	"sort"
	"strconv"
	"strings"
	"sync"

	bazelbeppb "github.com/bazelbuild/remote-apis-sdks/go/api/bazelbep/build_event_stream"
	bazelfdpb "github.com/bazelbuild/remote-apis-sdks/go/api/bazelbep/failure_details"
	beppb "github.com/bazelbuild/remote-apis-sdks/go/api/buildeventstream/build_event_stream"
	"github.com/bazelbuild/remote-apis-sdks/go/pkg/command"
	"github.com/bazelbuild/remote-apis-sdks/go/pkg/digest"
	log "github.com/golang/glog"
	besgrpc "google.golang.org/genproto/googleapis/devtools/build/v1"
	bespb "google.golang.org/genproto/googleapis/devtools/build/v1"
	anypb "google.golang.org/protobuf/types/known/anypb"
	tspb "google.golang.org/protobuf/types/known/timestamppb"
	"google.golang.org/protobuf/types/known/wrapperspb"
)

const (
	ReplaceLine = "\r\033[1A\033[K"
	GreenColor  = "\033[32m"
	RedColor    = "\033[31m\033[1m"
	YellowColor = "\033[33m"
	NoColor     = "\033[0m"
)

type BuildMetadata struct {
	InvocationID string
	BuildID      string
	ToolName     string
	ToolVersion  string
	Targets      []string
	// Parsed options, environment, etc.
	Options map[string]string
}

func (m *BuildMetadata) OptionValues() []string {
	var result []string
	for k, v := range m.Options {
		result = append(result, fmt.Sprintf("%s=%s", k, v))
	}
	sort.Strings(result)
	return result
}

// BuildResult represents the options for a finished build.
// It should be kept in sync with the BES BuildStatus.Result enum:
// googleapis/google/devtools/build/v1/build_status.proto
type BuildResult int

const (
	// UnspecifiedBuildResult is an invalid value, should not be used.
	UnspecifiedBuildResult BuildResult = iota

	// Build was successful and tests (if requested) all pass.
	CommandSucceededBuildResult

	// Build error and/or test failure.
	CommandFailedBuildResult

	// Unable to obtain a result due to input provided by the user.
	UserErrorBuildResult

	// Unable to obtain a result due to a failure within the build system.
	SystemErrorBuildResult

	// Build required too many resources, such as build tool RAM.
	ResourceExhaustedBuildResult

	// An invocation attempt time exceeded its deadline.
	InvocationDeadlineExceededBuildResult

	// The build was cancelled by a call to CancelBuild.
	CancelledBuildResult

	// Build request time exceeded the request_deadline.
	RequestDeadlineExceededBuildResult
)

var buildResults = [...]string{
	"UnspecifiedBuildResult",
	"CommandSucceededBuildResult",
	"CommandFailedBuildResult",
	"UserErrorBuildResult",
	"SystemErrorBuildResult",
	"ResourceExhaustedBuildResult",
	"InvocationDeadlineExceededBuildResult",
	"RequestDeadlineExceededBuildResult",
	"CancelledBuildResult",
}

// IsOk returns whether the result indicates a successful build.
func (s BuildResult) IsOk() bool {
	return s == CommandSucceededBuildResult
}

// IsOk returns whether the result indicates a successful build.
func (s BuildResult) ToBESBuildStatusResult() bespb.BuildStatus_Result {
	return bespb.BuildStatus_Result(s)
}

func (s BuildResult) String() string {
	if UnspecifiedBuildResult <= s && s <= RequestDeadlineExceededBuildResult {
		return buildResults[s]
	}
	return fmt.Sprintf("InvalidBuildResult(%d)", s)
}

// Encapsulating the underlying BES proto.
type BuildStatus struct {
	Result   BuildResult
	ExitCode int32
	Error    error
}

func (s *BuildStatus) ToBESBuildStatus() *bespb.BuildStatus {
	return &bespb.BuildStatus{
		Result:            s.Result.ToBESBuildStatusResult(),
		BuildToolExitCode: &wrapperspb.Int32Value{Value: s.ExitCode},
		//		ErrorMessage:      errMsg,
	}
}

func (c *Client) NewBuildEventStream(ctx context.Context, meta *BuildMetadata) (*BuildEventStream, error) {
	if c.bes == nil {
		return nil, fmt.Errorf("BESService value not set")
	}
	host := strings.Split(c.BESConnection.Target(), ":")[0]
	return &BuildEventStream{
		client:    c,
		Metadata:  meta,
		seqNumber: 0,
		streamID: &bespb.StreamId{
			BuildId:      meta.BuildID,
			InvocationId: meta.InvocationID,
			Component:    besgrpc.StreamId_TOOL,
		},
		finished:  false,
		uriPrefix: fmt.Sprintf("bytestream://%s/blobs/", host),
	}, nil
}

// Context is the long lived object for sending Build Events.
type BuildEventStream struct {
	Metadata      *BuildMetadata
	client        *Client
	besStream     besgrpc.PublishBuildEvent_PublishBuildToolEventStreamClient
	seqNumber     int64
	streamID      *bespb.StreamId
	chAck         chan struct{}
	chEvents      chan *bespb.PublishBuildToolEventStreamRequest
	chEventsDone  chan struct{}
	err           error
	finished      bool
	uriPrefix     string
	progressCount int32
	mu            sync.RWMutex
}

// Start sends the relevant lifecycle events to BES.
func (s *BuildEventStream) Start(ctx context.Context) error {
	if s.seqNumber > 0 {
		return fmt.Errorf("the build event stream is already started")
	}
	s.seqNumber = 1
	now := tspb.Now()
	req := &bespb.PublishLifecycleEventRequest{
		ServiceLevel: bespb.PublishLifecycleEventRequest_INTERACTIVE,
		BuildEvent: &bespb.OrderedBuildEvent{
			StreamId:       s.streamID,
			SequenceNumber: 1,
			Event: &bespb.BuildEvent{
				EventTime: now,
				Event: &bespb.BuildEvent_BuildEnqueued_{
					BuildEnqueued: &bespb.BuildEvent_BuildEnqueued{},
				},
			},
		},
	}
	_, err := s.client.PublishLifecycleEvent(ctx, req)
	if err != nil {
		return err
	}
	req = &bespb.PublishLifecycleEventRequest{
		ServiceLevel: bespb.PublishLifecycleEventRequest_INTERACTIVE,
		BuildEvent: &bespb.OrderedBuildEvent{
			StreamId:       s.streamID,
			SequenceNumber: 1,
			Event: &bespb.BuildEvent{
				EventTime: now,
				Event: &bespb.BuildEvent_InvocationAttemptStarted_{
					InvocationAttemptStarted: &bespb.BuildEvent_InvocationAttemptStarted{
						AttemptNumber: 1,
					},
				},
			},
		},
	}
	_, err = s.client.PublishLifecycleEvent(ctx, req)
	if err != nil {
		return err
	}
	s.besStream, err = s.client.PublishBuildToolEventStream(ctx)
	if err != nil {
		return err
	}
	s.chAck = make(chan struct{})
	go func() {
		for {
			_, err := s.besStream.Recv()
			if err != nil {
				if err != io.EOF {
					log.Errorf("%s> error in BES stream: %v", s.Metadata.InvocationID, err)
				}
				close(s.chAck)
				return
			}
			// TODO(ola): implement proper error handling (sequence) and retries.
		}
	}()
	s.chEvents = make(chan *bespb.PublishBuildToolEventStreamRequest)
	s.chEventsDone = make(chan struct{})
	go func() {
		for req := range s.chEvents {
			if s.err != nil {
				continue
			}
			if err := s.besStream.Send(req); err != nil {
				s.mu.Lock()
				s.err = err
				s.mu.Unlock()
			}
		}
		close(s.chEventsDone)
	}()
	err = s.sendBazelEvent(&bazelbeppb.BuildEvent{
		Id: &bazelbeppb.BuildEventId{
			Id: &bazelbeppb.BuildEventId_Started{
				Started: &bazelbeppb.BuildEventId_BuildStartedId{},
			},
		},
		Children: []*bazelbeppb.BuildEventId{
			&bazelbeppb.BuildEventId{
				Id: &bazelbeppb.BuildEventId_OptionsParsed{
					OptionsParsed: &bazelbeppb.BuildEventId_OptionsParsedId{},
				},
			},
			&bazelbeppb.BuildEventId{
				Id: &bazelbeppb.BuildEventId_WorkspaceStatus{
					WorkspaceStatus: &bazelbeppb.BuildEventId_WorkspaceStatusId{},
				},
			},
			&bazelbeppb.BuildEventId{
				Id: &bazelbeppb.BuildEventId_Pattern{
					Pattern: &bazelbeppb.BuildEventId_PatternExpandedId{
						Pattern: s.Metadata.Targets,
					},
				},
			},
			&bazelbeppb.BuildEventId{
				Id: &bazelbeppb.BuildEventId_BuildFinished{
					BuildFinished: &bazelbeppb.BuildEventId_BuildFinishedId{},
				},
			},
		},
		Payload: &bazelbeppb.BuildEvent_Started{
			Started: &bazelbeppb.BuildStarted{
				Uuid:             s.Metadata.BuildID,
				StartTime:        now,
				BuildToolVersion: s.Metadata.ToolVersion,
			},
		},
	})
	if err != nil {
		return err
	}
	err = s.sendBazelEvent(&bazelbeppb.BuildEvent{
		Id: &bazelbeppb.BuildEventId{
			Id: &bazelbeppb.BuildEventId_OptionsParsed{
				OptionsParsed: &bazelbeppb.BuildEventId_OptionsParsedId{},
			},
		},
		Payload: &bazelbeppb.BuildEvent_OptionsParsed{
			OptionsParsed: &bazelbeppb.OptionsParsed{
				CmdLine: s.Metadata.OptionValues(),
			},
		},
	})
	if err != nil {
		return err
	}
	hostName, err := os.Hostname()
	if err != nil {
		return err
	}
	userName, err := user.Current()
	if err != nil {
		return err
	}
	err = s.sendBazelEvent(&bazelbeppb.BuildEvent{
		Id: &bazelbeppb.BuildEventId{
			Id: &bazelbeppb.BuildEventId_WorkspaceStatus{
				WorkspaceStatus: &bazelbeppb.BuildEventId_WorkspaceStatusId{},
			},
		},
		Payload: &bazelbeppb.BuildEvent_WorkspaceStatus{
			WorkspaceStatus: &bazelbeppb.WorkspaceStatus{
				Item: []*bazelbeppb.WorkspaceStatus_Item{
					&bazelbeppb.WorkspaceStatus_Item{
						Key:   "BUILD_HOST",
						Value: hostName,
					},
					&bazelbeppb.WorkspaceStatus_Item{
						Key:   "BUILD_USER",
						Value: userName.Username,
					},
				},
			},
		},
	})
	if err != nil {
		return err
	}
	if err := s.SendConsole(fmt.Sprintf("%sINFO:%s Invocation ID: %s\n", GreenColor, NoColor, s.Metadata.InvocationID), ""); err != nil {
		return err
	}
	if err := s.SendConsole(fmt.Sprintf("%sINFO:%s Streaming build results to: https://%s/invocation/%s\n", GreenColor, NoColor, s.client.BESConnection.Target(), s.Metadata.InvocationID), ""); err != nil {
		return err
	}
	err = s.sendBazelEvent(&bazelbeppb.BuildEvent{
		Id: &bazelbeppb.BuildEventId{
			Id: &bazelbeppb.BuildEventId_Pattern{
				Pattern: &bazelbeppb.BuildEventId_PatternExpandedId{
					Pattern: s.Metadata.Targets,
				},
			},
		},
	})
	if err != nil {
		return err
	}
	// The point of configurations is mnemonics for different action types.
	// TODO(ola): compute these better.
	return s.sendBazelEvent(&bazelbeppb.BuildEvent{
		Id: &bazelbeppb.BuildEventId{
			Id: &bazelbeppb.BuildEventId_Configuration{
				Configuration: &bazelbeppb.BuildEventId_ConfigurationId{
					Id: "none",
				},
			},
		},
		Payload: &bazelbeppb.BuildEvent_Configuration{
			Configuration: &bazelbeppb.Configuration{
				// TODO: compute this better.
				Mnemonic:     "darwin_arm64-fastbuild",
				PlatformName: "darwin_arm64",
				Cpu:          "darwin_arm64",
			},
		},
	})
}

// Finish sends the relevant lifecycle events to BES.
// TODO(ola): accept exit code name, because it is tool dependent.
func (s *BuildEventStream) Finish(ctx context.Context, st *BuildStatus) error {
	status := st.ToBESBuildStatus()
	if s.finished {
		return fmt.Errorf("the build event stream is already finished")
	}
	now := tspb.Now()
	var code int32
	if status.BuildToolExitCode != nil {
		code = status.BuildToolExitCode.Value
	}
	success := status.Result == bespb.BuildStatus_COMMAND_SUCCEEDED
	// TODO: this doesn't have to be red or green, it can be interrupted or whatever.
	msg := fmt.Sprintf("%s%sINFO:%s Build completed successfully\n", ReplaceLine, GreenColor, NoColor)
	if !success {
		msg = fmt.Sprintf("%sFAILED:%s Build did NOT complete successfully\n", RedColor, NoColor)
	}
	if err := s.SendConsole("", msg); err != nil {
		return err
	}
	err := s.sendBazelEvent(&bazelbeppb.BuildEvent{
		Id: &bazelbeppb.BuildEventId{
			Id: &bazelbeppb.BuildEventId_BuildFinished{
				BuildFinished: &bazelbeppb.BuildEventId_BuildFinishedId{},
			},
		},
		Payload: &bazelbeppb.BuildEvent_Finished{
			Finished: &bazelbeppb.BuildFinished{
				FinishTime:     now,
				OverallSuccess: success,
				ExitCode: &bazelbeppb.BuildFinished_ExitCode{
					Name: status.Result.String(),
					Code: code,
				},
			},
		},
	})
	if err != nil {
		return err
	}
	s.mu.Lock()
	s.finished = true
	s.mu.Unlock()
	close(s.chEvents)
	<-s.chEventsDone // wait until all pending events are written.
	if err = s.besStream.CloseSend(); err != nil {
		return err
	}
	<-s.chAck
	req := &bespb.PublishLifecycleEventRequest{
		ServiceLevel: bespb.PublishLifecycleEventRequest_INTERACTIVE,
		BuildEvent: &bespb.OrderedBuildEvent{
			StreamId:       s.streamID,
			SequenceNumber: 2,
			Event: &bespb.BuildEvent{
				EventTime: now,
				Event: &bespb.BuildEvent_InvocationAttemptFinished_{
					InvocationAttemptFinished: &bespb.BuildEvent_InvocationAttemptFinished{
						InvocationStatus: status,
					},
				},
			},
		},
	}
	_, err = s.client.PublishLifecycleEvent(ctx, req)
	if err != nil {
		return err
	}
	s.streamID.InvocationId = ""
	req = &bespb.PublishLifecycleEventRequest{
		ServiceLevel: bespb.PublishLifecycleEventRequest_INTERACTIVE,
		BuildEvent: &bespb.OrderedBuildEvent{
			StreamId:       s.streamID,
			SequenceNumber: 2,
			Event: &bespb.BuildEvent{
				EventTime: now,
				Event: &bespb.BuildEvent_BuildFinished_{
					BuildFinished: &bespb.BuildEvent_BuildFinished{
						Status: status,
					},
				},
			},
		},
	}
	_, err = s.client.PublishLifecycleEvent(ctx, req)
	return err
}

func (s *BuildEventStream) sendBazelEvent(event *bazelbeppb.BuildEvent) error {
	s.mu.Lock()
	defer s.mu.Unlock()
	if s.err != nil {
		return s.err
	}
	if s.seqNumber == 0 {
		return fmt.Errorf("the build event stream is not started")
	}
	if s.finished {
		return fmt.Errorf("the build event stream is already finished")
	}
	any, err := anypb.New(event)
	if err != nil {
		return err
	}
	req := &bespb.PublishBuildToolEventStreamRequest{
		OrderedBuildEvent: &bespb.OrderedBuildEvent{
			StreamId:       s.streamID,
			SequenceNumber: s.seqNumber,
			Event: &bespb.BuildEvent{
				EventTime: tspb.Now(),
				Event: &bespb.BuildEvent_BazelEvent{
					BazelEvent: any,
				},
			},
		},
	}
	s.seqNumber++
	s.chEvents <- req
	return nil
}

func (s *BuildEventStream) SendConsole(stdout string, stderr string) error {
	s.mu.Lock()
	ev := &bazelbeppb.BuildEvent{
		Id: &bazelbeppb.BuildEventId{
			Id: &bazelbeppb.BuildEventId_Progress{
				Progress: &bazelbeppb.BuildEventId_ProgressId{
					OpaqueCount: s.progressCount,
				},
			},
		},
		Payload: &bazelbeppb.BuildEvent_Progress{
			Progress: &bazelbeppb.Progress{
				Stdout: stdout,
				Stderr: stderr,
			},
		},
	}
	s.progressCount++
	s.mu.Unlock()
	return s.sendBazelEvent(ev)
}

func (s *BuildEventStream) CommandStarted(cmd *command.Command) error {
	out := cmd.GetPrimaryOutput()
	return s.ActionStarted(&beppb.ActionStarted{
		ConsolePrintout: fmt.Sprintf("Building %s...\n", out),
		PrimaryOutput:   out,
	})
}

// TODO: decide what to do about stdout/err streams. Add the raw ones to Metadata is an option; or support digest inlining
// on the server.
func (s *BuildEventStream) CommandFinished(cmd *command.Command, res *command.Result, meta *command.Metadata) error {
	ac := &beppb.ActionCompleted{
		ActionDigest:      meta.ActionDigest.String(),
		Result:            command.ResultToProto(res),
		PrimaryOutput:     cmd.GetPrimaryOutput(),
		StdoutDigest:      meta.StdoutDigest.String(),
		StderrDigest:      meta.StderrDigest.String(),
		Stdout:            meta.StdoutRaw,
		Stderr:            meta.StderrRaw,
		OutputFileDigests: make(map[string]string),
	}
	for name, d := range meta.OutputFileDigests {
		ac.OutputFileDigests[name] = d.String()
	}
	return s.ActionCompleted(ac)
}

func (s *BuildEventStream) ActionStarted(ac *beppb.ActionStarted) error {
	label := "//" + ac.PrimaryOutput + ":build"
	if err := s.SendConsole(ReplaceLine+ac.ConsolePrintout, ""); err != nil {
		return err
	}
	return s.sendBazelEvent(&bazelbeppb.BuildEvent{
		Id: &bazelbeppb.BuildEventId{
			Id: &bazelbeppb.BuildEventId_TargetConfigured{
				TargetConfigured: &bazelbeppb.BuildEventId_TargetConfiguredId{
					Label: label,
				},
			},
		},
		Children: []*bazelbeppb.BuildEventId{
			&bazelbeppb.BuildEventId{
				Id: &bazelbeppb.BuildEventId_TargetCompleted{
					TargetCompleted: &bazelbeppb.BuildEventId_TargetCompletedId{
						Label: label,
						Configuration: &bazelbeppb.BuildEventId_ConfigurationId{
							Id: "none",
						},
					},
				},
			},
		},
	})
}

func (s *BuildEventStream) ActionCompleted(ac *beppb.ActionCompleted) error {
	success := command.ResultFromProto(ac.Result).IsOk()
	nsfId := strconv.Itoa(int(s.seqNumber))
	// Action outputs.
	nsf := &bazelbeppb.NamedSetOfFiles{}
	for name, digest := range ac.OutputFileDigests {
		f := &bazelbeppb.File{
			Name: name,
			File: &bazelbeppb.File_Uri{Uri: s.uriPrefix + digest},
		}
		nsf.Files = append(nsf.Files, f)
	}
	err := s.sendBazelEvent(&bazelbeppb.BuildEvent{
		Id: &bazelbeppb.BuildEventId{
			Id: &bazelbeppb.BuildEventId_NamedSet{
				NamedSet: &bazelbeppb.BuildEventId_NamedSetOfFilesId{Id: nsfId},
			},
		},
		Payload: &bazelbeppb.BuildEvent_NamedSetOfFiles{NamedSetOfFiles: nsf},
	})
	if err != nil {
		return err
	}
	label := "//" + ac.PrimaryOutput + ":build"
	var children []*bazelbeppb.BuildEventId
	if !success {
		children = append(children, &bazelbeppb.BuildEventId{
			Id: &bazelbeppb.BuildEventId_ActionCompleted{
				ActionCompleted: &bazelbeppb.BuildEventId_ActionCompletedId{
					Label: label,
					Configuration: &bazelbeppb.BuildEventId_ConfigurationId{
						Id: "none",
					},
				},
			},
		})
	}
	var fd *bazelfdpb.FailureDetail
	if !success {
		fd = &bazelfdpb.FailureDetail{Message: ""}
	}
	err = s.sendBazelEvent(&bazelbeppb.BuildEvent{
		Id: &bazelbeppb.BuildEventId{
			Id: &bazelbeppb.BuildEventId_TargetCompleted{
				TargetCompleted: &bazelbeppb.BuildEventId_TargetCompletedId{
					Label: label,
					Configuration: &bazelbeppb.BuildEventId_ConfigurationId{
						Id: "none",
					},
				},
			},
		},
		Children: children,
		Payload: &bazelbeppb.BuildEvent_Completed{
			Completed: &bazelbeppb.TargetComplete{
				Success: success,
				OutputGroup: []*bazelbeppb.OutputGroup{&bazelbeppb.OutputGroup{
					Name:     "default",
					FileSets: []*bazelbeppb.BuildEventId_NamedSetOfFilesId{&bazelbeppb.BuildEventId_NamedSetOfFilesId{Id: nsfId}},
				}},
				FailureDetail: fd,
			},
		},
	})
	if err != nil {
		return err
	}
	if ac.Stdout != "" {
		if err := s.SendConsole(fmt.Sprintf("From building %s:\n%s\n", ac.PrimaryOutput, ac.Stdout), ""); err != nil {
			return err
		}
	}
	if ac.Stderr != "" {
		prefix := ""
		if !success {
			prefix = fmt.Sprintf("%sERROR:%s ", RedColor, NoColor)
		}
		if err := s.SendConsole("", fmt.Sprintf("%sFrom building %s:\n%s\n", prefix, ac.PrimaryOutput, ac.Stderr)); err != nil {
			return err
		}
	}
	if !success {
		err = s.sendBazelEvent(&bazelbeppb.BuildEvent{
			Id: &bazelbeppb.BuildEventId{
				Id: &bazelbeppb.BuildEventId_ActionCompleted{
					ActionCompleted: &bazelbeppb.BuildEventId_ActionCompletedId{
						Label: label,
						Configuration: &bazelbeppb.BuildEventId_ConfigurationId{
							Id: "none",
						},
					},
				},
			},
			Payload: &bazelbeppb.BuildEvent_Action{
				Action: &bazelbeppb.ActionExecuted{
					ExitCode: ac.Result.ExitCode,
					Stderr: &bazelbeppb.File{
						Name: "stderr",
						File: &bazelbeppb.File_Uri{Uri: s.uriPrefix + ac.StderrDigest},
					},
					Type: "todoGetType",
				},
			},
		})
		if err != nil {
			return err
		}
	}
	return nil
}

func (s *BuildEventStream) BuildLogs(logs map[string]digest.Digest) error {
	return nil
}

func (s *BuildEventStream) BuildMetrics(m *beppb.BuildMetrics) error {
	return nil
}
