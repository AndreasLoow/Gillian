module SMemory = Js_memory.JSILMemory.Symbolic

module CLI =
  Gillian.Command_line.Make
    (Gillian.General.Init_data.Dummy)
    (Semantics.Concrete)
    (SMemory)
    (Js2jsil_lib.JS2GIL_ParserAndCompiler)
    (Semantics.External)
    (struct
      let runners : Gillian.Bulk.Runner.t list =
        [ (module Test262.Test262_runner); (module CosetteRunner) ]
    end)
    (Gillian.Debugger.Lifter.Gil_lifter.Make
       (SMemory)
       (Js2jsil_lib.JS2GIL_ParserAndCompiler))

let () = CLI.main ()
