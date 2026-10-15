(* The JSIL memory lives in Gillian-JS (Js_memory.JSILMemory) *)
include Js_memory.JSILMemory
module ParserAndCompiler = Js2jsil_lib.JS2GIL_ParserAndCompiler
module ExternalSemantics = Semantics.External
