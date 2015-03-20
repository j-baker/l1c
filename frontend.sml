val _ = PolyML.print_depth 0;

load"printerLib";
load"parsingLib";
load"compilerTheory";
load"bossLib";
load"boolLib";
load"intSimps";
open HolKernel compilerTheory bossLib boolLib parsingLib printerLib CommandLine;

fun snd (a, b) = b;

fun main () = let val args = CommandLine.arguments()
              in
                  if length(args) = 0 orelse length(args) > 1 then
                      (print("Must provide one input file as a command line argument.\n"); OS.Process.exit(OS.Process.failure))
                  else (let val filename = hd args
                           val file = TextIO.openIn filename
                           val file_contents = TextIO.inputAll file
                           val _ = TextIO.closeIn file
                           val parsed = parsingLib.parse file_contents
                           val compiled = snd (dest_eq (snd (dest_thm (SIMP_RULE intSimps.int_ss [] (EVAL ``compile ^parsed``)))))
               in (printerLib.print_prog (printerLib.get_instructions compiled); OS.Process.exit(OS.Process.success)) end) end;

PolyML.export("l1c", main);
