structure l1 :> l1 =
struct

   structure L1_ParseLrVals = L1_ParseLrValsFun(structure Token = LrParser.Token)
   structure L1Lex = L1LexFun(structure Tokens = L1_ParseLrVals.Tokens)

   structure L1_ParseParser = Join(structure LrParser = LrParser
                                   structure ParserData = L1_ParseLrVals.ParserData
                                   structure Lex = L1Lex)

	fun input prog = let val read = ref 0
	  val size = String.size(prog)
	  in
  	  fn x => let val remaining = size - (!read)
	                val to_read = Int.min(remaining, x)
	                val old_read = !read
	            in
              	read := (!read) + to_read;
	              substring(prog, old_read, to_read)
	            end
	  end


  fun invoke lexstream =
      let fun print_error (s,_,_) =
              TextIO.output(TextIO.stdOut,
                            "Error, line " ^ ", " ^ s ^ "\n")
       in L1_ParseParser.parse(0,lexstream,print_error,())
      end

  fun parse text =
      let val lexer = L1_ParseParser.makeLexer (input text)
          val dummyEOF = L1_ParseLrVals.Tokens.EOF(0,0)
          fun loop lexer =
              let val (result,lexer) = invoke lexer
               in result
              end
       in loop lexer
      end
end
