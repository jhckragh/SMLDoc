type int = Int.int
functor ParamPatternLexFun(structure Tokens : ParamPattern_TOKENS)=
   struct
    structure UserDeclarations =
      struct
(* -*- sml-lex -*-
 *)
(**
 * lexer of parameter pattern in @params tag of doc comment.
 * @author YAMATODANI Kiyoshi
 * @version $Id: ParamPattern.lex,v 1.2 2007/04/02 09:42:28 katsu Exp $
 *)

type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type pos = int
type lexresult= (svalue, pos) token

type arg = 
     {
       error : (string * int * int) -> unit
     }

val eof = fn _ => Tokens.EOF(0, 0)

end (* end of user routines *)
exception LexError (* raised if illegal leaf action tried *)
structure Internal =
	struct

datatype yyfinstate = N of int
type statedata = {fin : yyfinstate list, trans: string}
(* transition & final state table *)
val tab = let
val s = [ 
 (0, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (1, 
"\003\003\003\003\003\003\003\003\003\014\017\003\014\016\003\003\
\\003\003\003\003\003\003\003\003\003\003\003\003\003\003\003\003\
\\014\003\003\003\003\003\003\003\013\012\011\003\010\003\009\003\
\\003\003\003\003\003\003\003\003\003\003\003\003\003\008\003\003\
\\003\006\006\006\006\006\006\006\006\006\006\006\006\006\006\006\
\\006\006\006\006\006\006\006\006\006\006\006\003\003\003\003\003\
\\003\006\006\006\006\006\006\006\006\006\006\006\006\006\006\006\
\\006\006\006\006\006\006\006\006\006\006\006\005\003\004\003\003\
\\003"
),
 (6, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\007\000\000\000\000\000\000\000\000\
\\007\007\007\007\007\007\007\007\007\007\000\000\000\000\000\000\
\\000\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\
\\007\007\007\007\007\007\007\007\007\007\007\000\000\000\000\007\
\\000\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\
\\007\007\007\007\007\007\007\007\007\007\007\000\000\000\000\000\
\\000"
),
 (14, 
"\000\000\000\000\000\000\000\000\000\015\000\000\015\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\015\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (16, 
"\000\000\000\000\000\000\000\000\000\000\017\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
(0, "")]
fun f x = x 
val s = map f (rev (tl (rev s))) 
exception LexHackingError 
fun look ((j,x)::r, i) = if i = j then x else look(r, i) 
  | look ([], i) = raise LexHackingError
fun g {fin=x, trans=i} = {fin=x, trans=look(s,i)} 
in Vector.fromList(map g 
[{fin = [], trans = 0},
{fin = [(N 2)], trans = 1},
{fin = [(N 2)], trans = 1},
{fin = [(N 28)], trans = 0},
{fin = [(N 15),(N 28)], trans = 0},
{fin = [(N 13),(N 28)], trans = 0},
{fin = [(N 26),(N 28)], trans = 6},
{fin = [(N 26)], trans = 6},
{fin = [(N 9),(N 28)], trans = 0},
{fin = [(N 21),(N 28)], trans = 0},
{fin = [(N 11),(N 28)], trans = 0},
{fin = [(N 23),(N 28)], trans = 0},
{fin = [(N 19),(N 28)], trans = 0},
{fin = [(N 17),(N 28)], trans = 0},
{fin = [(N 2),(N 28)], trans = 14},
{fin = [(N 2)], trans = 14},
{fin = [(N 7),(N 28)], trans = 16},
{fin = [(N 7)], trans = 0}])
end
structure StartStates =
	struct
	datatype yystartstate = STARTSTATE of int

(* start state definitions *)

val INITIAL = STARTSTATE 1;

end
type result = UserDeclarations.lexresult
	exception LexerError (* raised if illegal leaf action tried *)
end

type int = Int.int
fun makeLexer (yyinput: int -> string) =
let	val yygone0:int= ~1
	val yyb = ref "\n" 		(* buffer *)
	val yybl: int ref = ref 1		(*buffer length *)
	val yybufpos: int ref = ref 1		(* location of next character to use *)
	val yygone: int ref = ref yygone0	(* position in file of beginning of buffer *)
	val yydone = ref false		(* eof found yet? *)
	val yybegin: int ref = ref 1		(*Current 'start state' for lexer *)

	val YYBEGIN = fn (Internal.StartStates.STARTSTATE x) =>
		 yybegin := x

fun lex (yyarg as (arg as 
{
  error
} : 
{
  error : (string * int * int) -> unit
})) =
let fun continue() : Internal.result = 
  let fun scan (s,AcceptingLeaves : Internal.yyfinstate list list,l,i0: int) =
	let fun action (i: int,nil) = raise LexError
	| action (i,nil::l) = action (i-1,l)
	| action (i,(node::acts)::l) =
		case node of
		    Internal.N yyk => 
			(let fun yymktext() = String.substring(!yyb,i0,i-i0)
			     val yypos: int = i0+ !yygone
			fun REJECT() = action(i,acts::l)
			open UserDeclarations Internal.StartStates
 in (yybufpos := i; case yyk of 

			(* Application actions *)

  11 => (Tokens.COMMA(yypos,yypos+1))
| 13 => (Tokens.LBRACE(yypos,yypos+1))
| 15 => (Tokens.RBRACE(yypos,yypos+1))
| 17 => (Tokens.LPAREN(yypos,yypos+1))
| 19 => (Tokens.RPAREN(yypos,yypos+1))
| 2 => (continue())
| 21 => (Tokens.DOT(yypos,yypos+1))
| 23 => (Tokens.ASTERISK(yypos,yypos+1))
| 26 => let val yytext=yymktext() in Tokens.ID(yytext, yypos, yypos+size yytext) end
| 28 => let val yytext=yymktext() in error ("illegal token(" ^ yytext ^ ")", yypos, yypos+1);
                    continue() end
| 7 => (continue())
| 9 => (Tokens.EQUALOP(yypos,yypos+1))
| _ => raise Internal.LexerError

		) end )

	val {fin,trans} = Vector.sub (Internal.tab, s)
	val NewAcceptingLeaves = fin::AcceptingLeaves
	in if l = !yybl then
	     if trans = #trans(Vector.sub(Internal.tab,0))
	       then action(l,NewAcceptingLeaves
) else	    let val newchars= if !yydone then "" else yyinput 1024
	    in if (String.size newchars)=0
		  then (yydone := true;
		        if (l=i0) then UserDeclarations.eof yyarg
		                  else action(l,NewAcceptingLeaves))
		  else (if i0=l then yyb := newchars
		     else yyb := String.substring(!yyb,i0,l-i0)^newchars;
		     yygone := !yygone+i0;
		     yybl := String.size (!yyb);
		     scan (s,AcceptingLeaves,l-i0,0))
	    end
	  else let val NewChar = Char.ord (CharVector.sub (!yyb,l))
		val NewChar = if NewChar<128 then NewChar else 128
		val NewState = Char.ord (CharVector.sub (trans,NewChar))
		in if NewState=0 then action(l,NewAcceptingLeaves)
		else scan(NewState,NewAcceptingLeaves,l+1,i0)
	end
	end
(*
	val start= if String.substring(!yyb,!yybufpos-1,1)="\n"
then !yybegin+1 else !yybegin
*)
	in scan(!yybegin (* start *),nil,!yybufpos,!yybufpos)
    end
in continue end
  in lex
  end
end
