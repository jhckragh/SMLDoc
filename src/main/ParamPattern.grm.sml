functor ParamPatternLrValsFun(structure Token : TOKEN)
 : sig structure ParserData : PARSER_DATA
       structure Tokens : ParamPattern_TOKENS
   end
 = 
struct
structure ParserData=
struct
structure Header = 
struct
(**
 * grammar of parameter pattern in @params tag of doc comment.
 * @author YAMATODANI Kiyoshi
 * @copyright 2010, Tohoku University.
 * @version $Id: ParamPattern.grm,v 1.2 2007/04/02 09:42:28 katsu Exp $
 *)

open DocComment

  
end
structure LrTable = Token.LrTable
structure Token = Token
local open LrTable in 
val table=let val actionRows =
"\
\\001\000\001\000\000\000\000\000\
\\001\000\002\000\007\000\008\000\006\000\009\000\005\000\000\000\
\\001\000\002\000\007\000\008\000\006\000\009\000\005\000\011\000\010\000\000\000\
\\001\000\002\000\014\000\000\000\
\\001\000\002\000\014\000\010\000\013\000\000\000\
\\001\000\007\000\016\000\011\000\015\000\000\000\
\\001\000\010\000\017\000\000\000\
\\001\000\011\000\024\000\000\000\
\\028\000\000\000\
\\029\000\000\000\
\\030\000\000\000\
\\031\000\000\000\
\\032\000\000\000\
\\033\000\000\000\
\\034\000\000\000\
\\035\000\000\000\
\\036\000\004\000\019\000\000\000\
\\037\000\000\000\
\\038\000\007\000\018\000\000\000\
\\039\000\007\000\025\000\000\000\
\\040\000\000\000\
\\041\000\002\000\007\000\008\000\006\000\009\000\005\000\000\000\
\\042\000\000\000\
\"
val actionRowNumbers =
"\001\000\021\000\010\000\002\000\
\\004\000\008\000\022\000\005\000\
\\011\000\006\000\018\000\013\000\
\\016\000\009\000\001\000\014\000\
\\003\000\001\000\007\000\019\000\
\\017\000\015\000\012\000\001\000\
\\020\000\000\000"
val gotoT =
"\
\\001\000\002\000\002\000\001\000\006\000\025\000\000\000\
\\001\000\002\000\002\000\001\000\006\000\006\000\000\000\
\\000\000\
\\001\000\002\000\002\000\007\000\000\000\
\\003\000\010\000\004\000\009\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\001\000\002\000\002\000\019\000\005\000\018\000\000\000\
\\000\000\
\\003\000\010\000\004\000\020\000\000\000\
\\001\000\002\000\002\000\021\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\001\000\002\000\002\000\019\000\005\000\024\000\000\000\
\\000\000\
\\000\000\
\"
val numstates = 26
val numrules = 15
val s = ref "" and index = ref 0
val string_to_int = fn () => 
let val i = !index
in index := i+2; Char.ord(String.sub(!s,i)) + Char.ord(String.sub(!s,i+1)) * 256
end
val string_to_list = fn s' =>
    let val len = String.size s'
        fun f () =
           if !index < len then string_to_int() :: f()
           else nil
   in index := 0; s := s'; f ()
   end
val string_to_pairlist = fn (conv_key,conv_entry) =>
     let fun f () =
         case string_to_int()
         of 0 => EMPTY
          | n => PAIR(conv_key (n-1),conv_entry (string_to_int()),f())
     in f
     end
val string_to_pairlist_default = fn (conv_key,conv_entry) =>
    let val conv_row = string_to_pairlist(conv_key,conv_entry)
    in fn () =>
       let val default = conv_entry(string_to_int())
           val row = conv_row()
       in (row,default)
       end
   end
val string_to_table = fn (convert_row,s') =>
    let val len = String.size s'
        fun f ()=
           if !index < len then convert_row() :: f()
           else nil
     in (s := s'; index := 0; f ())
     end
local
  val memo = Array.array(numstates+numrules,ERROR)
  val _ =let fun g i=(Array.update(memo,i,REDUCE(i-numstates)); g(i+1))
       fun f i =
            if i=numstates then g i
            else (Array.update(memo,i,SHIFT (STATE i)); f (i+1))
          in f 0 handle Subscript => ()
          end
in
val entry_to_action = fn 0 => ACCEPT | 1 => ERROR | j => Array.sub(memo,(j-2))
end
val gotoT=Array.fromList(string_to_table(string_to_pairlist(NT,STATE),gotoT))
val actionRows=string_to_table(string_to_pairlist_default(T,entry_to_action),actionRows)
val actionRowNumbers = string_to_list actionRowNumbers
val actionT = let val actionRowLookUp=
let val a=Array.fromList(actionRows) in fn i=>Array.sub(a,i) end
in Array.fromList(map actionRowLookUp actionRowNumbers)
end
in LrTable.mkLrTable {actions=actionT,gotos=gotoT,numRules=numrules,
numStates=numstates,initialState=STATE 0}
end
end
local open Header in
type pos = int
type arg = unit
structure MlyValue = 
struct
datatype svalue = VOID | ntVOID of unit ->  unit
 | ID of unit ->  (string) | apats of unit ->  (paramPattern list)
 | pat_list of unit ->  (paramPattern list)
 | plabels of unit ->  ( ( (string * paramPattern) list ) )
 | plabel of unit ->  ( ( string * paramPattern ) )
 | apat of unit ->  (paramPattern) | id of unit ->  (string)
end
type svalue = MlyValue.svalue
type result = paramPattern list
end
structure EC=
struct
open LrTable
infix 5 $$
fun x $$ y = y::x
val is_keyword =
fn _ => false
val preferred_change : (term list * term list) list = 
nil
val noShift = 
fn (T 0) => true | _ => false
val showTerminal =
fn (T 0) => "EOF"
  | (T 1) => "ID"
  | (T 2) => "DOT"
  | (T 3) => "EQUALOP"
  | (T 4) => "ASTERISK"
  | (T 5) => "COLON"
  | (T 6) => "COMMA"
  | (T 7) => "LBRACE"
  | (T 8) => "LPAREN"
  | (T 9) => "RBRACE"
  | (T 10) => "RPAREN"
  | _ => "bogus-term"
local open Header in
val errtermvalue=
fn (T 1) => MlyValue.ID(fn () => ("BOGUS")) | 
_ => MlyValue.VOID
end
val terms : term list = nil
 $$ (T 10) $$ (T 9) $$ (T 8) $$ (T 7) $$ (T 6) $$ (T 5) $$ (T 4) $$ 
(T 3) $$ (T 2) $$ (T 0)end
structure Actions =
struct 
type int = Int.int
exception mlyAction of int
local open Header in
val actions = 
fn (i392:int,defaultPos,stack,
    (()):arg) =>
case (i392,stack)
of  ( 0, ( ( _, ( MlyValue.ID ID1, ID1left, ID1right)) :: rest671)) =>
 let val  result = MlyValue.id (fn _ => let val  (ID as ID1) = ID1 ()
 in (ID)
end)
 in ( LrTable.NT 0, ( result, ID1left, ID1right), rest671)
end
|  ( 1, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.apat apat1, _
, _)) :: ( _, ( _, LPAREN1left, _)) :: rest671)) => let val  result = 
MlyValue.apat (fn _ => let val  (apat as apat1) = apat1 ()
 in (apat)
end)
 in ( LrTable.NT 1, ( result, LPAREN1left, RPAREN1right), rest671)
end
|  ( 2, ( ( _, ( MlyValue.id id1, id1left, id1right)) :: rest671)) =>
 let val  result = MlyValue.apat (fn _ => let val  (id as id1) = id1
 ()
 in (IDParamPat id)
end)
 in ( LrTable.NT 1, ( result, id1left, id1right), rest671)
end
|  ( 3, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( _, LPAREN1left, _)) ::
 rest671)) => let val  result = MlyValue.apat (fn _ => (
TupleParamPat([])))
 in ( LrTable.NT 1, ( result, LPAREN1left, RPAREN1right), rest671)
end
|  ( 4, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.pat_list 
pat_list1, _, _)) :: _ :: ( _, ( MlyValue.apat apat1, _, _)) :: ( _, (
 _, LPAREN1left, _)) :: rest671)) => let val  result = MlyValue.apat
 (fn _ => let val  (apat as apat1) = apat1 ()
 val  (pat_list as pat_list1) = pat_list1 ()
 in (TupleParamPat(apat :: pat_list))
end)
 in ( LrTable.NT 1, ( result, LPAREN1left, RPAREN1right), rest671)
end
|  ( 5, ( ( _, ( _, _, RBRACE1right)) :: ( _, ( _, LBRACE1left, _)) ::
 rest671)) => let val  result = MlyValue.apat (fn _ => (
RecordParamPat([])))
 in ( LrTable.NT 1, ( result, LBRACE1left, RBRACE1right), rest671)
end
|  ( 6, ( ( _, ( _, _, RBRACE1right)) :: ( _, ( MlyValue.plabels 
plabels1, _, _)) :: ( _, ( _, LBRACE1left, _)) :: rest671)) => let
 val  result = MlyValue.apat (fn _ => let val  (plabels as plabels1) =
 plabels1 ()
 in (RecordParamPat plabels)
end)
 in ( LrTable.NT 1, ( result, LBRACE1left, RBRACE1right), rest671)
end
|  ( 7, ( ( _, ( MlyValue.apat apat1, _, apat1right)) :: _ :: ( _, ( 
MlyValue.ID ID1, ID1left, _)) :: rest671)) => let val  result = 
MlyValue.plabel (fn _ => let val  (ID as ID1) = ID1 ()
 val  (apat as apat1) = apat1 ()
 in ((ID,apat))
end)
 in ( LrTable.NT 2, ( result, ID1left, apat1right), rest671)
end
|  ( 8, ( ( _, ( MlyValue.ID ID1, ID1left, ID1right)) :: rest671)) =>
 let val  result = MlyValue.plabel (fn _ => let val  (ID as ID1) = ID1
 ()
 in (ID, IDParamPat ID)
end)
 in ( LrTable.NT 2, ( result, ID1left, ID1right), rest671)
end
|  ( 9, ( ( _, ( MlyValue.plabels plabels1, _, plabels1right)) :: _ ::
 ( _, ( MlyValue.plabel plabel1, plabel1left, _)) :: rest671)) => let
 val  result = MlyValue.plabels (fn _ => let val  (plabel as plabel1)
 = plabel1 ()
 val  (plabels as plabels1) = plabels1 ()
 in (plabel :: plabels)
end)
 in ( LrTable.NT 3, ( result, plabel1left, plabels1right), rest671)

end
|  ( 10, ( ( _, ( MlyValue.plabel plabel1, plabel1left, plabel1right))
 :: rest671)) => let val  result = MlyValue.plabels (fn _ => let val 
 (plabel as plabel1) = plabel1 ()
 in ([plabel])
end)
 in ( LrTable.NT 3, ( result, plabel1left, plabel1right), rest671)
end
|  ( 11, ( ( _, ( MlyValue.apat apat1, apat1left, apat1right)) :: 
rest671)) => let val  result = MlyValue.pat_list (fn _ => let val  (
apat as apat1) = apat1 ()
 in ([apat])
end)
 in ( LrTable.NT 4, ( result, apat1left, apat1right), rest671)
end
|  ( 12, ( ( _, ( MlyValue.pat_list pat_list1, _, pat_list1right)) ::
 _ :: ( _, ( MlyValue.apat apat1, apat1left, _)) :: rest671)) => let
 val  result = MlyValue.pat_list (fn _ => let val  (apat as apat1) = 
apat1 ()
 val  (pat_list as pat_list1) = pat_list1 ()
 in (apat :: pat_list)
end)
 in ( LrTable.NT 4, ( result, apat1left, pat_list1right), rest671)
end
|  ( 13, ( ( _, ( MlyValue.apat apat1, apat1left, apat1right)) :: 
rest671)) => let val  result = MlyValue.apats (fn _ => let val  (apat
 as apat1) = apat1 ()
 in ([apat])
end)
 in ( LrTable.NT 5, ( result, apat1left, apat1right), rest671)
end
|  ( 14, ( ( _, ( MlyValue.apats apats1, _, apats1right)) :: ( _, ( 
MlyValue.apat apat1, apat1left, _)) :: rest671)) => let val  result = 
MlyValue.apats (fn _ => let val  (apat as apat1) = apat1 ()
 val  (apats as apats1) = apats1 ()
 in (apat :: apats)
end)
 in ( LrTable.NT 5, ( result, apat1left, apats1right), rest671)
end
| _ => raise (mlyAction i392)
end
val void = MlyValue.VOID
val extract = fn a => (fn MlyValue.apats x => x
| _ => let exception ParseInternal
	in raise ParseInternal end) a ()
end
end
structure Tokens : ParamPattern_TOKENS =
struct
type svalue = ParserData.svalue
type ('a,'b) token = ('a,'b) Token.token
fun EOF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 0,(
ParserData.MlyValue.VOID,p1,p2))
fun ID (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 1,(
ParserData.MlyValue.ID (fn () => i),p1,p2))
fun DOT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 2,(
ParserData.MlyValue.VOID,p1,p2))
fun EQUALOP (p1,p2) = Token.TOKEN (ParserData.LrTable.T 3,(
ParserData.MlyValue.VOID,p1,p2))
fun ASTERISK (p1,p2) = Token.TOKEN (ParserData.LrTable.T 4,(
ParserData.MlyValue.VOID,p1,p2))
fun COLON (p1,p2) = Token.TOKEN (ParserData.LrTable.T 5,(
ParserData.MlyValue.VOID,p1,p2))
fun COMMA (p1,p2) = Token.TOKEN (ParserData.LrTable.T 6,(
ParserData.MlyValue.VOID,p1,p2))
fun LBRACE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 7,(
ParserData.MlyValue.VOID,p1,p2))
fun LPAREN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 8,(
ParserData.MlyValue.VOID,p1,p2))
fun RBRACE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 9,(
ParserData.MlyValue.VOID,p1,p2))
fun RPAREN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 10,(
ParserData.MlyValue.VOID,p1,p2))
end
end
