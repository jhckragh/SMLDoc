functor LinkFileLrValsFun(structure Token : TOKEN)
 : sig structure ParserData : PARSER_DATA
       structure Tokens : LinkFile_TOKENS
   end
 = 
struct
structure ParserData=
struct
structure Header = 
struct
(* LinkFile.grm
 * @author YAMATODANI Kiyoshi
 * @copyright 2010, Tohoku University.
 *)

structure EA = ElaboratedAst
structure LF = LinkFile

  
end
structure LrTable = Token.LrTable
structure Token = Token
local open LrTable in 
val table=let val actionRows =
"\
\\001\000\001\000\000\000\000\000\
\\001\000\002\000\019\000\003\000\018\000\004\000\017\000\000\000\
\\001\000\006\000\015\000\007\000\014\000\000\000\
\\001\000\008\000\030\000\000\000\
\\001\000\009\000\012\000\010\000\011\000\011\000\010\000\012\000\009\000\000\000\
\\035\000\000\000\
\\036\000\000\000\
\\037\000\000\000\
\\038\000\000\000\
\\039\000\000\000\
\\040\000\000\000\
\\041\000\000\000\
\\042\000\005\000\031\000\000\000\
\\043\000\000\000\
\\044\000\000\000\
\\045\000\000\000\
\\046\000\006\000\029\000\000\000\
\\047\000\000\000\
\\048\000\000\000\
\\049\000\000\000\
\\050\000\009\000\012\000\010\000\011\000\011\000\010\000\012\000\009\000\
\\013\000\008\000\014\000\007\000\015\000\006\000\000\000\
\\051\000\000\000\
\\052\000\000\000\
\"
val actionRowNumbers =
"\020\000\022\000\020\000\002\000\
\\001\000\001\000\001\000\001\000\
\\001\000\001\000\001\000\021\000\
\\020\000\004\000\019\000\007\000\
\\006\000\005\000\018\000\016\000\
\\011\000\010\000\009\000\008\000\
\\003\000\015\000\012\000\004\000\
\\014\000\004\000\017\000\013\000\
\\000\000"
val gotoT =
"\
\\002\000\003\000\004\000\002\000\005\000\001\000\006\000\032\000\000\000\
\\000\000\
\\002\000\003\000\004\000\002\000\005\000\011\000\000\000\
\\000\000\
\\001\000\014\000\000\000\
\\001\000\018\000\000\000\
\\001\000\019\000\000\000\
\\001\000\020\000\000\000\
\\001\000\021\000\000\000\
\\001\000\022\000\000\000\
\\001\000\023\000\000\000\
\\000\000\
\\002\000\003\000\004\000\002\000\005\000\024\000\000\000\
\\002\000\026\000\003\000\025\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\002\000\026\000\003\000\030\000\000\000\
\\000\000\
\\002\000\026\000\003\000\031\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\"
val numstates = 33
val numrules = 18
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
 | ID of unit ->  (string) | linkfile of unit ->  (LF.item list)
 | items of unit ->  (LF.item list) | item of unit ->  (LF.item)
 | fqn of unit ->  (EA.moduleFQN)
 | arc of unit ->  (EA.moduleType*string) | ident of unit ->  (string)
end
type svalue = MlyValue.svalue
type result = LF.item list
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
  | (T 2) => "ASTERISK"
  | (T 3) => "EQUALOP"
  | (T 4) => "DOT"
  | (T 5) => "DARROW"
  | (T 6) => "LBRACE"
  | (T 7) => "RBRACE"
  | (T 8) => "STRUCTURE"
  | (T 9) => "SIGNATURE"
  | (T 10) => "FUNCTOR"
  | (T 11) => "FUNSIG"
  | (T 12) => "TYPE"
  | (T 13) => "VAL"
  | (T 14) => "EXCEPTION"
  | _ => "bogus-term"
local open Header in
val errtermvalue=
fn _ => MlyValue.VOID
end
val terms : term list = nil
 $$ (T 14) $$ (T 13) $$ (T 12) $$ (T 11) $$ (T 10) $$ (T 9) $$ (T 8)
 $$ (T 7) $$ (T 6) $$ (T 5) $$ (T 4) $$ (T 3) $$ (T 2) $$ (T 0)end
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
 let val  result = MlyValue.ident (fn _ => let val  (ID as ID1) = ID1
 ()
 in (ID)
end)
 in ( LrTable.NT 0, ( result, ID1left, ID1right), rest671)
end
|  ( 1, ( ( _, ( _, ASTERISK1left, ASTERISK1right)) :: rest671)) =>
 let val  result = MlyValue.ident (fn _ => ("*"))
 in ( LrTable.NT 0, ( result, ASTERISK1left, ASTERISK1right), rest671)

end
|  ( 2, ( ( _, ( _, EQUALOP1left, EQUALOP1right)) :: rest671)) => let
 val  result = MlyValue.ident (fn _ => ("="))
 in ( LrTable.NT 0, ( result, EQUALOP1left, EQUALOP1right), rest671)

end
|  ( 3, ( ( _, ( MlyValue.ident ident1, _, ident1right)) :: ( _, ( _, 
STRUCTURE1left, _)) :: rest671)) => let val  result = MlyValue.arc (fn
 _ => let val  (ident as ident1) = ident1 ()
 in (EA.STRUCTURE, ident)
end)
 in ( LrTable.NT 1, ( result, STRUCTURE1left, ident1right), rest671)

end
|  ( 4, ( ( _, ( MlyValue.ident ident1, _, ident1right)) :: ( _, ( _, 
SIGNATURE1left, _)) :: rest671)) => let val  result = MlyValue.arc (fn
 _ => let val  (ident as ident1) = ident1 ()
 in (EA.SIGNATURE, ident)
end)
 in ( LrTable.NT 1, ( result, SIGNATURE1left, ident1right), rest671)

end
|  ( 5, ( ( _, ( MlyValue.ident ident1, _, ident1right)) :: ( _, ( _, 
FUNCTOR1left, _)) :: rest671)) => let val  result = MlyValue.arc (fn _
 => let val  (ident as ident1) = ident1 ()
 in (EA.FUNCTOR, ident)
end)
 in ( LrTable.NT 1, ( result, FUNCTOR1left, ident1right), rest671)
end
|  ( 6, ( ( _, ( MlyValue.ident ident1, _, ident1right)) :: ( _, ( _, 
FUNSIG1left, _)) :: rest671)) => let val  result = MlyValue.arc (fn _
 => let val  (ident as ident1) = ident1 ()
 in (EA.FUNCTORSIGNATURE, ident)
end)
 in ( LrTable.NT 1, ( result, FUNSIG1left, ident1right), rest671)
end
|  ( 7, ( ( _, ( MlyValue.arc arc1, arc1left, arc1right)) :: rest671))
 => let val  result = MlyValue.fqn (fn _ => let val  (arc as arc1) = 
arc1 ()
 in ([arc])
end)
 in ( LrTable.NT 2, ( result, arc1left, arc1right), rest671)
end
|  ( 8, ( ( _, ( MlyValue.fqn fqn1, _, fqn1right)) :: _ :: ( _, ( 
MlyValue.arc arc1, arc1left, _)) :: rest671)) => let val  result = 
MlyValue.fqn (fn _ => let val  (arc as arc1) = arc1 ()
 val  (fqn as fqn1) = fqn1 ()
 in (arc :: fqn)
end)
 in ( LrTable.NT 2, ( result, arc1left, fqn1right), rest671)
end
|  ( 9, ( ( _, ( _, _, RBRACE1right)) :: ( _, ( MlyValue.items items1,
 _, _)) :: _ :: ( _, ( MlyValue.arc arc1, arc1left, _)) :: rest671))
 => let val  result = MlyValue.item (fn _ => let val  (arc as arc1) = 
arc1 ()
 val  (items as items1) = items1 ()
 in (LF.ModuleDefine(arc, items))
end)
 in ( LrTable.NT 3, ( result, arc1left, RBRACE1right), rest671)
end
|  ( 10, ( ( _, ( MlyValue.fqn fqn1, _, fqn1right)) :: _ :: ( _, ( 
MlyValue.arc arc1, arc1left, _)) :: rest671)) => let val  result = 
MlyValue.item (fn _ => let val  (arc as arc1) = arc1 ()
 val  (fqn as fqn1) = fqn1 ()
 in (LF.ModuleReplica(arc, fqn))
end)
 in ( LrTable.NT 3, ( result, arc1left, fqn1right), rest671)
end
|  ( 11, ( ( _, ( MlyValue.ident ident1, _, ident1right)) :: ( _, ( _,
 TYPE1left, _)) :: rest671)) => let val  result = MlyValue.item (fn _
 => let val  (ident as ident1) = ident1 ()
 in (LF.TypeDefine(ident))
end)
 in ( LrTable.NT 3, ( result, TYPE1left, ident1right), rest671)
end
|  ( 12, ( ( _, ( MlyValue.fqn fqn1, _, fqn1right)) :: _ :: ( _, ( 
MlyValue.ident ident1, _, _)) :: ( _, ( _, TYPE1left, _)) :: rest671))
 => let val  result = MlyValue.item (fn _ => let val  (ident as ident1
) = ident1 ()
 val  (fqn as fqn1) = fqn1 ()
 in (LF.TypeReplica(ident, fqn))
end)
 in ( LrTable.NT 3, ( result, TYPE1left, fqn1right), rest671)
end
|  ( 13, ( ( _, ( MlyValue.ident ident1, _, ident1right)) :: ( _, ( _,
 VAL1left, _)) :: rest671)) => let val  result = MlyValue.item (fn _
 => let val  (ident as ident1) = ident1 ()
 in (LF.ValDefine(ident))
end)
 in ( LrTable.NT 3, ( result, VAL1left, ident1right), rest671)
end
|  ( 14, ( ( _, ( MlyValue.ident ident1, _, ident1right)) :: ( _, ( _,
 EXCEPTION1left, _)) :: rest671)) => let val  result = MlyValue.item
 (fn _ => let val  (ident as ident1) = ident1 ()
 in (LF.ExceptionDefine(ident))
end)
 in ( LrTable.NT 3, ( result, EXCEPTION1left, ident1right), rest671)

end
|  ( 15, ( rest671)) => let val  result = MlyValue.items (fn _ => ([])
)
 in ( LrTable.NT 4, ( result, defaultPos, defaultPos), rest671)
end
|  ( 16, ( ( _, ( MlyValue.items items1, _, items1right)) :: ( _, ( 
MlyValue.item item1, item1left, _)) :: rest671)) => let val  result = 
MlyValue.items (fn _ => let val  (item as item1) = item1 ()
 val  (items as items1) = items1 ()
 in (item :: items)
end)
 in ( LrTable.NT 4, ( result, item1left, items1right), rest671)
end
|  ( 17, ( ( _, ( MlyValue.items items1, items1left, items1right)) :: 
rest671)) => let val  result = MlyValue.linkfile (fn _ => let val  (
items as items1) = items1 ()
 in (items)
end)
 in ( LrTable.NT 5, ( result, items1left, items1right), rest671)
end
| _ => raise (mlyAction i392)
end
val void = MlyValue.VOID
val extract = fn a => (fn MlyValue.linkfile x => x
| _ => let exception ParseInternal
	in raise ParseInternal end) a ()
end
end
structure Tokens : LinkFile_TOKENS =
struct
type svalue = ParserData.svalue
type ('a,'b) token = ('a,'b) Token.token
fun EOF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 0,(
ParserData.MlyValue.VOID,p1,p2))
fun ID (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 1,(
ParserData.MlyValue.ID (fn () => i),p1,p2))
fun ASTERISK (p1,p2) = Token.TOKEN (ParserData.LrTable.T 2,(
ParserData.MlyValue.VOID,p1,p2))
fun EQUALOP (p1,p2) = Token.TOKEN (ParserData.LrTable.T 3,(
ParserData.MlyValue.VOID,p1,p2))
fun DOT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 4,(
ParserData.MlyValue.VOID,p1,p2))
fun DARROW (p1,p2) = Token.TOKEN (ParserData.LrTable.T 5,(
ParserData.MlyValue.VOID,p1,p2))
fun LBRACE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 6,(
ParserData.MlyValue.VOID,p1,p2))
fun RBRACE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 7,(
ParserData.MlyValue.VOID,p1,p2))
fun STRUCTURE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 8,(
ParserData.MlyValue.VOID,p1,p2))
fun SIGNATURE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 9,(
ParserData.MlyValue.VOID,p1,p2))
fun FUNCTOR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 10,(
ParserData.MlyValue.VOID,p1,p2))
fun FUNSIG (p1,p2) = Token.TOKEN (ParserData.LrTable.T 11,(
ParserData.MlyValue.VOID,p1,p2))
fun TYPE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 12,(
ParserData.MlyValue.VOID,p1,p2))
fun VAL (p1,p2) = Token.TOKEN (ParserData.LrTable.T 13,(
ParserData.MlyValue.VOID,p1,p2))
fun EXCEPTION (p1,p2) = Token.TOKEN (ParserData.LrTable.T 14,(
ParserData.MlyValue.VOID,p1,p2))
end
end
