functor CMLrValsFun(structure Token : TOKEN)
 : sig structure ParserData : PARSER_DATA
       structure Tokens : CM_TOKENS
   end
 = 
struct
structure ParserData=
struct
structure Header = 
struct
(* -*- sml-yacc -*-
 *
 * cm.grm
 *
 * ML-Yacc grammar for CM description files
 *
 * (C) 1999,2001 Lucent Technologies, Bell Laboratories
 *
 * Author: Matthias Blume (blume@research.bell-labs.com)
 *)


end
structure LrTable = Token.LrTable
structure Token = Token
local open LrTable in 
val table=let val actionRows =
"\
\\001\000\001\000\000\000\000\000\
\\001\000\002\000\229\000\003\000\229\000\007\000\229\000\008\000\229\000\
\\011\000\229\000\012\000\229\000\014\000\229\000\015\000\229\000\
\\016\000\229\000\017\000\229\000\018\000\229\000\019\000\229\000\
\\020\000\229\000\021\000\229\000\022\000\229\000\029\000\229\000\
\\030\000\229\000\034\000\229\000\000\000\
\\001\000\002\000\011\000\000\000\
\\001\000\002\000\011\000\007\000\010\000\008\000\009\000\009\000\008\000\
\\011\000\007\000\000\000\
\\001\000\002\000\011\000\007\000\010\000\008\000\009\000\011\000\007\000\000\000\
\\001\000\002\000\011\000\008\000\009\000\011\000\007\000\000\000\
\\001\000\002\000\011\000\012\000\065\000\000\000\
\\001\000\002\000\035\000\003\000\034\000\000\000\
\\001\000\002\000\035\000\003\000\034\000\011\000\124\000\000\000\
\\001\000\002\000\035\000\003\000\034\000\033\000\068\000\000\000\
\\001\000\004\000\056\000\006\000\055\000\011\000\054\000\023\000\053\000\
\\024\000\052\000\028\000\051\000\031\000\050\000\000\000\
\\001\000\004\000\056\000\006\000\055\000\011\000\087\000\024\000\052\000\
\\028\000\051\000\000\000\
\\001\000\004\000\056\000\019\000\023\000\020\000\022\000\021\000\021\000\
\\022\000\020\000\000\000\
\\001\000\005\000\042\000\000\000\
\\001\000\005\000\043\000\000\000\
\\001\000\005\000\044\000\000\000\
\\001\000\005\000\045\000\000\000\
\\001\000\007\000\028\000\008\000\027\000\010\000\041\000\011\000\040\000\
\\014\000\025\000\018\000\024\000\019\000\023\000\020\000\022\000\
\\021\000\021\000\022\000\020\000\034\000\019\000\000\000\
\\001\000\007\000\028\000\008\000\027\000\010\000\135\000\011\000\040\000\
\\014\000\025\000\018\000\024\000\019\000\023\000\020\000\022\000\
\\021\000\021\000\022\000\020\000\034\000\019\000\000\000\
\\001\000\007\000\028\000\008\000\027\000\011\000\026\000\014\000\025\000\
\\018\000\024\000\019\000\023\000\020\000\022\000\021\000\021\000\
\\022\000\020\000\034\000\019\000\000\000\
\\001\000\007\000\028\000\008\000\027\000\011\000\040\000\012\000\093\000\
\\014\000\025\000\018\000\024\000\019\000\023\000\020\000\022\000\
\\021\000\021\000\022\000\020\000\034\000\019\000\000\000\
\\001\000\007\000\028\000\008\000\027\000\011\000\040\000\014\000\025\000\
\\015\000\108\000\016\000\107\000\017\000\106\000\018\000\024\000\
\\019\000\023\000\020\000\022\000\021\000\021\000\022\000\020\000\
\\034\000\019\000\000\000\
\\001\000\007\000\028\000\008\000\027\000\011\000\040\000\014\000\025\000\
\\017\000\144\000\018\000\024\000\019\000\023\000\020\000\022\000\
\\021\000\021\000\022\000\020\000\034\000\019\000\000\000\
\\001\000\007\000\028\000\008\000\027\000\011\000\040\000\014\000\025\000\
\\018\000\024\000\019\000\023\000\020\000\022\000\021\000\021\000\
\\022\000\020\000\034\000\019\000\000\000\
\\001\000\007\000\028\000\008\000\027\000\011\000\040\000\019\000\023\000\
\\020\000\022\000\021\000\021\000\022\000\020\000\034\000\019\000\000\000\
\\001\000\010\000\061\000\000\000\
\\001\000\010\000\139\000\000\000\
\\001\000\011\000\036\000\000\000\
\\001\000\011\000\060\000\000\000\
\\001\000\011\000\089\000\000\000\
\\001\000\012\000\094\000\000\000\
\\001\000\012\000\097\000\000\000\
\\001\000\012\000\100\000\000\000\
\\001\000\012\000\119\000\026\000\080\000\029\000\079\000\030\000\078\000\000\000\
\\001\000\012\000\120\000\024\000\084\000\025\000\083\000\000\000\
\\001\000\012\000\120\000\024\000\084\000\025\000\083\000\026\000\082\000\
\\027\000\081\000\000\000\
\\001\000\012\000\133\000\000\000\
\\001\000\012\000\134\000\000\000\
\\001\000\012\000\136\000\000\000\
\\001\000\012\000\147\000\000\000\
\\001\000\015\000\143\000\016\000\142\000\017\000\141\000\000\000\
\\001\000\017\000\155\000\000\000\
\\001\000\024\000\084\000\025\000\083\000\026\000\082\000\027\000\081\000\000\000\
\\160\000\000\000\
\\161\000\000\000\
\\162\000\000\000\
\\163\000\000\000\
\\164\000\000\000\
\\165\000\000\000\
\\166\000\000\000\
\\167\000\000\000\
\\168\000\000\000\
\\169\000\000\000\
\\170\000\000\000\
\\171\000\000\000\
\\172\000\000\000\
\\173\000\000\000\
\\174\000\000\000\
\\175\000\000\000\
\\176\000\007\000\028\000\008\000\027\000\011\000\031\000\014\000\025\000\
\\018\000\024\000\019\000\023\000\020\000\022\000\021\000\021\000\
\\022\000\020\000\034\000\019\000\000\000\
\\176\000\007\000\028\000\008\000\027\000\011\000\040\000\014\000\025\000\
\\018\000\024\000\019\000\023\000\020\000\022\000\021\000\021\000\
\\022\000\020\000\034\000\019\000\000\000\
\\177\000\007\000\028\000\008\000\027\000\011\000\040\000\014\000\025\000\
\\018\000\024\000\019\000\023\000\020\000\022\000\021\000\021\000\
\\022\000\020\000\034\000\019\000\000\000\
\\178\000\000\000\
\\178\000\002\000\035\000\003\000\034\000\000\000\
\\178\000\002\000\059\000\000\000\
\\179\000\000\000\
\\180\000\032\000\038\000\033\000\037\000\000\000\
\\181\000\000\000\
\\182\000\000\000\
\\183\000\000\000\
\\184\000\000\000\
\\185\000\000\000\
\\186\000\000\000\
\\187\000\000\000\
\\188\000\032\000\038\000\000\000\
\\189\000\000\000\
\\190\000\000\000\
\\191\000\000\000\
\\192\000\000\000\
\\193\000\000\000\
\\194\000\000\000\
\\195\000\002\000\035\000\003\000\034\000\014\000\075\000\018\000\074\000\000\000\
\\196\000\000\000\
\\197\000\002\000\035\000\003\000\034\000\000\000\
\\197\000\002\000\035\000\003\000\034\000\013\000\149\000\000\000\
\\198\000\000\000\
\\199\000\000\000\
\\200\000\000\000\
\\201\000\000\000\
\\202\000\011\000\124\000\000\000\
\\203\000\000\000\
\\204\000\013\000\102\000\000\000\
\\205\000\000\000\
\\206\000\000\000\
\\207\000\000\000\
\\208\000\000\000\
\\209\000\000\000\
\\210\000\000\000\
\\211\000\000\000\
\\212\000\000\000\
\\213\000\000\000\
\\214\000\000\000\
\\215\000\000\000\
\\216\000\026\000\080\000\029\000\079\000\030\000\078\000\000\000\
\\217\000\000\000\
\\218\000\000\000\
\\219\000\000\000\
\\220\000\025\000\083\000\000\000\
\\221\000\000\000\
\\222\000\000\000\
\\223\000\000\000\
\\224\000\000\000\
\\225\000\000\000\
\\226\000\000\000\
\\227\000\026\000\080\000\000\000\
\\228\000\026\000\080\000\029\000\079\000\000\000\
\\230\000\000\000\
\\231\000\024\000\084\000\025\000\083\000\000\000\
\\232\000\024\000\084\000\025\000\083\000\000\000\
\\233\000\000\000\
\\234\000\000\000\
\\235\000\000\000\
\\236\000\000\000\
\\237\000\000\000\
\\238\000\000\000\
\\239\000\000\000\
\\240\000\000\000\
\\241\000\000\000\
\"
val actionRowNumbers =
"\003\000\004\000\019\000\059\000\
\\043\000\050\000\007\000\054\000\
\\052\000\101\000\055\000\053\000\
\\027\000\066\000\071\000\057\000\
\\017\000\070\000\013\000\014\000\
\\015\000\016\000\068\000\010\000\
\\064\000\028\000\069\000\025\000\
\\061\000\063\000\006\000\044\000\
\\124\000\123\000\009\000\024\000\
\\024\000\058\000\062\000\081\000\
\\122\000\121\000\120\000\119\000\
\\105\000\062\000\103\000\042\000\
\\010\000\011\000\011\000\029\000\
\\010\000\104\000\102\000\020\000\
\\030\000\049\000\007\000\081\000\
\\031\000\125\000\051\000\005\000\
\\032\000\126\000\127\000\074\000\
\\073\000\091\000\081\000\048\000\
\\095\000\010\000\067\000\021\000\
\\010\000\010\000\010\000\011\000\
\\011\000\011\000\011\000\116\000\
\\109\000\011\000\110\000\012\000\
\\033\000\035\000\065\000\072\000\
\\023\000\089\000\046\000\060\000\
\\005\000\056\000\075\000\089\000\
\\002\000\082\000\081\000\077\000\
\\078\000\062\000\010\000\115\000\
\\114\000\001\000\117\000\118\000\
\\108\000\107\000\034\000\036\000\
\\037\000\113\000\106\000\018\000\
\\038\000\090\000\083\000\026\000\
\\093\000\092\000\096\000\094\000\
\\040\000\022\000\062\000\112\000\
\\111\000\081\000\076\000\039\000\
\\084\000\081\000\097\000\098\000\
\\081\000\010\000\079\000\080\000\
\\047\000\088\000\085\000\008\000\
\\045\000\041\000\081\000\083\000\
\\083\000\099\000\100\000\086\000\
\\087\000\000\000"
val gotoT =
"\
\\001\000\157\000\002\000\004\000\003\000\003\000\004\000\002\000\
\\024\000\001\000\000\000\
\\003\000\011\000\004\000\010\000\024\000\001\000\000\000\
\\007\000\016\000\010\000\015\000\020\000\014\000\021\000\013\000\
\\032\000\012\000\000\000\
\\007\000\028\000\008\000\027\000\010\000\015\000\020\000\014\000\
\\021\000\013\000\032\000\012\000\000\000\
\\000\000\
\\006\000\030\000\000\000\
\\022\000\031\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\010\000\037\000\020\000\014\000\021\000\013\000\032\000\012\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\017\000\047\000\018\000\046\000\019\000\045\000\023\000\044\000\000\000\
\\005\000\056\000\009\000\055\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\010\000\037\000\020\000\014\000\021\000\013\000\032\000\012\000\000\000\
\\009\000\055\000\022\000\061\000\030\000\060\000\000\000\
\\024\000\062\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\022\000\061\000\030\000\065\000\031\000\064\000\000\000\
\\020\000\014\000\021\000\067\000\032\000\012\000\000\000\
\\020\000\014\000\021\000\068\000\032\000\012\000\000\000\
\\000\000\
\\009\000\055\000\000\000\
\\013\000\071\000\014\000\070\000\022\000\069\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\009\000\075\000\011\000\074\000\000\000\
\\000\000\
\\000\000\
\\017\000\047\000\018\000\083\000\023\000\044\000\000\000\
\\017\000\084\000\023\000\044\000\000\000\
\\017\000\086\000\023\000\044\000\000\000\
\\000\000\
\\017\000\089\000\018\000\088\000\023\000\044\000\000\000\
\\000\000\
\\000\000\
\\010\000\090\000\020\000\014\000\021\000\013\000\032\000\012\000\000\000\
\\000\000\
\\000\000\
\\022\000\093\000\000\000\
\\013\000\094\000\014\000\070\000\022\000\069\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\004\000\097\000\024\000\096\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\026\000\099\000\000\000\
\\013\000\101\000\014\000\070\000\022\000\069\000\000\000\
\\000\000\
\\000\000\
\\017\000\047\000\018\000\046\000\019\000\102\000\023\000\044\000\000\000\
\\000\000\
\\010\000\090\000\012\000\103\000\020\000\014\000\021\000\013\000\
\\032\000\012\000\000\000\
\\017\000\047\000\018\000\107\000\023\000\044\000\000\000\
\\017\000\047\000\018\000\108\000\023\000\044\000\000\000\
\\017\000\047\000\018\000\109\000\023\000\044\000\000\000\
\\017\000\110\000\023\000\044\000\000\000\
\\017\000\111\000\023\000\044\000\000\000\
\\017\000\112\000\023\000\044\000\000\000\
\\017\000\113\000\023\000\044\000\000\000\
\\000\000\
\\000\000\
\\017\000\114\000\023\000\044\000\000\000\
\\000\000\
\\020\000\116\000\023\000\115\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\007\000\119\000\010\000\015\000\020\000\014\000\021\000\013\000\
\\032\000\012\000\000\000\
\\028\000\121\000\029\000\120\000\000\000\
\\000\000\
\\007\000\028\000\008\000\123\000\010\000\015\000\020\000\014\000\
\\021\000\013\000\032\000\012\000\000\000\
\\004\000\010\000\024\000\096\000\000\000\
\\000\000\
\\000\000\
\\028\000\121\000\029\000\124\000\000\000\
\\024\000\126\000\025\000\125\000\000\000\
\\000\000\
\\013\000\128\000\014\000\070\000\015\000\127\000\022\000\069\000\000\000\
\\000\000\
\\000\000\
\\009\000\129\000\000\000\
\\017\000\047\000\018\000\046\000\019\000\130\000\023\000\044\000\000\000\
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
\\010\000\037\000\020\000\014\000\021\000\013\000\032\000\012\000\000\000\
\\000\000\
\\000\000\
\\022\000\136\000\027\000\135\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\016\000\138\000\000\000\
\\010\000\090\000\020\000\014\000\021\000\013\000\032\000\012\000\000\000\
\\009\000\075\000\011\000\143\000\000\000\
\\000\000\
\\000\000\
\\013\000\144\000\014\000\070\000\022\000\069\000\000\000\
\\000\000\
\\000\000\
\\022\000\136\000\027\000\146\000\000\000\
\\013\000\148\000\014\000\070\000\022\000\069\000\000\000\
\\000\000\
\\000\000\
\\013\000\149\000\014\000\070\000\022\000\069\000\000\000\
\\017\000\047\000\018\000\046\000\019\000\150\000\023\000\044\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\022\000\152\000\028\000\151\000\000\000\
\\000\000\
\\000\000\
\\013\000\128\000\014\000\070\000\015\000\154\000\022\000\069\000\000\000\
\\022\000\136\000\027\000\155\000\000\000\
\\022\000\136\000\027\000\156\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\"
val numstates = 158
val numrules = 82
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
type arg = {}
structure MlyValue = 
struct
datatype svalue = VOID | ntVOID of unit ->  unit
 | INEQSYM of unit ->  (CMSemantic.ineqsym)
 | EQSYM of unit ->  (CMSemantic.eqsym)
 | MULSYM of unit ->  (CMSemantic.mulsym)
 | ADDSYM of unit ->  (CMSemantic.addsym) | ERROR of unit ->  (string)
 | NUMBER of unit ->  (int) | ML_ID of unit ->  (string)
 | CM_ID of unit ->  (string) | FILE_NATIVE of unit ->  (string)
 | FILE_STANDARD of unit ->  (string) | filecat of unit ->  (unit)
 | srcfiles of unit ->  (unit) | srcfile of unit ->  (unit)
 | opttoolopts of unit ->  (unit) | ptoolopts of unit ->  (unit)
 | toolopts of unit ->  (unit) | optclass of unit ->  (string option)
 | class of unit ->  (string) | word of unit ->  (string)
 | sym of unit ->  (unit) | pathname of unit ->  (CMSemantic.pathName)
 | ml_symbolset of unit ->  (unit) | ml_symbol of unit ->  (unit)
 | exp of unit ->  (unit) | boolexp of unit ->  (unit)
 | aexp of unit ->  (unit) | else_members of unit ->  (unit)
 | guarded_members of unit ->  ( ( CMSemantic.pathName * string option )  list)
 | member of unit ->  ( ( CMSemantic.pathName * string option )  list)
 | members of unit ->  ( ( CMSemantic.pathName * string option )  list)
 | else_exports of unit ->  (unit)
 | guarded_exports of unit ->  (unit) | export of unit ->  (unit)
 | exports of unit ->  (unit) | opt_exports of unit ->  (unit)
 | mand_exports of unit ->  (unit) | wrapspec of unit ->  (unit)
 | version of unit ->  (unit) | lprivspec of unit ->  (unit)
 | gprivspec of unit ->  (unit)
 | group of unit ->  ( ( CMSemantic.pathName * string option )  list)
 | description of unit ->  (CMSemantic.description)
end
type svalue = MlyValue.svalue
type result = CMSemantic.description
end
structure EC=
struct
open LrTable
infix 5 $$
fun x $$ y = y::x
val is_keyword =
fn (T 6) => true | (T 7) => true | (T 9) => true | (T 13) => true | 
(T 14) => true | (T 15) => true | (T 16) => true | (T 22) => true | 
(T 18) => true | (T 19) => true | (T 20) => true | (T 21) => true | _ => false
val preferred_change : (term list * term list) list = 
(nil
,nil
 $$ (T 10))::
nil
val noShift = 
fn (T 0) => true | _ => false
val showTerminal =
fn (T 0) => "EOF"
  | (T 1) => "FILE_STANDARD"
  | (T 2) => "FILE_NATIVE"
  | (T 3) => "CM_ID"
  | (T 4) => "ML_ID"
  | (T 5) => "NUMBER"
  | (T 6) => "GROUP"
  | (T 7) => "LIBRARY"
  | (T 8) => "ALIAS"
  | (T 9) => "IS"
  | (T 10) => "LPAREN"
  | (T 11) => "RPAREN"
  | (T 12) => "COLON"
  | (T 13) => "IF"
  | (T 14) => "ELIF"
  | (T 15) => "ELSE"
  | (T 16) => "ENDIF"
  | (T 17) => "ERROR"
  | (T 18) => "STRUCTURE"
  | (T 19) => "SIGNATURE"
  | (T 20) => "FUNCTOR"
  | (T 21) => "FUNSIG"
  | (T 22) => "DEFINED"
  | (T 23) => "ADDSYM"
  | (T 24) => "MULSYM"
  | (T 25) => "EQSYM"
  | (T 26) => "INEQSYM"
  | (T 27) => "TILDE"
  | (T 28) => "ANDALSO"
  | (T 29) => "ORELSE"
  | (T 30) => "NOT"
  | (T 31) => "STAR"
  | (T 32) => "DASH"
  | (T 33) => "SOURCE"
  | _ => "bogus-term"
local open Header in
val errtermvalue=
fn _ => MlyValue.VOID
end
val terms : term list = nil
 $$ (T 33) $$ (T 32) $$ (T 31) $$ (T 30) $$ (T 29) $$ (T 28) $$ (T 27)
 $$ (T 22) $$ (T 21) $$ (T 20) $$ (T 19) $$ (T 18) $$ (T 16) $$ (T 15)
 $$ (T 14) $$ (T 13) $$ (T 12) $$ (T 11) $$ (T 10) $$ (T 9) $$ (T 8)
 $$ (T 7) $$ (T 6) $$ (T 0)end
structure Actions =
struct 
type int = Int.int
exception mlyAction of int
local open Header in
val actions = 
fn (i392:int,defaultPos,stack,
    ({}):arg) =>
case (i392,stack)
of  ( 0, ( ( _, ( MlyValue.group group1, group1left, group1right)) :: 
rest671)) => let val  result = MlyValue.description (fn _ => let val 
 (group as group1) = group1 ()
 in (CMSemantic.Group group)
end)
 in ( LrTable.NT 0, ( result, group1left, group1right), rest671)
end
|  ( 1, ( ( _, ( MlyValue.pathname pathname1, _, pathname1right)) :: (
 _, ( _, ALIAS1left, _)) :: rest671)) => let val  result = 
MlyValue.description (fn _ => let val  (pathname as pathname1) = 
pathname1 ()
 in (CMSemantic.Alias pathname)
end)
 in ( LrTable.NT 0, ( result, ALIAS1left, pathname1right), rest671)

end
|  ( 2, ( ( _, ( MlyValue.members members1, _, members1right)) :: _ ::
 ( _, ( MlyValue.opt_exports opt_exports1, _, _)) :: _ :: ( _, ( 
MlyValue.srcfile srcfile1, _, _)) :: _ :: ( _, ( MlyValue.gprivspec 
gprivspec1, gprivspec1left, _)) :: rest671)) => let val  result = 
MlyValue.group (fn _ => let val  gprivspec1 = gprivspec1 ()
 val  srcfile1 = srcfile1 ()
 val  opt_exports1 = opt_exports1 ()
 val  (members as members1) = members1 ()
 in (members)
end)
 in ( LrTable.NT 1, ( result, gprivspec1left, members1right), rest671)

end
|  ( 3, ( ( _, ( MlyValue.members members1, _, members1right)) :: _ ::
 ( _, ( MlyValue.opt_exports opt_exports1, _, _)) :: ( _, ( 
MlyValue.gprivspec gprivspec1, gprivspec1left, _)) :: rest671)) => let
 val  result = MlyValue.group (fn _ => let val  gprivspec1 = 
gprivspec1 ()
 val  opt_exports1 = opt_exports1 ()
 val  (members as members1) = members1 ()
 in (members)
end)
 in ( LrTable.NT 1, ( result, gprivspec1left, members1right), rest671)

end
|  ( 4, ( ( _, ( MlyValue.members members1, _, members1right)) :: _ ::
 ( _, ( MlyValue.mand_exports mand_exports1, _, _)) :: _ :: ( _, ( 
MlyValue.version version1, _, _)) :: _ :: ( _, ( MlyValue.lprivspec 
lprivspec1, lprivspec1left, _)) :: rest671)) => let val  result = 
MlyValue.group (fn _ => let val  lprivspec1 = lprivspec1 ()
 val  version1 = version1 ()
 val  mand_exports1 = mand_exports1 ()
 val  (members as members1) = members1 ()
 in (members)
end)
 in ( LrTable.NT 1, ( result, lprivspec1left, members1right), rest671)

end
|  ( 5, ( ( _, ( MlyValue.members members1, _, members1right)) :: _ ::
 ( _, ( MlyValue.mand_exports mand_exports1, _, _)) :: ( _, ( 
MlyValue.lprivspec lprivspec1, lprivspec1left, _)) :: rest671)) => let
 val  result = MlyValue.group (fn _ => let val  lprivspec1 = 
lprivspec1 ()
 val  mand_exports1 = mand_exports1 ()
 val  (members as members1) = members1 ()
 in (members)
end)
 in ( LrTable.NT 1, ( result, lprivspec1left, members1right), rest671)

end
|  ( 6, ( ( _, ( MlyValue.FILE_STANDARD FILE_STANDARD1, 
FILE_STANDARD1left, FILE_STANDARD1right)) :: rest671)) => let val  
result = MlyValue.version (fn _ => let val  FILE_STANDARD1 = 
FILE_STANDARD1 ()
 in ()
end)
 in ( LrTable.NT 4, ( result, FILE_STANDARD1left, FILE_STANDARD1right)
, rest671)
end
|  ( 7, ( rest671)) => let val  result = MlyValue.wrapspec (fn _ => ()
)
 in ( LrTable.NT 5, ( result, defaultPos, defaultPos), rest671)
end
|  ( 8, ( ( _, ( MlyValue.word word1, _, word1right)) :: ( _, ( 
MlyValue.wrapspec wrapspec1, wrapspec1left, _)) :: rest671)) => let
 val  result = MlyValue.wrapspec (fn _ => let val  wrapspec1 = 
wrapspec1 ()
 val  word1 = word1 ()
 in ()
end)
 in ( LrTable.NT 5, ( result, wrapspec1left, word1right), rest671)
end
|  ( 9, ( ( _, ( _, GROUP1left, GROUP1right)) :: rest671)) => let val 
 result = MlyValue.gprivspec (fn _ => ())
 in ( LrTable.NT 2, ( result, GROUP1left, GROUP1right), rest671)
end
|  ( 10, ( ( _, ( MlyValue.gprivspec gprivspec1, _, gprivspec1right))
 :: ( _, ( MlyValue.word word1, word1left, _)) :: rest671)) => let
 val  result = MlyValue.gprivspec (fn _ => let val  word1 = word1 ()
 val  gprivspec1 = gprivspec1 ()
 in ()
end)
 in ( LrTable.NT 2, ( result, word1left, gprivspec1right), rest671)

end
|  ( 11, ( ( _, ( _, LIBRARY1left, LIBRARY1right)) :: rest671)) => let
 val  result = MlyValue.lprivspec (fn _ => ())
 in ( LrTable.NT 3, ( result, LIBRARY1left, LIBRARY1right), rest671)

end
|  ( 12, ( ( _, ( MlyValue.lprivspec lprivspec1, _, lprivspec1right))
 :: ( _, ( MlyValue.word word1, word1left, _)) :: rest671)) => let
 val  result = MlyValue.lprivspec (fn _ => let val  word1 = word1 ()
 val  lprivspec1 = lprivspec1 ()
 in ()
end)
 in ( LrTable.NT 3, ( result, word1left, lprivspec1right), rest671)

end
|  ( 13, ( ( _, ( MlyValue.lprivspec lprivspec1, _, lprivspec1right))
 :: _ :: ( _, ( MlyValue.wrapspec wrapspec1, _, _)) :: ( _, ( _, 
LPAREN1left, _)) :: rest671)) => let val  result = MlyValue.lprivspec
 (fn _ => let val  wrapspec1 = wrapspec1 ()
 val  lprivspec1 = lprivspec1 ()
 in ()
end)
 in ( LrTable.NT 3, ( result, LPAREN1left, lprivspec1right), rest671)

end
|  ( 14, ( ( _, ( MlyValue.export export1, export1left, export1right))
 :: rest671)) => let val  result = MlyValue.mand_exports (fn _ => let
 val  export1 = export1 ()
 in ()
end)
 in ( LrTable.NT 6, ( result, export1left, export1right), rest671)
end
|  ( 15, ( ( _, ( MlyValue.export export1, _, export1right)) :: ( _, (
 MlyValue.mand_exports mand_exports1, mand_exports1left, _)) :: 
rest671)) => let val  result = MlyValue.mand_exports (fn _ => let val 
 mand_exports1 = mand_exports1 ()
 val  export1 = export1 ()
 in ()
end)
 in ( LrTable.NT 6, ( result, mand_exports1left, export1right), 
rest671)
end
|  ( 16, ( rest671)) => let val  result = MlyValue.opt_exports (fn _
 => ())
 in ( LrTable.NT 7, ( result, defaultPos, defaultPos), rest671)
end
|  ( 17, ( ( _, ( MlyValue.mand_exports mand_exports1, 
mand_exports1left, mand_exports1right)) :: rest671)) => let val  
result = MlyValue.opt_exports (fn _ => let val  mand_exports1 = 
mand_exports1 ()
 in ()
end)
 in ( LrTable.NT 7, ( result, mand_exports1left, mand_exports1right), 
rest671)
end
|  ( 18, ( rest671)) => let val  result = MlyValue.exports (fn _ => ()
)
 in ( LrTable.NT 8, ( result, defaultPos, defaultPos), rest671)
end
|  ( 19, ( ( _, ( MlyValue.export export1, _, export1right)) :: ( _, (
 MlyValue.exports exports1, exports1left, _)) :: rest671)) => let val 
 result = MlyValue.exports (fn _ => let val  exports1 = exports1 ()
 val  export1 = export1 ()
 in ()
end)
 in ( LrTable.NT 8, ( result, exports1left, export1right), rest671)

end
|  ( 20, ( ( _, ( MlyValue.ml_symbolset ml_symbolset1, 
ml_symbolset1left, ml_symbolset1right)) :: rest671)) => let val  
result = MlyValue.export (fn _ => let val  ml_symbolset1 = 
ml_symbolset1 ()
 in ()
end)
 in ( LrTable.NT 9, ( result, ml_symbolset1left, ml_symbolset1right), 
rest671)
end
|  ( 21, ( ( _, ( MlyValue.guarded_exports guarded_exports1, _, 
guarded_exports1right)) :: ( _, ( MlyValue.exp exp1, _, _)) :: ( _, (
 _, IF1left, _)) :: rest671)) => let val  result = MlyValue.export (fn
 _ => let val  exp1 = exp1 ()
 val  guarded_exports1 = guarded_exports1 ()
 in ()
end)
 in ( LrTable.NT 9, ( result, IF1left, guarded_exports1right), rest671
)
end
|  ( 22, ( ( _, ( MlyValue.ERROR ERROR1, ERROR1left, ERROR1right)) :: 
rest671)) => let val  result = MlyValue.export (fn _ => let val  
ERROR1 = ERROR1 ()
 in ()
end)
 in ( LrTable.NT 9, ( result, ERROR1left, ERROR1right), rest671)
end
|  ( 23, ( ( _, ( _, GROUP1left, GROUP1right)) :: rest671)) => let
 val  result = MlyValue.filecat (fn _ => ())
 in ( LrTable.NT 31, ( result, GROUP1left, GROUP1right), rest671)
end
|  ( 24, ( ( _, ( _, SOURCE1left, SOURCE1right)) :: rest671)) => let
 val  result = MlyValue.filecat (fn _ => ())
 in ( LrTable.NT 31, ( result, SOURCE1left, SOURCE1right), rest671)

end
|  ( 25, ( ( _, ( MlyValue.ml_symbol ml_symbol1, ml_symbol1left, 
ml_symbol1right)) :: rest671)) => let val  result = 
MlyValue.ml_symbolset (fn _ => let val  ml_symbol1 = ml_symbol1 ()
 in ()
end)
 in ( LrTable.NT 20, ( result, ml_symbol1left, ml_symbol1right), 
rest671)
end
|  ( 26, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.exports 
exports1, _, _)) :: ( _, ( _, LPAREN1left, _)) :: rest671)) => let
 val  result = MlyValue.ml_symbolset (fn _ => let val  exports1 = 
exports1 ()
 in ()
end)
 in ( LrTable.NT 20, ( result, LPAREN1left, RPAREN1right), rest671)

end
|  ( 27, ( ( _, ( MlyValue.ml_symbolset ml_symbolset2, _, 
ml_symbolset2right)) :: _ :: ( _, ( MlyValue.ml_symbolset 
ml_symbolset1, ml_symbolset1left, _)) :: rest671)) => let val  result
 = MlyValue.ml_symbolset (fn _ => let val  ml_symbolset1 = 
ml_symbolset1 ()
 val  ml_symbolset2 = ml_symbolset2 ()
 in ()
end)
 in ( LrTable.NT 20, ( result, ml_symbolset1left, ml_symbolset2right),
 rest671)
end
|  ( 28, ( ( _, ( MlyValue.ml_symbolset ml_symbolset2, _, 
ml_symbolset2right)) :: _ :: ( _, ( MlyValue.ml_symbolset 
ml_symbolset1, ml_symbolset1left, _)) :: rest671)) => let val  result
 = MlyValue.ml_symbolset (fn _ => let val  ml_symbolset1 = 
ml_symbolset1 ()
 val  ml_symbolset2 = ml_symbolset2 ()
 in ()
end)
 in ( LrTable.NT 20, ( result, ml_symbolset1left, ml_symbolset2right),
 rest671)
end
|  ( 29, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.srcfiles 
srcfiles1, _, _)) :: _ :: ( _, ( MlyValue.filecat filecat1, 
filecat1left, _)) :: rest671)) => let val  result = 
MlyValue.ml_symbolset (fn _ => let val  filecat1 = filecat1 ()
 val  srcfiles1 = srcfiles1 ()
 in ()
end)
 in ( LrTable.NT 20, ( result, filecat1left, RPAREN1right), rest671)

end
|  ( 30, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.opttoolopts 
opttoolopts1, _, _)) :: ( _, ( MlyValue.pathname pathname1, _, _)) ::
 _ :: ( _, ( _, LIBRARY1left, _)) :: rest671)) => let val  result = 
MlyValue.ml_symbolset (fn _ => let val  pathname1 = pathname1 ()
 val  opttoolopts1 = opttoolopts1 ()
 in ()
end)
 in ( LrTable.NT 20, ( result, LIBRARY1left, RPAREN1right), rest671)

end
|  ( 31, ( ( _, ( MlyValue.else_exports else_exports1, _, 
else_exports1right)) :: ( _, ( MlyValue.exports exports1, exports1left
, _)) :: rest671)) => let val  result = MlyValue.guarded_exports (fn _
 => let val  exports1 = exports1 ()
 val  else_exports1 = else_exports1 ()
 in ()
end)
 in ( LrTable.NT 10, ( result, exports1left, else_exports1right), 
rest671)
end
|  ( 32, ( ( _, ( _, ENDIF1left, ENDIF1right)) :: rest671)) => let
 val  result = MlyValue.else_exports (fn _ => ())
 in ( LrTable.NT 11, ( result, ENDIF1left, ENDIF1right), rest671)
end
|  ( 33, ( ( _, ( _, _, ENDIF1right)) :: ( _, ( MlyValue.exports 
exports1, _, _)) :: ( _, ( _, ELSE1left, _)) :: rest671)) => let val  
result = MlyValue.else_exports (fn _ => let val  exports1 = exports1
 ()
 in ()
end)
 in ( LrTable.NT 11, ( result, ELSE1left, ENDIF1right), rest671)
end
|  ( 34, ( ( _, ( MlyValue.guarded_exports guarded_exports1, _, 
guarded_exports1right)) :: ( _, ( MlyValue.exp exp1, _, _)) :: ( _, (
 _, ELIF1left, _)) :: rest671)) => let val  result = 
MlyValue.else_exports (fn _ => let val  exp1 = exp1 ()
 val  guarded_exports1 = guarded_exports1 ()
 in ()
end)
 in ( LrTable.NT 11, ( result, ELIF1left, guarded_exports1right), 
rest671)
end
|  ( 35, ( rest671)) => let val  result = MlyValue.members (fn _ => (
[]))
 in ( LrTable.NT 12, ( result, defaultPos, defaultPos), rest671)
end
|  ( 36, ( ( _, ( MlyValue.members members1, _, members1right)) :: ( _
, ( MlyValue.member member1, member1left, _)) :: rest671)) => let val 
 result = MlyValue.members (fn _ => let val  (member as member1) = 
member1 ()
 val  (members as members1) = members1 ()
 in (member @ members)
end)
 in ( LrTable.NT 12, ( result, member1left, members1right), rest671)

end
|  ( 37, ( rest671)) => let val  result = MlyValue.toolopts (fn _ => (
))
 in ( LrTable.NT 26, ( result, defaultPos, defaultPos), rest671)
end
|  ( 38, ( ( _, ( MlyValue.toolopts toolopts1, _, toolopts1right)) :: 
( _, ( MlyValue.pathname pathname1, pathname1left, _)) :: rest671)) =>
 let val  result = MlyValue.toolopts (fn _ => let val  pathname1 = 
pathname1 ()
 val  toolopts1 = toolopts1 ()
 in ()
end)
 in ( LrTable.NT 26, ( result, pathname1left, toolopts1right), rest671
)
end
|  ( 39, ( ( _, ( MlyValue.toolopts toolopts1, _, toolopts1right)) :: 
( _, ( MlyValue.ptoolopts ptoolopts1, _, _)) :: _ :: ( _, ( 
MlyValue.pathname pathname1, pathname1left, _)) :: rest671)) => let
 val  result = MlyValue.toolopts (fn _ => let val  pathname1 = 
pathname1 ()
 val  ptoolopts1 = ptoolopts1 ()
 val  toolopts1 = toolopts1 ()
 in ()
end)
 in ( LrTable.NT 26, ( result, pathname1left, toolopts1right), rest671
)
end
|  ( 40, ( ( _, ( MlyValue.toolopts toolopts1, _, toolopts1right)) :: 
( _, ( MlyValue.pathname pathname2, _, _)) :: _ :: ( _, ( 
MlyValue.pathname pathname1, pathname1left, _)) :: rest671)) => let
 val  result = MlyValue.toolopts (fn _ => let val  pathname1 = 
pathname1 ()
 val  pathname2 = pathname2 ()
 val  toolopts1 = toolopts1 ()
 in ()
end)
 in ( LrTable.NT 26, ( result, pathname1left, toolopts1right), rest671
)
end
|  ( 41, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.toolopts 
toolopts1, _, _)) :: ( _, ( _, LPAREN1left, _)) :: rest671)) => let
 val  result = MlyValue.ptoolopts (fn _ => let val  toolopts1 = 
toolopts1 ()
 in ()
end)
 in ( LrTable.NT 27, ( result, LPAREN1left, RPAREN1right), rest671)

end
|  ( 42, ( rest671)) => let val  result = MlyValue.opttoolopts (fn _
 => ())
 in ( LrTable.NT 28, ( result, defaultPos, defaultPos), rest671)
end
|  ( 43, ( ( _, ( MlyValue.ptoolopts ptoolopts1, ptoolopts1left, 
ptoolopts1right)) :: rest671)) => let val  result = 
MlyValue.opttoolopts (fn _ => let val  ptoolopts1 = ptoolopts1 ()
 in ()
end)
 in ( LrTable.NT 28, ( result, ptoolopts1left, ptoolopts1right), 
rest671)
end
|  ( 44, ( rest671)) => let val  result = MlyValue.optclass (fn _ => (
NONE))
 in ( LrTable.NT 25, ( result, defaultPos, defaultPos), rest671)
end
|  ( 45, ( ( _, ( MlyValue.class class1, _, class1right)) :: ( _, ( _,
 COLON1left, _)) :: rest671)) => let val  result = MlyValue.optclass
 (fn _ => let val  (class as class1) = class1 ()
 in (SOME class)
end)
 in ( LrTable.NT 25, ( result, COLON1left, class1right), rest671)
end
|  ( 46, ( ( _, ( MlyValue.opttoolopts opttoolopts1, _, 
opttoolopts1right)) :: ( _, ( MlyValue.optclass optclass1, _, _)) :: (
 _, ( MlyValue.pathname pathname1, pathname1left, _)) :: rest671)) =>
 let val  result = MlyValue.member (fn _ => let val  (pathname as 
pathname1) = pathname1 ()
 val  (optclass as optclass1) = optclass1 ()
 val  opttoolopts1 = opttoolopts1 ()
 in ([(pathname, optclass)])
end)
 in ( LrTable.NT 13, ( result, pathname1left, opttoolopts1right), 
rest671)
end
|  ( 47, ( ( _, ( MlyValue.guarded_members guarded_members1, _, 
guarded_members1right)) :: ( _, ( MlyValue.exp exp1, _, _)) :: ( _, (
 _, IF1left, _)) :: rest671)) => let val  result = MlyValue.member (fn
 _ => let val  exp1 = exp1 ()
 val  (guarded_members as guarded_members1) = guarded_members1 ()
 in (guarded_members)
end)
 in ( LrTable.NT 13, ( result, IF1left, guarded_members1right), 
rest671)
end
|  ( 48, ( ( _, ( MlyValue.ERROR ERROR1, ERROR1left, ERROR1right)) :: 
rest671)) => let val  result = MlyValue.member (fn _ => let val  
ERROR1 = ERROR1 ()
 in ([])
end)
 in ( LrTable.NT 13, ( result, ERROR1left, ERROR1right), rest671)
end
|  ( 49, ( ( _, ( MlyValue.word word1, word1left, word1right)) :: 
rest671)) => let val  result = MlyValue.class (fn _ => let val  (word
 as word1) = word1 ()
 in (word)
end)
 in ( LrTable.NT 24, ( result, word1left, word1right), rest671)
end
|  ( 50, ( ( _, ( MlyValue.else_members else_members1, _, 
else_members1right)) :: ( _, ( MlyValue.members members1, members1left
, _)) :: rest671)) => let val  result = MlyValue.guarded_members (fn _
 => let val  (members as members1) = members1 ()
 val  else_members1 = else_members1 ()
 in (members)
end)
 in ( LrTable.NT 14, ( result, members1left, else_members1right), 
rest671)
end
|  ( 51, ( ( _, ( _, ENDIF1left, ENDIF1right)) :: rest671)) => let
 val  result = MlyValue.else_members (fn _ => ())
 in ( LrTable.NT 15, ( result, ENDIF1left, ENDIF1right), rest671)
end
|  ( 52, ( ( _, ( _, _, ENDIF1right)) :: ( _, ( MlyValue.members 
members1, _, _)) :: ( _, ( _, ELSE1left, _)) :: rest671)) => let val  
result = MlyValue.else_members (fn _ => let val  members1 = members1
 ()
 in ()
end)
 in ( LrTable.NT 15, ( result, ELSE1left, ENDIF1right), rest671)
end
|  ( 53, ( ( _, ( MlyValue.guarded_members guarded_members1, _, 
guarded_members1right)) :: ( _, ( MlyValue.exp exp1, _, _)) :: ( _, (
 _, ELIF1left, _)) :: rest671)) => let val  result = 
MlyValue.else_members (fn _ => let val  exp1 = exp1 ()
 val  guarded_members1 = guarded_members1 ()
 in ()
end)
 in ( LrTable.NT 15, ( result, ELIF1left, guarded_members1right), 
rest671)
end
|  ( 54, ( ( _, ( MlyValue.FILE_STANDARD FILE_STANDARD1, 
FILE_STANDARD1left, FILE_STANDARD1right)) :: rest671)) => let val  
result = MlyValue.word (fn _ => let val  (FILE_STANDARD as 
FILE_STANDARD1) = FILE_STANDARD1 ()
 in (FILE_STANDARD)
end)
 in ( LrTable.NT 23, ( result, FILE_STANDARD1left, FILE_STANDARD1right
), rest671)
end
|  ( 55, ( ( _, ( MlyValue.CM_ID CM_ID1, CM_ID1left, CM_ID1right)) :: 
rest671)) => let val  result = MlyValue.sym (fn _ => let val  CM_ID1 =
 CM_ID1 ()
 in ()
end)
 in ( LrTable.NT 22, ( result, CM_ID1left, CM_ID1right), rest671)
end
|  ( 56, ( ( _, ( MlyValue.boolexp boolexp1, boolexp1left, 
boolexp1right)) :: rest671)) => let val  result = MlyValue.exp (fn _
 => let val  boolexp1 = boolexp1 ()
 in ()
end)
 in ( LrTable.NT 18, ( result, boolexp1left, boolexp1right), rest671)

end
|  ( 57, ( ( _, ( MlyValue.NUMBER NUMBER1, NUMBER1left, NUMBER1right))
 :: rest671)) => let val  result = MlyValue.aexp (fn _ => let val  
NUMBER1 = NUMBER1 ()
 in ()
end)
 in ( LrTable.NT 16, ( result, NUMBER1left, NUMBER1right), rest671)

end
|  ( 58, ( ( _, ( MlyValue.sym sym1, sym1left, sym1right)) :: rest671)
) => let val  result = MlyValue.aexp (fn _ => let val  sym1 = sym1 ()
 in ()
end)
 in ( LrTable.NT 16, ( result, sym1left, sym1right), rest671)
end
|  ( 59, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.aexp aexp1,
 _, _)) :: ( _, ( _, LPAREN1left, _)) :: rest671)) => let val  result
 = MlyValue.aexp (fn _ => let val  aexp1 = aexp1 ()
 in ()
end)
 in ( LrTable.NT 16, ( result, LPAREN1left, RPAREN1right), rest671)

end
|  ( 60, ( ( _, ( MlyValue.aexp aexp2, _, aexp2right)) :: ( _, ( 
MlyValue.ADDSYM ADDSYM1, _, _)) :: ( _, ( MlyValue.aexp aexp1, 
aexp1left, _)) :: rest671)) => let val  result = MlyValue.aexp (fn _
 => let val  aexp1 = aexp1 ()
 val  ADDSYM1 = ADDSYM1 ()
 val  aexp2 = aexp2 ()
 in ()
end)
 in ( LrTable.NT 16, ( result, aexp1left, aexp2right), rest671)
end
|  ( 61, ( ( _, ( MlyValue.aexp aexp2, _, aexp2right)) :: ( _, ( 
MlyValue.MULSYM MULSYM1, _, _)) :: ( _, ( MlyValue.aexp aexp1, 
aexp1left, _)) :: rest671)) => let val  result = MlyValue.aexp (fn _
 => let val  aexp1 = aexp1 ()
 val  MULSYM1 = MULSYM1 ()
 val  aexp2 = aexp2 ()
 in ()
end)
 in ( LrTable.NT 16, ( result, aexp1left, aexp2right), rest671)
end
|  ( 62, ( ( _, ( MlyValue.aexp aexp1, _, aexp1right)) :: ( _, ( _, 
TILDE1left, _)) :: rest671)) => let val  result = MlyValue.aexp (fn _
 => let val  aexp1 = aexp1 ()
 in ()
end)
 in ( LrTable.NT 16, ( result, TILDE1left, aexp1right), rest671)
end
|  ( 63, ( ( _, ( MlyValue.aexp aexp1, _, aexp1right)) :: ( _, ( 
MlyValue.ADDSYM ADDSYM1, ADDSYM1left, _)) :: rest671)) => let val  
result = MlyValue.aexp (fn _ => let val  ADDSYM1 = ADDSYM1 ()
 val  aexp1 = aexp1 ()
 in ()
end)
 in ( LrTable.NT 16, ( result, ADDSYM1left, aexp1right), rest671)
end
|  ( 64, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.ml_symbol 
ml_symbol1, _, _)) :: _ :: ( _, ( _, DEFINED1left, _)) :: rest671)) =>
 let val  result = MlyValue.boolexp (fn _ => let val  ml_symbol1 = 
ml_symbol1 ()
 in ()
end)
 in ( LrTable.NT 17, ( result, DEFINED1left, RPAREN1right), rest671)

end
|  ( 65, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.sym sym1, _,
 _)) :: _ :: ( _, ( _, DEFINED1left, _)) :: rest671)) => let val  
result = MlyValue.boolexp (fn _ => let val  sym1 = sym1 ()
 in ()
end)
 in ( LrTable.NT 17, ( result, DEFINED1left, RPAREN1right), rest671)

end
|  ( 66, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.boolexp 
boolexp1, _, _)) :: ( _, ( _, LPAREN1left, _)) :: rest671)) => let
 val  result = MlyValue.boolexp (fn _ => let val  boolexp1 = boolexp1
 ()
 in ()
end)
 in ( LrTable.NT 17, ( result, LPAREN1left, RPAREN1right), rest671)

end
|  ( 67, ( ( _, ( MlyValue.boolexp boolexp2, _, boolexp2right)) :: _
 :: ( _, ( MlyValue.boolexp boolexp1, boolexp1left, _)) :: rest671))
 => let val  result = MlyValue.boolexp (fn _ => let val  boolexp1 = 
boolexp1 ()
 val  boolexp2 = boolexp2 ()
 in ()
end)
 in ( LrTable.NT 17, ( result, boolexp1left, boolexp2right), rest671)

end
|  ( 68, ( ( _, ( MlyValue.boolexp boolexp2, _, boolexp2right)) :: _
 :: ( _, ( MlyValue.boolexp boolexp1, boolexp1left, _)) :: rest671))
 => let val  result = MlyValue.boolexp (fn _ => let val  boolexp1 = 
boolexp1 ()
 val  boolexp2 = boolexp2 ()
 in ()
end)
 in ( LrTable.NT 17, ( result, boolexp1left, boolexp2right), rest671)

end
|  ( 69, ( ( _, ( MlyValue.boolexp boolexp2, _, boolexp2right)) :: ( _
, ( MlyValue.EQSYM EQSYM1, _, _)) :: ( _, ( MlyValue.boolexp boolexp1,
 boolexp1left, _)) :: rest671)) => let val  result = MlyValue.boolexp
 (fn _ => let val  boolexp1 = boolexp1 ()
 val  EQSYM1 = EQSYM1 ()
 val  boolexp2 = boolexp2 ()
 in ()
end)
 in ( LrTable.NT 17, ( result, boolexp1left, boolexp2right), rest671)

end
|  ( 70, ( ( _, ( MlyValue.boolexp boolexp1, _, boolexp1right)) :: ( _
, ( _, NOT1left, _)) :: rest671)) => let val  result = 
MlyValue.boolexp (fn _ => let val  boolexp1 = boolexp1 ()
 in ()
end)
 in ( LrTable.NT 17, ( result, NOT1left, boolexp1right), rest671)
end
|  ( 71, ( ( _, ( MlyValue.aexp aexp2, _, aexp2right)) :: ( _, ( 
MlyValue.INEQSYM INEQSYM1, _, _)) :: ( _, ( MlyValue.aexp aexp1, 
aexp1left, _)) :: rest671)) => let val  result = MlyValue.boolexp (fn
 _ => let val  aexp1 = aexp1 ()
 val  INEQSYM1 = INEQSYM1 ()
 val  aexp2 = aexp2 ()
 in ()
end)
 in ( LrTable.NT 17, ( result, aexp1left, aexp2right), rest671)
end
|  ( 72, ( ( _, ( MlyValue.aexp aexp2, _, aexp2right)) :: ( _, ( 
MlyValue.EQSYM EQSYM1, _, _)) :: ( _, ( MlyValue.aexp aexp1, aexp1left
, _)) :: rest671)) => let val  result = MlyValue.boolexp (fn _ => let
 val  aexp1 = aexp1 ()
 val  EQSYM1 = EQSYM1 ()
 val  aexp2 = aexp2 ()
 in ()
end)
 in ( LrTable.NT 17, ( result, aexp1left, aexp2right), rest671)
end
|  ( 73, ( ( _, ( MlyValue.ML_ID ML_ID1, _, ML_ID1right)) :: ( _, ( _,
 STRUCTURE1left, _)) :: rest671)) => let val  result = 
MlyValue.ml_symbol (fn _ => let val  ML_ID1 = ML_ID1 ()
 in ()
end)
 in ( LrTable.NT 19, ( result, STRUCTURE1left, ML_ID1right), rest671)

end
|  ( 74, ( ( _, ( MlyValue.ML_ID ML_ID1, _, ML_ID1right)) :: ( _, ( _,
 SIGNATURE1left, _)) :: rest671)) => let val  result = 
MlyValue.ml_symbol (fn _ => let val  ML_ID1 = ML_ID1 ()
 in ()
end)
 in ( LrTable.NT 19, ( result, SIGNATURE1left, ML_ID1right), rest671)

end
|  ( 75, ( ( _, ( MlyValue.ML_ID ML_ID1, _, ML_ID1right)) :: ( _, ( _,
 FUNCTOR1left, _)) :: rest671)) => let val  result = 
MlyValue.ml_symbol (fn _ => let val  ML_ID1 = ML_ID1 ()
 in ()
end)
 in ( LrTable.NT 19, ( result, FUNCTOR1left, ML_ID1right), rest671)

end
|  ( 76, ( ( _, ( MlyValue.ML_ID ML_ID1, _, ML_ID1right)) :: ( _, ( _,
 FUNSIG1left, _)) :: rest671)) => let val  result = MlyValue.ml_symbol
 (fn _ => let val  ML_ID1 = ML_ID1 ()
 in ()
end)
 in ( LrTable.NT 19, ( result, FUNSIG1left, ML_ID1right), rest671)
end
|  ( 77, ( ( _, ( MlyValue.FILE_STANDARD FILE_STANDARD1, 
FILE_STANDARD1left, FILE_STANDARD1right)) :: rest671)) => let val  
result = MlyValue.pathname (fn _ => let val  (FILE_STANDARD as 
FILE_STANDARD1) = FILE_STANDARD1 ()
 in (CMSemantic.StandardPathName FILE_STANDARD)
end)
 in ( LrTable.NT 21, ( result, FILE_STANDARD1left, FILE_STANDARD1right
), rest671)
end
|  ( 78, ( ( _, ( MlyValue.FILE_NATIVE FILE_NATIVE1, FILE_NATIVE1left,
 FILE_NATIVE1right)) :: rest671)) => let val  result = 
MlyValue.pathname (fn _ => let val  (FILE_NATIVE as FILE_NATIVE1) = 
FILE_NATIVE1 ()
 in (CMSemantic.NativePathName FILE_NATIVE)
end)
 in ( LrTable.NT 21, ( result, FILE_NATIVE1left, FILE_NATIVE1right), 
rest671)
end
|  ( 79, ( ( _, ( MlyValue.pathname pathname1, pathname1left, 
pathname1right)) :: rest671)) => let val  result = MlyValue.srcfile
 (fn _ => let val  pathname1 = pathname1 ()
 in ()
end)
 in ( LrTable.NT 29, ( result, pathname1left, pathname1right), rest671
)
end
|  ( 80, ( ( _, ( MlyValue.srcfile srcfile1, srcfile1left, 
srcfile1right)) :: rest671)) => let val  result = MlyValue.srcfiles
 (fn _ => let val  srcfile1 = srcfile1 ()
 in ()
end)
 in ( LrTable.NT 30, ( result, srcfile1left, srcfile1right), rest671)

end
|  ( 81, ( ( _, ( _, DASH1left, DASH1right)) :: rest671)) => let val  
result = MlyValue.srcfiles (fn _ => ())
 in ( LrTable.NT 30, ( result, DASH1left, DASH1right), rest671)
end
| _ => raise (mlyAction i392)
end
val void = MlyValue.VOID
val extract = fn a => (fn MlyValue.description x => x
| _ => let exception ParseInternal
	in raise ParseInternal end) a ()
end
end
structure Tokens : CM_TOKENS =
struct
type svalue = ParserData.svalue
type ('a,'b) token = ('a,'b) Token.token
fun EOF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 0,(
ParserData.MlyValue.VOID,p1,p2))
fun FILE_STANDARD (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 1,(
ParserData.MlyValue.FILE_STANDARD (fn () => i),p1,p2))
fun FILE_NATIVE (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 2,(
ParserData.MlyValue.FILE_NATIVE (fn () => i),p1,p2))
fun CM_ID (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 3,(
ParserData.MlyValue.CM_ID (fn () => i),p1,p2))
fun ML_ID (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 4,(
ParserData.MlyValue.ML_ID (fn () => i),p1,p2))
fun NUMBER (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 5,(
ParserData.MlyValue.NUMBER (fn () => i),p1,p2))
fun GROUP (p1,p2) = Token.TOKEN (ParserData.LrTable.T 6,(
ParserData.MlyValue.VOID,p1,p2))
fun LIBRARY (p1,p2) = Token.TOKEN (ParserData.LrTable.T 7,(
ParserData.MlyValue.VOID,p1,p2))
fun ALIAS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 8,(
ParserData.MlyValue.VOID,p1,p2))
fun IS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 9,(
ParserData.MlyValue.VOID,p1,p2))
fun LPAREN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 10,(
ParserData.MlyValue.VOID,p1,p2))
fun RPAREN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 11,(
ParserData.MlyValue.VOID,p1,p2))
fun COLON (p1,p2) = Token.TOKEN (ParserData.LrTable.T 12,(
ParserData.MlyValue.VOID,p1,p2))
fun IF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 13,(
ParserData.MlyValue.VOID,p1,p2))
fun ELIF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 14,(
ParserData.MlyValue.VOID,p1,p2))
fun ELSE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 15,(
ParserData.MlyValue.VOID,p1,p2))
fun ENDIF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 16,(
ParserData.MlyValue.VOID,p1,p2))
fun ERROR (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 17,(
ParserData.MlyValue.ERROR (fn () => i),p1,p2))
fun STRUCTURE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 18,(
ParserData.MlyValue.VOID,p1,p2))
fun SIGNATURE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 19,(
ParserData.MlyValue.VOID,p1,p2))
fun FUNCTOR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 20,(
ParserData.MlyValue.VOID,p1,p2))
fun FUNSIG (p1,p2) = Token.TOKEN (ParserData.LrTable.T 21,(
ParserData.MlyValue.VOID,p1,p2))
fun DEFINED (p1,p2) = Token.TOKEN (ParserData.LrTable.T 22,(
ParserData.MlyValue.VOID,p1,p2))
fun ADDSYM (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 23,(
ParserData.MlyValue.ADDSYM (fn () => i),p1,p2))
fun MULSYM (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 24,(
ParserData.MlyValue.MULSYM (fn () => i),p1,p2))
fun EQSYM (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 25,(
ParserData.MlyValue.EQSYM (fn () => i),p1,p2))
fun INEQSYM (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 26,(
ParserData.MlyValue.INEQSYM (fn () => i),p1,p2))
fun TILDE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 27,(
ParserData.MlyValue.VOID,p1,p2))
fun ANDALSO (p1,p2) = Token.TOKEN (ParserData.LrTable.T 28,(
ParserData.MlyValue.VOID,p1,p2))
fun ORELSE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 29,(
ParserData.MlyValue.VOID,p1,p2))
fun NOT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 30,(
ParserData.MlyValue.VOID,p1,p2))
fun STAR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 31,(
ParserData.MlyValue.VOID,p1,p2))
fun DASH (p1,p2) = Token.TOKEN (ParserData.LrTable.T 32,(
ParserData.MlyValue.VOID,p1,p2))
fun SOURCE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 33,(
ParserData.MlyValue.VOID,p1,p2))
end
end
