// define a type representing Lambdapi tactics

require open Stdlib.Set Stdlib.Prop Stdlib.List;

constant symbol String : TYPE;
builtin "String" ≔ String;

constant symbol string : Set;
rule τ string ↪ String;

type "hello world!";

compute "hello world!";

assert ⊢ "a" : String;

assert ⊢ "a" ≡ "a";

assertnot ⊢ "a" ≡ "b";

constant symbol Tactic : TYPE;
 symbol tactic : Set;
 rule τ tactic ↪ Tactic;

constant symbol #admit : Tactic;
builtin "admit" ≔ #admit;

symbol and : Tactic → Tactic → Tactic;
builtin "and" ≔ and;
notation and infix right 15;

constant symbol #apply [p] : π p → Tactic;
builtin "apply" ≔ #apply;

constant symbol #assume : String → Tactic;
builtin "assume" ≔ #assume;

constant symbol #fail : Tactic;
builtin "fail" ≔ #fail;

constant symbol #generalize : Π [a], τ a → Tactic;
builtin "generalize" ≔ #generalize;

constant symbol #have : String → Π p, π p → Tactic;
builtin "have" ≔ #have;

constant symbol #induction : Tactic;
builtin "induction" ≔ #induction;

constant symbol #orelse : Tactic → Tactic → Tactic;
builtin "orelse" ≔ #orelse;
notation #orelse infix left 10;


constant symbol #refine : String → Tactic;
builtin "refine" ≔ #refine;

constant symbol #reflexivity : Tactic;
builtin "reflexivity" ≔ #reflexivity;

constant symbol #remove : Π [a], π a → Tactic;
builtin "remove" ≔ #remove;

constant symbol #repeat : Tactic → Tactic;
builtin "repeat" ≔ #repeat;

constant symbol #rewrite_gen : String → String → Π [p], π p → Tactic;
builtin "rewrite" ≔ #rewrite_gen;

symbol #rewrite : Π [p], π p → Tactic ≔ @#rewrite_gen "" "";

constant symbol #set : String → Π [a], τ a → Tactic;
builtin "set" ≔ #set;

constant symbol #simplify : /* Π [a], τ a → */ Tactic;
builtin "simplify" ≔ #simplify;

constant symbol #simplify_beta : Tactic;
builtin "simplify rule off" ≔ #simplify_beta;

constant symbol #solve : Tactic;
builtin "solve" ≔ #solve;

constant symbol #symmetry : Tactic;
builtin "symmetry" ≔ #symmetry;

constant symbol #try : Tactic → Tactic;
builtin "try" ≔ #try;

constant symbol #why3 : /*τ (option string) →*/ Tactic;
builtin "why3" ≔ #why3;

constant symbol #change [p] : π p → Tactic;
builtin "change" ≔ #change;

/*****************************************************************************/

symbol nothing ≔ #try #fail;

require open Stdlib.Nat;

symbol do : ℕ → Tactic → Tactic;

rule do 0 _ ↪ nothing
with do ($n +1) $t ↪ $t and (do $n $t);

require open Stdlib.Eq;

symbol lem1 x y z t : π (((x + y) + z) + t = x + (y + (z + t))) ≔
begin
  assume x;
  eval #generalize x;
  //assume x y z t;
  //compute #assume "x" & #assume "y" & #assume "z" & #assume "t";
  eval #assume "x" and #assume "y" and #assume "z" and #assume "t";
  //rewrite addnA; rewrite addnA; reflexivity
  //compute 2 * #rewrite addnA;
  eval do 2 (#rewrite addnA) and #reflexivity;
end;

symbol lem2 p : π p → π p ≔
begin
  assume p h; eval #refine "h"
end;

