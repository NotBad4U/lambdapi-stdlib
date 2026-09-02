require open Stdlib.Nat  Stdlib.Pos Stdlib.Prod Stdlib.Set Stdlib.List Stdlib.Eq Stdlib.Prop Stdlib.FOL Stdlib.Bool Stdlib.Comp;

// Stdlib.Pos now declares decimal notation for ℙ (upstream #55), which would
// otherwise capture the numeric literals below. Restore ℕ as their type.
builtin "0" ≔ Stdlib.Nat._0;
builtin "1" ≔ Stdlib.Nat._1;
builtin "2" ≔ Stdlib.Nat._2;
builtin "3" ≔ Stdlib.Nat._3;
builtin "4" ≔ Stdlib.Nat._4;
builtin "5" ≔ Stdlib.Nat._5;
builtin "6" ≔ Stdlib.Nat._6;
builtin "7" ≔ Stdlib.Nat._7;
builtin "8" ≔ Stdlib.Nat._8;
builtin "9" ≔ Stdlib.Nat._9;
builtin "10" ≔ Stdlib.Nat._10;
builtin "+" ≔ Stdlib.Nat.+;
builtin "*" ≔ Stdlib.Nat.*;

symbol split [a: Set] (l : τ (list a)): τ(list a × list a);
rule split □ ↪ (□ ‚ □)
with split ($x ⸬ □) ↪ (($x ⸬ □) ‚ □)
with split ($x ⸬ $y ⸬ $l) ↪  
    let res ≔  (split $l) in
        ($x ⸬ (res ₁)) ‚ ($y ⸬ (res ₂));


symbol merge  (l1 l2 : τ (list nat)): τ (list nat);
rule merge □ □ ↪ □
with merge □ $l2 ↪ $l2
with merge $l1 □ ↪ $l1
with merge ($a1 ⸬ $l1') ($a2 ⸬ $l2') ↪
    if ($a1 ≤ $a2) 
        ($a1 ⸬ merge $l1' ($a2 ⸬ $l2'))
        ($a2 ⸬ merge ($a1 ⸬ $l1') $l2');

symbol mergesort:  τ (list nat) →  τ (list nat);
rule mergesort □ ↪ □
with mergesort ($x ⸬ □) ↪ ($x ⸬ □)
with mergesort ($x ⸬ $y ⸬ $l) ↪ 
    let s ≔ split ($x ⸬ $y ⸬ $l) in
    let l1 ≔ s ₁ in
    let l2 ≔ s ₂ in
        merge (mergesort l1) (mergesort l2);

compute mergesort (3 ⸬ 1 ⸬ 4 ⸬ 1 ⸬ □);