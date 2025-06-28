require open Stdlib.Nat  Stdlib.Pos Stdlib.Prod Stdlib.Set Stdlib.List Stdlib.Eq Stdlib.Prop Stdlib.FOL Stdlib.Bool Stdlib.Comp;

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