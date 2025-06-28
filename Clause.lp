require open Stdlib.Bool Stdlib.List Stdlib.Prop Stdlib.Eq Stdlib.HOL Stdlib.Prod Stdlib.Nat  Stdlib.Set Stdlib.Impred Stdlib.Comp;

inductive Clause: TYPE ≔
| P: ℕ → Clause;

symbol cl: Set;
rule τ cl ↪ Clause;

constant symbol R : TYPE;
constant symbol Index : ℕ → R;
constant symbol New : ℕ → R;

symbol case [a] : R → (ℕ → τ a) → (ℕ → τ a) → τ a;

rule case (Index $i) $f _ ↪ $f $i
with case (New $i) _ $g ↪ $g $i;

/* index of a value in a list: returns New if the value is not
definitionally equivalent to some element of the list */

sequential symbol index: ℕ → Π [a], τ a → τ(list a) → R;

rule index $k $x □ ↪ New $k
with index $k $x ($x ⸬ _) ↪ Index $k
with index $k $x ($y ⸬ $l) ↪ index ($k +1) $x $l;

sequential symbol get_map_aux : τ (list o) → 𝕃 o → τ (list o);
rule get_map_aux $ctx □ ↪ $ctx
with get_map_aux $ctx ($x ⸬ $xs) ↪ 
    let ctx' ≔ case (index _0 $x $ctx)  (λ (i: τ nat), $ctx) (λ (i: τ nat), ($ctx ++ ($x ⸬ □))) in
        get_map_aux ctx' $xs
;

symbol get_map l ≔ get_map_aux □ l;

sequential symbol propeq: Prop → Prop → 𝔹;
rule propeq $x $x ↪ true
with propeq $x $y ↪ false;

sequential symbol reify : τ (list o) → 𝕃 o → τ (list cl);

rule reify $ctx □ ↪ □
with reify $ctx ($x ⸬ $xs) ↪ 
    P (find (λ x, propeq x $x) $ctx ) ⸬ (reify $ctx $xs)
;

symbol nth ≔ nth ⊥;

symbol compN : ℕ → ℕ → Comp;

rule compN _0 _0 ↪ Eq
with compN _0 (_ +1) ↪ Lt
with compN (_ +1) _0 ↪ Gt
with compN ($x +1) ($y +1) ↪ compN $x $y;

symbol den: τ (list o) → τ (list cl) → Prop;
rule den _ □ ↪  ⊥
with den $l ((P $i) ⸬ $xs) ↪ (nth $l $i) ∨ (den $l $xs);

symbol insert: Clause → τ(list cl) → τ(list cl);
rule insert $x □ ↪ $x ⸬ □
with insert (P $i) ((P $j) ⸬ $l) ↪
    case_Comp (compN $i $j)
        ((P $i) ⸬ (P $j) ⸬ $l)
        ((P $i) ⸬ (P $j) ⸬ $l)
        ((P $j) ⸬ (insert (P $i) $l))
;

private symbol a: Prop;
private symbol b: Prop;
private symbol c: Prop;
private symbol d: Prop;

private symbol σ ≔ get_map (a ⸬ b ⸬ a ⸬ c ⸬ d ⸬ □);

compute σ;

private symbol foo ≔ a ⸬ b ⸬ a ⸬ c ⸬ d ⸬ □;

private symbol testcl ≔ reify σ (foo);

private symbol foo2 ≔ d ⸬ c ⸬ a ⸬ b ⸬ a ⸬ □;

private symbol testcl2 ≔ reify σ (foo2);

symbol norm: τ(list cl) → τ(list cl);
rule norm □ ↪ □
with norm ($x ⸬ $xs) ↪ insert $x (norm $xs);

compute norm testcl;
compute norm testcl2;

opaque symbol compN_correct x y : π (compN x y = Eq ⇒ x = y) ≔
begin
induction
{ induction
  {assume h; reflexivity}
  {assume y hy h; apply ⊥ₑ; apply Lt≠Eq h}
}
{ assume x hx; induction
  {assume h; apply ⊥ₑ; apply Gt≠Eq h}
  {assume y hy h; apply feq (+1); apply hx y h }
}
end;

symbol ∨_assoc x y z : π (((x ∨ y) ∨ z) = (x ∨ y ∨ z));

require open Stdlib.propExt;

symbol insert_correct l c cls : π (den l (insert c cls) = den l (c ⸬ cls)) ≔
begin
assume l;
induction;
assume i;
induction
{ reflexivity }
{
    induction;
    assume j xs IH;
    simplify insert;
    refine ind_Comp (λ u, (compN i j) = u ⇒  (den l (case_Comp u (P i ⸬ (P j ⸬ xs)) (P i ⸬ (P j ⸬ xs)) (P j ⸬ insert (P i) xs)) = den l (P i ⸬ (P j ⸬ xs)))) _ _ _ (compN i j) _
    {
        assume Heq;
        simplify case_Comp;
        rewrite compN_correct i j Heq;
        reflexivity
    }
    { assume Hlt; simplify case_Comp; reflexivity }
    {
        assume Hgt;
        simplify;
        rewrite IH;
        simplify;
        rewrite ∨_assoc;
        rewrite .[in x in (x ∨ _) = _] ∨_com ;
        rewrite ∨_assoc;
        reflexivity
    }
    { reflexivity }
}   
end;

symbol norm_correct l cl : π (den l (norm cl) = den l cl) ≔
begin
assume l;
induction
{ reflexivity }
{
    induction;
    assume n xs IH;
    simplify;
    rewrite left IH;
    rewrite insert_correct l (P n) (norm xs);
    reflexivity
}
end;

symbol eq_cl l c1 c2 : π (den l (norm c1) = den l (norm c2) ⇒  (den l c1 = den l c2)) ≔
begin
   assume l c1 c2;
    rewrite norm_correct l c1;
    rewrite norm_correct l c2;
    refine λ x, x;
end;

//assert ⊢ (reify (a ⸬ b ⸬ c ⸬ d ⸬ □)) ₁ ≡ ( );