/* Linear integer arithmetic.

The normalisation procedure and its correctness proof are generic and
live in `Stdlib.LinArith`; this file only provides

  - the `Lin` structure `Zlin` for ℤ and the proof `ZlinAx` of its laws,
  - the reification of ℤ terms, which is by nature syntactic,
  - the order-theoretic lemmas used by the ℤ decision procedure. */

require Stdlib.Nat as Nat;
open Stdlib.Nat;
require open Stdlib.LinArith;
require open Stdlib.Z;
require open Stdlib.List;

symbol pos2nat : ℙ → ℕ;
rule pos2nat H ↪  Stdlib.Nat._1
with pos2nat (O $p) ↪ Stdlib.Nat.double (pos2nat $p)
with pos2nat (I $p)  ↪ (Stdlib.Nat.double (pos2nat $p)) Stdlib.Nat.+ Stdlib.Nat._1;

symbol int2nat n : π (0 < (n + 1)) → ℕ;
rule int2nat Z0 _  ↪ Stdlib.Nat._0
with int2nat (Zpos $n) _  ↪ pos2nat $n;

// ===========================================================================
// ℤ as a `Lin` structure
//
// Coefficients and values are both ℤ, the action is the multiplication and
// constants embed by the identity: this is the one-sorted instance.
// ===========================================================================

symbol Zis0 : ℤ → 𝔹;

rule Zis0 Z0 ↪ true
with Zis0 (Zpos _) ↪ false
with Zis0 (Zneg _) ↪ false;

constant symbol Zlin : Lin;

rule scal Zlin ↪ int;
rule carr Zlin ↪ int;

rule s0 Zlin ↪ Z0
with sadd Zlin ↪ (+)
with smul Zlin ↪ (*)
with snull Zlin ↪ Zis0
with v0 Zlin ↪ Z0
with vadd Zlin ↪ (+)
with act Zlin ↪ (*)
with emb Zlin ↪ λ x, x;

opaque symbol ZlinAx : π (LinAx Zlin) ≔
begin
  refine ∧ᵢ _ (∧ᵢ _ (∧ᵢ _ (∧ᵢ _ (∧ᵢ _ (∧ᵢ _ (∧ᵢ _ _))))))
  // (x + y) + z = x + (y + z)
  { assume x y z; refine +_assoc x y z }
  // x + y = y + x
  { assume x y; refine +_com x y }
  // 0 + x = x
  { assume x; reflexivity }
  // (j + k) * x = j * x + k * x
  { assume j k x;
    simplify;
    rewrite *_com (j + k) x;
    rewrite *_distr_+;
    rewrite *_com x j;
    rewrite *_com x k;
    reflexivity }
  // constants: the embedding is the identity
  { assume j k; reflexivity }
  // 0 * x = 0
  { assume x; reflexivity }
  { reflexivity }
  // the zero test is sound
  { induction
    { assume h; reflexivity }
    { assume p h; apply ⊥ₑ h }
    { assume p h; apply ⊥ₑ h } }
end;

// ℤ instances of the generic operations, under their usual names.

symbol val ≔ lval Zlin;
symbol val_grp ≔ lval_grp Zlin;
symbol mul ≔ scale Zlin;              // multiplication by a constant
symbol opp ≔ scale Zlin (— 1);
symbol norm_speed ≔ norm Zlin;

symbol varmax ≔ Stdlib.LinArith.varmax Zlin;

/* The ℤ instances of the correctness lemmas.  They are restated with the
   ℤ names above — and not simply defined as `norm_correct Zlin ZlinAx` —
   so that `rewrite`, whose matching is syntactic, finds them in goals
   that mention `val`. */

opaque symbol merge_correct l g1 g2 :
  π (val ((merge Zlin g1 g2) ‚ l) = val (g1 ‚ l) + val (g2 ‚ l)) ≔
begin
  assume l g1 g2; refine Stdlib.LinArith.merge_correct Zlin ZlinAx l g1 g2
end;

opaque symbol split_correct l gs :
  π (val (((split gs ₁) ++ (split gs ₂)) ‚ l) = val (gs ‚ l)) ≔
begin
  assume l gs; refine Stdlib.LinArith.split_correct Zlin ZlinAx l gs
end;

opaque symbol mergesort_correct l g :
  π (val ((mergesort Zlin g) ‚ l) = val (g ‚ l)) ≔
begin
  assume l g; refine Stdlib.LinArith.mergesort_correct Zlin ZlinAx l g
end;

opaque symbol remove0_correct l gs :
  π (val ((remove0 Zlin gs) ‚ l) = val (gs ‚ l)) ≔
begin
  assume l gs; refine Stdlib.LinArith.remove0_correct Zlin ZlinAx l gs
end;

opaque symbol norm_correct_env (x : 𝕃 (grp int)) l :
  π (val ((norm_speed x) ‚ l) = val (x ‚ l)) ≔
begin
  assume x l; refine Stdlib.LinArith.norm_correct Zlin ZlinAx x l
end;

/* The form used by the reflection tactic: it takes the reified expression
   as a whole, so that the right-hand side `val e` is literally what the
   goal contains after `reify_correct` (no η-expansion needed there). */
opaque symbol norm_correct (e : τ (lexpr Zlin)) :
  π (val ((norm_speed (e ₁)) ‚ (e ₂)) = val e) ≔
begin
  assume e;
  rewrite norm_correct_env;
  symmetry;
  refine feq val (eta_prod e)
end;

// comparison of two monomials
symbol compG : G int → G int → Comp;

rule compG (Var $i _) (Var $j _) ↪ compN $i $j
with compG (Var _ _) (Cst _) ↪ Gt
with compG (Cst _) (Var _ _)  ↪ Lt
with compG (Cst $c1) (Cst $c2)  ↪ $c1 ≐ $c2;

//compute norm_speed ((Var Nat._3 2) ⸬ (Var Nat._2 2) ⸬ (Var Nat._1 2) ⸬ Cst 10 ⸬ □);

// ===========================================================================
// Reification: given a Lambdapi term x of type ℤ, compute an expression in
// `G int` and a list of values whose evaluation is equal to x.
// WARNING: rfy is sequential.
// ===========================================================================

sequential symbol rfy : τ (list int) → ℤ → τ (lexpr Zlin);

// addition
rule rfy $l ($x + $y) ↪
  let x ≔ rfy $l $x in let y ≔ rfy (x ₂) $y in ((x ₁) ++ (y ₁)) ‚ (y ₂)

// opposite
with rfy $l (— $x) ↪ let x ≔ rfy $l $x in opp (x ₁) ‚ (x ₂)

// substraction
with rfy $l ($x - $y) ↪ rfy $l ($x + — $y)

// constants
with rfy $l 0 ↪ (Cst 0 ⸬ □) ‚ $l
with rfy $l (Zpos $k) ↪ (Cst (Zpos $k) ⸬ □) ‚ $l
with rfy $l (Zneg $k) ↪ (Cst (Zneg $k) ⸬ □) ‚ $l

// multiplication by a constant
with rfy $l (0 * _) ↪ (Cst 0 ⸬ □) ‚ $l
with rfy $l (Zpos $k * $x) ↪ let x ≔ rfy $l $x in (mul (Zpos $k) (x ₁)) ‚ (x ₂)
with rfy $l (Zneg $k * $x) ↪ let x ≔ rfy $l $x in (mul (Zneg $k) (x ₁)) ‚ (x ₂)
with rfy $l ($x * Zpos $k) ↪ let x ≔ rfy $l $x in (mul (Zpos $k) (x ₁)) ‚ (x ₂)
with rfy $l ($x * Zneg $k) ↪ let x ≔ rfy $l $x in (mul (Zneg $k) (x ₁)) ‚ (x ₂)

//other cases are abstracted by a variable
with rfy $l $x ↪
  case_Loc (lookup Stdlib.Nat._0 $x $l)
    (λ i, (Var i 1 ⸬ □) ‚ $l)
    (λ i, (Var i 1 ⸬ □) ‚ ($l ++ ($x ⸬ □)))
;

symbol reify ≔ rfy □;

opaque symbol reify_correct x : π (val (reify x) = x) ≔
begin
induction
{reflexivity}
{reflexivity}
{reflexivity}
end;

opaque symbol reify_correct_withenv l x : π (val (rfy l x) = x) ≔
begin
assume l;
induction
{reflexivity}
{reflexivity}
{reflexivity}
end;

symbol ≐_decides_neq [x y] : π (x ≐ y ≠ Eq ⇒ x ≠ y) ≔
begin
assume x y h h2;
apply h;
rewrite h2;
remove h; remove h2; remove x;
generalize y;
induction
{reflexivity}
{
  induction
  {assume x ih; simplify; rewrite left .[x in _ = x] ih; simplify; reflexivity }
  {assume x ih; simplify; rewrite left .[x in _ = x] ih; simplify; reflexivity }
  {reflexivity}
}
{
  induction
  {assume x ih; simplify; rewrite left .[x in _ = x] ih; simplify; reflexivity }
  {assume x ih; simplify; rewrite left .[x in _ = x] ih; simplify; reflexivity }
  {reflexivity}
}
end;

// symbol l1 x y : π(((2 * x) + y) - ((2 * x) + y) ≠ 1) ≔
// begin
//   assume x y;
//   refine ≐_decides_neq _;
//   rewrite left .[z in z ≐ _] reify_correct;
//   set e ≔ reify (((2 * x) + y) - ((2 * x) + y));
//   rewrite .[z in val z] eta_prod;
//   rewrite left norm_correct (e ₁) (e ₂);
//   refine Lt≠Eq
// end;


require open Stdlib.PropExt;

symbol Zle_not_gt n m:  π ((n ≤ m) = ¬ (n > m)) ≔
begin
assume n m;
rewrite left iff_equiv_eq;
apply ∧ᵢ
{
  simplify;
  assume h;
  change π (¬ ¬ ¬ istrue (isGt (n ≐ m)));
  rewrite ¬¬ₑ_eq;
  refine h
}
{
  simplify;
  assume h1 h2;
  apply h1;
  change π (¬ ¬ istrue (isGt (n ≐ m)));
  rewrite ¬¬ₑ_eq;
  refine h2
}
end;

symbol Zlt_not_ge n m:  π ((n < m) = ¬ (n ≥ m)) ≔
begin
  assume n m;
  simplify ≥;
  simplify rule off;
  rewrite ¬¬ₑ_eq;
  reflexivity
end;

symbol Zge_not_lt : Π n: ℤ, Π m: ℤ, π ((n ≥ m) = ¬ (n < m)) ≔
begin
  assume n m;
  simplify ≥;
  simplify rule off;
  reflexivity
end;

symbol Zgt_not_le : Π n: ℤ, Π m: ℤ, π ((n > m) = ¬ (n ≤ m)) ≔
begin
  assume n m;
  simplify ≤;
  simplify rule off;
  reflexivity
end;

symbol Zmult_gt_compat c a b : π (c > 0) → π (a > b) → π (c * a > c * b) ;

symbol Zmult_ge_compat c a b : π (c > 0) → π (a ≥ b) → π (c * a ≥ c * b);

symbol Zsum_geq_s a b c d : π (a ≥ b) → π (c ≥ d) → π (a + c ≥ b + d) ≔
begin
  assume a b c d hab hcd;
  admit
end;

symbol Zgt_le_succ_r_eq a b: π ((a > b) = (a ≥ b + 1)) ≔
begin
  assume a b;
  simplify >;
  simplify rule off;
  simplify ≥;
  simplify rule off;
  refine feq (¬) _;
  rewrite left iff_equiv_eq;
  apply ∧ᵢ
  { admit}
  { admit }
end;


symbol Zinv_lt_eq a b: π ((a < b) = (— a > — b)) ≔
begin
  assume a b; rewrite left iff_equiv_eq; generalize a;
  admit
end;


symbol Zinv_le_eq a b: π ((a ≤ b) = (— a ≥ — b));
symbol Z_diff_geq_Z0_eq a b: π ((a ≥ b) = (a - b ≥ 0));
symbol Z_diff_gt_Z0_eq a b: π ((a > b) = (a - b > 0));

symbol Z_diff_eq_Z0_eq a b: π ((a = b) = (a - b = 0)) ≔
begin
  assume a b;
  rewrite left iff_equiv_eq;
  apply ∧ᵢ
  {
    assume h; rewrite h; simplify;
    apply -_same b;
  }
  {
      assume h;
      have g: π (((a - b) + b) = (0 + b)) { refine =_add_compat (a - b) 0 b h };
      have g2: π ((a + (— b + b)) = b) { rewrite left +_assoc; refine g };
      have g3: π ((a + 0) = b) { rewrite left -_same b; rewrite +_com b (— b); refine g2 };
      refine g3
    }
end;

//FIXME:
symbol Z_eq_antisym (a b: τ int):  π ((¬ (a = b)) = ¬ (a ≥ b));

symbol Zmult_eq_compat_eq (c a b: τ int) : π ((¬ (a = b)) = ¬ (c * a = c * b)) ≔
begin
 assume c a b;
 apply feq (¬);
 rewrite left iff_equiv_eq;
 apply ∧ᵢ
  { assume heq; rewrite heq; reflexivity }
  {
    assume h;
    have g2: π ((c * a) - (c * b) = 0) { rewrite h; simplify;  rewrite -_same (c * b); reflexivity };
    have g3: π (c * (a - b) = 0) { simplify;  rewrite *_distr_+; rewrite left neg_mul_r; refine g2 };
    admit
  }
end;

symbol Zmult_gt_compat_eq c a b : π (¬ (a > b) = ¬ (c * a > c * b)) ;
symbol Zmult_ge_compat_eq c a b : π (¬ (a ≥ b) = ¬ (c * a ≥ c * b)) ;

// symbol la_mult_neg_eq [t1 t2 t3] : π ((t1 < 0) ⇒ (t2 = t3) ⇒ (t1 * t2) = (t1 * t3));
// symbol la_mult_neg_lt t1 t2 t3 : π (t1 < 0) → π (t2 < t3) → π ((t1 * t2) > (t1 * t3));
// symbol la_mult_neg_leq [t1 t2 t3] : π ((t1 < 0) ⇒ (t2 ≤ t3) ⇒ (t1 * t2) ≥ (t1 * t3));
// symbol la_mult_neg_gt [t1 t2 t3] : π ((t1 < 0) ⇒ (t2 > t3) ⇒ (t1 * t2) < (t1 * t3));
// symbol la_mult_neg_ge [t1 t2 t3] : π ((t1 < 0) ⇒ (t2 ≥ t3) ⇒ (t1 * t2) ≤ (t1 * t3));

// The reflection tactic at work: both sides reify, normalise to the same
// list of monomials, and the goal closes by `reflexivity`.
symbol foo (X : τ int) :  π ((— _1 * (— _1 + X)) = (_1 + (— _1 * X))) ≔
begin
  assume X;
  rewrite left  .[x in x = _] reify_correct;
  rewrite left  .[x in _ = x] reify_correct;
  rewrite left norm_correct (reify ((— 1) * ((— 1) + X)));
  rewrite left norm_correct (reify (1 + ((— 1) * X)));
  reflexivity
end;
