/* Linear rational and (linear) real arithmetic.

Both procedures are instances of the generic normalisation of
`Stdlib.LinArith`, exactly like `LIA.lp` is for ℤ.  Only three things are
theory-specific and appear here:

  - the `Lin` structure and the proof of its eight laws,
  - the decidable test for a null coefficient,
  - the reification, which is by nature syntactic.

  * ℚ is the one-sorted instance: coefficients and values are both `rat`.

  * The reals of `Real.lp` are the two-sorted instance: the values live in
    the abstract `real`, where nothing computes, while the coefficients
    are *rationals*, where everything computes.  The two are related by
    the embedding `ofQ : ℚ → τ real`. */

require Stdlib.Nat as Nat;
open Stdlib.Nat;
require open Stdlib.LinArith;
require open Stdlib.Z;
require open Stdlib.Q;
require open Stdlib.Real;
require open Stdlib.List;

// ===========================================================================
// Deciding whether a rational is null
//
// `ᵣ≐` already compares two rationals by cross-multiplication and it
// computes on normalised fractions, so the test and its soundness proof
// come for free from `ᵣ≐_decides`.
// ===========================================================================

opaque symbol isEq_Eq c : π (istrue (isEq c) ⇒ c = Eq) ≔
begin
  induction
  { assume h; reflexivity }
  { assume h; apply ⊥ₑ h }
  { assume h; apply ⊥ₑ h }
end;

symbol Qis0 (q : ℚ) : 𝔹 ≔ isEq (q ᵣ≐ (0 / 1));

opaque symbol Qis0_sound q : π (istrue (Qis0 q) ⇒ q = 0 / 1) ≔
begin
  assume q h;
  refine ᵣ≐_decides q (0 / 1) (isEq_Eq (q ᵣ≐ (0 / 1)) h)
end;

// 0 is absorbing for the rational product (missing from Q.lp).
opaque symbol ᵣ*_absorb_l x : π ((0 / 1) *ᵣ x = 0 / 1) ≔
begin
  refine ind_Rat (λ u, ((0 / 1) *ᵣ u) = 0 / 1) _;
  assume n d;
  refine div_0_num _
end;

/* `ᵣ-` is declared in Q.lp without any rule.  The reification below needs
   to know what a subtraction is, so we give it its definition here. */
rule $x ᵣ- $y ↪ $x ᵣ+ (—ᵣ $y);

// ===========================================================================
// ℚ as a `Lin` structure
// ===========================================================================

constant symbol Qlin : Lin;

rule scal Qlin ↪ rat;
rule carr Qlin ↪ rat;

rule s0 Qlin ↪ 0 / 1
with sadd Qlin ↪ (ᵣ+)
with smul Qlin ↪ (*ᵣ)
with snull Qlin ↪ Qis0
with v0 Qlin ↪ 0 / 1
with vadd Qlin ↪ (ᵣ+)
with act Qlin ↪ (*ᵣ)
with emb Qlin ↪ λ x, x;

opaque symbol QlinAx : π (LinAx Qlin) ≔
begin
  refine ∧ᵢ _ (∧ᵢ _ (∧ᵢ _ (∧ᵢ _ (∧ᵢ _ (∧ᵢ _ (∧ᵢ _ _))))))
  // (x + y) + z = x + (y + z)
  { assume x y z; refine ᵣ+_assoc x y z }
  // x + y = y + x
  { assume x y; refine ᵣ+_com x y }
  // 0 + x = x
  { assume x; refine ᵣ+_neutral_div_l x }
  // (j + k) * x = j * x + k * x
  { assume j k x;
    simplify;
    rewrite ᵣ*_com (j ᵣ+ k) x;
    rewrite ᵣdistr*+;
    rewrite ᵣ*_com x j;
    rewrite ᵣ*_com x k;
    reflexivity }
  // constants: the embedding is the identity
  { assume j k; reflexivity }
  // 0 * x = 0
  { assume x; refine ᵣ*_absorb_l x }
  { reflexivity }
  // the zero test is sound
  { assume k; refine Qis0_sound k }
end;

symbol valQ ≔ lval Qlin;
symbol normQ ≔ norm Qlin;

// ===========================================================================
// Reification of a rational expression
//
// A rational in normal form is headed by `/`, so a `/`-term is a constant
// and anything else that is not an addition, an opposite, a subtraction or
// a product by a constant is abstracted by a variable.
// WARNING: rfyQ is sequential.
// ===========================================================================

sequential symbol rfyQ : τ (list rat) → ℚ → τ (lexpr Qlin);

// addition
rule rfyQ $l ($x ᵣ+ $y) ↪
  let x ≔ rfyQ $l $x in let y ≔ rfyQ (x ₂) $y in ((x ₁) ++ (y ₁)) ‚ (y ₂)

// opposite and subtraction
with rfyQ $l (—ᵣ $x) ↪
  let x ≔ rfyQ $l $x in (scale Qlin ((— 1) / 1) (x ₁)) ‚ (x ₂)
with rfyQ $l ($x ᵣ- $y) ↪ rfyQ $l ($x ᵣ+ (—ᵣ $y))

// multiplication by a constant
with rfyQ $l (($n / $d) *ᵣ $x) ↪
  let x ≔ rfyQ $l $x in (scale Qlin ($n / $d) (x ₁)) ‚ (x ₂)
with rfyQ $l ($x *ᵣ ($n / $d)) ↪
  let x ≔ rfyQ $l $x in (scale Qlin ($n / $d) (x ₁)) ‚ (x ₂)

// constants
with rfyQ $l ($n / $d) ↪ (Cst ($n / $d) ⸬ □) ‚ $l

// other cases are abstracted by a variable
with rfyQ $l $x ↪
  case_Loc (lookup Stdlib.Nat._0 $x $l)
    (λ i, (Var i (1 / 1) ⸬ □) ‚ $l)
    (λ i, (Var i (1 / 1) ⸬ □) ‚ ($l ++ ($x ⸬ □)))
;

symbol reifyQ ≔ rfyQ □;

opaque symbol reify_correctQ x : π (valQ (reifyQ x) = x) ≔
begin
  refine ind_Rat (λ u, valQ (reifyQ u) = u) _;
  assume n d;
  refine ᵣ+_neutral_div_r _
end;

opaque symbol norm_correctQ_env (x : 𝕃 (grp rat)) l :
  π (valQ ((normQ x) ‚ l) = valQ (x ‚ l)) ≔
begin
  assume x l; refine norm_correct Qlin QlinAx x l
end;

opaque symbol norm_correctQ (e : τ (lexpr Qlin)) :
  π (valQ ((normQ (e ₁)) ‚ (e ₂)) = valQ e) ≔
begin
  assume e;
  rewrite norm_correctQ_env;
  symmetry;
  refine feq valQ (eta_prod e)
end;

// The reflection tactic at work on ℚ: both sides reify to the same normal
// form, so the goal closes by `reflexivity`.
opaque symbol fooQ (X : ℚ) :
  π ((((— 1) / 1) *ᵣ ((((— 1) / 1)) ᵣ+ X)) = ((1 / 1) ᵣ+ ((((— 1) / 1)) *ᵣ X))) ≔
begin
  assume X;
  rewrite left .[x in x = _] reify_correctQ;
  rewrite left .[x in _ = x] reify_correctQ;
  rewrite left norm_correctQ (reifyQ ((((— 1) / 1)) *ᵣ ((((— 1) / 1)) ᵣ+ X)));
  rewrite left norm_correctQ (reifyQ ((1 / 1) ᵣ+ ((((— 1) / 1)) *ᵣ X)));
  reflexivity
end;

// ===========================================================================
// The reals of Real.lp
//
// `Real.lp` axiomatises a complete ordered field; ℚ embeds into any such
// field.  `ofQ` is that embedding.  It is deliberately a symbol *without*
// rewrite rules: the reification has to recognise it in a left-hand side.
//
// The three statements below are the only new axioms of this file.  They
// hold in every model of the axioms of `Real.lp` (a field of
// characteristic zero contains a copy of ℚ) and they are exactly the
// morphism laws needed by `LinAx`.
// ===========================================================================

symbol ofQ : ℚ → τ real;

symbol ofQ_zero : π (ofQ (0 / 1) = zero);
symbol ofQ_one : π (ofQ (1 / 1) = one);
symbol ofQ_add j k : π (ofQ (j ᵣ+ k) = add (ofQ j) (ofQ k));

constant symbol Rlin : Lin;

rule scal Rlin ↪ rat;
rule carr Rlin ↪ real;

rule s0 Rlin ↪ 0 / 1
with sadd Rlin ↪ (ᵣ+)
with smul Rlin ↪ (*ᵣ)
with snull Rlin ↪ Qis0
with v0 Rlin ↪ zero
with vadd Rlin ↪ add
with act Rlin ↪ λ k x, mul (ofQ k) x
with emb Rlin ↪ ofQ;

opaque symbol RlinAx : π (LinAx Rlin) ≔
begin
  refine ∧ᵢ _ (∧ᵢ _ (∧ᵢ _ (∧ᵢ _ (∧ᵢ _ (∧ᵢ _ (∧ᵢ _ _))))))
  // (x + y) + z = x + (y + z)
  { assume x y z;
    refine leibniz_of_eq (add (add x y) z) (add x (add y z))
             (eq_sym' (add x (add y z)) (add (add x y) z) (add_associative x y z)) }
  // x + y = y + x
  { assume x y; refine leibniz_of_eq (add x y) (add y x) (add_commutative x y) }
  // 0 + x = x
  { assume x; refine leibniz_of_eq (add zero x) x (add_zero_left x) }
  // (j + k) · x = j · x + k · x
  { assume j k x;
    refine leibniz_of_eq (mul (ofQ (j ᵣ+ k)) x) (add (mul (ofQ j) x) (mul (ofQ k) x))
      (eq_tr (mul (ofQ (j ᵣ+ k)) x) (mul (add (ofQ j) (ofQ k)) x)
             (add (mul (ofQ j) x) (mul (ofQ k) x))
        (mul_cong_l x (ofQ (j ᵣ+ k)) (add (ofQ j) (ofQ k))
           (eq_of_leibniz (ofQ (j ᵣ+ k)) (add (ofQ j) (ofQ k)) (ofQ_add j k)))
        (mul_distributive_left (ofQ j) (ofQ k) x)) }
  // the embedding is additive
  { assume j k; refine ofQ_add j k }
  // 0 · x = 0
  { assume x;
    refine leibniz_of_eq (mul (ofQ (0 / 1)) x) zero
      (eq_tr (mul (ofQ (0 / 1)) x) (mul zero x) zero
        (mul_cong_l x (ofQ (0 / 1)) zero
           (eq_of_leibniz (ofQ (0 / 1)) zero ofQ_zero))
        (mul_zero_l x)) }
  // the embedding maps 0 to 0
  { refine ofQ_zero }
  // the zero test is sound
  { assume k; refine Qis0_sound k }
end;

symbol valR ≔ lval Rlin;
symbol normR ≔ norm Rlin;

// ===========================================================================
// Reification of a real expression
//
// `add`, `opp`, `zero`, `one` and the rational constants `ofQ k` are
// recognised.  For a product neither factor is syntactically a constant in
// general (`two` for instance unfolds to `add one one`), so both factors
// are reified and normalised first: if one of them turns out to be a
// single constant monomial the product is linear, otherwise the whole
// product is abstracted by a variable.
// WARNING: rfyR and mulcomb are sequential.
// ===========================================================================

sequential symbol mulcomb :
  𝕃 (grp rat) → 𝕃 (grp rat) → 𝕃 real → τ real → 𝕃 real → τ (lexpr Rlin);

// a null factor makes the product null
rule mulcomb □ _ _ _ $l ↪ (□ ‚ $l)
with mulcomb _ □ _ _ $l ↪ (□ ‚ $l)
// one of the factors is a constant: the product is linear
with mulcomb (Cst $k ⸬ □) $ys $e _ _ ↪ (scale Rlin $k $ys) ‚ $e
with mulcomb $xs (Cst $k ⸬ □) $e _ _ ↪ (scale Rlin $k $xs) ‚ $e
// otherwise the product is not linear: abstract it
with mulcomb _ _ _ $t $l ↪
     case_Loc (lookup Stdlib.Nat._0 $t $l)
       (λ i, (Var i (1 / 1) ⸬ □) ‚ $l)
       (λ i, (Var i (1 / 1) ⸬ □) ‚ ($l ++ ($t ⸬ □)));

sequential symbol rfyR : 𝕃 real → τ real → τ (lexpr Rlin);

// addition
rule rfyR $l (add $x $y) ↪
  let a ≔ rfyR $l $x in let b ≔ rfyR (a ₂) $y in ((a ₁) ++ (b ₁)) ‚ (b ₂)

// opposite
with rfyR $l (opp $x) ↪
  let a ≔ rfyR $l $x in (scale Rlin ((— 1) / 1) (a ₁)) ‚ (a ₂)

// constants
with rfyR $l zero ↪ (□ ‚ $l)
with rfyR $l one ↪ ((Cst (1 / 1)) ⸬ □) ‚ $l
with rfyR $l (ofQ $k) ↪ ((Cst $k) ⸬ □) ‚ $l

// product: linear only if one of the factors is constant
with rfyR $l (mul $x $y) ↪
  let a ≔ rfyR $l $x in let b ≔ rfyR (a ₂) $y in
    mulcomb (norm Rlin (a ₁)) (norm Rlin (b ₁)) (b ₂) (mul $x $y) $l

// other cases are abstracted by a variable
with rfyR $l $x ↪
  case_Loc (lookup Stdlib.Nat._0 $x $l)
    (λ i, (Var i (1 / 1) ⸬ □) ‚ $l)
    (λ i, (Var i (1 / 1) ⸬ □) ‚ ($l ++ ($x ⸬ □)))
;

symbol reifyR ≔ rfyR □;

/* As in `LIA.lp`, this is the bridge between a term and its reification.
   Note that the reals have no induction principle: the proof below is the
   variable case, which is the only rule of `rfyR` that applies to the
   universally quantified `x`. */
opaque symbol reify_correctR x : π (valR (reifyR x) = x) ≔
begin
  assume x;
  refine leibniz_of_eq (add (mul (ofQ (1 / 1)) x) zero) x
    (eq_tr (add (mul (ofQ (1 / 1)) x) zero) (add x zero) x
      (add_cong_l zero (mul (ofQ (1 / 1)) x) x
        (eq_tr (mul (ofQ (1 / 1)) x) (mul one x) x
          (mul_cong_l x (ofQ (1 / 1)) one
             (eq_of_leibniz (ofQ (1 / 1)) one ofQ_one))
          (mul_one_left x)))
      (add_zero_r x))
end;

opaque symbol norm_correctR_env (x : 𝕃 (grp rat)) l :
  π (valR ((normR x) ‚ l) = valR (x ‚ l)) ≔
begin
  assume x l; refine norm_correct Rlin RlinAx x l
end;

opaque symbol norm_correctR (e : τ (lexpr Rlin)) :
  π (valR ((normR (e ₁)) ‚ (e ₂)) = valR e) ≔
begin
  assume e;
  rewrite norm_correctR_env;
  symmetry;
  refine feq valR (eta_prod e)
end;

// The reflection tactic at work on the reals: −1·(−1+X) = 1+(−1·X).
opaque symbol fooR (X : τ real) :
  π (mul (opp one) (add (opp one) X) = add one (mul (opp one) X)) ≔
begin
  assume X;
  rewrite left .[x in x = _] reify_correctR;
  rewrite left .[x in _ = x] reify_correctR;
  rewrite left norm_correctR (reifyR (mul (opp one) (add (opp one) X)));
  rewrite left norm_correctR (reifyR (add one (mul (opp one) X)));
  reflexivity
end;

// `two` is not a constant of the language: it unfolds to `1 + 1`, which
// the reification adds up.  Here `2·X + (−X) = X`.
opaque symbol fooR2 (X : τ real) :
  π (add (mul two X) (opp X) = X) ≔
begin
  assume X;
  rewrite left .[x in x = _] reify_correctR;
  rewrite left .[x in _ = x] reify_correctR;
  rewrite left norm_correctR (reifyR (add (mul two X) (opp X)));
  rewrite left norm_correctR (reifyR X);
  reflexivity
end;
