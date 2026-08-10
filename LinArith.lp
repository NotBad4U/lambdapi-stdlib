/* Generic core of a linear-arithmetic reflection procedure.

This file contains everything in the decision procedure that does *not*
depend on the arithmetic being ℤ, ℚ or ℝ: the syntax of linear
expressions, their evaluation, the normalisation function (sort the
monomials by variable, merge the like ones, drop the null ones) and its
correctness proof.

The concrete theories only have to

  1. build a `Lin` structure (the operations),
  2. prove the eight `LinAx` laws,
  3. write their own reification `rfy` (which is inherently syntactic),

see `LIA.lp` (ℤ), and `LRA.lp` (ℚ and the axiomatic reals).

Two sorts are used on purpose:

  - `scal R` are the *coefficients*.  They must support a decidable test
    for zero, so this is where the computation happens.
  - `carr R` are the *values*.  Nothing is computed there; for the
    axiomatic reals of `Real.lp` there is nothing to compute anyway.

Taking `scal R = carr R` (ℤ, ℚ) recovers the usual one-sorted setting,
while the reals are handled with rational coefficients acting on an
abstract carrier. */

require Stdlib.Nat as Nat;
open Stdlib.Nat;
require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Eq Stdlib.Bool
  Stdlib.Comp Stdlib.List Stdlib.Prod;

// ===========================================================================
// The signature: a commutative monoid (carr,vadd,v0) together with an
// action of the coefficients (act) and an embedding of the constants (emb).
// ===========================================================================

constant symbol Lin : TYPE;

symbol scal : Lin → Set;                                    // coefficients
symbol carr : Lin → Set;                                    // values

symbol s0    : Π R, τ (scal R);
symbol sadd  : Π R, τ (scal R) → τ (scal R) → τ (scal R);
symbol smul  : Π R, τ (scal R) → τ (scal R) → τ (scal R);
symbol snull : Π R, τ (scal R) → 𝔹;                         // decides = s0

symbol v0    : Π R, τ (carr R);
symbol vadd  : Π R, τ (carr R) → τ (carr R) → τ (carr R);
symbol act   : Π R, τ (scal R) → τ (carr R) → τ (carr R);   // k · x
symbol emb   : Π R, τ (scal R) → τ (carr R);                // constants

// ===========================================================================
// Syntax of linear expressions
//
// A linear expression is a list of monomials — `Cst k` for a constant and
// `Var i k` for `k` times the i-th variable — paired with the list of the
// values of the variables.  Variables whose index is out of the list are
// interpreted by `v0`.
// ===========================================================================

(a : Set) inductive G : TYPE ≔
| Cst : τ a → G a
| Var : ℕ → τ a → G a;

constant symbol grp : Set → Set;
rule τ (grp $a) ↪ G $a;

// a reified expression: monomials + environment
symbol lexpr (R : Lin) : Set ≔ list (grp (scal R)) × list (carr R);

symbol lval_grp (R : Lin) : G (scal R) → 𝕃 (carr R) → τ (carr R);

rule lval_grp $R (Cst $k) _ ↪ emb $R $k
with lval_grp $R (Var $i $k) $l ↪ act $R $k (nth (v0 $R) $l $i);

symbol lval (R : Lin) : τ (lexpr R) → τ (carr R);

rule lval $R (□ ‚ _) ↪ v0 $R
with lval $R (($x ⸬ $xs) ‚ $l) ↪ vadd $R (lval_grp $R $x $l) (lval $R ($xs ‚ $l));

symbol va (R : Lin) l x ≔ lval R (x ‚ l);

// ===========================================================================
// The laws.  They are bundled in a single proposition so that a generic
// lemma only carries one extra hypothesis.
// ===========================================================================

symbol LinAx (R : Lin) : Prop ≔
    (`∀ x, `∀ y, `∀ z, vadd R (vadd R x y) z = vadd R x (vadd R y z))
  ∧ (`∀ x, `∀ y, vadd R x y = vadd R y x)
  ∧ (`∀ x, vadd R (v0 R) x = x)
  ∧ (`∀ j, `∀ k, `∀ x, act R (sadd R j k) x = vadd R (act R j x) (act R k x))
  ∧ (`∀ j, `∀ k, emb R (sadd R j k) = vadd R (emb R j) (emb R k))
  ∧ (`∀ x, act R (s0 R) x = v0 R)
  ∧ (emb R (s0 R) = v0 R)
  ∧ (`∀ k, istrue (snull R k) ⇒ k = s0 R);

// --- projections

symbol ax_assoc R (H : π (LinAx R)) x y z :
  π (vadd R (vadd R x y) z = vadd R x (vadd R y z)) ≔ ∧ₑ₁ H x y z;

symbol ax_com R (H : π (LinAx R)) x y :
  π (vadd R x y = vadd R y x) ≔ ∧ₑ₁ (∧ₑ₂ H) x y;

symbol ax_neutral R (H : π (LinAx R)) x :
  π (vadd R (v0 R) x = x) ≔ ∧ₑ₁ (∧ₑ₂ (∧ₑ₂ H)) x;

symbol ax_act_add R (H : π (LinAx R)) j k x :
  π (act R (sadd R j k) x = vadd R (act R j x) (act R k x)) ≔
  ∧ₑ₁ (∧ₑ₂ (∧ₑ₂ (∧ₑ₂ H))) j k x;

symbol ax_emb_add R (H : π (LinAx R)) j k :
  π (emb R (sadd R j k) = vadd R (emb R j) (emb R k)) ≔
  ∧ₑ₁ (∧ₑ₂ (∧ₑ₂ (∧ₑ₂ (∧ₑ₂ H)))) j k;

symbol ax_act_0 R (H : π (LinAx R)) x :
  π (act R (s0 R) x = v0 R) ≔ ∧ₑ₁ (∧ₑ₂ (∧ₑ₂ (∧ₑ₂ (∧ₑ₂ (∧ₑ₂ H))))) x;

symbol ax_emb_0 R (H : π (LinAx R)) :
  π (emb R (s0 R) = v0 R) ≔ ∧ₑ₁ (∧ₑ₂ (∧ₑ₂ (∧ₑ₂ (∧ₑ₂ (∧ₑ₂ (∧ₑ₂ H)))))) ;

symbol ax_null R (H : π (LinAx R)) k :
  π (istrue (snull R k) ⇒ k = s0 R) ≔
  ∧ₑ₂ (∧ₑ₂ (∧ₑ₂ (∧ₑ₂ (∧ₑ₂ (∧ₑ₂ (∧ₑ₂ H)))))) k;

// --- derived monoid lemmas.  Every rearrangement below goes through one
// of these three, which keeps the normalisation proofs free of positional
// rewriting.

opaque symbol ax_neutral_r R (H : π (LinAx R)) x :
  π (vadd R x (v0 R) = x) ≔
begin
  assume R H x; rewrite ax_com R H; refine ax_neutral R H x
end;

// a + (b + c) = b + (a + c)
opaque symbol ax_shuffle R (H : π (LinAx R)) a b c :
  π (vadd R a (vadd R b c) = vadd R b (vadd R a c)) ≔
begin
  assume R H a b c;
  rewrite left ax_assoc R H a b c;
  rewrite ax_com R H a b;
  rewrite ax_assoc R H b a c;
  reflexivity
end;

// (a + b) + (c + d) = (a + c) + (b + d)
opaque symbol ax_swap R (H : π (LinAx R)) a b c d :
  π (vadd R (vadd R a b) (vadd R c d) = vadd R (vadd R a c) (vadd R b d)) ≔
begin
  assume R H a b c d;
  rewrite ax_assoc R H a b (vadd R c d);
  rewrite ax_shuffle R H b c d;
  rewrite left ax_assoc R H a c (vadd R b d);
  reflexivity
end;

// ===========================================================================
// Operations on reified expressions
// ===========================================================================

// multiplication by a constant
symbol scale (R : Lin) : τ (scal R) → 𝕃 (grp (scal R)) → 𝕃 (grp (scal R));

rule scale _ _ □ ↪ □
with scale $R $k (Cst $c ⸬ $xs) ↪ Cst (smul $R $k $c) ⸬ scale $R $k $xs
with scale $R $k (Var $i $c ⸬ $xs) ↪ Var $i (smul $R $k $c) ⸬ scale $R $k $xs;

// comparison of variable indices
symbol compN : ℕ → ℕ → Comp;

rule compN _0 _0 ↪ Eq
with compN _0 (_ +1) ↪ Lt
with compN (_ +1) _0 ↪ Gt
with compN ($x +1) ($y +1) ↪ compN $x $y;

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

// splitting a list in two halves
symbol split [a : Set] (l : τ (list a)) : τ (list a × list a);

rule split □ ↪ (□ ‚ □)
with split ($x ⸬ □) ↪ (($x ⸬ □) ‚ □)
with split ($x ⸬ $y ⸬ $l) ↪
    let res ≔ split $l in (($x ⸬ (res ₁)) ‚ ($y ⸬ (res ₂)));

// merging two sorted lists of monomials
symbol merge (R : Lin) (l1 l2 : 𝕃 (grp (scal R))) : 𝕃 (grp (scal R));

rule merge _ □ $l2 ↪ $l2
with merge _ $l1 □ ↪ $l1
with merge $R (Cst $c1 ⸬ $l1) (Cst $c2 ⸬ $l2) ↪
     Cst (sadd $R $c1 $c2) ⸬ merge $R $l1 $l2
with merge $R (Cst $c ⸬ $l1) (Var $i $k ⸬ $l2) ↪
     Cst $c ⸬ merge $R $l1 (Var $i $k ⸬ $l2)
with merge $R (Var $i $k ⸬ $l1) (Cst $c ⸬ $l2) ↪
     Cst $c ⸬ merge $R (Var $i $k ⸬ $l1) $l2
with merge $R (Var $i $k1 ⸬ $l1) (Var $j $k2 ⸬ $l2) ↪
    case_Comp (compN $i $j)
        (Var $i (sadd $R $k1 $k2) ⸬ merge $R $l1 $l2)
        (Var $i $k1 ⸬ merge $R $l1 (Var $j $k2 ⸬ $l2))
        (Var $j $k2 ⸬ merge $R (Var $i $k1 ⸬ $l1) $l2);

symbol mergesort (R : Lin) : 𝕃 (grp (scal R)) → 𝕃 (grp (scal R));

rule mergesort _ □ ↪ □
with mergesort _ ($x ⸬ □) ↪ ($x ⸬ □)
with mergesort $R ($x ⸬ $y ⸬ $l) ↪
    let s ≔ split ($x ⸬ $y ⸬ $l) in
        merge $R (mergesort $R (s ₁)) (mergesort $R (s ₂));

// removing the null monomials
symbol remove0 (R : Lin) : 𝕃 (grp (scal R)) → 𝕃 (grp (scal R));

rule remove0 _ □ ↪ □
with remove0 $R (Cst $c ⸬ $l) ↪
     if (snull $R $c) (remove0 $R $l) (Cst $c ⸬ remove0 $R $l)
with remove0 $R (Var $i $c ⸬ $l) ↪
     if (snull $R $c) (remove0 $R $l) (Var $i $c ⸬ remove0 $R $l);

// the normal form
symbol norm (R : Lin) x ≔ remove0 R (mergesort R x);

// biggest variable index occurring in an expression
symbol varmax (R : Lin) : 𝕃 (grp (scal R)) → ℕ;

rule varmax $R ((Cst _) ⸬ $xs) ↪ varmax $R $xs
with varmax $R ((Var $k _) ⸬ $xs) ↪ max $k (varmax $R $xs)
with varmax _ □ ↪ _0;

// ===========================================================================
// Correctness
// ===========================================================================

opaque symbol eq_trans [a] (x y z : τ a) : π (x = y ⇒ y = z ⇒ x = z) ≔
begin
assume a x y z xy yz; rewrite xy; refine yz
end;

opaque symbol rec_𝕃 : Π [a : Set], Π l : 𝕃 a, Π p : (𝕃 a → Prop),
  π (p □) → (Π x0 : τ a, Π l' : 𝕃 a, π (p (x0 ⸬ l'))) → π (p l) ≔
begin
  assume a l P H1 H2;
  refine @ind_𝕃 a P H1 (λ x l' ih, H2 x l') l
end;

// two-step induction on lists; used for `split`
symbol list_ind2_principle [A : Set] :
  Π (P : τ (list A) → Prop),
    π (P □) →
    (Π (a : τ A), π (P (a ⸬ □))) →
    (Π (a b : τ A) (l : τ (list A)), π (P l) → π (P (a ⸬ b ⸬ l))) →
    Π (l : τ (list A)), π (P l);

opaque symbol ++_eq_+ R (H : π (LinAx R)) l x y :
  π (lval R ((x ++ y) ‚ l) = vadd R (lval R (x ‚ l)) (lval R (y ‚ l))) ≔
begin
assume R H l;
induction
{ assume y; simplify; symmetry; refine ax_neutral R H (lval R (y ‚ l)) }
{ assume x xs ih y; simplify; rewrite ih y; rewrite ax_assoc R H; reflexivity }
end;

opaque symbol split_correct R (H : π (LinAx R)) l gs :
  π (lval R (((split gs ₁) ++ (split gs ₂)) ‚ l) = lval R (gs ‚ l)) ≔
begin
assume R H l;
refine list_ind2_principle
  (λ u, (lval R (((split u ₁) ++ (split u ₂)) ‚ l) = lval R (u ‚ l))) _ _ _
{reflexivity}
{assume a; reflexivity}
{
  assume a b tl ih;
  simplify;
  rewrite ++_eq_+ R H;
  rewrite left ih;
  rewrite ++_eq_+ R H;
  simplify;
  rewrite ax_shuffle R H (lval R (split tl ₁ ‚ l)) (lval_grp R b l)
                         (lval R (split tl ₂ ‚ l));
  reflexivity
}
end;

opaque symbol merge_correct R (H : π (LinAx R)) l g1 g2 :
  π (lval R ((merge R g1 g2) ‚ l) = vadd R (lval R (g1 ‚ l)) (lval R (g2 ‚ l))) ≔
begin
    assume R H l;
    induction
    { assume g2; simplify; symmetry; refine ax_neutral R H (lval R (g2 ‚ l)) }
    {
      induction
      {
        // g1 = Cst k1 ⸬ xs
        assume k1 xs ih1;
        induction
        { simplify; symmetry; refine ax_neutral_r R H _ }
        {
          induction
          {
            // g2 = Cst k2 ⸬ ys
            assume k2 ys ih2;
            simplify;
            rewrite ax_emb_add R H;
            rewrite ih1 ys;
            refine ax_swap R H (emb R k1) (emb R k2)
                     (lval R (xs ‚ l)) (lval R (ys ‚ l))
          }
          {
            // g2 = Var j k2 ⸬ ys
            assume j k2 ys ih2;
            simplify;
            rewrite ih1;
            symmetry;
            rewrite ax_assoc R H;
            reflexivity
          }
        }
      }
      {
        // g1 = Var i k1 ⸬ xs
        assume i k1 xs ih1;
        induction
        { simplify; symmetry; refine ax_neutral_r R H _ }
        {
          induction
          {
            // g2 = Cst k2 ⸬ ys
            assume k2 ys ih2;
            simplify;
            rewrite ih2;
            refine ax_shuffle R H (emb R k2)
                     (vadd R (act R k1 (nth (v0 R) l i)) (lval R (xs ‚ l)))
                     (lval R (ys ‚ l))
          }
          {
            // g2 = Var j k2 ⸬ ys
            assume j k2 ys ih2;
            simplify;
            refine ind_Comp
              (λ u, (compN i j) = u ⇒
                 lval R (case_Comp (compN i j)
                          (Var i (sadd R k1 k2) ⸬ merge R xs ys)
                          (Var i k1 ⸬ merge R xs (Var j k2 ⸬ ys))
                          (Var j k2 ⸬ merge R (Var i k1 ⸬ xs) ys) ‚ l)
                 = vadd R (vadd R (act R k1 (nth (v0 R) l i)) (lval R (xs ‚ l)))
                          (vadd R (act R k2 (nth (v0 R) l j)) (lval R (ys ‚ l))))
              _ _ _ (compN i j) _
            {
              // i = j
              assume heq;
              rewrite heq;
              simplify;
              rewrite left compN_correct i j heq;
              rewrite ax_act_add R H;
              rewrite ih1;
              refine ax_swap R H (act R k1 (nth (v0 R) l i))
                       (act R k2 (nth (v0 R) l i))
                       (lval R (xs ‚ l)) (lval R (ys ‚ l))
            }
            {
              // i < j
              assume hlt;
              rewrite hlt;
              simplify;
              rewrite ih1;
              symmetry;
              rewrite ax_assoc R H;
              reflexivity
            }
            {
              // i > j
              assume hgt;
              rewrite hgt;
              simplify;
              rewrite ih2;
              refine ax_shuffle R H (act R k2 (nth (v0 R) l j))
                       (vadd R (act R k1 (nth (v0 R) l i)) (lval R (xs ‚ l)))
                       (lval R (ys ‚ l))
            }
            {reflexivity}
          }
        }
      }
  }
end;

opaque symbol case_l [a] x (l : 𝕃 a) n :
  π ((size (x ⸬ l)) Nat.≤ (n +1)) → π (size l Nat.≤ n) ≔
begin
  assume a x l n;
  refine λ x, x;
end;

opaque symbol size_split [a] (l : 𝕃 a) : π (size ((split l) ₁) Nat.≤ size l) ≔
begin
  assume a;
  refine list_ind2_principle (λ u, istrue (size (split u ₁) Nat.≤ size u)) _ _ _
  {apply ⊤ᵢ}
  {assume y; apply ⊤ᵢ}
  {
    simplify;
    assume x y l ih;
    apply @leq_trans (size (split l ₁)) (size l) (size l +1) ih _;
    refine leqnSn (size l)
  }
end;

opaque symbol size_split2 [a] (l : 𝕃 a) : π (size ((split l) ₂) Nat.≤ size l) ≔
begin
  assume a;
  refine list_ind2_principle (λ u, istrue (size (split u ₂) Nat.≤ size u)) _ _ _
  {apply ⊤ᵢ}
  {assume y; apply ⊤ᵢ}
  {
    simplify;
    assume x y l ih;
    apply @leq_trans (size (split l ₂)) (size l) (size l +1) ih _;
    refine leqnSn (size l)
  }
end;

opaque symbol mergesort_correct_aux R (H : π (LinAx R)) n l g :
  π (size g Nat.≤ n) → π (lval R ((mergesort R g) ‚ l) = lval R (g ‚ l)) ≔
begin
    assume R H;
    induction
    {
        assume l;
        assume g h;
        rewrite size0nil g (≤0 (size g) h);
        reflexivity
    }
    {
      assume n ihn l g;
      refine rec_𝕃 g (λ u, (size u Nat.≤ (n +1)) ⇒
               ((lval R ((mergesort R u) ‚ l) = lval R (u ‚ l)))) _ _
      {
        simplify;
        reflexivity
      }
      {
        assume x g';
        refine rec_𝕃 g' (λ u, (size (x ⸬ u) Nat.≤ (n +1)) ⇒
                 ((lval R ((mergesort R (x ⸬ u)) ‚ l) = lval R ((x ⸬ u) ‚ l)))) _ _
        {reflexivity}
        {
          assume y g'' inv1;
          simplify;
          rewrite (merge_correct R H l (mergesort R (x ⸬ ((split g'') ₁)))
                                       (mergesort R (y ⸬ ((split g'') ₂))));
          have tmp3x : π (istrue (size (x ⸬ (split g'' ₁)) Nat.≤ n)) {
            apply @leq_trans
            (size (split g'' ₁) +1)
            (size g'' +1)
            n
            _
            inv1;
            apply size_split g''
          };
          rewrite ihn l (x ⸬ (split g'' ₁)) tmp3x;
          have tmp3y : π (istrue (size (y ⸬ (split g'' ₂)) Nat.≤ n)) {
            simplify;
            apply @leq_trans
            (size (split g'' ₂) +1)
            (size g'' +1)
            n
            _
            inv1;
            simplify;
            apply size_split2 g''
          };
          rewrite ihn l (y ⸬ (split g'' ₂)) tmp3y;
          simplify;
          rewrite ax_swap R H (lval_grp R x l) (lval R (split g'' ₁ ‚ l))
                              (lval_grp R y l) (lval R (split g'' ₂ ‚ l));
          rewrite ax_assoc R H;
          rewrite left ++_eq_+ R H l (split g'' ₁) (split g'' ₂);
          rewrite split_correct R H;
          reflexivity
        }
      }
    }
end;

symbol mergesort_correct R (H : π (LinAx R)) l g ≔
  mergesort_correct_aux R H (size g) l g (Nat.≤_refl (size g));

opaque symbol remove0_correct R (H : π (LinAx R)) l gs :
  π (lval R ((remove0 R gs) ‚ l) = lval R (gs ‚ l)) ≔
begin
  assume R H l;
  induction
  { reflexivity }
  {
    induction
    {
      // Cst c
      assume c gs ih;
      refine ind_𝔹 (λ b, (snull R c = b) ⇒
          (lval R ((if (snull R c) (remove0 R gs) (Cst c ⸬ remove0 R gs)) ‚ l)
             = vadd R (emb R c) (lval R (gs ‚ l)))) _ _ (snull R c) _
      {
        assume hb;
        have hc : π (c = s0 R) { refine ax_null R H c _; rewrite hb; refine ⊤ᵢ };
        rewrite hb;
        rewrite hc;
        rewrite ax_emb_0 R H;
        rewrite ax_neutral R H;
        refine ih
      }
      { assume hb; rewrite hb; simplify; rewrite ih; reflexivity }
      { reflexivity }
    }
    {
      // Var i c
      assume i c gs ih;
      refine ind_𝔹 (λ b, (snull R c = b) ⇒
          (lval R ((if (snull R c) (remove0 R gs) (Var i c ⸬ remove0 R gs)) ‚ l)
             = vadd R (act R c (nth (v0 R) l i)) (lval R (gs ‚ l)))) _ _ (snull R c) _
      {
        assume hb;
        have hc : π (c = s0 R) { refine ax_null R H c _; rewrite hb; refine ⊤ᵢ };
        rewrite hb;
        rewrite hc;
        rewrite ax_act_0 R H;
        rewrite ax_neutral R H;
        refine ih
      }
      { assume hb; rewrite hb; simplify; rewrite ih; reflexivity }
      { reflexivity }
    }
  }
end;

opaque symbol norm_correct R (H : π (LinAx R)) (x : 𝕃 (grp (scal R))) l :
  π (lval R ((norm R x) ‚ l) = lval R (x ‚ l)) ≔
begin
  assume R H x l;
  simplify;
  apply eq_trans (lval R (remove0 R (mergesort R x) ‚ l))
                 (lval R (mergesort R x ‚ l)) (lval R (x ‚ l))
  { apply remove0_correct R H l (mergesort R x) }
  { apply mergesort_correct R H l x }
end;

// ===========================================================================
// Reification helpers (generic: they only look for a term in a list)
// ===========================================================================

constant symbol Loc : TYPE;
constant symbol Old : ℕ → Loc;     // found at that index
constant symbol Fresh : ℕ → Loc;   // not found; index to be used for it

symbol case_Loc [a] : Loc → (ℕ → τ a) → (ℕ → τ a) → τ a;

rule case_Loc (Old $i) $f _ ↪ $f $i
with case_Loc (Fresh $i) _ $g ↪ $g $i;

/* Index of a value in a list: returns `Fresh` if the value is not
   definitionally equal to some element of the list. */

sequential symbol lookup : ℕ → Π [a], τ a → τ (list a) → Loc;

rule lookup $k _ □ ↪ Fresh $k
with lookup $k $x ($x ⸬ _) ↪ Old $k
with lookup $k $x (_ ⸬ $l) ↪ lookup ($k +1) $x $l;

// η for pairs, used to put a reified expression in the shape `e ‚ l`
symbol eta_prod [a b] (x : τ (a × b)) : π (x = (x ₁) ‚ (x ₂));
