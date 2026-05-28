// All definitions inspired by https://rocq-prover.org/doc/v9.0/stdlib/Stdlib.PArith.BinPosDef.html

require open Stdlib.Nat Stdlib.Z Stdlib.Prop Stdlib.Prod;


inductive Mask: TYPE ≔
| IsNul : Mask
| IsPos : ℙ →  Mask
| IsNeg : Mask
;

symbol mask: Set;
rule τ mask ↪ Mask;

symbol sub': Mask → ℙ;
rule sub' (IsPos $p) ↪ $p
with sub' IsNeg ↪ H
with sub' IsNul ↪ H
;

// x -> 2*x
symbol double_mask: Mask → Mask;
rule double_mask IsNul ↪ IsNul
with double_mask IsNeg ↪ IsNeg
with double_mask (IsPos $x) ↪ IsPos (O $x)
;

// x -> 2*x-1
symbol pred_double : ℙ → ℙ;
rule pred_double (I $x) ↪ I (O $x)
with pred_double (O $x) ↪ I (pred_double $x)
with pred_double H ↪ H
;

compute val ((O (O (I H))));
compute val (pred_double (O (O (I H))));

//  x -> 2*x - 2
symbol double_pred_mask: ℙ → Mask;
rule double_pred_mask H ↪ IsNul
with double_pred_mask (I $x) ↪ IsPos (O (O $x))
with double_pred_mask (O $x) ↪ IsPos (O (pred_double $x))
;

// x -> 2 * x + 1
symbol suc_double_mask: Mask → Mask;
rule suc_double_mask IsNul ↪ IsPos H
with suc_double_mask IsNeg ↪ IsNeg
with suc_double_mask (IsPos $x) ↪ IsPos (I $x)
;

symbol sub_mask_carry :  ℙ → ℙ → Mask;
symbol sub_mask :  ℙ → ℙ → Mask;

rule sub_mask_carry (I $p) (I $q) ↪ suc_double_mask (sub_mask_carry $p $q)
with sub_mask_carry (I $p) (O $q) ↪ double_mask (sub_mask $p $q)
with sub_mask_carry (I $p) H ↪ IsPos (pred_double $p)
with sub_mask_carry (O $p) (I $q) ↪ double_mask (sub_mask_carry $p $q)
with sub_mask_carry (O $p) (O $q) ↪ suc_double_mask (sub_mask_carry $p $q)
with sub_mask_carry (O $p) H ↪ double_pred_mask $p
with sub_mask_carry H _ ↪ IsNeg
;

rule sub_mask (I $p) (I $q) ↪ double_mask (sub_mask $p $q)
with sub_mask (I $p) (O $q) ↪ suc_double_mask (sub_mask $p $q)
with sub_mask (I $p) H ↪ IsPos (O $p)
with sub_mask (O $p) (I $q) ↪ suc_double_mask (sub_mask_carry $p $q)
with sub_mask (O $p) (O $q) ↪ double_mask (sub_mask $p $q)
with sub_mask (O $p) H ↪ IsPos (pred_double $p)
with sub_mask H H ↪ IsNul
with sub_mask H (I $q) ↪ IsNeg
with sub_mask H (O $q) ↪ IsNeg
;

symbol sub: ℙ → ℙ → ℙ;
rule sub $a $b ↪ sub' (sub_mask $a $b);

// https://coq.inria.fr/doc/V8.18.0/aclia/Coq.PArith.BinPosDef.html#Pos.gcdn
symbol Stein_gcd (a b: ℙ): ℙ;
rule Stein_gcd H _ ↪ H    // 1 / gcd(1, b) = 1
with Stein_gcd _ H ↪ H    // gcd(a, 1) = 1
with Stein_gcd (O $a) (O $b) ↪ O (Stein_gcd $a $b) // gcd(2a, 2b) = 2 * gcd(a,b) bc 2 is a common divisor
with Stein_gcd (I $a) (O $b) ↪ (Stein_gcd $a $b) // u is odd then 2 is not a common division
with Stein_gcd (O $a) (I $b) ↪ (Stein_gcd $a (I $b))
with Stein_gcd (I $a) (I $b) ↪
    let res ≔ (compare $a $b) in
        if (isEq res) 
            (I $a)  // Eq
            (if (isLt res)
                (Stein_gcd (sub $b $a) (I $a)) // Lt
                (Stein_gcd (sub $a $b) (I $b))) // Gt
;

symbol abs: ℤ → ℤ;
rule abs Z0 ↪ Z0
with abs (Zpos $x) ↪ Zpos $x
with abs (Zneg $x) ↪ Zpos $x
;

// ============================================================
// Coq-style safe wrapper (mirrors Pos.gcd = gcdn (size_nat a + size_nat b) a b).
//
// Coq's Pos.gcdn returns the gcd given enough fuel; the public Pos.gcd
// passes `size_nat a + size_nat b` (sum of bit-lengths) as the fuel,
// which is provably sufficient. We mirror that pattern:
//   - size_nat          : bit-length of a positive.
//   - ggcd_fuel         : the bounded-fuel computation, mirroring Pos.ggcdn.
//   - ggcd_safe         : ggcd_fuel (size_nat x + size_nat y) x y.
//   - red_by_Stein_v2   : a/gcd projection of ggcd_safe.
//
// Correctness flows through ggcd_fuel_correct + ggcd_fuel_sym to give
// the cross identity red_by_Stein_v2_cross, which Z_red_Stein_correct
// consumes (Z_red_Stein and its correctness are defined at the end of
// this file, after all the supporting lemmas).

// Bit-length of a positive (Coq's Pos.size_nat).
symbol size_nat : ℙ → ℕ;
rule size_nat H ↪ _0 +1
with size_nat (O $p) ↪ size_nat $p +1
with size_nat (I $p) ↪ size_nat $p +1;

// ============================================================
// Coq's ggcdn — returns (gcd, (a/gcd, b/gcd)) as a triple.
// Mirrors Pos.ggcdn faithfully. In case (I a, I b) the recursion
// SWAPS arguments (first arg becomes sub b a / sub a b, second becomes
// I a / I b) — this is what makes the recursion terminate, unlike the
// original red_by_Stein where (9, 3) loops because the first arg is
// never reduced.
symbol ggcd_fuel : ℕ → ℙ → ℙ → τ (pos × pos × pos);
symbol ggcd_step_II : ℕ → ℙ → ℙ → Comp → τ (pos × pos × pos);

rule ggcd_fuel _0 $a $b ↪ H ‚ $a ‚ $b
with ggcd_fuel (_ +1) H $b ↪ H ‚ H ‚ $b
with ggcd_fuel (_ +1) $a H ↪ H ‚ $a ‚ H
with ggcd_fuel ($n +1) (O $a) (O $b) ↪
  let r ≔ ggcd_fuel $n $a $b in
    O ((r)₁) ‚ ((r)₂)
with ggcd_fuel ($n +1) (I $a) (O $b) ↪
  let r ≔ ggcd_fuel $n (I $a) $b in
    ((r)₁) ‚ (((r)₂)₁) ‚ O (((r)₂)₂)
with ggcd_fuel ($n +1) (O $a) (I $b) ↪
  let r ≔ ggcd_fuel $n $a (I $b) in
    ((r)₁) ‚ O (((r)₂)₁) ‚ (((r)₂)₂)
with ggcd_fuel ($n +1) (I $a) (I $b) ↪
  ggcd_step_II $n $a $b (compare $a $b)
;

rule ggcd_step_II _ $a _ Eq ↪ (I $a) ‚ H ‚ H
with ggcd_step_II $n $a $b Lt ↪
  let r ≔ ggcd_fuel $n (sub $b $a) (I $a) in
    ((r)₁) ‚ (((r)₂)₂) ‚ add (((r)₂)₂) (O (((r)₂)₁))
with ggcd_step_II $n $a $b Gt ↪
  let r ≔ ggcd_fuel $n (sub $a $b) (I $b) in
    ((r)₁) ‚ add (((r)₂)₂) (O (((r)₂)₁)) ‚ (((r)₂)₂)
;

// Safe wrappers at size_nat fuel.
symbol ggcd_safe : ℙ → ℙ → τ (pos × pos × pos);
rule ggcd_safe $x $y ↪
  ggcd_fuel (Stdlib.Nat.+ (size_nat $x) (size_nat $y)) $x $y;

// New a/gcd function, derived from ggcd_safe. Mirrors Coq's pattern.
symbol red_by_Stein_v2 : ℙ → ℙ → ℙ;
rule red_by_Stein_v2 $x $y ↪ ((ggcd_safe $x $y)₂)₁;

// Sanity checks: verify the v2 function on the problematic input (9, 3)
// where the old red_by_Stein loops.
assert ⊢ red_by_Stein_v2 (I H) (I (O (O H))) ≡ H;            // 3, 9 → 1
assert ⊢ red_by_Stein_v2 (I (O (O H))) (I H) ≡ I H;          // 9, 3 → 3
assert ⊢ mul (red_by_Stein_v2 (I H) (I (O (O H)))) (I (O (O H)))
       ≡ mul (I H) (red_by_Stein_v2 (I (O (O H))) (I H));    // cross check: 1·9 = 3·3

// ============================================================
// Sub-add identity (Coq's Pos.sub_add): when q < p, q + (p - q) = p.
// We prove the form needed for the (I a, I b) case of ggcd:
//   compare a b = Lt → add (I a) (O (sub b a)) = I b.

// Successor of pred_double (Zgcd-local copy of Pos.succ_pos_pred_double).
opaque symbol succ_pred_double_local x : π (succ (pred_double x) = O x) ≔
begin
  induction
  // x = I y
  { assume y IH; reflexivity }
  // x = O y
  { assume y IH; simplify; rewrite IH; reflexivity }
  // x = H
  { reflexivity }
end;

// sub of a positive by H: succ (sub p H) = p when p ≠ H.
// Encoded without a hypothesis by case analysis on p's constructor:
// for I _ and O _ it holds, for H both sides degenerate (and is unused).
opaque symbol succ_sub_H_I x : π (succ (sub (I x) H) = I x) ≔
begin
  assume x; reflexivity
end;

opaque symbol succ_sub_H_O x : π (succ (sub (O x) H) = O x) ≔
begin
  assume x; simplify; refine succ_pred_double_local x
end;

// ============================================================
// Mask discriminators and Prop-level case eliminator.
// `mask_inv m P Q` is `P` if m is IsNul, `Q r` if m is IsPos r, and `⊤` for
// IsNeg. This lets us state the sub_mask invariants without `⇒` inside the
// proposition, so the proof can proceed by direct rewriting once we case
// on m via ind_Mask.

symbol mask_inv : Mask → Prop → (ℙ → Prop) → Prop;
rule mask_inv IsNul $P _ ↪ $P
with mask_inv (IsPos $r) _ $Q ↪ $Q $r
with mask_inv IsNeg _ _ ↪ ⊤;

// ============================================================
// Combined sub_mask / sub_mask_carry invariants.
//   - if sub_mask p q reduces to IsNul, then p = q;
//   - if sub_mask p q reduces to IsPos r, then p = add q r;
//   - if sub_mask_carry p q reduces to IsNul, then p = succ q;
//   - if sub_mask_carry p q reduces to IsPos r, then p = succ (add q r).
// IsNeg cases hold trivially (⊤).
opaque symbol sub_mask_invariants p q : π (
  mask_inv (sub_mask p q) (p = q) (λ r, p = add q r) ∧
  mask_inv (sub_mask_carry p q) (p = succ q) (λ r, p = succ (add q r))
) ≔
begin
  induction
  // p = I a
  { assume a IH;
    induction
    // q = I b
    { assume b IHb;
      apply ∧ᵢ
      { refine ind_Mask
          (λ m, mask_inv m (a = b) (λ r, a = add b r) ⇒
                mask_inv (double_mask m) (I a = I b) (λ r, I a = add (I b) r))
          _ _ _ (sub_mask a b) (∧ₑ₁ (IH b))
        { assume h; apply feq I; refine h }
        { assume x h; apply feq I; refine h }
        { assume hxx; refine ⊤ᵢ } }
      { refine ind_Mask
          (λ m, mask_inv m (a = succ b) (λ r, a = succ (add b r)) ⇒
                mask_inv (suc_double_mask m) (I a = succ (I b)) (λ r, I a = succ (add (I b) r)))
          _ _ _ (sub_mask_carry a b) (∧ₑ₂ (IH b))
        { assume h; simplify; apply feq I; refine h }
        { assume x h; simplify; apply feq I; rewrite h; rewrite succ_add; reflexivity }
        { assume hxx; refine ⊤ᵢ } } }
    // q = O b
    { assume b IHb;
      apply ∧ᵢ
      { refine ind_Mask
          (λ m, mask_inv m (a = b) (λ r, a = add b r) ⇒
                mask_inv (suc_double_mask m) (I a = O b) (λ r, I a = add (O b) r))
          _ _ _ (sub_mask a b) (∧ₑ₁ (IH b))
        { assume h; simplify; apply feq I; refine h }
        { assume x h; simplify; apply feq I; refine h }
        { assume hxx; refine ⊤ᵢ } }
      { refine ind_Mask
          (λ m, mask_inv m (a = b) (λ r, a = add b r) ⇒
                mask_inv (double_mask m) (I a = succ (O b)) (λ r, I a = succ (add (O b) r)))
          _ _ _ (sub_mask a b) (∧ₑ₁ (IH b))
        { assume h; simplify; apply feq I; refine h }
        { assume x h; simplify; apply feq I; refine h }
        { assume hxx; refine ⊤ᵢ } } }
    // q = H
    { apply ∧ᵢ
      { simplify; reflexivity }
      // sub_mask_carry (I a) H = IsPos (pred_double a). Goal: I a = succ (succ (pred_double a)).
      { simplify;
        refine ind_ℙ (λ x, I x = succ (succ (pred_double x))) _ _ _ a
        // a = I y
        { assume y IHy; reflexivity }
        // a = O y
        { assume y IHy; simplify; rewrite succ_pred_double_local; reflexivity }
        // a = H
        { reflexivity } } } }
  // p = O a
  { assume a IH;
    induction
    // q = I b
    { assume b IHb;
      apply ∧ᵢ
      { refine ind_Mask
          (λ m, mask_inv m (a = succ b) (λ r, a = succ (add b r)) ⇒
                mask_inv (suc_double_mask m) (O a = I b) (λ r, O a = add (I b) r))
          _ _ _ (sub_mask_carry a b) (∧ₑ₂ (IH b))
        { assume h; simplify; apply feq O; refine h }
        { assume x h; simplify; apply feq O; rewrite h; rewrite succ_add; reflexivity }
        { assume hxx; refine ⊤ᵢ } }
      { refine ind_Mask
          (λ m, mask_inv m (a = succ b) (λ r, a = succ (add b r)) ⇒
                mask_inv (double_mask m) (O a = succ (I b)) (λ r, O a = succ (add (I b) r)))
          _ _ _ (sub_mask_carry a b) (∧ₑ₂ (IH b))
        { assume h; simplify; apply feq O; refine h }
        { assume x h; simplify; apply feq O; refine h }
        { assume hxx; refine ⊤ᵢ } } }
    // q = O b
    { assume b IHb;
      apply ∧ᵢ
      { refine ind_Mask
          (λ m, mask_inv m (a = b) (λ r, a = add b r) ⇒
                mask_inv (double_mask m) (O a = O b) (λ r, O a = add (O b) r))
          _ _ _ (sub_mask a b) (∧ₑ₁ (IH b))
        { assume h; apply feq O; refine h }
        { assume x h; simplify; apply feq O; refine h }
        { assume hxx; refine ⊤ᵢ } }
      { refine ind_Mask
          (λ m, mask_inv m (a = succ b) (λ r, a = succ (add b r)) ⇒
                mask_inv (suc_double_mask m) (O a = succ (O b)) (λ r, O a = succ (add (O b) r)))
          _ _ _ (sub_mask_carry a b) (∧ₑ₂ (IH b))
        { assume h; simplify; apply feq O; refine h }
        { assume x h; simplify; apply feq O; rewrite h; rewrite succ_add; reflexivity }
        { assume hxx; refine ⊤ᵢ } } }
    // q = H
    { apply ∧ᵢ
      { simplify; rewrite succ_pred_double_local; reflexivity }
      // sub_mask_carry (O a) H = double_pred_mask a — case on a
      { refine ind_ℙ
          (λ x, mask_inv (double_pred_mask x) (O x = succ H) (λ r, O x = succ (add H r)))
          _ _ _ a
        // a = I y
        { assume y IHy; simplify; reflexivity }
        // a = O y
        { assume y IHy; simplify; rewrite succ_pred_double_local; reflexivity }
        // a = H
        { simplify; reflexivity } } } }
  // p = H
  { induction
    // q = I b
    { assume b IHb; apply ∧ᵢ { simplify; refine ⊤ᵢ } { simplify; refine ⊤ᵢ } }
    // q = O b
    { assume b IHb; apply ∧ᵢ { simplify; refine ⊤ᵢ } { simplify; refine ⊤ᵢ } }
    // q = H
    { apply ∧ᵢ { simplify; reflexivity } { simplify; refine ⊤ᵢ } } }
end;

// ============================================================
// Compare-related helpers needed to derive sub_add_lt from sub_mask_invariants.

// compare_acc x c x reduces to c (any positive compared with itself yields the
// accumulator). Proof by induction on x.
opaque symbol compare_acc_refl x : Π c, π (compare_acc x c x = c) ≔
begin
  induction
  { assume x h c; simplify; refine h c }
  { assume x h c; simplify; refine h c }
  { assume c; reflexivity }
end;

// Corollary: compare x x = Eq.
opaque symbol compare_refl x : π (compare x x = Eq) ≔
begin
  assume x; refine compare_acc_refl x Eq
end;

// Discriminator for Mask: true on IsNeg, false otherwise.
// ind_eq lifts (istrue ∘ isIsNeg) from RHS to LHS: ⊤ᵢ at IsNeg yields ⊥ at IsNul/IsPos.
symbol isIsNeg : Mask → 𝔹;
rule isIsNeg IsNul ↪ false
with isIsNeg (IsPos _) ↪ false
with isIsNeg IsNeg ↪ true;

opaque symbol IsNul≠IsNeg : π (IsNul ≠ IsNeg) ≔
begin
  assume h; refine ind_eq h (λ m, istrue (isIsNeg m)) ⊤ᵢ
end;

opaque symbol IsPos≠IsNeg x : π (IsPos x ≠ IsNeg) ≔
begin
  assume x h; refine ind_eq h (λ m, istrue (isIsNeg m)) ⊤ᵢ
end;

// double_mask / suc_double_mask preserve "IsNeg-ness". I.e., the only way
// for the wrapper to be IsNeg is for the input to already be IsNeg.

opaque symbol double_mask_IsNeg_inv m : π (double_mask m = IsNeg ⇒ m = IsNeg) ≔
begin
  refine ind_Mask (λ m, double_mask m = IsNeg ⇒ m = IsNeg) _ _ _
  { assume h; apply ⊥ₑ; refine IsNul≠IsNeg h }     // double_mask IsNul = IsNul ≠ IsNeg
  { assume x h; apply ⊥ₑ; refine IsPos≠IsNeg (O x) h }
  { assume hxxx; reflexivity }
end;

opaque symbol suc_double_mask_IsNeg_inv m : π (suc_double_mask m = IsNeg ⇒ m = IsNeg) ≔
begin
  refine ind_Mask (λ m, suc_double_mask m = IsNeg ⇒ m = IsNeg) _ _ _
  { assume h; apply ⊥ₑ; refine IsPos≠IsNeg H h }    // suc_double_mask IsNul = IsPos H
  { assume x h; apply ⊥ₑ; refine IsPos≠IsNeg (I x) h }
  { assume hxxx; reflexivity }
end;

// double_pred_mask a is never IsNeg (rules out the (O a, H) carry case).
opaque symbol double_pred_mask_not_IsNeg a : π (double_pred_mask a ≠ IsNeg) ≔
begin
  refine ind_ℙ (λ a, double_pred_mask a ≠ IsNeg) _ _ _
  { assume y IHy h; refine IsPos≠IsNeg (O (O y)) h }
  { assume y IHy h; refine IsPos≠IsNeg (O (pred_double y)) h }
  { assume h; refine IsNul≠IsNeg h }
end;

// Mutually-recursive correspondence between sub_mask/sub_mask_carry and
// compare. The IsNeg cases of the sub-masks correspond to the strict (Lt)
// and the non-strict (Lt ∨ Eq) sides of compare, respectively.
opaque symbol sub_mask_neg_compare p q : π (
  (sub_mask p q = IsNeg ⇒ compare p q = Lt) ∧
  (sub_mask_carry p q = IsNeg ⇒ compare p q = Lt ∨ compare p q = Eq)
) ≔
begin
  induction
  // p = I a
  { assume a IH;
    induction
    // q = I b
    { assume b IHb;
      apply ∧ᵢ
      { assume hsub;
        // double_mask (sub_mask a b) = IsNeg → sub_mask a b = IsNeg
        have ha : π (sub_mask a b = IsNeg)
          { refine double_mask_IsNeg_inv (sub_mask a b) hsub };
        // compare (I a) (I b) reduces to compare a b
        simplify; refine (∧ₑ₁ (IH b)) ha }
      { assume hsub;
        have ha : π (sub_mask_carry a b = IsNeg)
          { refine suc_double_mask_IsNeg_inv (sub_mask_carry a b) hsub };
        simplify; refine (∧ₑ₂ (IH b)) ha } }
    // q = O b
    { assume b IHb;
      apply ∧ᵢ
      { assume hsub;
        have ha : π (sub_mask a b = IsNeg)
          { refine suc_double_mask_IsNeg_inv (sub_mask a b) hsub };
        // compare (I a) (O b) = compare_acc a Gt b = case_Comp (compare a b) Gt Lt Gt
        have hab : π (compare a b = Lt) { refine (∧ₑ₁ (IH b)) ha };
        simplify; rewrite compare_Gt; rewrite hab; reflexivity }
      { assume hsub;
        have ha : π (sub_mask a b = IsNeg)
          { refine double_mask_IsNeg_inv (sub_mask a b) hsub };
        have hab : π (compare a b = Lt) { refine (∧ₑ₁ (IH b)) ha };
        apply ∨ᵢ₁; simplify; rewrite compare_Gt; rewrite hab; reflexivity } }
    // q = H
    { apply ∧ᵢ
      { assume hsub; apply ⊥ₑ; refine IsPos≠IsNeg (O a) hsub }
      { assume hsub; apply ⊥ₑ; refine IsPos≠IsNeg (pred_double a) hsub } } }
  // p = O a
  { assume a IH;
    induction
    // q = I b
    { assume b IHb;
      apply ∧ᵢ
      { assume hsub;
        have ha : π (sub_mask_carry a b = IsNeg)
          { refine suc_double_mask_IsNeg_inv (sub_mask_carry a b) hsub };
        // From IH carry: compare a b = Lt ∨ Eq.
        // compare (O a) (I b) = compare_acc a Lt b = case_Comp (compare a b) Lt Lt Gt = Lt in both cases.
        simplify; rewrite compare_Lt;
        refine ∨ₑ ((∧ₑ₂ (IH b)) ha) _ _
          { assume h; rewrite h; reflexivity }
          { assume h; rewrite h; reflexivity } }
      { assume hsub;
        have ha : π (sub_mask_carry a b = IsNeg)
          { refine double_mask_IsNeg_inv (sub_mask_carry a b) hsub };
        apply ∨ᵢ₁; simplify; rewrite compare_Lt;
        refine ∨ₑ ((∧ₑ₂ (IH b)) ha) _ _
          { assume h; rewrite h; reflexivity }
          { assume h; rewrite h; reflexivity } } }
    // q = O b
    { assume b IHb;
      apply ∧ᵢ
      { assume hsub;
        have ha : π (sub_mask a b = IsNeg)
          { refine double_mask_IsNeg_inv (sub_mask a b) hsub };
        simplify; refine (∧ₑ₁ (IH b)) ha }
      { assume hsub;
        have ha : π (sub_mask_carry a b = IsNeg)
          { refine suc_double_mask_IsNeg_inv (sub_mask_carry a b) hsub };
        simplify; refine (∧ₑ₂ (IH b)) ha } }
    // q = H
    { apply ∧ᵢ
      { assume hsub; apply ⊥ₑ; refine IsPos≠IsNeg (pred_double a) hsub }
      { assume hsub; apply ⊥ₑ; refine double_pred_mask_not_IsNeg a hsub } } }
  // p = H
  { induction
    // q = I b
    { assume b IHb;
      apply ∧ᵢ
      { assume hxxx; reflexivity }
      { assume hh; apply ∨ᵢ₁; reflexivity } }
    // q = O b
    { assume b IHb;
      apply ∧ᵢ
      { assume hxxx; reflexivity }
      { assume hh; apply ∨ᵢ₁; reflexivity } }
    // q = H
    { apply ∧ᵢ
      { assume hsub; apply ⊥ₑ; refine IsNul≠IsNeg hsub }
      { assume hh; apply ∨ᵢ₂; reflexivity } } }
end;

// ============================================================
// sub_add_lt and sub_add_gt: the form of the sub-add identity directly
// consumed by ggcd_step_II_correct.
//
// sub_add_lt: when a < b, (I a) + 2·(b - a) = I b.
// Equivalently: I (add a (sub b a)) = I b, i.e., add a (sub b a) = b.
//
// Proof: case on sub_mask b a via ind_Mask, using
//   1. sub_mask_invariants: if sub_mask b a = IsPos r, then b = add a r;
//   2. sub_mask_invariants + compare_refl: rules out sub_mask b a = IsNul
//      (would force b = a, contradicting compare a b = Lt);
//   3. sub_mask_neg_compare: rules out sub_mask b a = IsNeg
//      (would give compare b a = Lt, contradicting compare a b = Lt via opp).

opaque symbol sub_add_lt :
  Π a b, π (compare a b = Lt) → π (add (I a) (O (sub b a)) = I b) ≔
begin
  assume a b hlt;
  refine ind_Mask
    (λ m, sub_mask b a = m ⇒ add (I a) (O (sub' m)) = I b)
    _ _ _ (sub_mask b a) (eq_refl _)
  // m = IsNul: sub_mask b a = IsNul → b = a → compare a a = Eq, contradicts hlt
  { assume heq;
    apply ⊥ₑ;
    // Pull `b = a` out of mask_inv at IsNul by substituting heq into the invariant.
    have hba : π (b = a)
      { refine ind_eq (eq_sym heq)
          (λ m, mask_inv m (b = a) (λ r, b = add a r))
          (∧ₑ₁ (sub_mask_invariants b a)) };
    have hcab : π (compare a b = Eq)
      { rewrite hba; refine compare_refl a };
    refine Lt≠Eq (ind_eq (eq_sym hlt) (λ x, x = Eq) hcab) }
  // m = IsPos r: sub_mask b a = IsPos r → b = add a r → add (I a) (O r) = I (add a r) = I b
  { assume r heq;
    simplify;
    have hba : π (b = add a r)
      { refine ind_eq (eq_sym heq)
          (λ m, mask_inv m (b = a) (λ r0, b = add a r0))
          (∧ₑ₁ (sub_mask_invariants b a)) };
    rewrite left hba; reflexivity }
  // m = IsNeg: sub_mask b a = IsNeg → compare b a = Lt → compare a b = Gt, contradicts hlt
  { assume heq;
    apply ⊥ₑ;
    have hba : π (compare b a = Lt) { refine (∧ₑ₁ (sub_mask_neg_compare b a)) heq };
    // compare a b = opp (compare b a) = opp Lt = Gt
    have habGt : π (compare a b = Gt)
      { rewrite compare_com; rewrite hba; reflexivity };
    refine Gt≠Lt (eq_sym (ind_eq (eq_sym hlt) (λ x, x = Gt) habGt)) }
end;

// sub_add_gt: symmetric, derived from sub_add_lt by swapping a and b.
//   compare a b = Gt ⇔ compare b a = Lt (by compare_com),
// so sub_add_gt a b h = sub_add_lt b a (derived hypothesis).
opaque symbol sub_add_gt :
  Π a b, π (compare a b = Gt) → π (add (I b) (O (sub a b)) = I a) ≔
begin
  assume a b hgt;
  // compare b a = opp (compare a b) = opp Gt = Lt
  have hba : π (compare b a = Lt)
    { rewrite compare_com; rewrite hgt; reflexivity };
  refine sub_add_lt b a hba
end;

// ============================================================
// Correctness of ggcd_fuel: for any n, x, y, letting (g, aa, bb) =
// ggcd_fuel n x y, we have x = g·aa and y = g·bb. Stated as a joint
// conjunction so the induction can use both parts of the IH at once.

// Helper used in the (I a, I b) branch: case-analyzes on a Comp result.
// For Eq: the body returns (I a, H, H) immediately; compare_decides
// gives a = b, so I a = I b and both sides reduce to I a.
// For Lt/Gt: the body recurses through ggcd_fuel; needs sub-add identity.
// Parameterized on IHk (the fuel-k correctness) to avoid a forward
// reference to ggcd_fuel_correct; the caller (ggcd_fuel_correct) supplies
// its inductive hypothesis here.
opaque symbol ggcd_step_II_correct : Π k,
  (Π x y, π ((x = mul ((ggcd_fuel k x y)₁) (((ggcd_fuel k x y)₂)₁)) ∧
             (y = mul ((ggcd_fuel k x y)₁) (((ggcd_fuel k x y)₂)₂)))) →
  Π a b,
  π ((I a = mul ((ggcd_step_II k a b (compare a b))₁)
                (((ggcd_step_II k a b (compare a b))₂)₁)) ∧
     (I b = mul ((ggcd_step_II k a b (compare a b))₁)
                (((ggcd_step_II k a b (compare a b))₂)₂))) ≔
begin
  assume k IHk a b;
  refine ind_Comp
    (λ c, (compare a b = c) ⇒
          (I a = mul ((ggcd_step_II k a b c)₁)
                     (((ggcd_step_II k a b c)₂)₁)) ∧
          (I b = mul ((ggcd_step_II k a b c)₁)
                     (((ggcd_step_II k a b c)₂)₂)))
    _ _ _
    (compare a b) _
  // P Eq
  { assume heq;
    have aeqb : π (a = b) { refine compare_decides a b heq };
    apply ∧ᵢ
    { reflexivity }
    { rewrite left aeqb; reflexivity } }
  // P Lt
  { assume hlt;
    simplify;
    apply ∧ᵢ
    { refine ∧ₑ₂ (IHk (sub' (sub_mask b a)) (I a)) }
    { rewrite mul_distr_l;
      rewrite mul_x0_r;
      rewrite left (∧ₑ₂ (IHk (sub' (sub_mask b a)) (I a)));
      rewrite left (∧ₑ₁ (IHk (sub' (sub_mask b a)) (I a)));
      symmetry; refine sub_add_lt a b hlt } }
  // P Gt
  { assume hgt;
    simplify;
    apply ∧ᵢ
    { rewrite mul_distr_l;
      rewrite mul_x0_r;
      rewrite left (∧ₑ₂ (IHk (sub' (sub_mask a b)) (I b)));
      rewrite left (∧ₑ₁ (IHk (sub' (sub_mask a b)) (I b)));
      symmetry; refine sub_add_gt a b hgt }
    { refine ∧ₑ₂ (IHk (sub' (sub_mask a b)) (I b)) } }
  // compare a b = compare a b
  { reflexivity }
end;

opaque symbol ggcd_fuel_correct : Π n x y,
  π ((x = mul ((ggcd_fuel n x y)₁) (((ggcd_fuel n x y)₂)₁)) ∧
     (y = mul ((ggcd_fuel n x y)₁) (((ggcd_fuel n x y)₂)₂))) ≔
begin
  induction
  // n = 0: ggcd_fuel 0 x y → (H, x, y). g = H, aa = x, bb = y.
  // mul H x = x, mul H y = y, so both equalities are reflexive.
  { assume x y; apply ∧ᵢ { reflexivity } { reflexivity } }
  // n = succ k
  { assume k IHk;
    induction
    // x = I a
    { assume a IH_xa;
      induction
      // y = I b — dispatches to ggcd_step_II; use ggcd_step_II_correct
      { assume b IH_yb; refine ggcd_step_II_correct k IHk a b }
      // y = O b — recurse to ggcd_fuel k (I a) b
      { assume b IH_yb; simplify; apply ∧ᵢ
        { refine ∧ₑ₁ (IHk (I a) b) }
        { rewrite mul_x0_r; refine feq O _; refine ∧ₑ₂ (IHk (I a) b) } }
      // y = H — base case via rule 3
      { apply ∧ᵢ { reflexivity } { reflexivity } } }
    // x = O a
    { assume a IH_xa;
      induction
      // y = I b — recurse to ggcd_fuel k a (I b)
      { assume b IH_yb; simplify; apply ∧ᵢ
        { rewrite mul_x0_r; refine feq O _; refine ∧ₑ₁ (IHk a (I b)) }
        { refine ∧ₑ₂ (IHk a (I b)) } }
      // y = O b — recurse to ggcd_fuel k a b
      { assume b IH_yb; simplify; apply ∧ᵢ
        { refine feq O _; refine ∧ₑ₁ (IHk a b) }
        { refine feq O _; refine ∧ₑ₂ (IHk a b) } }
      // y = H — base case via rule 3
      { apply ∧ᵢ { reflexivity } { reflexivity } } }
    // x = H — base case via rule 2
    { assume y; apply ∧ᵢ { reflexivity } { reflexivity } } }
end;
// ============================================================
// Symmetry of ggcd_fuel: swapping the two arguments yields the same gcd
// (first projection) and swaps the (second, third) projections.
//
// Used (with ggcd_fuel_correct) to derive the cross identity for
// red_by_Stein_v2: aa(x,y) · y = x · aa(y,x), via the chain
//   aa·y = aa·(g·bb) = (g·aa)·bb = x·bb = x·aa(y,x).
//
// The (I a, I b) case dispatches to ggcd_step_II_sym; the other cases
// recurse via the inductive hypothesis IHk.

opaque symbol ggcd_step_II_sym : Π k a b, π (
  (((ggcd_step_II k a b (compare a b))₁) = ((ggcd_step_II k b a (compare b a))₁)) ∧
  ((((ggcd_step_II k a b (compare a b))₂)₁) = (((ggcd_step_II k b a (compare b a))₂)₂))
) ≔
begin
  assume k a b;
  // Express compare b a in terms of compare a b so a single ind_Comp covers both.
  have hcom : π (compare b a = opp (compare a b)) { refine compare_com a b };
  rewrite hcom;
  refine ind_Comp
    (λ c, (compare a b = c) ⇒
      ( (((ggcd_step_II k a b c)₁) = ((ggcd_step_II k b a (opp c))₁)) ∧
        ((((ggcd_step_II k a b c)₂)₁) = (((ggcd_step_II k b a (opp c))₂)₂)) ))
    _ _ _
    (compare a b) (eq_refl _)
  // c = Eq: compare_decides gives a = b, so I a = I b
  { assume heq;
    have hab : π (a = b) { refine compare_decides a b heq };
    apply ∧ᵢ
    { simplify; apply feq I; refine hab }
    { simplify; reflexivity } }
  // c = Lt: opp Lt = Gt. Both step_IIs share r ≔ ggcd_fuel k (sub b a) (I a).
  { assume hlt;
    apply ∧ᵢ { simplify; reflexivity } { simplify; reflexivity } }
  // c = Gt: opp Gt = Lt. Both step_IIs share r ≔ ggcd_fuel k (sub a b) (I b).
  { assume hgt;
    apply ∧ᵢ { simplify; reflexivity } { simplify; reflexivity } }
end;

opaque symbol ggcd_fuel_sym : Π n x y, π (
  (((ggcd_fuel n x y)₁) = ((ggcd_fuel n y x)₁)) ∧
  ((((ggcd_fuel n x y)₂)₁) = (((ggcd_fuel n y x)₂)₂))
) ≔
begin
  induction
  // n = 0: ggcd_fuel 0 x y = (H, x, y); ggcd_fuel 0 y x = (H, y, x).
  { assume x y; apply ∧ᵢ { reflexivity } { reflexivity } }
  // n = k+1
  { assume k IHk;
    induction
    // x = I a
    { assume a IH_xa;
      induction
      // y = I b — both compute via ggcd_step_II; use ggcd_step_II_sym.
      { assume b IH_yb; refine ggcd_step_II_sym k a b }
      // y = O b
      { assume b IH_yb;
        apply ∧ᵢ
        { refine (∧ₑ₁ (IHk (I a) b)) }
        { refine (∧ₑ₂ (IHk (I a) b)) } }
      // y = H
      { apply ∧ᵢ { reflexivity } { reflexivity } } }
    // x = O a
    { assume a IH_xa;
      induction
      // y = I b
      { assume b IH_yb;
        apply ∧ᵢ
        { refine (∧ₑ₁ (IHk a (I b))) }
        { apply feq O; refine (∧ₑ₂ (IHk a (I b))) } }
      // y = O b
      { assume b IH_yb;
        apply ∧ᵢ
        { apply feq O; refine (∧ₑ₁ (IHk a b)) }
        { refine (∧ₑ₂ (IHk a b)) } }
      // y = H
      { apply ∧ᵢ { reflexivity } { reflexivity } } }
    // x = H
    { induction
      { assume b IH_yb; apply ∧ᵢ { reflexivity } { reflexivity } }
      { assume b IH_yb; apply ∧ᵢ { reflexivity } { reflexivity } }
      { apply ∧ᵢ { reflexivity } { reflexivity } } } }
end;

// ============================================================
// Cross identity for red_by_Stein_v2: the form consumed by Z_red_Stein_correct.
//
// Mathematically: red_by_Stein_v2 x y = x / gcd(x,y), so
//   (x/gcd) · y = x · (y/gcd) — both equal x·y/gcd.
//
// Proof outline (letting n = Stdlib.Nat.+ (size_nat x) (size_nat y), aa = (ggcd_fuel n x y)₂.₁,
// bb = (ggcd_fuel n x y)₂.₂, g = (ggcd_fuel n x y)₁):
//   1. Align fuels via addnC: ggcd_safe y x uses Stdlib.Nat.+ (size_nat y) (size_nat x) = n.
//   2. Apply ggcd_fuel_sym to rewrite (ggcd_fuel n y x)₂.₁ as bb.
//   3. Goal: mul aa y = mul x bb.
//   4. From ggcd_fuel_correct: x = mul g aa and y = mul g bb.
//   5. Both sides reduce to mul g (mul aa bb) by assoc + com.

opaque symbol red_by_Stein_v2_cross x y :
  π (mul (red_by_Stein_v2 x y) y = mul x (red_by_Stein_v2 y x)) ≔
begin
  assume x y;
  // Step 1: align fuels. ggcd_safe y x uses Stdlib.Nat.+ (size_nat y) (size_nat x).
  // Rewrite to Stdlib.Nat.+ (size_nat x) (size_nat y) via addnC.
  have hfuel : π (Stdlib.Nat.+ (size_nat y) (size_nat x) = Stdlib.Nat.+ (size_nat x) (size_nat y))
    { refine addnC (size_nat y) (size_nat x) };
  simplify;
  rewrite hfuel;
  // Step 2: use ggcd_fuel_sym applied at (y, x) to substitute
  //   ((ggcd_fuel n y x)₂)₁ = ((ggcd_fuel n x y)₂)₂.
  rewrite (∧ₑ₂ (ggcd_fuel_sym (Stdlib.Nat.+ (size_nat x) (size_nat y)) y x));
  // Goal: mul ((ggcd_fuel n x y)₂)₁ y = mul x ((ggcd_fuel n x y)₂)₂.
  //
  // Let aa = ((ggcd_fuel n x y)₂)₁, bb = ((ggcd_fuel n x y)₂)₂, g = (ggcd_fuel n x y)₁.
  // From ggcd_fuel_correct: x = mul g aa, y = mul g bb.
  // Chain: mul aa y = mul aa (mul g bb)       [hy]
  //                 = mul (mul aa g) bb       [mul_assoc]
  //                 = mul (mul g aa) bb       [mul_com]
  //                 = mul x bb                [hx, reversed]
  have hx : π (x = mul ((ggcd_fuel (Stdlib.Nat.+ (size_nat x) (size_nat y)) x y)₁)
                       (((ggcd_fuel (Stdlib.Nat.+ (size_nat x) (size_nat y)) x y)₂)₁))
    { refine ∧ₑ₁ (ggcd_fuel_correct (Stdlib.Nat.+ (size_nat x) (size_nat y)) x y) };
  have hy : π (y = mul ((ggcd_fuel (Stdlib.Nat.+ (size_nat x) (size_nat y)) x y)₁)
                       (((ggcd_fuel (Stdlib.Nat.+ (size_nat x) (size_nat y)) x y)₂)₂))
    { refine ∧ₑ₂ (ggcd_fuel_correct (Stdlib.Nat.+ (size_nat x) (size_nat y)) x y) };
  // Substitute y → mul g bb only in the LHS's outer position (`mul _ y = _`),
  // avoiding the y inside ggcd_fuel's arguments.
  rewrite .[in v in mul _ v = _] hy;
  // Goal: mul aa (mul g bb) = mul x bb
  rewrite mul_assoc;
  // Goal: mul (mul aa g) bb = mul x bb
  // Substitute x → mul g aa on RHS at the outer position.
  rewrite .[in v in _ = mul v _] hx;
  // Goal: mul (mul aa g) bb = mul (mul g aa) bb
  // Commute mul aa g → mul g aa.
  rewrite (mul_com (((ggcd_fuel (Stdlib.Nat.+ (size_nat x) (size_nat y)) x y)₂)₁)
                   ((ggcd_fuel (Stdlib.Nat.+ (size_nat x) (size_nat y)) x y)₁));
  reflexivity
end;

// ============================================================
// Z_red_Stein: reduce ℤ by gcd, keeping the sign of the first argument.
//
// Semantically Z_red_Stein a b = a / gcd(|a|, |b|) (with sign carried from a).
// Implemented on ℙ payloads via red_by_Stein_v2 (the ggcd_safe-based, total,
// terminating version). Z0 reduces to Z0; reduction by Z0 returns the sign
// of the first argument (a/|a|).
symbol Z_red_Stein : ℤ → ℤ → ℤ;
rule Z_red_Stein Z0 _ ↪ Z0
with Z_red_Stein $a Z0 ↪ sign $a
with Z_red_Stein (Zpos $a) (Zpos $b) ↪ Zpos (red_by_Stein_v2 $a $b)
with Z_red_Stein (Zpos $a) (Zneg $b) ↪ Zpos (red_by_Stein_v2 $a $b)
with Z_red_Stein (Zneg $a) (Zpos $b) ↪ Zneg (red_by_Stein_v2 $a $b)
with Z_red_Stein (Zneg $a) (Zneg $b) ↪ Zneg (red_by_Stein_v2 $a $b);

// Cross-product correctness: (a/gcd)·b = a·(b/gcd). Since the gcd is symmetric,
// this form avoids naming the gcd explicitly. Consumed by Q.lp normalization.
//
// Reduces to red_by_Stein_v2_cross on the ℙ payload in each sign combination;
// the Z0 cases close by reflexivity.
opaque symbol Z_red_Stein_correct a b :
  π (Z_red_Stein a b * b = a * Z_red_Stein b a) ≔
begin
  induction
  // a = Z0
  { induction
    { reflexivity }
    { assume y; reflexivity }
    { assume y; reflexivity } }
  // a = Zpos x
  { assume x;
    induction
    { reflexivity }
    { assume y; simplify; apply feq (Zpos); refine red_by_Stein_v2_cross x y }
    { assume y; simplify; apply feq (Zneg); refine red_by_Stein_v2_cross x y } }
  // a = Zneg x
  { assume x;
    induction
    { reflexivity }
    { assume y; simplify; apply feq (Zneg); refine red_by_Stein_v2_cross x y }
    { assume y; simplify; apply feq (Zpos); refine red_by_Stein_v2_cross x y } }
end;
