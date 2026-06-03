require open Stdlib.Zgcd;

symbol ℚ : TYPE;
symbol rat: Set;
rule τ rat ↪ ℚ;

// The symbol `rat` denotes any fraction while `/` denotes irreducible fractions.
injective symbol frac : ℤ → ℤ → ℚ; // raw fraction constructor

symbol ind_Rat : Π p0: (ℚ → Prop), (Π x: ℤ, Π y: ℤ, π (p0 (frac x y))) → Π x: ℚ, π (p0 x);
rule ind_Rat $p0 $frac (frac $x $y) ↪ $frac $x $y;


injective symbol / : ℤ → ℤ → ℚ; notation / infix right 30;

rule frac $x $y ↪ (sign $y * Z_red_Stein $x $y) / (sign $y * Z_red_Stein $y $x);


symbol ᵣ+  : ℚ → ℚ → ℚ; notation ᵣ+ infix right 20;
symbol ᵣ- : ℚ → ℚ → ℚ; notation ᵣ- infix left 20;
symbol *ᵣ  : ℚ → ℚ → ℚ; notation *ᵣ infix right 22;
symbol —ᵣ : ℚ → ℚ; notation —ᵣ prefix 24;

rule ($x / $y) ᵣ+ ($u / $v) ↪ frac (($x * $v) + ($u * $y)) ($y * $v);
rule ($x / $y) *ᵣ ($u / $v) ↪ frac ( $x * $u ) ( $y * $v );

rule —ᵣ (Zpos $x / Zpos $y) ↪ (Zneg $x / Zpos $y)
with —ᵣ (Zneg $x / Zpos $y) ↪ (Zpos $x / Zpos $y)
with —ᵣ (0 / $d) ↪ (0 / $d);

symbol inj_z : ℤ → ℚ;
rule inj_z $x ↪ $x / 1;

coerce_rule coerce ℤ ℚ $x ↪ inj_z $x;

compute frac 152 12;

rule _ / 0 ↪ 0 / 1;
rule 0 / Zpos (I _) ↪ 0 / 1
with 0 / Zpos (O _) ↪ 0 / 1
with 0 / Zneg (I _) ↪ 0 / 1
with 0 / Zneg (O _) ↪ 0 / 1
with 0 / Zneg H ↪ 0 / 1;

rule (Zneg $x) / (Zneg $y) ↪ Zpos $x / Zpos $y;
rule (Zpos $x) / (Zneg $y) ↪ Zneg $x / Zpos $y;

symbol 0⫽1 : ℚ ≔  Z0 / 1;
symbol 1⫽1 : ℚ ≔  1 / 1;


opaque symbol sign_case x : π (sign x = 1 ∨ sign x = — 1) ≔
begin
    induction
    {apply ∨ᵢ₁;  reflexivity}
    {assume p; apply ∨ᵢ₁;  reflexivity}
    {assume p; apply ∨ᵢ₂;  reflexivity}
end;

opaque symbol sign_inj x : π (sign (sign x) = sign x) ≔
begin
    induction
    {reflexivity}
    {assume p; reflexivity}
    {assume p; reflexivity}
end;

opaque symbol frac_neg n d : π (frac (— n) (— d) = frac n d) ≔
begin
    simplify;
    induction
    {
        induction
        {reflexivity}
        {assume p; reflexivity}
        {assume p; reflexivity}
    }
    {
        assume p;
        induction
        {reflexivity}
        {assume q; reflexivity}
        {assume q; reflexivity}
    }
    {
        assume p;
        induction
        {reflexivity}
        {assume q; reflexivity}
        {assume q; reflexivity}
    }
end;

opaque symbol neg_neg_cancel_div n d : π (((— n) / (— d)) = (n / d)) ≔
begin
    induction
    {
        induction
        {reflexivity}
        {
            simplify;
            induction
            {assume p ih; simplify; reflexivity }
            {assume p ih; simplify; reflexivity }
            {reflexivity}
        }
        {
            simplify;
            induction
            {assume p ih; simplify; reflexivity }
            {assume p ih; simplify; reflexivity }
            {reflexivity}
        }
    }
    {
        assume p;
        simplify —;
        induction
        {
            reflexivity
        }
        {
            assume q;
            simplify —;
            reflexivity
        }
        {
            assume q;
            simplify;
            reflexivity
        }
    }
    {
         assume p;
        simplify —;
        induction
        {
            reflexivity
        }
        {
            assume q;
            simplify —;
            reflexivity
        }
        {
            assume q;
            simplify;
            reflexivity
        }
    }
end;

opaque symbol frac_0_num d: π (frac 0 d = 0 / 1) ≔
begin
    induction
    {reflexivity}
    {reflexivity}
    {reflexivity}
end;

opaque symbol div_0_num d: π (0 / d = 0 / 1) ≔
begin
   simplify;
    //assume d;
    induction
    {reflexivity}
    {induction {reflexivity} {reflexivity} {reflexivity}}
    {induction {reflexivity} {reflexivity} {reflexivity}}
end;

opaque symbol frac_0_den n: π (frac n 0 = 0 / 1) ≔
begin
    induction
    {reflexivity}
    {reflexivity;}
    {reflexivity}
end;

symbol 0⫽n_is_0⫽1  n : π (0 / n = 0 / 1) ≔
begin
    induction
    {reflexivity}
    {induction {reflexivity} {reflexivity} {reflexivity}}
    {induction {reflexivity} {reflexivity} { reflexivity }} 
end;

symbol *ᵣ_com_div n1 d1 n2 d2 :  π ((n1 / d1) *ᵣ (n2 / d2) = (n2 / d2) *ᵣ  (n1 / d1) ) ≔
begin
assume n1 d1 n2 d2;
simplify *ᵣ;
refine @feq2 int int rat (frac) (n1 * n2) (n2 * n1)  _ (d1 * d2) (d2 * d1)  _ 
{ rewrite *_com; reflexivity }
{ rewrite *_com; reflexivity }
end;

symbol ᵣ+_com_div n1 d1 n2 d2 :  π ((n1 / d1) ᵣ+ (n2 / d2) = (n2 / d2) ᵣ+  (n1 / d1) ) ≔
begin
assume n1 d1 n2 d2;
simplify ᵣ+;
apply @feq2 int int rat (frac) ((n1 * d2) + (n2 * d1)) ((n2 * d1) + (n1 * d2))  _ (d1 * d2) (d2 * d1) _ 
{ rewrite +_com; reflexivity }
{ rewrite *_com; reflexivity }
end;

// ============================================================
// Foundational axioms for rational associativity.
// These encapsulate the GCD theory needed to prove that fraction
// normalization respects rational equality. Postulated; their full
// proof from the binary Stein algorithm in Zgcd.lp requires substantial
// divisibility/coprimality lemmas and is left for future work.
//
// (1) Cross-product of GCD reduction is now DISCHARGED: it is exactly
//     Z_red_Stein_correct, proved in Zgcd.lp from the fuel-based ggcd
//     (ggcd_fuel_correct + ggcd_fuel_sym). Used below via that name.

// (2) Standard cross-multiplication characterization of rational equality.
//     For nonzero b, d: frac a b = frac c d iff a*d = c*b.
//     NOW PROVEN (see `frac_eq` below, after the supporting lemmas).
//     Integral-domain helper: c·b = 0 with b ≠ 0 forces c = 0.
opaque symbol mul_eq_0_l c b : π (c * b = Z0) → π (b ≠ 0) → π (c = Z0) ≔
begin
  induction
  { assume b h hb; reflexivity }
  { assume pc; induction
    { assume h hb; apply ⊥ₑ; refine hb _; reflexivity }
    { assume pb h hb; apply ⊥ₑ; refine Zpos≠Z0 (mul pc pb) h }
    { assume pb h hb; apply ⊥ₑ; refine Zneg≠Z0 (mul pc pb) h } }
  { assume pc; induction
    { assume h hb; apply ⊥ₑ; refine hb _; reflexivity }
    { assume pb h hb; apply ⊥ₑ; refine Zneg≠Z0 (mul pc pb) h }
    { assume pb h hb; apply ⊥ₑ; refine Zpos≠Z0 (mul pc pb) h } }
end;

// (3) Non-zero preservation lemmas (now PROVEN by case analysis on the
//     Z0/Zpos/Zneg shapes, using the integral-domain mul rules and the
//     constructor discriminators Zpos≠Z0 / Zneg≠Z0).
opaque symbol mul_ne_0 a b : π (a ≠ 0) → π (b ≠ 0) → π (a * b ≠ 0) ≔
begin
  induction
  { assume b ha hb; apply ⊥ₑ; refine ha _; reflexivity }
  { assume pa; induction
    { assume ha hb; apply ⊥ₑ; refine hb _; reflexivity }
    { assume pb ha hb; refine Zpos≠Z0 (mul pa pb) }
    { assume pb ha hb; refine Zneg≠Z0 (mul pa pb) } }
  { assume pa; induction
    { assume ha hb; apply ⊥ₑ; refine hb _; reflexivity }
    { assume pb ha hb; refine Zneg≠Z0 (mul pa pb) }
    { assume pb ha hb; refine Zpos≠Z0 (mul pa pb) } }
end;

opaque symbol sign_ne_0 a : π (a ≠ 0) → π (sign a ≠ 0) ≔
begin
  induction
  { assume ha; refine Zpos≠Z0 H }
  { assume pa ha; refine Zpos≠Z0 H }
  { assume pa ha; refine Zneg≠Z0 H }
end;

opaque symbol Z_red_Stein_l_ne_0 a b : π (a ≠ 0) → π (Z_red_Stein a b ≠ 0) ≔
begin
  induction
  { assume b ha; apply ⊥ₑ; refine ha _; reflexivity }
  { assume pa; induction
    { assume ha; refine Zpos≠Z0 H }
    { assume pb ha; refine Zpos≠Z0 (red_by_Stein_v2 pa pb) }
    { assume pb ha; refine Zpos≠Z0 (red_by_Stein_v2 pa pb) } }
  { assume pa; induction
    { assume ha; refine Zneg≠Z0 H }
    { assume pb ha; refine Zneg≠Z0 (red_by_Stein_v2 pa pb) }
    { assume pb ha; refine Zneg≠Z0 (red_by_Stein_v2 pa pb) } }
end;

// Scaled cross-product: with sign factors, the cross-product identity
// for the normalized numerator/denominator pair.
opaque symbol frac_red_cross b A :
  π ((sign b * Z_red_Stein A b) * b = A * (sign b * Z_red_Stein b A)) ≔
begin
    assume b A;
    rewrite *_assoc;
    rewrite Z_red_Stein_correct;
    rewrite left *_assoc;
    rewrite *_com (sign b) A;
    rewrite *_assoc;
    reflexivity
end;

// The normalized denominator sign b · Z_red_Stein b a is positive: it equals
// Zpos of the ℙ reduction of |b|/|a|. (4 nonzero sign cases, each reflexivity.)
opaque symbol denom_pos a b :
  π (a ≠ 0) → π (b ≠ 0) →
  π (sign b * Z_red_Stein b a = Zpos (red_by_Stein_v2 (unZpos b) (unZpos a))) ≔
begin
  induction
  { assume b ha hb; apply ⊥ₑ; refine ha _; reflexivity }
  { assume pa; induction
    { assume ha hb; apply ⊥ₑ; refine hb _; reflexivity }
    { assume pb ha hb; reflexivity }
    { assume pb ha hb; reflexivity } }
  { assume pa; induction
    { assume ha hb; apply ⊥ₑ; refine hb _; reflexivity }
    { assume pb ha hb; reflexivity }
    { assume pb ha hb; reflexivity } }
end;

// |a·b| = |a|·|b| at the ℙ payload level (for nonzero a, b).
opaque symbol unZpos_mul a b :
  π (a ≠ 0) → π (b ≠ 0) →
  π (unZpos (a * b) = mul (unZpos a) (unZpos b)) ≔
begin
  induction
  { assume b ha hb; apply ⊥ₑ; refine ha _; reflexivity }
  { assume pa; induction
    { assume ha hb; apply ⊥ₑ; refine hb _; reflexivity }
    { assume pb ha hb; reflexivity }
    { assume pb ha hb; reflexivity } }
  { assume pa; induction
    { assume ha hb; apply ⊥ₑ; refine hb _; reflexivity }
    { assume pb ha hb; reflexivity }
    { assume pb ha hb; reflexivity } }
end;

// Uniform non-degenerate case: all of a,b,c,d nonzero.
// Denominators match via ℙ uniqueness (red_unique); numerators then match
// by cross-multiplication (frac_red_cross) + cancellation — no sign casework.
opaque symbol frac_eq_nz a b c d :
  π (a ≠ 0) → π (b ≠ 0) → π (c ≠ 0) → π (d ≠ 0) →
  π (a * d = c * b) → π (frac a b = frac c d) ≔
begin
  assume a b c d ha hb hc hd hcross;
  have hmul : π (mul (unZpos a) (unZpos d) = mul (unZpos c) (unZpos b))
    { rewrite left (unZpos_mul a d ha hd);
      rewrite left (unZpos_mul c b hc hb);
      refine feq unZpos hcross };
  have hD : π (sign b * Z_red_Stein b a = sign d * Z_red_Stein d c)
    { rewrite (denom_pos a b ha hb);
      rewrite (denom_pos c d hc hd);
      refine feq Zpos (∧ₑ₂ (red_unique (unZpos a) (unZpos b) (unZpos c) (unZpos d) hmul)) };
  have hN : π (sign b * Z_red_Stein a b = sign d * Z_red_Stein c d)
    { refine *_reg_r (sign b * Z_red_Stein a b) (sign d * Z_red_Stein c d) (b * d)
        (mul_ne_0 b d hb hd) _;
      rewrite left *_assoc (sign b * Z_red_Stein a b) b d;
      rewrite (frac_red_cross b a);
      rewrite *_com b d;
      rewrite left *_assoc (sign d * Z_red_Stein c d) d b;
      rewrite (frac_red_cross d c);
      rewrite hD;
      rewrite *_assoc a (sign d * Z_red_Stein d c) d;
      rewrite *_com (sign d * Z_red_Stein d c) d;
      rewrite left *_assoc a d (sign d * Z_red_Stein d c);
      rewrite *_assoc c (sign d * Z_red_Stein d c) b;
      rewrite *_com (sign d * Z_red_Stein d c) b;
      rewrite left *_assoc c b (sign d * Z_red_Stein d c);
      rewrite hcross;
      reflexivity };
  refine @feq2 int int rat (/)
    (sign b * Z_red_Stein a b) (sign d * Z_red_Stein c d) hN
    (sign b * Z_red_Stein b a) (sign d * Z_red_Stein d c) hD
end;

// Main theorem: ℚ-normalization is well-defined.
opaque symbol frac_eq a b c d :
  π (b ≠ 0) → π (d ≠ 0) → π (a * d = c * b) → π (frac a b = frac c d) ≔
begin
  induction
  { assume b c d hb hd hcross;
    have hcb : π (c * b = Z0) { symmetry; refine hcross };
    have hc : π (c = Z0) { refine mul_eq_0_l c b hcb hb };
    rewrite hc;
    rewrite (frac_0_num b);
    rewrite (frac_0_num d);
    reflexivity }
  { assume pa b c d hb hd hcross;
    have ha : π (Zpos pa ≠ 0) { refine Zpos≠Z0 pa };
    have hc : π (c ≠ 0)
      { assume hc0;
        refine mul_ne_0 (Zpos pa) d ha hd _;
        rewrite hcross; rewrite hc0; reflexivity };
    refine frac_eq_nz (Zpos pa) b c d ha hb hc hd hcross }
  { assume pa b c d hb hd hcross;
    have ha : π (Zneg pa ≠ 0) { refine Zneg≠Z0 pa };
    have hc : π (c ≠ 0)
      { assume hc0;
        refine mul_ne_0 (Zneg pa) d ha hd _;
        rewrite hcross; rewrite hc0; reflexivity };
    refine frac_eq_nz (Zneg pa) b c d ha hb hc hd hcross }
end;

opaque symbol ᵣ+_assoc_div n1 d1 n2 d2 n3 d3
    (hd1 : π (d1 ≠ 0)) (hd2 : π (d2 ≠ 0)) (hd3 : π (d3 ≠ 0)) :
    π ((n1 / d1 ᵣ+ n2 /d2) ᵣ+ n3 / d3 = (n1 / d1) ᵣ+ n2 / d2 ᵣ+  n3 / d3) ≔
begin
    assume n1 d1 n2 d2 n3 d3 hd1 hd2 hd3;
    simplify ᵣ+;
    // Derive non-zero conditions for the normalized denominators.
    have hd1d2 : π (d1 * d2 ≠ 0) { refine mul_ne_0 _ _ hd1 hd2 };
    have hd2d3 : π (d2 * d3 ≠ 0) { refine mul_ne_0 _ _ hd2 hd3 };
    have hD12 : π (sign (d1 * d2) * Z_red_Stein (d1 * d2) ((n1 * d2) + (n2 * d1)) ≠ 0)
        { refine mul_ne_0 _ _ (sign_ne_0 _ hd1d2)
            (Z_red_Stein_l_ne_0 (d1 * d2) ((n1 * d2) + (n2 * d1)) hd1d2) };
    have hD23 : π (sign (d2 * d3) * Z_red_Stein (d2 * d3) ((n2 * d3) + (n3 * d2)) ≠ 0)
        { refine mul_ne_0 _ _ (sign_ne_0 _ hd2d3)
            (Z_red_Stein_l_ne_0 (d2 * d3) ((n2 * d3) + (n3 * d2)) hd2d3) };
    // Apply the cross-multiplication characterization of rational equality.
    refine frac_eq _ _ _ _ (mul_ne_0 _ _ hD12 hd3) (mul_ne_0 _ _ hd1 hD23) _;
    // ===== Cross-multiplication identity at the integer level =====
    //   ((N12·d3 + n3·D12) · (d1·D23))  =  ((n1·D23 + N23·d1) · (D12·d3))
    // where N12, D12 = normalized num/den of (n1/d1 ⊕ n2/d2),
    //       N23, D23 = normalized num/den of (n2/d2 ⊕ n3/d3).
    //
    // Strategy: introduce a d2 factor (via *_reg_r), use frac_red_cross
    // to substitute  N12·(d1·d2) = (n1·d2 + n2·d1)·D12  and similarly for
    // N23. Both sides reduce to D12·D23·(n1·d2·d3 + n2·d1·d3 + n3·d1·d2).
    set N12 ≔ sign (d1 * d2) * Z_red_Stein ((n1 * d2) + (n2 * d1)) (d1 * d2);
    set D12 ≔ sign (d1 * d2) * Z_red_Stein (d1 * d2) ((n1 * d2) + (n2 * d1));
    set N23 ≔ sign (d2 * d3) * Z_red_Stein ((n2 * d3) + (n3 * d2)) (d2 * d3);
    set D23 ≔ sign (d2 * d3) * Z_red_Stein (d2 * d3) ((n2 * d3) + (n3 * d2));
    have R1 : π (N12 * (d1 * d2) = ((n1 * d2) + (n2 * d1)) * D12)
        { refine frac_red_cross (d1 * d2) ((n1 * d2) + (n2 * d1)) };
    have R2 : π (N23 * (d2 * d3) = ((n2 * d3) + (n3 * d2)) * D23)
        { refine frac_red_cross (d2 * d3) ((n2 * d3) + (n3 * d2)) };
    refine *_reg_r _ _ d2 hd2 _;
    // After *_reg_r the goal is
    //   ((N12·d3 + n3·D12)·(d1·D23))·d2 = ((n1·D23 + N23·d1)·(D12·d3))·d2.
    // We distribute both sums and the trailing d2:
    rewrite *_com ((N12 * d3) + (n3 * D12)) (d1 * D23);
    rewrite *_distr_+;
    rewrite *_com ((n1 * D23) + (N23 * d1)) (D12 * d3);
    rewrite *_distr_+;
    rewrite *_com (((d1 * D23) * (N12 * d3)) + ((d1 * D23) * (n3 * D12))) d2;
    rewrite *_distr_+;
    rewrite *_com (((D12 * d3) * (n1 * D23)) + ((D12 * d3) * (N23 * d1))) d2;
    rewrite *_distr_+;
    // Goal is now
    //   d2·((d1·D23)·(N12·d3)) + d2·((d1·D23)·(n3·D12)) =
    //   d2·((D12·d3)·(n1·D23)) + d2·((D12·d3)·(N23·d1))
    //
    // Re-associate the first LHS monomial to expose N12·(d1·d2), apply R1:
    rewrite left *_assoc d2 (d1 * D23) (N12 * d3);
    rewrite left *_assoc d2 d1 D23;
    rewrite *_com d2 d1;
    rewrite *_assoc (d1 * d2) D23 (N12 * d3);
    rewrite *_com D23 (N12 * d3);
    rewrite left *_assoc (d1 * d2) (N12 * d3) D23;
    rewrite *_com (d1 * d2) (N12 * d3);
    rewrite *_assoc N12 d3 (d1 * d2);
    rewrite *_com d3 (d1 * d2);
    rewrite left *_assoc N12 (d1 * d2) d3;
    rewrite R1;
    // Symmetric substitution on the RHS to expose N23·(d2·d3), apply R2:
    rewrite left *_assoc d2 (D12 * d3) (N23 * d1);
    rewrite *_com d2 (D12 * d3);
    rewrite *_assoc D12 d3 d2;
    rewrite *_com d3 d2;
    rewrite *_com (D12 * (d2 * d3)) (N23 * d1);
    rewrite *_assoc N23 d1 (D12 * (d2 * d3));
    rewrite *_com d1 (D12 * (d2 * d3));
    rewrite left *_assoc N23 (D12 * (d2 * d3)) d1;
    rewrite *_com N23 (D12 * (d2 * d3));
    rewrite *_assoc D12 (d2 * d3) N23;
    rewrite *_com (d2 * d3) N23;
    rewrite R2;
    // Distribute the two binomial sums via *_distr_+ (using *_com to swap
    // each sum to the right-hand side of a multiplication so *_distr_+ matches):
    rewrite *_com ((n1 * d2) + (n2 * d1)) D12;
    rewrite *_distr_+;
    rewrite *_com ((n2 * d3) + (n3 * d2)) D23;
    rewrite *_distr_+;
    rewrite *_com ((D12 * (n1 * d2)) + (D12 * (n2 * d1))) d3;
    rewrite *_distr_+;
    rewrite *_com ((d3 * (D12 * (n1 * d2))) + (d3 * (D12 * (n2 * d1)))) D23;
    rewrite *_distr_+;
    rewrite *_distr_+;
    rewrite *_com ((D12 * (D23 * (n2 * d3))) + (D12 * (D23 * (n3 * d2)))) d1;
    rewrite *_distr_+;
    // Now both sides are sums of 3 monomials each, each a product of the same
    // 5 atoms in different order. Reassociate the LHS sum to align bracketing:
    rewrite +_assoc;
    // Permute the factors of the first LHS monomial to match the first RHS monomial:
    rewrite *_com D12 (n1 * d2);
    rewrite *_com n1 d2;
    rewrite *_assoc d2 n1 D12;
    rewrite *_com d3 (d2 * (n1 * D12));
    rewrite *_assoc d2 (n1 * D12) d3;
    rewrite *_com D23 (d2 * ((n1 * D12) * d3));
    rewrite *_assoc d2 ((n1 * D12) * d3) D23;
    rewrite *_com n1 D12;
    rewrite *_assoc D12 n1 d3;
    rewrite *_com n1 d3;
    rewrite left *_assoc D12 d3 n1;
    rewrite *_assoc (D12 * d3) n1 D23;
    // Permute the second LHS monomial to match the second RHS monomial:
    rewrite *_com D12 (n2 * d1);
    rewrite *_com n2 d1;
    rewrite *_assoc d1 n2 D12;
    rewrite *_com d3 (d1 * (n2 * D12));
    rewrite *_assoc d1 (n2 * D12) d3;
    rewrite *_com D23 (d1 * ((n2 * D12) * d3));
    rewrite *_assoc d1 ((n2 * D12) * d3) D23;
    rewrite *_com n2 D12;
    rewrite *_assoc D12 n2 d3;
    rewrite *_assoc D12 (n2 * d3) D23;
    rewrite *_com (n2 * d3) D23;
    // Permute the third LHS monomial to match the third RHS monomial:
    rewrite *_com d2 ((d1 * D23) * (n3 * D12));
    rewrite *_assoc (d1 * D23) (n3 * D12) d2;
    rewrite *_assoc d1 D23 ((n3 * D12) * d2);
    rewrite *_com n3 D12;
    rewrite *_assoc D12 n3 d2;
    rewrite *_com D23 (D12 * (n3 * d2));
    rewrite *_assoc D12 (n3 * d2) D23;
    rewrite *_com (n3 * d2) D23;
    reflexivity
end;

// Associativity of ᵣ+ on raw `frac n d` triples with all denominators ≠ 0.
// Lifts ᵣ+_assoc_div by feeding it the *normalized* numerator/denominators
// (which are exactly what `frac n d` reduces to under the frac rewrite rule).
opaque symbol ᵣ+_assoc_nz n1 d1 n2 d2 n3 d3 :
    π (d1 ≠ 0) → π (d2 ≠ 0) → π (d3 ≠ 0) →
    π (((frac n1 d1 ᵣ+ frac n2 d2) ᵣ+ frac n3 d3) = (frac n1 d1 ᵣ+ (frac n2 d2 ᵣ+ frac n3 d3))) ≔
begin
  assume n1 d1 n2 d2 n3 d3 hd1 hd2 hd3;
  have hD1 : π (sign d1 * Z_red_Stein d1 n1 ≠ 0)
    { refine mul_ne_0 (sign d1) (Z_red_Stein d1 n1)
        (sign_ne_0 d1 hd1) (Z_red_Stein_l_ne_0 d1 n1 hd1) };
  have hD2 : π (sign d2 * Z_red_Stein d2 n2 ≠ 0)
    { refine mul_ne_0 (sign d2) (Z_red_Stein d2 n2)
        (sign_ne_0 d2 hd2) (Z_red_Stein_l_ne_0 d2 n2 hd2) };
  have hD3 : π (sign d3 * Z_red_Stein d3 n3 ≠ 0)
    { refine mul_ne_0 (sign d3) (Z_red_Stein d3 n3)
        (sign_ne_0 d3 hd3) (Z_red_Stein_l_ne_0 d3 n3 hd3) };
  refine ᵣ+_assoc_div (sign d1 * Z_red_Stein n1 d1) (sign d1 * Z_red_Stein d1 n1)
                       (sign d2 * Z_red_Stein n2 d2) (sign d2 * Z_red_Stein d2 n2)
                       (sign d3 * Z_red_Stein n3 d3) (sign d3 * Z_red_Stein d3 n3)
                       hD1 hD2 hD3
end;


opaque symbol ᵣ+_com x y :  π (x ᵣ+ y = y ᵣ+  x) ≔
begin
    refine ind_Rat (λ u, `∀ y, (u ᵣ+ y) = (y ᵣ+ u)) _;
    assume n1 d1;
    refine ind_Rat (λ u, (frac n1 d1 ᵣ+ u) = (u ᵣ+ frac n1 d1)) _;
    assume n2 d2;
    simplify frac;
    set N1 ≔ (sign d1 * Z_red_Stein n1 d1);
    set D1 ≔ (sign d1 * Z_red_Stein d1 n1);
    set N2 ≔ (sign d2 * Z_red_Stein n2 d2);
    set D2 ≔ (sign d2 * Z_red_Stein d2 n2);
    refine ᵣ+_com_div N1 D1 N2 D2
end;

opaque symbol ᵣ*_com x y :  π (x *ᵣ y = y *ᵣ x) ≔
begin
    refine ind_Rat (λ u, `∀ y, (u *ᵣ y) = (y *ᵣ u)) _;
    assume n1 d1;
    refine ind_Rat (λ u, (frac n1 d1 *ᵣ u) = (u *ᵣ frac n1 d1)) _;
    assume n2 d2;
     simplify frac;
    set N1 ≔ (sign d1 * Z_red_Stein n1 d1);
    set D1 ≔ (sign d1 * Z_red_Stein d1 n1);
    set N2 ≔ (sign d2 * Z_red_Stein n2 d2);
    set D2 ≔ (sign d2 * Z_red_Stein d2 n2);
    refine *ᵣ_com_div N1 D1 N2 D2
end;

opaque symbol *_neutral_l x : π ((1 * x) = x) ≔
begin
  induction {reflexivity} {reflexivity} {reflexivity}
end;

opaque symbol *_cancel_l x : π ((0 * x) = 0) ≔
begin
  induction {reflexivity} {reflexivity} {reflexivity}
end;

// Left/right neutrality stated with the raw constructor (Zpos H) rather than
// the `1` symbol, so `rewrite` matches the `Zpos H` factors produced by sign
// reduction (sign (Zpos _) ↪ Zpos H) inside normalized fractions.
opaque symbol mul1_l z : π (Zpos H * z = z) ≔
begin
  induction {reflexivity} {reflexivity} {reflexivity}
end;

opaque symbol mul1_r z : π (z * Zpos H = z) ≔
begin
  induction {reflexivity} {reflexivity} {reflexivity}
end;

// Multiplication by Zneg H (= -1) is negation; needed for the Zneg-sign branch
// where sign (Zneg _) ↪ Zneg H appears as a factor.
opaque symbol mulm1_l z : π (Zneg H * z = — z) ≔
begin
  induction {reflexivity} {reflexivity} {reflexivity}
end;

// NOTE: stated with `frac n d` on the RHS, not raw `n / d`. Addition normalizes
// its result (frac reduces to lowest terms), so `0/1 ᵣ+ n/d` equals the
// *normalized* fraction `frac n d`. The raw form `= n / d` is FALSE for
// non-reduced inputs (e.g. n=2, d=4 gives 1/2 ≠ 2/4).
opaque symbol div_add_neutral_l n d : π ((0 / 1 ᵣ+ n / d) = frac n d) ≔
begin
  assume n;
  induction
  { reflexivity }
  { assume p;
    refine frac_eq ((0 * Zpos p) + (n * 1)) (1 * Zpos p) n (Zpos p) _ _ _
    { refine mul_ne_0 1 (Zpos p) (Zpos≠Z0 H) (Zpos≠Z0 p) }
    { refine Zpos≠Z0 p }
    { rewrite *_cancel_l;
      rewrite *_neutral;
      rewrite *_neutral_l;
      reflexivity } }
  { assume p;
    refine frac_eq ((0 * Zneg p) + (n * 1)) (1 * Zneg p) n (Zneg p) _ _ _
    { refine mul_ne_0 1 (Zneg p) (Zpos≠Z0 H) (Zneg≠Z0 p) }
    { refine Zneg≠Z0 p }
    { rewrite *_cancel_l;
      rewrite *_neutral;
      rewrite *_neutral_l;
      reflexivity } }
end;

// Restated with `frac n d` on the RHS for the same reason as div_add_neutral_l.
opaque symbol div_add_neutral_r n d : π ((n / d ᵣ+ 0 / 1) = frac n d) ≔
begin
  assume n;
  induction
  { reflexivity }
  { assume p;
    refine frac_eq ((n * 1) + (0 * Zpos p)) (Zpos p * 1) n (Zpos p) _ _ _
    { refine mul_ne_0 (Zpos p) 1 (Zpos≠Z0 p) (Zpos≠Z0 H) }
    { refine Zpos≠Z0 p }
    { rewrite *_cancel_l;
      rewrite *_neutral;
      rewrite *_neutral;
      reflexivity } }
  { assume p;
    refine frac_eq ((n * 1) + (0 * Zneg p)) (Zneg p * 1) n (Zneg p) _ _ _
    { refine mul_ne_0 (Zneg p) 1 (Zneg≠Z0 p) (Zpos≠Z0 H) }
    { refine Zneg≠Z0 p }
    { rewrite *_cancel_l;
      rewrite *_neutral;
      rewrite *_neutral;
      reflexivity } }
end;

opaque symbol ᵣ+_neutral_frac_l x : π ((frac 0 1 ᵣ+ x) = x) ≔
begin
  refine ind_Rat (λ u, ((frac 0 1 ᵣ+ u) = u)) _;
  assume n;
  induction
  { reflexivity }
  { assume p;
    set N ≔ sign (Zpos p) * Z_red_Stein n (Zpos p);
    set D ≔ sign (Zpos p) * Z_red_Stein (Zpos p) n;
    refine frac_eq ((0 * D) + (N * 1)) (1 * D) n (Zpos p) _ _ _
    { refine mul_ne_0 1 D (Zpos≠Z0 H)
        (mul_ne_0 (sign (Zpos p)) (Z_red_Stein (Zpos p) n)
           (sign_ne_0 (Zpos p) (Zpos≠Z0 p))
           (Z_red_Stein_l_ne_0 (Zpos p) n (Zpos≠Z0 p))) }
    { refine Zpos≠Z0 p }
    { simplify;
      rewrite mul1_r;
      rewrite mul1_l;
      rewrite mul1_l;
      rewrite mul1_l;
      refine Z_red_Stein_correct n (Zpos p) } }
  { assume p;
    set N ≔ sign (Zneg p) * Z_red_Stein n (Zneg p);
    set D ≔ sign (Zneg p) * Z_red_Stein (Zneg p) n;
    refine frac_eq ((0 * D) + (N * 1)) (1 * D) n (Zneg p) _ _ _
    { refine mul_ne_0 1 D (Zpos≠Z0 H)
        (mul_ne_0 (sign (Zneg p)) (Z_red_Stein (Zneg p) n)
           (sign_ne_0 (Zneg p) (Zneg≠Z0 p))
           (Z_red_Stein_l_ne_0 (Zneg p) n (Zneg≠Z0 p))) }
    { refine Zneg≠Z0 p }
    { simplify;
      rewrite mul1_r;
      rewrite mul1_l;
      rewrite mulm1_l;
      rewrite mulm1_l;
      rewrite left neg_mul_l;
      rewrite left neg_mul_r;
      rewrite Z_red_Stein_correct;
      reflexivity } }
end;

opaque symbol ᵣ+_neutral_l x : π ((frac 0 1 ᵣ+ x) = x) ≔
begin
  assume x;
  refine ᵣ+_neutral_frac_l x
end;

opaque symbol ᵣ+_neutral_r x : π ((x ᵣ+ frac 0 1) = x) ≔
begin
  assume x;
  rewrite (ᵣ+_com x (frac 0 1));
  refine ᵣ+_neutral_frac_l x
end;

// `0 / 1` is definitionally `frac 0 1`, so these are the raw-`/` twins of
// ᵣ+_neutral_l / ᵣ+_neutral_r and close by delegation.
opaque symbol ᵣ+_neutral_div_l x : π ((0 / 1 ᵣ+ x) = x) ≔
begin
  assume x;
  refine ᵣ+_neutral_frac_l x
end;

opaque symbol ᵣ+_neutral_div_r x : π ((x ᵣ+ 0 / 1) = x) ≔
begin
  assume x;
  refine ᵣ+_neutral_r x
end;

opaque symbol ᵣ*_neutral_l x : π ((frac 1 1 *ᵣ x) = x) ≔
begin
  refine ind_Rat (λ u, (frac 1 1 *ᵣ u) = u) _;
  assume n;
  induction
  { reflexivity }
  { assume p;
    set N ≔ sign (Zpos p) * Z_red_Stein n (Zpos p);
    set D ≔ sign (Zpos p) * Z_red_Stein (Zpos p) n;
    refine frac_eq (1 * N) (1 * D) n (Zpos p) _ _ _
    { refine mul_ne_0 1 D (Zpos≠Z0 H)
        (mul_ne_0 (sign (Zpos p)) (Z_red_Stein (Zpos p) n)
           (sign_ne_0 (Zpos p) (Zpos≠Z0 p))
           (Z_red_Stein_l_ne_0 (Zpos p) n (Zpos≠Z0 p))) }
    { refine Zpos≠Z0 p }
    { rewrite *_neutral_l;
      rewrite *_neutral_l;
      refine frac_red_cross (Zpos p) n } }
  { assume p;
    set N ≔ sign (Zneg p) * Z_red_Stein n (Zneg p);
    set D ≔ sign (Zneg p) * Z_red_Stein (Zneg p) n;
    refine frac_eq (1 * N) (1 * D) n (Zneg p) _ _ _
    { refine mul_ne_0 1 D (Zpos≠Z0 H)
        (mul_ne_0 (sign (Zneg p)) (Z_red_Stein (Zneg p) n)
           (sign_ne_0 (Zneg p) (Zneg≠Z0 p))
           (Z_red_Stein_l_ne_0 (Zneg p) n (Zneg≠Z0 p))) }
    { refine Zneg≠Z0 p }
    { rewrite *_neutral_l;
      rewrite *_neutral_l;
      refine frac_red_cross (Zneg p) n } }
end;

opaque symbol ᵣ*_neutral_r x : π ((x *ᵣ frac 1 1) = x) ≔
begin
  assume x;
  rewrite (ᵣ*_com x (frac 1 1));
  refine ᵣ*_neutral_l x
end;

// `1 / 1` and `frac 1 1` are convertible (frac 1 1 reduces to 1/1), so the
// raw-`/` twins follow by delegation to ᵣ*_neutral_l / _r.
opaque symbol ᵣ*_neutral_div_l x : π ((1 / 1 *ᵣ x) = x) ≔
begin
  assume x;
  refine ᵣ*_neutral_l x
end;

opaque symbol ᵣ*_neutral_div_r x : π ((x *ᵣ 1 / 1) = x) ≔
begin
  assume x;
  refine ᵣ*_neutral_r x
end;

symbol nze_frac : π (0 / 1 = frac 0 1) ≔
begin reflexivity end;

// Lifting ᵣ+_assoc_div to abstract ℚ requires handling the degenerate
// case where d1, d2, or d3 = 0 (these reduce via the rule _/0 → 0/1
// and require the still-admitted neutral element lemmas
// ᵣ+_neutral_div_l / _r). Admitted for now; the meaty case lives in
// ᵣ+_assoc_div above.
opaque symbol ᵣ+_assoc x y z :  π (((x ᵣ+ y) ᵣ+ z) = (x ᵣ+ (y ᵣ+ z))) ≔
begin
  refine ind_Rat (λ u, `∀ b, `∀ c, ((u ᵣ+ b) ᵣ+ c) = (u ᵣ+ (b ᵣ+ c))) _;
  assume n1;
  induction
  // d1 = Z0
  { assume b c;
    rewrite (frac_0_den n1);
    rewrite (ᵣ+_neutral_div_l b);
    rewrite (ᵣ+_neutral_div_l (b ᵣ+ c));
    reflexivity }
  // d1 = Zpos p1
  { assume p1;
    refine ind_Rat (λ u, `∀ c,
      ((frac n1 (Zpos p1) ᵣ+ u) ᵣ+ c) = (frac n1 (Zpos p1) ᵣ+ (u ᵣ+ c))) _;
    assume n2;
    induction
    // d2 = Z0
    { assume c;
      rewrite (frac_0_den n2);
      rewrite (ᵣ+_neutral_div_r (frac n1 (Zpos p1)));
      rewrite (ᵣ+_neutral_div_l c);
      reflexivity }
    // d2 = Zpos p2
    { assume p2;
      refine ind_Rat (λ u,
        ((frac n1 (Zpos p1) ᵣ+ frac n2 (Zpos p2)) ᵣ+ u)
          = (frac n1 (Zpos p1) ᵣ+ (frac n2 (Zpos p2) ᵣ+ u))) _;
      assume n3;
      induction
      { rewrite (frac_0_den n3);
        rewrite (ᵣ+_neutral_div_r (frac n1 (Zpos p1) ᵣ+ frac n2 (Zpos p2)));
        rewrite (ᵣ+_neutral_div_r (frac n2 (Zpos p2)));
        reflexivity }
      { assume p3;
        refine ᵣ+_assoc_nz n1 (Zpos p1) n2 (Zpos p2) n3 (Zpos p3)
          (Zpos≠Z0 p1) (Zpos≠Z0 p2) (Zpos≠Z0 p3) }
      { assume p3;
        refine ᵣ+_assoc_nz n1 (Zpos p1) n2 (Zpos p2) n3 (Zneg p3)
          (Zpos≠Z0 p1) (Zpos≠Z0 p2) (Zneg≠Z0 p3) } }
    // d2 = Zneg p2
    { assume p2;
      refine ind_Rat (λ u,
        ((frac n1 (Zpos p1) ᵣ+ frac n2 (Zneg p2)) ᵣ+ u)
          = (frac n1 (Zpos p1) ᵣ+ (frac n2 (Zneg p2) ᵣ+ u))) _;
      assume n3;
      induction
      { rewrite (frac_0_den n3);
        rewrite (ᵣ+_neutral_div_r (frac n1 (Zpos p1) ᵣ+ frac n2 (Zneg p2)));
        rewrite (ᵣ+_neutral_div_r (frac n2 (Zneg p2)));
        reflexivity }
      { assume p3;
        refine ᵣ+_assoc_nz n1 (Zpos p1) n2 (Zneg p2) n3 (Zpos p3)
          (Zpos≠Z0 p1) (Zneg≠Z0 p2) (Zpos≠Z0 p3) }
      { assume p3;
        refine ᵣ+_assoc_nz n1 (Zpos p1) n2 (Zneg p2) n3 (Zneg p3)
          (Zpos≠Z0 p1) (Zneg≠Z0 p2) (Zneg≠Z0 p3) } } }
  // d1 = Zneg p1
  { assume p1;
    refine ind_Rat (λ u, `∀ c,
      ((frac n1 (Zneg p1) ᵣ+ u) ᵣ+ c) = (frac n1 (Zneg p1) ᵣ+ (u ᵣ+ c))) _;
    assume n2;
    induction
    { assume c;
      rewrite (frac_0_den n2);
      rewrite (ᵣ+_neutral_div_r (frac n1 (Zneg p1)));
      rewrite (ᵣ+_neutral_div_l c);
      reflexivity }
    { assume p2;
      refine ind_Rat (λ u,
        ((frac n1 (Zneg p1) ᵣ+ frac n2 (Zpos p2)) ᵣ+ u)
          = (frac n1 (Zneg p1) ᵣ+ (frac n2 (Zpos p2) ᵣ+ u))) _;
      assume n3;
      induction
      { rewrite (frac_0_den n3);
        rewrite (ᵣ+_neutral_div_r (frac n1 (Zneg p1) ᵣ+ frac n2 (Zpos p2)));
        rewrite (ᵣ+_neutral_div_r (frac n2 (Zpos p2)));
        reflexivity }
      { assume p3;
        refine ᵣ+_assoc_nz n1 (Zneg p1) n2 (Zpos p2) n3 (Zpos p3)
          (Zneg≠Z0 p1) (Zpos≠Z0 p2) (Zpos≠Z0 p3) }
      { assume p3;
        refine ᵣ+_assoc_nz n1 (Zneg p1) n2 (Zpos p2) n3 (Zneg p3)
          (Zneg≠Z0 p1) (Zpos≠Z0 p2) (Zneg≠Z0 p3) } }
    { assume p2;
      refine ind_Rat (λ u,
        ((frac n1 (Zneg p1) ᵣ+ frac n2 (Zneg p2)) ᵣ+ u)
          = (frac n1 (Zneg p1) ᵣ+ (frac n2 (Zneg p2) ᵣ+ u))) _;
      assume n3;
      induction
      { rewrite (frac_0_den n3);
        rewrite (ᵣ+_neutral_div_r (frac n1 (Zneg p1) ᵣ+ frac n2 (Zneg p2)));
        rewrite (ᵣ+_neutral_div_r (frac n2 (Zneg p2)));
        reflexivity }
      { assume p3;
        refine ᵣ+_assoc_nz n1 (Zneg p1) n2 (Zneg p2) n3 (Zpos p3)
          (Zneg≠Z0 p1) (Zneg≠Z0 p2) (Zpos≠Z0 p3) }
      { assume p3;
        refine ᵣ+_assoc_nz n1 (Zneg p1) n2 (Zneg p2) n3 (Zneg p3)
          (Zneg≠Z0 p1) (Zneg≠Z0 p2) (Zneg≠Z0 p3) } } }
end;


symbol ᵣ≐: ℚ → ℚ → Comp; notation ᵣ≐ infix 10;
rule ($n1 / $d1) ᵣ≐ ($n2 / $d2) ↪ $n1 * $d2 ≐ $n2 * $d1;


// Distributivity of *ᵣ over ᵣ+. The structural reduction (case-bash on the
// denominators d1,d2,d3) is straightforward — degenerate cases use
// `0_mul`/`mul_0` (absorbing 0/1) and the ᵣ+ neutral lemmas. The all-nonzero
// leaf reduces to a cross-product polynomial identity in n_i, d_i and the
// Z_red_Stein normalizations, requiring ~80 lines of careful tree-reshaping
// rewrites of comparable scale to ᵣ+_assoc_div's algebra (and using
// `frac_red_cross` three times to eliminate the normalizations). Left
// admitted; the heart is well-understood and reduces to the polynomial
// identity n1*(n2*d3+n3*d2)*R23*R12*R13 = (sum of two monomials after
// distributing the RHS), which holds modulo commutativity.
opaque symbol ᵣdistr*+ x y z : π(x *ᵣ (y ᵣ+ z) = x *ᵣ y ᵣ+ x *ᵣ z) ≔
begin
admitted;