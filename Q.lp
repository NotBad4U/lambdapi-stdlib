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


// Same precedence as ℤ's `≐` (Z.lp), so that `x ᵣ≐ y = c` parses as
// `(x ᵣ≐ y) = c` rather than binding against `=`.
symbol ᵣ≐: ℚ → ℚ → Comp; notation ᵣ≐ infix 12;
rule ($n1 / $d1) ᵣ≐ ($n2 / $d2) ↪ $n1 * $d2 ≐ $n2 * $d1;

// ============================================================
// Total order on ℚ
//
// Mirrors the ℤ development (Z.lp, "Directional comparison operators"):
// everything is derived from the three-way comparison ᵣ≐, so the four
// relations are definitions, not new symbols with rules. The `ᵣ` prefix
// avoids clashing with the ℤ operators, which are in scope here.
//
// Cross-multiplication is sound for ᵣ≐ because `/`-fractions are
// normalized with a *positive* denominator (see the `frac` rule: the
// denominator is `sign d * Z_red_Stein d n`).
// ============================================================

symbol ᵣ≤ x y ≔ ¬ (istrue (isGt (x ᵣ≐ y)));
notation ᵣ≤ infix 10;

symbol ᵣ< x y ≔ istrue (isLt (x ᵣ≐ y));
notation ᵣ< infix 10;

symbol ᵣ≥ x y ≔ ¬ (x ᵣ< y);
notation ᵣ≥ infix 10;

symbol ᵣ> x y ≔ ¬ (x ᵣ≤ y);
notation ᵣ> infix 10;

// Antisymmetry of the comparison itself: swapping the arguments flips it.
opaque symbol ᵣ≐_com x y : π (x ᵣ≐ y = opp (y ᵣ≐ x)) ≔
begin
  refine ind_Rat (λ u, `∀ v, (u ᵣ≐ v) = opp (v ᵣ≐ u)) _;
  assume n1 d1;
  refine ind_Rat (λ v, (frac n1 d1 ᵣ≐ v) = opp (v ᵣ≐ frac n1 d1)) _;
  assume n2 d2;
  simplify;
  rewrite ≐_com;
  reflexivity
end;

opaque symbol ᵣ≐_Eq x : π (x ᵣ≐ x = Eq) ≔
begin
  refine ind_Rat (λ u, (u ᵣ≐ u) = Eq) _;
  assume n d;
  simplify;
  rewrite ≐_Eq;
  reflexivity
end;

opaque symbol ᵣ≤_refl x : π (x ᵣ≤ x) ≔
begin
  assume x;
  have e : π (istrue (isGt (x ᵣ≐ x)) ⇒ ⊥)
    { rewrite ᵣ≐_Eq; refine λ h, h };
  refine e
end;

// Totality: any two rationals are comparable.
opaque symbol ᵣ≤_total x y : π (x ᵣ≤ y ∨ y ᵣ≤ x) ≔
begin
  assume x y;
  have e : π ((istrue (isGt (x ᵣ≐ y)) ⇒ ⊥) ∨ (istrue (isGt (y ᵣ≐ x)) ⇒ ⊥))
    { rewrite ᵣ≐_com y x;
      refine ind_Comp
        (λ c, (istrue (isGt c) ⇒ ⊥) ∨ (istrue (isGt (opp c)) ⇒ ⊥)) _ _ _ (x ᵣ≐ y)
      { refine ∨ᵢ₁ (λ h, h) }
      { refine ∨ᵢ₁ (λ h, h) }
      { refine ∨ᵢ₂ (λ h, h) } };
  refine e
end;

opaque symbol ᵣ<_ᵣ≤ x y : π (x ᵣ< y ⇒ x ᵣ≤ y) ≔
begin
  assume x y;
  have e : π (istrue (isLt (x ᵣ≐ y)) ⇒ istrue (isGt (x ᵣ≐ y)) ⇒ ⊥)
    { refine ind_Comp (λ c, istrue (isLt c) ⇒ istrue (isGt c) ⇒ ⊥) _ _ _ (x ᵣ≐ y)
      { refine λ h _, h }
      { refine λ _ h, h }
      { refine λ h _, h } };
  refine e
end;

// Irreflexivity of the strict order.
opaque symbol ᵣ<_irrefl x : π (¬ (x ᵣ< x)) ≔
begin
  assume x;
  have e : π (istrue (isLt (x ᵣ≐ x)) ⇒ ⊥)
    { rewrite ᵣ≐_Eq; refine λ h, h };
  refine e
end;

// `x ᵣ≥ y` and `y ᵣ≤ x` agree, i.e. ᵣ≥ is the mirror of ᵣ≤.
opaque symbol ᵣ≤_ᵣ≥ x y : π (x ᵣ≥ y ⇔ y ᵣ≤ x) ≔
begin
  assume x y;
  have e : π ((istrue (isLt (x ᵣ≐ y)) ⇒ ⊥) ⇔ (istrue (isGt (y ᵣ≐ x)) ⇒ ⊥))
    { rewrite ᵣ≐_com y x;
      refine ind_Comp
        (λ c, (istrue (isLt c) ⇒ ⊥) ⇔ (istrue (isGt (opp c)) ⇒ ⊥)) _ _ _ (x ᵣ≐ y)
      { refine ∧ᵢ (λ h, h) (λ h, h) }
      { refine ∧ᵢ (λ h, h) (λ h, h) }
      { refine ∧ᵢ (λ h, h) (λ h, h) } };
  refine e
end;

// `x ᵣ> y` and `y ᵣ< x` agree.
opaque symbol ᵣ<_ᵣ> x y : π (x ᵣ> y ⇔ y ᵣ< x) ≔
begin
  assume x y;
  have e : π ((((istrue (isGt (x ᵣ≐ y)) ⇒ ⊥) ⇒ ⊥)) ⇔ istrue (isLt (y ᵣ≐ x)))
    { rewrite ᵣ≐_com y x;
      refine ind_Comp
        (λ c, (((istrue (isGt c) ⇒ ⊥) ⇒ ⊥)) ⇔ istrue (isLt (opp c))) _ _ _ (x ᵣ≐ y)
      { refine ∧ᵢ (λ h, h (λ k, k)) (λ h _, h) }
      { refine ∧ᵢ (λ h, h (λ k, k)) (λ h _, h) }
      { refine ∧ᵢ (λ _, ⊤ᵢ) (λ _ k, k ⊤ᵢ) } };
  refine e
end;

// ---------- Antisymmetry ----------

// Middle-exchange law for ℤ products, used to shuffle the four factors of a
// cross-product into the pairing we need.
opaque symbol *_swap_mid a b c d : π ((a * b) * (c * d) = (a * c) * (b * d)) ≔
begin
  assume a b c d;
  rewrite *_assoc a b (c * d);
  rewrite left *_assoc b c d;
  rewrite *_com b c;
  rewrite *_assoc c b d;
  rewrite left *_assoc a c (b * d);
  reflexivity
end;

// From a cross-product equality between the *normalized* numerator/denominator
// pairs, recover the cross-product equality between the raw ones. Multiplying
// by D1·D2 (≠ 0) and cancelling, both sides become (N1·D2)·(d1·d2).
opaque symbol cross_denorm n1 d1 n2 d2 N1 D1 N2 D2 :
  π (D1 ≠ 0) → π (D2 ≠ 0) →
  π (N1 * d1 = n1 * D1) → π (N2 * d2 = n2 * D2) →
  π (N1 * D2 = N2 * D1) → π (n1 * d2 = n2 * d1) ≔
begin
  assume n1 d1 n2 d2 N1 D1 N2 D2 hD1 hD2 R1 R2 h;
  refine *_reg_r (n1 * d2) (n2 * d1) (D1 * D2) (mul_ne_0 D1 D2 hD1 hD2) _;
  // (n1·d2)·(D1·D2) = (n2·d1)·(D1·D2)
  rewrite *_swap_mid n1 d2 D1 D2;   // (n1·D1)·(d2·D2)
  rewrite left R1;                  // (N1·d1)·(d2·D2)
  rewrite *_com d2 D2;              // (N1·d1)·(D2·d2)
  rewrite *_swap_mid N1 d1 D2 d2;   // (N1·D2)·(d1·d2)
  rewrite h;                        // (N2·D1)·(d1·d2)
  rewrite *_com D1 D2;              // right side: (n2·d1)·(D2·D1)
  rewrite *_swap_mid n2 d1 D2 D1;   // (n2·D2)·(d1·D1)
  rewrite left R2;                  // (N2·d2)·(d1·D1)
  rewrite *_com d1 D1;              // (N2·d2)·(D1·d1)
  rewrite *_swap_mid N2 d2 D1 d1;   // (N2·D1)·(d2·d1)
  rewrite *_com d2 d1;
  reflexivity
end;

// ᵣ≐ decides equality of rationals, in the non-degenerate case.
opaque symbol ᵣ≐_decides_nz n1 d1 n2 d2 :
  π (d1 ≠ 0) → π (d2 ≠ 0) →
  π ((frac n1 d1 ᵣ≐ frac n2 d2) = Eq) → π (frac n1 d1 = frac n2 d2) ≔
begin
  assume n1 d1 n2 d2 hd1 hd2 h;
  have hD1 : π (sign d1 * Z_red_Stein d1 n1 ≠ 0)
    { refine mul_ne_0 (sign d1) (Z_red_Stein d1 n1)
        (sign_ne_0 d1 hd1) (Z_red_Stein_l_ne_0 d1 n1 hd1) };
  have hD2 : π (sign d2 * Z_red_Stein d2 n2 ≠ 0)
    { refine mul_ne_0 (sign d2) (Z_red_Stein d2 n2)
        (sign_ne_0 d2 hd2) (Z_red_Stein_l_ne_0 d2 n2 hd2) };
  // `frac` reduces to the normalized pair, so `h` *is* the ℤ comparison.
  have hc : π ((sign d1 * Z_red_Stein n1 d1) * (sign d2 * Z_red_Stein d2 n2)
              = (sign d2 * Z_red_Stein n2 d2) * (sign d1 * Z_red_Stein d1 n1))
    { refine ≐_decides _ _ h };
  refine frac_eq n1 d1 n2 d2 hd1 hd2 _;
  refine cross_denorm n1 d1 n2 d2
    (sign d1 * Z_red_Stein n1 d1) (sign d1 * Z_red_Stein d1 n1)
    (sign d2 * Z_red_Stein n2 d2) (sign d2 * Z_red_Stein d2 n2)
    hD1 hD2 (frac_red_cross d1 n1) (frac_red_cross d2 n2) hc
end;

// ᵣ≐ decides equality on all of ℚ. The degenerate denominators are handled by
// `frac_0_den` (frac n 0 = 0/1 = frac 0 1), which reinstates a nonzero one.
opaque symbol ᵣ≐_decides x y : π ((x ᵣ≐ y) = Eq) → π (x = y) ≔
begin
  refine ind_Rat (λ u, `∀ v, ((u ᵣ≐ v) = Eq) ⇒ u = v) _;
  assume n1;
  induction
  // d1 = Z0: frac n1 0 collapses to 0/1, whose denominator is nonzero.
  { rewrite (frac_0_den n1);
    refine ind_Rat (λ v, ((0 / 1 ᵣ≐ v) = Eq) ⇒ 0 / 1 = v) _;
    assume n2;
    induction
    { rewrite (frac_0_den n2); assume h; reflexivity }
    { assume p2; refine ᵣ≐_decides_nz 0 1 n2 (Zpos p2) (Zpos≠Z0 H) (Zpos≠Z0 p2) }
    { assume p2; refine ᵣ≐_decides_nz 0 1 n2 (Zneg p2) (Zpos≠Z0 H) (Zneg≠Z0 p2) } }
  // d1 = Zpos p1
  { assume p1;
    refine ind_Rat (λ v, ((frac n1 (Zpos p1) ᵣ≐ v) = Eq) ⇒ frac n1 (Zpos p1) = v) _;
    assume n2;
    induction
    { rewrite (frac_0_den n2);
      refine ᵣ≐_decides_nz n1 (Zpos p1) 0 1 (Zpos≠Z0 p1) (Zpos≠Z0 H) }
    { assume p2;
      refine ᵣ≐_decides_nz n1 (Zpos p1) n2 (Zpos p2) (Zpos≠Z0 p1) (Zpos≠Z0 p2) }
    { assume p2;
      refine ᵣ≐_decides_nz n1 (Zpos p1) n2 (Zneg p2) (Zpos≠Z0 p1) (Zneg≠Z0 p2) } }
  // d1 = Zneg p1
  { assume p1;
    refine ind_Rat (λ v, ((frac n1 (Zneg p1) ᵣ≐ v) = Eq) ⇒ frac n1 (Zneg p1) = v) _;
    assume n2;
    induction
    { rewrite (frac_0_den n2);
      refine ᵣ≐_decides_nz n1 (Zneg p1) 0 1 (Zneg≠Z0 p1) (Zpos≠Z0 H) }
    { assume p2;
      refine ᵣ≐_decides_nz n1 (Zneg p1) n2 (Zpos p2) (Zneg≠Z0 p1) (Zpos≠Z0 p2) }
    { assume p2;
      refine ᵣ≐_decides_nz n1 (Zneg p1) n2 (Zneg p2) (Zneg≠Z0 p1) (Zneg≠Z0 p2) } }
end;

// Antisymmetry: x ᵣ≤ y and y ᵣ≤ x force x = y.
opaque symbol ᵣ≤_antisym x y : π (x ᵣ≤ y) → π (y ᵣ≤ x) → π (x = y) ≔
begin
  assume x y hxy hyx;
  refine ᵣ≐_decides x y _;
  have e : π (¬ (istrue (isGt (x ᵣ≐ y))) ⇒ ¬ (istrue (isGt (opp (x ᵣ≐ y))))
              ⇒ (x ᵣ≐ y) = Eq)
    { refine ind_Comp (λ c, ((x ᵣ≐ y) = c) ⇒ ¬ (istrue (isGt c))
                              ⇒ ¬ (istrue (isGt (opp c))) ⇒ (x ᵣ≐ y) = Eq)
        _ _ _ (x ᵣ≐ y) _
      { refine λ hEq _ _, hEq }
      { refine λ _ _ h, ⊥ₑ (h ⊤ᵢ) }
      { refine λ _ h _, ⊥ₑ (h ⊤ᵢ) }
      { reflexivity } };
  refine e hxy _;
  rewrite left ᵣ≐_com y x;
  refine hyx
end;


// ============================================================
// Inequalities on ℚ — directional comparison operators.
// ============================================================
// Mirrors Z.lp's pattern: defined via the three-way comparison
// `ᵣ≐` and the `Comp` predicates `isLt`, `isGt`.
//
// For raw fractions n1/d1, n2/d2 (with the normalization rules
// above forcing denominators to be positive), the definitions
// reduce to the standard cross-product convention (cf. Coq's
// `Qle`/`Qlt` in `Stdlib.QArith.QArith_base`):
//
//   (n1 / d1) ᵣ≤ (n2 / d2)  ≡  (n1 * d2) ≤ (n2 * d1)
//   (n1 / d1) ᵣ< (n2 / d2)  ≡  (n1 * d2) < (n2 * d1)
//   x ᵣ≥ y                  ≡  ¬ (x ᵣ< y)
//   x ᵣ> y                  ≡  ¬ (x ᵣ≤ y)


// --- Reflexivity / irreflexivity ---

opaque symbol ᵣ<_no_refl x : π (¬ (x ᵣ< x)) ≔
begin
  refine ind_Rat (λ u, ¬ (u ᵣ< u)) _;
  assume n d;
  refine <_no_refl ((sign d * Z_red_Stein n d) * (sign d * Z_red_Stein d n))
end;

opaque symbol ᵣ≥_refl x : π (x ᵣ≥ x) ≔
begin
  assume x;
  refine ᵣ<_no_refl x
end;

opaque symbol ᵣ>_no_refl x : π (¬ (x ᵣ> x)) ≔
begin
  assume x h;
  refine h (ᵣ≤_refl x)
end;

// --- Order relations: < implies ≤, ≥ ⇒ ¬<, > ⇒ ¬≤, < ⇒ ¬≤ (other direction) ---

opaque symbol ᵣ<_≤ x y : π (x ᵣ< y ⇒ x ᵣ≤ y) ≔
begin
  refine ind_Rat (λ u, `∀ v, u ᵣ< v ⇒ u ᵣ≤ v) _;
  assume n1 d1;
  refine ind_Rat (λ v, ((frac n1 d1) ᵣ< v) ⇒ ((frac n1 d1) ᵣ≤ v)) _;
  assume n2 d2;
  refine <_≤ ((sign d1 * Z_red_Stein n1 d1) * (sign d2 * Z_red_Stein d2 n2))
              ((sign d2 * Z_red_Stein n2 d2) * (sign d1 * Z_red_Stein d1 n1))
end;

opaque symbol ᵣ≥_¬_< x y : π (x ᵣ≥ y ⇒ ¬ (x ᵣ< y)) ≔
begin
  assume x y h; refine h
end;

opaque symbol ᵣ>_¬_≤ x y : π (x ᵣ> y ⇒ ¬ (x ᵣ≤ y)) ≔
begin
  assume x y h; refine h
end;

// `x ᵣ< y` rules out `y ᵣ≤ x` (strict precludes weak in the other direction).
opaque symbol ᵣ<_neg_≤ x y : π (x ᵣ< y ⇒ ¬ (y ᵣ≤ x)) ≔
begin
  refine ind_Rat (λ u, `∀ v, u ᵣ< v ⇒ ¬ (v ᵣ≤ u)) _;
  assume n1 d1;
  refine ind_Rat (λ v, ((frac n1 d1) ᵣ< v) ⇒ ¬ (v ᵣ≤ (frac n1 d1))) _;
  assume n2 d2;
  refine <_neg_≤ ((sign d1 * Z_red_Stein n1 d1) * (sign d2 * Z_red_Stein d2 n2))
                  ((sign d2 * Z_red_Stein n2 d2) * (sign d1 * Z_red_Stein d1 n1))
end;

// --- Antisymmetry at the cross-product level ---
// Two raw /-fractions that are mutually ≤ have equal cross-products.

opaque symbol ᵣ≤_antisym_cross n1 d1 n2 d2 :
    π ((n1 / d1) ᵣ≤ (n2 / d2) ⇒ (n2 / d2) ᵣ≤ (n1 / d1) ⇒ (n1 * d2) = (n2 * d1)) ≔
begin
  assume n1 d1 n2 d2;
  refine ≤_antisym (n1 * d2) (n2 * d1)
end;

// Equality implies ≤ and ≥ (cf. Coq's `Qle_refl` used via Leibniz).
opaque symbol ᵣ≤_eq_incl x y : π (x = y ⇒ x ᵣ≤ y) ≔
begin
  assume x y heq;
  rewrite heq;
  refine ᵣ≤_refl y
end;

opaque symbol ᵣ≥_eq_incl x y : π (x = y ⇒ x ᵣ≥ y) ≔
begin
  assume x y heq;
  rewrite heq;
  refine ᵣ≥_refl y
end;

// Swap the first two factors in a right-associated triple product.
// Generic ℤ-level helper used both in the inequality theory below and
// in the ᵣdistr*+ algebra further down.
opaque symbol *_swap_l a b c : π (a * (b * c) = b * (a * c)) ≔
begin
  assume a b c;
  rewrite left *_assoc a b c;
  rewrite *_com a b;
  rewrite *_assoc b a c;
  reflexivity
end;

// --- ℤ-level helper: ≤ version of `mul_lt_mono_pos_l` ---
// Multiplying by a positive integer preserves (and reflects) ≤.
// Derived from Z.lp's `mul_lt_mono_pos_l` via the `≤_≥` duality:
// `n ≤ m ⇔ ¬ (m < n)`, then push through the strict bicond.
opaque symbol mul_le_mono_pos_l p : π (Z0 < p) → Π n m, π (n ≤ m ⇔ n * p ≤ m * p) ≔
begin
  assume p Hp n m;
  apply ∧ᵢ
  { assume Hnm;
    refine ∧ₑ₁ (≤_≥ (m * p) (n * p)) _;
    assume Hltmp;
    have Hltmn : π (m < n) { refine ∧ₑ₂ (mul_lt_mono_pos_l p Hp m n) Hltmp };
    refine ∧ₑ₂ (≤_≥ m n) Hnm Hltmn }
  { assume Hnmp;
    refine ∧ₑ₁ (≤_≥ m n) _;
    assume Hltmn;
    have Hltmp : π (m * p < n * p) { refine ∧ₑ₁ (mul_lt_mono_pos_l p Hp m n) Hltmn };
    refine ∧ₑ₂ (≤_≥ (m * p) (n * p)) Hnmp Hltmp }
end;

// Right-multiplication by a positive preserves ≤ (one-directional shorthand).
opaque symbol mul_le_compat_r a b c : π (Z0 < c) → π (a ≤ b) → π (a * c ≤ b * c) ≔
begin
  assume a b c Hc Hab;
  refine ∧ₑ₁ (mul_le_mono_pos_l c Hc a b) Hab
end;

// Right-cancellation by a positive reflects ≤.
opaque symbol mul_le_cancel_r a b c : π (Z0 < c) → π (a * c ≤ b * c) → π (a ≤ b) ≔
begin
  assume a b c Hc Hac;
  refine ∧ₑ₂ (mul_le_mono_pos_l c Hc a b) Hac
end;

// --- Transitivity of ᵣ≤ on raw /-fractions (positive denominators) ---
// Mirrors Coq's `Qle_trans` (which assumes `QDen > 0` in its data type).
// Strategy: multiply each hypothesis by the missing-side positive denominator,
// chain via Z.lp's `≤_trans`, then cancel the common middle denominator.
opaque symbol ᵣ≤_trans_div n1 d1 n2 d2 n3 d3 :
    π (Z0 < d1) → π (Z0 < d2) → π (Z0 < d3) →
    π ((n1 / d1) ᵣ≤ (n2 / d2) ⇒ (n2 / d2) ᵣ≤ (n3 / d3) ⇒ (n1 / d1) ᵣ≤ (n3 / d3)) ≔
begin
  assume n1 d1 n2 d2 n3 d3 Hd1 Hd2 Hd3 H12 H23;
  // H12 : (n1 * d2) ≤ (n2 * d1)
  // H23 : (n2 * d3) ≤ (n3 * d2)
  // Goal: (n1 * d3) ≤ (n3 * d1)
  refine mul_le_cancel_r (n1 * d3) (n3 * d1) d2 Hd2 _;
  // Goal: (n1 * d3) * d2 ≤ (n3 * d1) * d2
  have H12' : π ((n1 * d2) * d3 ≤ (n2 * d1) * d3)
    { refine mul_le_compat_r (n1 * d2) (n2 * d1) d3 Hd3 H12 };
  have H23' : π ((n2 * d3) * d1 ≤ (n3 * d2) * d1)
    { refine mul_le_compat_r (n2 * d3) (n3 * d2) d1 Hd1 H23 };
  // Reshape H12': (n1*d2)*d3 = (n1*d3)*d2 and (n2*d1)*d3 = (n2*d3)*d1.
  have R1 : π ((n1 * d2) * d3 = (n1 * d3) * d2)
    { rewrite *_assoc n1 d2 d3; rewrite *_com d2 d3;
      rewrite left *_assoc n1 d3 d2; reflexivity };
  have R2 : π ((n2 * d1) * d3 = (n2 * d3) * d1)
    { rewrite *_assoc n2 d1 d3; rewrite *_com d1 d3;
      rewrite left *_assoc n2 d3 d1; reflexivity };
  have R3 : π ((n3 * d2) * d1 = (n3 * d1) * d2)
    { rewrite *_assoc n3 d2 d1; rewrite *_com d2 d1;
      rewrite left *_assoc n3 d1 d2; reflexivity };
  have H12'' : π ((n1 * d3) * d2 ≤ (n2 * d3) * d1)
    { rewrite left R1; rewrite left R2; refine H12' };
  have H23'' : π ((n2 * d3) * d1 ≤ (n3 * d1) * d2)
    { rewrite left R3; refine H23' };
  refine ≤_trans ((n1 * d3) * d2) ((n2 * d3) * d1) ((n3 * d1) * d2) H12'' H23''
end;

// Left-multiplication variants — useful when the multiplier is on the left.

opaque symbol mul_le_compat_l a b c : π (Z0 < c) → π (a ≤ b) → π (c * a ≤ c * b) ≔
begin
  assume a b c Hc Hab;
  rewrite *_com c a;
  rewrite *_com c b;
  refine mul_le_compat_r a b c Hc Hab
end;

opaque symbol mul_le_cancel_l a b c : π (Z0 < c) → π (c * a ≤ c * b) → π (a ≤ b) ≔
begin
  assume a b c Hc Hac;
  refine mul_le_cancel_r a b c Hc _;
  rewrite *_com a c;
  rewrite *_com b c;
  refine Hac
end;

// --- ℤ-level strict-order helpers (analogous to the ≤ ones above) ---

opaque symbol mul_lt_compat_r a b c : π (Z0 < c) → π (a < b) → π (a * c < b * c) ≔
begin
  assume a b c Hc Hab;
  refine ∧ₑ₁ (mul_lt_mono_pos_l c Hc a b) Hab
end;

opaque symbol mul_lt_cancel_r a b c : π (Z0 < c) → π (a * c < b * c) → π (a < b) ≔
begin
  assume a b c Hc Hac;
  refine ∧ₑ₂ (mul_lt_mono_pos_l c Hc a b) Hac
end;

opaque symbol mul_lt_compat_l a b c : π (Z0 < c) → π (a < b) → π (c * a < c * b) ≔
begin
  assume a b c Hc Hab;
  rewrite *_com c a;
  rewrite *_com c b;
  refine mul_lt_compat_r a b c Hc Hab
end;

opaque symbol mul_lt_cancel_l a b c : π (Z0 < c) → π (c * a < c * b) → π (a < b) ≔
begin
  assume a b c Hc Hac;
  refine mul_lt_cancel_r a b c Hc _;
  rewrite *_com a c;
  rewrite *_com b c;
  refine Hac
end;

// Z.lp has `<_trans_1` (< then ≤) and `<_trans_2` (≤ then <) but no plain `<_trans`.
// Derive: a < b ⇒ b < c ⇒ a < c via `<_to_≤` + `<_trans_2`.
opaque symbol <_trans a b c : π (a < b) → π (b < c) → π (a < c) ≔
begin
  assume a b c Hab Hbc;
  refine <_trans_2 a b c (<_to_≤ a b Hab) Hbc
end;

// --- Strict transitivity of ᵣ< on raw /-fractions (positive denominators) ---
opaque symbol ᵣ<_trans_div n1 d1 n2 d2 n3 d3 :
    π (Z0 < d1) → π (Z0 < d2) → π (Z0 < d3) →
    π ((n1 / d1) ᵣ< (n2 / d2) ⇒ (n2 / d2) ᵣ< (n3 / d3) ⇒ (n1 / d1) ᵣ< (n3 / d3)) ≔
begin
  assume n1 d1 n2 d2 n3 d3 Hd1 Hd2 Hd3 H12 H23;
  refine mul_lt_cancel_r (n1 * d3) (n3 * d1) d2 Hd2 _;
  have H12' : π ((n1 * d2) * d3 < (n2 * d1) * d3)
    { refine mul_lt_compat_r (n1 * d2) (n2 * d1) d3 Hd3 H12 };
  have H23' : π ((n2 * d3) * d1 < (n3 * d2) * d1)
    { refine mul_lt_compat_r (n2 * d3) (n3 * d2) d1 Hd1 H23 };
  have R1 : π ((n1 * d2) * d3 = (n1 * d3) * d2)
    { rewrite *_assoc n1 d2 d3; rewrite *_com d2 d3;
      rewrite left *_assoc n1 d3 d2; reflexivity };
  have R2 : π ((n2 * d1) * d3 = (n2 * d3) * d1)
    { rewrite *_assoc n2 d1 d3; rewrite *_com d1 d3;
      rewrite left *_assoc n2 d3 d1; reflexivity };
  have R3 : π ((n3 * d2) * d1 = (n3 * d1) * d2)
    { rewrite *_assoc n3 d2 d1; rewrite *_com d2 d1;
      rewrite left *_assoc n3 d1 d2; reflexivity };
  have H12'' : π ((n1 * d3) * d2 < (n2 * d3) * d1)
    { rewrite left R1; rewrite left R2; refine H12' };
  have H23'' : π ((n2 * d3) * d1 < (n3 * d1) * d2)
    { rewrite left R3; refine H23' };
  refine <_trans ((n1 * d3) * d2) ((n2 * d3) * d1) ((n3 * d1) * d2) H12'' H23''
end;

// Mixed transitivity (cf. Coq's `Qle_lt_trans` / `Qlt_le_trans`).
opaque symbol ᵣ≤_<_trans_div n1 d1 n2 d2 n3 d3 :
    π (Z0 < d1) → π (Z0 < d2) → π (Z0 < d3) →
    π ((n1 / d1) ᵣ≤ (n2 / d2) ⇒ (n2 / d2) ᵣ< (n3 / d3) ⇒ (n1 / d1) ᵣ< (n3 / d3)) ≔
begin
  assume n1 d1 n2 d2 n3 d3 Hd1 Hd2 Hd3 H12 H23;
  refine mul_lt_cancel_r (n1 * d3) (n3 * d1) d2 Hd2 _;
  have H12' : π ((n1 * d2) * d3 ≤ (n2 * d1) * d3)
    { refine mul_le_compat_r (n1 * d2) (n2 * d1) d3 Hd3 H12 };
  have H23' : π ((n2 * d3) * d1 < (n3 * d2) * d1)
    { refine mul_lt_compat_r (n2 * d3) (n3 * d2) d1 Hd1 H23 };
  have R1 : π ((n1 * d2) * d3 = (n1 * d3) * d2)
    { rewrite *_assoc n1 d2 d3; rewrite *_com d2 d3;
      rewrite left *_assoc n1 d3 d2; reflexivity };
  have R2 : π ((n2 * d1) * d3 = (n2 * d3) * d1)
    { rewrite *_assoc n2 d1 d3; rewrite *_com d1 d3;
      rewrite left *_assoc n2 d3 d1; reflexivity };
  have R3 : π ((n3 * d2) * d1 = (n3 * d1) * d2)
    { rewrite *_assoc n3 d2 d1; rewrite *_com d2 d1;
      rewrite left *_assoc n3 d1 d2; reflexivity };
  have H12'' : π ((n1 * d3) * d2 ≤ (n2 * d3) * d1)
    { rewrite left R1; rewrite left R2; refine H12' };
  have H23'' : π ((n2 * d3) * d1 < (n3 * d1) * d2)
    { rewrite left R3; refine H23' };
  refine <_trans_2 ((n1 * d3) * d2) ((n2 * d3) * d1) ((n3 * d1) * d2) H12'' H23''
end;

opaque symbol ᵣ<_≤_trans_div n1 d1 n2 d2 n3 d3 :
    π (Z0 < d1) → π (Z0 < d2) → π (Z0 < d3) →
    π ((n1 / d1) ᵣ< (n2 / d2) ⇒ (n2 / d2) ᵣ≤ (n3 / d3) ⇒ (n1 / d1) ᵣ< (n3 / d3)) ≔
begin
  assume n1 d1 n2 d2 n3 d3 Hd1 Hd2 Hd3 H12 H23;
  refine mul_lt_cancel_r (n1 * d3) (n3 * d1) d2 Hd2 _;
  have H12' : π ((n1 * d2) * d3 < (n2 * d1) * d3)
    { refine mul_lt_compat_r (n1 * d2) (n2 * d1) d3 Hd3 H12 };
  have H23' : π ((n2 * d3) * d1 ≤ (n3 * d2) * d1)
    { refine mul_le_compat_r (n2 * d3) (n3 * d2) d1 Hd1 H23 };
  have R1 : π ((n1 * d2) * d3 = (n1 * d3) * d2)
    { rewrite *_assoc n1 d2 d3; rewrite *_com d2 d3;
      rewrite left *_assoc n1 d3 d2; reflexivity };
  have R2 : π ((n2 * d1) * d3 = (n2 * d3) * d1)
    { rewrite *_assoc n2 d1 d3; rewrite *_com d1 d3;
      rewrite left *_assoc n2 d3 d1; reflexivity };
  have R3 : π ((n3 * d2) * d1 = (n3 * d1) * d2)
    { rewrite *_assoc n3 d2 d1; rewrite *_com d2 d1;
      rewrite left *_assoc n3 d1 d2; reflexivity };
  have H12'' : π ((n1 * d3) * d2 < (n2 * d3) * d1)
    { rewrite left R1; rewrite left R2; refine H12' };
  have H23'' : π ((n2 * d3) * d1 ≤ (n3 * d1) * d2)
    { rewrite left R3; refine H23' };
  refine <_trans_1 ((n1 * d3) * d2) ((n2 * d3) * d1) ((n3 * d1) * d2) H12'' H23''
end;

// --- Positivity of the normalized denominator (d > 0 ⇒ D > 0) ---
// For `d : ℤ` with `d > 0` (so `d = Zpos p`), the normalized denominator
// `sign d * Z_red_Stein d n` reduces to a `Zpos _` value, hence is > 0.
opaque symbol sign_Z_red_Stein_pos d n :
    π (Z0 < d) → π (Z0 < sign d * Z_red_Stein d n) ≔
begin
  induction
  { assume n h; apply ⊥ₑ; refine h }
  { assume p; induction
    { assume h; refine ⊤ᵢ }
    { assume a h; refine ⊤ᵢ }
    { assume a h; refine ⊤ᵢ } }
  { assume p n h; apply ⊥ₑ; refine h }
end;

// --- A small ℤ-level abstraction: ≤ commutes with multiplying by positives ---
// If `a * k1 = c * k2` and `b * k1 = d * k2` for positive `k1, k2`, then
// `a ≤ b ⇔ c ≤ d`. Reduces a ≤-on-fractions bicond to two cross-product
// equalities + positivity, which is exactly the shape needed for ᵣ≤_frac_iff_cross.
opaque symbol mul_le_iff_via_pos a b c d k1 k2 :
    π (Z0 < k1) → π (Z0 < k2) →
    π (a * k1 = c * k2) → π (b * k1 = d * k2) →
    π (a ≤ b ⇔ c ≤ d) ≔
begin
  assume a b c d k1 k2 Hk1 Hk2 E1 E2;
  apply ∧ᵢ
  { assume Hab;
    refine mul_le_cancel_r c d k2 Hk2 _;
    rewrite left E1; rewrite left E2;
    refine mul_le_compat_r a b k1 Hk1 Hab }
  { assume Hcd;
    refine mul_le_cancel_r a b k1 Hk1 _;
    rewrite E1; rewrite E2;
    refine mul_le_compat_r c d k2 Hk2 Hcd }
end;

// --- Cross-product characterization of ᵣ≤ on `frac n d` ---
// For positive denominators, comparison of `frac n1 d1` and `frac n2 d2`
// in ℚ is equivalent to the natural integer cross-product. The normalized
// numerator/denominator (N_i, D_i) collapse via two applications of
// `frac_red_cross` plus a cancellation by `D1 * D2`.
opaque symbol ᵣ≤_frac_iff_cross n1 d1 n2 d2 :
    π (Z0 < d1) → π (Z0 < d2) →
    π (frac n1 d1 ᵣ≤ frac n2 d2 ⇔ n1 * d2 ≤ n2 * d1) ≔
begin
  assume n1 d1 n2 d2 Hd1 Hd2;
  set N1 ≔ sign d1 * Z_red_Stein n1 d1;
  set D1 ≔ sign d1 * Z_red_Stein d1 n1;
  set N2 ≔ sign d2 * Z_red_Stein n2 d2;
  set D2 ≔ sign d2 * Z_red_Stein d2 n2;
  have R1 : π (N1 * d1 = n1 * D1) { refine frac_red_cross d1 n1 };
  have R2 : π (N2 * d2 = n2 * D2) { refine frac_red_cross d2 n2 };
  have HD1 : π (Z0 < D1) { refine sign_Z_red_Stein_pos d1 n1 Hd1 };
  have HD2 : π (Z0 < D2) { refine sign_Z_red_Stein_pos d2 n2 Hd2 };
  have Hd1d2 : π (Z0 < d1 * d2)
    { refine ∧ₑ₂ (<_> Z0 (d1 * d2)) _;
      refine *_pos_pos d1 d2 (∧ₑ₁ (<_> Z0 d1) Hd1) (∧ₑ₁ (<_> Z0 d2) Hd2) };
  have HD1D2 : π (Z0 < D1 * D2)
    { refine ∧ₑ₂ (<_> Z0 (D1 * D2)) _;
      refine *_pos_pos D1 D2 (∧ₑ₁ (<_> Z0 D1) HD1) (∧ₑ₁ (<_> Z0 D2) HD2) };
  // E1: (N1*D2)*(d1*d2) = (n1*d2)*(D1*D2)  — by reshaping + R1
  have E1 : π ((N1 * D2) * (d1 * d2) = (n1 * d2) * (D1 * D2))
    { rewrite *_assoc N1 D2 (d1 * d2);
      rewrite *_swap_l D2 d1 d2;
      rewrite left *_assoc N1 d1 (D2 * d2);
      rewrite R1;
      rewrite *_assoc n1 D1 (D2 * d2);
      rewrite left *_assoc D1 D2 d2;
      rewrite *_com (D1 * D2) d2;
      rewrite left *_assoc n1 d2 (D1 * D2);
      reflexivity };
  // E2: (N2*D1)*(d1*d2) = (n2*d1)*(D1*D2)  — by reshaping + R2
  have E2 : π ((N2 * D1) * (d1 * d2) = (n2 * d1) * (D1 * D2))
    { rewrite *_assoc N2 D1 (d1 * d2);
      rewrite left *_assoc D1 d1 d2;
      rewrite *_com (D1 * d1) d2;
      rewrite left *_assoc N2 d2 (D1 * d1);
      rewrite R2;
      rewrite *_assoc n2 D2 (D1 * d1);
      rewrite left *_assoc D2 D1 d1;
      rewrite *_com (D2 * D1) d1;
      rewrite left *_assoc n2 d1 (D2 * D1);
      rewrite *_com D2 D1;
      reflexivity };
  refine mul_le_iff_via_pos (N1 * D2) (N2 * D1) (n1 * d2) (n2 * d1) (d1 * d2) (D1 * D2)
                              Hd1d2 HD1D2 E1 E2
end;

// --- Compat lemmas for ᵣ+ (positive denominators) ---
// `frac n1 d1 ᵣ≤ frac n2 d2` and adding the same `frac n3 d3` preserves ≤.
// The proof goes through `ᵣ≤_frac_iff_cross` to reduce the (post-ᵣ+) ᵣ≤ to
// the integer cross-product inequality
//   `(n1*d3 + n3*d1)*(d2*d3) ≤ (n2*d3 + n3*d2)*(d1*d3)`
// which after distributing both sides has matching "n3 cross terms" (equal
// by commutativity) and a difference proportional to `(n1*d2 − n2*d1)*d3²`.
// Apply `≤_compat_add` to peel off the common term, then `mul_le_compat_r`
// with the hypothesis `n1*d2 ≤ n2*d1` and `d3*d3 > 0`.
opaque symbol ᵣ+_le_compat_div_r n1 d1 n2 d2 n3 d3 :
    π (Z0 < d1) → π (Z0 < d2) → π (Z0 < d3) →
    π ((n1 / d1) ᵣ≤ (n2 / d2)
       ⇒ ((n1 / d1) ᵣ+ (n3 / d3)) ᵣ≤ ((n2 / d2) ᵣ+ (n3 / d3))) ≔
begin
  assume n1 d1 n2 d2 n3 d3 Hd1 Hd2 Hd3 H12;
  // H12 unfolds (definitionally) to `(n1 * d2) ≤ (n2 * d1)`.
  have Hd1d3 : π (Z0 < d1 * d3)
    { refine ∧ₑ₂ (<_> Z0 (d1 * d3)) _;
      refine *_pos_pos d1 d3 (∧ₑ₁ (<_> Z0 d1) Hd1) (∧ₑ₁ (<_> Z0 d3) Hd3) };
  have Hd2d3 : π (Z0 < d2 * d3)
    { refine ∧ₑ₂ (<_> Z0 (d2 * d3)) _;
      refine *_pos_pos d2 d3 (∧ₑ₁ (<_> Z0 d2) Hd2) (∧ₑ₁ (<_> Z0 d3) Hd3) };
  have Hd3d3 : π (Z0 < d3 * d3)
    { refine ∧ₑ₂ (<_> Z0 (d3 * d3)) _;
      refine *_pos_pos d3 d3 (∧ₑ₁ (<_> Z0 d3) Hd3) (∧ₑ₁ (<_> Z0 d3) Hd3) };
  refine ∧ₑ₂ (ᵣ≤_frac_iff_cross
                ((n1 * d3) + (n3 * d1)) (d1 * d3)
                ((n2 * d3) + (n3 * d2)) (d2 * d3) Hd1d3 Hd2d3) _;
  // Goal: ((n1*d3 + n3*d1) * (d2*d3)) ≤ ((n2*d3 + n3*d2) * (d1*d3))
  // Distribute LHS:
  rewrite *_com ((n1 * d3) + (n3 * d1)) (d2 * d3);
  rewrite *_distr_+ (d2 * d3) (n1 * d3) (n3 * d1);
  // Distribute RHS:
  rewrite *_com ((n2 * d3) + (n3 * d2)) (d1 * d3);
  rewrite *_distr_+ (d1 * d3) (n2 * d3) (n3 * d2);
  // Goal: (d2*d3)*(n1*d3) + (d2*d3)*(n3*d1) ≤ (d1*d3)*(n2*d3) + (d1*d3)*(n3*d2)
  // Show the two "right summands" are equal (commutativity of factors):
  have Beq : π ((d2 * d3) * (n3 * d1) = (d1 * d3) * (n3 * d2))
    { rewrite *_assoc d2 d3 (n3 * d1);
      rewrite *_swap_l d3 n3 d1;
      rewrite *_swap_l d2 n3 (d3 * d1);
      rewrite *_swap_l d2 d3 d1;
      rewrite *_com d2 d1;
      rewrite *_assoc d1 d3 (n3 * d2);
      rewrite *_swap_l d3 n3 d2;
      rewrite *_swap_l d1 n3 (d3 * d2);
      rewrite *_swap_l d1 d3 d2;
      reflexivity };
  rewrite Beq;
  // Goal: (d2*d3)*(n1*d3) + (d1*d3)*(n3*d2) ≤ (d1*d3)*(n2*d3) + (d1*d3)*(n3*d2)
  refine ≤_compat_add ((d2 * d3) * (n1 * d3)) ((d1 * d3) * (n2 * d3))
                       ((d1 * d3) * (n3 * d2)) _;
  // Goal: (d2*d3)*(n1*d3) ≤ (d1*d3)*(n2*d3)
  // Reshape both sides to expose (n1*d2)*(d3*d3) and (n2*d1)*(d3*d3):
  have Aeq : π ((d2 * d3) * (n1 * d3) = (n1 * d2) * (d3 * d3))
    { rewrite *_assoc d2 d3 (n1 * d3);
      rewrite *_swap_l d3 n1 d3;
      rewrite *_swap_l d2 n1 (d3 * d3);
      rewrite left *_assoc n1 d2 (d3 * d3);
      reflexivity };
  have Ceq : π ((d1 * d3) * (n2 * d3) = (n2 * d1) * (d3 * d3))
    { rewrite *_assoc d1 d3 (n2 * d3);
      rewrite *_swap_l d3 n2 d3;
      rewrite *_swap_l d1 n2 (d3 * d3);
      rewrite left *_assoc n2 d1 (d3 * d3);
      reflexivity };
  rewrite Aeq;
  rewrite Ceq;
  refine mul_le_compat_r (n1 * d2) (n2 * d1) (d3 * d3) Hd3d3 H12
end;

// Left variant — derived from the right variant via ᵣ+_com_div.
opaque symbol ᵣ+_le_compat_div_l n1 d1 n2 d2 n3 d3 :
    π (Z0 < d1) → π (Z0 < d2) → π (Z0 < d3) →
    π ((n1 / d1) ᵣ≤ (n2 / d2)
       ⇒ ((n3 / d3) ᵣ+ (n1 / d1)) ᵣ≤ ((n3 / d3) ᵣ+ (n2 / d2))) ≔
begin
  assume n1 d1 n2 d2 n3 d3 Hd1 Hd2 Hd3 H12;
  rewrite (ᵣ+_com_div n3 d3 n1 d1);
  rewrite (ᵣ+_com_div n3 d3 n2 d2);
  refine ᵣ+_le_compat_div_r n1 d1 n2 d2 n3 d3 Hd1 Hd2 Hd3 H12
end;

// --- Compat lemma for *ᵣ (positive multiplier, positive denominators) ---
// `frac n1 d1 ᵣ≤ frac n2 d2 → 0 < n3 → frac n1 d1 *ᵣ frac n3 d3 ᵣ≤ frac n2 d2 *ᵣ frac n3 d3`
// After *ᵣ rule fires, cross-product (n1*n3)*(d2*d3) ≤ (n2*n3)*(d1*d3) reshapes
// (commute n3 with d2, d1) to (n1*d2)*(n3*d3) ≤ (n2*d1)*(n3*d3); close with
// `mul_le_compat_r` on `H12 : n1*d2 ≤ n2*d1` and `n3*d3 > 0`.
opaque symbol ᵣ*_le_compat_pos_div_r n1 d1 n2 d2 n3 d3 :
    π (Z0 < d1) → π (Z0 < d2) → π (Z0 < d3) → π (Z0 < n3) →
    π ((n1 / d1) ᵣ≤ (n2 / d2)
       ⇒ ((n1 / d1) *ᵣ (n3 / d3)) ᵣ≤ ((n2 / d2) *ᵣ (n3 / d3))) ≔
begin
  assume n1 d1 n2 d2 n3 d3 Hd1 Hd2 Hd3 Hn3 H12;
  have Hd1d3 : π (Z0 < d1 * d3)
    { refine ∧ₑ₂ (<_> Z0 (d1 * d3)) _;
      refine *_pos_pos d1 d3 (∧ₑ₁ (<_> Z0 d1) Hd1) (∧ₑ₁ (<_> Z0 d3) Hd3) };
  have Hd2d3 : π (Z0 < d2 * d3)
    { refine ∧ₑ₂ (<_> Z0 (d2 * d3)) _;
      refine *_pos_pos d2 d3 (∧ₑ₁ (<_> Z0 d2) Hd2) (∧ₑ₁ (<_> Z0 d3) Hd3) };
  have Hn3d3 : π (Z0 < n3 * d3)
    { refine ∧ₑ₂ (<_> Z0 (n3 * d3)) _;
      refine *_pos_pos n3 d3 (∧ₑ₁ (<_> Z0 n3) Hn3) (∧ₑ₁ (<_> Z0 d3) Hd3) };
  refine ∧ₑ₂ (ᵣ≤_frac_iff_cross (n1 * n3) (d1 * d3) (n2 * n3) (d2 * d3)
                                  Hd1d3 Hd2d3) _;
  // Goal: (n1*n3) * (d2*d3) ≤ (n2*n3) * (d1*d3)
  have Aeq : π ((n1 * n3) * (d2 * d3) = (n1 * d2) * (n3 * d3))
    { rewrite *_assoc n1 n3 (d2 * d3);
      rewrite *_swap_l n3 d2 d3;
      rewrite left *_assoc n1 d2 (n3 * d3);
      reflexivity };
  have Ceq : π ((n2 * n3) * (d1 * d3) = (n2 * d1) * (n3 * d3))
    { rewrite *_assoc n2 n3 (d1 * d3);
      rewrite *_swap_l n3 d1 d3;
      rewrite left *_assoc n2 d1 (n3 * d3);
      reflexivity };
  rewrite Aeq;
  rewrite Ceq;
  refine mul_le_compat_r (n1 * d2) (n2 * d1) (n3 * d3) Hn3d3 H12
end;

// Left variant for *ᵣ — derived from the right variant via *ᵣ_com_div.
opaque symbol ᵣ*_le_compat_pos_div_l n1 d1 n2 d2 n3 d3 :
    π (Z0 < d1) → π (Z0 < d2) → π (Z0 < d3) → π (Z0 < n3) →
    π ((n1 / d1) ᵣ≤ (n2 / d2)
       ⇒ ((n3 / d3) *ᵣ (n1 / d1)) ᵣ≤ ((n3 / d3) *ᵣ (n2 / d2))) ≔
begin
  assume n1 d1 n2 d2 n3 d3 Hd1 Hd2 Hd3 Hn3 H12;
  rewrite (*ᵣ_com_div n3 d3 n1 d1);
  rewrite (*ᵣ_com_div n3 d3 n2 d2);
  refine ᵣ*_le_compat_pos_div_r n1 d1 n2 d2 n3 d3 Hd1 Hd2 Hd3 Hn3 H12
end;

opaque symbol zero_mul_l x : π ((0 / 1) *ᵣ x = (0 / 1)) ≔
begin
  refine ind_Rat (λ u, ((0 / 1) *ᵣ u) = (0 / 1)) _;
  assume n d;
  simplify *ᵣ;
  rewrite *_cancel_l;
  refine frac_0_num (1 * (sign d * Z_red_Stein d n))
end;

opaque symbol zero_mul_r x : π (x *ᵣ (0 / 1) = (0 / 1)) ≔
begin
  assume x;
  rewrite (ᵣ*_com x (0 / 1));
  refine zero_mul_l x
end;

opaque symbol ᵣdistr*+_div_nz n1 d1 n2 d2 n3 d3
    (hd1 : π (d1 ≠ 0)) (hd2 : π (d2 ≠ 0)) (hd3 : π (d3 ≠ 0)) :
    π (n1/d1 *ᵣ (n2/d2 ᵣ+ n3/d3) = (n1/d1 *ᵣ n2/d2) ᵣ+ (n1/d1 *ᵣ n3/d3)) ≔
begin
  assume n1 d1 n2 d2 n3 d3 hd1 hd2 hd3;
  simplify *ᵣ; simplify ᵣ+;
  have hd2d3 : π (d2 * d3 ≠ 0) { refine mul_ne_0 d2 d3 hd2 hd3 };
  have hd1d2 : π (d1 * d2 ≠ 0) { refine mul_ne_0 d1 d2 hd1 hd2 };
  have hd1d3 : π (d1 * d3 ≠ 0) { refine mul_ne_0 d1 d3 hd1 hd3 };
  have hQ : π (sign (d2 * d3) * Z_red_Stein (d2 * d3) ((n2 * d3) + (n3 * d2)) ≠ 0)
    { refine mul_ne_0 (sign (d2 * d3)) (Z_red_Stein (d2 * d3) ((n2 * d3) + (n3 * d2)))
        (sign_ne_0 (d2 * d3) hd2d3)
        (Z_red_Stein_l_ne_0 (d2 * d3) ((n2 * d3) + (n3 * d2)) hd2d3) };
  have hS : π (sign (d1 * d2) * Z_red_Stein (d1 * d2) (n1 * n2) ≠ 0)
    { refine mul_ne_0 (sign (d1 * d2)) (Z_red_Stein (d1 * d2) (n1 * n2))
        (sign_ne_0 (d1 * d2) hd1d2)
        (Z_red_Stein_l_ne_0 (d1 * d2) (n1 * n2) hd1d2) };
  have hU : π (sign (d1 * d3) * Z_red_Stein (d1 * d3) (n1 * n3) ≠ 0)
    { refine mul_ne_0 (sign (d1 * d3)) (Z_red_Stein (d1 * d3) (n1 * n3))
        (sign_ne_0 (d1 * d3) hd1d3)
        (Z_red_Stein_l_ne_0 (d1 * d3) (n1 * n3) hd1d3) };
  refine frac_eq _ _ _ _ (mul_ne_0 _ _ hd1 hQ) (mul_ne_0 _ _ hS hU) _;
  // Cross-product goal: (n1 * P) * (S * U) = ((R * U) + (T * S)) * (d1 * Q)
  set P ≔ sign (d2 * d3) * Z_red_Stein ((n2 * d3) + (n3 * d2)) (d2 * d3);
  set Q ≔ sign (d2 * d3) * Z_red_Stein (d2 * d3) ((n2 * d3) + (n3 * d2));
  set R ≔ sign (d1 * d2) * Z_red_Stein (n1 * n2) (d1 * d2);
  set S ≔ sign (d1 * d2) * Z_red_Stein (d1 * d2) (n1 * n2);
  set T ≔ sign (d1 * d3) * Z_red_Stein (n1 * n3) (d1 * d3);
  set U ≔ sign (d1 * d3) * Z_red_Stein (d1 * d3) (n1 * n3);
  have R1 : π (P * (d2 * d3) = ((n2 * d3) + (n3 * d2)) * Q)
    { refine frac_red_cross (d2 * d3) ((n2 * d3) + (n3 * d2)) };
  have R2 : π (R * (d1 * d2) = (n1 * n2) * S)
    { refine frac_red_cross (d1 * d2) (n1 * n2) };
  have R3 : π (T * (d1 * d3) = (n1 * n3) * U)
    { refine frac_red_cross (d1 * d3) (n1 * n3) };
  refine *_reg_r _ _ (d2 * d3) hd2d3 _;
  // Goal: ((n1 * P) * (S * U)) * (d2 * d3) = (((R * U) + (T * S)) * (d1 * Q)) * (d2 * d3)

  // === LHS: reshape, apply R1, distribute the resulting binomial ===
  rewrite *_assoc (n1 * P) (S * U) (d2 * d3);
  rewrite *_com (S * U) (d2 * d3);
  rewrite left *_assoc (n1 * P) (d2 * d3) (S * U);
  rewrite *_assoc n1 P (d2 * d3);
  rewrite R1;
  // LHS = (n1 * (((n2 * d3) + (n3 * d2)) * Q)) * (S * U)
  rewrite *_com ((n2 * d3) + (n3 * d2)) Q;
  rewrite *_distr_+ Q (n2 * d3) (n3 * d2);
  rewrite *_distr_+ n1 (Q * (n2 * d3)) (Q * (n3 * d2));
  rewrite *_com ((n1 * (Q * (n2 * d3))) + (n1 * (Q * (n3 * d2)))) (S * U);
  rewrite *_distr_+ (S * U) (n1 * (Q * (n2 * d3))) (n1 * (Q * (n3 * d2)));
  // LHS = ((S*U) * (n1*(Q*(n2*d3)))) + ((S*U) * (n1*(Q*(n3*d2))))

  // === RHS: distribute ===
  rewrite *_com ((R * U) + (T * S)) (d1 * Q);
  rewrite *_distr_+ (d1 * Q) (R * U) (T * S);
  rewrite *_com (((d1 * Q) * (R * U)) + ((d1 * Q) * (T * S))) (d2 * d3);
  rewrite *_distr_+ (d2 * d3) ((d1 * Q) * (R * U)) ((d1 * Q) * (T * S));
  // RHS = ((d2*d3) * ((d1*Q)*(R*U))) + ((d2*d3) * ((d1*Q)*(T*S)))

  // === Split into two monomial equalities ===
  refine @feq2 int int int (+)
    ((S * U) * (n1 * (Q * (n2 * d3))))
    ((d2 * d3) * ((d1 * Q) * (R * U)))
    _
    ((S * U) * (n1 * (Q * (n3 * d2))))
    ((d2 * d3) * ((d1 * Q) * (T * S)))
    _
  // ===== Sub-goal 1: (S*U)*(n1*(Q*(n2*d3))) = (d2*d3)*((d1*Q)*(R*U)) =====
  { // Reshape RHS to expose R*(d1*d2), then apply R2.
    rewrite *_com d2 d3;
    rewrite *_assoc d3 d2 ((d1 * Q) * (R * U));
    rewrite *_swap_l d2 (d1 * Q) (R * U);
    rewrite *_swap_l d2 R U;
    rewrite *_swap_l (d1 * Q) R (d2 * U);
    rewrite *_assoc d1 Q (d2 * U);
    rewrite *_swap_l Q d2 U;
    rewrite left *_assoc d1 d2 (Q * U);
    rewrite left *_assoc R (d1 * d2) (Q * U);
    rewrite R2;
    // RHS = d3 * (((n1*n2)*S) * (Q*U))
    rewrite *_assoc n1 n2 S;
    rewrite *_assoc n1 (n2 * S) (Q * U);
    rewrite *_swap_l d3 n1 ((n2 * S) * (Q * U));
    rewrite *_swap_l d3 (n2 * S) (Q * U);
    rewrite *_assoc n2 S (d3 * (Q * U));
    rewrite *_swap_l n2 S (d3 * (Q * U));
    rewrite left *_assoc n2 d3 (Q * U);
    rewrite *_com (n2 * d3) (Q * U);
    rewrite *_assoc Q U (n2 * d3);
    rewrite *_swap_l Q U (n2 * d3);
    // RHS = n1 * (S * (U * (Q * (n2 * d3))))
    // Reshape LHS to match.
    rewrite *_swap_l (S * U) n1 (Q * (n2 * d3));
    rewrite *_assoc S U (Q * (n2 * d3));
    reflexivity }
  // ===== Sub-goal 2: (S*U)*(n1*(Q*(n3*d2))) = (d2*d3)*((d1*Q)*(T*S)) =====
  { // Reshape RHS to expose T*(d1*d3), then apply R3.
    rewrite *_assoc d2 d3 ((d1 * Q) * (T * S));
    rewrite *_swap_l d3 (d1 * Q) (T * S);
    rewrite *_swap_l d3 T S;
    rewrite *_swap_l (d1 * Q) T (d3 * S);
    rewrite *_assoc d1 Q (d3 * S);
    rewrite *_swap_l Q d3 S;
    rewrite left *_assoc d1 d3 (Q * S);
    rewrite left *_assoc T (d1 * d3) (Q * S);
    rewrite R3;
    // RHS = d2 * (((n1*n3)*U) * (Q*S))
    rewrite *_assoc n1 n3 U;
    rewrite *_assoc n1 (n3 * U) (Q * S);
    rewrite *_swap_l d2 n1 ((n3 * U) * (Q * S));
    rewrite *_swap_l d2 (n3 * U) (Q * S);
    rewrite *_assoc n3 U (d2 * (Q * S));
    rewrite *_swap_l n3 U (d2 * (Q * S));
    rewrite left *_assoc n3 d2 (Q * S);
    rewrite *_com (n3 * d2) (Q * S);
    rewrite *_assoc Q S (n3 * d2);
    rewrite *_swap_l Q S (n3 * d2);
    // RHS = n1 * (U * (S * (Q * (n3 * d2))))
    // Reshape LHS to match: LHS = (S*U)*(n1*(Q*(n3*d2)))
    rewrite *_swap_l (S * U) n1 (Q * (n3 * d2));
    rewrite *_com S U;
    rewrite *_assoc U S (Q * (n3 * d2));
    reflexivity }
end;

// Lift ᵣdistr*+_div_nz to abstract `frac n d` form, feeding normalized N, D.
opaque symbol ᵣdistr*+_nz n1 d1 n2 d2 n3 d3 :
    π (d1 ≠ 0) → π (d2 ≠ 0) → π (d3 ≠ 0) →
    π (frac n1 d1 *ᵣ (frac n2 d2 ᵣ+ frac n3 d3)
       = (frac n1 d1 *ᵣ frac n2 d2) ᵣ+ (frac n1 d1 *ᵣ frac n3 d3)) ≔
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
  refine ᵣdistr*+_div_nz (sign d1 * Z_red_Stein n1 d1) (sign d1 * Z_red_Stein d1 n1)
                          (sign d2 * Z_red_Stein n2 d2) (sign d2 * Z_red_Stein d2 n2)
                          (sign d3 * Z_red_Stein n3 d3) (sign d3 * Z_red_Stein d3 n3)
                          hD1 hD2 hD3
end;

opaque symbol ᵣdistr*+ x y z : π(x *ᵣ (y ᵣ+ z) = x *ᵣ y ᵣ+ x *ᵣ z) ≔
begin
  refine ind_Rat (λ u, `∀ b, `∀ c, (u *ᵣ (b ᵣ+ c)) = ((u *ᵣ b) ᵣ+ (u *ᵣ c))) _;
  assume n1;
  induction
  // d1 = Z0: x = 0/1
  { assume b c;
    rewrite (frac_0_den n1);
    rewrite (zero_mul_l (b ᵣ+ c));
    rewrite (zero_mul_l b);
    rewrite (zero_mul_l c);
    rewrite (ᵣ+_neutral_div_l (0 / 1));
    reflexivity }
  // d1 = Zpos p1
  { assume p1;
    refine ind_Rat (λ u, `∀ c,
      (frac n1 (Zpos p1) *ᵣ (u ᵣ+ c))
        = ((frac n1 (Zpos p1) *ᵣ u) ᵣ+ (frac n1 (Zpos p1) *ᵣ c))) _;
    assume n2;
    induction
    // d2 = Z0: y = 0/1
    { assume c;
      rewrite (frac_0_den n2);
      rewrite (ᵣ+_neutral_div_l c);
      rewrite (zero_mul_r (frac n1 (Zpos p1)));
      rewrite (ᵣ+_neutral_div_l (frac n1 (Zpos p1) *ᵣ c));
      reflexivity }
    // d2 = Zpos p2
    { assume p2;
      refine ind_Rat (λ u,
        (frac n1 (Zpos p1) *ᵣ (frac n2 (Zpos p2) ᵣ+ u))
          = ((frac n1 (Zpos p1) *ᵣ frac n2 (Zpos p2)) ᵣ+ (frac n1 (Zpos p1) *ᵣ u))) _;
      assume n3;
      induction
      { rewrite (frac_0_den n3);
        rewrite (ᵣ+_neutral_div_r (frac n2 (Zpos p2)));
        rewrite (zero_mul_r (frac n1 (Zpos p1)));
        rewrite (ᵣ+_neutral_div_r (frac n1 (Zpos p1) *ᵣ frac n2 (Zpos p2)));
        reflexivity }
      { assume p3;
        refine ᵣdistr*+_nz n1 (Zpos p1) n2 (Zpos p2) n3 (Zpos p3)
          (Zpos≠Z0 p1) (Zpos≠Z0 p2) (Zpos≠Z0 p3) }
      { assume p3;
        refine ᵣdistr*+_nz n1 (Zpos p1) n2 (Zpos p2) n3 (Zneg p3)
          (Zpos≠Z0 p1) (Zpos≠Z0 p2) (Zneg≠Z0 p3) } }
    // d2 = Zneg p2
    { assume p2;
      refine ind_Rat (λ u,
        (frac n1 (Zpos p1) *ᵣ (frac n2 (Zneg p2) ᵣ+ u))
          = ((frac n1 (Zpos p1) *ᵣ frac n2 (Zneg p2)) ᵣ+ (frac n1 (Zpos p1) *ᵣ u))) _;
      assume n3;
      induction
      { rewrite (frac_0_den n3);
        rewrite (ᵣ+_neutral_div_r (frac n2 (Zneg p2)));
        rewrite (zero_mul_r (frac n1 (Zpos p1)));
        rewrite (ᵣ+_neutral_div_r (frac n1 (Zpos p1) *ᵣ frac n2 (Zneg p2)));
        reflexivity }
      { assume p3;
        refine ᵣdistr*+_nz n1 (Zpos p1) n2 (Zneg p2) n3 (Zpos p3)
          (Zpos≠Z0 p1) (Zneg≠Z0 p2) (Zpos≠Z0 p3) }
      { assume p3;
        refine ᵣdistr*+_nz n1 (Zpos p1) n2 (Zneg p2) n3 (Zneg p3)
          (Zpos≠Z0 p1) (Zneg≠Z0 p2) (Zneg≠Z0 p3) } } }
  // d1 = Zneg p1
  { assume p1;
    refine ind_Rat (λ u, `∀ c,
      (frac n1 (Zneg p1) *ᵣ (u ᵣ+ c))
        = ((frac n1 (Zneg p1) *ᵣ u) ᵣ+ (frac n1 (Zneg p1) *ᵣ c))) _;
    assume n2;
    induction
    { assume c;
      rewrite (frac_0_den n2);
      rewrite (ᵣ+_neutral_div_l c);
      rewrite (zero_mul_r (frac n1 (Zneg p1)));
      rewrite (ᵣ+_neutral_div_l (frac n1 (Zneg p1) *ᵣ c));
      reflexivity }
    { assume p2;
      refine ind_Rat (λ u,
        (frac n1 (Zneg p1) *ᵣ (frac n2 (Zpos p2) ᵣ+ u))
          = ((frac n1 (Zneg p1) *ᵣ frac n2 (Zpos p2)) ᵣ+ (frac n1 (Zneg p1) *ᵣ u))) _;
      assume n3;
      induction
      { rewrite (frac_0_den n3);
        rewrite (ᵣ+_neutral_div_r (frac n2 (Zpos p2)));
        rewrite (zero_mul_r (frac n1 (Zneg p1)));
        rewrite (ᵣ+_neutral_div_r (frac n1 (Zneg p1) *ᵣ frac n2 (Zpos p2)));
        reflexivity }
      { assume p3;
        refine ᵣdistr*+_nz n1 (Zneg p1) n2 (Zpos p2) n3 (Zpos p3)
          (Zneg≠Z0 p1) (Zpos≠Z0 p2) (Zpos≠Z0 p3) }
      { assume p3;
        refine ᵣdistr*+_nz n1 (Zneg p1) n2 (Zpos p2) n3 (Zneg p3)
          (Zneg≠Z0 p1) (Zpos≠Z0 p2) (Zneg≠Z0 p3) } }
    { assume p2;
      refine ind_Rat (λ u,
        (frac n1 (Zneg p1) *ᵣ (frac n2 (Zneg p2) ᵣ+ u))
          = ((frac n1 (Zneg p1) *ᵣ frac n2 (Zneg p2)) ᵣ+ (frac n1 (Zneg p1) *ᵣ u))) _;
      assume n3;
      induction
      { rewrite (frac_0_den n3);
        rewrite (ᵣ+_neutral_div_r (frac n2 (Zneg p2)));
        rewrite (zero_mul_r (frac n1 (Zneg p1)));
        rewrite (ᵣ+_neutral_div_r (frac n1 (Zneg p1) *ᵣ frac n2 (Zneg p2)));
        reflexivity }
      { assume p3;
        refine ᵣdistr*+_nz n1 (Zneg p1) n2 (Zneg p2) n3 (Zpos p3)
          (Zneg≠Z0 p1) (Zneg≠Z0 p2) (Zpos≠Z0 p3) }
      { assume p3;
        refine ᵣdistr*+_nz n1 (Zneg p1) n2 (Zneg p2) n3 (Zneg p3)
          (Zneg≠Z0 p1) (Zneg≠Z0 p2) (Zneg≠Z0 p3) } } }
end;

