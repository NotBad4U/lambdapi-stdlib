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

// (1) Cross-product of GCD reduction:
//     Z_red_Stein a b = a / gcd(a,b), so (a/g) * b = a * (b/g).
symbol Z_red_Stein_cross a b : π (Z_red_Stein a b * b = a * Z_red_Stein b a);

// (2) Standard cross-multiplication characterization of rational equality.
//     For nonzero b, d: frac a b = frac c d iff a*d = c*b.
symbol frac_eq a b c d : π (b ≠ 0) → π (d ≠ 0) → π (a * d = c * b) → π (frac a b = frac c d);

// (3) Non-zero preservation lemmas (would normally live in Z.lp / Zgcd.lp).
symbol mul_ne_0 a b : π (a ≠ 0) → π (b ≠ 0) → π (a * b ≠ 0);
symbol sign_ne_0 a : π (a ≠ 0) → π (sign a ≠ 0);
symbol Z_red_Stein_l_ne_0 a b : π (a ≠ 0) → π (Z_red_Stein a b ≠ 0);

// Scaled cross-product: with sign factors, the cross-product identity
// for the normalized numerator/denominator pair.
opaque symbol frac_red_cross b A :
  π ((sign b * Z_red_Stein A b) * b = A * (sign b * Z_red_Stein b A)) ≔
begin
    assume b A;
    rewrite *_assoc;
    rewrite Z_red_Stein_cross;
    rewrite left *_assoc;
    rewrite *_com (sign b) A;
    rewrite *_assoc;
    reflexivity
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
    refine *_reg_r _ _ d2 _;
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


symbol ᵣ+_com x y :  π (x ᵣ+ y = y ᵣ+  x) ≔
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

symbol ᵣ*_com x y :  π (x *ᵣ y = y *ᵣ x) ≔
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

opaque symbol div_add_neutral_l n d : π ((0 / 1 ᵣ+ n / d) = n / d) ≔
begin
assume n1 d1;
simplify;
change π ((sign (_1 * d1) * Z_red_Stein (n1 * _1) (_1 * d1)) / (sign (1 * d1) * Z_red_Stein (_1 * d1) (n1 * _1)) = (n1 / d1));
rewrite *_neutral_l;
rewrite *_neutral;
admit
end;

opaque symbol div_add_neutral_r n d : π ((n / d ᵣ+ 0 / 1) = n / d) ≔
begin
admitted;

opaque symbol ᵣ+_neutral_frac_l x : π ((frac 0 1 ᵣ+ x) = x) ≔
begin
    refine ind_Rat (λ u, ((frac 0 _1 ᵣ+ u) = u)) _;
    assume n d;
    simplify;
    set N ≔ (sign d * Z_red_Stein n d);
    set D ≔ (sign d * Z_red_Stein d n);
    change  π (((sign (_1 * D) * Z_red_Stein (N * _1) (_1 * D)) / (sign (_1 * D) * Z_red_Stein (_1 * D) (N * _1))) = (N / D));
    rewrite *_neutral_l;
    rewrite *_neutral;
    have HD: π (sign D = 1 ∨ sign D = — 1) { refine sign_case D };
    have Hd: π (sign d = 1 ∨ sign d = — 1) { refine sign_case d };
    apply ∨ₑ HD
    {
        assume heq; rewrite heq;
        apply ∨ₑ Hd
        {
            assume heq2;
            admit
        }
        {admit}
    }
    {admit}
end;

opaque symbol ᵣ+_neutral_l x : π ((frac 0 1 ᵣ+ x) = x) ≔
begin
admitted;

opaque symbol ᵣ+_neutral_r x : π ((x ᵣ+ frac 0 1) = x) ≔
begin
admitted;

opaque symbol ᵣ+_neutral_div_l x : π ((0 / 1 ᵣ+ x) = x) ≔
begin
    refine ind_Rat (λ u, (((0 / _1) ᵣ+ u) = u)) _;
    assume x y;
    simplify ᵣ+;
    change π (frac ((0 * (sign y * Z_red_Stein y x)) + ((sign y * Z_red_Stein x y) * _1)) (_1 * (sign y * Z_red_Stein y x)) = frac x y);
    rewrite *_neutral;
    rewrite *_neutral_l;
    rewrite *_cancel_l;
    simplify +;
    admit
end;

opaque symbol ᵣ+_neutral_div_r x : π ((x ᵣ+ 0 / 1) = x) ≔
begin
admitted;

opaque symbol ᵣ*_neutral_l x : π ((frac 1 1 *ᵣ x) = x) ≔
begin
admitted;

opaque symbol ᵣ*_neutral_r x : π ((x *ᵣ frac 1 1) = x) ≔
begin
admitted;

opaque symbol ᵣ*_neutral_div_l x : π ((1 / 1 *ᵣ x) = x) ≔
begin
admitted;

opaque symbol ᵣ*_neutral_div_r x : π ((x *ᵣ 1 / 1) = x) ≔
begin
admitted;

symbol nze_frac : π (0 / 1 = frac 0 1) ≔
begin reflexivity end;

// Lifting ᵣ+_assoc_div to abstract ℚ requires handling the degenerate
// case where d1, d2, or d3 = 0 (these reduce via the rule _/0 → 0/1
// and require the still-admitted neutral element lemmas
// ᵣ+_neutral_div_l / _r). Admitted for now; the meaty case lives in
// ᵣ+_assoc_div above.
opaque symbol ᵣ+_assoc x y z :  π (((x ᵣ+ y) ᵣ+ z) = (x ᵣ+ (y ᵣ+ z))) ≔
begin
admitted;


symbol ᵣ≐: ℚ → ℚ → Comp; notation ᵣ≐ infix 10;
rule ($n1 / $d1) ᵣ≐ ($n2 / $d2) ↪ $n1 * $d2 ≐ $n2 * $d1;


opaque symbol distr*ᵣᵣ+ x y z : π(x *ᵣ (y ᵣ+ z) = x *ᵣ y ᵣ+ x *ᵣ z) ≔
begin
admitted;