require open Stdlib.Prop Stdlib.Eq Stdlib.Z Stdlib.Prod Stdlib.Zgcd;


symbol rat: Set;

// Decidable predicate gcd |a| |b| = 1
symbol coprime (a b: τ int): 𝔹 ≔  isEq ((Z_gcd (abs a) (abs b)) ≐ 1);

// Rational numbers, implemented as a pair of integers num / den such that
// the denominator is positive and the numerator and denominator are coprime.
// The denominator of the rational number is greater than zero.
// The numerator and denominator are coprime: it is in "reduced form".
symbol Rat : Π (a b: τ int), π (isLt (0 ≐ b) and coprime a b) → τ rat;

symbol num (a: τ rat) : τ int;
rule num  (Rat $a _ _) ↪ $a;

symbol den (a: τ rat) : τ int;
rule den (Rat _ $b _ ) ↪ $b;

symbol valq : τ rat → τ (int × int);
rule valq (Rat $n $d _) ↪ ($n ‚ $d);

symbol 1⫽1 : τ rat ≔ Rat 1 1 ⊤ᵢ;

symbol bool_to_Z : 𝔹 → ℤ;
rule bool_to_Z true ↪ 1
with  bool_to_Z false ↪ 0;

// symbol fracq_subdef (x : τ (int × int)): τ (int × int);
// rule fracq_subdef ($x ‚ $y) ↪
//     if (isNEq  ($y ≐ 0))
//         (let g ≔ (Z_gcd (abs $x) (abs $y)) in
//             let yIsLt0 ≔ bool_to_Z (isLt ($y ≐ 0)) in
//             let xIsLt0 ≔ bool_to_Z (isLt ($x ≐ 0)) in
//             (
//                 (((— 1) ^ (yIsLt0 + xIsLt0)) * (div (abs $x) g))‚ (div (abs $y) g)
//             )
//         )
//         (0 ‚ 1);

// Function returns a normalized a pair of integers representing a rational number with:
// * No common divisors (i.e. reduced to lowest terms),
// * A positive denominator, and
// * A sign encoded in the numerator.
symbol fracq_subdef (x : τ (int × int)): τ (int × int) ≔
    if (isNEq  ((x ₂) ≐ 0))
        (let g ≔ (Z_gcd (abs (x ₁)) (abs (x ₂))) in // compute GCD
            let yIsLt0 ≔ bool_to_Z (isLt ((x ₂) ≐ 0)) in
            let xIsLt0 ≔ bool_to_Z (isLt ((x ₁) ≐ 0)) in
            (
                (((— 1) ^ (yIsLt0 + xIsLt0)) * (div (abs (x ₁)) g))‚ (div (abs (x ₂)) g) // normalize the Fraction
            )
        )
        (0 ‚ 1);

assert ⊢ fracq_subdef (0 ‚ 1) ≡ (0 ‚ 1);
assert ⊢ fracq_subdef (16 ‚ 24) ≡ (2 ‚ 3);
assert ⊢ fracq_subdef ((— 16) ‚ 24) ≡ ((— 2) ‚ 3);
assert ⊢ fracq_subdef (16 ‚ — 24) ≡ ((— 2) ‚ 3);
assert ⊢ fracq_subdef ((— 16) ‚ — 24) ≡ (2 ‚ 3);

// symbol fracq_opt_subdef (x : τ (int × int)): τ (int × int);
// rule fracq_opt_subdef ($x ‚ $y) ↪ 
//     if (isLt (0 ≐ $y) and coprime $x $y) ($x ‚ $y) (fracq_subdef ($x ‚ $y));

symbol fracq_opt_subdef (x : τ (int × int)): τ (int × int) ≔
    if (isLt (0 ≐ (x ₂)) and coprime (x ₁) (x ₂)) ((x ₁) ‚ (x ₂)) (fracq_subdef ((x ₁) ‚ (x ₂)));

opaque symbol fracq_opt_subdefE (x : τ (int × int)) : π ((fracq_opt_subdef x) = (fracq_subdef x)) ≔
begin
admitted;

opaque symbol fracq_subproof_aux x y : π (isLt (0 ≐ y) and coprime x y) ≔
begin
admitted;

opaque symbol fracq_subproof (x: τ (int × int))
    : let y ≔ (fracq_opt_subdef x) in π (isLt (0 ≐ (y ₂)) and coprime (y ₁) (y ₂)) ≔
begin
    assume x;
    simplify;
    admit
end;


// `fracq` returns a normalized rational number with:
// * No common divisors (i.e. reduced to lowest terms),
// * A positive denominator, and
// * A sign encoded in the numerator.
symbol fracq (n d : τ int) : τ rat;
rule fracq $n Z0 ↪ Rat 0 1 (fracq_subproof (1 ‚ 0))
with fracq $n (Zpos $d) ↪ 
    let res ≔ fracq_opt_subdef  ($n ‚ (Zpos $d)) in
    let n' ≔ res ₁ in
    let d' ≔ res ₂ in
        Rat (res ₁) (res ₂) (fracq_subproof ($n ‚ (Zpos $d)))
with fracq $n (Zneg $d) ↪ 
    let res ≔ fracq_opt_subdef  ($n ‚ (Zneg $d)) in
    let n' ≔ res ₁ in
    let d' ≔ res ₂ in
        Rat (res ₁) (res ₂) (fracq_subproof ($n ‚ (Zneg $d)))
;

assert ⊢ fracq 0 100 ≡ Rat 0 1 (fracq_subproof (0 ‚ 100));

assert ⊢ fracq 1 0 ≡ Rat 0 1 (fracq_subproof (1 ‚ 0));

assert ⊢ fracq 98 42 ≡ Rat 7 3 (fracq_subproof (98 ‚ 42));

opaque symbol valqK x : π ((fracq ((valq x) ₁) ((valq x) ₂)) = x) ≔
begin admitted;

opaque symbol coprimen1 n : π (coprime n 1) ≔
begin admitted;

symbol ratz (n : τ int) ≔ Rat n 1 (coprimen1 n);

opaque symbol coprime0n n : π (coprime 0 n) ≔
begin admitted;

symbol 0⫽1 : τ rat ≔ Rat 0 1 ⊤ᵢ;

opaque symbol coprime_num_den n : π (coprime (num n) (den n)) ≔
begin admitted;

opaque symbol rat-def n p : π (Rat (num n) (den n) p = n) ≔
begin admitted;

symbol q+ : τ rat → τ rat → τ rat; notation q+ infix left 20 ; 
rule (Rat $n1 $d1 _) q+ (Rat $n2 $d2 _) ↪
    let u ≔ ($n1 * $d2) + ($n2 * $d1) in
    let d ≔ $d1 * $d2 in
    fracq u d;

opaque symbol q+_com x y: π (x q+ y = y q+ x) ≔
begin
admitted;

opaque symbol q+_trans x y z: π (x q+ y q+ z = x q+ (y q+ z)) ≔
begin
admitted;


opaque symbol q+_neutral_l q : π ((0⫽1 q+ q) = q) ≔
begin
admitted;

opaque symbol q+_neutral_r q : π ((q q+ 0⫽1) = q) ≔
begin
admitted;

symbol q* : τ rat → τ rat → τ rat; notation q* infix left 20 ;
rule (Rat $n1 $d1 _) q* (Rat $n2 $d2 _) ↪
    let u ≔ $n1 * $n2 in
    let d ≔ $d1 * $d2 in
    fracq u d;

opaque symbol q*_com x y: π (x q* y = y q* x) ≔
begin
admitted;

opaque symbol q*_trans x y z: π (x q* y q* z = x q* (y q* z)) ≔
begin
admitted;

opaque symbol q*_cancel_r x: π (x q* 0⫽1 = 0⫽1) ≔
begin
admitted;

opaque symbol q*_cancel_l x: π (0⫽1 q* x = 0⫽1) ≔
begin
admitted;

opaque symbol q*_neutral_r x: π (x q* 1⫽1 = x) ≔
begin
admitted;

opaque symbol q*_neutral_l x: π (1⫽1 q* x = x) ≔
begin
admitted;

opaque symbol distrq*q+ x y z : π(x q* (y q+ z) = x q* y q+ x q* z) ≔
begin
admitted;

symbol q- : τ rat → τ rat → τ rat; notation q- infix left 20;
rule  (Rat $n1 $d1 _) q- (Rat $n2 $d2 _) ↪
    let u ≔ ($n1 * $d2) - ($n2 * $d1) in
    let d ≔ $d1 * $d2 in
    fracq u d;

symbol q~: τ rat → τ rat; notation q~ prefix 24;
rule q~ (Rat $n $d _) ↪ fracq (— $n) $d;

opaque symbol q+_opp_l q : π ((q~ q) q+ q = 0⫽1) ≔
begin admitted;

opaque symbol q-_equiv_q_opp x y : π ((x q- y) = (x q+ (q~ y))) ≔
begin
admitted;

symbol ⁻¹ : τ rat → τ rat; notation ⁻¹ postfix 25;
rule (Rat $n $d _) ⁻¹ ↪ fracq $d $n;

opaque symbol qinvinv_eq_id x : π ((x ⁻¹) ⁻¹ = x) ≔
begin
admitted;
