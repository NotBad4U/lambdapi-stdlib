require open Stdlib.Prop Stdlib.Prod Stdlib.Set Stdlib.Eq Stdlib.Nat Stdlib.Bool;
require open Stdlib.List Stdlib.Impred;


require Stdlib.Fin as fin;
open Stdlib.Fin;

// We define bitvectors. We choose the `Fin` representation over others for its relative efficiency
// and the fact that bitwise operations on `Fin` are defined. Some other possible
// representations are `Vec n 𝔹`, `{ l : List Bool | l.length = w}`, `{ n : BinNat | size n = w}`.
injective symbol BitVec n ≔ Fin (2 ^ n);
symbol mkBv n v p : BitVec n  ≔ FinMk (2 ^ n) v p;

symbol bvnil ≔ BitVec 0;

// b#00101

symbol from_fin n m : Fin n →  π (n ≤ 2 ^ m) → BitVec m ≔
begin
assume n m bv1 p;
apply FinMk (2 ^ m) (val bv1) ;
admit
end;

private symbol bv0 : BitVec 4 ≔ FinMk (2 ^ 4) 2 ⊤ᵢ;
private symbol bv1 : BitVec 4 ≔ FinMk (2 ^ 4) 5 ⊤ᵢ;
private symbol bv2 : BitVec 4 ≔ FinMk (2 ^ 4) 15 ⊤ᵢ;
private symbol bv7 : BitVec 4 ≔ FinMk (2 ^ 4) 7 ⊤ᵢ;
private symbol bv3 : BitVec 4 ≔ FinMk (2 ^ 4) 13 ⊤ᵢ;

// We inherit `Fin` implementations
// symbol bvadd (n: ℕ): BitVec n → BitVec n → BitVec n ≔ λ x, λ y, (add (2 ^ n) x y);
symbol bvadd [n: ℕ]: BitVec n → BitVec n → BitVec n;
rule @bvadd $n $bv1 $bv2 ↪ @add (2 ^ $n) $bv1 $bv2;


symbol to_nat [n: ℕ]: BitVec n → ℕ ;
rule @to_nat $n (exist $v _) ↪ $v; 

compute to_nat (bvadd bv1 bv2);
assert ⊢ @to_nat 4 (bvadd (FinMk (2 ^ 4) 5 ⊤ᵢ) (FinMk (2 ^ 4) 15 ⊤ᵢ)) ≡ 4;

//compute 

symbol bvsub [n: ℕ]: BitVec n → BitVec n → BitVec n ≔ λ x, λ y, (fin.sub (2 ^ n) x y);

symbol bvmul [n: ℕ]: BitVec n → BitVec n → BitVec n ≔ λ x, λ y, (fin.mul (2 ^ n) x y);

symbol bvshiftl [n: ℕ]: BitVec n → BitVec n → BitVec n ≔ λ x, λ y, (fin.shiftl (2 ^ n) x y);

symbol bvshiftr [n: ℕ]: BitVec n → BitVec n → BitVec n ≔ λ x, λ y, (fin.shiftr (2 ^ n) x y);

symbol bvand [n: ℕ]: BitVec n → BitVec n → BitVec n ≔ λ x, λ y, (fin.and (2 ^ n) x y);

symbol bvor [n: ℕ]: BitVec n → BitVec n → BitVec n ≔ λ x, λ y, (fin.or (2 ^ n) x y);

compute bvor bv0 bv1;
type bv7;
compute bv7;

// assert ⊢ bvor bv0 bv1  ≡ bv7;

// Create a bitvector of size `n` fill with 0 
symbol bv_fill_zero (n: ℕ): BitVec n ≔ begin
    assume n;
    apply FinMk (2 ^ n) 0;
    generalize n;
    induction
    {apply ⊤ᵢ}
    {
        assume x IH; rewrite expnS;
        apply @leq_trans  1 (2 ^ x) (2 * (2 ^ x))
        {apply IH}
        {
            change (π (istrue ((1 * 2 ^ x) ≤ (2 * (2 ^ x)))));
            apply leq_mul 1 (2 ^ x) 2 (2 ^ x) {apply ⊤ᵢ} { apply ≤_refl (2 ^ x) };
        };
    }
end;

//     (concat (_ BitVec i) (_ BitVec j) (_ BitVec m))
//   - concatenation of bitvectors of size i and j to get a new bitvector of
//     size m, where m = i + j
symbol bvconcat [n m: ℕ]: BitVec n → BitVec m → BitVec (n + m) ≔
begin
    assume n m bv1 bv2;
    set val_bv1 ≔ (bv1 s₁);
    set val_bv2 ≔ (bv2 s₁);
    apply mkBv (n + m) (val_bv1 + val_bv2);
    simplify;
    set x ≔ (bv1 s₁);
    set y ≔ (bv2 s₁); 
    type (bv1 s₂);
    have h1 : π (istrue (x + 1 ≤ (2 ^ n))) { refine bv1 s₂  };
    have h2 : π (istrue (y + 1 ≤ (2 ^ m))) { refine bv2 s₂  };
    have h3:  π (istrue ((x + 1) + (y + 1) ≤ ((2 ^ n) + (2 ^ m)))) {
        refine leq_add (x + 1) (y + 1) (2 ^ n) (2 ^ m) h1 h2;
    };
    have h4:  π (istrue (x + y + 2  ≤ ((2 ^ n) + (2 ^ m)))) {
        admit
    };
    admit //finish proof
end;

symbol of_nat_lt (n v: ℕ) (p: π (v ≤ 2 ^ n) ): BitVec n;

symbol bv_size [n] : BitVec n → ℕ ≔ λ _, n;

compute bv_size bv0;

symbol nat_to_prop: ℕ → Prop;
rule nat_to_prop 0 ↪ ⊥
with nat_to_prop (_ +1) ↪ ⊤;

// (n & ( 1 << k )) >> k ≡ (n >> k) & 1
symbol bitof [n] (m: ℕ) : BitVec n → ℕ;
rule @bitof $n $m $bvn ↪ ((@to_nat $n $bvn) >>> $m) Stdlib.Nat.&& 1;

// 13 = 1101#b
assert ⊢ @bitof 4 0 (FinMk (2 ^ 4) 13 ⊤ᵢ) ≡ 1;
assert ⊢ @bitof 4 1 (FinMk (2 ^ 4) 13 ⊤ᵢ) ≡ 0;
assert ⊢ @bitof 4 2 (FinMk (2 ^ 4) 13 ⊤ᵢ) ≡ 1;
assert ⊢ @bitof 4 3 (FinMk (2 ^ 4) 13 ⊤ᵢ) ≡ 1;

assert ⊢ (FinMk 2 1 ⊤ᵢ) : BitVec 1;

coerce_rule coerce 𝔹 ℕ $x ↪ if $x 1 0;

symbol list_bool_to_nat: 𝕃 bool → τ nat;
rule list_bool_to_nat (true ⸬ $xs) ↪ (list_bool_to_nat $xs) * 2 + 1
with list_bool_to_nat (false ⸬ $xs) ↪ (list_bool_to_nat $xs) * 2
with list_bool_to_nat □ ↪ 0;

compute list_bool_to_nat (true ⸬ false ⸬ true ⸬ true ⸬ □);

symbol bbT (l: 𝕃 bool) :  BitVec (size l) ≔
begin
    assume l;
    apply mkBv (size l) (list_bool_to_nat l);
    generalize l;
    induction
    { apply ⊤ᵢ }
    {
        assume b bs ih;
        refine ∨ₑ (case_𝔹 b) _ _
        {
            assume hb_is_true; rewrite hb_is_true; simplify;
            have g: π (2 * (list_bool_to_nat bs +1) ≤ 2 * 2 ^ size bs)
            {
                refine ∧ₑ₂ (leq_pmul2l 2 (list_bool_to_nat bs +1) (2 ^ size bs) ⊤ᵢ) ih
            };
            remove ih;
            rewrite mulnC;
            simplify;
            refine g
        }
        {
            assume hb_is_false; rewrite hb_is_false; simplify;
            have g: π (istrue ((list_bool_to_nat bs +1) ≤ (2 ^ size bs))) { refine ih };
            have g3: π (2 * (list_bool_to_nat bs +1) ≤ 2 * 2 ^ size bs) { refine ∧ₑ₂ (leq_pmul2l 2  (list_bool_to_nat bs +1) (2 ^ size bs) ⊤ᵢ) g };
            have g4: π (istrue ((list_bool_to_nat bs + (1 * (list_bool_to_nat bs +1))) < ((2 ^ size bs) + (2 ^ size bs)))) { refine g3 };
            rewrite mulnC;
            simplify;
            have same : π (istrue (((list_bool_to_nat bs + list_bool_to_nat bs)) < ((2 ^ size bs) + (2 ^ size bs)))) → π (istrue (((list_bool_to_nat bs + list_bool_to_nat bs) +1) ≤ ((2 ^ size bs) + (2 ^ size bs)))) { refine λ x, x }; 
            refine same _;
            have g5: π (istrue ((list_bool_to_nat bs + list_bool_to_nat bs) < ((2 ^ size bs) + (2 ^ size bs)))) { refine ltsnm (list_bool_to_nat bs + list_bool_to_nat bs) ((2 ^ size bs) + (2 ^ size bs)) g4 };
            refine g5
        };
    }
end;

symbol ite : Prop → Π [a], τ a → τ a → τ a;

rule ite ⊤  $x _ ↪ $x
with ite ⊥ _ $y ↪ $y;

compute bv0;

compute @bitof 4 1 (ite ⊤ bv0 bv1);


compute to_nat (bbT (true ⸬ true ⸬ true ⸬ □));

// compute (bbT2 4 (⊤ ⸬ ⊥ ⸬ ⊤ ⸬ □));

// compute (bbT2 4 (istrue true ⸬ istrue false ⸬ istrue true ⸬ □));

// compute (bbT2 4 ((@bitof 4 1 (ite ⊥ bv0 bv1)) ⸬ ⊥ ⸬ ⊤ ⸬ □));

require open  Stdlib.Tactic;

symbol MyAll [a] : (τ a → τ o) → 𝕃 a → τ o;
rule MyAll _ □ ↪ ⊤
with MyAll $p ($x ⸬ $l) ↪  ($p $x) ∧ (MyAll $p $l);

// Function that cast a BitVec (size l) into a BitVec n.
// This is necessary because bbT construct a bitvector from a list
symbol bbt_cast (n: ℕ)  (l: 𝕃 o): BitVec (size l) → π (size l = n) → BitVec n ≔
begin
    simplify;
    assume n l bv h;
    print ind_eq;
    type (bv s₂);
    have g: π ((λ u, istrue ((u +1) ≤ (2 ^ n))) (bv s₁)) { rewrite left h; refine (bv s₂) };
    refine @exist nat (λ u, istrue ((u +1) ≤ (2 ^ n))) (bv s₁) g;
end;


symbol zero_extend [n : ℕ] (k: ℕ) : BitVec n → BitVec (k + n);
rule @zero_extend $n $k $bv ↪ @bvconcat $k $n (bv_fill_zero $k) $bv;

assert ⊢ zero_extend 3 bv1 : BitVec ((bv_size bv1) + 3);

symbol bveq [n : ℕ] : BitVec n → BitVec n → 𝔹 ≔ λ b1 b2,  (eqn (to_nat b1) (to_nat b2));

//   (bvcomp (_ BitVec m) (_ BitVec m) (_ BitVec 1))
//      - bit comparator: equals #b1 iff all bits are equal
symbol bvcomp [n : ℕ] : BitVec n → BitVec n → BitVec 1;
rule bvcomp $b1 $b2 ↪ if (bveq $b1 $b2) (FinMk (2  ^ 1) 1 ⊤ᵢ) (FinMk (2  ^ 1) 0 ⊤ᵢ);

symbol bvult [n]: BitVec n → BitVec n → Prop ≔ λ b1 b2, istrue((to_nat b1) < (to_nat b2));

symbol bvugt [n]: BitVec n → BitVec n → Prop ≔ λ b1 b2, istrue((to_nat b1) > (to_nat b2));

symbol bvuge [n]: BitVec n → BitVec n → Prop ≔ λ b1 b2, istrue((to_nat b1) ≥ (to_nat b2));

symbol bvule [n]: BitVec n → BitVec n → Prop ≔ λ b1 b2, istrue((to_nat b1) ≤ (to_nat b2));


// coerce_rule coerce 𝔹 ℕ $x ↪ if $x 1 0;

symbol nat_to_bool : ℕ → 𝔹;
rule  nat_to_bool 0 ↪ false
with  nat_to_bool (_ +1) ↪ true;

symbol BitOfVar_aux (c: ℕ) (n: ℕ) (t: BitVec n):  𝕃 bool;
rule BitOfVar_aux _0 _ _ ↪ □
with BitOfVar_aux ($c +1) $n $t ↪ nat_to_bool (bitof $c $t) ⸬ (BitOfVar_aux $c $n $t);


symbol BitOfVar [n: ℕ] (t: BitVec n):  𝕃 bool ≔ Stdlib.List.rev (BitOfVar_aux (bv_size t) (bv_size t) t);

compute BitOfVar bv0;

compute bv0 s₁;

// compute bbT (BitOfVar bv0);


// @[norm_cast, simp]
// theorem val_bitvec_eq {a b : BitVec w} : a.val = b.val ↔ a = b :=
//   ⟨(match a, b, · with | ⟨_, _⟩,⟨_, _⟩, rfl => rfl), (· ▸ rfl)⟩
opaque symbol val_bitvec_eq [n] (x y : BitVec n) : π (x s₁ = y s₁ ⇔ x = y) ≔
begin
    assume n;
    assume x y;
    apply ∧ᵢ
    {
        generalize x;
        induction;
        assume xval xproof;
        induction;
        assume yval yproof;
        simplify;
        assume h;
        apply eq_Σ;
        refine h
    }
    {
        simplify;
        assume h;
        rewrite h;
        reflexivity
    }
end;

// theorem BV_eq {x y : BitVec w} (h: 0 < w): bitwise_eq x.val y.val w = (x = y) := by
//   simp [← bitwise_eq_eq h x.isLt y.isLt]

// Signed result

require open Stdlib.Z;
require open Stdlib.Pos;
require open Stdlib.Comp;

symbol nat_to_int : ℕ → ℤ;
rule nat_to_int _0 ↪ Z0
with nat_to_int ($x +1) ↪ Zpos (of_succ_nat ($x +1));

symbol to_int [n: ℕ] : BitVec n → ℤ;

// symbol last_bit [n: ℕ] : BitVec n → ℕ;
// rule @last_bit $n $b ↪ (@bitof $n ($n - 1) $b);
 
// rule @to_int $n $bv ↪ let m ≔ nat_to_int (@to_nat $n $bv) in
//                         if (eqn _0 (last_bit $bv)) m (m - 2 ^ nat_to_int $n);

symbol bvslt [n]: BitVec n → BitVec n → Prop ≔ λ b1 b2, (to_int b1) < (to_int b2);

symbol bvsgt [n]: BitVec n → BitVec n → Prop ≔ λ b1 b2, (to_int b1) > (to_int b2);

symbol bvsge [n]: BitVec n → BitVec n → Prop ≔ λ b1 b2, (to_int b1) ≥ (to_int b2);

symbol bvsle [n]: BitVec n → BitVec n → Prop ≔ λ b1 b2, (to_int b1) ≤ (to_int b2);
