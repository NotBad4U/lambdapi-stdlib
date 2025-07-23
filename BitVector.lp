require open Stdlib.Prop Stdlib.Prod Stdlib.Set Stdlib.Eq Stdlib.BinNat Stdlib.Nat Stdlib.Bool;
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
apply FinMk (2 ^ m) (val bv1);

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
        apply @leq_trans  1 (_2 ^ x) (_2 * (_2 ^ x))
        {apply IH}
        {
            have g: π (_2 ^ x = 1 * _2 ^ x) { reflexivity };
            rewrite .[x in istrue (x ≤ _)] g ;
            apply leq_mul 1 (_2 ^ x) 2 (_2 ^ x) {apply ⊤ᵢ} { apply ≤_refl (_2 ^ x) };
        };
    }
end;

symbol bvconcat [n m: ℕ]: BitVec n → BitVec m → BitVec (n + m) ≔
begin
    assume n m bv1 bv2;
    set val_bv1 ≔ (to_nat bv1);
    set val_bv2 ≔ (to_nat bv2);
    set bv1' ≔ (0 ⎪⎪ val_bv1) <<< m;
    set bv2' ≔ 0 ⎪⎪ val_bv2;
    apply FinMk (2 ^ (n + m)) (bv1' ⎪⎪ bv2');
    admit
end;

symbol of_nat_lt (n v: ℕ) (p: π (v ≤ 2 ^ n) ): BitVec n;

symbol bv_size [n] : BitVec n → ℕ ≔ λ _, n; 

// (n & ( 1 << k )) >> k ≡ (n >> k) & 1
symbol bitof [n] m: π (m ≤ n) → BitVec n → ℕ;
rule @bitof $n $m _ $bvn ↪ ((@to_nat $n $bvn) >>> $m) && 1;

// 13 = 1101#b
assert ⊢ @bitof 4 0 (⊤ᵢ) (FinMk (2 ^ 4) 13 ⊤ᵢ) ≡ 1;
assert ⊢ @bitof 4 1 (⊤ᵢ) (FinMk (2 ^ 4) 13 ⊤ᵢ) ≡ 0;
assert ⊢ @bitof 4 2 (⊤ᵢ) (FinMk (2 ^ 4) 13 ⊤ᵢ) ≡ 1;
assert ⊢ @bitof 4 3 (⊤ᵢ) (FinMk (2 ^ 4) 13 ⊤ᵢ) ≡ 1;

assert ⊢ (FinMk 2 1 ⊤ᵢ) : BitVec 1;

//coerce_rule coerce 𝔹 ℕ $x ↪ if $x 1 0;

symbol list_bool_to_nat: 𝕃 bool → τ nat ≔ λ l, foldl (λ acc, λ x, acc * 2 + (if x 1 0)) 0 l;

symbol list_Bool_to_nat: 𝕃 o → τ nat;
rule list_Bool_to_nat (⊤ ⸬ $xs) ↪ (list_Bool_to_nat $xs) * 2 + 1
with list_Bool_to_nat (⊥ ⸬ $xs) ↪ (list_Bool_to_nat $xs) * 2
with list_Bool_to_nat □ ↪ 0;

compute list_bool_to_nat (true ⸬ false ⸬ true ⸬ true ⸬ □);

require open  Stdlib.Tactic;

symbol MyAll [a] : (τ a → τ o) → 𝕃 a → τ o;
rule MyAll _ □ ↪ ⊤
with MyAll $p ($x ⸬ $l) ↪  ($p $x) ∧ (MyAll $p $l);

symbol bbT (l: 𝕃 o) : π (MyAll (λ x, x = ⊤ ∨ x = ⊥) l) →  BitVec (size l) ≔
begin
    assume l h;
    apply  FinMk (2 ^ size l) (list_Bool_to_nat l);
    simplify;
    generalize l;
    induction
    {simplify; refine λ x, x }
    {
        assume x xs ih;
        simplify;
        assume h;
        have g1: π ((x = ⊤) ∨ (x = ⊥)) { refine ∧ₑ₁ h };
        have g2: π (MyAll (λ x0, (x0 = ⊤) ∨ (x0 = ⊥)) xs) { refine ∧ₑ₂ h };
        remove  h;
        apply ∨ₑ g1
        {
            remove g1;
            assume xisT;
            rewrite xisT;
            remove xisT;
            simplify;
            have g: π (istrue ((list_Bool_to_nat xs +1) ≤ (2 ^ size xs))) { refine ih g2 };
            remove ih; remove g2;
            // have g3: π (istrue (list_Bool_to_nat xs ≤ (_2 ^ size xs))) 
            // { refine leqsnm (list_Bool_to_nat xs) (_2 ^ size xs) g };
            // have go: π (istrue (((list_Bool_to_nat xs) * _2) ≤ ((_2 ^ size xs) * _2)))
            // { refine ∧ₑ₂ (leq_pmul2r 2 (list_Bool_to_nat xs) (_2 ^ size xs) ⊤ᵢ) g3 };
            // remove g3; remove g;
            // have h: π (istrue ((list_Bool_to_nat xs * _2) ≤ ((_2 ^ size xs) + (_2 ^ size xs)))) {
            //     rewrite left n_plus_n_eq_times_2;
            //     refine go;
            // };
            admit
        }
        {
            assume xisF;
            rewrite xisF;
            simplify;
            type ih g2;
            have g: π (istrue ((list_Bool_to_nat xs +1) ≤ (2 ^ size xs))) { refine ih g2 };
            admit
        }
    }
end;

require open Stdlib.Tauto;

symbol rev: Π x: τ o, Π y: τ o, π ((x = y) = (x ⇔ y));

opaque symbol exemple2: π (MyAll (λ x, (x = ⊤) ∨ (x = ⊥)) (⊤ ⸬ (⊥ ⸬ (⊤ ⸬ □)))) ≔
begin
simplify;
eval #repeat (#rewrite rev);
eval tauto;
end;

assert ⊢ bbT (⊤ ⸬ ⊥ ⸬ ⊤ ⸬ □) exemple2 : BitVec 3;

symbol zero_extend [n : ℕ] (k: ℕ) : BitVec n → BitVec (k + n);
rule @zero_extend $n $k $bv ↪ @bvconcat $k $n (bv_fill_zero $k) $bv;

assert ⊢ zero_extend 3 bv1 : BitVec ((bv_size bv1) + 3);

symbol bveq [n : ℕ] : BitVec n → BitVec n → 𝔹 ≔ λ b1 b2,  (eqn (to_nat b1) (to_nat b2));


symbol bvcomp [n : ℕ] : BitVec n → BitVec n → BitVec 1;
rule bvcomp $b1 $b2 ↪ if (bveq $b1 $b2) (FinMk (2  ^ 1) 1 ⊤ᵢ) (FinMk (2  ^ 1) 0 ⊤ᵢ);


symbol last_bit [n: ℕ] : BitVec n → ℕ ≔ begin
    assume n b;
    refine (@bitof n (n - 1) _ b);
    simplify;
    apply leq_subr 1 n;
end;

symbol bvult [n]: BitVec n → BitVec n → Prop ≔ λ b1 b2, istrue((to_nat b1) < (to_nat b2));

symbol bvugt [n]: BitVec n → BitVec n → Prop ≔ λ b1 b2, istrue((to_nat b1) > (to_nat b2));

symbol bvuge [n]: BitVec n → BitVec n → Prop ≔ λ b1 b2, istrue((to_nat b1) ≥ (to_nat b2));

symbol bvule [n]: BitVec n → BitVec n → Prop ≔ λ b1 b2, istrue((to_nat b1) ≤ (to_nat b2));




// Signed result

require open Stdlib.Z;
require open Stdlib.Pos;
require open Stdlib.Comp;

symbol nat_to_int : ℕ → ℤ;
rule nat_to_int _0 ↪ Z0
with nat_to_int ($x +1) ↪ Zpos (of_succ_nat ($x +1));

symbol to_int [n: ℕ] : BitVec n → ℤ;
 
rule @to_int $n $bv ↪ let m ≔ nat_to_int (@to_nat $n $bv) in
                        if (eqn _0 (last_bit $bv)) m (m - 2 ^ nat_to_int $n);

symbol bvslt [n]: BitVec n → BitVec n → Prop ≔ λ b1 b2, (to_int b1) < (to_int b2);

symbol bvsgt [n]: BitVec n → BitVec n → Prop ≔ λ b1 b2, (to_int b1) > (to_int b2);

symbol bvsge [n]: BitVec n → BitVec n → Prop ≔ λ b1 b2, (to_int b1) ≥ (to_int b2);

symbol bvsle [n]: BitVec n → BitVec n → Prop ≔ λ b1 b2, (to_int b1) ≤ (to_int b2);

