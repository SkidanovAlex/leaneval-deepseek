import Submission.Work.GYCorr10
import Submission.Work.GYFactor10
import Submission.Commons.NumberTheory.Sieve.abs_LambdaR_le_log_mul_card
import Submission.Commons.NumberTheory.ZMod.abs_bal_eq_min
import Submission.Commons.NumberTheory.Sieve.prod_rpow_le_sum_pairs
import Submission.Commons.Combinatorics.Finset.sum_pairs_le_of_orderEmb

/-!
# `GYCorr11`: the correlation condition for `ν = nuGT` (Green–Tao §9)

This file assembles the correlation condition (Green–Tao's `mu-cor-con`) from the box average
`boxAvgCorr_ub'` (Green–Tao's Proposition GY2) and the multinomial reduction of `GYCorr10`.

Contents:
* crude `L^∞` bounds for `Λ_R` and hence for `nuBulk`/`nuGT` (needed for the collision case);
* the balanced-representative API;
* the `A = ∅` and `|A| = 1` terms of the multinomial expansion;
* the main `|A| ≥ 2` term (window lift + box average);
* the assembly.
-/

open Finset
open scoped BigOperators

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace GYMaj
namespace Corr

open GYMaj.BoxAvg
open Commons.NumberTheory.Sieve

/-! ## 1. Crude `L^∞` bounds -/

lemma abs_LambdaR_le_log_mul_self {R n : ℕ} (hR : 1 ≤ R) :
    |LambdaR R n| ≤ Real.log (R : ℝ) * (n : ℝ) := by
  have hb := Commons.NumberTheory.Sieve.abs_LambdaR_le_log_mul_card (R := R) (n := n) hR
  have h2 : (n.divisors.filter (fun d => d ≤ R)).card ≤ n.divisors.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have h1 : ((n.divisors.filter (fun d => d ≤ R)).card : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast le_trans h2 (Nat.card_divisors_le_self n)
  have h3 : (0 : ℝ) ≤ Real.log (R : ℝ) := Real.log_nonneg (by exact_mod_cast hR)
  calc |LambdaR R n|
      ≤ Real.log (R : ℝ) * ((n.divisors.filter (fun d => d ≤ R)).card : ℝ) := hb
    _ ≤ Real.log (R : ℝ) * (n : ℝ) := mul_le_mul_of_nonneg_left h1 h3

lemma LambdaR_sq_le {R n : ℕ} (hR : 1 ≤ R) :
    (LambdaR R n) ^ 2 ≤ (Real.log (R : ℝ)) ^ 2 * (n : ℝ) ^ 2 := by
  have h := abs_LambdaR_le_log_mul_self (R := R) (n := n) hR
  have h2 : |LambdaR R n| ^ 2 ≤ (Real.log (R : ℝ) * (n : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h 2
  rwa [sq_abs, mul_pow] at h2

lemma nuBulk_le {R W p : ℕ} [NeZero p] (hR : 1 < R) (hW : 1 ≤ W) (x : ZMod p) :
    nuBulk R W p x ≤ (Nat.totient W : ℝ) * (W : ℝ) * (p : ℝ) ^ 2 * Real.log (R : ℝ) := by
  have hR1 : 1 ≤ R := le_of_lt hR
  have hlog : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast hR)
  have hn : ((W * x.val + 1 : ℕ) : ℝ) ≤ (W : ℝ) * (p : ℝ) := by
    have h1 : W * x.val + 1 ≤ W * p := by
      have h2 : x.val + 1 ≤ p := by have := ZMod.val_lt x; omega
      calc W * x.val + 1 ≤ W * x.val + W := by omega
        _ = W * (x.val + 1) := by ring
        _ ≤ W * p := Nat.mul_le_mul_left _ h2
    exact_mod_cast h1
  have hn0 : (0 : ℝ) ≤ ((W * x.val + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hL : (LambdaR R (W * x.val + 1)) ^ 2
      ≤ (Real.log (R : ℝ)) ^ 2 * ((W : ℝ) * (p : ℝ)) ^ 2 := by
    refine le_trans (LambdaR_sq_le hR1) ?_
    have h2 : (((W * x.val + 1 : ℕ) : ℝ)) ^ 2 ≤ ((W : ℝ) * (p : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hn0 hn 2
    exact mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  have hΛ : (LambdaR R (W * x.val + 1)) ^ 2 / Real.log (R : ℝ)
      ≤ ((W : ℝ) * (p : ℝ)) ^ 2 * Real.log (R : ℝ) := by
    rw [div_le_iff₀ hlog]
    nlinarith [hL, sq_nonneg ((W : ℝ) * (p : ℝ)), hlog]
  rw [nuBulk]
  have hφ0 : (0 : ℝ) ≤ (Nat.totient W : ℝ) / (W : ℝ) := by positivity
  calc (Nat.totient W : ℝ) / (W : ℝ)
        * ((LambdaR R (W * x.val + 1)) ^ 2 / Real.log (R : ℝ))
      ≤ (Nat.totient W : ℝ) / (W : ℝ) * (((W : ℝ) * (p : ℝ)) ^ 2 * Real.log (R : ℝ)) :=
        mul_le_mul_of_nonneg_left hΛ hφ0
    _ = (Nat.totient W : ℝ) * (W : ℝ) * (p : ℝ) ^ 2 * Real.log (R : ℝ) := by
        have hW0 : (W : ℝ) ≠ 0 := by
          have : 0 < W := by omega
          exact_mod_cast Nat.pos_iff_ne_zero.mp this
        field_simp

lemma nuGT_le_bnd {R W p : ℕ} [NeZero p] (hR : 1 < R) (hW : 1 ≤ W) (ε : ℝ) (x : ZMod p) :
    nuGT R W p ε x
      ≤ max (1 : ℝ) ((Nat.totient W : ℝ) * (W : ℝ) * (p : ℝ) ^ 2 * Real.log (R : ℝ)) := by
  by_cases hw : ε * (p : ℝ) ≤ (x.val : ℝ) ∧ (x.val : ℝ) ≤ 2 * ε * (p : ℝ)
  · rw [nuGT, if_pos hw]
    exact le_trans (nuBulk_le hR hW x)
      (le_max_right (1 : ℝ) ((Nat.totient W : ℝ) * (W : ℝ) * (p : ℝ) ^ 2 * Real.log (R : ℝ)))
  · rw [nuGT, if_neg hw]
    exact le_max_left (1 : ℝ) _

/-! ## 2. The balanced representative -/

section Bal

variable {p : ℕ} [NeZero p]

/-- The natural-number `min` of the two windows is the integer `min`. -/
lemma intCast_min_val (z : ZMod p) :
    ((min z.val (p - z.val) : ℕ) : ℤ) = min (z.val : ℤ) ((p : ℤ) - (z.val : ℤ)) := by
  rw [Nat.cast_min, Nat.cast_sub (le_of_lt (ZMod.val_lt z))]

/-- `min z.val (p - z.val) = 0` iff `z = 0`. -/
lemma min_val_eq_zero_iff (z : ZMod p) : min z.val (p - z.val) = 0 ↔ z = 0 := by
  constructor
  · intro h
    rcases Nat.min_eq_zero_iff.mp h with h1 | h1
    · exact ZMod.val_eq_zero z |>.mp h1
    · have := ZMod.val_lt z; omega
  · intro h
    rw [h, ZMod.val_zero, Nat.sub_zero, min_eq_left (Nat.zero_le p)]

/-- If `b : ℤ` represents `z : ZMod p` and `4|b| ≤ p`, then `b` is the balanced representative
of `z`. -/
lemma eq_bal_of_four_mul_abs_le {z : ZMod p} {b : ℤ} (h : (b : ZMod p) = z)
    (hb : 4 * |b| ≤ (p : ℤ)) : b = bal z := by
  have hp : (0 : ℤ) < (p : ℤ) := by exact_mod_cast Nat.pos_of_neZero p
  have hbal : 2 * |bal z| ≤ (p : ℤ) := two_mul_abs_bal_le z
  have hcong : (b : ZMod p) = ((bal z : ℤ) : ZMod p) := by rw [h, bal_cast]
  have hlt : |b| + |bal z| < (p : ℤ) := by linarith
  exact eq_of_abs_add_abs_lt_of_intCast_eq' hcong hlt

/-- **The key identity.**  If `b₁, b₂` are representatives of `z₁, z₂` differing by at most
`p/4`, then their difference is the balanced representative of `z₁ - z₂`, so that

`|b₁ - b₂| = min ((z₁ - z₂).val) (p - (z₁ - z₂).val)`. -/
lemma abs_sub_eq_min_val {z₁ z₂ : ZMod p} {b₁ b₂ : ℤ}
    (h₁ : (b₁ : ZMod p) = z₁) (h₂ : (b₂ : ZMod p) = z₂) (h : 4 * |b₁ - b₂| ≤ (p : ℤ)) :
    (b₁ - b₂).natAbs = min (z₁ - z₂).val (p - (z₁ - z₂).val) := by
  have hp : (0 : ℤ) < (p : ℤ) := by exact_mod_cast Nat.pos_of_neZero p
  have hcong : ((b₁ - b₂ : ℤ) : ZMod p) = z₁ - z₂ := by
    rw [Int.cast_sub, h₁, h₂]
  have hbal := eq_bal_of_four_mul_abs_le hcong h
  rw [hbal]
  have h2 : |bal (z₁ - z₂)| = ((min (z₁ - z₂).val (p - (z₁ - z₂).val) : ℕ) : ℤ) := by
    rw [abs_bal_eq_min, intCast_min_val]
  have h3 : ((bal (z₁ - z₂)).natAbs : ℤ) = ((min (z₁ - z₂).val (p - (z₁ - z₂).val) : ℕ) : ℤ) := by
    rw [Int.natCast_natAbs]; exact h2
  exact_mod_cast h3

end Bal

/-! ## 3. The pair weight and the constants of the correlation bound -/

variable {p : ℕ} [NeZero p]

/-- The pair weight `V(z) = ∏_{q | min z.val (p - z.val)} (1 + q^{-1/2})`. -/
noncomputable def Vw (z : ZMod p) : ℝ :=
  ∏ q ∈ (min z.val (p - z.val)).primeFactors, (1 + (q : ℝ) ^ (-(1 / 2 : ℝ)))

lemma one_le_Vw (z : ZMod p) : 1 ≤ Vw z := by
  rw [Vw]
  exact Finset.one_le_prod (fun q _ => le_add_of_nonneg_right (Real.rpow_nonneg (by positivity) _))

lemma one_le_Vw_pow (z : ZMod p) (n : ℕ) : 1 ≤ (Vw z) ^ n := one_le_pow₀ (one_le_Vw z)

lemma Vw_nonneg (z : ZMod p) : 0 ≤ Vw z := le_trans zero_le_one (one_le_Vw z)

/-- The exponent `E m` attached to the pair weights: large enough for
`prod_rpow_le_sum_pairs` and monotone in `m`. -/
noncomputable def Ec (m : ℕ) : ℕ := ⌈Da m * (m : ℝ) ^ 2⌉₊

lemma Da_mul_sq_le_Ec (m : ℕ) : Da m * (m : ℝ) ^ 2 ≤ (Ec m : ℝ) :=
  Nat.le_ceil _

lemma K0_mono : Monotone K0 := by
  intro a b hab
  unfold K0
  have h4 : (4 : ℝ) ^ a ≤ (4 : ℝ) ^ b := pow_le_pow_right₀ (by norm_num) hab
  have h1 : (1000 : ℝ) ^ a ≤ (1000 : ℝ) ^ b := pow_le_pow_right₀ (by norm_num) hab
  have hb4 : (0 : ℝ) ≤ (4 : ℝ) ^ b := by positivity
  have hb1 : (0 : ℝ) ≤ (1000 : ℝ) ^ b := by positivity
  have hmul : (4 : ℝ) ^ a * (1000 : ℝ) ^ a ≤ (4 : ℝ) ^ b * (1000 : ℝ) ^ b :=
    mul_le_mul h4 h1 (by positivity) hb4
  linarith

lemma Da_mono : Monotone Da := by
  intro a b hab
  have h1 : (2 : ℝ) * (24 : ℝ) ^ a ≤ 2 * (24 : ℝ) ^ b := by
    have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 24) hab
    linarith
  have h2 : 2 * K0 a ≤ 2 * K0 b := by
    have := K0_mono hab; linarith
  exact max_le_max h1 h2

lemma Ec_mono : Monotone Ec := by
  intro a b hab
  apply Nat.ceil_mono
  have h1 : Da a ≤ Da b := Da_mono hab
  have ha : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  have h2 : (a : ℝ) ^ 2 ≤ (b : ℝ) ^ 2 :=
    pow_le_pow_left₀ ha (by exact_mod_cast hab) 2
  have hD : 0 ≤ Da a := Da_nonneg a
  calc Da a * (a : ℝ) ^ 2 ≤ Da b * (b : ℝ) ^ 2 :=
        mul_le_mul h1 h2 (sq_nonneg _) (le_trans hD h1)

/-- The constant multiplying the pair weights, per subset size. -/
noncomputable def Ktil (ε_box εcorr : ℝ) (m : ℕ) : ℝ :=
  1 + ε_box + ∑ a ∈ Finset.range (m + 1), (1 + εcorr) * Kc a

/-- The constant of the correlation weight. -/
noncomputable def Kcorr (ε_box εcorr : ℝ) (m : ℕ) : ℝ := 2 ^ m * Ktil ε_box εcorr m

lemma Kc_nonneg' (a : ℕ) : 0 ≤ Kc a := (Kc_pos a).le

lemma self_le_Ktil (ε_box εcorr : ℝ) (hεb : 0 ≤ ε_box) (hεc : 0 ≤ εcorr) (m a : ℕ)
    (ha : a ≤ m) :
    1 + ε_box + (1 + εcorr) * Kc a ≤ Ktil ε_box εcorr m := by
  rw [Ktil]
  have h1 : a ∈ Finset.range (m + 1) := Finset.mem_range.mpr (by omega)
  have h2 : 0 ≤ (1 + εcorr) * Kc a := by
    have := Kc_nonneg' a; nlinarith
  calc 1 + ε_box + (1 + εcorr) * Kc a
      ≤ 1 + ε_box + ∑ b ∈ Finset.range (m + 1), (1 + εcorr) * Kc b := by
        have := Finset.single_le_sum (f := fun b => (1 + εcorr) * Kc b)
          (fun b _ => by have := Kc_nonneg' b; nlinarith) h1
        linarith
    _ = Ktil ε_box εcorr m := rfl

lemma one_le_Ktil (ε_box εcorr : ℝ) (hεb : 0 ≤ ε_box) (hεc : 0 ≤ εcorr) (m : ℕ) :
    1 ≤ Ktil ε_box εcorr m := by
  rw [Ktil]
  have h1 : 0 ≤ ∑ a ∈ Finset.range (m + 1), (1 + εcorr) * Kc a :=
    Finset.sum_nonneg (fun b _ => by have := Kc_nonneg' b; nlinarith)
  linarith

lemma Ktil_nonneg (ε_box εcorr : ℝ) (hεb : 0 ≤ ε_box) (hεc : 0 ≤ εcorr) (m : ℕ) :
    0 ≤ Ktil ε_box εcorr m := le_trans zero_le_one (one_le_Ktil ε_box εcorr hεb hεc m)

lemma Kcorr_nonneg (ε_box εcorr : ℝ) (hεb : 0 ≤ ε_box) (hεc : 0 ≤ εcorr) (m : ℕ) :
    0 ≤ Kcorr ε_box εcorr m := by
  rw [Kcorr]; exact mul_nonneg (by positivity) (Ktil_nonneg _ _ hεb hεc m)

lemma Ktil_le_Kcorr (ε_box εcorr : ℝ) (hεb : 0 ≤ ε_box) (hεc : 0 ≤ εcorr) (m : ℕ) :
    Ktil ε_box εcorr m ≤ Kcorr ε_box εcorr m := by
  rw [Kcorr]
  have h1 : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  calc Ktil ε_box εcorr m = 1 * Ktil ε_box εcorr m := (one_mul _).symm
    _ ≤ 2 ^ m * Ktil ε_box εcorr m :=
        mul_le_mul_of_nonneg_right h1 (Ktil_nonneg _ _ hεb hεc m)


/-! ## 4. Reindexing tools -/

section Index

variable {m : ℕ}

/-- The increasing enumeration of `A ⊆ Fin m`, as an order embedding. -/
noncomputable def eEmb (A : Finset (Fin m)) : Fin A.card ↪o Fin m :=
  Finset.orderEmbOfFin A (rfl : A.card = A.card)

/-- The `k`-th smallest element of `A ⊆ Fin m`. -/
noncomputable def eFin (A : Finset (Fin m)) (k : Fin A.card) : Fin m := eEmb A k

lemma eFin_strictMono (A : Finset (Fin m)) : StrictMono (eFin A) := (eEmb A).strictMono

lemma eFin_lt {A : Finset (Fin m)} {k k' : Fin A.card} (h : k < k') : eFin A k < eFin A k' :=
  eFin_strictMono A h

lemma eFin_mem (A : Finset (Fin m)) (k : Fin A.card) : eFin A k ∈ A :=
  Finset.orderEmbOfFin_mem A (rfl : A.card = A.card) k

lemma eFin_injective (A : Finset (Fin m)) : Function.Injective (eFin A) :=
  (eEmb A).injective

lemma eFin_surj (A : Finset (Fin m)) : ∀ i ∈ A, ∃ k : Fin A.card, eFin A k = i := by
  intro i hi
  have hrange : i ∈ Set.range (eFin A) := by
    have h := Finset.range_orderEmbOfFin A (rfl : A.card = A.card)
    exact h ▸ hi
  obtain ⟨k, hk⟩ := hrange
  exact ⟨k, hk⟩

lemma prod_eFin (A : Finset (Fin m)) (f : Fin m → ℝ) :
    ∏ i ∈ A, f i = ∏ k : Fin A.card, f (eFin A k) := by
  have h1 : ∏ i ∈ A, f i = ∏ x : ↥A, f x.val := by
    rw [← Finset.prod_attach A (fun i => f i), ← Finset.univ_eq_attach A]
  rw [h1]
  refine Fintype.prod_equiv ((Finset.orderIsoOfFin A (rfl : A.card = A.card)).symm :
      ↥A ≃ Fin A.card) (fun x : ↥A => f x.val) (fun k : Fin A.card => f (eFin A k))
    (fun x => ?_)
  congr 1
  rw [eFin, eEmb, ← Finset.coe_orderIsoOfFin_apply]
  simp

end Index

section Sums

variable {p : ℕ} [NeZero p]

/-- Sums over `ZMod p` are sums over `Fin p` through the representatives. -/
lemma sum_zmod_eq_sum_fin (F : ZMod p → ℝ) :
    ∑ x : ZMod p, F x = ∑ t : Fin p, F (t : ZMod p) :=
  (Fintype.sum_bijective (fun t : Fin p => (t : ZMod p))
    ⟨fun a b h => by
      have h2 := congrArg ZMod.val h
      have h' : (a : ℕ) = (b : ℕ) := by
        simpa only [ZMod.val_natCast_of_lt a.isLt, ZMod.val_natCast_of_lt b.isLt] using h2
      exact Fin.ext h',
     fun x => ⟨⟨x.val, ZMod.val_lt x⟩, ZMod.natCast_zmod_val x⟩⟩
    (fun t : Fin p => F (t : ZMod p)) F (fun _ => rfl)).symm

/-- Translation invariance of the sum over `ZMod p`. -/
lemma sum_zmod_add_right (F : ZMod p → ℝ) (a : ZMod p) :
    ∑ x : ZMod p, F (x + a) = ∑ x : ZMod p, F x :=
  Fintype.sum_equiv (Equiv.addRight a) (fun x => F (x + a)) F (fun _ => rfl)

/-- A sum over `Fintype.piFinset` for `Fin 1` is a sum over `s 0`. -/
lemma sum_piFinset_fin_one {s : Fin 1 → Finset ℤ} (F : (Fin 1 → ℤ) → ℝ) :
    ∑ x ∈ Fintype.piFinset s, F x = ∑ n ∈ s 0, F (fun _ => n) := by
  refine Finset.sum_bij (fun x _ => x 0) ?_ ?_ ?_ ?_
  · intro x hx
    have := (Fintype.mem_piFinset.mp hx) 0
    simpa using this
  · intro x₁ hx₁ x₂ hx₂ h
    funext j
    fin_cases j
    exact h
  · intro n hn
    refine ⟨fun _ => n, ?_, rfl⟩
    rw [Fintype.mem_piFinset]
    intro j
    have hj : j = 0 := Subsingleton.elim j 0
    rw [hj]
    simpa using hn
  · intro x hx
    congr 1
    funext j
    fin_cases j
    rfl

end Sums

/-! ## 5. The `A`-term of the multinomial expansion -/

section ATerm

variable {m : ℕ} {p : ℕ} [NeZero p]

/-- The window condition on `A` at `x`. -/
def InWin (h : Fin m → ZMod p) (A : Finset (Fin m)) (ε : ℝ) (x : ZMod p) : Prop :=
  ∀ i ∈ A, ε * (p : ℝ) ≤ ((x + h i).val : ℝ) ∧ ((x + h i).val : ℝ) ≤ 2 * ε * (p : ℝ)

/-- The shift vector of the correlation system relative to `i₀`. -/
noncomputable def dsh (h : Fin m → ZMod p) (i₀ : Fin m) (i : Fin m) : ℤ := bal (h i - h i₀)

lemma dsh_self (h : Fin m → ZMod p) (i₀ : Fin m) : dsh h i₀ i₀ = 0 := by
  simp [dsh, bal]

lemma dsh_cast (h : Fin m → ZMod p) (i₀ i : Fin m) :
    ((dsh h i₀ i : ℤ) : ZMod p) = h i - h i₀ := by
  rw [dsh]; exact bal_cast _

/-- `Int.toNat (W n + 1) = W n + 1` for `n : ℕ`. -/
lemma intToNat_mul_add_one (W n : ℕ) : Int.toNat ((W : ℤ) * (n : ℤ) + 1) = W * n + 1 := by
  have h : ((W : ℤ) * (n : ℤ) + 1) = ((W * n + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, Int.toNat_natCast]

/-- Reindexing a product over `A` by `Finset.equivFin`. -/
theorem prod_eFin_shift (A : Finset (Fin m)) (R W : ℕ) (t : ℤ) (d : Fin m → ℤ) :
    ∏ i ∈ A, ((LambdaR R (Int.toNat ((W : ℤ) * (t + d i) + 1))) ^ 2)
      = ∏ k : Fin A.card,
          ((LambdaR R (Int.toNat ((W : ℤ) * (t + d (eFin A k)) + 1))) ^ 2) :=
  prod_eFin A (fun i => ((LambdaR R (Int.toNat ((W : ℤ) * (t + d i) + 1))) ^ 2))

/-- The window lift for the shift vector. -/
lemma val_eq_of_win {h : Fin m → ZMod p} {A : Finset (Fin m)} {i₀ : Fin m} {ε : ℝ}
    (hε0 : 0 < ε) (hε4 : 4 * ε ≤ 1) (hi₀ : i₀ ∈ A) {x : ZMod p} (hw : InWin h A ε x) :
    ∀ i ∈ A, (((x + h i).val : ℤ)) = (((x + h i₀).val : ℤ)) + dsh h i₀ i :=
  fun i hi => val_add_eq_of_window (p := p) hε0 hε4 hi₀ (fun i hi => (hw i hi).1)
    (fun i hi => (hw i hi).2) hi

/-- Off the window at least one factor vanishes. -/
lemma prod_gGT_eq_zero_of_not_win {h : Fin m → ZMod p} {A : Finset (Fin m)} {ε : ℝ}
    {x : ZMod p} {R W : ℕ} (hn : ¬ InWin h A ε x) :
    ∏ i ∈ A, gGT R W p ε (x + h i) = 0 := by
  by_contra hne
  have hne' : ∏ i ∈ A, gGT R W p ε (x + h i) ≠ 0 := hne
  rw [Finset.prod_ne_zero_iff] at hne'
  exact hn (fun i hi => by
    by_contra hc
    exact hne' i hi (by rw [gGT, if_neg hc]))

/-- **The pointwise bound** for a fixed `x`. -/
lemma gGT_prod_le_of_win {h : Fin m → ZMod p} {A : Finset (Fin m)} {i₀ : Fin m} (hi₀ : i₀ ∈ A)
    {ε : ℝ} (hε0 : 0 < ε) (hε4 : 4 * ε ≤ 1) {R W : ℕ} {x : ZMod p}
    (hw : InWin h A ε x) :
    ∏ i ∈ A, gGT R W p ε (x + h i)
      = ((Nat.totient W : ℝ) / (W : ℝ) / Real.log (R : ℝ)) ^ A.card *
        ∏ i ∈ A, ((LambdaR R (Int.toNat ((W : ℤ) * (((x + h i₀).val : ℤ) + dsh h i₀ i) + 1))) ^ 2) := by
  have hlift := val_eq_of_win (A := A) hε0 hε4 hi₀ hw
  have hstep : ∀ i ∈ A, gGT R W p ε (x + h i)
      = ((Nat.totient W : ℝ) / (W : ℝ) / Real.log (R : ℝ))
        * ((LambdaR R (Int.toNat ((W : ℤ) * (((x + h i₀).val : ℤ) + dsh h i₀ i) + 1))) ^ 2) := by
    intro i hi
    rw [gGT, if_pos (hw i hi), nuBulk]
    have harg : Int.toNat ((W : ℤ) * (((x + h i₀).val : ℤ) + dsh h i₀ i) + 1)
        = W * (x + h i).val + 1 := by
      rw [← hlift i hi, intToNat_mul_add_one]
    rw [harg]
    ring
  rw [Finset.prod_congr rfl hstep, Finset.prod_mul_distrib, Finset.prod_const]

end ATerm

/-! ## 6. From the `Fin p`-sum to the box sum -/

section Box

variable {m : ℕ} {p : ℕ} [NeZero p]

/-- The support of the `A`-term lies in the box `[l, l+p)`, where `l = 1 - m₁` and `m₁` is the
minimum of the shift vector over `A`. -/
lemma mem_box_of_win {h : Fin m → ZMod p} {A : Finset (Fin m)} {i₀ : Fin m} (hi₀ : i₀ ∈ A)
    {ε : ℝ} (hε0 : 0 < ε) (hε4 : 4 * ε ≤ 1) (hεp1 : 1 ≤ ε * (p : ℝ)) {l r : Fin 1 → ℤ}
    {m₁ : ℤ} (hm₁' : ∃ i ∈ A, dsh h i₀ i = m₁)
    (hl : l 0 = 1 - m₁) (hr : r 0 = l 0 + p) {t : Fin p}
    (hw : InWin h A ε ((t : ZMod p) - h i₀)) :
    l 0 ≤ (t.val : ℤ) ∧ (t.val : ℤ) < r 0 := by
  have hε2 : 2 * ε ≤ 1 := by linarith
  obtain ⟨i₁, hi₁, hi₁eq⟩ := hm₁'
  have hbal : bal (h i₁ - h i₀) = m₁ := by simpa only [dsh] using hi₁eq
  have hval₀ : ((((t : ZMod p) - h i₀) + h i₀).val : ℕ) = t.val := by
    rw [sub_add_cancel, ZMod.val_natCast_of_lt t.isLt]
  have hlift₁ := val_add_eq_of_window (p := p) hε0 hε4 hi₀
    (fun i hi => (hw i hi).1) (fun i hi => (hw i hi).2) hi₁
  rw [hval₀, hbal] at hlift₁
  -- lower bound
  have hlow : (1 : ℤ) ≤ (t.val : ℤ) + m₁ := by
    have h1 : (1 : ℝ) ≤ ((((t : ZMod p) - h i₀) + h i₁).val : ℝ) :=
      le_trans hεp1 (hw i₁ hi₁).1
    have h2 : (1 : ℤ) ≤ ((((t : ZMod p) - h i₀) + h i₁).val : ℤ) := by exact_mod_cast h1
    rwa [hlift₁] at h2
  -- upper bound
  have hfloor : ⌊2 * ε * (p : ℝ)⌋ ≤ (p : ℤ) := by
    have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
    have h2εp : 2 * ε * (p : ℝ) ≤ (p : ℝ) := by nlinarith
    calc ⌊2 * ε * (p : ℝ)⌋ ≤ ⌊(p : ℝ)⌋ := Int.floor_mono h2εp
      _ = (p : ℤ) := Int.floor_natCast p
  have hup : (t.val : ℤ) + m₁ ≤ (p : ℤ) := by
    have h1 : ((((t : ZMod p) - h i₀) + h i₁).val : ℤ) ≤ ⌊2 * ε * (p : ℝ)⌋ := by
      refine Int.le_floor.mpr ?_
      push_cast
      exact (hw i₁ hi₁).2
    rw [hlift₁] at h1
    linarith
  exact ⟨by rw [hl]; linarith, by rw [hr, hl]; linarith⟩

/-- **The `Fin p`-sum of the `A`-term is bounded by the box sum.** -/
lemma gsum_le_boxsum {h : Fin m → ZMod p} {A : Finset (Fin m)} {i₀ : Fin m} (hi₀ : i₀ ∈ A)
    {ε : ℝ} (hε0 : 0 < ε) (hε4 : 4 * ε ≤ 1) (hεp1 : 1 ≤ ε * (p : ℝ)) {R W : ℕ}
    {l r : Fin 1 → ℤ} {m₁ : ℤ} (hm₁' : ∃ i ∈ A, dsh h i₀ i = m₁)
    (hl : l 0 = 1 - m₁) (hr : r 0 = l 0 + p) :
    ∑ t : Fin p, ∏ i ∈ A, gGT R W p ε (((t : ZMod p) - h i₀) + h i)
      ≤ ((Nat.totient W : ℝ) / (W : ℝ) / Real.log (R : ℝ)) ^ A.card *
          boxSum R W (Ac A.card) (fun k => dsh h i₀ (eFin A k)) l r := by
  classical
  set S : Finset (Fin p) := Finset.univ.filter
    (fun t => InWin h A ε ((t : ZMod p) - h i₀)) with hS
  set c : ℝ := ((Nat.totient W : ℝ) / (W : ℝ) / Real.log (R : ℝ)) ^ A.card with hc
  set G : ℤ → ℝ := fun n => ∏ k : Fin A.card,
    ((LambdaR R (Int.toNat ((W : ℤ) * (n + dsh h i₀ (eFin A k)) + 1))) ^ 2) with hG
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hGnn : ∀ n : ℤ, 0 ≤ G n := by
    intro n
    rw [hG]
    exact Finset.prod_nonneg (fun k _ => sq_nonneg _)
  have hrestrict : ∑ t : Fin p, ∏ i ∈ A, gGT R W p ε (((t : ZMod p) - h i₀) + h i)
      = ∑ t ∈ S, ∏ i ∈ A, gGT R W p ε (((t : ZMod p) - h i₀) + h i) :=
    (Finset.sum_subset (Finset.subset_univ S) (fun t _ ht =>
      prod_gGT_eq_zero_of_not_win (R := R) (W := W) (by simpa [hS] using ht))).symm
  rw [hrestrict]
  have hon : ∀ t ∈ S, ∏ i ∈ A, gGT R W p ε (((t : ZMod p) - h i₀) + h i) ≤ c * G (t.val : ℤ) := by
    intro t ht
    have hw : InWin h A ε ((t : ZMod p) - h i₀) := by simpa [hS] using ht
    have hval : ((((t : ZMod p) - h i₀) + h i₀).val : ℕ) = t.val := by
      rw [sub_add_cancel, ZMod.val_natCast_of_lt t.isLt]
    rw [gGT_prod_le_of_win (p := p) hi₀ hε0 hε4 hw, hc, hval,
      prod_eFin_shift A R W (t.val : ℤ) (dsh h i₀), hG]
  calc ∑ t ∈ S, ∏ i ∈ A, gGT R W p ε (((t : ZMod p) - h i₀) + h i)
      ≤ ∑ t ∈ S, c * G (t.val : ℤ) := Finset.sum_le_sum hon
    _ = c * ∑ t ∈ S, G (t.val : ℤ) := (Finset.mul_sum S (fun t => G (t.val : ℤ)) c).symm
    _ ≤ c * ∑ n ∈ Finset.Ico (l 0) (r 0), G n := by
        refine mul_le_mul_of_nonneg_left ?_ hc0
        have hinj : Set.InjOn (fun t : Fin p => (t.val : ℤ)) (↑S) := by
          intro a _ b _ hab
          have h2 : (a.val : ℤ) = (b.val : ℤ) := hab
          have hh : a.val = b.val := by exact_mod_cast h2
          exact Fin.ext hh
        rw [← Finset.sum_image (f := fun n : ℤ => G n)
          (s := S) (g := fun t : Fin p => (t.val : ℤ)) hinj]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => hGnn n)
        rw [Finset.image_subset_iff]
        intro t ht
        exact Finset.mem_Ico.mpr (mem_box_of_win (p := p) hi₀ hε0 hε4 hεp1 hm₁' hl hr
          (by simpa [hS] using ht))
    _ = c * boxSum R W (Ac A.card) (fun k => dsh h i₀ (eFin A k)) l r := by
        congr 1
        rw [boxSum, BoxAvg.box, sum_piFinset_fin_one]
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [hG]
        refine Finset.prod_congr rfl (fun k _ => ?_)
        rw [theta_eq]

end Box

/-! ## 7. The pair-sum bound and the distribution of `LamD` -/

section Dist

variable {m : ℕ} {p : ℕ} [NeZero p]

/-- The correlation pair sum. -/
noncomputable def Pw (h : Fin m → ZMod p) (E : ℕ) : ℝ :=
  ∑ i : Fin m, ∑ j ∈ Finset.univ.filter (fun j : Fin m => i < j), (Vw (h i - h j)) ^ E

lemma one_le_Pw {m : ℕ} (hm : 2 ≤ m) (h : Fin m → ZMod p) (E : ℕ) : 1 ≤ Pw h E := by
  classical
  set i₀ : Fin m := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin m := ⟨1, by omega⟩ with hi₁
  have hlt : i₀ < i₁ := by simp [hi₀, hi₁, Fin.lt_def]
  have hmem : i₁ ∈ Finset.univ.filter (fun j : Fin m => i₀ < j) := by simp [hlt]
  have hnn : ∀ j ∈ Finset.univ.filter (fun j : Fin m => i₀ < j), 0 ≤ (Vw (h i₀ - h j)) ^ E :=
    fun j _ => pow_nonneg (Vw_nonneg _) E
  have h1 := Finset.single_le_sum hnn hmem
  have h2 : 1 ≤ (Vw (h i₀ - h i₁)) ^ E := one_le_pow₀ (one_le_Vw _)
  have h3 : (∑ j ∈ Finset.univ.filter (fun j : Fin m => i₀ < j), (Vw (h i₀ - h j)) ^ E)
      ≤ Pw h E := Finset.single_le_sum
        (f := fun i : Fin m => ∑ j ∈ Finset.univ.filter (fun j : Fin m => i < j),
          (Vw (h i - h j)) ^ E)
        (fun i _ => Finset.sum_nonneg (fun j _ => pow_nonneg (Vw_nonneg _) E))
        (Finset.mem_univ i₀)
  linarith

lemma RHS_nonneg (h : Fin m → ZMod p) (E : ℕ) : 0 ≤ Pw h E :=
  Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => pow_nonneg (Vw_nonneg _) E))

/-- **The identity of the shifts on the window.**  If the whole system `x ↦ x + h i` (`i ∈ A`) is
in the window at some `x`, then the differences of the shift vector are the balanced
representatives of the differences of `h`. -/
lemma abs_sub_dsh_eq {h : Fin m → ZMod p} {A : Finset (Fin m)} {i₀ : Fin m} (hi₀ : i₀ ∈ A)
    {ε : ℝ} (hε0 : 0 < ε) (hε4 : 4 * ε ≤ 1) {x : ZMod p} (hw : InWin h A ε x)
    {i j : Fin m} (hi : i ∈ A) (hj : j ∈ A) :
    (dsh h i₀ i - dsh h i₀ j).natAbs = min ((h i - h j).val) (p - (h i - h j).val) := by
  have hli := val_add_eq_of_window (p := p) hε0 hε4 hi₀ (fun i hi => (hw i hi).1)
    (fun i hi => (hw i hi).2) hi
  have hlj := val_add_eq_of_window (p := p) hε0 hε4 hi₀ (fun i hi => (hw i hi).1)
    (fun i hi => (hw i hi).2) hj
  have hsub : dsh h i₀ i - dsh h i₀ j
      = (((x + h i).val : ℤ)) - (((x + h j).val : ℤ)) := by
    rw [dsh, dsh, hli, hlj]; ring
  have hcast₁ : ((((x + h i).val : ℤ)) : ZMod p) = x + h i := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hcast₂ : ((((x + h j).val : ℤ)) : ZMod p) = x + h j := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have h5 : 4 * |(((x + h i).val : ℤ)) - (((x + h j).val : ℤ))| ≤ (p : ℤ) := by
    have h1 : ((x + h i).val : ℝ) - ((x + h j).val : ℝ) ≤ ε * (p : ℝ) := by
      linarith [(hw i hi).2, (hw j hj).1]
    have h2 : -(ε * (p : ℝ)) ≤ ((x + h i).val : ℝ) - ((x + h j).val : ℝ) := by
      linarith [(hw i hi).1, (hw j hj).2]
    have h3 : |((x + h i).val : ℝ) - ((x + h j).val : ℝ)| ≤ ε * (p : ℝ) :=
      abs_le.mpr ⟨h2, h1⟩
    have habs : ((|(((x + h i).val : ℤ)) - (((x + h j).val : ℤ))| : ℤ) : ℝ)
        = |((x + h i).val : ℝ) - ((x + h j).val : ℝ)| := by
      push_cast
      ring
    have h4 : 4 * ((|(((x + h i).val : ℤ)) - (((x + h j).val : ℤ))| : ℤ) : ℝ) ≤ (p : ℝ) := by
      rw [habs]
      have h4a : (4 : ℝ) * |((x + h i).val : ℝ) - ((x + h j).val : ℝ)|
          ≤ 4 * (ε * (p : ℝ)) := mul_le_mul_of_nonneg_left h3 (by norm_num : (0 : ℝ) ≤ 4)
      have h4b : (4 : ℝ) * (ε * (p : ℝ)) ≤ (p : ℝ) := by
        have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
        nlinarith [hε4, hp0]
      linarith
    exact_mod_cast h4
  have hz : x + h i - (x + h j) = h i - h j := by abel
  have hmain := abs_sub_eq_min_val (z₁ := x + h i) (z₂ := x + h j)
    (b₁ := ((x + h i).val : ℤ)) (b₂ := ((x + h j).val : ℤ)) hcast₁ hcast₂ h5
  rw [hsub, hmain, hz]

/-- **The distribution of `LamD` over the pairs.** -/
lemma LamD_le_sum_Vw {a : ℕ} {δ : Fin a → ℤ} {z : Fin a → ZMod p}
    (ha : 2 ≤ a) (hinj : Function.Injective δ)
    (hident : ∀ k k', (δ k - δ k').natAbs = min ((z k - z k').val) (p - (z k - z k').val)) :
    LamD a δ ≤ ∑ k : Fin a, ∑ k' ∈ Finset.univ.filter (fun k' : Fin a => k < k'),
        (Vw (z k - z k')) ^ (Ec a) := by
  classical
  have hDa1 : (1 : ℝ) ≤ Da a := by
    rw [Da]
    have h1 : (1 : ℝ) ≤ (24 : ℝ) ^ a := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 24)
    exact le_trans (by linarith : (1 : ℝ) ≤ 2 * (24 : ℝ) ^ a) (le_max_left _ _)
  have hE : Da a * (a : ℝ) ^ 2 ≤ ((Ec a : ℕ) : ℝ) := Da_mul_sq_le_Ec a
  have hd : ∀ i j : Fin a, 1 ≤ max 1 ((δ i - δ j).natAbs) := fun i j => le_max_left _ _
  have hkey := prod_rpow_le_sum_pairs (n := a) ha (C := Da a) (E := ((Ec a : ℕ) : ℝ)) hDa1 hE
    (fun i j => max 1 ((δ i - δ j).natAbs)) hd
  -- identify the left-hand side with `LamD a δ`
  have hprod : (∏ i : Fin a, ∏ j ∈ Finset.univ.filter (fun j : Fin a => i < j),
        max 1 ((δ i - δ j).natAbs)) = Delta δ := by
    rw [Delta]
    refine Finset.prod_congr rfl (fun i _ => Finset.prod_congr rfl (fun j hj => ?_))
    rw [Finset.mem_filter] at hj
    have hne : i ≠ j := ne_of_lt hj.2
    have h1 : 1 ≤ (δ i - δ j).natAbs := by
      rcases Nat.eq_zero_or_pos ((δ i - δ j).natAbs) with h0 | h
      · exact absurd h0 (by simp [sub_ne_zero.mpr (fun hc => hne (hinj hc))])
      · exact h
    rw [max_eq_right h1]
  have hLamD : LamD a δ = (∏ q ∈ (∏ i : Fin a, ∏ j ∈ Finset.univ.filter (fun j : Fin a => i < j),
        max 1 ((δ i - δ j).natAbs)).primeFactors, (1 + (q : ℝ) ^ (-(1 / 2 : ℝ)))) ^ (Da a) := by
    rw [LamD, hprod, Real.finsetProd_rpow]
    refine fun q _ => ?_
    have := Real.rpow_nonneg (Nat.cast_nonneg q) (-(1 / 2 : ℝ))
    linarith
  rw [hLamD]
  refine le_trans hkey ?_
  -- replace the weight on each term
  refine Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun k' hk' => ?_))
  rw [Finset.mem_filter] at hk'
  have hne : k ≠ k' := ne_of_lt hk'.2
  have hid := hident k k'
  have hpos : 1 ≤ min ((z k - z k').val) (p - (z k - z k').val) := by
    rw [← hid]
    rcases Nat.eq_zero_or_pos ((δ k - δ k').natAbs) with h0 | h
    · exact absurd h0 (by simp [sub_ne_zero.mpr (fun hc => hne (hinj hc))])
    · exact h
  have hmax : max 1 ((δ k - δ k').natAbs)
      = min ((z k - z k').val) (p - (z k - z k').val) := by
    rw [max_eq_right]
    · exact hid
    · rw [hid]; exact hpos
  rw [hmax, Vw, Real.rpow_natCast]

end Dist


/-! ## 8. The multinomial assembly -/

section Main

variable {m : ℕ} {k R W p : ℕ} [NeZero p] {εw ε_box εcorr : ℝ}

/-- Reindexing the `ZMod p`-sum by the translation `x ↦ x + h i₀` and the representatives. -/
lemma sum_reindex_gGT {A : Finset (Fin m)} (h : Fin m → ZMod p) (i₀ : Fin m) :
    ∑ x : ZMod p, ∏ i ∈ A, gGT R W p εw (x + h i)
      = ∑ t : Fin p, ∏ i ∈ A, gGT R W p εw (((t : ZMod p) - h i₀) + h i) := by
  set F : ZMod p → ℝ := fun y => ∏ i ∈ A, gGT R W p εw (y + h i) with hF
  have h2 : ∑ y : ZMod p, F y = ∑ y : ZMod p, F (y - h i₀) :=
    (Fintype.sum_equiv (Equiv.subRight (h i₀)) (fun y : ZMod p => F (y - h i₀)) F
      (fun _ => rfl)).symm
  rw [h2, sum_zmod_eq_sum_fin (fun y : ZMod p => F (y - h i₀))]

end Main


/-! ## 9. The `A`-term bound -/

section ATermBound

variable {m : ℕ} {k R W p : ℕ} [NeZero p] {εw ε_box εcorr : ℝ}

/-- **The `A`-term bound** of the correlation condition: for a non-empty `A ⊆ Fin m` of size at
most `k·2^{k-1}`, the average of `∏_{i∈A} g(x+h_i)` is at most `Ktil ·` (the pair sum). -/
theorem gTerm_le {A : Finset (Fin m)} (hAne : A.Nonempty) (hAcard : A.card ≤ k * 2 ^ (k - 1))
    {h : Fin m → ZMod p} (hinj : Function.Injective h)
    (hk : 1 ≤ k) (hR : 3 ≤ R) (hRk : 3 * k ≤ R) (hW : 1 ≤ W)
    (hεbox : 0 ≤ ε_box) (hεcorr : 0 < εcorr) (hεw : 0 < εw) (hεw4 : 4 * εw ≤ 1)
    (hεp1 : 1 ≤ εw * (p : ℝ)) (hm2 : 2 ≤ m)
    (hsmallEr : 6 * (3 * (k : ℝ)) * (Real.log (R : ℝ)) ^ (k * 2 ^ (k - 1))
      ≤ εcorr * (R : ℝ) ^ 6)
    (hsmallMn : ∀ a : ℕ, 1 ≤ a → a ≤ k * 2 ^ (k - 1) →
      4 * ((zbC a) ^ a * (EK a * stripBound W a)) ≤ (εcorr / 2) * Real.log (R : ℝ) * Kc a)
    (hside : (R : ℤ) ^ (10 * A.card) ≤ (p : ℤ)) :
    (p : ℝ)⁻¹ * ∑ x : ZMod p, ∏ i ∈ A, gGT R W p εw (x + h i)
      ≤ Ktil ε_box εcorr m * Pw h (Ec m) := by
  classical
  obtain ⟨i₀, hi₀⟩ := hAne
  have hεc0 : 0 ≤ εcorr := le_of_lt hεcorr
  have hlogR : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < R))
  have hcardm : A.card ≤ m := by
    have := Finset.card_le_univ A
    simpa using this
  have honeK : (1 : ℝ) ≤ Ktil ε_box εcorr m := one_le_Ktil ε_box εcorr hεbox hεc0 m
  have hK0 : 0 ≤ Ktil ε_box εcorr m := Ktil_nonneg ε_box εcorr hεbox hεc0 m
  have hP1 : 1 ≤ Pw h (Ec m) := one_le_Pw hm2 h (Ec m)
  have hP0 : 0 ≤ Pw h (Ec m) := le_trans zero_le_one hP1
  by_cases hsupp : ∃ x : ZMod p, InWin h A εw x
  · obtain ⟨x₀, hx₀⟩ := hsupp
    have hident : ∀ k k' : Fin A.card,
        (dsh h i₀ (eFin A k) - dsh h i₀ (eFin A k')).natAbs
          = min ((h (eFin A k) - h (eFin A k')).val)
              (p - (h (eFin A k) - h (eFin A k')).val) :=
      fun k k' => abs_sub_dsh_eq (p := p) hi₀ hεw hεw4 hx₀ (eFin_mem A k) (eFin_mem A k')
    -- the minimum of the shift vector
    set m₁ : ℤ := (A.image (dsh h i₀)).min' (Finset.image_nonempty.mpr ⟨i₀, hi₀⟩) with hm₁def
    have hm₁le : ∀ i ∈ A, m₁ ≤ dsh h i₀ i := by
      intro i hi
      rw [hm₁def]
      exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    have hm₁mem : ∃ i ∈ A, dsh h i₀ i = m₁ := by
      rw [hm₁def]
      obtain ⟨v, hv, hveq⟩ := Finset.mem_image.mp
        (Finset.min'_mem (A.image (dsh h i₀)) (Finset.image_nonempty.mpr ⟨i₀, hi₀⟩))
      exact ⟨v, hv, hveq⟩
    -- injectivity of the shift vector
    have hδ'inj : Function.Injective (fun k : Fin A.card => dsh h i₀ (eFin A k)) := by
      intro k k' hkk
      have hkk' : dsh h i₀ (eFin A k) = dsh h i₀ (eFin A k') := hkk
      have h1 : ((dsh h i₀ (eFin A k) - dsh h i₀ (eFin A k') : ℤ) : ZMod p) = 0 := by
        rw [Int.cast_sub, hkk', sub_self]
      rw [Int.cast_sub, dsh_cast, dsh_cast] at h1
      have h5 : h (eFin A k) - h i₀ + h i₀ = h (eFin A k') - h i₀ + h i₀ := by
        rw [sub_eq_zero.mp h1]
      exact eFin_injective A (hinj (by simpa using h5))
    -- the box data
    have hboxD : CorrBoxData k R W A.card (fun k => dsh h i₀ (eFin A k))
        (fun _ : Fin 1 => 1 - m₁) (fun _ : Fin 1 => 1 - m₁ + p) := by
      have hc0 : 1 ≤ A.card := Finset.card_pos.mpr ⟨i₀, hi₀⟩
      refine ⟨hc0, hAcard, ?_, ?_, ?_⟩
      · intro j
        fin_cases j
        have hcomp : (1 - m₁ + (p : ℤ)) - (1 - m₁) = (p : ℤ) := by ring
        rw [hcomp]
        exact hside
      · intro x hx i
        rw [mem_box] at hx
        rw [theta_eq]
        have hx0 : (1 - m₁) ≤ x 0 := (hx 0).1
        have hδi : m₁ ≤ dsh h i₀ (eFin A i) := hm₁le _ (eFin_mem A i)
        have h1 : (1 : ℤ) ≤ x 0 + dsh h i₀ (eFin A i) := by linarith
        have hW0 : (0 : ℤ) ≤ (W : ℤ) := Int.natCast_nonneg W
        have h2 : (0 : ℤ) ≤ x 0 + dsh h i₀ (eFin A i) := le_trans (by norm_num) h1
        have := mul_nonneg hW0 h2
        linarith
      · have h1 : 1 ≤ Delta (fun k : Fin A.card => dsh h i₀ (eFin A k)) := by
          rw [Delta]
          refine Finset.one_le_prod (fun i _ => ?_)
          refine Finset.one_le_prod (fun j hj => ?_)
          rw [Finset.mem_filter] at hj
          have hne : (fun k : Fin A.card => dsh h i₀ (eFin A k)) i
              ≠ (fun k : Fin A.card => dsh h i₀ (eFin A k)) j :=
            fun hc => absurd (hδ'inj hc) (ne_of_lt hj.2)
          rcases Nat.eq_zero_or_pos (((fun k : Fin A.card => dsh h i₀ (eFin A k)) i
              - (fun k : Fin A.card => dsh h i₀ (eFin A k)) j).natAbs) with h0 | h
          · exact absurd h0 (by simp [sub_ne_zero.mpr hne])
          · exact h
        omega
    have hbu := boxAvgCorr_ub' k R W εcorr hk hR hRk hW hεcorr hsmallEr hsmallMn
      A.card (fun k => dsh h i₀ (eFin A k)) (fun _ : Fin 1 => 1 - m₁)
      (fun _ : Fin 1 => 1 - m₁ + p) hboxD
    have hsp : sideProd (fun _ : Fin 1 => 1 - m₁) (fun _ : Fin 1 => 1 - m₁ + p) = (p : ℝ) := by
      rw [sideProd, Fin.prod_univ_one]
      have hcomp : (1 - m₁ + (p : ℤ)) - (1 - m₁) = (p : ℤ) := by ring
      rw [hcomp]
      simp
    have hbu' : (p : ℝ)⁻¹ * boxSum R W (Ac A.card) (fun k => dsh h i₀ (eFin A k))
        (fun _ : Fin 1 => 1 - m₁) (fun _ : Fin 1 => 1 - m₁ + p)
        ≤ (1 + εcorr) * ((W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ)) ^ A.card
            * (Kc A.card * LamD A.card (fun k => dsh h i₀ (eFin A k))) := by
      rw [← hsp]
      exact hbu
    -- the identification `c · P^a = 1`
    have hφpos : (0 : ℝ) < (Nat.totient W : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (by omega))
    have hWpos : (0 : ℝ) < (W : ℝ) := by exact_mod_cast (by omega : 0 < W)
    have hcP : ((Nat.totient W : ℝ) / (W : ℝ) / Real.log (R : ℝ)) ^ A.card
        * ((W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ)) ^ A.card = 1 := by
      rw [← mul_pow]
      have h1 : (Nat.totient W : ℝ) / (W : ℝ) / Real.log (R : ℝ)
          * ((W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ)) = 1 := by
        field_simp
      rw [h1, one_pow]
    -- the distribution
    have hfinal : (1 + εcorr) * (Kc A.card * LamD A.card (fun k => dsh h i₀ (eFin A k)))
        ≤ Ktil ε_box εcorr m * Pw h (Ec m) := by
      rcases lt_or_ge A.card 2 with hlt | hge2
      · -- `A.card = 1`: `Lambda` is trivial
        have hdelta : Delta (fun k : Fin A.card => dsh h i₀ (eFin A k)) = 1 := by
          rw [Delta]
          refine Finset.prod_eq_one (fun i _ => ?_)
          refine Finset.prod_eq_one (fun j hj => ?_)
          rw [Finset.mem_filter] at hj
          have hi := i.isLt
          have hj' := j.isLt
          rw [Fin.lt_def] at hj
          omega
        have hLamD1 : LamD A.card (fun k => dsh h i₀ (eFin A k)) = 1 := by
          rw [LamD, hdelta]
          simp
        rw [hLamD1, mul_one]
        have hle_ktil : (1 + εcorr) * Kc A.card ≤ Ktil ε_box εcorr m :=
          le_trans (by linarith [Kc_nonneg' A.card]) (self_le_Ktil ε_box εcorr hεbox hεc0 m A.card hcardm)
        calc (1 + εcorr) * Kc A.card ≤ Ktil ε_box εcorr m := hle_ktil
          _ = Ktil ε_box εcorr m * 1 := (mul_one _).symm
          _ ≤ Ktil ε_box εcorr m * Pw h (Ec m) := mul_le_mul_of_nonneg_left hP1 hK0
      · -- `2 ≤ A.card`: the pair distribution
        have hdist := LamD_le_sum_Vw (p := p) hge2 hδ'inj hident
        have hmono : ∀ k k' : Fin A.card,
            (Vw (h (eFin A k) - h (eFin A k'))) ^ (Ec A.card)
              ≤ (Vw (h (eFin A k) - h (eFin A k'))) ^ (Ec m) :=
          fun k k' => pow_le_pow_right₀ (one_le_Vw _) (Ec_mono hcardm)
        have hstep : (∑ k : Fin A.card,
              ∑ k' ∈ Finset.univ.filter (fun k' : Fin A.card => k < k'),
                (Vw (h (eFin A k) - h (eFin A k'))) ^ (Ec A.card)) ≤ Pw h (Ec m) := by
          refine le_trans (Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun k' _ => hmono k k'))) ?_
          exact Commons.Combinatorics.Finset.sum_pairs_le_of_orderEmb (eEmb A)
            (fun i j => (Vw (h i - h j)) ^ (Ec m)) (fun i j => pow_nonneg (Vw_nonneg _) _)
        have hS0 : 0 ≤ ∑ k : Fin A.card,
            ∑ k' ∈ Finset.univ.filter (fun k' : Fin A.card => k < k'),
              (Vw (h (eFin A k) - h (eFin A k'))) ^ (Ec A.card) :=
          Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun k' _ => pow_nonneg (Vw_nonneg _) _))
        have hle_ktil : (1 + εcorr) * Kc A.card ≤ Ktil ε_box εcorr m :=
          le_trans (by linarith [Kc_nonneg' A.card])
            (self_le_Ktil ε_box εcorr hεbox hεc0 m A.card hcardm)
        calc (1 + εcorr) * (Kc A.card * LamD A.card (fun k => dsh h i₀ (eFin A k)))
            ≤ (1 + εcorr) * (Kc A.card * ∑ k : Fin A.card,
                ∑ k' ∈ Finset.univ.filter (fun k' : Fin A.card => k < k'),
                  (Vw (h (eFin A k) - h (eFin A k'))) ^ (Ec A.card)) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hdist (Kc_nonneg' A.card)) (by linarith)
          _ = ((1 + εcorr) * Kc A.card) * (∑ k : Fin A.card,
                ∑ k' ∈ Finset.univ.filter (fun k' : Fin A.card => k < k'),
                  (Vw (h (eFin A k) - h (eFin A k'))) ^ (Ec A.card)) := by ring
          _ ≤ Ktil ε_box εcorr m * (∑ k : Fin A.card,
                ∑ k' ∈ Finset.univ.filter (fun k' : Fin A.card => k < k'),
                  (Vw (h (eFin A k) - h (eFin A k'))) ^ (Ec A.card)) :=
              mul_le_mul_of_nonneg_right hle_ktil hS0
          _ ≤ Ktil ε_box εcorr m * Pw h (Ec m) := mul_le_mul_of_nonneg_left hstep hK0
    -- the main computation
    calc (p : ℝ)⁻¹ * ∑ x : ZMod p, ∏ i ∈ A, gGT R W p εw (x + h i)
        = (p : ℝ)⁻¹ * ∑ t : Fin p,
            ∏ i ∈ A, gGT R W p εw (((t : ZMod p) - h i₀) + h i) := by
          rw [sum_reindex_gGT (A := A) h i₀]
      _ ≤ (p : ℝ)⁻¹ * (((Nat.totient W : ℝ) / (W : ℝ) / Real.log (R : ℝ)) ^ A.card
            * boxSum R W (Ac A.card) (fun k => dsh h i₀ (eFin A k))
                (fun _ : Fin 1 => 1 - m₁) (fun _ : Fin 1 => 1 - m₁ + p)) := by
          refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (Nat.cast_nonneg p))
          exact gsum_le_boxsum (p := p) hi₀ hεw hεw4 hεp1 hm₁mem rfl rfl
      _ = ((Nat.totient W : ℝ) / (W : ℝ) / Real.log (R : ℝ)) ^ A.card
            * ((p : ℝ)⁻¹ * boxSum R W (Ac A.card) (fun k => dsh h i₀ (eFin A k))
                (fun _ : Fin 1 => 1 - m₁) (fun _ : Fin 1 => 1 - m₁ + p)) := by ring
      _ ≤ ((Nat.totient W : ℝ) / (W : ℝ) / Real.log (R : ℝ)) ^ A.card
            * ((1 + εcorr) * ((W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ)) ^ A.card
                * (Kc A.card * LamD A.card (fun k => dsh h i₀ (eFin A k)))) :=
          mul_le_mul_of_nonneg_left hbu' (by positivity)
      _ = (1 + εcorr) * (Kc A.card * LamD A.card (fun k => dsh h i₀ (eFin A k))) := by
          rw [show ((Nat.totient W : ℝ) / (W : ℝ) / Real.log (R : ℝ)) ^ A.card
              * ((1 + εcorr) * ((W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ)) ^ A.card
                * (Kc A.card * LamD A.card (fun k => dsh h i₀ (eFin A k))))
              = (1 + εcorr) * (((Nat.totient W : ℝ) / (W : ℝ) / Real.log (R : ℝ)) ^ A.card
                * ((W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ)) ^ A.card)
                * (Kc A.card * LamD A.card (fun k => dsh h i₀ (eFin A k))) by ring]
          rw [hcP, mul_one]
      _ ≤ Ktil ε_box εcorr m * Pw h (Ec m) := hfinal
  · -- the support is empty
    have hzero : ∑ x : ZMod p, ∏ i ∈ A, gGT R W p εw (x + h i) = 0 := by
      refine Finset.sum_eq_zero (fun x _ => ?_)
      exact prod_gGT_eq_zero_of_not_win (R := R) (W := W) (fun hc => hsupp ⟨x, hc⟩)
    rw [hzero, mul_zero]
    exact mul_nonneg hK0 hP0

end ATermBound


/-! ## 10. The correlation condition for the Goldston–Yıldırım majorant -/

section Assembly

variable {k R W : ℕ} {εw ε_box εcorr : ℝ}

/-- The crude `L^∞` bound of the majorant, used in the collision case. -/
noncomputable def Bnd (R W p : ℕ) : ℝ :=
  max (1 : ℝ) ((Nat.totient W : ℝ) * (W : ℝ) * (p : ℝ) ^ 2 * Real.log (R : ℝ))

lemma Bnd_nonneg (R W p : ℕ) : 0 ≤ Bnd R W p :=
  le_trans zero_le_one (le_max_left _ _)

/-- **Green–Tao's correlation condition (Proposition `mu-cor-con`) for the Goldston–Yıldırım
majorant `ν = nuGT`.** -/
theorem corrCond_nuGT {p : ℕ} [Fact p.Prime]
    (hk : 1 ≤ k) (hR : 3 ≤ R) (hRk : 3 * k ≤ R) (hW : 1 ≤ W)
    (hεbox : 0 ≤ ε_box) (hεcorr : 0 < εcorr) (hεw : 0 < εw) (hεw4 : 4 * εw ≤ 1)
    (hεp1 : 1 ≤ εw * (p : ℝ))
    (hsmallEr : 6 * (3 * (k : ℝ)) * (Real.log (R : ℝ)) ^ (k * 2 ^ (k - 1))
      ≤ εcorr * (R : ℝ) ^ 6)
    (hsmallMn : ∀ a : ℕ, 1 ≤ a → a ≤ k * 2 ^ (k - 1) →
      4 * ((zbC a) ^ a * (EK a * stripBound W a)) ≤ (εcorr / 2) * Real.log (R : ℝ) * Kc a)
    (hside : (R : ℤ) ^ (10 * (k * 2 ^ (k - 1))) ≤ (p : ℤ))
    (hp3 : 3 ≤ p) :
    ∃ C : ℕ → ℕ → ℝ,
      Commons.NumberTheory.Sieve.CorrCond p (nuGT R W p εw) (2 ^ (k - 1)) C := by
  classical
  have hR1 : 1 < R := by omega
  have hεc0 : 0 ≤ εcorr := le_of_lt hεcorr
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero (Fact.out : p.Prime))
  have hRz : (1 : ℤ) ≤ (R : ℤ) := by exact_mod_cast (by omega : 1 ≤ R)
  refine corrCond_of_gy_ub hp3 (nuGT R W p εw) (2 ^ (k - 1))
    (K := fun m => Kcorr ε_box εcorr m) (Dc := fun m => (Bnd R W p) ^ m) (E := Ec)
    (fun m => Kcorr_nonneg ε_box εcorr hεbox hεc0 m)
    (fun m => pow_nonneg (Bnd_nonneg R W p) m) ?_
  intro m hm1 hm2 h
  have hm2' : 2 ≤ m := hm1
  have hmk : m ≤ k * 2 ^ (k - 1) := by
    refine le_trans hm2 ?_
    calc 2 ^ (k - 1) = 1 * 2 ^ (k - 1) := (one_mul _).symm
      _ ≤ (k : ℕ) * 2 ^ (k - 1) := Nat.mul_le_mul_right _ hk
  have hAcard : ∀ A ∈ (Finset.univ : Finset (Fin m)).powerset, A.card ≤ k * 2 ^ (k - 1) := by
    intro A _
    have h1 : A.card ≤ m := by
      have := Finset.card_le_univ A
      simpa using this
    exact le_trans h1 hmk
  have hP1 : 1 ≤ Pw h (Ec m) := one_le_Pw hm2' h (Ec m)
  by_cases hinj : Function.Injective h
  · have hstep : (p : ℝ)⁻¹ * ∑ x : ZMod p, ∏ i : Fin m, nuGT R W p εw (x + h i)
        ≤ Kcorr ε_box εcorr m * Pw h (Ec m) := by
      have h1 : (∑ x : ZMod p, ∏ i : Fin m, nuGT R W p εw (x + h i))
          ≤ ∑ A ∈ (Finset.univ : Finset (Fin m)).powerset,
              ∑ x : ZMod p, ∏ i ∈ A, gGT R W p εw (x + h i) := by
        refine le_trans (Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset (ZMod p))) =>
          prod_nuGT_le_sum_gGT (W := W) (ε := εw) hR1 h x)) ?_
        rw [Finset.sum_comm]
      refine le_trans (mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr (Nat.cast_nonneg p))) ?_
      rw [Finset.mul_sum]
      have hper : ∀ A ∈ (Finset.univ : Finset (Fin m)).powerset,
          (p : ℝ)⁻¹ * (∑ x : ZMod p, ∏ i ∈ A, gGT R W p εw (x + h i))
            ≤ Ktil ε_box εcorr m * Pw h (Ec m) := by
        intro A hA
        rw [Finset.mem_powerset] at hA
        by_cases hAe : A = ∅
        · subst hAe
          have hsum : ∑ x : ZMod p, ∏ i ∈ (∅ : Finset (Fin m)), gGT R W p εw (x + h i)
              = (p : ℝ) := by
            have hc : ∀ x : ZMod p,
                (∏ i ∈ (∅ : Finset (Fin m)), gGT R W p εw (x + h i)) = (1 : ℝ) :=
              fun x => Finset.prod_empty
            simp only [hc, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
          rw [hsum, inv_mul_cancel₀ hp0]
          have honeK : (1 : ℝ) ≤ Ktil ε_box εcorr m := one_le_Ktil ε_box εcorr hεbox hεc0 m
          nlinarith [honeK, hP1]
        · refine gTerm_le (k := k) (R := R) (W := W) (p := p) (A := A)
            (Finset.nonempty_iff_ne_empty.mpr hAe) (hAcard A (Finset.mem_powerset.mpr hA))
            hinj hk hR hRk hW hεbox hεcorr hεw hεw4 hεp1 hm2' hsmallEr hsmallMn ?_
          have hc : A.card ≤ k * 2 ^ (k - 1) := hAcard A (Finset.mem_powerset.mpr hA)
          have hm : 10 * A.card ≤ 10 * (k * 2 ^ (k - 1)) := by omega
          exact le_trans (pow_le_pow_right₀ hRz hm) hside
      calc ∑ A ∈ (Finset.univ : Finset (Fin m)).powerset,
            (p : ℝ)⁻¹ * (∑ x : ZMod p, ∏ i ∈ A, gGT R W p εw (x + h i))
          ≤ ∑ _A ∈ (Finset.univ : Finset (Fin m)).powerset,
              Ktil ε_box εcorr m * Pw h (Ec m) := Finset.sum_le_sum hper
        _ = 2 ^ m * (Ktil ε_box εcorr m * Pw h (Ec m)) := by
            rw [Finset.sum_const, Finset.card_powerset, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul]
            push_cast
            ring
        _ = Kcorr ε_box εcorr m * Pw h (Ec m) := by rw [Kcorr]; ring
    calc (p : ℝ)⁻¹ * ∑ x : ZMod p, ∏ i : Fin m, nuGT R W p εw (x + h i)
        ≤ Kcorr ε_box εcorr m * Pw h (Ec m) := hstep
      _ = ∑ i : Fin m, ∑ j ∈ Finset.univ.filter (fun j : Fin m => i < j),
            (if h i = h j then (Bnd R W p) ^ m
             else Kcorr ε_box εcorr m
               * (∏ q ∈ (min (h i - h j).val (p - (h i - h j).val)).primeFactors,
                     (1 + (q : ℝ) ^ (-(1 / 2 : ℝ)))) ^ (Ec m)) := by
          rw [Pw, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j hj => ?_)
          rw [Finset.mem_filter] at hj
          have hne : h i ≠ h j := fun hc => absurd (hinj hc) (ne_of_lt hj.2)
          rw [if_neg hne, Vw]
  · have hcoll : ∃ i j : Fin m, i ≠ j ∧ h i = h j := by
      by_contra hc
      push_neg at hc
      exact hinj (fun a b hab => by
        by_contra hne
        exact hc a b hne hab)
    obtain ⟨i, j, hij, heq⟩ := hcoll
    have hLHS : (p : ℝ)⁻¹ * ∑ x : ZMod p, ∏ i : Fin m, nuGT R W p εw (x + h i)
        ≤ (Bnd R W p) ^ m := by
      have h1 : ∀ x : ZMod p, (∏ i : Fin m, nuGT R W p εw (x + h i))
          ≤ (Bnd R W p) ^ m := by
        intro x
        calc (∏ i : Fin m, nuGT R W p εw (x + h i))
            ≤ ∏ _i : Fin m, Bnd R W p :=
              Finset.prod_le_prod (fun i _ => nuGT_nonneg hR1 _)
                (fun i _ => nuGT_le_bnd hR1 hW εw _)
          _ = (Bnd R W p) ^ m := by
              rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have h2 : (∑ x : ZMod p, ∏ i : Fin m, nuGT R W p εw (x + h i))
          ≤ ∑ x : ZMod p, (Bnd R W p) ^ m :=
        Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset (ZMod p))) => h1 x)
      have h3 : (∑ _x : ZMod p, (Bnd R W p) ^ m) = (p : ℝ) * (Bnd R W p) ^ m := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      rw [h3] at h2
      have h4 := mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr (Nat.cast_nonneg p))
      have h5 : (p : ℝ)⁻¹ * ((p : ℝ) * (Bnd R W p) ^ m) = (Bnd R W p) ^ m := by
        rw [← mul_assoc, inv_mul_cancel₀ hp0, one_mul]
      rw [h5] at h4
      exact h4
    set F : Fin m → Fin m → ℝ := fun i' j' => (if h i' = h j' then (Bnd R W p) ^ m
        else Kcorr ε_box εcorr m
          * (∏ q ∈ (min (h i' - h j').val (p - (h i' - h j').val)).primeFactors,
                (1 + (q : ℝ) ^ (-(1 / 2 : ℝ)))) ^ (Ec m)) with hF
    have hnn : ∀ i' j' : Fin m, 0 ≤ F i' j' := by
      intro i' j'
      change 0 ≤ (if h i' = h j' then (Bnd R W p) ^ m
        else Kcorr ε_box εcorr m
          * (∏ q ∈ (min (h i' - h j').val (p - (h i' - h j').val)).primeFactors,
                (1 + (q : ℝ) ^ (-(1 / 2 : ℝ)))) ^ (Ec m))
      by_cases hc : h i' = h j'
      · rw [if_pos hc]; exact pow_nonneg (Bnd_nonneg R W p) m
      · rw [if_neg hc]
        exact mul_nonneg (Kcorr_nonneg ε_box εcorr hεbox hεc0 m) (pow_nonneg (Vw_nonneg _) _)
    have hRHS : (Bnd R W p) ^ m ≤ ∑ i' : Fin m,
        ∑ j' ∈ Finset.univ.filter (fun j' : Fin m => i' < j'), F i' j' := by
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · have hmem : j ∈ Finset.univ.filter (fun j' : Fin m => i < j') := by
          rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hlt⟩
        have hii : F i j = (Bnd R W p) ^ m := by rw [hF]; exact if_pos heq
        calc (Bnd R W p) ^ m = F i j := hii.symm
          _ ≤ ∑ j' ∈ Finset.univ.filter (fun j' : Fin m => i < j'), F i j' :=
              Finset.single_le_sum (f := fun j' : Fin m => F i j')
                (fun j' _ => hnn i j') hmem
          _ ≤ ∑ i' : Fin m, ∑ j' ∈ Finset.univ.filter (fun j' : Fin m => i' < j'), F i' j' :=
              Finset.single_le_sum
                (f := fun i' : Fin m =>
                  ∑ j' ∈ Finset.univ.filter (fun j' : Fin m => i' < j'), F i' j')
                (fun i' _ => Finset.sum_nonneg (fun j' _ => hnn i' j')) (Finset.mem_univ i)
      · have hmem : i ∈ Finset.univ.filter (fun j' : Fin m => j < j') := by
          rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hgt⟩
        have hii : F j i = (Bnd R W p) ^ m := by rw [hF]; exact if_pos heq.symm
        calc (Bnd R W p) ^ m = F j i := hii.symm
          _ ≤ ∑ j' ∈ Finset.univ.filter (fun j' : Fin m => j < j'), F j j' :=
              Finset.single_le_sum (f := fun j' : Fin m => F j j')
                (fun j' _ => hnn j j') hmem
          _ ≤ ∑ i' : Fin m, ∑ j' ∈ Finset.univ.filter (fun j' : Fin m => i' < j'), F i' j' :=
              Finset.single_le_sum
                (f := fun i' : Fin m =>
                  ∑ j' ∈ Finset.univ.filter (fun j' : Fin m => i' < j'), F i' j')
                (fun i' _ => Finset.sum_nonneg (fun j' _ => hnn i' j')) (Finset.mem_univ j)
    rw [hF] at hRHS
    exact le_trans hLHS hRHS

end Assembly


end Corr
end GYMaj
