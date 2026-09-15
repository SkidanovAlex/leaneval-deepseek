import Mathlib
import Submission.Commons.NumberTheory.Sieve.KPseudorandom_mean
import Submission.Commons.Combinatorics.Transference.lfc_weight_moment
import Submission.Commons.NumberTheory.Sieve.qmod_rat_div
import Submission.Commons.NumberTheory.Sieve.isSmallRat_rat_div
import Submission.Commons.Combinatorics.Finset.card_sigma_bool_false

set_option autoImplicit false

namespace Commons.Combinatorics.Transference

open _root_.Finset
open scoped BigOperators
open Commons.NumberTheory.Sieve

/-! ## Helpers for `qmod` and `IsSmallRat` of a signed rational -/

lemma isSmallRat_mono {L L' : ℕ} (h : L ≤ L') {q : ℚ} (hq : IsSmallRat L q) :
    IsSmallRat L' q := ⟨le_trans hq.1 h, le_trans hq.2 h⟩

lemma isSmallRat_neg {L : ℕ} {q : ℚ} (hq : IsSmallRat L q) : IsSmallRat L (-q) := by
  rw [IsSmallRat, Rat.neg_num, Rat.neg_den]
  exact ⟨by simpa using hq.1, hq.2⟩

lemma isSmallRat_rat_div_int {a b : ℤ} {L₀ : ℕ} (hb : b ≠ 0) (ha : a.natAbs ≤ L₀)
    (hbn : b.natAbs ≤ L₀) : IsSmallRat L₀ ((a : ℚ) / (b : ℚ)) := by
  rw [show ((a : ℚ) / (b : ℚ)) = Rat.divInt a b from (Rat.divInt_eq_div a b).symm, IsSmallRat]
  constructor
  · have hdvd : (Rat.divInt a b).num.natAbs ∣ a.natAbs :=
      Int.natAbs_dvd_natAbs.mpr (Rat.num_dvd a hb)
    rcases eq_or_ne a 0 with rfl | ha0
    · have hzero : Rat.divInt (0 : ℤ) b = 0 := by rw [Rat.divInt_eq_div]; simp
      rw [hzero]; simp
    · exact le_trans (Nat.le_of_dvd (Int.natAbs_pos.mpr ha0) hdvd) ha
  · rw [Rat.den_divInt, if_neg hb]
    exact le_trans (Nat.div_le_self b.natAbs (b.gcd a)) hbn

lemma qmod_rat_div_int {p : ℕ} [Fact p.Prime] (a b : ℤ) (hb : (b : ZMod p) ≠ 0) :
    qmod p ((a : ℚ) / (b : ℚ)) = (a : ZMod p) / (b : ZMod p) := by
  set q : ℚ := Rat.divInt a b with hq
  have hbZ : b ≠ 0 := by intro h; exact hb (by rw [h]; simp)
  obtain ⟨c, ha, hb'⟩ := Rat.num_den_mk (q := q) (n := a) (d := b) hbZ hq
  have hbcast : (b : ZMod p) = (c : ZMod p) * (q.den : ZMod p) := by
    rw [hb']; push_cast; ring
  have hne : (c : ZMod p) * (q.den : ZMod p) ≠ 0 := by rw [← hbcast]; exact hb
  have hcz : (c : ZMod p) ≠ 0 := (mul_ne_zero_iff.mp hne).1
  have hd : (q.den : ZMod p) ≠ 0 := (mul_ne_zero_iff.mp hne).2
  have hcast : (a : ZMod p) = (c : ZMod p) * (q.num : ZMod p) := by
    rw [ha]; push_cast; ring
  rw [show ((a : ℚ)/(b:ℚ)) = q from (Rat.divInt_eq_div a b).symm.trans hq.symm]
  rw [qmod, hbcast, hcast]
  field_simp

lemma two_mul_le_two_sq (K : ℕ) : K + K ≤ 2 * K * K + 2 := by
  have h := Nat.mul_le_mul_left 2 (Nat.le_mul_self K)
  rw [← Nat.mul_assoc] at h
  omega

lemma le_two_sq (K : ℕ) : K ≤ 2 * K * K + 2 := by
  calc K ≤ K * K := Nat.le_mul_self K
    _ ≤ K * K + (K * K + 2) := Nat.le_add_right _ _
    _ = 2 * K * K + 2 := by ring

lemma isSmallRat_cubeCoeff' {d : ℕ} {L₀ : ℕ} (hL : 1 ≤ L₀) (ω : Fin d → Bool)
    (j : Ix d) : IsSmallRat L₀ (cubeCoeff d ω j) := by
  rcases j with j | k
  · rw [cubeCoeff_inl]; split_ifs
    · exact isSmallRat_one hL
    · exact isSmallRat_zero hL
  · fin_cases k
    · change IsSmallRat L₀ (cubeCoeff d ω (Sum.inr 0)); rw [cubeCoeff_inr0]
      exact isSmallRat_one hL
    · change IsSmallRat L₀ (cubeCoeff d ω (Sum.inr 1)); rw [cubeCoeff_inr1]
      exact isSmallRat_zero hL
    · change IsSmallRat L₀ (cubeCoeff d ω (Sum.inr 2)); rw [cubeCoeff_inr2]
      exact isSmallRat_zero hL

/-! ## Generalized coefficients -/

/-- The integer coefficient `c (j+1)` attached to the index `j : Fin (k-1)`. -/
noncomputable def cg {k : ℕ} (c : Fin k → ℤ) (j : Fin (k-1)) : ℤ :=
  c ⟨j.val + 1, by have := j.isLt; omega⟩

lemma cg_eq_one_add {k : ℕ} (c : Fin k → ℤ) (i : Fin (k-1)) :
    cg c i = c ⟨1 + i.val, by have := i.isLt; omega⟩ := by
  unfold cg
  congr 1
  apply Fin.ext
  show i.val + 1 = 1 + i.val
  omega

noncomputable def gC {k : ℕ} (c : Fin k → ℤ) (i : Fin (k-1)) : ℚ := ((cg c i : ℤ) : ℚ)

/-- A rational coefficient of `h_j` in the `φ_i` form whose `qmod` is `1 - c_{i+1}/c_{j+1}`.
When `p ∣ c_{j+1}` the class `c_{j+1}` is `0` and we take `1`. -/
noncomputable def gphiC (p : ℕ) [Fact p.Prime] {k : ℕ} (c : Fin k → ℤ)
    (i j : Fin (k-1)) : ℚ :=
  if p ∣ (cg c j).natAbs then 1
  else (((cg c j - cg c i : ℤ) : ℚ) / ((cg c j : ℤ) : ℚ))

noncomputable def phiCoeffG (p : ℕ) [Fact p.Prime] {k : ℕ} (c : Fin k → ℤ)
    (i : Fin (k-1)) (ω : Fin (k-1) → Bool) : Ix (k-1) → ℚ :=
  Sum.elim (fun j => if ω j then gphiC p c i j else 0) ![1, -(gC c i), 0]

noncomputable def phiCoeffG' (p : ℕ) [Fact p.Prime] {k : ℕ} (c : Fin k → ℤ)
    (i : Fin (k-1)) (ω : Fin (k-1) → Bool) : Ix (k-1) → ℚ :=
  Sum.elim (fun j => if ω j then gphiC p c i j else 0) ![1, 0, -(gC c i)]

lemma phiCoeffG_inl (p : ℕ) [Fact p.Prime] {k : ℕ} (c : Fin k → ℤ)
    (i : Fin (k-1)) (ω : Fin (k-1) → Bool) (j : Fin (k-1)) :
    phiCoeffG p c i ω (Sum.inl j) = if ω j then gphiC p c i j else 0 := rfl
lemma phiCoeffG_inr0 (p : ℕ) [Fact p.Prime] {k : ℕ} (c : Fin k → ℤ)
    (i : Fin (k-1)) (ω : Fin (k-1) → Bool) : phiCoeffG p c i ω (Sum.inr 0) = 1 := rfl
lemma phiCoeffG_inr1 (p : ℕ) [Fact p.Prime] {k : ℕ} (c : Fin k → ℤ)
    (i : Fin (k-1)) (ω : Fin (k-1) → Bool) : phiCoeffG p c i ω (Sum.inr 1) = -(gC c i) := rfl
lemma phiCoeffG_inr2 (p : ℕ) [Fact p.Prime] {k : ℕ} (c : Fin k → ℤ)
    (i : Fin (k-1)) (ω : Fin (k-1) → Bool) : phiCoeffG p c i ω (Sum.inr 2) = 0 := rfl

lemma phiCoeffG'_inl (p : ℕ) [Fact p.Prime] {k : ℕ} (c : Fin k → ℤ)
    (i : Fin (k-1)) (ω : Fin (k-1) → Bool) (j : Fin (k-1)) :
    phiCoeffG' p c i ω (Sum.inl j) = if ω j then gphiC p c i j else 0 := rfl
lemma phiCoeffG'_inr0 (p : ℕ) [Fact p.Prime] {k : ℕ} (c : Fin k → ℤ)
    (i : Fin (k-1)) (ω : Fin (k-1) → Bool) : phiCoeffG' p c i ω (Sum.inr 0) = 1 := rfl
lemma phiCoeffG'_inr1 (p : ℕ) [Fact p.Prime] {k : ℕ} (c : Fin k → ℤ)
    (i : Fin (k-1)) (ω : Fin (k-1) → Bool) : phiCoeffG' p c i ω (Sum.inr 1) = 0 := rfl
lemma phiCoeffG'_inr2 (p : ℕ) [Fact p.Prime] {k : ℕ} (c : Fin k → ℤ)
    (i : Fin (k-1)) (ω : Fin (k-1) → Bool) : phiCoeffG' p c i ω (Sum.inr 2) = -(gC c i) := rfl

noncomputable def phiFormG (p : ℕ) [Fact p.Prime] {k : ℕ} (c : Fin k → ℤ)
    (i : Fin (k-1)) (ω : Fin (k-1) → Bool) (v : Ix (k-1) → ZMod p) : ZMod p :=
  ∑ kk : Ix (k-1), qmod p (phiCoeffG p c i ω kk) * v kk

noncomputable def phiFormG' (p : ℕ) [Fact p.Prime] {k : ℕ} (c : Fin k → ℤ)
    (i : Fin (k-1)) (ω : Fin (k-1) → Bool) (v : Ix (k-1) → ZMod p) : ZMod p :=
  ∑ kk : Ix (k-1), qmod p (phiCoeffG' p c i ω kk) * v kk

lemma cg_zmod_eq_zero_iff {p : ℕ} [Fact p.Prime] {k : ℕ} (c : Fin k → ℤ) (j : Fin (k-1)) :
    ((cg c j : ℤ) : ZMod p) = 0 ↔ p ∣ (cg c j).natAbs := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]

lemma qmod_gphiC {p : ℕ} [Fact p.Prime] {k : ℕ} (c : Fin k → ℤ) (i j : Fin (k-1)) :
    qmod p (gphiC p c i j)
      = 1 - ((cg c i : ℤ) : ZMod p) * (((cg c j : ℤ) : ZMod p))⁻¹ := by
  unfold gphiC
  split_ifs with hp
  · rw [qmod_one]
    have hb0 : ((cg c j : ℤ) : ZMod p) = 0 := (cg_zmod_eq_zero_iff c j).mpr hp
    rw [hb0, inv_zero, mul_zero, sub_zero]
  · have hbne : ((cg c j : ℤ) : ZMod p) ≠ 0 := fun h =>
      hp ((cg_zmod_eq_zero_iff c j).mp h)
    rw [qmod_rat_div_int _ _ hbne, Int.cast_sub, div_eq_mul_inv, sub_mul,
      mul_inv_cancel₀ hbne]

lemma qmod_phiCoeffG_inl {p : ℕ} [Fact p.Prime] {k : ℕ} (c : Fin k → ℤ)
    (i : Fin (k-1)) (ω : Fin (k-1) → Bool) (j : Fin (k-1)) :
    qmod p (phiCoeffG p c i ω (Sum.inl j))
      = (if ω j then (1 : ZMod p) else 0)
        * (1 - ((cg c i : ℤ) : ZMod p) * (((cg c j : ℤ) : ZMod p))⁻¹) := by
  rw [phiCoeffG_inl]
  split_ifs with h
  · rw [qmod_gphiC, one_mul]
  · rw [qmod_zero, zero_mul]

lemma qmod_phiCoeffG'_inl {p : ℕ} [Fact p.Prime] {k : ℕ} (c : Fin k → ℤ)
    (i : Fin (k-1)) (ω : Fin (k-1) → Bool) (j : Fin (k-1)) :
    qmod p (phiCoeffG' p c i ω (Sum.inl j))
      = (if ω j then (1 : ZMod p) else 0)
        * (1 - ((cg c i : ℤ) : ZMod p) * (((cg c j : ℤ) : ZMod p))⁻¹) := by
  rw [phiCoeffG'_inl]
  split_ifs with h
  · rw [qmod_gphiC, one_mul]
  · rw [qmod_zero, zero_mul]

lemma eval_phiFormG {p : ℕ} [Fact p.Prime] {k : ℕ} (c : Fin k → ℤ) (i : Fin (k-1))
    (ω : Fin (k-1) → Bool) (v : Ix (k-1) → ZMod p) :
    phiFormG p c i ω v
      = v (Sum.inr 0)
        + ∑ j : Fin (k-1), (if ω j then (1 : ZMod p) else 0) * v (Sum.inl j)
        - (((cg c i : ℤ) : ZMod p))
          * (v (Sum.inr 1)
            + ∑ j : Fin (k-1), (if ω j then (1 : ZMod p) else 0) * v (Sum.inl j)
                * (((cg c j : ℤ) : ZMod p))⁻¹) := by
  rw [phiFormG, Fintype.sum_sum_type, Fin.sum_univ_three]
  have h1 : ∀ j : Fin (k-1),
      qmod p (phiCoeffG p c i ω (Sum.inl j)) * v (Sum.inl j)
        = (if ω j then (1 : ZMod p) else 0) * v (Sum.inl j)
          - (((cg c i : ℤ) : ZMod p))
            * ((if ω j then (1 : ZMod p) else 0) * v (Sum.inl j)
                * (((cg c j : ℤ) : ZMod p))⁻¹) := by
    intro j
    rw [qmod_phiCoeffG_inl]
    ring
  rw [Finset.sum_congr rfl (fun j _ => h1 j)]
  have h2 : qmod p (phiCoeffG p c i ω (Sum.inr 0)) * v (Sum.inr 0) = v (Sum.inr 0) := by
    rw [phiCoeffG_inr0, qmod_one, one_mul]
  have h3 : qmod p (phiCoeffG p c i ω (Sum.inr 1)) * v (Sum.inr 1)
      = -(((cg c i : ℤ) : ZMod p)) * v (Sum.inr 1) := by
    rw [phiCoeffG_inr1, gC, qmod_neg, qmod_intCast]
  have h4 : qmod p (phiCoeffG p c i ω (Sum.inr 2)) * v (Sum.inr 2) = 0 := by
    rw [phiCoeffG_inr2, qmod_zero, zero_mul]
  rw [h2, h3, h4, Finset.sum_sub_distrib]
  have hsumB : (∑ j : Fin (k-1), (((cg c i : ℤ) : ZMod p))
        * ((if ω j then (1 : ZMod p) else 0) * v (Sum.inl j)
            * (((cg c j : ℤ) : ZMod p))⁻¹))
      = (((cg c i : ℤ) : ZMod p))
        * ∑ j : Fin (k-1), (if ω j then (1 : ZMod p) else 0) * v (Sum.inl j)
            * (((cg c j : ℤ) : ZMod p))⁻¹ := by
    rw [Finset.mul_sum]
  rw [hsumB, mul_add]
  ring

lemma eval_phiFormG' {p : ℕ} [Fact p.Prime] {k : ℕ} (c : Fin k → ℤ) (i : Fin (k-1))
    (ω : Fin (k-1) → Bool) (v : Ix (k-1) → ZMod p) :
    phiFormG' p c i ω v
      = v (Sum.inr 0)
        + ∑ j : Fin (k-1), (if ω j then (1 : ZMod p) else 0) * v (Sum.inl j)
        - (((cg c i : ℤ) : ZMod p))
          * (v (Sum.inr 2)
            + ∑ j : Fin (k-1), (if ω j then (1 : ZMod p) else 0) * v (Sum.inl j)
                * (((cg c j : ℤ) : ZMod p))⁻¹) := by
  rw [phiFormG', Fintype.sum_sum_type, Fin.sum_univ_three]
  have h1 : ∀ j : Fin (k-1),
      qmod p (phiCoeffG' p c i ω (Sum.inl j)) * v (Sum.inl j)
        = (if ω j then (1 : ZMod p) else 0) * v (Sum.inl j)
          - (((cg c i : ℤ) : ZMod p))
            * ((if ω j then (1 : ZMod p) else 0) * v (Sum.inl j)
                * (((cg c j : ℤ) : ZMod p))⁻¹) := by
    intro j
    rw [qmod_phiCoeffG'_inl]
    ring
  rw [Finset.sum_congr rfl (fun j _ => h1 j)]
  have h2 : qmod p (phiCoeffG' p c i ω (Sum.inr 0)) * v (Sum.inr 0) = v (Sum.inr 0) := by
    rw [phiCoeffG'_inr0, qmod_one, one_mul]
  have h3 : qmod p (phiCoeffG' p c i ω (Sum.inr 1)) * v (Sum.inr 1) = 0 := by
    rw [phiCoeffG'_inr1, qmod_zero, zero_mul]
  have h4 : qmod p (phiCoeffG' p c i ω (Sum.inr 2)) * v (Sum.inr 2)
      = -(((cg c i : ℤ) : ZMod p)) * v (Sum.inr 2) := by
    rw [phiCoeffG'_inr2, gC, qmod_neg, qmod_intCast]
  rw [h2, h3, h4, Finset.sum_sub_distrib]
  have hsumB : (∑ j : Fin (k-1), (((cg c i : ℤ) : ZMod p))
        * ((if ω j then (1 : ZMod p) else 0) * v (Sum.inl j)
            * (((cg c j : ℤ) : ZMod p))⁻¹))
      = (((cg c i : ℤ) : ZMod p))
        * ∑ j : Fin (k-1), (if ω j then (1 : ZMod p) else 0) * v (Sum.inl j)
            * (((cg c j : ℤ) : ZMod p))⁻¹ := by
    rw [Finset.mul_sum]
  rw [hsumB, mul_add]
  ring


/-! ## Size and non-degeneracy of the generalized coefficients -/

lemma cg_natAbs_le {k : ℕ} {K : ℕ} (c : Fin k → ℤ) (hcb : ∀ m, (c m).natAbs ≤ K)
    (j : Fin (k-1)) : (cg c j).natAbs ≤ K := by
  unfold cg
  exact hcb ⟨j.val + 1, by have := j.isLt; omega⟩

lemma isSmallRat_gphiC {p : ℕ} [Fact p.Prime] {k : ℕ} {K : ℕ} (c : Fin k → ℤ)
    (hcb : ∀ m, (c m).natAbs ≤ K) (i j : Fin (k-1)) :
    IsSmallRat (2 * K * K + 2) (gphiC p c i j) := by
  unfold gphiC
  split_ifs with hp
  · exact isSmallRat_one (by omega)
  · apply isSmallRat_rat_div_int
    · intro h
      have h' : cg c j = 0 := Int.cast_injective h
      exact hp (by rw [h']; simp)
    · calc (cg c j - cg c i).natAbs ≤ (cg c j).natAbs + (cg c i).natAbs :=
            Int.natAbs_sub_le _ _
        _ ≤ K + K := by
            have h1 := cg_natAbs_le c hcb j
            have h2 := cg_natAbs_le c hcb i
            omega
        _ ≤ 2 * K * K + 2 := two_mul_le_two_sq K
    · have hj := cg_natAbs_le c hcb j
      calc (cg c j).natAbs ≤ K := hj
        _ ≤ 2 * K * K + 2 := le_two_sq K

lemma isSmallRat_phiCoeffG {p : ℕ} [Fact p.Prime] {k : ℕ} {K : ℕ} (c : Fin k → ℤ)
    (hcb : ∀ m, (c m).natAbs ≤ K) (i : Fin (k-1)) (ω : Fin (k-1) → Bool) (j : Ix (k-1)) :
    IsSmallRat (2 * K * K + 2) (phiCoeffG p c i ω j) := by
  have hL : 1 ≤ 2 * K * K + 2 := by omega
  have hi : (cg c i).natAbs ≤ 2 * K * K + 2 :=
    le_trans (cg_natAbs_le c hcb i) (le_two_sq K)
  rcases j with j | kk
  · rw [phiCoeffG_inl]; split_ifs
    · exact isSmallRat_gphiC c hcb i j
    · exact isSmallRat_zero hL
  · fin_cases kk
    · change IsSmallRat (2 * K * K + 2) (phiCoeffG p c i ω (Sum.inr 0))
      rw [phiCoeffG_inr0]; exact isSmallRat_one hL
    · change IsSmallRat (2 * K * K + 2) (phiCoeffG p c i ω (Sum.inr 1))
      rw [phiCoeffG_inr1, gC]
      exact isSmallRat_neg (isSmallRat_intCast hL _ hi)
    · change IsSmallRat (2 * K * K + 2) (phiCoeffG p c i ω (Sum.inr 2))
      rw [phiCoeffG_inr2]; exact isSmallRat_zero hL

lemma isSmallRat_phiCoeffG' {p : ℕ} [Fact p.Prime] {k : ℕ} {K : ℕ} (c : Fin k → ℤ)
    (hcb : ∀ m, (c m).natAbs ≤ K) (i : Fin (k-1)) (ω : Fin (k-1) → Bool) (j : Ix (k-1)) :
    IsSmallRat (2 * K * K + 2) (phiCoeffG' p c i ω j) := by
  have hL : 1 ≤ 2 * K * K + 2 := by omega
  have hi : (cg c i).natAbs ≤ 2 * K * K + 2 :=
    le_trans (cg_natAbs_le c hcb i) (le_two_sq K)
  rcases j with j | kk
  · rw [phiCoeffG'_inl]; split_ifs
    · exact isSmallRat_gphiC c hcb i j
    · exact isSmallRat_zero hL
  · fin_cases kk
    · change IsSmallRat (2 * K * K + 2) (phiCoeffG' p c i ω (Sum.inr 0))
      rw [phiCoeffG'_inr0]; exact isSmallRat_one hL
    · change IsSmallRat (2 * K * K + 2) (phiCoeffG' p c i ω (Sum.inr 1))
      rw [phiCoeffG'_inr1]; exact isSmallRat_zero hL
    · change IsSmallRat (2 * K * K + 2) (phiCoeffG' p c i ω (Sum.inr 2))
      rw [phiCoeffG'_inr2, gC]
      exact isSmallRat_neg (isSmallRat_intCast hL _ hi)

lemma gphiC_ne_zero {p : ℕ} [Fact p.Prime] {k : ℕ} {c : Fin k → ℤ}
    (hc_inj : Function.Injective c) {i j : Fin (k-1)} (h : i ≠ j) : gphiC p c i j ≠ 0 := by
  unfold gphiC
  split_ifs with hp
  · norm_num
  · apply div_ne_zero
    · rw [Int.cast_sub, sub_ne_zero]
      intro hc
      have hc' : cg c j = cg c i := Int.cast_injective hc
      exact h (by
        have hfin := hc_inj (a₁ := ⟨j.val + 1, by have := j.isLt; omega⟩)
          (a₂ := ⟨i.val + 1, by have := i.isLt; omega⟩) hc'
        exact Fin.ext (by have := congrArg Fin.val hfin; simp at this; omega))
    · intro hb
      have hb' : cg c j = 0 := Int.cast_injective hb
      exact hp (by rw [hb']; simp)

lemma phiCoeffG_inj {p : ℕ} [Fact p.Prime] {k : ℕ} {c : Fin k → ℤ}
    (hc_inj : Function.Injective c) {i i' : Fin (k-1)} {ω ω' : Fin (k-1) → Bool}
    (hω : ω i = false) (hω' : ω' i' = false)
    (h : phiCoeffG p c i ω = phiCoeffG p c i' ω') : i = i' ∧ ω = ω' := by
  have h1 := congrFun h (Sum.inr 1)
  rw [phiCoeffG_inr1, phiCoeffG_inr1, gC, gC] at h1
  have hcg : cg c i = cg c i' := Int.cast_injective (neg_inj.mp h1)
  have hii : i = i' := by
    have hfin := hc_inj (a₁ := ⟨i.val + 1, by have := i.isLt; omega⟩)
      (a₂ := ⟨i'.val + 1, by have := i'.isLt; omega⟩) hcg
    exact Fin.ext (by have := congrArg Fin.val hfin; simp at this; omega)
  refine ⟨hii, ?_⟩
  subst hii
  funext j
  by_cases hj : j = i
  · subst hj
    rw [hω, hω']
  · have hz : gphiC p c i j ≠ 0 := gphiC_ne_zero hc_inj (Ne.symm hj)
    have h2 := congrFun h (Sum.inl j)
    rw [phiCoeffG_inl, phiCoeffG_inl] at h2
    by_cases hωj : ω j
    · by_cases hω'j : ω' j
      · simp [hωj, hω'j]
      · refine absurd ?_ hz
        simpa [hωj, hω'j] using h2
    · by_cases hω'j : ω' j
      · refine absurd ?_ hz
        simpa [hωj, hω'j] using h2.symm
      · simp [hωj, hω'j]

lemma phiCoeffG'_inj {p : ℕ} [Fact p.Prime] {k : ℕ} {c : Fin k → ℤ}
    (hc_inj : Function.Injective c) {i i' : Fin (k-1)} {ω ω' : Fin (k-1) → Bool}
    (hω : ω i = false) (hω' : ω' i' = false)
    (h : phiCoeffG' p c i ω = phiCoeffG' p c i' ω') : i = i' ∧ ω = ω' := by
  have h1 := congrFun h (Sum.inr 2)
  rw [phiCoeffG'_inr2, phiCoeffG'_inr2, gC, gC] at h1
  have hcg : cg c i = cg c i' := Int.cast_injective (neg_inj.mp h1)
  have hii : i = i' := by
    have hfin := hc_inj (a₁ := ⟨i.val + 1, by have := i.isLt; omega⟩)
      (a₂ := ⟨i'.val + 1, by have := i'.isLt; omega⟩) hcg
    exact Fin.ext (by have := congrArg Fin.val hfin; simp at this; omega)
  refine ⟨hii, ?_⟩
  subst hii
  funext j
  by_cases hj : j = i
  · subst hj
    rw [hω, hω']
  · have hz : gphiC p c i j ≠ 0 := gphiC_ne_zero hc_inj (Ne.symm hj)
    have h2 := congrFun h (Sum.inl j)
    rw [phiCoeffG'_inl, phiCoeffG'_inl] at h2
    by_cases hωj : ω j
    · by_cases hω'j : ω' j
      · simp [hωj, hω'j]
      · refine absurd ?_ hz
        simpa [hωj, hω'j] using h2
    · by_cases hω'j : ω' j
      · refine absurd ?_ hz
        simpa [hωj, hω'j] using h2.symm
      · simp [hωj, hω'j]

lemma notProp_phiG {p : ℕ} [Fact p.Prime] {k : ℕ} {c : Fin k → ℤ}
    (hc_inj : Function.Injective c) {s s' : PhiIx (k-1)} (h : s ≠ s') :
    ¬ ∃ lam : ℚ, ∀ j, phiCoeffG p c s'.1 s'.2.1 j = lam * phiCoeffG p c s.1 s.2.1 j := by
  obtain ⟨i, ω, hω⟩ := s
  obtain ⟨i', ω', hω'⟩ := s'
  refine notProp_of_x_eq_one (L := phiCoeffG p c i ω) (L' := phiCoeffG p c i' ω')
    (phiCoeffG_inr0 p c i ω) (phiCoeffG_inr0 p c i' ω') ?_
  intro hc
  apply h
  obtain ⟨h1a, h1b⟩ := phiCoeffG_inj hc_inj hω hω' hc
  subst h1a
  congr 1
  exact Subtype.ext h1b

lemma notProp_phiG' {p : ℕ} [Fact p.Prime] {k : ℕ} {c : Fin k → ℤ}
    (hc_inj : Function.Injective c) {s s' : PhiIx (k-1)} (h : s ≠ s') :
    ¬ ∃ lam : ℚ, ∀ j, phiCoeffG' p c s'.1 s'.2.1 j = lam * phiCoeffG' p c s.1 s.2.1 j := by
  obtain ⟨i, ω, hω⟩ := s
  obtain ⟨i', ω', hω'⟩ := s'
  refine notProp_of_x_eq_one (L := phiCoeffG' p c i ω) (L' := phiCoeffG' p c i' ω')
    (phiCoeffG'_inr0 p c i ω) (phiCoeffG'_inr0 p c i' ω') ?_
  intro hc
  apply h
  obtain ⟨h1a, h1b⟩ := phiCoeffG'_inj hc_inj hω hω' hc
  subst h1a
  congr 1
  exact Subtype.ext h1b

lemma phiCoeffG_inr0_ne (p : ℕ) [Fact p.Prime] {k : ℕ} (c : Fin k → ℤ)
    (i : Fin (k-1)) (ω : Fin (k-1) → Bool) : phiCoeffG p c i ω (Sum.inr 0) ≠ 0 := by
  rw [phiCoeffG_inr0]; norm_num

lemma phiCoeffG'_inr0_ne (p : ℕ) [Fact p.Prime] {k : ℕ} (c : Fin k → ℤ)
    (i : Fin (k-1)) (ω : Fin (k-1) → Bool) : phiCoeffG' p c i ω (Sum.inr 0) ≠ 0 := by
  rw [phiCoeffG'_inr0]; norm_num

lemma phiCoeffG_inr1_ne {p : ℕ} [Fact p.Prime] {k : ℕ} (c : Fin k → ℤ)
    (hcne : ∀ i : Fin (k-1), cg c i ≠ 0) (i : Fin (k-1)) (ω : Fin (k-1) → Bool) :
    phiCoeffG p c i ω (Sum.inr 1) ≠ 0 := by
  rw [phiCoeffG_inr1, gC, neg_ne_zero]
  exact_mod_cast hcne i

lemma phiCoeffG'_inr2_ne {p : ℕ} [Fact p.Prime] {k : ℕ} (c : Fin k → ℤ)
    (hcne : ∀ i : Fin (k-1), cg c i ≠ 0) (i : Fin (k-1)) (ω : Fin (k-1) → Bool) :
    phiCoeffG' p c i ω (Sum.inr 2) ≠ 0 := by
  rw [phiCoeffG'_inr2, gC, neg_ne_zero]
  exact_mod_cast hcne i


/-! ## The applications of the linear forms condition -/

noncomputable abbrev LphiG (p : ℕ) [Fact p.Prime] {k : ℕ} (c : Fin k → ℤ) :
    PhiIx (k-1) → Ix (k-1) → ℚ := fun s => phiCoeffG p c s.1 s.2.1

noncomputable abbrev LphiG' (p : ℕ) [Fact p.Prime] {k : ℕ} (c : Fin k → ℤ) :
    PhiIx (k-1) → Ix (k-1) → ℚ := fun s => phiCoeffG' p c s.1 s.2.1

lemma lfc_gvn_S0G {p : ℕ} [Fact p.Prime] {k : ℕ} {ν : ZMod p → ℝ} {ε : ℝ} {K : ℕ}
    (hLFC : LinFormsCond p ν (2 ^ (k-1) * (k+1)) (k+3) (2 * K * K + 2) ε) :
    |((Fintype.card (Ix (k-1) → ZMod p) : ℝ))⁻¹ *
      (∑ v : Ix (k-1) → ZMod p, ∏ ω : CubeIx (k-1), ν (cubeForm (k-1) v ω)) - 1| ≤ ε := by
  have hcard1 : 1 ≤ Fintype.card (CubeIx (k-1)) := by
    rw [card_cubeIx]; exact Nat.one_le_two_pow
  have hcard2 : Fintype.card (CubeIx (k-1)) ≤ 2 ^ (k-1) * (k+1) := by
    rw [card_cubeIx]
    exact Nat.le_mul_of_pos_right _ (by omega)
  have h := lfc_apply_equiv (V := Ix (k-1)) (e := finSumFinEquiv) hLFC (t := (k-1) + 3)
    (by omega) (by omega) hcard1 hcard2 (Lcube (k-1))
    (fun i j => isSmallRat_cubeCoeff' (by omega) i j)
    (fun i => ⟨Sum.inr 0, cubeCoeff_inr0_ne i⟩)
    (fun i i' hii => notProp_cube hii)
    (fun _ => 0)
  simpa only [Lcube, cubeForm, Pi.zero_apply, add_zero] using h

lemma lfc_gvn_S1G {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : 2 ≤ k) {ν : ZMod p → ℝ} {ε : ℝ}
    {K : ℕ} (c : Fin k → ℤ) (hcb : ∀ m, (c m).natAbs ≤ K)
    (hc_inj : Function.Injective c) (hcne : ∀ i : Fin (k-1), cg c i ≠ 0)
    (hLFC : LinFormsCond p ν (2 ^ (k-1) * (k+1)) (k+3) (2 * K * K + 2) ε) :
    |((Fintype.card (Ix (k-1) → ZMod p) : ℝ))⁻¹ *
      (∑ v : Ix (k-1) → ZMod p,
        (∏ ω : CubeIx (k-1), ν (cubeForm (k-1) v ω))
        * ∏ s : PhiIx (k-1), ν (phiFormG p c s.1 s.2.1 v)) - 1| ≤ ε := by
  have hcard : Fintype.card (CubeIx (k-1) ⊕ PhiIx (k-1)) ≤ 2 ^ (k-1) * (k+1) := by
    rw [Fintype.card_sum, card_cubeIx, card_phiIx]
    have h1 : (k - 1) * 2 ^ ((k - 1) - 1) ≤ (k - 1) * 2 ^ (k - 1) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    refine le_trans (Nat.add_le_add_left h1 _) ?_
    have hm : 1 + (k - 1) = k := by omega
    have he : 2 ^ (k - 1) + (k - 1) * 2 ^ (k - 1) = 2 ^ (k - 1) * (1 + (k - 1)) := by ring
    rw [he, hm]
    exact Nat.mul_le_mul_left _ (by omega)
  have hcard1 : 1 ≤ Fintype.card (CubeIx (k-1) ⊕ PhiIx (k-1)) := by
    rw [Fintype.card_sum, card_cubeIx]
    have := Nat.one_le_two_pow (n := k-1)
    omega
  have h := lfc_apply_equiv (V := Ix (k-1)) (e := finSumFinEquiv) hLFC (t := (k-1) + 3)
    (by omega) (by omega) hcard1 hcard
    (Sum.elim (Lcube (k-1)) (LphiG p c))
    (fun i j => by
      rcases i with i | i
      · exact isSmallRat_cubeCoeff' (by omega) i j
      · exact isSmallRat_phiCoeffG c hcb i.1 i.2.1 j)
    (fun i => by
      rcases i with i | i
      · exact ⟨Sum.inr 0, cubeCoeff_inr0_ne i⟩
      · exact ⟨Sum.inr 0, phiCoeffG_inr0_ne p c i.1 i.2.1⟩)
    (fun i i' hii => by
      rcases i with i | i <;> rcases i' with i' | i'
      · exact notProp_cube (fun hc => hii (by rw [hc]))
      · exact notProp_of_zero_coord (L := cubeCoeff (k-1) i) (L' := phiCoeffG p c i'.1 i'.2.1)
          (k := Sum.inr 1) (cubeCoeff_inr1 (k-1) i) (phiCoeffG_inr1_ne c hcne i'.1 i'.2.1)
      · refine notProp_of_zero_coord' (L := phiCoeffG p c i.1 i.2.1) (L' := cubeCoeff (k-1) i')
          (k := Sum.inr 1) (phiCoeffG_inr1_ne c hcne i.1 i.2.1) (cubeCoeff_inr1 (k-1) i') ?_
        exact cubeCoeff_inr0 (k-1) i'
      · exact notProp_phiG hc_inj (fun hc => hii (by rw [hc])))
    (fun _ => 0)
  simp only [Fintype.prod_sum_type] at h
  simpa only [Lcube, LphiG, Sum.elim_inl, Sum.elim_inr, cubeForm, phiFormG, Pi.zero_apply,
    add_zero] using h

lemma lfc_gvn_S2G {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : 2 ≤ k) {ν : ZMod p → ℝ} {ε : ℝ}
    {K : ℕ} (c : Fin k → ℤ) (hcb : ∀ m, (c m).natAbs ≤ K)
    (hc_inj : Function.Injective c) (hcne : ∀ i : Fin (k-1), cg c i ≠ 0)
    (hLFC : LinFormsCond p ν (2 ^ (k-1) * (k+1)) (k+3) (2 * K * K + 2) ε) :
    |((Fintype.card (Ix (k-1) → ZMod p) : ℝ))⁻¹ *
      (∑ v : Ix (k-1) → ZMod p,
        (∏ ω : CubeIx (k-1), ν (cubeForm (k-1) v ω))
        * (∏ s : PhiIx (k-1), ν (phiFormG p c s.1 s.2.1 v))
        * ∏ s : PhiIx (k-1), ν (phiFormG' p c s.1 s.2.1 v)) - 1| ≤ ε := by
  have hcard : Fintype.card (CubeIx (k-1) ⊕ (PhiIx (k-1) ⊕ PhiIx (k-1)))
      ≤ 2 ^ (k-1) * (k+1) := by
    have hd1 : 1 ≤ k - 1 := by omega
    have hpow : 2 ^ (k - 1) = 2 * 2 ^ ((k - 1) - 1) := pow_two_eq (k - 1) hd1
    have hm : 1 + (k - 1) = k := by omega
    have hkey : 2 ^ (k - 1)
        + ((k - 1) * 2 ^ ((k - 1) - 1) + (k - 1) * 2 ^ ((k - 1) - 1))
        ≤ 2 ^ (k - 1) * (k + 1) := by
      rw [hpow]
      have he : 2 * 2 ^ ((k - 1) - 1)
          + ((k - 1) * 2 ^ ((k - 1) - 1) + (k - 1) * 2 ^ ((k - 1) - 1))
          = 2 * 2 ^ ((k - 1) - 1) * (1 + (k - 1)) := by ring
      rw [he, hm]
      exact Nat.mul_le_mul_left _ (by omega)
    rw [Fintype.card_sum, Fintype.card_sum, card_cubeIx, card_phiIx]
    exact hkey
  have hcard1 : 1 ≤ Fintype.card (CubeIx (k-1) ⊕ (PhiIx (k-1) ⊕ PhiIx (k-1))) := by
    rw [Fintype.card_sum, card_cubeIx]
    have := Nat.one_le_two_pow (n := k-1)
    omega
  have h := lfc_apply_equiv (V := Ix (k-1)) (e := finSumFinEquiv) hLFC (t := (k-1) + 3)
    (by omega) (by omega) hcard1 hcard
    (Sum.elim (Lcube (k-1)) (Sum.elim (LphiG p c) (LphiG' p c)))
    (fun i j => by
      rcases i with i | i | i
      · exact isSmallRat_cubeCoeff' (by omega) i j
      · exact isSmallRat_phiCoeffG c hcb i.1 i.2.1 j
      · exact isSmallRat_phiCoeffG' c hcb i.1 i.2.1 j)
    (fun i => by
      rcases i with i | i | i
      · exact ⟨Sum.inr 0, cubeCoeff_inr0_ne i⟩
      · exact ⟨Sum.inr 0, phiCoeffG_inr0_ne p c i.1 i.2.1⟩
      · exact ⟨Sum.inr 0, phiCoeffG'_inr0_ne p c i.1 i.2.1⟩)
    (fun i i' hii => by
      rcases i with i | i | i <;> rcases i' with i' | i' | i'
      · exact notProp_cube (fun hc => hii (by rw [hc]))
      · exact notProp_of_zero_coord (L := cubeCoeff (k-1) i) (L' := phiCoeffG p c i'.1 i'.2.1)
          (k := Sum.inr 1) (cubeCoeff_inr1 (k-1) i) (phiCoeffG_inr1_ne c hcne i'.1 i'.2.1)
      · exact notProp_of_zero_coord (L := cubeCoeff (k-1) i) (L' := phiCoeffG' p c i'.1 i'.2.1)
          (k := Sum.inr 2) (cubeCoeff_inr2 (k-1) i) (phiCoeffG'_inr2_ne c hcne i'.1 i'.2.1)
      · refine notProp_of_zero_coord' (L := phiCoeffG p c i.1 i.2.1) (L' := cubeCoeff (k-1) i')
          (k := Sum.inr 1) (phiCoeffG_inr1_ne c hcne i.1 i.2.1) (cubeCoeff_inr1 (k-1) i') ?_
        exact cubeCoeff_inr0 (k-1) i'
      · exact notProp_phiG hc_inj (fun hc => hii (by rw [hc]))
      · refine notProp_of_zero_coord' (L := phiCoeffG p c i.1 i.2.1)
          (L' := phiCoeffG' p c i'.1 i'.2.1) (k := Sum.inr 1)
          (phiCoeffG_inr1_ne c hcne i.1 i.2.1) (phiCoeffG'_inr1 p c i'.1 i'.2.1) ?_
        exact phiCoeffG'_inr0 p c i'.1 i'.2.1
      · refine notProp_of_zero_coord' (L := phiCoeffG' p c i.1 i.2.1) (L' := cubeCoeff (k-1) i')
          (k := Sum.inr 2) (phiCoeffG'_inr2_ne c hcne i.1 i.2.1) (cubeCoeff_inr2 (k-1) i') ?_
        exact cubeCoeff_inr0 (k-1) i'
      · exact notProp_of_zero_coord (L := phiCoeffG' p c i.1 i.2.1)
          (L' := phiCoeffG p c i'.1 i'.2.1) (k := Sum.inr 1)
          (phiCoeffG'_inr1 p c i.1 i.2.1) (phiCoeffG_inr1_ne c hcne i'.1 i'.2.1)
      · exact notProp_phiG' hc_inj (fun hc => hii (by rw [hc])))
    (fun _ => 0)
  simp only [Fintype.prod_sum_type] at h
  simpa only [Lcube, LphiG, LphiG', Sum.elim_inl, Sum.elim_inr, cubeForm, phiFormG, phiFormG',
    Pi.zero_apply, add_zero, mul_assoc] using h


/-! ## The `φ`-product with generalized coefficients -/

/-- The `φ`-product `∏_{i, ω_i = 0} ν(x + ω·h - c_{i+1}(s + ω·h/c_{j+1}))`. -/
noncomputable def PhiFG (p : ℕ) [Fact p.Prime] (k : ℕ) (c : Fin k → ℤ) (ν : ZMod p → ℝ)
    (h : Fin (k-1) → ZMod p) (x s : ZMod p) : ℝ :=
  ∏ i : Fin (k-1), ∏ ω ∈ (Finset.univ.filter (fun ω : Fin (k-1) → Bool => ω i = false)),
    ν (x + ∑ j : Fin (k-1), (if ω j then (1 : ZMod p) else 0) * h j
      - ((c ⟨1 + i.val, by have := i.isLt; omega⟩ : ℤ) : ZMod p)
        * (s + ∑ j : Fin (k-1), (if ω j then (1 : ZMod p) else 0) * h j
            * (((c ⟨j.val + 1, by have := j.isLt; omega⟩ : ℤ) : ZMod p))⁻¹))

/-- The average of `PhiFG` over `s`. -/
noncomputable def AavgG (p : ℕ) [Fact p.Prime] (k : ℕ) (c : Fin k → ℤ) (ν : ZMod p → ℝ)
    (h : Fin (k-1) → ZMod p) (x : ZMod p) : ℝ :=
  (p : ℝ)⁻¹ * ∑ s : ZMod p, PhiFG p k c ν h x s

lemma phiFormG_mk {p : ℕ} [Fact p.Prime] {k : ℕ} (c : Fin k → ℤ)
    (h : Fin (k-1) → ZMod p) (x s s' : ZMod p) (i : Fin (k-1)) (ω : Fin (k-1) → Bool) :
    phiFormG p c i ω (Sum.elim h ![x, s, s'])
      = x + ∑ j : Fin (k-1), (if ω j then (1 : ZMod p) else 0) * h j
        - ((c ⟨1 + i.val, by have := i.isLt; omega⟩ : ℤ) : ZMod p)
          * (s + ∑ j : Fin (k-1), (if ω j then (1 : ZMod p) else 0) * h j
              * (((c ⟨j.val + 1, by have := j.isLt; omega⟩ : ℤ) : ZMod p))⁻¹) := by
  rw [eval_phiFormG]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [show ((cg c i : ℤ) : ZMod p)
        = ((c ⟨1 + i.val, by have := i.isLt; omega⟩ : ℤ) : ZMod p) from by
      rw [cg_eq_one_add]]
  rfl

lemma phiFormG'_mk {p : ℕ} [Fact p.Prime] {k : ℕ} (c : Fin k → ℤ)
    (h : Fin (k-1) → ZMod p) (x s s' : ZMod p) (i : Fin (k-1)) (ω : Fin (k-1) → Bool) :
    phiFormG' p c i ω (Sum.elim h ![x, s, s'])
      = x + ∑ j : Fin (k-1), (if ω j then (1 : ZMod p) else 0) * h j
        - ((c ⟨1 + i.val, by have := i.isLt; omega⟩ : ℤ) : ZMod p)
          * (s' + ∑ j : Fin (k-1), (if ω j then (1 : ZMod p) else 0) * h j
              * (((c ⟨j.val + 1, by have := j.isLt; omega⟩ : ℤ) : ZMod p))⁻¹) := by
  rw [eval_phiFormG']
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [show ((cg c i : ℤ) : ZMod p)
        = ((c ⟨1 + i.val, by have := i.isLt; omega⟩ : ℤ) : ZMod p) from by
      rw [cg_eq_one_add]]
  rfl

lemma prod_phiG_mk {p : ℕ} [Fact p.Prime] {k : ℕ} {c : Fin k → ℤ} {ν : ZMod p → ℝ}
    {h : Fin (k-1) → ZMod p} {x s s' : ZMod p} :
    (∏ s0 : PhiIx (k-1), ν (phiFormG p c s0.1 s0.2.1 (Sum.elim h ![x, s, s'])))
      = PhiFG p k c ν h x s := by
  rw [PhiFG]
  rw [prod_phiIx (F := fun i ω => ν (phiFormG p c i ω (Sum.elim h ![x, s, s'])))]
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro ω _
  rw [phiFormG_mk]

lemma prod_phiG'_mk {p : ℕ} [Fact p.Prime] {k : ℕ} {c : Fin k → ℤ} {ν : ZMod p → ℝ}
    {h : Fin (k-1) → ZMod p} {x s s' : ZMod p} :
    (∏ s0 : PhiIx (k-1), ν (phiFormG' p c s0.1 s0.2.1 (Sum.elim h ![x, s, s'])))
      = PhiFG p k c ν h x s' := by
  rw [PhiFG]
  rw [prod_phiIx (F := fun i ω => ν (phiFormG' p c i ω (Sum.elim h ![x, s, s'])))]
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro ω _
  rw [phiFormG'_mk]


/-! ## The weighted cube moment with generalized coefficients -/

set_option maxHeartbeats 4000000 in
theorem lfc_weight_moment_inj {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : 3 ≤ k) {ν : ZMod p → ℝ}
    (hν : ∀ x, 0 ≤ ν x) {ε : ℝ} (hε0 : 0 ≤ ε)
    (c : Fin k → ℤ) (K : ℕ) (hcb : ∀ m, (c m).natAbs ≤ K)
    (hinj : Function.Injective (fun m : Fin k => ((c m : ℤ) : ZMod p)))
    (hcne : ∀ m : Fin k, 1 ≤ m.val → c m ≠ 0)
    (hLFC : Commons.NumberTheory.Sieve.LinFormsCond p ν (2 ^ (k-1) * (k+1)) (k+3) (2 * K * K + 2) ε) :
    (∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p,
        (∏ ω : Fin (k-1) → Bool,
            ν (x + ∑ j : Fin (k-1), (if ω j then (1 : ZMod p) else 0) * h j))
        * (((((p : ℝ)⁻¹) * (∑ s : ZMod p,
              ∏ i : Fin (k-1),
                ∏ ω ∈ (Finset.univ.filter (fun ω : Fin (k-1) → Bool => ω i = false)),
                  ν (x + ∑ j : Fin (k-1), (if ω j then (1 : ZMod p) else 0) * h j
                    - ((c ⟨1 + i.val, by have := i.isLt; omega⟩ : ℤ) : ZMod p)
                      * (s + ∑ j : Fin (k-1), (if ω j then (1 : ZMod p) else 0) * h j
                          * (((c ⟨j.val+1, by have := j.isLt; omega⟩ : ℤ) : ZMod p))⁻¹))))
            - 1) ^ 2))
      ≤ 4 * ε * (p : ℝ) ^ (k - 1 + 1) := by
  set P : ℝ := (p : ℝ) with hP
  have hPpos : 0 < P := by
    rw [hP]; exact_mod_cast (Fact.out : Nat.Prime p).pos
  have hpne : (p : ℝ) ≠ 0 := by
    have h := (Fact.out : Nat.Prime p).pos
    exact_mod_cast (ne_of_gt h)
  have hPne : P ≠ 0 := by rw [hP]; exact hpne
  have hinjZ : Function.Injective c := by
    intro a b hab
    exact hinj (congrArg (fun z : ℤ => (z : ZMod p)) hab)
  have hcne' : ∀ i : Fin (k-1), cg c i ≠ 0 := by
    intro i
    unfold cg
    exact hcne ⟨i.val + 1, by have := i.isLt; omega⟩ (by
      show (1:ℕ) ≤ i.val + 1
      omega)
  have hS0 := lfc_gvn_S0G (p := p) (k := k) (K := K) hLFC
  have hS1 := lfc_gvn_S1G (p := p) (k := k) (by omega) c hcb hinjZ hcne' hLFC
  have hS2 := lfc_gvn_S2G (p := p) (k := k) (by omega) c hcb hinjZ hcne' hLFC
  rw [sum_fun_sum_equiv] at hS0 hS1 hS2
  simp only [prod_cube_mk] at hS0 hS1 hS2
  simp only [prod_phiG_mk] at hS1 hS2
  simp only [prod_phiG'_mk] at hS2
  have hNval : (Fintype.card (Ix (k-1) → ZMod p) : ℝ) = P ^ ((k-1) + 3) := by
    rw [Fintype.card_fun, ZMod.card]
    simp only [Fintype.card_sum, Fintype.card_fin]
    push_cast
    rw [hP]
  rw [hNval] at hS0 hS1 hS2
  have hNpos : 0 < P ^ ((k-1) + 3) := by positivity
  have hNne : P ^ ((k-1) + 3) ≠ 0 := ne_of_gt hNpos
  have hb0 := abs_le.mp hS0
  have hb1 := abs_le.mp hS1
  have hb2 := abs_le.mp hS2
  have key0 : (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p, T0 p (k-1) ν h x)
      ≤ (1 + ε) * P ^ ((k-1) + 3) := by
    have h1 : (P ^ ((k-1) + 3))⁻¹
        * (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p, T0 p (k-1) ν h x)
        ≤ 1 + ε := by linarith [hb0.2]
    have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt hNpos)
    rwa [← mul_assoc, mul_inv_cancel₀ hNne, one_mul,
      mul_comm (P ^ ((k-1) + 3)) (1 + ε)] at h2
  have key1 : (1 - ε) * P ^ ((k-1) + 3)
      ≤ (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p,
          T0 p (k-1) ν h x * PhiFG p k c ν h x s) := by
    have h1 : 1 - ε ≤ (P ^ ((k-1) + 3))⁻¹
        * (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p,
            T0 p (k-1) ν h x * PhiFG p k c ν h x s) := by
      linarith [hb1.1]
    have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt hNpos)
    rwa [← mul_assoc, mul_inv_cancel₀ hNne, one_mul,
      mul_comm (P ^ ((k-1) + 3)) (1 - ε)] at h2
  have key2 : (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p,
        T0 p (k-1) ν h x * PhiFG p k c ν h x s * PhiFG p k c ν h x s')
      ≤ (1 + ε) * P ^ ((k-1) + 3) := by
    have h1 : (P ^ ((k-1) + 3))⁻¹ * (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p,
          T0 p (k-1) ν h x * PhiFG p k c ν h x s * PhiFG p k c ν h x s') ≤ 1 + ε := by
      linarith [hb2.2]
    have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt hNpos)
    rwa [← mul_assoc, mul_inv_cancel₀ hNne, one_mul,
      mul_comm (P ^ ((k-1) + 3)) (1 + ε)] at h2
  have hA : ∀ h x, P * AavgG p k c ν h x = ∑ s : ZMod p, PhiFG p k c ν h x s := by
    intro h x
    rw [hP, AavgG, ← mul_assoc, mul_inv_cancel₀ hpne, one_mul]
  have h0 : (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p, T0 p (k-1) ν h x)
      = P ^ 2 * (∑ h, ∑ x, T0 p (k-1) ν h x) := by
    have e : ∀ h x, (∑ s : ZMod p, ∑ s' : ZMod p, T0 p (k-1) ν h x)
        = P ^ 2 * T0 p (k-1) ν h x := by
      intro h x
      rw [zmod_sum_sum_const, hP]
      ring
    rw [show (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p, T0 p (k-1) ν h x)
          = ∑ h, ∑ x, P ^ 2 * T0 p (k-1) ν h x from by
        apply Finset.sum_congr rfl
        intro h _
        apply Finset.sum_congr rfl
        intro x _
        exact e h x]
    simp only [Finset.mul_sum]
  have h1e : (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p,
        T0 p (k-1) ν h x * PhiFG p k c ν h x s)
      = P ^ 2 * (∑ h, ∑ x, T0 p (k-1) ν h x * AavgG p k c ν h x) := by
    have e : ∀ h x, (∑ s : ZMod p, ∑ s' : ZMod p, T0 p (k-1) ν h x * PhiFG p k c ν h x s)
        = P ^ 2 * (T0 p (k-1) ν h x * AavgG p k c ν h x) := by
      intro h x
      rw [zmod_sum_sum_smul, ← hA h x, hP]
      ring
    rw [show (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p,
          T0 p (k-1) ν h x * PhiFG p k c ν h x s)
          = ∑ h, ∑ x, P ^ 2 * (T0 p (k-1) ν h x * AavgG p k c ν h x) from by
        apply Finset.sum_congr rfl
        intro h _
        apply Finset.sum_congr rfl
        intro x _
        exact e h x]
    simp only [Finset.mul_sum]
  have h2e : (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p,
        T0 p (k-1) ν h x * PhiFG p k c ν h x s * PhiFG p k c ν h x s')
      = P ^ 2 * (∑ h, ∑ x, T0 p (k-1) ν h x * (AavgG p k c ν h x) ^ 2) := by
    have e : ∀ h x, (∑ s : ZMod p, ∑ s' : ZMod p,
          T0 p (k-1) ν h x * PhiFG p k c ν h x s * PhiFG p k c ν h x s')
        = P ^ 2 * (T0 p (k-1) ν h x * (AavgG p k c ν h x) ^ 2) := by
      intro h x
      rw [zmod_sum_sum_mul, ← hA h x, hP]
      ring
    rw [show (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p,
          T0 p (k-1) ν h x * PhiFG p k c ν h x s * PhiFG p k c ν h x s')
          = ∑ h, ∑ x, P ^ 2 * (T0 p (k-1) ν h x * (AavgG p k c ν h x) ^ 2) from by
        apply Finset.sum_congr rfl
        intro h _
        apply Finset.sum_congr rfl
        intro x _
        exact e h x]
    simp only [Finset.mul_sum]
  have hLexp : (∑ h, ∑ x, T0 p (k-1) ν h x * (AavgG p k c ν h x - 1) ^ 2)
      = (∑ h, ∑ x, T0 p (k-1) ν h x * (AavgG p k c ν h x) ^ 2)
        - 2 * (∑ h, ∑ x, T0 p (k-1) ν h x * AavgG p k c ν h x)
        + (∑ h, ∑ x, T0 p (k-1) ν h x) := by
    have h2Y : 2 * (∑ h, ∑ x, T0 p (k-1) ν h x * AavgG p k c ν h x)
        = ∑ h, ∑ x, 2 * (T0 p (k-1) ν h x * AavgG p k c ν h x) := by
      simp only [Finset.mul_sum]
    rw [h2Y, ← sum_sum_sub, ← sum_sum_add]
    apply Finset.sum_congr rfl
    intro h _
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hP2L : P ^ 2 * (∑ h, ∑ x, T0 p (k-1) ν h x * (AavgG p k c ν h x - 1) ^ 2)
      = (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p,
            T0 p (k-1) ν h x * PhiFG p k c ν h x s * PhiFG p k c ν h x s')
        - 2 * (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p,
            T0 p (k-1) ν h x * PhiFG p k c ν h x s)
        + (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p, T0 p (k-1) ν h x) := by
    rw [hLexp]
    have e : P ^ 2 * ((∑ h, ∑ x, T0 p (k-1) ν h x * (AavgG p k c ν h x) ^ 2)
          - 2 * (∑ h, ∑ x, T0 p (k-1) ν h x * AavgG p k c ν h x)
          + (∑ h, ∑ x, T0 p (k-1) ν h x))
        = P ^ 2 * (∑ h, ∑ x, T0 p (k-1) ν h x * (AavgG p k c ν h x) ^ 2)
          - 2 * (P ^ 2 * (∑ h, ∑ x, T0 p (k-1) ν h x * AavgG p k c ν h x))
          + P ^ 2 * (∑ h, ∑ x, T0 p (k-1) ν h x) := by ring
    rw [e, ← h2e, ← h1e, ← h0]
  have hNfact : P ^ ((k-1) + 3) = P ^ 2 * (p : ℝ) ^ ((k-1) + 1) := by
    rw [hP, show (k-1) + 3 = 2 + ((k-1) + 1) from by omega, pow_add]
  have hP2pos : 0 < P ^ 2 := by positivity
  have hfinal : P ^ 2 * (∑ h, ∑ x, T0 p (k-1) ν h x * (AavgG p k c ν h x - 1) ^ 2)
      ≤ P ^ 2 * (4 * ε * (p : ℝ) ^ ((k-1) + 1)) := by
    rw [hP2L]
    have h4 : (1 + ε) * P ^ ((k-1) + 3) - 2 * ((1 - ε) * P ^ ((k-1) + 3))
          + (1 + ε) * P ^ ((k-1) + 3)
        = 4 * ε * (P ^ 2 * (p : ℝ) ^ ((k-1) + 1)) := by
      rw [hNfact]; ring
    linarith [key0, key1, key2, h4]
  have hfin := (mul_le_mul_iff_of_pos_left hP2pos).mp hfinal
  have hgoal : (∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p,
        (∏ ω : Fin (k-1) → Bool,
            ν (x + ∑ j : Fin (k-1), (if ω j then (1 : ZMod p) else 0) * h j))
        * (((((p : ℝ)⁻¹) * (∑ s : ZMod p,
              ∏ i : Fin (k-1),
                ∏ ω ∈ (Finset.univ.filter (fun ω : Fin (k-1) → Bool => ω i = false)),
                  ν (x + ∑ j : Fin (k-1), (if ω j then (1 : ZMod p) else 0) * h j
                    - ((c ⟨1 + i.val, by have := i.isLt; omega⟩ : ℤ) : ZMod p)
                      * (s + ∑ j : Fin (k-1), (if ω j then (1 : ZMod p) else 0) * h j
                          * (((c ⟨j.val+1, by have := j.isLt; omega⟩ : ℤ) : ZMod p))⁻¹))))
            - 1) ^ 2))
      = (∑ h, ∑ x, T0 p (k-1) ν h x * (AavgG p k c ν h x - 1) ^ 2) := by
    simp only [T0, AavgG, PhiFG]
  rw [hgoal]
  exact hfin

end Commons.Combinatorics.Transference
