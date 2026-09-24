import Mathlib
import Submission.Work.GM.Affine.setup

/-!
# GM §9: the "far mass" of the Fourier transform of the test function `f`

Let `f : ℝ → ℝ` be the §9 test function and `Fhat f` its Fourier transform.  Assume the
decay hypothesis

  `‖Fhat f ξ‖ ≤ c j ε * T^ε * (T/|ξ|)^j * Λ`  for every `ξ ≠ 0` and every `j ≥ 1`,

which is the shape of GM's §9 hypothesis (with `Λ` playing the role of `supf f`).

This file proves the elementary `L²` bound for the mass of `Fhat f` far from the origin:

  `∫_{|y| ≥ Y} ‖Fhat f y‖² ≤ 2 (c j ε T^ε)² Λ² T (T/Y)^{2j-1} / (2j-1)`

The mathematical content is the explicit evaluation of `∫_{|y| ≥ Y} |y|^{-2j}`.

All statements are in the namespace `Work.GM.Affine`.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-! ## Elementary rpow/pow algebra -/

lemma div_pow_eq_mul_rpow {T y : ℝ} (hT : 0 < T) (hy : 0 < y) (k : ℕ) :
    (T / y) ^ k = T ^ k * y ^ (-(k:ℝ)) := by
  rw [div_eq_mul_inv]
  rw [← Real.rpow_natCast (T * y⁻¹) k]
  rw [Real.mul_rpow (le_of_lt hT) (inv_nonneg.mpr (le_of_lt hy))]
  rw [Real.inv_rpow (le_of_lt hy)]
  rw [Real.rpow_neg (le_of_lt hy) (k:ℝ)]
  rw [Real.rpow_natCast T k]

lemma pow_mul_rpow_eq {T Y : ℝ} (hY : 0 < Y) {k : ℕ} (hk : 1 ≤ k) :
    T ^ k * Y ^ (1 - (k:ℝ)) = T * (T/Y) ^ (k - 1) := by
  have hkc : (((k-1:ℕ)):ℝ) = (k:ℝ) - 1 := by
    rw [Nat.cast_sub hk, Nat.cast_one]
  rw [show (1:ℝ) - (k:ℝ) = -((k:ℝ)-1) by ring]
  rw [Real.rpow_neg (le_of_lt hY) ((k:ℝ)-1), ← hkc, Real.rpow_natCast]
  have hTk : T ^ k = T * T ^ (k - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hk]
  rw [hTk, div_pow, div_eq_mul_inv]
  ring

/-! ## The one-sided integral `∫_Y^∞ (T/y)^k` -/

lemma integral_Ioi_rpow_neg_cpow {Y : ℝ} (hY : 0 < Y) {k : ℕ} (hk : 1 < k) :
    ∫ y in Set.Ioi Y, y ^ (-(k:ℝ)) = Y ^ (1 - (k:ℝ)) / ((k:ℝ) - 1) := by
  have hk1 : (1:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have ha : -(k:ℝ) < -1 := by linarith
  rw [integral_Ioi_rpow_of_lt ha hY]
  have h1 : - (k:ℝ) + 1 = -( (k:ℝ) - 1) := by ring
  rw [h1, neg_div_neg_eq]
  rw [show -((k:ℝ) - 1) = 1 - (k:ℝ) by ring]

lemma integral_Ioi_div_pow {T Y : ℝ} (hT : 0 < T) (hY : 0 < Y) {k : ℕ} (hk : 1 < k) :
    ∫ y in Set.Ioi Y, (T / y) ^ k = T * (T/Y)^(k-1) / ((k:ℝ) - 1) := by
  have hpt : Set.EqOn (fun y => (T/y)^k) (fun y => T^k * y^(-(k:ℝ))) (Set.Ioi Y) :=
    fun y hy => div_pow_eq_mul_rpow hT (lt_trans hY hy) k
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
      integral_Ioi_rpow_neg_cpow hY hk, ← mul_div_assoc, pow_mul_rpow_eq hY hk.le]

/-! ## The symmetric integral `∫_{|y| ≥ Y} (T/|y|)^k` -/

lemma setOf_le_abs_eq (Y : ℝ) : {y : ℝ | Y ≤ |y|} = Set.Ici Y ∪ Set.Iic (-Y) := by
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Ici, Set.mem_Iic]
  constructor
  · intro h
    by_cases hy : 0 ≤ y
    · left; rw [abs_of_nonneg hy] at h; exact h
    · right; rw [abs_of_neg (not_le.mp hy)] at h; linarith
  · intro h
    rcases h with h | h
    · exact le_trans h (le_abs_self y)
    · exact le_trans (by linarith : Y ≤ -y) (neg_le_abs y)

lemma integrableOn_abs_div_pow {T Y : ℝ} (hT : 0 < T) (hY : 0 < Y) {k : ℕ} (hk : 1 < k) :
    IntegrableOn (fun y : ℝ => (T / |y|) ^ k) {y : ℝ | Y ≤ |y|} := by
  have ha : -(k:ℝ) < -1 := by
    have : (1:ℝ) < k := by exact_mod_cast hk
    linarith
  have hIoi : IntegrableOn (fun y : ℝ => (T / y) ^ k) (Set.Ioi Y) := by
    have h1 : Integrable (fun y : ℝ => y ^ (-(k:ℝ))) (volume.restrict (Set.Ioi Y)) :=
      integrableOn_Ioi_rpow_of_lt ha hY
    have h2 : Integrable (fun y : ℝ => T ^ k * y ^ (-(k:ℝ))) (volume.restrict (Set.Ioi Y)) :=
      h1.const_mul (T ^ k)
    exact IntegrableOn.congr_fun h2
      (fun y hy => (div_pow_eq_mul_rpow hT (lt_trans hY hy) k).symm) measurableSet_Ioi
  have hIci : IntegrableOn (fun y : ℝ => (T / |y|) ^ k) (Set.Ici Y) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact IntegrableOn.congr_fun hIoi
      (fun y hy => by rw [abs_of_pos (lt_trans hY hy)]) measurableSet_Ioi
  have hIic : IntegrableOn (fun y : ℝ => (T / |y|) ^ k) (Set.Iic (-Y)) := by
    have hc : IntegrableOn (fun y : ℝ => (T / |y|) ^ k) (Set.Ici (-(-Y))) := by simpa using hIci
    have := IntegrableOn.comp_neg_Iic (c := -Y) hc
    exact this.congr_fun (fun y _ => by simp [abs_neg]) measurableSet_Iic
  rw [setOf_le_abs_eq Y]
  exact hIci.union hIic

lemma integral_abs_div_pow {T Y : ℝ} (hT : 0 < T) (hY : 0 < Y) {k : ℕ} (hk : 1 < k) :
    ∫ y in {y : ℝ | Y ≤ |y|}, (T / |y|) ^ k = 2 * T * (T/Y)^(k-1) / ((k:ℝ) - 1) := by
  have hK := integrableOn_abs_div_pow hT hY hk
  have hIci : IntegrableOn (fun y : ℝ => (T / |y|) ^ k) (Set.Ici Y) :=
    hK.mono_set (fun y hy => by
      simp only [Set.mem_Ici] at hy
      simp only [Set.mem_ofPred_eq]
      rwa [abs_of_pos (lt_of_lt_of_le hY hy)])
  have hIic : IntegrableOn (fun y : ℝ => (T / |y|) ^ k) (Set.Iic (-Y)) :=
    hK.mono_set (fun y hy => by
      simp only [Set.mem_Iic] at hy
      simp only [Set.mem_ofPred_eq]
      rw [abs_of_neg (by linarith : y < 0)]
      linarith)
  have hdisj : Disjoint (Set.Ici Y) (Set.Iic (-Y)) := by
    rw [Set.disjoint_left]
    intro y hy1 hy2
    simp only [Set.mem_Ici] at hy1
    simp only [Set.mem_Iic] at hy2
    linarith
  have hval_iic : ∫ y in Set.Iic (-Y), (T / |y|) ^ k = ∫ y in Set.Ioi Y, (T / |y|) ^ k := by
    have hcomp : ∫ x in Set.Iic (-Y), (T / |-x|) ^ k = ∫ x in Set.Ioi Y, (T / |x|) ^ k := by
      simpa using integral_comp_neg_Iic (-Y) (fun x : ℝ => (T / |x|) ^ k)
    simpa [abs_neg] using hcomp
  have hval_ioi : ∫ y in Set.Ioi Y, (T / |y|) ^ k = T * (T/Y)^(k-1) / ((k:ℝ) - 1) := by
    rw [setIntegral_congr_fun measurableSet_Ioi
          (fun y hy => by rw [abs_of_pos (lt_trans hY hy)])]
    exact integral_Ioi_div_pow hT hY hk
  rw [setOf_le_abs_eq Y, setIntegral_union hdisj measurableSet_Iic hIci hIic,
      integral_Ici_eq_integral_Ioi, hval_iic, hval_ioi]
  ring

/-! ## The requested far-mass estimate -/

theorem far_mass_le {T Λ Y : ℝ} (hT : 1 ≤ T) (hY : 0 < Y) {c : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hdec : ∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
      ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ)
    (j : ℕ) (hj : 1 ≤ j) {ε : ℝ} (hε : 0 < ε) (hΛ : 0 ≤ Λ) (hc : 0 ≤ c j ε) :
    ∫ y in {y : ℝ | Y ≤ |y|}, ‖Fhat f y‖ ^ 2 ≤
      2 * (c j ε * T ^ ε) ^ 2 * Λ ^ 2 * T * (T / Y) ^ (2 * j - 1) / ((2 * j : ℝ) - 1) := by
  have hT0 : (0:ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  have h2j : 1 < 2 * j := by omega
  have hIntK : IntegrableOn (fun y : ℝ => (T / |y|) ^ (2*j)) {y : ℝ | Y ≤ |y|} :=
    integrableOn_abs_div_pow hT0 hY h2j
  have hIntG : IntegrableOn
      (fun y : ℝ => (c j ε * T^ε * Λ)^2 * (T / |y|) ^ (2*j)) {y : ℝ | Y ≤ |y|} :=
    hIntK.const_mul ((c j ε * T^ε * Λ)^2)
  have hpoint : ∀ y ∈ {y : ℝ | Y ≤ |y|},
      ‖Fhat f y‖^2 ≤ (c j ε * T^ε * Λ)^2 * (T / |y|) ^ (2*j) := by
    intro y hy
    have habs : 0 < |y| := lt_of_lt_of_le hY hy
    have hyne : y ≠ 0 := by
      intro h0; rw [h0, abs_zero] at habs; exact lt_irrefl (0:ℝ) habs
    have hd := hdec j ε hε y hyne
    have hTe : (0:ℝ) < T^ε := Real.rpow_pos_of_pos hT0 ε
    have hTy : (0:ℝ) ≤ T / |y| := div_nonneg (le_of_lt hT0) (le_of_lt habs)
    have hA0 : (0:ℝ) ≤ c j ε * T^ε * (T/|y|)^j * Λ :=
      mul_nonneg (mul_nonneg (mul_nonneg hc (le_of_lt hTe)) (pow_nonneg hTy j)) hΛ
    have hsq : ‖Fhat f y‖^2 ≤ (c j ε * T^ε * (T/|y|)^j * Λ)^2 := by
      nlinarith [hd, norm_nonneg (Fhat f y), hA0]
    calc ‖Fhat f y‖^2 ≤ (c j ε * T^ε * (T/|y|)^j * Λ)^2 := hsq
      _ = (c j ε * T^ε * Λ)^2 * (T/|y|)^(2*j) := by
          rw [show (2*j:ℕ) = j*2 from Nat.mul_comm 2 j, pow_mul]
          ring
  have hmono : ∫ y in {y : ℝ | Y ≤ |y|}, ‖Fhat f y‖^2 ≤
      ∫ y in {y : ℝ | Y ≤ |y|}, (c j ε * T^ε * Λ)^2 * (T/|y|)^(2*j) :=
    setIntegral_mono_of_nonneg (fun y _ => sq_nonneg _) hpoint hIntG
  have hvalG : ∫ y in {y : ℝ | Y ≤ |y|}, (c j ε * T^ε * Λ)^2 * (T/|y|)^(2*j)
      = (c j ε * T^ε * Λ)^2 * (2 * T * (T/Y)^(2*j-1) / (((2*j:ℕ):ℝ) - 1)) := by
    rw [integral_const_mul, integral_abs_div_pow hT0 hY h2j]
  calc ∫ y in {y : ℝ | Y ≤ |y|}, ‖Fhat f y‖^2
      ≤ ∫ y in {y : ℝ | Y ≤ |y|}, (c j ε * T^ε * Λ)^2 * (T/|y|)^(2*j) := hmono
    _ = (c j ε * T^ε * Λ)^2 * (2 * T * (T/Y)^(2*j-1) / (((2*j:ℕ):ℝ) - 1)) := hvalG
    _ = 2 * (c j ε * T ^ ε) ^ 2 * Λ ^ 2 * T * (T / Y) ^ (2 * j - 1) / ((2 * j : ℝ) - 1) := by
        have htwoj : (((2*j:ℕ)):ℝ) = 2 * (j:ℝ) := by push_cast; ring
        rw [htwoj]
        ring

end

end Work.GM.Affine
