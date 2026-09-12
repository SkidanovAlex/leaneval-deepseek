import Mathlib
import ChallengeDeps
import Submission.QCover

/-! Small degrees `2 ≤ m < m0`: handled by the explicit family
`P_m(z) := 1 − z − z^2 − ⋯ − z^m`, which has NO zeros on the unit circle for
`m ≥ 2` (paper arXiv:1907.09464v1, introduction).  PROOF: if `z ≠ 1` and
`P_m(z) = 0` then `1 = Σ_{k=1}^m z^k`; multiply by `1−z`: `z^(m+1) = 2z − 1`,
so `1 = |2z−1|`, which for `|z|=1` forces `z = 1` (compute
`|2z−1|^2 = 5 − 4·Re z`, set equal to 1), contradiction; and `z = 1` gives
value `1−m ≠ 0`.

Since the range `2 ≤ m < m0` is finite and `|P_m|` is continuous on the
compact unit circle and never zero, each degree has a positive minimum
`c_m := min_{|z|=1}|P_m(z)|`; take `δ := min_{2 ≤ m < m0} c_m/√m > 0`, which
yields the required uniform lower bound for all small `m` (upper bound:
`|P_m(z)| ≤ m+1 ≤ (m0+1)·√m` since `√m ≥ 1`).

Use `Metric.isCompact_iff_isCompact`-style API: the unit circle
`{z : ℂ | ‖z‖ = 1}` is compact (`Metric.sphere` / `Metric.isCompact_sphere`),
the function `z ↦ ‖(P_m).eval z‖` is continuous (`Continuous.norm`,
`Polynomial.continuous_eval`), and on a nonempty compact set a continuous
function attains its minimum (`IsCompact.exists_isMinOn` /
`IsCompact.exists_forall_le` + `ContinuousOn.exists_forall_le`-style lemmas;
search Mathlib).  For the finite minimum use `Finset.min'` (needs
`Finset.Nonempty`; provide it from `2 ≤ m0`). -/

noncomputable section
open scoped Polynomial BigOperators
open Polynomial Complex

set_option autoImplicit false

open FlatLittlewoodPoly

namespace Submission
namespace Small

/-- `P_m(z) = 1 − z − z^2 − ⋯ − z^m`. -/
def smallP (m : ℕ) : ℂ[X] := 1 - (∑ k ∈ Finset.range (m + 1), X ^ k) + X ^ 0

lemma smallP_coeff_zero (m : ℕ) : (smallP m).coeff 0 = (1 : ℂ) := by
  unfold smallP
  simp [Polynomial.coeff_X_pow, Polynomial.coeff_one]

lemma smallP_coeff_neg (m : ℕ) {k : ℕ} (hk1 : 1 ≤ k) (hkm : k ≤ m) :
    (smallP m).coeff k = (-1 : ℂ) := by
  unfold smallP
  have hk0 : k ≠ 0 := by omega
  simp [Polynomial.coeff_X_pow, Polynomial.coeff_one, hk0, hkm]

lemma smallP_coeff_of_gt (m : ℕ) {j : ℕ} (hj : m < j) : (smallP m).coeff j = 0 := by
  unfold smallP
  have hjm : ¬ j ≤ m := by omega
  have hj0 : j ≠ 0 := by omega
  simp [Polynomial.coeff_X_pow, Polynomial.coeff_one, hjm, hj0]

lemma smallP_natDegree (m : ℕ) : (smallP m).natDegree = m := by
  apply le_antisymm
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    exact smallP_coeff_of_gt m hN
  · by_cases hm : m = 0
    · subst m
      simp [smallP]
    · have hmpos : 1 ≤ m := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hm)
      have hcoeff : (smallP m).coeff m = (-1 : ℂ) := smallP_coeff_neg m hmpos le_rfl
      by_contra hlt
      have hndlt : (smallP m).natDegree < m := Nat.lt_of_not_ge hlt
      have hzero : (smallP m).coeff m = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hndlt
      rw [hcoeff] at hzero
      norm_num at hzero

lemma smallP_isLittlewood (m : ℕ) : IsLittlewoodPolynomial (smallP m) := by
  intro i hi
  have him : i ≤ m := by rwa [smallP_natDegree m] at hi
  by_cases hi0 : i = 0
  · subst i
    left
    exact smallP_coeff_zero m
  · right
    have hi1 : 1 ≤ i := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hi0)
    exact smallP_coeff_neg m hi1 him

/-- Coeffs are ±1 and the degree is `m`. -/
lemma smallP_littlewood (m : ℕ) : IsLittlewoodPolynomial (smallP m) ∧ (smallP m).natDegree = m := by
  constructor
  · exact smallP_isLittlewood m
  · exact smallP_natDegree m

lemma smallP_eval (m : ℕ) (z : ℂ) :
    (smallP m).eval z = 1 - (∑ k ∈ Finset.range (m + 1), z ^ k) + z ^ 0 := by
  unfold smallP
  simp

lemma smallP_eval_form (m : ℕ) (z : ℂ) :
    (smallP m).eval z = 2 - (∑ k ∈ Finset.range (m + 1), z ^ k) := by
  rw [smallP_eval]
  simp
  ring

lemma smallP_eval_one_form (m : ℕ) : (smallP m).eval (1 : ℂ) = (1 : ℂ) - (m : ℂ) := by
  rw [smallP_eval_form]
  simp
  ring

lemma smallP_eval_tail (m : ℕ) (z : ℂ) :
    (smallP m).eval z = 1 - (∑ k ∈ Finset.range m, z ^ (k + 1)) := by
  rw [smallP_eval]
  have hS : (∑ k ∈ Finset.range (m + 1), z ^ k) = (∑ k ∈ Finset.range m, z ^ (k + 1)) + 1 := by
    rw [Finset.sum_range_succ']
    simp
  rw [hS]
  ring

lemma smallP_norm_le (m : ℕ) (z : ℂ) (hz : ‖z‖ = 1) : ‖(smallP m).eval z‖ ≤ (m : ℝ) + 1 := by
  rw [smallP_eval_tail m z]
  calc
    ‖(1 : ℂ) - (∑ k ∈ Finset.range m, z ^ (k + 1))‖
        ≤ ‖(1 : ℂ)‖ + ‖∑ k ∈ Finset.range m, z ^ (k + 1)‖ := norm_sub_le _ _
    _ = 1 + ‖∑ k ∈ Finset.range m, z ^ (k + 1)‖ := by simp
    _ ≤ 1 + (∑ k ∈ Finset.range m, ‖z ^ (k + 1)‖) := by
      have hns : ‖∑ k ∈ Finset.range m, z ^ (k + 1)‖ ≤ ∑ k ∈ Finset.range m, ‖z ^ (k + 1)‖ :=
        norm_sum_le (Finset.range m) (fun k => z ^ (k + 1))
      nlinarith
    _ = 1 + (∑ _k ∈ Finset.range m, (1 : ℝ)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [norm_pow, hz]
      simp
    _ = (m : ℝ) + 1 := by
      simp
      ring

lemma eq_one_of_norm_eq_one_of_norm_two_mul_sub_one_eq_one (z : ℂ)
    (hz : ‖z‖ = 1) (h2 : ‖2 * z - 1‖ = 1) : z = 1 := by
  have hnsz : Complex.normSq z = 1 := by
    rw [Complex.normSq_eq_norm_sq, hz]
    norm_num
  have hsq : z.re ^ 2 + z.im ^ 2 = 1 := by
    have htmp : z.re * z.re + z.im * z.im = 1 := by
      simpa [Complex.normSq_apply] using hnsz
    nlinarith
  have hns2 : Complex.normSq (2 * z - 1) = 1 := by
    rw [Complex.normSq_eq_norm_sq, h2]
    norm_num
  have hexp : Complex.normSq (2 * z - 1) = 5 - 4 * z.re := by
    rw [Complex.normSq_apply]
    simp
    nlinarith [hsq]
  have hre1 : z.re = 1 := by
    have : 5 - 4 * z.re = 1 := by
      rw [← hexp]
      exact hns2
    nlinarith
  have him0 : z.im = 0 := by
    have himsq : z.im ^ 2 = 0 := by nlinarith [hsq]
    nlinarith [sq_nonneg z.im]
  exact Complex.ext (by simpa using hre1) (by simpa using him0)

/-- `P_m` has no zeros on the unit circle for `m ≥ 2`. -/
lemma smallP_root_free (m : ℕ) (hm : 2 ≤ m) (z : ℂ) (hz : ‖z‖ = 1) :
    (smallP m).eval z ≠ 0 := by
  intro hz0
  by_cases hz1 : z = 1
  · subst z
    have hval : (smallP m).eval (1 : ℂ) = (1 : ℂ) - (m : ℂ) := smallP_eval_one_form m
    rw [hval] at hz0
    have hne : (1 : ℂ) - (m : ℂ) ≠ 0 := by
      intro h
      have hre : (1 : ℝ) - (m : ℝ) = 0 := by
        have := congrArg Complex.re h
        simpa using this
      have hmreal : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      nlinarith
    exact hne hz0
  · have hev : (smallP m).eval z = 2 - (∑ k ∈ Finset.range (m + 1), z ^ k) := smallP_eval_form m z
    have hS : (∑ k ∈ Finset.range (m + 1), z ^ k) = 2 := by
      have : 2 - (∑ k ∈ Finset.range (m + 1), z ^ k) = 0 := by
        rwa [← hev]
      exact (sub_eq_zero.mp this).symm
    have hgeo : (1 - z) * (∑ k ∈ Finset.range (m + 1), z ^ k) = 1 - z ^ (m + 1) := by
      simpa using (mul_neg_geom_sum z (m + 1))
    have hmain : (1 - z) * 2 = 1 - z ^ (m + 1) := by
      calc
        (1 - z) * 2 = (1 - z) * (∑ k ∈ Finset.range (m + 1), z ^ k) := by rw [hS]
        _ = 1 - z ^ (m + 1) := hgeo
    have hlin : 2 - 2 * z = 1 - z ^ (m + 1) := by
      calc
        2 - 2 * z = (1 - z) * 2 := by ring
        _ = 1 - z ^ (m + 1) := hmain
    have hpow : z ^ (m + 1) = 2 * z - 1 := by
      calc
        z ^ (m + 1) = 1 - (1 - z ^ (m + 1)) := by ring
        _ = 1 - (2 - 2 * z) := by rw [hlin.symm]
        _ = 2 * z - 1 := by ring
    have hn1 : ‖z ^ (m + 1)‖ = 1 := by
      rw [norm_pow, hz]
      simp
    have hnorm : ‖2 * z - 1‖ = 1 := by
      rw [← hpow]
      exact hn1
    have hzeq1 : z = 1 := eq_one_of_norm_eq_one_of_norm_two_mul_sub_one_eq_one z hz hnorm
    exact hz1 hzeq1

/-- Positive minimum of `|P_m|` on the circle. -/
lemma circle_min_pos (m : ℕ) (hm : 2 ≤ m) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : ℂ, ‖z‖ = 1 → c ≤ ‖(smallP m).eval z‖ := by
  classical
  let S : Set ℂ := Metric.sphere (0 : ℂ) 1
  let f : ℂ → ℝ := fun z => ‖(smallP m).eval z‖
  have hS : IsCompact S := isCompact_sphere (0 : ℂ) 1
  have hne : S.Nonempty := ⟨(1 : ℂ), by simp [S]⟩
  have hf : ContinuousOn f S := by
    have hc : Continuous f := (Polynomial.continuous (smallP m)).norm
    exact hc.continuousOn
  rcases hS.exists_isMinOn hne hf with ⟨x, hxS, hmin⟩
  refine ⟨f x, ?_, ?_⟩
  · have hxnorm : ‖x‖ = 1 := by
      simpa [S, Metric.sphere, dist_eq_norm] using hxS
    have hne0 : (smallP m).eval x ≠ 0 := smallP_root_free m hm x hxnorm
    exact norm_pos_iff.mpr hne0
  · intro z hz
    have hzS : z ∈ S := by
      simpa [S, Metric.sphere, dist_eq_norm] using hz
    exact (isMinOn_iff.mp hmin) z hzS


noncomputable def circleMin (m : ℕ) (hm : 2 ≤ m) : ℝ :=
  Classical.choose (circle_min_pos m hm)

lemma circleMin_pos (m : ℕ) (hm : 2 ≤ m) : 0 < circleMin m hm :=
  (Classical.choose_spec (circle_min_pos m hm)).1

lemma circleMin_le (m : ℕ) (hm : 2 ≤ m) (z : ℂ) (hz : ‖z‖ = 1) :
    circleMin m hm ≤ ‖(smallP m).eval z‖ :=
  (Classical.choose_spec (circle_min_pos m hm)).2 z hz

lemma smallP_norm_le_m0 (m0 m : ℕ) (hm1 : 1 ≤ m) (hmm0 : m < m0) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖(smallP m).eval z‖ ≤ ((m0 : ℝ) + 1) * Real.sqrt (m : ℝ) := by
  have hnorm : ‖(smallP m).eval z‖ ≤ (m : ℝ) + 1 := smallP_norm_le m z hz
  have hm1m0 : (m : ℝ) + 1 ≤ (m0 : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt hmm0)
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (m : ℝ) := by
    have h1m : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have : Real.sqrt (1 : ℝ) ≤ Real.sqrt (m : ℝ) := Real.sqrt_le_sqrt h1m
    simpa using this
  have hsqrt0 : 0 ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
  have hm0nn : 0 ≤ (m0 : ℝ) := by exact_mod_cast (Nat.zero_le m0)
  have hmul : (m0 : ℝ) ≤ ((m0 : ℝ) + 1) * Real.sqrt (m : ℝ) := by
    calc
      (m0 : ℝ) = (m0 : ℝ) * 1 := by ring
      _ ≤ (m0 : ℝ) * Real.sqrt (m : ℝ) := mul_le_mul_of_nonneg_left hsqrt1 hm0nn
      _ ≤ ((m0 : ℝ) + 1) * Real.sqrt (m : ℝ) := by nlinarith [hsqrt0]
  calc
    ‖(smallP m).eval z‖ ≤ (m : ℝ) + 1 := hnorm
    _ ≤ (m0 : ℝ) := hm1m0
    _ ≤ ((m0 : ℝ) + 1) * Real.sqrt (m : ℝ) := hmul

/-- Small-degree case with a uniform lower bound: for `m0 ≥ 2` there is
`0 < δ` such that every `2 ≤ m < m0` has a Littlewood polynomial of degree
`m` bounded below by `δ·√m` (and above by `(m0+1)·√m`) on the unit circle. -/
theorem small_case (m0 : ℕ) (hm0 : 2 ≤ m0) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ m : ℕ, 2 ≤ m → m < m0 →
        ∃ P : ℂ[X], IsLittlewoodPolynomial P ∧ P.natDegree = m ∧
          ∀ z : ℂ, ‖z‖ = 1 →
            δ * Real.sqrt (m : ℝ) ≤ ‖P.eval z‖ ∧ ‖P.eval z‖ ≤ (m0 + 1) * Real.sqrt (m : ℝ) := by
  classical
  by_cases hm0le2 : m0 ≤ 2
  · refine ⟨1, by norm_num, ?_⟩
    intro m hm hm0m
    omega
  · let S : Finset ℕ := Finset.Ico 2 m0
    let f : ℕ → ℝ := fun m => if h : 2 ≤ m then circleMin m h / Real.sqrt (m : ℝ) else 0
    have hSne : S.Nonempty := by
      rw [Finset.nonempty_Ico]
      omega
    let δ : ℝ := S.inf' hSne f
    refine ⟨δ, ?_, ?_⟩
    · -- 0 < δ
      rw [Finset.lt_inf'_iff hSne]
      intro m hmS
      have h2m : 2 ≤ m := (Finset.mem_Ico.mp hmS).1
      have hf : f m = circleMin m h2m / Real.sqrt (m : ℝ) := by
        unfold f
        rw [dif_pos h2m]
      have hsqrtpos : 0 < Real.sqrt (m : ℝ) := by
        apply Real.sqrt_pos.mpr
        positivity
      rw [hf]
      exact div_pos (circleMin_pos m h2m) hsqrtpos
    · intro m hm2 hm0m
      have hmS : m ∈ S := by
        simp [S]
        exact ⟨hm2, hm0m⟩
      refine ⟨smallP m, smallP_isLittlewood m, smallP_natDegree m, ?_⟩
      intro z hz
      have hδle : δ ≤ f m := by
        change S.inf' hSne f ≤ f m
        exact Finset.inf'_le (s := S) f hmS
      have hf : f m = circleMin m hm2 / Real.sqrt (m : ℝ) := by
        unfold f
        rw [dif_pos hm2]
      have hsqrtpos : 0 < Real.sqrt (m : ℝ) := by
        apply Real.sqrt_pos.mpr
        positivity
      have hδle' : δ ≤ circleMin m hm2 / Real.sqrt (m : ℝ) := by
        rw [hf] at hδle
        exact hδle
      have hδ' : δ * Real.sqrt (m : ℝ) ≤ circleMin m hm2 := by
        calc
          δ * Real.sqrt (m : ℝ) ≤ (circleMin m hm2 / Real.sqrt (m : ℝ)) * Real.sqrt (m : ℝ) := by
            exact mul_le_mul_of_nonneg_right hδle' (Real.sqrt_nonneg _)
          _ = circleMin m hm2 := by
            rw [div_mul_cancel₀ _ (ne_of_gt hsqrtpos)]
      have hlower : δ * Real.sqrt (m : ℝ) ≤ ‖(smallP m).eval z‖ :=
        le_trans hδ' (circleMin_le m hm2 z hz)
      have hupper : ‖(smallP m).eval z‖ ≤ ((m0 : ℝ) + 1) * Real.sqrt (m : ℝ) :=
        smallP_norm_le_m0 m0 m (by omega) hm0m z hz
      exact ⟨hlower, hupper⟩

end Small
end Submission
