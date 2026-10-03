import Mathlib

/-!
# Bounds for `ξ ↦ (c * ξ)^n * u ξ`

If `u : ℝ → ℂ` is `C²` and supported in `[-R, R]`, then the function
`ξ ↦ ((c * ξ : ℝ) : ℂ) ^ n * u ξ` is again `C²` with compact support, and all of it,
its first and its second derivative are bounded by a multiple of the corresponding
derivative of `u` (with the same constant, depending only on `c`, `n`, `R`).
-/

namespace Work.KMTPlan.A6

open scoped Topology

/-- A function vanishing on the open set `{ξ | R < |ξ|}` has all its iterated
derivatives vanishing there as well. -/
private lemma iteratedDeriv_eq_zero_of_lt_abs {u : ℝ → ℂ} {R : ℝ}
    (hout : ∀ ξ : ℝ, R < |ξ| → u ξ = 0) (k : ℕ) {ξ : ℝ} (hξ : R < |ξ|) :
    iteratedDeriv k u ξ = 0 := by
  have hopen : IsOpen {x : ℝ | R < |x|} := isOpen_lt continuous_const continuous_abs
  have h : u =ᶠ[𝓝 ξ] (fun _ : ℝ => (0 : ℂ)) := by
    filter_upwards [hopen.mem_nhds hξ] with y hy
    exact hout y hy
  rw [Filter.EventuallyEq.iteratedDeriv_eq k h]
  simp

/-- Leibniz rule for the first iterated derivative, in the exact shape used below. -/
private lemma iteratedDeriv_one_mul (F G : ℝ → ℂ) (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G)
    (x : ℝ) :
    iteratedDeriv 1 (F * G) x = F x * iteratedDeriv 1 G x + iteratedDeriv 1 F x * G x := by
  rw [iteratedDeriv_mul hF.contDiffAt hG.contDiffAt]
  simp [Finset.sum_range_succ]

/-- Leibniz rule for the second iterated derivative, in the exact shape used below. -/
private lemma iteratedDeriv_two_mul (F G : ℝ → ℂ) (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G)
    (x : ℝ) :
    iteratedDeriv 2 (F * G) x
      = F x * iteratedDeriv 2 G x + 2 * (iteratedDeriv 1 F x * iteratedDeriv 1 G x)
        + iteratedDeriv 2 F x * G x := by
  rw [iteratedDeriv_mul (n := 2) hF.contDiffAt hG.contDiffAt]
  simp [Finset.sum_range_succ]
  ring


/-- The triangle inequality for three terms. -/
private lemma norm_add3_le (a b c : ℂ) : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
  have h1 : ‖a + b + c‖ ≤ ‖a + b‖ + ‖c‖ := norm_add_le _ _
  have h2 : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le _ _
  linarith

theorem natPow_mul_bounds (u : ℝ → ℂ) (hu : ContDiff ℝ 2 u) (hcs : HasCompactSupport u)
    {R : ℝ} (hR : 0 ≤ R) (hout : ∀ ξ : ℝ, R < |ξ| → u ξ = 0) (c : ℝ) (n : ℕ) :
    ContDiff ℝ 2 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ n * u ξ) ∧
    HasCompactSupport (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ n * u ξ) ∧
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ ξ : ℝ, ‖((c * ξ : ℝ) : ℂ) ^ n * u ξ‖ ≤ K * ‖u ξ‖) ∧
      (∀ ξ : ℝ, ‖iteratedDeriv 1 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ n * u ξ) ξ‖ ≤
        K * (‖u ξ‖ + ‖iteratedDeriv 1 u ξ‖)) ∧
      (∀ ξ : ℝ, ‖iteratedDeriv 2 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ n * u ξ) ξ‖ ≤
        K * (‖u ξ‖ + ‖iteratedDeriv 1 u ξ‖ + ‖iteratedDeriv 2 u ξ‖)) := by
  have hv : ContDiff ℝ 2 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ n) := by
    have h1 : ContDiff ℝ (2 : ℕ∞) (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)
    exact h1.pow n
  have hv1 : ContDiff ℝ 1 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ n) := hv.of_le (by norm_num)
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hform1 : ∀ x : ℝ, iteratedDeriv 1 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ n * u ξ) x
      = ((c * x : ℝ) : ℂ) ^ n * iteratedDeriv 1 u x
        + iteratedDeriv 1 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ n) x * u x :=
    fun x => iteratedDeriv_one_mul (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ n) u hv1 hu1 x
  have hform2 : ∀ x : ℝ, iteratedDeriv 2 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ n * u ξ) x
      = ((c * x : ℝ) : ℂ) ^ n * iteratedDeriv 2 u x
        + 2 * (iteratedDeriv 1 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ n) x * iteratedDeriv 1 u x)
        + iteratedDeriv 2 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ n) x * u x :=
    fun x => iteratedDeriv_two_mul (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ n) u hv hu x
  refine ⟨hv.mul hu, HasCompactSupport.mul_left hcs, ?_⟩
  obtain ⟨A0, hA0⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc (-R) R)
    hv.continuous.continuousOn
  obtain ⟨A1, hA1⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc (-R) R)
    (hv1.continuous_iteratedDeriv' 1).continuousOn
  obtain ⟨A2, hA2⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc (-R) R)
    (hv.continuous_iteratedDeriv' 2).continuousOn
  have hmem : ∀ {x : ℝ}, |x| ≤ R → x ∈ Set.Icc (-R) R := by
    intro x hx
    rw [Set.mem_Icc]
    exact abs_le.mp hx
  let M : ℝ := max 1 (max A0 (max A1 A2))
  have hM0 : 0 ≤ M := le_trans zero_le_one (le_max_left _ _)
  have hMA0 : A0 ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
  have hMA1 : A1 ≤ M :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hMA2 : A2 ≤ M :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have h2M0 : 0 ≤ 2 * M := by linarith
  refine ⟨2 * M, h2M0, ?_, ?_, ?_⟩
  · intro ξ
    rcases le_or_gt |ξ| R with hle | hlt
    · have hb : ‖((c * ξ : ℝ) : ℂ) ^ n‖ ≤ A0 := by
        simpa using hA0 ξ (hmem hle)
      calc ‖((c * ξ : ℝ) : ℂ) ^ n * u ξ‖
          = ‖((c * ξ : ℝ) : ℂ) ^ n‖ * ‖u ξ‖ := norm_mul _ _
        _ ≤ A0 * ‖u ξ‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg _)
        _ ≤ (2 * M) * ‖u ξ‖ :=
            mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    · have hu0 : u ξ = 0 := hout ξ hlt
      simp [hu0]
  · intro ξ
    rcases le_or_gt |ξ| R with hle | hlt
    · have hb0 : ‖((c * ξ : ℝ) : ℂ) ^ n‖ ≤ A0 := by
        simpa using hA0 ξ (hmem hle)
      have hb1 : ‖iteratedDeriv 1 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ n) ξ‖ ≤ A1 :=
        hA1 ξ (hmem hle)
      rw [hform1 ξ]
      calc ‖((c * ξ : ℝ) : ℂ) ^ n * iteratedDeriv 1 u ξ
              + iteratedDeriv 1 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ n) ξ * u ξ‖
          ≤ ‖((c * ξ : ℝ) : ℂ) ^ n * iteratedDeriv 1 u ξ‖
              + ‖iteratedDeriv 1 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ n) ξ * u ξ‖ :=
            norm_add_le _ _
        _ = ‖((c * ξ : ℝ) : ℂ) ^ n‖ * ‖iteratedDeriv 1 u ξ‖
              + ‖iteratedDeriv 1 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ n) ξ‖ * ‖u ξ‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ A0 * ‖iteratedDeriv 1 u ξ‖ + A1 * ‖u ξ‖ :=
            add_le_add (mul_le_mul_of_nonneg_right hb0 (norm_nonneg _))
              (mul_le_mul_of_nonneg_right hb1 (norm_nonneg _))
        _ ≤ (2 * M) * (‖u ξ‖ + ‖iteratedDeriv 1 u ξ‖) := by
            have e1 : A0 * ‖iteratedDeriv 1 u ξ‖ ≤ (2 * M) * ‖iteratedDeriv 1 u ξ‖ :=
              mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
            have e2 : A1 * ‖u ξ‖ ≤ (2 * M) * ‖u ξ‖ :=
              mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
            nlinarith [e1, e2]
    · have hu0 : u ξ = 0 := hout ξ hlt
      have hu1 : iteratedDeriv 1 u ξ = 0 := iteratedDeriv_eq_zero_of_lt_abs hout 1 hlt
      rw [hform1 ξ, hu0, hu1]
      simp
  · intro ξ
    rcases le_or_gt |ξ| R with hle | hlt
    · have hb0 : ‖((c * ξ : ℝ) : ℂ) ^ n‖ ≤ A0 := by
        simpa using hA0 ξ (hmem hle)
      have hb1 : ‖iteratedDeriv 1 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ n) ξ‖ ≤ A1 :=
        hA1 ξ (hmem hle)
      have hb2 : ‖iteratedDeriv 2 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ n) ξ‖ ≤ A2 :=
        hA2 ξ (hmem hle)
      rw [hform2 ξ]
      have hA : ‖((c * ξ : ℝ) : ℂ) ^ n * iteratedDeriv 2 u ξ‖
          ≤ A0 * ‖iteratedDeriv 2 u ξ‖ := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right hb0 (norm_nonneg _)
      have hB : ‖(2 : ℂ) * (iteratedDeriv 1 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ n) ξ
            * iteratedDeriv 1 u ξ)‖ ≤ 2 * (A1 * ‖iteratedDeriv 1 u ξ‖) := by
        have hinner : ‖iteratedDeriv 1 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ n) ξ
            * iteratedDeriv 1 u ξ‖ ≤ A1 * ‖iteratedDeriv 1 u ξ‖ := by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right hb1 (norm_nonneg _)
        calc ‖(2 : ℂ) * (iteratedDeriv 1 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ n) ξ
              * iteratedDeriv 1 u ξ)‖
            = ‖(2 : ℂ)‖ * ‖iteratedDeriv 1 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ n) ξ
                * iteratedDeriv 1 u ξ‖ := norm_mul _ _
          _ = 2 * ‖iteratedDeriv 1 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ n) ξ
                * iteratedDeriv 1 u ξ‖ := by rw [Complex.norm_ofNat]
          _ ≤ 2 * (A1 * ‖iteratedDeriv 1 u ξ‖) :=
              mul_le_mul_of_nonneg_left hinner (by norm_num)
      have hC : ‖iteratedDeriv 2 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ n) ξ * u ξ‖
          ≤ A2 * ‖u ξ‖ := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right hb2 (norm_nonneg _)
      have key : ‖((c * ξ : ℝ) : ℂ) ^ n * iteratedDeriv 2 u ξ
              + 2 * (iteratedDeriv 1 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ n) ξ
                  * iteratedDeriv 1 u ξ)
              + iteratedDeriv 2 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ n) ξ * u ξ‖
            ≤ (A0 * ‖iteratedDeriv 2 u ξ‖ + 2 * (A1 * ‖iteratedDeriv 1 u ξ‖))
              + A2 * ‖u ξ‖ := by
        have htri := norm_add3_le (((c * ξ : ℝ) : ℂ) ^ n * iteratedDeriv 2 u ξ)
          (2 * (iteratedDeriv 1 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ n) ξ
            * iteratedDeriv 1 u ξ))
          (iteratedDeriv 2 (fun ξ : ℝ => ((c * ξ : ℝ) : ℂ) ^ n) ξ * u ξ)
        linarith [htri, hA, hB, hC]
      refine key.trans ?_
      have e1 : A0 * ‖iteratedDeriv 2 u ξ‖ ≤ (2 * M) * ‖iteratedDeriv 2 u ξ‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      have e2 : 2 * (A1 * ‖iteratedDeriv 1 u ξ‖) ≤ (2 * M) * ‖iteratedDeriv 1 u ξ‖ := by
        rw [show (2 : ℝ) * (A1 * ‖iteratedDeriv 1 u ξ‖)
              = (2 * A1) * ‖iteratedDeriv 1 u ξ‖ by ring]
        exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      have e3 : A2 * ‖u ξ‖ ≤ (2 * M) * ‖u ξ‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      nlinarith [e1, e2, e3]
    · have hu0 : u ξ = 0 := hout ξ hlt
      have hu1 : iteratedDeriv 1 u ξ = 0 := iteratedDeriv_eq_zero_of_lt_abs hout 1 hlt
      have hu2 : iteratedDeriv 2 u ξ = 0 := iteratedDeriv_eq_zero_of_lt_abs hout 2 hlt
      rw [hform2 ξ, hu0, hu1, hu2]
      simp

end Work.KMTPlan.A6
