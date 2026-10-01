import Mathlib
import Submission.Work.NumberTheory.Linnik.scratch_wsadd

open Complex DirichletCharacter Metric Filter Set Topology MeasureTheory
open scoped Real Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.ZeroFreeTables.Table4

/-- **The two-term window bound of HB (6.15), multiplicity `≥ 1` form.**

Variant of `Commons.NumberTheory.Linnik.le_windowSum_of_mem_add` in which the second window zero
`σ` is only required to have divisor multiplicity `≥ 1` (instead of `= 1`); the price is the extra
hypothesis `hσnn` that the window contribution of `σ` is non-negative.  The proof is that of
`le_windowSum_of_mem_add`: the summands `T u` are non-negative, `T ρ` dominates the contribution
of `ρ`, and `T σ ≥ (contribution of σ)` because the multiplicity of `σ` is `≥ 1` and the
contribution of `σ` is non-negative. -/
theorem windowSumGe {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {f : ℝ → ℝ} {x₀ L C : ℝ} {s ρ σ : ℂ} {δ : ℝ} (hL : 0 ≤ L)
    (hF : ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
    (hρσ : ρ ≠ σ) (hCnn : 0 ≤ C)
    (hdivρ : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|s.im| + 2))) ρ ≠ 0)
    (hwinρ : ‖(1:ℂ) + (s.im : ℂ) * Complex.I - ρ‖ ≤ δ)
    (hρnn : 0 ≤ (∫ t in (0:ℝ)..x₀,
        Complex.exp (-(((s - ρ) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
    (hmultσ : (1 : ℤ) ≤ (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|s.im| + 2))) σ)
    (hσnn : 0 ≤ (∫ t in (0:ℝ)..x₀,
        Complex.exp (-(((s - σ) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
    (hcase : ‖(1:ℂ) + (s.im : ℂ) * Complex.I - σ‖ ≤ δ ∨
        (∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - σ) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re ≤ C)
    (hzero : ∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|s.im| + 2))) u ≠ 0 →
        ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ → u ≠ ρ → u ≠ σ → u.re ≤ s.re) :
    (∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - ρ) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re
      + (∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - σ) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re - C
      ≤ ∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
        (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then
          ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
          else 0) := by
  classical
  have han : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall 0 (|s.im| + 2)) :=
    fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  have hDnn : ∀ u : ℂ, (0:ℤ) ≤ (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall 0 (|s.im| + 2))) u := fun u =>
    (MeromorphicOn.AnalyticOnNhd.divisor_nonneg han) u
  let T : ℂ → ℝ := fun u => ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
      (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then
        ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
        else 0)
  change (∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - ρ) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re
      + (∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - σ) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re - C
      ≤ ∑ᶠ u : ℂ, T u
  have hzshift : ∀ u : ℂ, u.re ≤ s.re → 0 ≤ (((s - u) * L : ℂ)).re := by
    intro u hu
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    have : 0 ≤ (s - u).re := by rw [Complex.sub_re]; linarith
    exact mul_nonneg this hL
  have hTnnu : ∀ u : ℂ, u ≠ ρ → u ≠ σ → 0 ≤ T u := by
    intro u huρ huσ
    simp only [T]
    by_cases hdu : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|s.im| + 2))) u = 0
    · rw [hdu]; norm_num
    · by_cases hw : ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ
      · rw [if_pos hw]
        refine mul_nonneg ?_ ?_
        · exact_mod_cast hDnn u
        · exact hF ((s - u) * L) (hzshift u (hzero u hdu hw huρ huσ))
      · rw [if_neg hw, mul_zero]
  have hDρ : (1:ℤ) ≤ (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall 0 (|s.im| + 2))) ρ := by
    have h0 := hDnn ρ
    omega
  have hTρ : (∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - ρ) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re
      ≤ T ρ := by
    simp only [T]
    rw [if_pos hwinρ]
    have hDge : (1:ℝ) ≤ ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|s.im| + 2))) ρ : ℤ) := by exact_mod_cast hDρ
    calc (∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - ρ) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re
        = 1 * (∫ t in (0:ℝ)..x₀,
            Complex.exp (-(((s - ρ) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hDge hρnn
  have hTσ : (∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - σ) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re
      ≤ T σ + C := by
    rcases hcase with hw | hle
    · simp only [T]
      rw [if_pos hw]
      have hDgeZ : (1:ℤ) ≤ (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 (|s.im| + 2))) σ := hmultσ
      have hDge : (1:ℝ) ≤ ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 (|s.im| + 2))) σ : ℤ) := by exact_mod_cast hDgeZ
      have hstep : (∫ t in (0:ℝ)..x₀,
            Complex.exp (-(((s - σ) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re
          ≤ ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.closedBall 0 (|s.im| + 2))) σ : ℤ) *
            (∫ t in (0:ℝ)..x₀,
              Complex.exp (-(((s - σ) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re := by
        have := mul_le_mul_of_nonneg_right hDge hσnn
        simpa using this
      linarith
    · simp only [T]
      by_cases hw : ‖(1:ℂ) + (s.im : ℂ) * Complex.I - σ‖ ≤ δ
      · rw [if_pos hw]
        have hprod : 0 ≤ ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 (|s.im| + 2))) σ : ℤ) *
              (∫ t in (0:ℝ)..x₀,
                Complex.exp (-(((s - σ) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re :=
          mul_nonneg (by exact_mod_cast (hDnn σ)) hσnn
        linarith
      · rw [if_neg hw, mul_zero]; linarith
  have hTfin : (Function.support T).Finite := by
    have hDfin : (Function.support (fun u : ℂ => MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ) (Metric.closedBall 0 (|s.im| + 2)) u)).Finite :=
      MeromorphicOn.divisor_support_finite_of_subset
        (f := DirichletCharacter.completedLFunction χ)
        (U := Metric.closedBall (0:ℂ) (|s.im| + 2))
        (V := Metric.closedBall (0:ℂ) (|s.im| + 2))
        (fun z _ => ((DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z).meromorphicAt)
        (isCompact_closedBall 0 (|s.im| + 2)) (subset_refl _)
    refine hDfin.subset ?_
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro h0
    apply hu
    simp only [T]
    rw [h0]
    norm_num
  have hsum : T ρ + T σ ≤ ∑ᶠ u : ℂ, T u := by
    set S : Finset ℂ := hTfin.toFinset ∪ {ρ, σ} with hS
    have hSfin : ∑ u ∈ hTfin.toFinset, T u = ∑ u ∈ S, T u := by
      refine Finset.sum_subset Finset.subset_union_left ?_
      intro u hu hnu
      exact Function.notMem_support.mp (fun hc => hnu (hTfin.mem_toFinset.mpr hc))
    have hpair : ({ρ, σ} : Finset ℂ) ⊆ S := Finset.subset_union_right
    have hnn : ∀ u ∈ S, u ∉ ({ρ, σ} : Finset ℂ) → 0 ≤ T u := by
      intro u _ hnu
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnu
      exact hTnnu u hnu.1 hnu.2
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hpair hnn
    rw [Finset.sum_pair hρσ] at hle
    rw [← hSfin] at hle
    rw [← finsum_eq_sum_of_support_subset T (s := hTfin.toFinset)
      (fun x hx => hTfin.mem_toFinset.mpr hx)] at hle
    exact hle
  linarith [hTρ, hTσ, hsum]

end Work.ZeroFreeTables.Table4
