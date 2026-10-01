import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Order.CompletePartialOrder

namespace Commons.NumberTheory.Linnik

open Complex

/-- If `ρ` is a zero of the completed `L`-function of a non-principal Dirichlet character `χ`
lying in the window `‖1 + (Im s) i - ρ‖ ≤ δ`, if the integral over `ρ` is non-negative, and if
every *other* window zero `u` satisfies `Re u ≤ Re s`, then the single integral over `ρ` is
dominated by the window sum of the integrals over all window zeros, weighted by their
multiplicities.

The key points are that, the character being non-principal, the completed `L`-function is
entire, so all divisor multiplicities are non-negative (`hχ`), that the term at `ρ` is at least
the left-hand side (`hρnn` plus multiplicity `≥ 1`), and that all *other* summands are
non-negative: multiplicities are non-negative and the integral is non-negative because
`(s - u) * L` has non-negative real part, so `hF` applies. -/
theorem le_windowSum_of_mem_ne {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {f : ℝ → ℝ}
    {x₀ L : ℝ} {s ρ : ℂ} {δ : ℝ} (hL : 0 ≤ L)
    (hF : ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
    (hdiv : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|s.im| + 2))) ρ ≠ 0)
    (hwin : ‖(1:ℂ) + (s.im : ℂ) * Complex.I - ρ‖ ≤ δ)
    (hρnn : 0 ≤ ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - ρ) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re))
    (hzero : ∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|s.im| + 2))) u ≠ 0 →
        ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ → u ≠ ρ → u.re ≤ s.re) :
    ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - ρ) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
      ≤ ∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
        (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then
          ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
          else 0) := by
  classical
  -- The completed `L`-function of a non-principal character is entire, hence its divisor
  -- is non-negative on the ball.
  have han : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall 0 (|s.im| + 2)) :=
    fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  have hDnn : ∀ u : ℂ, (0:ℤ) ≤ (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall 0 (|s.im| + 2))) u := fun u =>
    (MeromorphicOn.AnalyticOnNhd.divisor_nonneg han) u
  let T : ℂ → ℝ := fun u =>
    ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
      (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then
        ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
        else 0)
  change ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - ρ) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
      ≤ ∑ᶠ u : ℂ, T u
  -- `Re ((s - u) L) ≥ 0` whenever `Re u ≤ Re s`.
  have hzshift : ∀ u : ℂ, u.re ≤ s.re → 0 ≤ (((s - u) * L : ℂ)).re := by
    intro u hu
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    have : 0 ≤ (s - u).re := by rw [Complex.sub_re]; linarith
    exact mul_nonneg this hL
  -- All summands are non-negative.
  have hTnn : ∀ u : ℂ, 0 ≤ T u := by
    intro u
    simp only [T]
    by_cases hu : u = ρ
    · -- the term at `ρ` is handled by `hρnn` and the non-negative multiplicity
      rw [hu, if_pos hwin]
      exact mul_nonneg (by exact_mod_cast hDnn ρ) hρnn
    · by_cases hdu : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 (|s.im| + 2))) u = 0
      · rw [hdu]
        norm_num
      · by_cases hw : ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ
        · rw [if_pos hw]
          refine mul_nonneg ?_ ?_
          · exact_mod_cast hDnn u
          · exact hF ((s - u) * L) (hzshift u (hzero u hdu hw hu))
        · rw [if_neg hw, mul_zero]
  -- The single term at `ρ` dominates the left-hand side.
  have hTρ : ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - ρ) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
      ≤ T ρ := by
    simp only [T]
    rw [if_pos hwin]
    have hDgeZ : (1:ℤ) ≤ (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|s.im| + 2))) ρ := by
      have h0 := hDnn ρ
      omega
    have hDge : (1:ℝ) ≤ ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|s.im| + 2))) ρ : ℤ) := by exact_mod_cast hDgeZ
    calc ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - ρ) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
        = 1 * ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - ρ) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re) := by ring
      _ ≤ ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 (|s.im| + 2))) ρ : ℤ) *
          ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - ρ) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re) :=
          mul_le_mul_of_nonneg_right hDge hρnn
  -- `T` is finitely supported, since its support is contained in that of the divisor.
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
  rcases eq_or_lt_of_le (hTnn ρ) with h0 | h0
  · -- `T ρ = 0`: use that the whole sum is non-negative.
    exact le_trans hTρ (le_trans (le_of_eq h0.symm) (finsum_nonneg hTnn))
  · -- `T ρ > 0`: the sum over the (finite) support contains the term `ρ`.
    have hmem : ρ ∈ Function.support T := Function.mem_support.mpr (ne_of_gt h0)
    have heq := finsum_eq_sum_of_support_subset T (s := hTfin.toFinset)
      (fun x hx => hTfin.mem_toFinset.mpr hx)
    rw [heq]
    exact le_trans hTρ (Finset.single_le_sum (fun i _ => hTnn i) (hTfin.mem_toFinset.mpr hmem))

end Commons.NumberTheory.Linnik
