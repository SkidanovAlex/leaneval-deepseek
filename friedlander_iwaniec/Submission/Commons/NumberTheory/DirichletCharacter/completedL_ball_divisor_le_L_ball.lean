import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.completedL_divisor_le_L
import Submission.Commons.NumberTheory.DirichletCharacter.zerosInStrip

open Complex DirichletCharacter Metric
open scoped Real Topology BigOperators

noncomputable section

namespace Commons.NumberTheory.DirichletCharacter

/-!
# Divisor sum of the completed L-function over a disk is at most that of the L-function

For a primitive non-trivial character `χ`, every zero of the completed L-function
`Λ(s, χ) = completedLFunction χ s` lies in the critical strip `0 < Re s < 1`
(`zerosInStrip`).  At each point of the right half-plane the archimedean Gamma
factor is analytic and zero-free, so the divisor of `Λ` there is at most the
divisor of the ordinary L-function (`completedL_divisor_le_L`); at any other
point the divisor of `Λ` vanishes.  Both divisor sums have finite support on the
closed ball (which is compact), so the pointwise inequality integrates to an
inequality of the finite sums.
-/

/-- An analytic function with a nonzero value has zero divisor coefficient. -/
private lemma divisor_eq_zero_of_analytic_ne_zero {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hAnU : AnalyticOnNhd ℂ f U) (hz : z ∈ U) (hfz : f z ≠ 0) :
    MeromorphicOn.divisor f U z = 0 := by
  rw [MeromorphicOn.divisor_apply hAnU.meromorphicOn hz]
  have hAn : AnalyticAt ℂ f z := hAnU z hz
  have hord : meromorphicOrderAt f z = 0 := by
    rw [hAn.meromorphicOrderAt_eq]
    have h0 : analyticOrderAt f z = 0 := analyticOrderAt_eq_zero.mpr (Or.inr hfz)
    simp [h0]
  simp [hord]

/-- For a primitive non-trivial `χ`, the divisor of the completed L-function on an
arbitrary set `U` is at most the divisor of the ordinary L-function on `U`, at every point. -/
private lemma completedL_divisor_le_L_pointwise {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (U : Set ℂ) :
    ∀ u : ℂ,
      MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) U u ≤
        MeromorphicOn.divisor (DirichletCharacter.LFunction χ) U u := by
  classical
  intro u
  by_cases hu : u ∈ U
  · by_cases hz : DirichletCharacter.completedLFunction χ u = 0
    · have hstrip := zerosInStrip χ hχ hχprim u hz
      exact completedL_divisor_le_L χ hχ U hu hstrip.1
    · have hd0 : MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) U u = 0 := by
        apply divisor_eq_zero_of_analytic_ne_zero (f := DirichletCharacter.completedLFunction χ)
        · intro z hzU
          exact (differentiable_completedLFunction hχ).analyticAt z
        · exact hu
        · exact hz
      rw [hd0]
      exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg
        (show AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) U from
          (fun z hzU => (differentiable_LFunction hχ).analyticAt z)) u
  · simp [hu]

/-- **Divisor sum over a disk.**  For a primitive non-trivial Dirichlet character `χ`,
the (ℝ-valued, multiplicity-weighted) sum of the divisor of the completed L-function
`completedLFunction χ` over the closed disk `closedBall a ρ` is at most the analogous sum
for the ordinary L-function `LFunction χ`.  Indeed the zeros of `Λ` all lie in the
critical strip and coincide there (multiplicity included) with zeros of `L`, while
`L`'s divisor is non-negative everywhere; the sums are finite since both functions
are analytic on the compact disk. -/
theorem completedL_ball_divisor_le_L_ball {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (a : ℂ) (ρ : ℝ) :
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall a ρ)) u : ℤ) : ℝ)) ≤
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
        (Metric.closedBall a ρ)) u : ℤ) : ℝ)) := by
  classical
  let B : Set ℂ := Metric.closedBall a ρ
  have hfinΛ : Function.HasFiniteSupport
      (fun u : ℂ => (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) B) u) := by
    dsimp [B]
    simpa [Function.HasFiniteSupport] using
      ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall a ρ)).finiteSupport (isCompact_closedBall a ρ))
  have hfinL : Function.HasFiniteSupport
      (fun u : ℂ => (MeromorphicOn.divisor (DirichletCharacter.LFunction χ) B) u) := by
    dsimp [B]
    simpa [Function.HasFiniteSupport] using
      ((MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
          (Metric.closedBall a ρ)).finiteSupport (isCompact_closedBall a ρ))
  have hpt : ∀ u : ℂ,
      (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) B) u ≤
        (MeromorphicOn.divisor (DirichletCharacter.LFunction χ) B) u := by
    simpa [B] using completedL_divisor_le_L_pointwise χ hχ hχprim B
  have hZ : (∑ᶠ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) B) u) ≤
      (∑ᶠ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.LFunction χ) B) u) := by
    exact finsum_le_finsum' hfinΛ hfinL hpt
  have hEqΛ : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) B) u : ℤ) : ℝ)) =
      ((∑ᶠ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) B) u : ℤ) : ℝ) := by
    simpa using ((Int.castRingHom ℝ).map_finsum hfinΛ).symm
  have hEqL : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.LFunction χ) B) u : ℤ) : ℝ)) =
      ((∑ᶠ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.LFunction χ) B) u : ℤ) : ℝ) := by
    simpa using ((Int.castRingHom ℝ).map_finsum hfinL).symm
  calc
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall a ρ)) u : ℤ) : ℝ))
        = ((∑ᶠ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) B) u : ℤ) : ℝ) := by
          rw [show Metric.closedBall a ρ = B by rfl]
          exact hEqΛ
    _ ≤ ((∑ᶠ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.LFunction χ) B) u : ℤ) : ℝ) := by
      exact_mod_cast hZ
    _ = (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
        (Metric.closedBall a ρ)) u : ℤ) : ℝ)) := by
      rw [show Metric.closedBall a ρ = B by rfl]
      exact hEqL.symm

end Commons.NumberTheory.DirichletCharacter
