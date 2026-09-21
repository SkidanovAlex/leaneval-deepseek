import Mathlib
import Submission.Work.OddRadon.RadialDefs
import Submission.Work.Geometry.Ulam.odd_radial_reconstruction

/-!
# Existence of the radial pair for small data (`Work.OddRadon`)

The paper's odd-dimensional step solves, for every angle `α ∈ [0, π/2]`, the two-power system

  `R(α)^{2n+2} + r(α)^{2n+2} = 2 + A α`,   `R(α)^{2n+1} - r(α)^{2n+1} = B α`   (`d = 2n+1`),

where `(A, B)` is a small smooth perturbation of the ball's data `(0, 0)`, with `A, B` vanishing
at `π/2` and having vanishing first derivative at `0`.  This is nothing but the inverse function
theorem applied to the two-power map `(R,r) ↦ (R^{2n+2}+r^{2n+2}, R^{2n+1}-r^{2n+1})`, whose
differential at the ball's solution `(1,1)` is invertible.

The corresponding statement for the *divided* system is proved in
`Commons.Geometry.Ulam.spherical_radon_radial_reconstruction`.  Here we record the *cleared*
form actually used by the paper — the form encoded by `RadialSystem`, in which the two equations
are multiplied by `cos²α` and `cos α` respectively, i.e. the data `(Φ, Ψ)` are
`Φ α = (2 + A α) cos²α` and `Ψ α = B α cos α`.  Multiplication by a scalar is harmless, so the
cleared form follows at once from the divided one.

## Main result

* `radialSystem_exists` — for every `n ≥ 1` there is `ε > 0` such that every smooth
  `(A, B)` bounded by `ε` and vanishing appropriately gives a smooth radial pair `(R, r)`,
  within `1/2` of `1`, solving the cleared radial system for the perturbed data.
-/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace Pointwise Interval Topology

namespace Work.OddRadon

/-- **Existence of the radial pair for small data.**  For every `n ≥ 1` there is `ε > 0` such
that for all smooth `A, B` on `[0, π/2]`, uniformly `< ε`, with `A (π/2) = B (π/2) = 0` and
`deriv A 0 = deriv B 0 = 0`, there are smooth `R, r` on `[0, π/2]`, within `1/2` of `1`, with
`R (π/2) = r (π/2) = 1` and satisfying the cleared radial system
`RadialSystem n (fun α => (2 + A α) cos²α) (fun α => B α cos α) R r`. -/
theorem radialSystem_exists (n : ℕ) (hn : 1 ≤ n) :
    ∃ ε > 0, ∀ A B : ℝ → ℝ,
      ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) A (Set.Icc 0 (Real.pi / 2)) →
      ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) B (Set.Icc 0 (Real.pi / 2)) →
      (∀ α ∈ Set.Icc 0 (Real.pi / 2), |A α| < ε) →
      (∀ α ∈ Set.Icc 0 (Real.pi / 2), |B α| < ε) →
      A (Real.pi / 2) = 0 → B (Real.pi / 2) = 0 →
      deriv A 0 = 0 → deriv B 0 = 0 →
      ∃ R r : ℝ → ℝ,
        ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) R (Set.Icc 0 (Real.pi / 2)) ∧
        ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) r (Set.Icc 0 (Real.pi / 2)) ∧
        RadialSystem n (fun α => (2 + A α) * Real.cos α ^ 2)
          (fun α => B α * Real.cos α) R r ∧
        R (Real.pi / 2) = 1 ∧ r (Real.pi / 2) = 1 ∧
        (∀ α ∈ Set.Icc 0 (Real.pi / 2), |R α - 1| < 1 / 2 ∧ |r α - 1| < 1 / 2) := by
  -- The inverse function theorem applied to the two-power map, in divided form.
  obtain ⟨ε, hεpos, hε⟩ :=
    Commons.Geometry.Ulam.spherical_radon_radial_reconstruction n hn
  refine ⟨ε, hεpos, ?_⟩
  intro A B hA hB hAsmall hBsmall hAend hBend hAderiv hBderiv
  obtain ⟨R, r, hR, hr, hdiv, hRend, hrend, hclose⟩ :=
    hε A B hA hB hAsmall hBsmall hAend hBend hAderiv hBderiv
  refine ⟨R, r, hR, hr, ?_, hRend, hrend, hclose⟩
  -- Clear the two divisions by `cos²α` and `cos α`.
  intro α hα
  obtain ⟨h1, h2⟩ := hdiv α hα
  exact ⟨by rw [h1], by rw [h2]⟩

end Work.OddRadon
