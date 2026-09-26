import Mathlib
import Submission.Work.Drive.Mono.Band.HeightGoodDefs
import Submission.Work.Drive.EpsForm.goodHeight_exists

namespace Work.Drive.Mono.Band

open LeanEval.KnotTheory.PardonDistortion

noncomputable section

/-! ## Periodicity of the height and of its derivative -/

/-- The height `heightIn ψ n` is invariant under translations of the `2π`-lattice. -/
theorem heightIn_add_shift (ψ : Submission.Diffeo) (n : R3) (K M : ℤ) (q : ℝ × ℝ) :
    heightIn ψ n (q + ((K : ℝ) * (2 * Real.pi), (M : ℝ) * (2 * Real.pi))) = heightIn ψ n q := by
  simpa only [heightIn, Work.Drive.EpsForm.heightOf] using
    Work.Drive.EpsForm.heightOf_add_shift ψ n K M q

/-- The derivative of the height is invariant under translations of the `2π`-lattice. -/
theorem fderiv_heightIn_add_shift (ψ : Submission.Diffeo) (n : R3) (K M : ℤ) (p : ℝ × ℝ) :
    fderiv ℝ (heightIn ψ n) (p + ((K : ℝ) * (2 * Real.pi), (M : ℝ) * (2 * Real.pi)))
      = fderiv ℝ (heightIn ψ n) p :=
  Work.Drive.EpsForm.fderiv_periodic_add' (h := heightIn ψ n)
    (c := ((K : ℝ) * (2 * Real.pi), (M : ℝ) * (2 * Real.pi)))
    (fun q => (heightIn_contDiff_two ψ n).differentiable (by norm_num) q)
    (fun q => heightIn_add_shift ψ n K M q) p

/-- **Branches of the critical points of the height are equivariant under the period lattice.**
(Namespace `Work.Drive.Mono.Band`, file `Submission/Work/Drive/Mono/Band/branch_lattice_shift.lean`,
importing `Submission.Work.Drive.Mono.Band.HeightGoodDefs` and
`Submission.Work.Drive.EpsForm.goodHeight_exists`.)

`y x` is a branch of critical points of the height in direction `n` near the base direction `n₀`,
with `y x n₀ = x`, unique in the ball of radius `ε` around `x` (`huniq`), staying within that ball
for `‖n - n₀‖ < δ` (`hclose`).  If the base points `x, x'` differ by a period `(2πK, 2πM)` of the
parametrisation, then the branches differ by the same period: `y x' n = y x n + (2πK, 2πM)`.

Proof: `q := y x n + (2πK, 2πM)` is a critical point of the height in direction `n` (the height and
its derivative are invariant under the period lattice) and `‖q - x'‖ = ‖y x n - x‖ < ε`, so
`q = y x' n` by uniqueness. -/
theorem branch_lattice_shift (ψ : Submission.Diffeo)
    (n₀ : LeanEval.KnotTheory.PardonDistortion.R3) (X : Finset (ℝ × ℝ))
    (y : ℝ × ℝ → LeanEval.KnotTheory.PardonDistortion.R3 → ℝ × ℝ) (ε δ : ℝ)
    (hy0 : ∀ x ∈ X, y x n₀ = x)
    (hcrit : ∀ x ∈ X, ∀ n : LeanEval.KnotTheory.PardonDistortion.R3, ‖n - n₀‖ < δ →
      fderiv ℝ (Work.Drive.Mono.Band.heightIn ψ n) (y x n) = 0)
    (huniq : ∀ x ∈ X, ∀ n : LeanEval.KnotTheory.PardonDistortion.R3, ‖n - n₀‖ < δ →
      ∀ p : ℝ × ℝ, ‖p - x‖ < ε →
      fderiv ℝ (Work.Drive.Mono.Band.heightIn ψ n) p = 0 → p = y x n)
    (hclose : ∀ x ∈ X, ∀ n : LeanEval.KnotTheory.PardonDistortion.R3, ‖n - n₀‖ < δ →
      ‖y x n - x‖ < ε)
    {x x' : ℝ × ℝ} (hx : x ∈ X) (hx' : x' ∈ X) (K M : ℤ)
    (hshift : x' = x + ((K : ℝ) * (2 * Real.pi), (M : ℝ) * (2 * Real.pi))) :
    ∀ n : LeanEval.KnotTheory.PardonDistortion.R3, ‖n - n₀‖ < δ →
      y x' n = y x n + ((K : ℝ) * (2 * Real.pi), (M : ℝ) * (2 * Real.pi)) := by
  intro n hn
  have hnorm : ‖y x n + ((K : ℝ) * (2 * Real.pi), (M : ℝ) * (2 * Real.pi)) - x'‖ < ε := by
    have hkey : y x n + ((K : ℝ) * (2 * Real.pi), (M : ℝ) * (2 * Real.pi)) - x'
        = y x n - x := by
      rw [hshift]
      abel
    rw [hkey]
    exact hclose x hx n hn
  have hcrit' : fderiv ℝ (heightIn ψ n)
      (y x n + ((K : ℝ) * (2 * Real.pi), (M : ℝ) * (2 * Real.pi))) = 0 := by
    rw [fderiv_heightIn_add_shift ψ n K M (y x n)]
    exact hcrit x hx n hn
  exact (huniq x' hx' n hn (y x n + ((K : ℝ) * (2 * Real.pi), (M : ℝ) * (2 * Real.pi)))
    hnorm hcrit').symm

end

end Work.Drive.Mono.Band
