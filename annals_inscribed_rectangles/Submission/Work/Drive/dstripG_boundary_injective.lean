import Mathlib
import Submission.Work.Drive.stripData
import Submission.Work.Drive.curve_eq_iff
import Submission.Work.Drive.dstripU_boundary_val

namespace Work.Drive

/-- **Injectivity of `dstripG` on the boundary of the strip.**  At `τ = 0` the first component of
`dstripG M W (α, 0) = (M (e^{iα}, 0), A(α, 0))` is the complexified curve point
`M (e^{iα}, 0) = symmC (curve γ α)` (`dstripU_boundary_val`).  Since `symmC` is injective
(`Prod.ext` on the two coordinates) and the parametrisation `s ↦ γ (Circle.exp s)` of a smoothly
embedded Jordan curve is injective modulo `2π` (`curve_eq_iff`), two boundary points of the strip map
to the same value exactly when their angles differ by a multiple of `2π`.

The second component `A(α, 0) = ‖M (e^{iα}, 0)‖²` is then automatically equal, so it carries no
further information and is not used. -/
theorem dstripG_boundary_injective {γ : Circle → ℝ × ℝ} {M W : ℂ × ℝ → ℂ}
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hMval : ∀ x : ℂ, ∀ τ : ℝ, 0 ≤ τ → ‖x‖ = 1 → M (x, τ) = Neutral.dataMid γ x (Real.sqrt τ)) :
    ∀ α α' : ℝ, dstripG M W (α, 0) = dstripG M W (α', 0) → ∃ k : ℤ, α - α' = 2 * Real.pi * k := by
  intro α α' h
  -- The equality of the `dstripG`-values gives the equality of the band data `M`.
  have hM : M (dstripU α, 0) = M (dstripU α', 0) := by
    have h1 := congrArg Prod.fst h
    simpa only [dstripG] using h1
  -- On the boundary `M` is the complexified curve point.
  rw [dstripU_boundary_val (γ := γ) (M := M) hMval α,
      dstripU_boundary_val (γ := γ) (M := M) hMval α'] at hM
  -- `symmC` is injective, coordinate by coordinate.
  have hcurve : curve γ α = curve γ α' := by
    refine Prod.ext ?_ ?_
    · have h1 := congrArg Complex.re hM
      simpa [Neutral.symmC] using h1
    · have h1 := congrArg Complex.im hM
      simpa [Neutral.symmC] using h1
  -- The parametrisation is injective modulo the period.
  obtain ⟨k, hk⟩ := (curve_eq_iff γ hγ α α').mp hcurve
  exact ⟨k, by linarith⟩

end Work.Drive
