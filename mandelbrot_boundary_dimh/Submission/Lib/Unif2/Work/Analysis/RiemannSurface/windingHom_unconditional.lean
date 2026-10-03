import Submission.Lib.Unif2.Work.Analysis.RiemannSurface.isEvenlyCovered_logProj
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.windingHomFromLogCover

/-!
# The winding homomorphism of a nowhere-vanishing continuous function, unconditionally

Let `Y` be a connected topological space and `ℓ : Y → ℂ` continuous with `ℓ y ≠ 0` everywhere.  The
*winding homomorphism* of `ℓ` is the integer-valued homomorphism
`W : π₁(Y,y₀) →+ ℤ` read off the monodromy of the log cover of `ℓ`:

  `monodromy_γ (y₀, w₀) = (y₀, w₀ + W γ · 2πi)`.

The tree proves the assembly (`Work.SimplyConnected.ABS.exists_windingHom`, in
`Submission/Work/SimplyConnected/ABS/windingHomFromLogCover.lean`) with the covering property of the
log cover passed as the hypothesis `hcov : IsCoveringMap (logProj ℓ)`; that file is otherwise
sorry-free.  This module *discharges that hypothesis* with
`Work.Analysis.RiemannSurface.isCoveringMap_logProj` (the logarithmic étale space of a
nowhere-vanishing continuous function is a covering space), so that the winding homomorphism is
available with no `sorry` in its closure.

This is the topological half of the "winding/licitness" route of
`NOTES_divisor_chapter_plan.md` §26.6--§26.7: the integer `W γ` is the winding number of `γ` about
the puncture `x₀` (for `Y = X ∖ {x₀}` and `ℓ` the linking map), and the identification
`greenPeriodHom = 2π · W` is the remaining analytic content of
`Work.SimplyConnected.ABS.exists_integerValued_greenPeriodHom`.
-/

open scoped Manifold ContDiff Topology

noncomputable section

open Classical

namespace Work.Analysis.RiemannSurface

open Work.SimplyConnected.ABS

variable {Y : Type*} [TopologicalSpace Y] [ConnectedSpace Y]

/-- **The winding homomorphism of a nowhere-vanishing continuous function.**  The monodromy of the
log cover of `ℓ` around a loop `γ` at `y₀` shifts the `ℂ`-coordinate of the lift `(y₀,w₀)` by
`2πi · W γ`, with `W : π₁(Y,y₀) →+ ℤ` additive.

The covering hypothesis of `Work.SimplyConnected.ABS.exists_windingHom` is discharged by
`Work.Analysis.RiemannSurface.isCoveringMap_logProj`, so this statement has no `sorry` in its
closure. -/
theorem exists_windingHom_of_continuous (ℓ : Y → ℂ) (hℓ : Continuous ℓ) (hne : ∀ y, ℓ y ≠ 0)
    (y₀ : Y) (w₀ : ℂ) (hw₀ : Complex.exp w₀ = ℓ y₀) :
    ∃ W : Additive (FundamentalGroup Y y₀) →+ ℤ,
      ∀ γ : FundamentalGroup Y y₀,
        logCoord ℓ
            ((isCoveringMap_logProj ℓ hℓ hne).monodromy γ (logPt ℓ y₀ w₀ hw₀)).1
          = w₀ + (W (Additive.ofMul γ) : ℂ) * (2 * Real.pi * Complex.I) :=
  Work.SimplyConnected.ABS.exists_windingHom ℓ hℓ hne y₀ w₀ hw₀
    (isCoveringMap_logProj ℓ hℓ hne)

/-- **Every loop of `Y` lifts to a shift of `w₀` by an integer multiple of `2πi`** — the form of
`exists_windingHom_of_continuous` in which only the *existence* of the integer is used. -/
theorem exists_int_shift_of_monodromy (ℓ : Y → ℂ) (hℓ : Continuous ℓ) (hne : ∀ y, ℓ y ≠ 0)
    (y₀ : Y) (w₀ : ℂ) (hw₀ : Complex.exp w₀ = ℓ y₀) (γ : FundamentalGroup Y y₀) :
    ∃ n : ℤ,
      logCoord ℓ
          ((isCoveringMap_logProj ℓ hℓ hne).monodromy γ (logPt ℓ y₀ w₀ hw₀)).1
        = w₀ + (n : ℂ) * (2 * Real.pi * Complex.I) := by
  obtain ⟨W, hW⟩ := exists_windingHom_of_continuous ℓ hℓ hne y₀ w₀ hw₀
  exact ⟨W (Additive.ofMul γ), hW γ⟩

end Work.Analysis.RiemannSurface
