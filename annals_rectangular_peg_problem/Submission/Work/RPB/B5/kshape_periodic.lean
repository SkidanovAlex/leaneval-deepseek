import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B5.kappaDefs

/-!
# B5: `2π`-periodicity of the glued shape `kshape`

`kshape` is assembled from three ingredients, each `2π`-periodic in the curve parameter `t`
under the hypotheses of the statement (periodicity of the chart `W` in the angle variable,
periodicity of the level inverse `ρh` in `t`, and the `2π`-periodicity of the curve family
`CI.c`):

* `knear` — the chart part `uproj (W τ t (ρh τ t σ'))`: shifting `t` by `2π` fixes `ρh`
  (`hρhper`), moves `W` by `Tk 1` (`hWper`), and `uproj` is invariant under `Tk`
  (`Work.RPV.uproj_Tk`); the `τ = 0` correction uses `ktarg`, which is `2π`-periodic in `t`
  because `Complex.exp` is (`Complex.exp_periodic`);
* `kfsh` — the far family `krd σ * CI.c _ (t + kphc δ k σ)`, periodic by `CI.per`.

Assembling these gives the periodicity of the glued shape; the blend cutoff `kblf δ σ` does not
depend on `t`.
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-- The target circle `ktarg` is `2π`-periodic in its angle variable `t`. -/
theorem ktarg_periodic (δ : ℝ) (k : ℤ) (σ t : ℝ) :
    ktarg δ k σ (t + 2 * Real.pi) = ktarg δ k σ t := by
  unfold ktarg
  have h : ((t + 2 * Real.pi : ℝ) : ℂ) + ((kphc δ k σ : ℝ) : ℂ)
      = ((t : ℂ) + ((kphc δ k σ : ℝ) : ℂ)) + 2 * (Real.pi : ℂ) := by
    push_cast; ring
  rw [h]
  have h2 : (((t : ℂ) + ((kphc δ k σ : ℝ) : ℂ)) + 2 * (Real.pi : ℂ)) * Complex.I
      = (((t : ℂ) + ((kphc δ k σ : ℝ) : ℂ)) * Complex.I) + 2 * (Real.pi : ℂ) * Complex.I := by
    ring
  rw [h2, Complex.exp_periodic]

/-- The far family `kfsh` is `2π`-periodic in `t`: it is the curve family `CI.c` reparametrised
by an affine function of `t` of slope `1`. -/
theorem kfsh_periodic (CI : Work.RPV.CurveIsotopy) (δ : ℝ) (k : ℤ) (τ σ t : ℝ) :
    kfsh CI δ k τ σ (t + 2 * Real.pi) = kfsh CI δ k τ σ t := by
  unfold kfsh
  rw [show t + 2 * Real.pi + kphc δ k σ = (t + kphc δ k σ) + 2 * Real.pi by ring,
    CI.per]

/-- The near shape `knear` is `2π`-periodic in `t`. -/
theorem knear_periodic (CI : Work.RPV.CurveIsotopy) (W : ℝ → ℝ → ℝ → Work.RPV.PS)
    (ρh : ℝ → ℝ → ℝ → ℝ) (δ : ℝ) (k : ℤ)
    (hWper : ∀ τ t ρ, W τ (t + 2 * Real.pi) ρ = Work.RPV.Tk 1 (W τ t ρ))
    (hρhper : ∀ τ t σ, ρh τ (t + 2 * Real.pi) σ = ρh τ t σ)
    (τ σ t : ℝ) :
    knear CI W ρh δ k τ σ (t + 2 * Real.pi) = knear CI W ρh δ k τ σ t := by
  unfold knear
  rw [hρhper τ t (kclamp δ σ), hρhper 0 t (kclamp δ σ)]
  rw [hWper τ t, hWper 0 t]
  rw [Work.RPV.uproj_Tk, Work.RPV.uproj_Tk]
  rw [ktarg_periodic]

theorem kshape_periodic (CI : Work.RPV.CurveIsotopy) (W : ℝ → ℝ → ℝ → Work.RPV.PS)
    (ρh : ℝ → ℝ → ℝ → ℝ) (δ : ℝ) (k : ℤ)
    (hWper : ∀ τ t ρ, W τ (t + 2 * Real.pi) ρ = Work.RPV.Tk 1 (W τ t ρ))
    (hρhper : ∀ τ t σ, ρh τ (t + 2 * Real.pi) σ = ρh τ t σ) :
    ∀ τ σ t, Work.RPB.B5.kshape CI W ρh δ k τ σ (t + 2 * Real.pi)
      = Work.RPB.B5.kshape CI W ρh δ k τ σ t := by
  intro τ σ t
  unfold kshape
  rw [knear_periodic CI W ρh δ k hWper hρhper, kfsh_periodic]

end Work.RPB.B5
