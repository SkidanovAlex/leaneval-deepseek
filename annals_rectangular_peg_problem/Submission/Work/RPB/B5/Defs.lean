import Mathlib
import Submission.Work.RPV.Defs
import Submission.Work.RPV.VBasic

/-!
# B5: the Lagrangian family `ℓ` built from the chord annulus and the collar

This file holds the *construction* (definitions only) used by `Work.RPB.B5.exists_lagFamily`.

## The shape of the construction (corrected layout)

`ℓ τ (x,t) = lagPt W Γc Ac ρ τ x t` is built from

* `W : ℝ → ℝ → ℝ → PS`, the **`ρ = r²`-chart of the chord annulus near the blown-up diagonal**
  (`W τ t (r^2) = chordSurf CI.c a τ t r` for `0 < r < π/2`, and `C^8` in `ρ` across `ρ = 0`);
  this is `Work.RPB.B5.chordSurf_rhoChart_range`;
* the **collar** `(Γc, Ac)` for the levels `σ ≥ 0` (`Work.RPB.B5.collar_exists`), placed by
  `levelPt` (`levelPt u σ a` has `K₀ = -1-σ`);
* a **radius function** `ρ : ℝ → ℝ → ℝ → ℝ` giving the chord parameter `ρ τ x t = r²` of the
  chord chart on the middle region.

The **left** half `x ≤ 0` is the "base":
* `x ≤ -√2`: the collar at level `σ = x^2/2 - 1`, i.e. `levelPt (Γc τ σ t) σ (Ac τ σ t)`;
* `x ∈ [-√2, 0]`: the chord chart `W τ t (ρ τ x t)`, with `r = 0` at `x = -√2` (the blown-up
  diagonal `Λ`, level `s = 0`, collar level `σ = 0`) and `r = π/2` at `x = 0` (the middle
  chord, `ρ = π²/4`).

The **right** half `x ≥ 0` is `tau π` of the left half with `t ↦ t - π`.  This makes the `symm`
field of `LagFamily` hold *definitionally* for `x ≤ 0` and reduces it, for `x > 0`, to
`base (x, t+π) = Tk 1 (base (x, t-π))`, which is the `2π`-quasiperiodicity of the base; at
`x = 0` it needs exactly `r(0,·) = π/2` (the middle chord is its own `τ_π`-image partner:
`tau π (chordSurf τ t π/2) = chordSurf τ (t+π) π/2`).

Why the left half and not the right one is the "base": at `τ = 0` the family must lie in the
zero section (`LagFamily.start`) and must be `stdZ x t` for `|x| ≥ X0` (`LagFamily.std`), so for
large positive `x` the point has `q₁ = x > 0`, while at the collar's `σ = 0` end (the blown-up
diagonal) one has `q₁ = -√2 < 0`; the collar, being in the zero section at `τ = 0`, keeps the
sign of `q₁` fixed, so the attachment `q₁ = -√2` has to be on the *negative* `x` side.  With the
far end `√(2+2σ) e^{i(t-π/2)}` (phase `A = t`) one has `q₁ = -√(2+2σ)`, i.e. `stdZ (-√(2+2σ)) t`,
which matches `x = -√(2+2σ)`, i.e. `σ = x^2/2 - 1`, for `x ≤ -X0`.
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-- The collar level attached to the parameter `x` on the left half: `σ = x²/2 - 1 ≥ 0` for
`x ≤ -√2` (it is `0` at the blown-up diagonal and makes `ℓ (x,t) = stdZ x t` at the far end). -/
def sig (x : ℝ) : ℝ := x ^ 2 / 2 - 1

/-- The collar point at level `σ ≥ 0`, reduced coordinate `Γc τ σ t`, phase `Ac τ σ t`. -/
def collarPt (Γc : ℝ → ℝ → ℝ → ℂ) (Ac : ℝ → ℝ → ℝ → ℝ) (τ σ t : ℝ) : Work.RPV.PS :=
  Work.RPV.levelPt (Γc τ σ t) σ (Ac τ σ t)

/-- The `x ≤ 0` half of `ℓ`: the collar for `x ≤ -√2` and the chord chart for `-√2 ≤ x ≤ 0`. -/
def basePt (W : ℝ → ℝ → ℝ → Work.RPV.PS) (Γc : ℝ → ℝ → ℝ → ℂ) (Ac : ℝ → ℝ → ℝ → ℝ)
    (rho : ℝ → ℝ → ℝ → ℝ) (τ x t : ℝ) : Work.RPV.PS :=
  if x ≤ -Real.sqrt 2 then collarPt Γc Ac τ (sig x) t else W τ t (rho τ x t)

/-- The Lagrangian family point `ℓ τ (x,t)`: the `x ≤ 0` half is `basePt`, and the `x > 0` half
is the `τ_π`-image of the reflected point (this is the `symm` field of `LagFamily` made
definitional on the left half). -/
def lagPt (W : ℝ → ℝ → ℝ → Work.RPV.PS) (Γc : ℝ → ℝ → ℝ → ℂ) (Ac : ℝ → ℝ → ℝ → ℝ)
    (rho : ℝ → ℝ → ℝ → ℝ) (τ x t : ℝ) : Work.RPV.PS :=
  if x ≤ 0 then basePt W Γc Ac rho τ x t
  else Work.RPV.tau Real.pi (basePt W Γc Ac rho τ (-x) (t - Real.pi))

end Work.RPB.B5
