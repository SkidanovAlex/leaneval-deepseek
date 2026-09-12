import ChallengeDeps
open OptimalMoebius
open scoped BigOperators

set_option autoImplicit false
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Elementary periodicity facts for the flat Möbius band model

The period map `period a (x, y) = (1−x, y+a)` generates the deck group of the
flat band `([0,1]×ℝ)/∼`.  This module records the basic algebraic facts used
when passing between the strip, its fundamental domain, and the quotient:
`period` preserves the strip, its square translates by `2a` in the second
coordinate, and (consequently) `f` is periodic with period `2a` in the second
coordinate along each horizontal line of the strip.
-/

noncomputable section
namespace Submission.PaperBand

/-- `period` maps the unit strip into itself. -/
lemma period_maps_strip (a : ℝ) {x : ℝ²} (hx : x ∈ unitStrip) : period a x ∈ unitStrip := by
  unfold unitStrip at hx ⊢
  simp [period]
  constructor
  · linarith [hx.2]
  · linarith [hx.1]

/-- Applying `period` twice translates the second coordinate by `2a` and
leaves the first coordinate fixed. -/
lemma period_twice (a : ℝ) (x : ℝ²) : period a (period a x) = !₂[x 0, x 1 + 2 * a] := by
  ext i <;> fin_cases i <;> simp [period] <;> ring

/-- `f` is periodic with period `2a` in the second coordinate on the strip:
`f (x, y + 2a) = f (x, y)`. -/
lemma f_period_twice {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) {x : ℝ²}
    (hx : x ∈ unitStrip) : f !₂[x 0, x 1 + 2 * a] = f x := by
  have h1 : period a x ∈ unitStrip := period_maps_strip a hx
  calc
    f !₂[x 0, x 1 + 2 * a] = f (period a (period a x)) := by
      rw [period_twice]
    _ = f (period a x) := hf.periodic (period a x) h1
    _ = f x := hf.periodic x hx

/-- Along the left edge `x = 0`, the map `y ↦ f (0, y)` has period `2a`. -/
lemma boundary_period_twice {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (y : ℝ) : f !₂[0, y + 2 * a] = f !₂[0, y] := by
  simpa using f_period_twice (x := !₂[0, y]) (a := a) hf (by unfold unitStrip; constructor <;> norm_num)

end Submission.PaperBand
end
