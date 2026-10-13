/-
# Shared definitions for the `𝒲^{4,∞}`-estimate of the singular radial piece `Ḡ`

These are the three objects the `Ḡ`-estimate is phrased in terms of.  They are kept in a
separate module so that the auxiliary lemmas about them (which live in sibling files) can
import the definitions without importing the main file `Gbar_wiln.lean` (which imports
*them*, so there would be a cycle).

* `At N j z = ∫_0^1 t^{N+j}/(1+zt)^{j+2} dt` is the basic family; after the change of
  variables `s = zt`, `z · At N 0 z = z^{-N}∫_0^z s^N(1+s)^{-2} ds`, which is (up to the
  factor `-1/2`) the singular piece `Ḡ` for `N = 5/α`.
* `Pi N z = z · At N 0 z`.
* `PhiL z = -(1/2)∫_0^z t/(1+t)^2 dt` is the *left branch* of `Ḡ`: for `z < 0` one has
  `Ḡ(z) = PhiL z` (because `Real.rpow` of a negative base is `1`), which is what pins down
  the (junk) values of the `deriv`-iterates of `Ḡ` at `z = 0`.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set
open scoped Real Topology

namespace Work.FTS.H2.PhiStarE

set_option autoImplicit false

/-- `At N j z = ∫_0^1 t^{N+j} / (1 + z*t)^{j+2} dt`. -/
def At (N : ℝ) (j : ℕ) (z : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, t ^ (N + (j : ℝ)) / (1 + z * t) ^ (j + 2)

/-- `Pi N z = z · At N 0 z`; on `[0,∞)` this is `z^{-N}∫_0^z s^N (1+s)^{-2} ds`. -/
def Pi (N : ℝ) : ℝ → ℝ := fun z => z * At N 0 z

/-- `PhiL z = -(1/2)∫_0^z t/(1+t)^2 dt`, the left branch of `Ḡ`. -/
def PhiL : ℝ → ℝ := fun z => -(1 / 2) * ∫ t in (0 : ℝ)..z, t / (1 + t) ^ 2

@[simp] theorem At_def (N : ℝ) (j : ℕ) (z : ℝ) :
    At N j z = ∫ t in (0 : ℝ)..1, t ^ (N + (j : ℝ)) / (1 + z * t) ^ (j + 2) := rfl

@[simp] theorem Pi_def (N : ℝ) (z : ℝ) : Pi N z = z * At N 0 z := rfl

@[simp] theorem PhiL_def (z : ℝ) :
    PhiL z = -(1 / 2) * ∫ t in (0 : ℝ)..z, t / (1 + t) ^ 2 := rfl

end Work.FTS.H2.PhiStarE
