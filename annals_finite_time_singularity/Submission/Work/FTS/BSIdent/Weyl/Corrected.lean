/-
# `Work.FTS.BSIdent.Weyl.Corrected` — the corrected stream-function field (route C)

`Work.Cyl.psiField ψ` is the correct no-swirl velocity field off the axis, but the *function*
`x ↦ psiField ψ x` computed by the definition is **discontinuous at the axis** whenever
`ψ(r,z)/r` has a non-zero limit: `psiField` evaluates `−ψ/r` at `r = 0` with Lean's junk
`0/0 = 0`, whereas the value of the continuous extension is `−2·lim_{r→0⁺} ψ(r,z)/r`.  (Verified in
Lean: `psiField (fun r z => r) (r,0,z) = −2•e_z` for `r > 0` but `= −e_z` at `(0,0,z)`.)  For the
genuine reconstruction `Φ ≈ c(z)·cos θ` near `θ = π/2`, so `ψ/r` does have a non-zero limit and the
Lean field really does jump.

Since the identification `hid` is only claimed on `Uax = {x₃ ≠ 0, r ≠ 0}` — and the axis is a
Lebesgue-null set on which the *values* of a field are invisible to the weak (distributional)
identities — route C replaces `Cyl.psiField (merPsi … · t)` by **any** field that agrees with it on
`Uax` and is globally continuous and decaying.  This module fixes the canonical such replacement:

  `psiFieldCorr ψ L x = if radial x = 0 then (−2 L (axial x)) • e_z else psiField ψ x`,

with `L` the axis level `z ↦ lim_{r→0⁺} ψ(r,z)/r` of the stream function.  Both branches agree with
`psiField ψ` off the axis, so `psiFieldCorr ψ L = psiField ψ` on `Uax`; the axis value
`−2 L z • e_z` is the continuous extension of `−ψ/r − ∂_rψ` (for an axis-regular `ψ` one has
`ψ/r → L z` and `∂_rψ → L z`, whence `−ψ/r − ∂_rψ → −2 L z`, while the radial component carries the
vanishing factor `radialVec`).

## What is proved here

* `psiFieldCorr`, `psiFieldCorr_apply` — the definition;
* `psiFieldCorr_of_radial_ne` — the off-axis branch (`x ↦ psiField ψ x`);
* `psiFieldCorr_of_radial_eq` — the on-axis branch;
* `psiFieldCorr_eq_psiField_of_mem_Uax` — **the agreement clause**: on `Uax` the corrected field is
  the Lean field `psiField ψ` (this is the `hv` hypothesis of `Work.FTS.BSIdent.hid_of_weyl`);
* `Continuous.psiFieldCorr`-shaped gluing (`continuous_psiFieldCorr`) is *delegated* (it needs the
  one-sided limits at the axis); see `Weyl/continuous_psiFieldCorr.lean`.

The remaining analytic input of route C is the existence, for the concrete meridian data
`merPsi α A B Φ C · · t`, of the level `L` and the continuity/decay of `psiFieldCorr`; that is
`Work.FTS.BSIdent.Weyl.merPsi_corrected_bundle`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.BSIdent.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set MeasureTheory
open scoped Topology

namespace Work.FTS.BSIdent

set_option autoImplicit false

/-- **The corrected stream-function field.**  Off the axis this is `Cyl.psiField ψ`; on the axis
`r = 0` it is the value `−2 L z • e_z` of the continuous extension, `L` being the axis level
`z ↦ lim_{r→0⁺} ψ(r,z)/r` of the stream function. -/
def psiFieldCorr (ψ : ℝ → ℝ → ℝ) (L : ℝ → ℝ) : R3 → R3 :=
  fun x => if Work.Cyl.radial x = 0 then (-(2 * L (Work.Cyl.axial x))) • Work.Cyl.eZ
    else Work.Cyl.psiField ψ x

@[simp] theorem psiFieldCorr_apply (ψ : ℝ → ℝ → ℝ) (L : ℝ → ℝ) (x : R3) :
    psiFieldCorr ψ L x
      = if Work.Cyl.radial x = 0 then (-(2 * L (Work.Cyl.axial x))) • Work.Cyl.eZ
        else Work.Cyl.psiField ψ x := rfl

/-- Off the axis the corrected field is the Lean stream-function field. -/
theorem psiFieldCorr_of_radial_ne {ψ : ℝ → ℝ → ℝ} {L : ℝ → ℝ} {x : R3}
    (hx : Work.Cyl.radial x ≠ 0) : psiFieldCorr ψ L x = Work.Cyl.psiField ψ x := by
  rw [psiFieldCorr_apply, if_neg hx]

/-- On the axis the corrected field takes the extension value `−2 L z • e_z`. -/
theorem psiFieldCorr_of_radial_eq {ψ : ℝ → ℝ → ℝ} {L : ℝ → ℝ} {x : R3}
    (hx : Work.Cyl.radial x = 0) :
    psiFieldCorr ψ L x = (-(2 * L (Work.Cyl.axial x))) • Work.Cyl.eZ := by
  rw [psiFieldCorr_apply, if_pos hx]

/-- **The agreement clause of route C.**  On `Uax = {x₃ ≠ 0, r ≠ 0}` the corrected field is the
Lean field `Cyl.psiField ψ`; this is exactly the `hv` hypothesis of
`Work.FTS.BSIdent.hid_of_weyl`. -/
theorem psiFieldCorr_eq_psiField_of_mem_Uax {ψ : ℝ → ℝ → ℝ} {L : ℝ → ℝ} {x : R3}
    (hx : x ∈ Uax) : psiFieldCorr ψ L x = Work.Cyl.psiField ψ x := by
  refine psiFieldCorr_of_radial_ne fun h0 => ?_
  have hmem : x 0 ^ 2 + x 1 ^ 2 = 0 := by
    have h1 : Work.Cyl.radSq x = 0 := by
      have h2 : (Real.sqrt (Work.Cyl.radSq x)) ^ 2 = (0 : ℝ) := by
        have := congrArg (fun t : ℝ => t ^ 2) h0
        simpa [Work.Cyl.radial] using this
      rwa [Real.sq_sqrt (by simp only [Work.Cyl.radSq]; positivity)] at h2
    simpa [Work.Cyl.radSq] using h1
  exact hx.2 (by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)])

end Work.FTS.BSIdent
