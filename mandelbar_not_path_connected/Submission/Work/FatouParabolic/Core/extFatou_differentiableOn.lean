import Mathlib
import Submission.Work.FatouParabolic.Core.Defs
import Submission.Work.FatouParabolic.Core.extFatou_independent
import Submission.Work.FatouParabolic.Core.extFatou_abel

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouParabolic.Core

/-!
# The extended Fatou coordinate is holomorphic on the punctured basin

`Work.FatouParabolic.extFatou fl` runs the orbit of a point of the punctured basin into the
petal `fl.Pa` and reads off `fl.φa` there, subtracting the number of steps taken
(`Work.FatouParabolic.entryTime`).  This file proves that the result is a holomorphic function
of the point on the whole punctured basin.

The point is that the (nonconstructive) `entryTime` is *locally constant* in effect: near a
point `x` of the basin we may tap the orbit at a **fixed** time `N` instead of at `entryTime`.
Choose `N` with `F^[N] x ∈ fl.Pa` (the flower's `enters_Pa`); since `fl.Pa` is open and `F^[N]`
is continuous (as `F` is differentiable), `F^[N] w ∈ fl.Pa` for all `w` in an open neighbourhood
`U ∋ x`.  Then for `w ∈ U` in the basin, `extFatou_independent` identifies the value read off at
`entryTime` with the value read off at the fixed time `N`:

`extFatou fl w = fl.φa (F^[N] w) - N`  for all `w` near `x`.

The right-hand side is holomorphic at `x` (composition of the holomorphic `fl.φa` on the open
`fl.Pa` with the holomorphic `F^[N]`), and `extFatou` agrees with it on the neighbourhood
`U ∩ puncturedBasin`.  Hence `extFatou` is holomorphic at `x`; this is the statement below.

Note that the openness of the punctured basin (`hopen`) is exactly what lets us invoke this
neighbourhood argument in the subspace topology: on an open set, differentiability within the
set at `x` is differentiability at `x`.
-/

theorem extFatou_differentiableOn {F g : ℂ → ℂ} {z₀ : ℂ}
    (fl : Work.FatouCoordFix.ParabolicFlowerFix F g z₀) (hF : Differentiable ℂ F)
    (hopen : IsOpen (Work.FatouParabolic.puncturedBasin F z₀)) :
    DifferentiableOn ℂ (Work.FatouParabolic.extFatou fl) (Work.FatouParabolic.puncturedBasin F z₀) := by
  intro x hx
  -- Tap the orbit of `x` at a fixed time `N` with `F^[N] x ∈ fl.Pa`.
  obtain ⟨N, hNx⟩ := fl.enters_Pa x (Work.FatouParabolic.mem_basin.mp hx.2) hx.1
  -- The set where `F^[N]` lands in the open petal is an open neighbourhood of `x`.
  have hUo : IsOpen ((F^[N]) ⁻¹' fl.Pa) := fl.isOpen_Pa.preimage (hF.continuous.iterate N)
  have hUx : x ∈ (F^[N]) ⁻¹' fl.Pa := hNx
  -- The comparison function `w ↦ φa (F^[N] w) - N` is holomorphic at `x`.
  have hFN : Differentiable ℂ (F^[N]) := hF.iterate N
  have hφaAt : DifferentiableAt ℂ fl.φa ((F^[N]) x) :=
    fl.φa_fatou.1.2.1.differentiableAt (fl.isOpen_Pa.mem_nhds hNx)
  have hG : DifferentiableAt ℂ (fun w => fl.φa ((F^[N]) w) - (N : ℂ)) x :=
    (hφaAt.comp x (hFN.differentiableAt)).sub_const _
  -- `extFatou` agrees with it on the neighbourhood `(F^[N]) ⁻¹' fl.Pa ∩ puncturedBasin`.
  have heq : Work.FatouParabolic.extFatou fl =ᶠ[nhds x]
      (fun w => fl.φa ((F^[N]) w) - (N : ℂ)) := by
    filter_upwards [hUo.mem_nhds hUx, hopen.mem_nhds hx] with w hwU hwB
    rw [Work.FatouParabolic.extFatou_eq fl hwB]
    exact Work.FatouParabolic.Core.extFatou_independent fl hwB
      (Work.FatouParabolic.entryTime_spec fl w hwB) hwU
  exact (hG.congr_of_eventuallyEq heq).differentiableWithinAt

end Work.FatouParabolic.Core
