/-
# `RayStrand` is false — the corrected route (`TailId` + crossing parity)

**Superseded.**  `Work.ELRig.RayStrand` (“on the strand of `R(αᵢ)` the smaller level is the deeper
point”) is **false in general**, as `NOTES_LEAD_mandelbar_residuals.md` §3.2 states: the lift `γ₁`
is an exactly `1`-periodic-shift curve, its shape does not straighten as `R → ∞`, and the finger
counterexample of `ELRig/NOTES.md` §6 is exactly such a curve.  It was never needed either:
`reach` and `rigidity` received a `LiftSides` argument and never used it (their signatures have now
been changed to drop it), and the only consumer of the lift was R-a3 (`htail`).

**The corrected route** (all in this directory):

* `Work.ELRig.RayCylLift` (`CylLift.lean`) — the curves of `exists_liftCurvesV3` together with
  **`TailId`**: in a far-left half plane the `Ψ`-preimages of the two root rays are *exactly* the
  two lifts;
* `Work.ELRig.exists_rayCylLift` — `TailId` **proved** from `exists_liftCurvesV3`, `fl.Ψ_inj`,
  `fl.Ψ_small` and the Green function (the level of a ray point is its Böttcher modulus, so at
  levels above `t* = τ s*` the ray point stays `δ` away from `z₁`, where `Ψ(H_R)` lives; below
  `t*` the lift `γ₁ (τ⁻¹ t)` lies in the injectivity half plane and injectivity of `Ψ` identifies
  it with `w`);
* `Work.ELRig.htail_of_rayCylLift` — R-a3 by **crossing parity**: under `E ⊆ K` the real axis meets
  neither lift, so `γ₁ ⊆ {Im > 0}`, `γ₂ = ιγ₁ ⊆ {Im < 0}`; a vertical segment at a generic `x₀`
  meets `γ₁` in an *odd* number of points (`Re γ₁ (s+1) = Re γ₁ s + 1`), each transversal crossing
  flips the side, and the top of the segment lies in `Pa ⊆ pairSide nest.P0` — so `Ψ x₀` is in the
  near side, and the whole real tail (connected, off the pair curve) is;
* `Work.EL.equatorLeak'` (`MainCyl.lean`) — the contract's `equatorLeak (hJ) (d) (fl)` with only
  `nest` (ELNest) and `tr` (ELNest/ELPull) as inputs.  No `RayLift`, no `RayStrand`, no
  `LiftSides`.

The **even** form of the same parity argument, `Work.ELRig.sidePreserve_of_rayCylLift`, gives the
side preservation `Z1Nest.SP` for the α-pair without the (false) `ELNest.NestData.band` field
(`NOTES_LEAD_mandelbar_residuals.md` §3.3).
-/
import Submission.Work.ELRig.CylLift
import Submission.Work.ELRig.exists_rayCylLift

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

end Work.ELRig
