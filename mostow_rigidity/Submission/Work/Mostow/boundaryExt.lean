import Mathlib
import Submission.Mostow.Interfaces
import Submission.Work.Mostow.BdExt.Basic
import Submission.Work.Mostow.BdExt.lawCosines
import Submission.Work.Mostow.BdExt.rayDist
import Submission.Work.Mostow.BdExt.rayChart
import Submission.Work.Mostow.BdExt.stepSum
import Submission.Work.Mostow.BdExt.coarseInverse
import Submission.Work.Mostow.BdExt.closeSeq
import Submission.Work.Mostow.BdExt.isomConv
import Submission.Work.Mostow.BdExt.isomRayCompare
import Submission.Work.Mostow.BdExt.bdMap
import Submission.Work.Mostow.BdExt.bdMapCmp
import Submission.Work.Mostow.BdExt.bdMapCont
import Submission.Work.Mostow.BdExt.bdMapClose
import Submission.Work.Mostow.BdExt.bdMapDetect
import Submission.Work.Mostow.BdExt.bdMapBij
import Submission.Work.Mostow.BdExt.bdMapEquiv

/-!
## Status of the C4 development (for the next agent)

PROVED (sorry-free, importable):
* `BdExt/Basic.lean`      : `ray`, `lvl`, `dirv`, `gpr`, `ConvTo`, `CloseSeq`.
* `BdExt/lawCosines.lean` : law of cosines at the origin; `norm_sub_dirv_sq_le` (the angular
  step bound), `sinh_lvl_smul_dirv`, `norm_dirv`.
* `BdExt/rayDist.lean`, `BdExt/rayChart.lean`, `BdExt/rayLawCosines.lean` : the rays are
  unit-speed geodesics; `hdist (ray ξ s) (ray ξ t) = |s - t|`.
* `BdExt/stepSum.lean`    : summable steps ⟹ convergence.
* `BdExt/qiRayLimit.lean` : **the existence of `bdMap` and its rate** (the analytic heart).
* `BdExt/closeSeq.lean`   : bounded-distance sequences have the same limit direction.
* `BdExt/coarseInverse.lean` : a quasi-isometry has a coarse inverse.
* `BdExt/isomConv.lean`   : `u_k → ξ` ⟹ `g • u_k → bd g ξ` (action on the compactification).
* `BdExt/isomRayCompare.lean` : the rays `g • ray ξ ·` and `ray (bd g ξ) ·` are at bounded
  distance.
* `BdExt/bdMap.lean`      : `bdMap`, `bdMap_spec`, `bdMap_rate` (uniform rate), `lvl_image_ray`.

DELEGATED (statements filed, proofs in progress at the time of writing):
* `BdExt/bdMapCmp.lean`   : two nearby boundary points are exponentially close (`T₀, C₆`).
* `BdExt/bdMapCont.lean`  : continuity of `bdMap` on `Sph n` (from `bdMapCmp`).
* `BdExt/bdMapDetect.lean`: the detector: `dirv z → ξ`, `lvl z → ∞` ⟹ `dirv (Φ z) → bdMap Φ ξ`.
* `BdExt/bdMapClose.lean` : bounded-distance quasi-isometries have the same boundary map.
* `BdExt/bdMapBij.lean`   : `bdMap Φ` is a bijection of `Sph n` (via a coarse inverse).
* `BdExt/qiRayRate.lean`  : the uniform rate (independent of `ξ`), used by `bdMap`.

LOCAL (this file): `bdMap_equivariant` — the coarse-equivariance of `bdMap`, proved directly
with `isomRayCompare` + `closeSeq` + `isomConv` (no functoriality of boundary maps needed).
-/

/-!
# C4 — `boundaryExt`: a quasi-isometry of `ℍⁿ` extends to a homeomorphism of the sphere

The boundary extension of a quasi-isometry `Φ` of `ℍⁿ` is `bdMap n Φ : E n → E n`
(`Submission/Work/Mostow/BdExt/bdMap.lean`): the limit of the directions of the image of the
geodesic ray to `ξ`.

This file proves `BoundaryExtProp n`: for every `IsQI Φ` there is a bijection `φ` of `Sph n`,
continuous in the subspace topology, compatible with coarse equivariance.  The proof collects:

* `bdMap_spec`, `bdMap_rate` (existence and the *uniform* rate),
* `bdMapCmp` (two nearby boundary points have exponentially close images),
* `bdMapCont` (continuity of `bdMap`),
* `bdMapDetect` (the boundary map can be evaluated on any sequence that is eventually close to
  a ray, i.e. on any sequence with `dirv z → ξ` and `lvl z → ∞`),
* `bdMapClose` (bounded-distance quasi-isometries induce the same boundary map),
* `bdMapBij` (bijectivity, via a coarse inverse),
* and the explicit coarse-equivariance argument `bdMap_equivariant`, which uses only
  `bdMap_spec`/`closeSeq`/`isomConv`/`isomRayCompare`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open Work.Mostow.BdExt
open Classical

noncomputable section

variable {n : ℕ}

/-- **`BoundaryExtProp`**: every quasi-isometry of `ℍⁿ` extends to a homeomorphism of the
boundary sphere, compatible with coarse equivariance. -/
theorem boundaryExt (n : ℕ) (hn : 3 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n) :
    BoundaryExtProp n := by
  intro Φ hΦ
  obtain ⟨K, C, hK, hC, hup, hlow, hsurj⟩ := hΦ
  -- continuity of the boundary map, from the two-point comparison
  obtain ⟨T₀, C₆, hT₀, hC₆, hcmp⟩ := bdMapCmp n hI Φ K C hK hC hup hlow
  have hcont : ContinuousOn (fun ξ : E n => bdMap n Φ ξ) (Sph n) :=
    bdMapCont n hI Φ K C T₀ C₆ (lt_of_lt_of_le zero_lt_one hK) hT₀ hC₆ hcmp
  -- bijectivity of the boundary map, via the detector `bdMapDetect` and a coarse inverse
  have hbij : Set.BijOn (fun ξ : E n => bdMap n Φ ξ) (Sph n) (Sph n) :=
    bdMapBij n hI Φ K C hK hC hup hlow hsurj
      (fun Ψ K' C' hK' hC' hup' hlow' hcont' =>
        bdMapDetect n hI Ψ K' C' hK' hC' hup' hlow' hcont')
  refine ⟨fun ξ => bdMap n Φ ξ, hbij, hcont, ?_⟩
  -- coarse equivariance
  intro g h hcoe ξ hξ
  obtain ⟨C₀, hC₀⟩ := hcoe
  have hC₀' : 0 ≤ C₀ := le_trans (hI.1 _ _) (hC₀ 0)
  exact bdMapEquiv n hA hI Φ K C hK hC hup hlow g h C₀ hC₀' hC₀ ξ hξ

end

end Work.Mostow
