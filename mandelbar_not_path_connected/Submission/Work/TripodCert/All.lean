/-
# TripodCert — the whole area in one import

Area `Submission/Work/TripodCert/` of `mandelbar_not_path_connected`: the certified `b₂`-tripod
data `Work.EL.Tripod d.hN` consumed by `ELAssembly.AssemblyInputs`.

## What this area delivers

* `Work.TripodCert.tripod_of_fixed` (`Basic.lean`) — **(T1)** if the `22/63`-ray lands at a point
  fixed by `Tsq c`, then the three tripod rays land there.
* `Work.TripodCert.tripod_of_transfer`, `Work.TripodCert.tripod_of_transfer_tripod`
  (`Transfer.lean`) — **(T2)** the transfer of the tripod along the FQC deformation
  (`Work.FQC.transfer_rays`), the `hzero_of_transfer` pattern.
* `Work.TripodCert.seed_tri` (`Seed.lean`) — **(T3)** TRI at the certified seed box: for
  `c ∈ Xb ∩ M*`, the landing point of the `22/63`-ray is fixed by `Tsq c`.
* `Work.TripodCert.seed_tripod` (`Seed.lean`) — the `Work.EL.Tripod` at any parameter of the
  certified box.
* `Work.TripodCert.tripod_of_seed_transfer` (`Seed.lean`) — **the final assembly**: from the seed
  certificate and the FQC datum `(θ, hb, hb₂, hesc)`, the tripod at the final parameter `c₂`.

See `Submission/Work/TripodCert/README.md` for the certificate architecture and the numerical
data.
-/
import Submission.Work.TripodCert.Basic
import Submission.Work.TripodCert.Transfer
import Submission.Work.TripodCert.Chain
import Submission.Work.TripodCert.Unique
import Submission.Work.TripodCert.Seed

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-! ## How the consumer uses this area

`ELAssembly.AssemblyInputs` needs `T : Work.EL.Tripod d.hN` at the final parameter `c₂`.  The
call site is: -/

open LeanEval.ComplexAnalysis (Mandelbar)

namespace Work.TripodCert

noncomputable section

example {c c₂ : ℂ} {φ : ℂ → ℂ} (θ : ℂ ≃ₜ ℂ)
    (hb : Work.ParamRays.IsDynBottcher c φ)
    (hb₂ : Work.ParamRays.IsDynBottcher c₂ (φ ∘ (θ.symm : ℂ → ℂ)))
    (hesc : ∀ z : ℂ, Work.ParamRays.Escaping c₂ (θ z) ↔ Work.ParamRays.Escaping c z)
    (d : Work.EL.RootParabolic c₂) (hc : c ∈ Mandelbar) (hcX : Work.SeedCertRay.Xb.mem c) :
    Work.EL.Tripod d.hN :=
  tripod_of_seed_transfer θ hb hb₂ hesc d.hN d.bottcher hc hcX

end

end Work.TripodCert
