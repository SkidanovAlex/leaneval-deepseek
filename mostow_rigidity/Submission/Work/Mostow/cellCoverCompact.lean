import Mathlib
import Submission.Work.Mostow.KMCellDefs
import Submission.Work.Mostow.finite_nearStab
import Submission.Work.Mostow.isCompact_matBallToPO

/-!
# Compactness of the unit ball of the orbit map

`{g : PO k 1 | hdist 0 (g • 0) ≤ 1}` is compact.

It is *closed*, being the preimage of the closed set `{v | hdist 0 v ≤ 1}` under the continuous
orbit map `g ↦ g • 0` (`POActionProp` gives continuity of the action, `HypIsometryProp` gives
continuity of `hdist`); and it is contained in the compact set `matBallToPO k (cosh 1)` because
an element displacing the origin by at most `1` has all matrix entries bounded by `cosh 1`
(`nearStab_orbitBall_subset`, from `Submission.Work.Mostow.finite_nearStab`), whose image in
`PO k 1` is compact (`isCompact_matBallToPO`).
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity
open scoped Topology

theorem cellCoverCompact (k : ℕ) (hA : Submission.Mostow.POActionProp k)
    (hI : Submission.Mostow.HypIsometryProp k) :
    IsCompact {g : LeanEval.Geometry.MostowRigidity.PO k 1 |
      Submission.Mostow.hdist (0 : Submission.Mostow.E k) (g • (0 : Submission.Mostow.E k)) ≤ 1} := by
  have hA' : POBasic k := POBasic.ofProp hA
  have hI' : HypIsoData k := HypIsoData.ofProp hI
  -- the orbit map `g ↦ g • 0` is continuous, and so is `hdist` composed with it
  have hc : Continuous (fun p : E k × E k => hdist p.1 p.2) := hI'.continuous
  have horbit : Continuous (fun g : PO k 1 => g • (0 : E k)) :=
    hA'.continuous_smul.comp (continuous_id.prodMk continuous_const)
  have hp : Continuous (fun g : PO k 1 => ((0 : E k), g • (0 : E k))) :=
    continuous_const.prodMk horbit
  have h2 : Continuous ((fun p : E k × E k => hdist p.1 p.2) ∘
      (fun g : PO k 1 => ((0 : E k), g • (0 : E k)))) := hc.comp hp
  have hf : Continuous (fun g : PO k 1 => hdist (0 : E k) (g • (0 : E k))) := h2
  -- hence the set is closed
  have hclosed : IsClosed {g : PO k 1 | hdist (0 : E k) (g • (0 : E k)) ≤ 1} :=
    isClosed_Iic.preimage hf
  -- and it sits inside the compact set `matBallToPO k (cosh 1)`
  have hcomp : IsCompact (matBallToPO k (Real.cosh (max 1 0))) :=
    isCompact_matBallToPO (n := k) (Real.cosh (max 1 0))
  have hsub : {g : PO k 1 | hdist (0 : E k) (g • (0 : E k)) ≤ 1} ⊆
      matBallToPO k (Real.cosh (max 1 0)) :=
    nearStab_orbitBall_subset (n := k) 1
  exact IsCompact.of_isClosed_subset hcomp hclosed hsub

end Work.Mostow
