/-
# Assembly of the challenge theorem from the area lemmas

`Work.Mostow.mostow_rigidity_of_areas` proves the statement of `Submission.mostow_rigidity`
(equivalently `Challenge.mostow_rigidity`) from the fifteen area lemmas of the workspace, through
the driver's glue `Submission.Mostow.mostow_of_areas` (`Submission/Mostow/Wiring.lean`, DO NOT EDIT).

All fifteen area lemmas are proved in their own files and CO-IMPORT (checked in one environment);
this module is the single place where their statement shapes are matched against the glue, so that
`Submission.lean` only has to call

```
  exact Work.Mostow.mostow_rigidity_of_areas n hn Γ Λ disc_Γ disc_Λ covol_Γ covol_Λ f
```

Nothing here is a `sorry`, and no file outside this one is modified by it.

NOTE (for whoever edits `Submission.lean`): the only `sorry`-taint of this assembly is whatever the
area lemmas still carry transitively (currently `geodStratum`, `finTypeTubeEven`,
`hlFreeHoroballParabolic`, `cuspShimizuHoroballAux`, `boundaryExt`); `#print axioms` of
`Work.Mostow.mostow_rigidity_of_areas` lists them.
-/

import Submission.Mostow.Wiring
import Submission.Work.Mostow.poAction
import Submission.Work.Mostow.hypIsometry
import Submission.Work.Mostow.visualMeasure
import Submission.Work.Mostow.barycentre
import Submission.Work.Mostow.haarBridge
import Submission.Work.Mostow.natMapEquiv
import Submission.Work.Mostow.natMapJac
import Submission.Work.Mostow.natMapSurj
import Submission.Work.Mostow.volumeSqueeze
import Submission.Work.Mostow.localIsom
import Submission.Work.Mostow.bieberbach
import Submission.Work.Mostow.geomFinite
import Submission.Work.Mostow.cuspRecognition
import Submission.Work.Mostow.equivQI
import Submission.Work.Mostow.boundaryExt

open LeanEval.Geometry.MostowRigidity MeasureTheory

namespace Work.Mostow

/-- The challenge statement, assembled from the fifteen area lemmas. -/
theorem mostow_rigidity_of_areas (n : ℕ) (hn : 3 ≤ n) (Γ Λ : Subgroup (PO n 1))
    (disc_Γ : IsDiscrete (SetLike.coe Γ)) (disc_Λ : IsDiscrete (SetLike.coe Λ))
    [HasFundamentalDomain Γ (PO n 1)] [HasFundamentalDomain Λ (PO n 1)]
    (covol_Γ : covolume Γ (PO n 1) ≠ ⊤) (covol_Λ : covolume Λ (PO n 1) ≠ ⊤)
    (f : Γ ≃* Λ) : ∃ g : PO n 1, ∀ γ : Γ, f γ = g * γ * g⁻¹ := by
  have hA : Submission.Mostow.POActionProp n := Work.Mostow.poAction n hn
  have hI : Submission.Mostow.HypIsometryProp n := Work.Mostow.hypIsometry n hn hA
  have hV : Submission.Mostow.VisualProp n := Work.Mostow.visualMeasure n hn hA hI
  have hB : Submission.Mostow.BaryProp n := Work.Mostow.barycentre n hn hA hI
  have hNE : Submission.Mostow.NatMapEquivProp n := Work.Mostow.natMapEquiv n hn hA hI hV hB
  have hNJ : Submission.Mostow.NatMapJacProp n := Work.Mostow.natMapJac n hn hA hI hV hB
  have hNS : Submission.Mostow.NatMapSurjProp n := Work.Mostow.natMapSurj n hn hA hI hV hB hNJ
  have hBr : Submission.Mostow.BridgeProp n := Work.Mostow.haarBridge n hn hA hI
  have hVol : Submission.Mostow.VolumeProp n := Work.Mostow.volumeSqueeze n hn hA hI
  have hL : Submission.Mostow.LocalIsomProp n := Work.Mostow.localIsom n hn hA hI
  have hBb : ∀ m, Submission.Mostow.BieberbachProp m := Work.Mostow.bieberbach
  have hGF : Submission.Mostow.GeomFiniteProp n := Work.Mostow.geomFinite n hn hA hI hBb
  have hCR : Submission.Mostow.CuspRecognitionProp n :=
    Work.Mostow.cuspRecognition n hn hA hI hBb hGF
  have hQI : Submission.Mostow.QIProp n := Work.Mostow.equivQI n hn hA hI hBb hGF hCR
  have hBE : Submission.Mostow.BoundaryExtProp n := Work.Mostow.boundaryExt n hn hA hI
  exact Submission.Mostow.mostow_of_areas n hA hI hBr hNE hNJ hNS hVol hL hQI hBE
    Γ Λ disc_Γ disc_Λ covol_Γ covol_Λ f

end Work.Mostow
