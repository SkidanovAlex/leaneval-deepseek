/-
# `PieceHomology/`: the concrete computations of the tori and the per-cusp fields

The per-cusp fields `eT2` (`H_k(T²_v) ≅ ℤ^{rankT2 k}`) and `eTorus` (`H_k(∂[-1,1]² × T²_v) ≅
ℤ^{rankT k}`) of `Work.HomologyIso.CuspData` are computations of the concrete model spaces of the
Ratcliffe–Tschantz construction (`Work.RTInstance`):

```
T_v = Fin 2 → AddCircle 1 = (ℝ/ℤ)² ,       ∂[-1,1]² × T_v ≅ S¹ × T² .
```

This file collects the concrete results proved in this area — the circle `∂[-1,1]² ≃ S¹`, the
homology of `AddCircle 1`, of `(ℝ/ℤ)²` and of `S¹ × (ℝ/ℤ)²` — and the two *transport* lemmas that
turn them into the per-cusp fields of an arbitrary `rt : Work.Space.RTData` whose torus factors are
the standard ones (as in `Work.RTInstance`, where `rt.core.Torus v` *is* `Fin 2 → AddCircle 1`, and
in `Work.Cusp`, where the homeomorphism `a.Torus v ≃ₜ (Fin 2 → AddCircle 1)` is part of the data).

## Main results

* `Work.PieceHomology.intHomology_bdryPt` — `H_k(∂[-1,1]²) ≅ ℤ` for `k = 0, 1`, `0` otherwise;
* `Work.PieceHomology.eT2_of_homeomorph`, `Work.PieceHomology.eTorus_of_homeomorph` — the per-cusp
  fields from a homeomorphism with the standard torus model and the concrete computation;
* `Work.PieceHomology.cuspDataOf` — the three fields of `Work.HomologyIso.CuspData`, assembled from
  the concrete computations.
-/
import Mathlib
import Submission.Work.PieceHomology.Basic
import Submission.Work.PieceHomology.intHomology_addCircle
import Submission.Work.PieceHomology.homeomorph_bdryPt
import Submission.Work.PieceHomology.HomModel_ofHomotopyEquiv
import Submission.Work.PieceHomology.Torus2
import Submission.Work.PieceHomology.torus2Realization
import Submission.Work.PieceHomology.intHomology_torus3
import Submission.Work.PieceHomology.Bridge

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open LeanEval.Topology
open scoped Topology

namespace Work.PieceHomology

noncomputable section

/-! ## §1  The boundary circle `∂[-1,1]² ≃ S¹` -/

/-- **The homology of the square boundary** `∂[-1,1]²`, as the image of the homology of the
additive circle under the explicit homeomorphism `homeomorph_bdryPt`. -/
theorem intHomology_bdryPt (k : ℕ) :
    Nonempty (LeanEval.Topology.intHomology k (TopCat.of Work.HomologyIso.BdryPt) ≅
      (if k = 0 ∨ k = 1 then ModuleCat.of ℤ ℤ else ModuleCat.of ℤ PUnit)) := by
  obtain ⟨e⟩ := homeomorph_bdryPt
  exact ⟨(Work.Homology.intHomology_iso_of_homeomorph k e).some ≪≫
    (intHomology_addCircle k).some⟩

/-! ## §2  Transfer of models across homeomorphisms and homotopy equivalences -/

/-- **A model transports along a homeomorphism**: a special case of
`Work.PieceHomology.HomModel_ofHomotopyEquiv` (a homeomorphism is a homotopy equivalence).  This is
how a model of a piece of the geometry moves between the several descriptions of the same space
(cores, collars, quotients). -/
theorem HomModel_ofHomeomorph {X Y : TopCat} {r : ℤ → ℕ} (M : HomModel Y r) (e : X ≃ₜ Y) :
    Nonempty (HomModel X r) :=
  HomModel_ofHomotopyEquiv M (Homeomorph.toHomotopyEquiv e)

/-! ## §3  The per-cusp fields from the concrete computations -/

/-- **`eT2` from a homeomorphism with the standard torus model**: for every cusp whose filling
torus `rt.core.Torus v` is homeomorphic to `(ℝ/ℤ)²` and every concrete computation of
`H_k((ℝ/ℤ)²)`, the first field of `Work.HomologyIso.CuspData` follows in the declared type. -/
def eT2_of_homeomorph {rt : Work.Space.RTData} (v : Work.Space.Cusp)
    (e : rt.core.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ)))
    (h : ∀ k : ℕ, Work.HomologyIso.ModelT2 (k : ℤ) ≅
      LeanEval.Topology.intHomology k (TopCat.of (Fin 2 → AddCircle (1 : ℝ)))) (k : ℕ) :
    Work.HomologyIso.ModelT2 (k : ℤ) ≅
      LeanEval.Topology.intHomology k (TopCat.of (rt.core.Torus v)) :=
  (h k) ≪≫ ((Work.Homology.intHomology_iso_of_homeomorph k e).some).symm

/-- **`eTorus` from a homeomorphism with the standard cusp model**: the same for the cusp
cross-section `∂[-1,1]² × T²_v ≅ S¹ × (ℝ/ℤ)²`. -/
def eTorus_of_homeomorph {rt : Work.Space.RTData} (v : Work.Space.Cusp)
    (e : Work.HomologyIso.BdryPt × rt.core.Torus v ≃ₜ
      (AddCircle (1 : ℝ) × (Fin 2 → AddCircle (1 : ℝ))))
    (h : ∀ k : ℕ, Work.HomologyIso.ModelT (k : ℤ) ≅
      LeanEval.Topology.intHomology k
        (TopCat.of (AddCircle (1 : ℝ) × (Fin 2 → AddCircle (1 : ℝ))))) (k : ℕ) :
    Work.HomologyIso.ModelT (k : ℤ) ≅
      LeanEval.Topology.intHomology k
        (TopCat.of (Work.HomologyIso.BdryPt × rt.core.Torus v)) :=
  (h k) ≪≫ ((Work.Homology.intHomology_iso_of_homeomorph
    (X := TopCat.of (Work.HomologyIso.BdryPt × rt.core.Torus v))
    (Y := TopCat.of (AddCircle (1 : ℝ) × (Fin 2 → AddCircle (1 : ℝ)))) k e).some).symm

/-- **The three fields of `Work.HomologyIso.CuspData` from the concrete computations** (in the
declared types, verbatim). -/
def cuspDataOf {rt : Work.Space.RTData}
    (htorus : ∀ v : Work.Space.Cusp, ∀ k : ℕ, Work.HomologyIso.ModelT (k : ℤ) ≅
      LeanEval.Topology.intHomology k
        (TopCat.of (Work.HomologyIso.BdryPt × rt.core.Torus v)))
    (hmbar : ∀ k : ℕ, Work.HomologyIso.ModelA (k : ℤ) ≅
      LeanEval.Topology.intHomology k (TopCat.of rt.core.Mbar))
    (ht2 : ∀ v : Work.Space.Cusp, ∀ k : ℕ, Work.HomologyIso.ModelT2 (k : ℤ) ≅
      LeanEval.Topology.intHomology k (TopCat.of (rt.core.Torus v))) :
    Work.HomologyIso.CuspData (rt := rt) where
  eTorus := htorus
  eA := hmbar
  eT2 := ht2

/-! ## §4  The concrete torus computation: `eT2` for `(ℝ/ℤ)²` -/

/-- **`eT2` for the concrete torus**, with *no hypothesis left*: the standard `Δ`-structure
`torus2DeltaCx` of `T²` is realized in `(ℝ/ℤ)²` (`torus2RealizationData`), its `Δ`-chain complex
has the certificate `torus2SDR` (`torus2ChainIsoAlt` identifies it with the matrix complex
`torus2Cx`), and the comparison with singular chains is a quasi-isomorphism by Hatcher 2.27
(`Work.DeltaHomology.deltaChainMap_quasiIso`).  The result is in the *declared* type of the
per-cusp field `Work.HomologyIso.CuspData.eT2`. -/
def eT2_concrete (k : ℕ) :
    Work.HomologyIso.ModelT2 (k : ℤ) ≅
      LeanEval.Topology.intHomology k (TopCat.of (Fin 2 → AddCircle (1 : ℝ))) :=
  eT2_torus2 torus2RealizationData k

/-- **The per-cusp field `eT2` for an `rt` whose torus factor is the standard `(ℝ/ℤ)²`**: the
concrete computation `eT2_concrete` transported along the homeomorphism `rt.core.Torus v ≃ₜ (ℝ/ℤ)²`
(in `Work.RTInstance` it is the identity, definitionally; in `Work.Cusp` the homeomorphism is part
of the data). -/
def eT2_of_concrete {rt : Work.Space.RTData} (v : Work.Space.Cusp)
    (e : rt.core.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ))) (k : ℕ) :
    Work.HomologyIso.ModelT2 (k : ℤ) ≅
      LeanEval.Topology.intHomology k (TopCat.of (rt.core.Torus v)) :=
  eT2_of_homeomorph v e eT2_concrete k

/-! ## §5  The concrete cusp cross-section computation: `eTorus` for `∂[-1,1]² × (ℝ/ℤ)²` -/

/-- **`eTorus` for the concrete cusp cross-section**, with *no hypothesis left*: `∂[-1,1]² ≃ S¹`
(`homeomorph_bdryPt`), so the cross-section is `S¹ × T²` and its homology is `ℤ^{rankT k}` by the
Künneth-with-a-circle computation `intHomology_torus3` (Mayer–Vietoris along the two-arc cover of
the circle).  The result is in the *declared* type of the per-cusp field
`Work.HomologyIso.CuspData.eTorus`. -/
def eTorus_concrete (k : ℕ) :
    Work.HomologyIso.ModelT (k : ℤ) ≅ LeanEval.Topology.intHomology k
      (TopCat.of (Work.HomologyIso.BdryPt × (Fin 2 → AddCircle (1 : ℝ)))) :=
  (intHomology_torus3 k).some.symm ≪≫ ((Work.Homology.intHomology_iso_of_homeomorph
    (X := TopCat.of (Work.HomologyIso.BdryPt × (Fin 2 → AddCircle (1 : ℝ))))
    (Y := TopCat.of (AddCircle (1 : ℝ) × (Fin 2 → AddCircle (1 : ℝ)))) k
    (Homeomorph.prodCongr (homeomorph_bdryPt.some) (Homeomorph.refl _))).some).symm

/-- **The per-cusp field `eTorus` for an `rt` whose torus factor is the standard `(ℝ/ℤ)²`.** -/
def eTorus_of_concrete {rt : Work.Space.RTData} (v : Work.Space.Cusp)
    (hv : rt.core.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ))) (k : ℕ) :
    Work.HomologyIso.ModelT (k : ℤ) ≅
      LeanEval.Topology.intHomology k
        (TopCat.of (Work.HomologyIso.BdryPt × rt.core.Torus v)) :=
  eTorus_of_homeomorph v
    (Homeomorph.prodCongr (homeomorph_bdryPt.some) hv)
    (fun k => (intHomology_torus3 k).some.symm) k

/-! ## §6  The concrete per-cusp data: `Work.HomologyIso.CuspData` with only `eA` as input -/

/-- **The per-cusp data of `Work.HomologyIso` for the concrete instance.**  For an `rt` whose
filling tori are the standard `(ℝ/ℤ)²` (as in `Work.RTInstance`, definitionally), two of the three
declared fields are *proved*:

* `eT2` — `eT2_of_concrete` (the standard `Δ`-structure of `T²`, realized, with the Hatcher 2.27
  quasi-isomorphism);
* `eTorus` — `eTorus_of_concrete` (`∂[-1,1]² ≃ S¹` and Künneth with a circle);

and the only remaining input is the homology of the hyperbolic piece,
`hmbar : ModelA (k:ℤ) ≅ H_k(M̄)`. -/
def cuspData_of_concrete {rt : Work.Space.RTData}
    (hv : ∀ v : Work.Space.Cusp, rt.core.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ)))
    (hmbar : ∀ k : ℕ, Work.HomologyIso.ModelA (k : ℤ) ≅
      LeanEval.Topology.intHomology k (TopCat.of rt.core.Mbar)) :
    Work.HomologyIso.CuspData (rt := rt) :=
  cuspDataOf
    (fun v k => eTorus_of_concrete v (hv v) k)
    hmbar
    (fun v k => eT2_of_concrete v (hv v) k)

/-! ## §7  The challenge theorem from the concrete data and the bridge -/

/-- **The per-cusp inputs of the area for the concrete instance**: the concrete `CuspData` above,
together with the bridge data `B`. -/
def cuspInputs_of_concrete {rt : Work.Space.RTData}
    (hv : ∀ v : Work.Space.Cusp, rt.core.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ)))
    (hmbar : ∀ k : ℕ, Work.HomologyIso.ModelA (k : ℤ) ≅
      LeanEval.Topology.intHomology k (TopCat.of rt.core.Mbar))
    (B : Bridge (rt := rt) (cuspData_of_concrete hv hmbar).toPieceData) :
    Work.HomologyIso.CuspInputs (rt := rt) :=
  Bridge.toCuspInputs (cuspData_of_concrete hv hmbar) B

/-- **The challenge theorem, from the remaining inputs, the concrete computations of this area and
the bridge.**  The only geometric inputs left are the assembled space `M̂` with its connection and
curvature (`Work.HomologyIso.Remaining`), the identification of its filling tori with `(ℝ/ℤ)²`,
the homology of `M̄`, and the bridge data. -/
theorem aspherical_integer_homology_four_sphere_of_concrete {rt : Work.Space.RTData}
    (R : Work.HomologyIso.Remaining (rt := rt))
    (hv : ∀ v : Work.Space.Cusp, rt.core.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ)))
    (hmbar : ∀ k : ℕ, Work.HomologyIso.ModelA (k : ℤ) ≅
      LeanEval.Topology.intHomology k (TopCat.of rt.core.Mbar))
    (B : Bridge (rt := rt) (cuspData_of_concrete hv hmbar).toPieceData) :
    ∃ M : Closed4Manifold, M.IsAspherical ∧ M.IsIntegerHomologySphere :=
  Work.HomologyIso.aspherical_integer_homology_four_sphere_of_cusps R
    (cuspInputs_of_concrete hv hmbar B)

end

end Work.PieceHomology
