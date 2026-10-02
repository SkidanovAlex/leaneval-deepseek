import Mathlib
import Submission.Work.Serre.cylCMidDefs
import Submission.Work.Serre.CMidCollarDefs
import Submission.Work.Serre.CylCMidVan.relChainsR_excisionInterior
import Submission.Work.Serre.cylCollarShrink
import Submission.Work.StemsB.relChainsRIsoOfHomeo
import Submission.Work.Serre.csrPairFunctoriality
import Submission.Work.Serre.CsrSharp.Tools
import Submission.Work.Serre.DiscPair.relPairHomotopic
import Submission.Work.Serre.C1CylExplicit

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The collapse `C_*(X, q⁻¹b) → C_*(CMid q b, P_b)` is a quasi-isomorphism

For a continuous map `q : C(X,B)` and a point `b : B`, the "collapse" of the mapping cylinder
`Work.Serre.collapseMap q b : C_*(X, q⁻¹b;ℚ) ⟶ C_*(CMid q b, P_b;ℚ)` is induced by the inclusion of
`X` as the bottom copy of the mapping cylinder.  Geometrically `CMid q b = A ∪ P_b` is the union of
the bottom copy `A ≅ X` with the cone `P_b` on the fibre `q⁻¹b`, and the pair `(CMid q b, P_b)` is
the quotient `X/q⁻¹b`; hence the collapse is a quasi-isomorphism, in every degree (`k = 0`
included).

The proof factors the map of pairs as

  `(X, q⁻¹b) --e--> (cylBot q, A) --inclAU--> (U, Ub) --inclUC--> (CMid q b, M)`

where `e` is the homeomorphism of `X` with the bottom copy (`Submission.Work.Serre.C1CylExplicit`),
`U` is the collar part of `CMid q b` (so that `inclAU` is a homotopy equivalence of pairs, by the
collar shrink `cylShrink`) and `inclUC` is an excision (`interior M ∪ interior U = univ`,
`Work.Serre.CMidCollar.interior_union_eq_univ`).
-/

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

variable {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]

/-! ## The homeomorphism of `X` with the bottom copy of the mapping cylinder -/

theorem cylHomeoExplicitBot (q : C(X, B)) :
    ∃ e : X ≃ₜ ↥(cylBot q), ∀ x : X, (e x : cyl q) = cylIncl q x := by
  obtain ⟨e, he⟩ := cylHomeoExplicit q
  exact ⟨e, he⟩

/-- The chosen homeomorphism of `X` with the bottom copy `cylBot q` of the mapping cylinder. -/
noncomputable def botHomeo (q : C(X, B)) : X ≃ₜ ↥(cylBot q) :=
  Classical.choose (cylHomeoExplicitBot q)

theorem botHomeo_spec (q : C(X, B)) (x : X) :
    ((botHomeo q x : ↥(cylBot q)) : cyl q) = cylIncl q x :=
  Classical.choose_spec (cylHomeoExplicitBot q) x

/-- The bottom-copy map `X → cylBot q`. -/
def botE (q : C(X, B)) : C(X, ↥(cylBot q)) :=
  ⟨fun x => botHomeo q x, (botHomeo q).continuous⟩

/-- Its inverse. -/
def botEI (q : C(X, B)) : C(↥(cylBot q), X) :=
  ⟨fun y => (botHomeo q).symm y, (botHomeo q).symm.continuous⟩

theorem botE_apply (q : C(X, B)) (x : X) :
    ((botE q x : ↥(cylBot q)) : cyl q) = cylIncl q x := botHomeo_spec q x

theorem botE_botEI (q : C(X, B)) (y : ↥(cylBot q)) : botE q (botEI q y) = y :=
  Homeomorph.apply_symm_apply (botHomeo q) y

theorem botEI_botE (q : C(X, B)) (x : X) : botEI q (botE q x) = x :=
  Homeomorph.symm_apply_apply (botHomeo q) x

theorem botE_mapsTo (q : C(X, B)) (b : B) :
    Set.MapsTo (botE q) (q ⁻¹' ({b} : Set B)) (CMidCollar.A q b) := by
  intro x hx
  show cylRetract q ((botE q x : ↥(cylBot q)) : cyl q) = b
  rw [botE_apply]
  rw [show cylRetract q (cylIncl q x) = q x from DFunLike.congr_fun (cylRetract_cylIncl q) x]
  exact hx

theorem botEI_mapsTo (q : C(X, B)) (b : B) :
    Set.MapsTo (botEI q) (CMidCollar.A q b) (q ⁻¹' ({b} : Set B)) := by
  intro y hy
  show q (botEI q y) = b
  have h2 : cylIncl q (botEI q y) = (y : cyl q) := by
    rw [← botE_apply q (botEI q y), botE_botEI]
  rw [← show cylRetract q (cylIncl q (botEI q y)) = q (botEI q y) from
    DFunLike.congr_fun (cylRetract_cylIncl q) (botEI q y)]
  rw [h2]
  exact hy

theorem botE_comp_botEI (q : C(X, B)) :
    (botE q).comp (botEI q) = ContinuousMap.id ↥(cylBot q) := by
  apply ContinuousMap.ext
  intro y
  exact botE_botEI q y

theorem botEI_comp_botE (q : C(X, B)) :
    (botEI q).comp (botE q) = ContinuousMap.id X := by
  apply ContinuousMap.ext
  intro x
  exact botEI_botE q x

/-- The collapse on the level of the bottom copy: `X ≅ cylBot q` is an isomorphism on relative
rational homology. -/
theorem isIso_botE (q : C(X, B)) (b : B) (n : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (relChainsRPairMap (q ⁻¹' ({b} : Set B)) (CMidCollar.A q b) (botE q)
        (botE_mapsTo q b)) n) := by
  refine IsIso.mk ⟨HomologicalComplex.homologyMap (relChainsRPairMap (CMidCollar.A q b)
    (q ⁻¹' ({b} : Set B)) (botEI q) (botEI_mapsTo q b)) n, ?_, ?_⟩
  · rw [← HomologicalComplex.homologyMap_comp,
      CsrSharp.Tools.relChainsRPairMap_comp (botE q) (botEI q) (botE_mapsTo q b)
        (botEI_mapsTo q b) (hg'' := (botEI_mapsTo q b).comp (botE_mapsTo q b)),
      CsrSharp.Tools.relChainsRPairMap_congr (botEI_comp_botE q)
        ((botEI_mapsTo q b).comp (botE_mapsTo q b)) (fun _ hx => hx),
      CsrSharp.Tools.relChainsRPairMap_id' (q ⁻¹' ({b} : Set B)) (fun _ hx => hx),
      HomologicalComplex.homologyMap_id]
  · rw [← HomologicalComplex.homologyMap_comp,
      CsrSharp.Tools.relChainsRPairMap_comp (botEI q) (botE q) (botEI_mapsTo q b)
        (botE_mapsTo q b) (hg'' := (botE_mapsTo q b).comp (botEI_mapsTo q b)),
      CsrSharp.Tools.relChainsRPairMap_congr (botE_comp_botEI q)
        ((botE_mapsTo q b).comp (botEI_mapsTo q b)) (fun _ hx => hx),
      CsrSharp.Tools.relChainsRPairMap_id' (CMidCollar.A q b) (fun _ hx => hx),
      HomologicalComplex.homologyMap_id]

/-! ## The collar retraction `(U, Ub) → (cylBot q, A)` -/

/-- The projection of the collar part `U q b` of `CMid q b` to the collar of the cylinder. -/
def pairProj (q : C(X, B)) (b : B) : C(↥(CMidCollar.U q b), ↥(cylCollar q)) where
  toFun x := ⟨(((x : ↥(CMidCollar.U q b)) : ↥(CMidCollar.Mid q b)) : cyl q), x.2⟩
  continuous_toFun := Continuous.subtype_mk
    (continuous_subtype_val.comp continuous_subtype_val) (fun x => x.2)

/-- The collar shrink at time `1`, as a map `U q b → cylBot q`. -/
def pairRetr (q : C(X, B)) (b : B) : C(↥(CMidCollar.U q b), ↥(cylBot q)) :=
  (cylShrinkToBot q).comp (pairProj q b)

theorem pairRetr_mapsTo (q : C(X, B)) (b : B) :
    Set.MapsTo (pairRetr q b) (CMidCollar.Ub q b) (CMidCollar.A q b) := by
  intro x hx
  show cylRetract q ((pairRetr q b x : ↥(cylBot q)) : cyl q) = b
  have hcoe : ((pairRetr q b x : ↥(cylBot q)) : cyl q)
      = ((cylShrink q 1 (pairProj q b x) : ↥(cylCollar q)) : cyl q) := rfl
  rw [hcoe, cylRetract_cylShrink]
  exact hx

theorem pairRetr_comp_inclAU (q : C(X, B)) (b : B) :
    (pairRetr q b).comp (CMidCollar.inclAU q b) = ContinuousMap.id ↥(cylBot q) := by
  apply ContinuousMap.ext
  intro y
  apply Subtype.ext
  have hproj : pairProj q b (CMidCollar.inclAU q b y)
      = ⟨(y : cyl q), cylBot_subset_cylCollar q y.2⟩ := rfl
  show ((cylShrink q 1 (pairProj q b (CMidCollar.inclAU q b y)) : ↥(cylCollar q)) : cyl q)
      = ((y : ↥(cylBot q)) : cyl q)
  rw [hproj]
  exact congrArg (fun z : ↥(cylCollar q) => (z : cyl q))
    (cylShrink_fixes_bot q 1 (y := ⟨(y : cyl q), cylBot_subset_cylCollar q y.2⟩) y.2)

theorem pairRetr_inclAU (q : C(X, B)) (b : B) (y : ↥(cylBot q)) :
    pairRetr q b (CMidCollar.inclAU q b y) = y :=
  congrFun (congrArg DFunLike.coe (pairRetr_comp_inclAU q b)) y

/-- The constant homotopy on the bottom copy. -/
def pairHomA (q : C(X, B)) (b : B) :
    ContinuousMap.Homotopy ((pairRetr q b).comp (CMidCollar.inclAU q b))
      (ContinuousMap.id ↥(cylBot q)) :=
  ContinuousMap.Homotopy.mk (((pairRetr q b).comp (CMidCollar.inclAU q b)).comp ContinuousMap.snd)
    (fun _ => rfl) (fun y => pairRetr_inclAU q b y)

theorem pairHomA_mapsTo (q : C(X, B)) (b : B) (t : unitInterval) {y : ↥(cylBot q)}
    (hy : y ∈ CMidCollar.A q b) : pairHomA q b (t, y) ∈ CMidCollar.A q b := by
  rw [show pairHomA q b (t, y) = pairRetr q b (CMidCollar.inclAU q b y) from rfl,
    pairRetr_inclAU]
  exact hy

theorem continuous_pairShrink (q : C(X, B)) (b : B) :
    Continuous fun p : unitInterval × ↥(CMidCollar.U q b) =>
      ((cylShrink q p.1 (pairProj q b p.2) : ↥(cylCollar q)) : cyl q) := by
  have hEq : (fun p : unitInterval × ↥(CMidCollar.U q b) =>
        ((cylShrink q p.1 (pairProj q b p.2) : ↥(cylCollar q)) : cyl q))
      = fun p : unitInterval × ↥(CMidCollar.U q b) =>
          (((cylShrinkHomotopy q) (p.1, pairProj q b p.2) : ↥(cylCollar q)) : cyl q) := by
    funext p
    exact congrArg Subtype.val (cylShrinkHomotopy_apply q p.1 (pairProj q b p.2))
  rw [hEq]
  exact continuous_subtype_val.comp ((cylShrinkHomotopy q).continuous.comp
    ((ContinuousMap.prodMap (ContinuousMap.id unitInterval) (pairProj q b)).continuous))

/-- The collar shrink, as a self-map of the collar part of `CMid q b`. -/
def pairShrink (q : C(X, B)) (b : B) :
    C(unitInterval × ↥(CMidCollar.U q b), ↥(CMidCollar.U q b)) where
  toFun p := ⟨⟨((cylShrink q p.1 (pairProj q b p.2) : ↥(cylCollar q)) : cyl q),
      CMidCollar.cylShrink_mem_Mid q b p.1 p.2.1.2⟩,
    (cylShrink q p.1 (pairProj q b p.2)).2⟩
  continuous_toFun := Continuous.subtype_mk
    (Continuous.subtype_mk (continuous_pairShrink q b)
      (fun p => CMidCollar.cylShrink_mem_Mid q b p.1 p.2.1.2))
    (fun p => (cylShrink q p.1 (pairProj q b p.2)).2)

/-- The shrink homotopy, from the identity to `inclAU ∘ pairRetr`. -/
def pairHomB (q : C(X, B)) (b : B) :
    ContinuousMap.Homotopy (ContinuousMap.id ↥(CMidCollar.U q b))
      ((CMidCollar.inclAU q b).comp (pairRetr q b)) where
  toContinuousMap := pairShrink q b
  map_zero_left := fun x => by
    apply Subtype.ext
    apply Subtype.ext
    show ((cylShrink q 0 (pairProj q b x) : ↥(cylCollar q)) : cyl q) = (x : cyl q)
    rw [← cylShrinkHomotopy_apply q 0 (pairProj q b x)]
    exact congrArg Subtype.val ((cylShrinkHomotopy q).map_zero_left (pairProj q b x))
  map_one_left := fun x => by
    apply Subtype.ext
    apply Subtype.ext
    show ((cylShrink q 1 (pairProj q b x) : ↥(cylCollar q)) : cyl q)
      = ((CMidCollar.inclAU q b (pairRetr q b x) : ↥(CMidCollar.U q b)) : cyl q)
    rfl

theorem pairHomB_mapsTo (q : C(X, B)) (b : B) (t : unitInterval) {x : ↥(CMidCollar.U q b)}
    (hx : x ∈ CMidCollar.Ub q b) : pairHomB q b (t, x) ∈ CMidCollar.Ub q b := by
  show cylRetract q (((pairShrink q b (t, x) : ↥(CMidCollar.U q b)) : ↥(CMidCollar.Mid q b))
    : cyl q) = b
  have hcoe : (((pairShrink q b (t, x) : ↥(CMidCollar.U q b)) : ↥(CMidCollar.Mid q b)) : cyl q)
      = ((cylShrink q t (pairProj q b x) : ↥(cylCollar q)) : cyl q) := rfl
  rw [hcoe, cylRetract_cylShrink]
  exact hx

/-- **The inclusion `(cylBot q, A) → (U, Ub)` is a quasi-isomorphism**: it is a homotopy
equivalence of pairs, by the collar shrink. -/
theorem isIso_inclAU (q : C(X, B)) (b : B) (n : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (relChainsRPairMap (CMidCollar.A q b) (CMidCollar.Ub q b) (CMidCollar.inclAU q b)
        (CMidCollar.mapsTo_inclAU q b)) n) := by
  have hcomp₁ := CsrSharp.Tools.relChainsRPairMap_comp (CMidCollar.inclAU q b) (pairRetr q b)
    (CMidCollar.mapsTo_inclAU q b) (pairRetr_mapsTo q b)
    (hg'' := (pairRetr_mapsTo q b).comp (CMidCollar.mapsTo_inclAU q b))
  have hcomp₂ := CsrSharp.Tools.relChainsRPairMap_comp (pairRetr q b) (CMidCollar.inclAU q b)
    (pairRetr_mapsTo q b) (CMidCollar.mapsTo_inclAU q b)
    (hg'' := (CMidCollar.mapsTo_inclAU q b).comp (pairRetr_mapsTo q b))
  have h1 : HomologicalComplex.homologyMap (relChainsRPairMap (CMidCollar.A q b)
        (CMidCollar.Ub q b) (CMidCollar.inclAU q b) (CMidCollar.mapsTo_inclAU q b)) n
      ≫ HomologicalComplex.homologyMap (relChainsRPairMap (CMidCollar.Ub q b)
        (CMidCollar.A q b) (pairRetr q b) (pairRetr_mapsTo q b)) n = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, hcomp₁,
      CsrSharp.Tools.relChainsRPairMap_congr (pairRetr_comp_inclAU q b)
        ((pairRetr_mapsTo q b).comp (CMidCollar.mapsTo_inclAU q b)) (fun _ hx => hx),
      CsrSharp.Tools.relChainsRPairMap_id' (CMidCollar.A q b) (fun _ hx => hx),
      HomologicalComplex.homologyMap_id]
  have h2 : HomologicalComplex.homologyMap (relChainsRPairMap (CMidCollar.Ub q b)
        (CMidCollar.A q b) (pairRetr q b) (pairRetr_mapsTo q b)) n
      ≫ HomologicalComplex.homologyMap (relChainsRPairMap (CMidCollar.A q b)
        (CMidCollar.Ub q b) (CMidCollar.inclAU q b) (CMidCollar.mapsTo_inclAU q b)) n = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, hcomp₂,
      ← DiscPair.relPairHomotopic (A := CMidCollar.Ub q b) (B := CMidCollar.Ub q b)
        (f := ContinuousMap.id ↥(CMidCollar.U q b))
        (g := (CMidCollar.inclAU q b).comp (pairRetr q b))
        (fun _ hx => hx) ((CMidCollar.mapsTo_inclAU q b).comp (pairRetr_mapsTo q b))
        (pairHomB q b) (fun t x hx => pairHomB_mapsTo q b t hx) n,
      CsrSharp.Tools.relChainsRPairMap_id' (CMidCollar.Ub q b) (fun _ hx => hx),
      HomologicalComplex.homologyMap_id]
  exact IsIso.mk ⟨_, h1, h2⟩

/-! ## Excision: `(U, Ub) → (CMid q b, M)` -/

theorem isIso_inclUC (q : C(X, B)) (b : B) (n : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (relChainsRPairMap (CMidCollar.Ub q b) (CMidCollar.M q b) (CMidCollar.inclUC q b)
        (CMidCollar.mapsTo_inclUC q b)) n) := by
  have h := CylCMidVan.relChainsR_excisionInterior (X := ↥(CMidCollar.Mid q b))
    (CMidCollar.U q b) (CMidCollar.M q b) (CMidCollar.interior_union_eq_univ q b) n
  have hEq : relChainsRInclPairMap (TopCat.of ↥(CMidCollar.Mid q b)) (CMidCollar.U q b)
        (CMidCollar.M q b)
      = relChainsRPairMap (CMidCollar.Ub q b) (CMidCollar.M q b) (CMidCollar.inclUC q b)
        (CMidCollar.mapsTo_inclUC q b) := by
    unfold relChainsRInclPairMap relChainsRPairMap
    refine CsrSharp.Tools.csrRelMapOf_congr rfl ?_ _ _
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    exact Subtype.ext rfl
  rwa [hEq] at h

/-! ## The factorization and the theorem -/

theorem inclAC_comp_botE (q : C(X, B)) (b : B) :
    (CMidCollar.inclAC q b).comp (botE q) = toCMid q b := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  rw [toCMid_coe]
  show ((botE q x : ↥(cylBot q)) : cyl q) = cylIncl q x
  exact botE_apply q x

theorem inclUC_comp_inclAU_comp_botE (q : C(X, B)) (b : B) :
    ((CMidCollar.inclUC q b).comp (CMidCollar.inclAU q b)).comp (botE q) = toCMid q b := by
  rw [CMidCollar.inclUC_comp_inclAU]
  exact inclAC_comp_botE q b

/-- **The factorization of the collapse.** -/
theorem collapseMap_eq (q : C(X, B)) (b : B) :
    collapseMap q b
      = relChainsRPairMap (q ⁻¹' ({b} : Set B)) (CMidCollar.A q b) (botE q) (botE_mapsTo q b)
        ≫ (relChainsRPairMap (CMidCollar.A q b) (CMidCollar.Ub q b) (CMidCollar.inclAU q b)
              (CMidCollar.mapsTo_inclAU q b)
            ≫ relChainsRPairMap (CMidCollar.Ub q b) (CMidCollar.M q b) (CMidCollar.inclUC q b)
                (CMidCollar.mapsTo_inclUC q b)) := by
  have hmap : ((CMidCollar.inclUC q b).comp (CMidCollar.inclAU q b)).comp (botE q)
      = toCMid q b := inclUC_comp_inclAU_comp_botE q b
  rw [CsrSharp.Tools.relChainsRPairMap_comp (CMidCollar.inclAU q b) (CMidCollar.inclUC q b)
      (CMidCollar.mapsTo_inclAU q b) (CMidCollar.mapsTo_inclUC q b)
      (hg'' := (CMidCollar.mapsTo_inclUC q b).comp (CMidCollar.mapsTo_inclAU q b))]
  rw [CsrSharp.Tools.relChainsRPairMap_comp (botE q)
      ((CMidCollar.inclUC q b).comp (CMidCollar.inclAU q b)) (botE_mapsTo q b)
      ((CMidCollar.mapsTo_inclUC q b).comp (CMidCollar.mapsTo_inclAU q b))
      (hg'' := ((CMidCollar.mapsTo_inclUC q b).comp (CMidCollar.mapsTo_inclAU q b)).comp
        (botE_mapsTo q b))]
  unfold collapseMap
  exact (CsrSharp.Tools.relChainsRPairMap_congr hmap
    (((CMidCollar.mapsTo_inclUC q b).comp (CMidCollar.mapsTo_inclAU q b)).comp
      (botE_mapsTo q b)) _).symm

theorem isIso_collapseMap {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]
    (q : C(X, B)) (b : B) (k : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap (Work.Serre.collapseMap q b) k) := by
  haveI h1 : CategoryTheory.IsIso (HomologicalComplex.homologyMap
    (relChainsRPairMap (q ⁻¹' ({b} : Set B)) (CMidCollar.A q b) (botE q)
      (botE_mapsTo q b)) k) := isIso_botE q b k
  haveI h2 : CategoryTheory.IsIso (HomologicalComplex.homologyMap
    (relChainsRPairMap (CMidCollar.A q b) (CMidCollar.Ub q b) (CMidCollar.inclAU q b)
      (CMidCollar.mapsTo_inclAU q b)) k) := isIso_inclAU q b k
  haveI h3 : CategoryTheory.IsIso (HomologicalComplex.homologyMap
    (relChainsRPairMap (CMidCollar.Ub q b) (CMidCollar.M q b) (CMidCollar.inclUC q b)
      (CMidCollar.mapsTo_inclUC q b)) k) := isIso_inclUC q b k
  rw [collapseMap_eq q b, HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_comp]
  haveI h23 : CategoryTheory.IsIso (HomologicalComplex.homologyMap
    (relChainsRPairMap (CMidCollar.A q b) (CMidCollar.Ub q b) (CMidCollar.inclAU q b)
      (CMidCollar.mapsTo_inclAU q b)) k
    ≫ HomologicalComplex.homologyMap
      (relChainsRPairMap (CMidCollar.Ub q b) (CMidCollar.M q b) (CMidCollar.inclUC q b)
        (CMidCollar.mapsTo_inclUC q b)) k) := CategoryTheory.IsIso.comp_isIso
  exact CategoryTheory.IsIso.comp_isIso

end

end Work.Serre
