import Mathlib
import Submission.Work.Serre.DiscPair.fibreRestrictionContractible
import Submission.Work.Serre.DiscPair.cvnReduction
import Submission.Work.Serre.DiscPair.cylPreimageRelChainsIso
import Submission.Work.Serre.isSerreFibration_restrictFibre
import Submission.Work.Thom.relCohHomeomorph
import Submission.Work.Serre.OneCell.Prelim
import Submission.Work.Serre.DiscPair.pathConnectedSpace_preimage_of_isSerreFibration

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Propagation of a fibre value of the relative class from a weakly contractible subset

Let `q : C(X,B)` be a Serre fibration, `V ⊆ B` a closed subset containing `b`, path connected with
all homotopy groups trivial at `b` (so `V` is *weakly contractible*).  Write

`A := range (cylIncl q) ⊂ cyl q`,  `M_V := (cylRetract q) ⁻¹' V`,  `M_b := (cylRetract q) ⁻¹' {b}`

for the part of the mapping cylinder over `V` (resp. over `b`).  The main theorem
`fibreValuePropagation` says: if a relative class `u ∈ H^{r+1}(cyl q, A;ℚ)` restricts to a
*non-zero* class on the pair over `V`, then it restricts to a non-zero class on the pair over `b`.

The mathematics is that the pair over `V` is the mapping cylinder pair of the *restricted*
fibration `q|_V : q ⁻¹' V → V` (`Work.Serre.DiscPair.cylPreimageHomeo`), over the weakly
contractible base `V`, so Serre's theorem in range form
(`Work.Serre.DiscPair.fibreRestrictionContractible`) applies to it: the restriction map to the
fibre pair over `b` is an isomorphism.  Transporting along the homeomorphism of pairs and using
the functoriality of `Work.Thom.relCohMap` gives the claim.
-/

namespace Work.Serre.DiscPair

open CategoryTheory CategoryTheory.Limits

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

/-! ## Notation -/

/-- The part of the mapping cylinder over a subset of the base. -/
abbrev fvpP {B X : Type} [TopologicalSpace B] [TopologicalSpace X] (q : C(X, B)) (V : Set B) :
    Set (Work.Serre.cyl q) :=
  (Work.Serre.cylRetract q) ⁻¹' V

/-- The bottom copy of the source inside the mapping cylinder. -/
abbrev fvpB {B X : Type} [TopologicalSpace B] [TopologicalSpace X] (q : C(X, B)) :
    Set (Work.Serre.cyl q) :=
  Set.range (Work.Serre.cylIncl q)

/-- The part of the bottom copy lying in a given subspace of the cylinder. -/
abbrev fvpS {B X : Type} [TopologicalSpace B] [TopologicalSpace X] (q : C(X, B))
    (S : Set (Work.Serre.cyl q)) : Set ↥S :=
  {x | (x : Work.Serre.cyl q) ∈ fvpB q}

/-- The inclusion of a subspace. -/
abbrev fvpIncl {Z : Type} [TopologicalSpace Z] (S : Set Z) : C(↥S, Z) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-! ## The two cylinders -/

/-- The identity `qS q S = restrictFibre q S`. -/
theorem qS_eq_restrictFibre {E Γ : Type} [TopologicalSpace E] [TopologicalSpace Γ]
    (q : C(E, Γ)) (S : Set Γ) : qS q S = Work.Serre.restrictFibre q S := rfl

/-- The retraction of the mapping cylinder is compatible with the identification of
`cyl (q|_S)` with the part `(cylRetract q) ⁻¹' S` of `cyl q` given by `cylPreimageHomeo`. -/
theorem cylRetract_cylPreimageHomeo {X Γ : Type} [TopologicalSpace X] [TopologicalSpace Γ]
    (q : C(X, Γ)) (S : Set Γ) (hS : IsClosed S) (y : Work.Serre.cyl (qS q S)) :
    (Work.Serre.cylRetract q (cylPreimageHomeo q S hS y) : Γ)
      = ((Work.Serre.cylRetract (qS q S) y : ↥S) : Γ) := by
  rw [cylPreimageHomeo_apply]
  revert y
  refine Quotient.ind ?_
  intro a
  rw [cylPreimageLift_mk]
  cases a with
  | inl z => rfl
  | inr y => rfl

/-! ## The fibre of the restricted fibration -/

/-- **The fibre of the restricted map over `b` is the fibre of `q` over `b`.** -/
noncomputable def homeoFibreRestrictFibre {E Γ : Type} [TopologicalSpace E] [TopologicalSpace Γ]
    (q : C(E, Γ)) (S : Set Γ) (b : Γ) (hb : b ∈ S) :
    Work.StemsB.fibre (Work.Serre.restrictFibre q S) ⟨b, hb⟩ ≃ₜ Work.StemsB.fibre q b where
  toFun x := ⟨x.1.1, by
    have h : ((Work.Serre.restrictFibre q S) x.1 : ↥S) = ⟨b, hb⟩ := x.2
    exact congrArg Subtype.val h⟩
  invFun y := ⟨⟨y.1, by show q y.1 ∈ S; rw [y.2]; exact hb⟩, by
    apply Subtype.ext; exact y.2⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv y := by apply Subtype.ext; rfl
  continuous_toFun :=
    Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  continuous_invFun :=
    Continuous.subtype_mk
      (Continuous.subtype_mk continuous_subtype_val (fun y => by
        show q y.1 ∈ S; rw [y.2]; exact hb)) _

/-- The vanishing of the rational homology of the fibre transports to the restricted fibration. -/
theorem isZero_ratH_fibre_qS {E Γ : Type} [TopologicalSpace E] [TopologicalSpace Γ]
    (q : C(E, Γ)) (S : Set Γ) (b : Γ) (hb : b ∈ S) (t : ℕ)
    (h : CategoryTheory.Limits.IsZero
      (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q b)) t)) :
    CategoryTheory.Limits.IsZero (Work.Serre.ratH
      (TopCat.of (Work.StemsB.fibre (qS q S) ⟨b, hb⟩)) t) :=
  Work.Serre.OneCell.isZero_ratH_of_homeo (homeoFibreRestrictFibre q S b hb) t h

/-- A non-zero rational homology line of the fibre transports to the restricted fibration. -/
theorem nonempty_ratH_iso_fibre_qS {E Γ : Type} [TopologicalSpace E] [TopologicalSpace Γ]
    (q : C(E, Γ)) (S : Set Γ) (b : Γ) (hb : b ∈ S) (t : ℕ)
    (h : Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q b)) t
      ≅ ModuleCat.of ℚ ℚ)) :
    Nonempty (Work.Serre.ratH
      (TopCat.of (Work.StemsB.fibre (qS q S) ⟨b, hb⟩)) t
      ≅ ModuleCat.of ℚ ℚ) := by
  obtain ⟨e⟩ := Work.Serre.OneCell.nonempty_ratH_iso_of_homeo
    (homeoFibreRestrictFibre q S b hb) t
  exact ⟨e ≪≫ Classical.choice h⟩

/-- Path connectedness of the fibre transports to the restricted fibration. -/
theorem pathConnectedSpace_fibre_qS {E Γ : Type} [TopologicalSpace E] [TopologicalSpace Γ]
    (q : C(E, Γ)) (S : Set Γ) (b : Γ) (hb : b ∈ S)
    (h : PathConnectedSpace (Work.StemsB.fibre q b)) :
    PathConnectedSpace (Work.StemsB.fibre (qS q S) ⟨b, hb⟩) := by
  rw [qS_eq_restrictFibre]
  haveI := h
  refine ⟨⟨(homeoFibreRestrictFibre q S b hb).symm
      (Classical.choice (inferInstance : Nonempty (Work.StemsB.fibre q b)))⟩, fun x y => ?_⟩
  have hj := (PathConnectedSpace.joined ((homeoFibreRestrictFibre q S b hb) x)
    ((homeoFibreRestrictFibre q S b hb) y)).map
    (homeoFibreRestrictFibre q S b hb).symm.continuous
  simpa only [Homeomorph.symm_apply_apply] using hj

/-! ## The main theorem -/

set_option maxHeartbeats 4000000 in
theorem fibreValuePropagation_aux {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]
    (q : C(X, B)) (hq : Work.StemsB.IsSerreFibration q) {V : Set B} (hV : IsClosed V)
    (b : B) (hb : b ∈ V) (r N : ℕ) (hr : 1 ≤ r) (hrN : r + 1 ≤ N)
    (hVpc : PathConnectedSpace ↥V)
    (hVc : ∀ i : ℕ, Subsingleton (HomotopyGroup (Fin i) ↥V ⟨b, hb⟩))
    (hXpc : PathConnectedSpace X)
    (hpcV : PathConnectedSpace (Work.StemsB.fibre q b))
    (hvanV : ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q b)) t))
    (hgenV : Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q b)) r
      ≅ ModuleCat.of ℚ ℚ))
    (u : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q) (fvpB q))
    (hu : (Work.Thom.relCohMap (fvpIncl (fvpP q V)) (fvpS q (fvpP q V)) (fvpB q)
        (fun _ hx => hx) ℚ (r + 1)).hom u ≠ 0) :
    (Work.Thom.relCohMap (fvpIncl (fvpP q ({b} : Set B))) (fvpS q (fvpP q ({b} : Set B)))
      (fvpB q) (fun _ hx => hx) ℚ (r + 1)).hom u ≠ 0 := by
  classical
  -- ## the restricted fibration is a Serre fibration
  have hqS : Work.StemsB.IsSerreFibration (qS q V) := by
    rw [qS_eq_restrictFibre]
    exact Work.Serre.isSerreFibration_restrictFibre q hq V
  -- ## the total space of the restricted fibration is path connected
  have hX' : PathConnectedSpace ↥(q ⁻¹' V) :=
    pathConnectedSpace_preimage_of_isSerreFibration q hq hVpc b hb hpcV
  -- ## the fibre data of the restricted fibration
  have hpc' : PathConnectedSpace (Work.StemsB.fibre (qS q V) ⟨b, hb⟩) :=
    pathConnectedSpace_fibre_qS q V b hb hpcV
  have hvan' : ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero
        (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre (qS q V) ⟨b, hb⟩)) t) :=
    fun t ht htr htN => isZero_ratH_fibre_qS q V b hb t (hvanV t ht htr htN)
  have hgen' : Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre (qS q V) ⟨b, hb⟩)) r
      ≅ ModuleCat.of ℚ ℚ) :=
    nonempty_ratH_iso_fibre_qS q V b hb r hgenV
  -- ## the restriction map of the restricted fibration is an isomorphism
  haveI hρ : IsIso (Work.Thom.relCohMap (fvpIncl (fvpP (qS q V) ({⟨b, hb⟩} : Set ↥V)))
      (fvpS (qS q V) (fvpP (qS q V) ({⟨b, hb⟩} : Set ↥V)))
      (fvpB (qS q V)) (fun _ hx => hx) ℚ (r + 1)) :=
    fibreRestrictionContractible (qS q V) hqS ⟨b, hb⟩ r N hr hVpc hVc hX' hpc' hvan' hgen' hrN
  -- ## the class on the part over `V`
  set uV : Work.Thom.RelCoh ℚ (r + 1) ↥(fvpP q V) (fvpS q (fvpP q V)) :=
    (Work.Thom.relCohMap (fvpIncl (fvpP q V)) (fvpS q (fvpP q V)) (fvpB q)
      (fun _ hx => hx) ℚ (r + 1)).hom u with huVdef
  have huV_ne : uV ≠ 0 := hu
  -- ## the commutativity of the retraction with the identification
  have hsym : ∀ x : ↥(fvpP (qS q V) ({⟨b, hb⟩} : Set ↥V)),
      (Work.Serre.cylRetract q ((cylPreimageHomeo q V hV) x.1) : B) = b := by
    intro x
    have h := cylRetract_cylPreimageHomeo q V hV x.1
    have hx : (Work.Serre.cylRetract (qS q V) x.1 : ↥V) = ⟨b, hb⟩ := by
      show (Work.Serre.cylRetract (qS q V) x.1 : ↥V) ∈ ({⟨b, hb⟩} : Set ↥V)
      exact x.2
    rw [h]
    exact congrArg (fun z : ↥V => (z : B)) hx
  -- ## the restriction of the homeomorphism to the fibre pairs
  let eF : C(↥(fvpP (qS q V) ({⟨b, hb⟩} : Set ↥V)), ↥(fvpP q ({b} : Set B))) :=
    ⟨fun x => ⟨(cylPreimageHomeo q V hV) x.1, by
        show (Work.Serre.cylRetract q ((cylPreimageHomeo q V hV) x.1) : B) = b
        exact hsym x⟩,
      by fun_prop⟩
  -- ## the square relating the two inclusions
  have hsquare : (fvpIncl (fvpP q ({b} : Set B))).comp eF
      = ((fvpIncl (fvpP q V)).comp
          (cylPreimageHomeo q V hV : C(Work.Serre.cyl (qS q V), ↥(fvpP q V)))).comp
        (fvpIncl (fvpP (qS q V) ({⟨b, hb⟩} : Set ↥V))) := by
    ext x
    rfl
  -- ## `eF` carries the bottom copy of the fibre into the bottom copy
  have hf1 : ∀ x ∈ fvpS (qS q V) (fvpP (qS q V) (Set.singleton (⟨b, hb⟩ : ↥V))),
      eF x ∈ fvpS q (fvpP q ({b} : Set B)) :=
    fun x hx => (cylPreimageHomeo_range q V hV x.1).mpr hx
  -- ## the composite `cyl (q|_V) → π⁻¹V → cyl q` carries the bottom copy into the bottom copy
  have hg2 : ∀ y ∈ fvpB (qS q V),
      ((fvpIncl (fvpP q V)).comp
        (cylPreimageHomeo q V hV : C(Work.Serre.cyl (qS q V), ↥(fvpP q V)))) y ∈ fvpB q :=
    fun y hy => (cylPreimageHomeo_range q V hV y).mpr hy
  -- ## the homeomorphism carries the bottom copy into the bottom copy
  have hf3 : ∀ x ∈ fvpB (qS q V), (cylPreimageHomeo q V hV : C(Work.Serre.cyl (qS q V),
        ↥(fvpP q V))) x ∈ fvpS q (fvpP q V) :=
    fun x hx => (cylPreimageHomeo_range q V hV x).mpr hx
  -- ## the homeomorphism of pairs induces an isomorphism on relative cohomology
  have hsymm : ∀ y ∈ fvpS q (fvpP q V), ((cylPreimageHomeo q V hV).symm
      : C(↥(fvpP q V), Work.Serre.cyl (qS q V))) y ∈ fvpB (qS q V) := by
    intro y hy
    refine (cylPreimageHomeo_range q V hV ((cylPreimageHomeo q V hV).symm y)).mp ?_
    simpa using hy
  haveI hΦiso : IsIso (Work.Thom.relCohMap (cylPreimageHomeo q V hV
      : C(Work.Serre.cyl (qS q V), ↥(fvpP q V))) (fvpB (qS q V)) (fvpS q (fvpP q V))
      hf3 ℚ (r + 1)) := by
    refine IsIso.mk ⟨Work.Thom.relCohMap ((cylPreimageHomeo q V hV).symm
        : C(↥(fvpP q V), Work.Serre.cyl (qS q V))) (fvpS q (fvpP q V)) (fvpB (qS q V))
        hsymm ℚ (r + 1), ?_, ?_⟩
    · rw [Work.Thom.relCohMap_compA (fvpS q (fvpP q V)) (fvpB (qS q V))
        (fvpS q (fvpP q V))
        ((cylPreimageHomeo q V hV).symm : C(↥(fvpP q V), Work.Serre.cyl (qS q V)))
        (cylPreimageHomeo q V hV : C(Work.Serre.cyl (qS q V), ↥(fvpP q V)))
        hsymm hf3 (fun x hx =>
          (Homeomorph.apply_symm_apply (cylPreimageHomeo q V hV) x).symm ▸ hx)]
      rw [Work.Thom.relCohMap_congrA (fvpS q (fvpP q V)) (fvpS q (fvpP q V))
        (show ((cylPreimageHomeo q V hV : C(Work.Serre.cyl (qS q V), ↥(fvpP q V))).comp
            ((cylPreimageHomeo q V hV).symm : C(↥(fvpP q V), Work.Serre.cyl (qS q V))))
            = ContinuousMap.id ↥(fvpP q V) from by
          ext x
          simp only [ContinuousMap.comp_apply, ContinuousMap.id_apply]
          exact congrArg Subtype.val
            (Homeomorph.apply_symm_apply (cylPreimageHomeo q V hV) x))
        (fun x hx => by simpa using hx) (fun _ hx => hx) ℚ (r + 1)]
      exact Work.Thom.relCohMap_idA (fvpS q (fvpP q V)) ℚ (r + 1)
    · rw [Work.Thom.relCohMap_compA (fvpB (qS q V)) (fvpS q (fvpP q V)) (fvpB (qS q V))
        (cylPreimageHomeo q V hV : C(Work.Serre.cyl (qS q V), ↥(fvpP q V)))
        ((cylPreimageHomeo q V hV).symm : C(↥(fvpP q V), Work.Serre.cyl (qS q V)))
        hf3 hsymm (fun x hx =>
          (Homeomorph.symm_apply_apply (cylPreimageHomeo q V hV) x).symm ▸ hx)]
      rw [Work.Thom.relCohMap_congrA (fvpB (qS q V)) (fvpB (qS q V))
        (show (((cylPreimageHomeo q V hV).symm : C(↥(fvpP q V), Work.Serre.cyl (qS q V))).comp
            (cylPreimageHomeo q V hV : C(Work.Serre.cyl (qS q V), ↥(fvpP q V))))
            = ContinuousMap.id (Work.Serre.cyl (qS q V)) from by
          ext x
          simp only [ContinuousMap.comp_apply, ContinuousMap.id_apply]
          exact Homeomorph.symm_apply_apply (cylPreimageHomeo q V hV) x)
        (fun x hx => by simpa using hx) (fun _ hx => hx) ℚ (r + 1)]
      exact Work.Thom.relCohMap_idA (fvpB (qS q V)) ℚ (r + 1)
  -- ## transported along the homeomorphism, the class is still non-zero
  have hΦuV_ne : (Work.Thom.relCohMap (cylPreimageHomeo q V hV
      : C(Work.Serre.cyl (qS q V), ↥(fvpP q V))) (fvpB (qS q V)) (fvpS q (fvpP q V))
      hf3 ℚ (r + 1)).hom uV ≠ 0 := by
    intro h0
    have hinj : Function.Injective ((Work.Thom.relCohMap (cylPreimageHomeo q V hV
        : C(Work.Serre.cyl (qS q V), ↥(fvpP q V))) (fvpB (qS q V)) (fvpS q (fvpP q V))
        hf3 ℚ (r + 1)).hom) :=
      (ModuleCat.mono_iff_injective _).mp inferInstance
    exact huV_ne (hinj (by rw [h0, map_zero]))
  -- ## and its restriction to the fibre over `b` is still non-zero
  have hw_ne : (Work.Thom.relCohMap (fvpIncl (fvpP (qS q V) ({⟨b, hb⟩} : Set ↥V)))
      (fvpS (qS q V) (fvpP (qS q V) ({⟨b, hb⟩} : Set ↥V))) (fvpB (qS q V))
      (fun _ hx => hx) ℚ (r + 1)).hom
      ((Work.Thom.relCohMap (cylPreimageHomeo q V hV
        : C(Work.Serre.cyl (qS q V), ↥(fvpP q V))) (fvpB (qS q V)) (fvpS q (fvpP q V))
        hf3 ℚ (r + 1)).hom uV) ≠ 0 := by
    intro h0
    have hinj : Function.Injective
        ((Work.Thom.relCohMap (fvpIncl (fvpP (qS q V) ({⟨b, hb⟩} : Set ↥V)))
          (fvpS (qS q V) (fvpP (qS q V) ({⟨b, hb⟩} : Set ↥V))) (fvpB (qS q V))
          (fun _ hx => hx) ℚ (r + 1)).hom) :=
      (ModuleCat.mono_iff_injective _).mp inferInstance
    exact hΦuV_ne (hinj (by rw [h0, map_zero]))
  -- ## the three composition identities
  have hcomp1 := Work.Thom.relCohMap_compA
    (fvpS (qS q V) (fvpP (qS q V) ({⟨b, hb⟩} : Set ↥V)))
    (fvpS q (fvpP q ({b} : Set B))) (fvpB q)
    eF (fvpIncl (fvpP q ({b} : Set B))) hf1 (fun _ hx => hx) hf1 ℚ (r + 1)
  have hcomp2 := Work.Thom.relCohMap_compA
    (fvpS (qS q V) (fvpP (qS q V) ({⟨b, hb⟩} : Set ↥V)))
    (fvpB (qS q V)) (fvpB q)
    (fvpIncl (fvpP (qS q V) ({⟨b, hb⟩} : Set ↥V)))
    ((fvpIncl (fvpP q V)).comp
      (cylPreimageHomeo q V hV : C(Work.Serre.cyl (qS q V), ↥(fvpP q V))))
    (fun _ hx => hx) hg2 hf1 ℚ (r + 1)
  have hconge := Work.Thom.relCohMap_congrA
    (f := (fvpIncl (fvpP q ({b} : Set B))).comp eF)
    (f' := ((fvpIncl (fvpP q V)).comp
      (cylPreimageHomeo q V hV : C(Work.Serre.cyl (qS q V), ↥(fvpP q V)))).comp
      (fvpIncl (fvpP (qS q V) ({⟨b, hb⟩} : Set ↥V))))
    (fvpS (qS q V) (fvpP (qS q V) ({⟨b, hb⟩} : Set ↥V))) (fvpB q) hsquare
    hf1 hf1 ℚ (r + 1)
  have hcomb := hcomp1.trans (hconge.trans hcomp2.symm)
  have hkey := congrArg (fun φ => (ModuleCat.Hom.hom φ) u) hcomb
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hkey
  -- ## the composite is the pullback along the homeomorphism
  have hcomp3 := Work.Thom.relCohMap_compA
    (fvpB (qS q V)) (fvpS q (fvpP q V)) (fvpB q)
    (cylPreimageHomeo q V hV : C(Work.Serre.cyl (qS q V), ↥(fvpP q V)))
    (fvpIncl (fvpP q V)) hf3 (fun _ hx => hx) hf3 ℚ (r + 1)
  have hkey3 := congrArg (fun φ => (ModuleCat.Hom.hom φ) u) hcomp3
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hkey3
  -- ## the proof arguments of `relCohMap` are irrelevant
  have hwit : (Work.Thom.relCohMap ((fvpIncl (fvpP q V)).comp
        (cylPreimageHomeo q V hV : C(Work.Serre.cyl (qS q V), ↥(fvpP q V))))
        (fvpB (qS q V)) (fvpB q) hg2 ℚ (r + 1))
      = (Work.Thom.relCohMap ((fvpIncl (fvpP q V)).comp
        (cylPreimageHomeo q V hV : C(Work.Serre.cyl (qS q V), ↥(fvpP q V))))
        (fvpB (qS q V)) (fvpB q) hf3 ℚ (r + 1)) :=
    Work.Thom.relCohMap_hcongrA _ _ _ hg2 hf3 ℚ (r + 1)
  have hkey3' : (Work.Thom.relCohMap ((fvpIncl (fvpP q V)).comp
        (cylPreimageHomeo q V hV : C(Work.Serre.cyl (qS q V), ↥(fvpP q V))))
        (fvpB (qS q V)) (fvpB q) hg2 ℚ (r + 1)).hom u
      = (Work.Thom.relCohMap (cylPreimageHomeo q V hV
          : C(Work.Serre.cyl (qS q V), ↥(fvpP q V))) (fvpB (qS q V)) (fvpS q (fvpP q V))
          hf3 ℚ (r + 1)).hom uV := by
    rw [hwit, ← hkey3, ← huVdef]
  -- ## the value of the restricted class on the fibre over `b`
  have hwk : (Work.Thom.relCohMap eF (fvpS (qS q V) (fvpP (qS q V) ({⟨b, hb⟩} : Set ↥V)))
        (fvpS q (fvpP q ({b} : Set B))) hf1 ℚ (r + 1)).hom
      ((Work.Thom.relCohMap (fvpIncl (fvpP q ({b} : Set B)))
        (fvpS q (fvpP q ({b} : Set B))) (fvpB q) (fun _ hx => hx) ℚ (r + 1)).hom u)
      = (Work.Thom.relCohMap (fvpIncl (fvpP (qS q V) ({⟨b, hb⟩} : Set ↥V)))
        (fvpS (qS q V) (fvpP (qS q V) ({⟨b, hb⟩} : Set ↥V))) (fvpB (qS q V))
        (fun _ hx => hx) ℚ (r + 1)).hom
        ((Work.Thom.relCohMap (cylPreimageHomeo q V hV
          : C(Work.Serre.cyl (qS q V), ↥(fvpP q V))) (fvpB (qS q V)) (fvpS q (fvpP q V))
          hf3 ℚ (r + 1)).hom uV) := by
    rw [hkey, hkey3']
  intro hub
  have hzero : (Work.Thom.relCohMap eF (fvpS (qS q V) (fvpP (qS q V) ({⟨b, hb⟩} : Set ↥V)))
        (fvpS q (fvpP q ({b} : Set B))) hf1 ℚ (r + 1)).hom
      ((Work.Thom.relCohMap (fvpIncl (fvpP q ({b} : Set B)))
        (fvpS q (fvpP q ({b} : Set B))) (fvpB q) (fun _ hx => hx) ℚ (r + 1)).hom u) = 0 := by
    rw [hub, map_zero]
  exact hw_ne (hwk ▸ hzero)

theorem fibreValuePropagation {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]
    (q : C(X, B)) (hq : Work.StemsB.IsSerreFibration q) {V : Set B} (hV : IsClosed V)
    (b : B) (hb : b ∈ V) (r N : ℕ) (hr : 1 ≤ r) (hrN : r + 1 ≤ N)
    (hVpc : PathConnectedSpace ↥V)
    (hVc : ∀ i : ℕ, Subsingleton (HomotopyGroup (Fin i) ↥V ⟨b, hb⟩))
    (hXpc : PathConnectedSpace X)
    (hpcV : PathConnectedSpace (Work.StemsB.fibre q b))
    (hvanV : ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q b)) t))
    (hgenV : Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q b)) r ≅ ModuleCat.of ℚ ℚ))
    (u : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q) (Set.range (Work.Serre.cylIncl q)))
    (hu : (Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥((Work.Serre.cylRetract q) ⁻¹' V), Work.Serre.cyl q))
        {x : ↥((Work.Serre.cylRetract q) ⁻¹' V) |
          (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}
        (Set.range (Work.Serre.cylIncl q)) (fun _ hx => hx) ℚ (r + 1)).hom u ≠ 0) :
    (Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥((Work.Serre.cylRetract q) ⁻¹' ({b} : Set B)), Work.Serre.cyl q))
      {x : ↥((Work.Serre.cylRetract q) ⁻¹' ({b} : Set B)) |
        (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}
      (Set.range (Work.Serre.cylIncl q)) (fun _ hx => hx) ℚ (r + 1)).hom u ≠ 0 :=
  fibreValuePropagation_aux q hq hV b hb r N hr hrN hVpc hVc hXpc hpcV hvanV hgenV u hu

end

end Work.Serre.DiscPair
