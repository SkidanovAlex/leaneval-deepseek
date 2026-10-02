import Mathlib
import Submission.Work.Thom.Glue
import Submission.Work.Thom.subsingleton_PieceCoh_of_lt_rank
import Submission.Work.Cohomology.relCohMV_honest_les
import Submission.Work.Cohomology.subsingleton_pdCohSub_union
import Submission.Work.Cohomology.pdCohSub_iUnion_of_wf
import Submission.Work.Thom.nonempty_thomClass_of_disjoint_cover
import Submission.Work.Thom.subsingleton_PieceCoh_genFibre
import Submission.Work.Thom.exists_glue_unique
import Submission.Work.Cohomology.rcKern_iUnion_limit
import Submission.Work.Cohomology.rcResLM_surjective
import Submission.Work.Cohomology.rcSet_homology_succ_subsingleton_iff
import Submission.Work.Thom.subsingleton_PieceCoh_of_lt_finrank
import Submission.Work.Thom.rcPrimitive_of_piece_primitives
import Submission.Work.Thom.localThomUnionAux
import Submission.Work.Cohomology.subsingleton_relCohomology_of_open_subset
import Submission.Work.Thom.pdCohMap_comp
import Submission.Work.Thom.rcPrimitive_of_piece_primitives_union_vanishing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-!
# A relative class of the Thom pair is zero as soon as it dies on every chart piece

`Work.Thom.openThom_eq_zero_of_baseSet_rank`: a class `τ ∈ Hⁿ(E, E∖0)` of the Thom pair of a real
bundle `Z → B` of rank `n ≥ 1` whose restriction to the piece over **every chart** `Z.baseSet i`
vanishes is zero.

The proof is the transfinite Mayer–Vietoris exhaustion of the total space by the *cumulative*
pieces `Q i = ⋃ β ≤ i, Z.baseSet β` of a well-order of the chart index type, with `n = k + 1`:

* `Work.Thom.pdCohRes_iUnion_eq_zero` — **the union step**: a class of the pair `(X, A)` whose
  restriction to each piece `V i` of an increasing well-ordered open cover vanishes, vanishes on
  the union `⋃ i, V i` (given the routine vanishing hypothesis on the unions of the lower pieces).
  This is the patching lemma `Work.Thom.rcPrimitive_of_piece_primitives_union_vanishing` applied
  to a cycle representing the restricted class, combined with the coboundary/class dictionary
  `rcSet_exists_cycle`, `rcResLM_exists_primitive_of_homologyMap_eq_zero` and
  `rcSet_homologyπ_eq_zero_of_exists_primitive`;
* the induction on `i ∈ ι` shows that `τ` dies on the piece over `Q i`: the piece over `Q i` is the
  union of the piece over `P i = ⋃ β < i, Z.baseSet β` (where `τ` dies by induction, through the
  union step over the subtype `{β // β < i}`) and the piece over the chart `Z.baseSet i` (where
  `τ` dies by hypothesis), and these glue by the two-piece Mayer–Vietoris injection
  `Work.Thom.pdCohSub_pdCohMap_biprod_injective` because the overlap lies in a chart, where
  `H^{n-1} = H^k` vanishes;
* finally `⋃ i, Q i = B`, so the union step over the whole index set gives that `τ` dies on the
  piece over `B`, i.e. on `(X, A)`; `Work.Thom.pdCohRes_univ_injective` (the restriction to
  `Set.univ` is an isomorphism) then concludes `τ = 0`.

The vanishing of `H^k` on every piece is `Work.Thom.subsingleton_PieceCoh_of_lt_finrank`
(`k < rank`).
-/

open Work.TangentClasses

namespace Work.Thom

open Work.Cohomology
open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-! ## The cycle/cocycle interface of the relative cochain complex -/

/-- The differential of the relative cochain complex, evaluated on a relative cochain. -/
theorem rcKern_d_coe (A : Set X) (U : Set X) (k : ℕ) (w : ↥(rcKern A U k)) :
    ((rcSet A U).d k (k+1) w : ↥(rcKern A U (k+1))) = rcDiff A U k w := by
  rw [rcSet_d]
  exact congrArg (fun (g : ↥(rcKern A U k) →ₗ[ℤ] ↥(rcKern A U (k+1))) => g w)
    (ModuleCat.hom_ofHom (rcDiff A U k))

/-- Every relative cohomology class is the class of a cycle. -/
theorem rcSet_exists_cycle (A : Set X) (U : Set X) (k : ℕ) :
    ∀ y : (rcSet A U).homology (k+1), ∃ z : (rcSet A U).cycles (k+1),
      (rcSet A U).homologyπ (k+1) z = y :=
  (ModuleCat.epi_iff_surjective ((rcSet A U).homologyπ (k+1))).mp inferInstance

/-- **A cycle whose class vanishes is a coboundary.** -/
theorem rcSet_exists_primitive_of_homologyπ_eq_zero (A : Set X) (U : Set X) (k : ℕ)
    (z : (rcSet A U).cycles (k+1)) (hz : (rcSet A U).homologyπ (k+1) z = 0) :
    ∃ w : ↥(rcKern A U k), rcDiff A U k w = ((rcSet A U).iCycles (k+1) z : ↥(rcKern A U (k+1))) := by
  have hprev : (ComplexShape.up ℕ).prev (k+1) = k :=
    ComplexShape.prev_eq' _ (ComplexShape.up_mk k (k+1) rfl)
  have hu : ((rcSet A U).sc (k+1)).homologyπ z = 0 := hz
  obtain ⟨w, hw⟩ := (pdHom_homologyπ_eq_zero_iff_sc (S := (rcSet A U).sc (k+1)) z).mp hu
  let w' : (rcSet A U).X ((ComplexShape.up ℕ).prev (k+1)) := w
  have hw' : (rcSet A U).d ((ComplexShape.up ℕ).prev (k+1)) (k+1) w' =
      (rcSet A U).iCycles (k+1) z := hw
  have h2 : (rcSet A U).d k (k+1) (((rcSet A U).XIsoOfEq hprev).hom w')
      = (rcSet A U).d ((ComplexShape.up ℕ).prev (k+1)) (k+1) w' := by
    have h := congrArg (fun (f : (rcSet A U).X ((ComplexShape.up ℕ).prev (k+1)) ⟶
      (rcSet A U).X (k+1)) => f w')
      (HomologicalComplex.XIsoOfEq_hom_comp_d (rcSet A U) hprev (k+1))
    rw [CategoryTheory.ConcreteCategory.comp_apply] at h
    exact h
  refine ⟨((rcSet A U).XIsoOfEq hprev).hom w', ?_⟩
  rw [← rcKern_d_coe A U k (((rcSet A U).XIsoOfEq hprev).hom w')]
  have h2r : ((rcSet A U).d k (k+1) (((rcSet A U).XIsoOfEq hprev).hom w') : ↥(rcKern A U (k+1)))
      = ((rcSet A U).d ((ComplexShape.up ℕ).prev (k+1)) (k+1) w' : ↥(rcKern A U (k+1))) := h2
  have hw'r : ((rcSet A U).d ((ComplexShape.up ℕ).prev (k+1)) (k+1) w' : ↥(rcKern A U (k+1)))
      = ((rcSet A U).iCycles (k+1) z : ↥(rcKern A U (k+1))) := hw'
  rw [h2r, hw'r]

/-- **A cycle with a primitive has vanishing class.** -/
theorem rcSet_homologyπ_eq_zero_of_exists_primitive (A : Set X) (U : Set X) (k : ℕ)
    (z : (rcSet A U).cycles (k+1))
    (h : ∃ w : ↥(rcKern A U k), rcDiff A U k w = ((rcSet A U).iCycles (k+1) z : ↥(rcKern A U (k+1)))) :
    (rcSet A U).homologyπ (k+1) z = 0 := by
  have hprev : (ComplexShape.up ℕ).prev (k+1) = k :=
    ComplexShape.prev_eq' _ (ComplexShape.up_mk k (k+1) rfl)
  obtain ⟨w, hw⟩ := h
  let w₀ : (rcSet A U).X k := w
  have hw0 : (rcSet A U).d k (k+1) w₀ = (rcSet A U).iCycles (k+1) z := by
    show ((rcSet A U).d k (k+1) w₀ : ↥(rcKern A U (k+1))) =
      ((rcSet A U).iCycles (k+1) z : ↥(rcKern A U (k+1)))
    rw [rcKern_d_coe]
    exact hw
  refine (pdHom_homologyπ_eq_zero_iff_sc (S := (rcSet A U).sc (k+1)) z).mpr ?_
  refine ⟨((rcSet A U).XIsoOfEq hprev).inv w₀, ?_⟩
  have h := congrArg (fun (f : (rcSet A U).X k ⟶ (rcSet A U).X (k+1)) => f w₀)
    (HomologicalComplex.XIsoOfEq_inv_comp_d (rcSet A U) hprev (k+1))
  rw [CategoryTheory.ConcreteCategory.comp_apply] at h
  show ((rcSet A U).d ((ComplexShape.up ℕ).prev (k+1)) (k+1))
      (((rcSet A U).XIsoOfEq hprev).inv w₀) = (rcSet A U).iCycles (k+1) z
  rw [h, hw0]

/-- **The restricted cycle of a class that dies on a piece is a coboundary on that piece.** -/
theorem rcResLM_exists_primitive_of_homologyMap_eq_zero (A : Set X) {U V : Set X}
    (h : V ⊆ U) (k : ℕ) (z : (rcSet A U).cycles (k+1))
    (hz : (HomologicalComplex.homologyMap (rcRes A h) (k+1)).hom
        ((rcSet A U).homologyπ (k+1) z) = 0) :
    ∃ w : ↥(rcKern A V k), rcDiff A V k w
      = rcResLM A h (k+1) ((rcSet A U).iCycles (k+1) z : ↥(rcKern A U (k+1))) := by
  have hnat : (HomologicalComplex.homologyMap (rcRes A h) (k+1)).hom ((rcSet A U).homologyπ (k+1) z)
      = (rcSet A V).homologyπ (k+1)
          ((HomologicalComplex.cyclesMap (rcRes A h) (k+1)) z) := by
    have h := congrArg (fun (g : (rcSet A U).cycles (k+1) ⟶ (rcSet A V).homology (k+1)) => g z)
      (HomologicalComplex.homologyπ_naturality (rcRes A h) (k+1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    exact h
  have hz' : (rcSet A V).homologyπ (k+1)
      ((HomologicalComplex.cyclesMap (rcRes A h) (k+1)) z) = 0 := by
    rw [← hnat]; exact hz
  obtain ⟨w, hw⟩ := rcSet_exists_primitive_of_homologyπ_eq_zero A V k
    ((HomologicalComplex.cyclesMap (rcRes A h) (k+1)) z) hz'
  refine ⟨w, ?_⟩
  rw [hw]
  have hci := congrArg (fun (g : (rcSet A U).cycles (k+1) ⟶ (rcSet A V).X (k+1)) => g z)
    (HomologicalComplex.cyclesMap_i (rcRes A h) (k+1))
  rw [rcRes_f] at hci
  exact hci

/-! ## Elements of the biproduct of two pieces are determined by their two projections -/

/-- Element extensionality for the biproduct of two relative cohomology modules. -/
theorem pdCohBiprod_ext {X : TopCat} {A U V : Set X} {n : ℕ} {x y : pdCohBiprod X A U V n}
    (h1 : (pdCohBiprodFst X A U V n).hom x = (pdCohBiprodFst X A U V n).hom y)
    (h2 : (pdCohBiprodSnd X A U V n).hom x = (pdCohBiprodSnd X A U V n).hom y) : x = y := by
  have htot : pdCohBiprodFst X A U V n ≫ pdCohBiprodInl X A U V n
      + pdCohBiprodSnd X A U V n ≫ pdCohBiprodInr X A U V n = 𝟙 (pdCohBiprod X A U V n) :=
    biprod.total
  have hx : (pdCohBiprodInl X A U V n) ((pdCohBiprodFst X A U V n).hom x)
      + (pdCohBiprodInr X A U V n) ((pdCohBiprodSnd X A U V n).hom x) = x := by
    have h := congrArg (fun (f : pdCohBiprod X A U V n ⟶ pdCohBiprod X A U V n) => f.hom x) htot
    simpa only [Preadditive.add_comp, ModuleCat.hom_add, LinearMap.add_apply,
      CategoryTheory.ConcreteCategory.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] using h
  have hy : (pdCohBiprodInl X A U V n) ((pdCohBiprodFst X A U V n).hom y)
      + (pdCohBiprodInr X A U V n) ((pdCohBiprodSnd X A U V n).hom y) = y := by
    have h := congrArg (fun (f : pdCohBiprod X A U V n ⟶ pdCohBiprod X A U V n) => f.hom y) htot
    simpa only [Preadditive.add_comp, ModuleCat.hom_add, LinearMap.add_apply,
      CategoryTheory.ConcreteCategory.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] using h
  rw [← hx, ← hy, h1, h2]

/-- An element of a biproduct of pieces is zero as soon as both projections vanish. -/
theorem pdCohBiprod_eq_zero {X : TopCat} {A U V : Set X} {n : ℕ} {x : pdCohBiprod X A U V n}
    (h1 : (pdCohBiprodFst X A U V n).hom x = 0)
    (h2 : (pdCohBiprodSnd X A U V n).hom x = 0) : x = 0 :=
  pdCohBiprod_ext (y := 0) (by simp only [h1, map_zero]) (by simp only [h2, map_zero])

/-! ## The two-piece injection on pieces -/

/-- **Two-piece Mayer–Vietoris injection.**  If `W = U ∪ V` is a union of two open pieces of an
ambient space and the relative cohomology of the overlap vanishes in degree `n - 1`, then a
relative class of the piece over `W` whose restrictions to `U` and to `V` vanish is zero. -/
theorem pdCohSub_pdCohMap_biprod_injective {X : TopCat} {A W U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hUW : U ⊆ W) (hVW : V ⊆ W) (hcov : U ∪ V = W) (n : ℕ)
    (hsub : Subsingleton (pdCohSub X A (U ∩ V) (n - 1))) :
    Function.Injective (fun x : pdCohSub X A W n =>
      ((pdCohMap X A W U hUW n).hom x, (pdCohMap X A W V hVW n).hom x)) := by
  intro x x' hxx
  have hUxx : (pdCohMap X A W U hUW n).hom x = (pdCohMap X A W U hUW n).hom x' := by
    have h := congrArg (fun p : pdCohSub X A U n × pdCohSub X A V n => p.1) hxx
    simpa using h
  have hVxx : (pdCohMap X A W V hVW n).hom x = (pdCohMap X A W V hVW n).hom x' := by
    have h := congrArg (fun p : pdCohSub X A U n × pdCohSub X A V n => p.2) hxx
    simpa using h
  have h1 : (pdCohMap X A W U hUW n).hom (x - x') = 0 := by
    rw [map_sub, hUxx, sub_self]
  have h2 : (pdCohMap X A W V hVW n).hom (x - x') = 0 := by
    rw [map_sub, hVxx, sub_self]
  set A' : Set ↥W := (Subtype.val : ↥W → X) ⁻¹' A with hA'
  set U' : Set ↥W := (Subtype.val : ↥W → X) ⁻¹' U with hU'def
  set V' : Set ↥W := (Subtype.val : ↥W → X) ⁻¹' V with hV'def
  have hWmem : (Subtype.val : ↥W → X) ⁻¹' W = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    exact y.2
  have hcov' : U' ∪ V' = Set.univ := by
    rw [hU'def, hV'def, ← Set.preimage_union, hcov, hWmem]
  have hU'o : IsOpen U' := hU.preimage continuous_subtype_val
  have hV'o : IsOpen V' := hV.preimage continuous_subtype_val
  have hsub' : Subsingleton (pdCohSub (TopCat.of ↥W) A' (U' ∩ V') (n - 1)) := by
    rw [hU'def, hV'def, ← Set.preimage_inter]
    exact Work.Cohomology.subsingleton_of_iso
      (luIso X A (Set.inter_subset_left.trans hUW) (n - 1)) hsub
  have hinj := honestF_injective_of_subsingleton_overlap (X := TopCat.of ↥W) (A := A')
    (U := U') (V := V') n hU'o hV'o hcov' hsub'
  have h3 : (pdCohRes (TopCat.of ↥W) ((Subtype.val : ↥W → X) ⁻¹' A)
      ((Subtype.val : ↥W → X) ⁻¹' U) n).hom (x - x') = 0 := by
    rw [(luIso_res X A hUW n).symm, ModuleCat.hom_comp, LinearMap.comp_apply, map_sub, map_sub]
    have hAB : ModuleCat.Hom.hom (luIso X A hUW n).hom ((pdCohMap X A W U hUW n).hom x)
        = ModuleCat.Hom.hom (luIso X A hUW n).hom ((pdCohMap X A W U hUW n).hom x') :=
      congrArg (fun (y : pdCohSub X A U n) => ModuleCat.Hom.hom (luIso X A hUW n).hom y) hUxx
    exact sub_eq_zero.mpr hAB
  have h4 : (pdCohRes (TopCat.of ↥W) ((Subtype.val : ↥W → X) ⁻¹' A)
      ((Subtype.val : ↥W → X) ⁻¹' V) n).hom (x - x') = 0 := by
    rw [(luIso_res X A hVW n).symm, ModuleCat.hom_comp, LinearMap.comp_apply, map_sub, map_sub]
    have hAB : ModuleCat.Hom.hom (luIso X A hVW n).hom ((pdCohMap X A W V hVW n).hom x)
        = ModuleCat.Hom.hom (luIso X A hVW n).hom ((pdCohMap X A W V hVW n).hom x') :=
      congrArg (fun (y : pdCohSub X A V n) => ModuleCat.Hom.hom (luIso X A hVW n).hom y) hVxx
    exact sub_eq_zero.mpr hAB
  have hF : (honestF (TopCat.of ↥W) A' U' V' n).hom (x - x') = 0 := by
    apply pdCohBiprod_eq_zero
    · rw [← ModuleCat.comp_apply, honestF_fst]
      exact h3
    · rw [← ModuleCat.comp_apply, honestF_snd]
      exact h4
  have h5 : x - x' = 0 := hinj (by rw [hF, map_zero])
  exact sub_eq_zero.mp h5

/-! ## The restriction of a class of the Thom pair to the whole space is injective -/

theorem pdCohRes_univ_injective {X : Type} [TopologicalSpace X] (A : Set X) (k : ℕ) :
    Function.Injective (pdCohRes (TopCat.of X) A Set.univ k).hom := by
  let e : ↥(Set.univ : Set X) ≃ₜ X :=
    { toFun := Subtype.val
      invFun := fun x => ⟨x, Set.mem_univ x⟩
      left_inv := fun y => Subtype.ext rfl
      right_inv := fun x => rfl
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk _ }
  have hbij := Work.Thom.bijective_relCohMap_of_homeomorphA
    ((Subtype.val : ↥(Set.univ : Set X) → X) ⁻¹' A) A e (fun y => Iff.rfl) ℤ k
  exact hbij.1

/-! ## The union step: a class that dies on the pieces dies on the union -/

theorem pdCohRes_iUnion_eq_zero {X : Type} [TopologicalSpace X] (A : Set X) {Γ : Type}
    [LinearOrder Γ] [WellFoundedLT Γ] (V : Γ → Set X) (hopen : ∀ i, IsOpen (V i))
    (hmono : Monotone V) {k : ℕ}
    (hvan : ∀ γ : Γ, (∃ δ, δ < γ) → Subsingleton ((rcSet A (⋃ δ < γ, V δ)).homology k))
    (x : pdCoh (TopCat.of X) A (k+1))
    (hx : ∀ i, (pdCohRes (TopCat.of X) A (V i) (k+1)).hom x = 0) :
    (pdCohRes (TopCat.of X) A (⋃ i, V i) (k+1)).hom x = 0 := by
  classical
  let U : Set X := ⋃ i, V i
  have hUi : ∀ i, V i ⊆ U := fun i => Set.subset_iUnion V i
  have hy : ∀ i, (pdCohMap (TopCat.of X) A U (V i) (hUi i) (k+1)).hom
      ((pdCohRes (TopCat.of X) A U (k+1)).hom x) = 0 := by
    intro i
    have hcomp := pdCohRes_comp (TopCat.of X) A U (V i) (hUi i) (k+1)
    have h := congrArg (fun (f : pdCoh (TopCat.of X) A (k+1) ⟶
        pdCohSub (TopCat.of X) A (V i) (k+1)) => f.hom x) hcomp
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rw [← h]
    exact hx i
  obtain ⟨z, hz⟩ := rcSet_exists_cycle A U k ((pdCohRes (TopCat.of X) A U (k+1)).hom x)
  have hzc : rcDiff A U (k+1) (((rcSet A U).iCycles (k+1) z) : ↥(rcKern A U (k+1))) = 0 :=
    relDiffLM_iCycles (TopCat.of U) {y : U | (y : X) ∈ A} (k+1) z
  have hprim : ∀ i, ∃ w : ↥(rcKern A (V i) k), rcDiff A (V i) k w
      = rcResLM A (hUi i) (k+1) (((rcSet A U).iCycles (k+1) z) : ↥(rcKern A U (k+1))) := by
    intro i
    refine rcResLM_exists_primitive_of_homologyMap_eq_zero A (hUi i) k z ?_
    rw [hz]
    exact hy i
  obtain ⟨w, hw⟩ := rcPrimitive_of_piece_primitives_union_vanishing A V hopen hmono k hvan
    (((rcSet A U).iCycles (k+1) z) : ↥(rcKern A U (k+1))) hzc hprim
  exact hz.symm.trans (rcSet_homologyπ_eq_zero_of_exists_primitive A U k z ⟨w, hw⟩)

theorem openThom_eq_zero_of_baseSet_rank {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type} [FiniteDimensional ℝ F]
    (Z : Work.TangentClasses.RealBundle B F ι) {n : ℕ} (hrank : Z.rank = n) (hn : 1 ≤ n)
    (τ : Work.Thom.OpenThom Z n)
    (hτ : ∀ i : ι, (Work.Thom.PieceRes Z (Z.baseSet i) n).hom τ = 0) : τ = 0 := by
  classical
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hk : k < Module.finrank ℝ F := by
    have hrank' : Module.finrank ℝ F = k + 1 := hrank
    omega
  obtain ⟨inst, hwf⟩ := exists_wellFoundedLT ι
  letI : LinearOrder ι := inst
  haveI : WellFoundedLT ι := hwf
  let A : Set Z.TotalSpace := zeroComplement Z
  let Q : ι → Set B := fun i => ⋃ β ≤ i, Z.baseSet β
  let P : ι → Set B := fun i => ⋃ β < i, Z.baseSet β
  let V : ι → Set Z.TotalSpace := fun i => Z.proj ⁻¹' Q i
  have hQP : ∀ i, Q i = P i ∪ Z.baseSet i := by
    intro i
    ext x
    simp only [Q, P, Set.mem_union, Set.mem_iUnion]
    constructor
    · rintro ⟨β, hβ, hx⟩
      rcases lt_or_eq_of_le hβ with h | h
      · exact Or.inl ⟨β, h, hx⟩
      · exact Or.inr (h ▸ hx)
    · rintro (⟨β, hβ, hx⟩ | hx)
      · exact ⟨β, le_of_lt hβ, hx⟩
      · exact ⟨i, le_rfl, hx⟩
  have hVopen : ∀ i, IsOpen (V i) := by
    intro i
    exact ((isOpen_iUnion fun β => isOpen_iUnion fun _ : β ≤ i => Z.isOpen_baseSet β).preimage
      Z.continuous_proj)
  have hVmono : Monotone V := by
    intro i j hij x hx
    simp only [V, Q, Set.mem_preimage, Set.mem_iUnion] at hx ⊢
    obtain ⟨β, hβ, hx⟩ := hx
    exact ⟨β, le_trans hβ hij, hx⟩
  have hPQ : ∀ i, (⋃ k : ↥(Set.Iio i), Q k.1) = P i := by
    intro i
    ext x
    simp only [P, Q, Set.mem_iUnion]
    constructor
    · rintro ⟨j, β, hβ, hx⟩
      exact ⟨β, lt_of_le_of_lt hβ j.2, hx⟩
    · rintro ⟨β, hβ, hx⟩
      exact ⟨⟨β, hβ⟩, β, le_rfl, hx⟩
  have hVP : ∀ i, (⋃ j : ↥(Set.Iio i), V j.1) = Z.proj ⁻¹' P i := by
    intro i
    simp only [V]
    rw [← Set.preimage_iUnion, hPQ i]
  have hvan_aux : ∀ (Γ : Type) [LinearOrder Γ] [WellFoundedLT Γ] (W : Γ → Set B) (γ : Γ),
      Subsingleton ((rcSet A (⋃ δ < γ, Z.proj ⁻¹' W δ)).homology k) := by
    intro Γ _ _ W γ
    have heq : Z.proj ⁻¹' (⋃ δ < γ, W δ) = ⋃ δ < γ, Z.proj ⁻¹' W δ := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_preimage]
    refine subsingleton_pdCohSub_of_eq A heq ?_
    exact subsingleton_PieceCoh_of_lt_finrank Z (⋃ δ < γ, W δ) hk
  have key : ∀ i : ι, (pdCohRes (TopCat.of Z.TotalSpace) A (V i) (k+1)).hom τ = 0 := by
    intro i
    refine WellFoundedLT.induction (motive := fun i : ι =>
      (pdCohRes (TopCat.of Z.TotalSpace) A (V i) (k+1)).hom τ = 0) i ?_
    intro i ih
    have hchart : (pdCohRes (TopCat.of Z.TotalSpace) A (Z.proj ⁻¹' Z.baseSet i) (k+1)).hom τ = 0 :=
      hτ i
    have hsmall : (pdCohRes (TopCat.of Z.TotalSpace) A (Z.proj ⁻¹' P i) (k+1)).hom τ = 0 := by
      rw [← hVP i]
      exact pdCohRes_iUnion_eq_zero A (fun j : ↥(Set.Iio i) => V j.1)
        (fun j => hVopen j.1) (fun a b hab => hVmono hab)
        (fun γ _ => hvan_aux (↥(Set.Iio i)) (fun j => Q j.1) γ) τ (fun j => ih j.1 j.2)
    have hsub : Subsingleton (pdCohSub (TopCat.of Z.TotalSpace) A
        ((Z.proj ⁻¹' P i) ∩ (Z.proj ⁻¹' Z.baseSet i)) ((k+1) - 1)) := by
      have heq : (Z.proj ⁻¹' P i) ∩ (Z.proj ⁻¹' Z.baseSet i)
          = Z.proj ⁻¹' (P i ∩ Z.baseSet i) := by rw [← Set.preimage_inter]
      rw [heq]
      exact subsingleton_PieceCoh_of_lt_finrank Z (P i ∩ Z.baseSet i) (by omega)
    have hUopen : IsOpen (Z.proj ⁻¹' P i) :=
      ((isOpen_iUnion fun β => isOpen_iUnion fun _ : β < i =>
        Z.isOpen_baseSet β).preimage Z.continuous_proj)
    have hWopen : IsOpen (Z.proj ⁻¹' Z.baseSet i) := (Z.isOpen_baseSet i).preimage Z.continuous_proj
    have hUsub : Z.proj ⁻¹' P i ⊆ V i := by
      intro x hx
      simp only [V, Q, P, Set.mem_preimage, Set.mem_iUnion] at hx ⊢
      obtain ⟨β, hβ, hx⟩ := hx
      exact ⟨β, le_of_lt hβ, hx⟩
    have hWsub : Z.proj ⁻¹' Z.baseSet i ⊆ V i := by
      intro x hx
      simp only [V, Q, Set.mem_preimage, Set.mem_iUnion]
      exact ⟨i, le_rfl, hx⟩
    have hcov : (Z.proj ⁻¹' P i) ∪ (Z.proj ⁻¹' Z.baseSet i) = V i := by
      show (Z.proj ⁻¹' P i) ∪ (Z.proj ⁻¹' Z.baseSet i) = Z.proj ⁻¹' Q i
      rw [hQP i, Set.preimage_union]
    have hinj := pdCohSub_pdCohMap_biprod_injective (X := TopCat.of Z.TotalSpace) (A := A)
      (W := V i) (U := Z.proj ⁻¹' P i) (V := Z.proj ⁻¹' Z.baseSet i)
      hUopen hWopen hUsub hWsub hcov (k+1) hsub
    have hpair1 : (pdCohMap (TopCat.of Z.TotalSpace) A (V i) (Z.proj ⁻¹' P i) hUsub (k+1)).hom
        ((pdCohRes (TopCat.of Z.TotalSpace) A (V i) (k+1)).hom τ) = 0 := by
      have hc := congrArg (fun (f : pdCoh (TopCat.of Z.TotalSpace) A (k+1) ⟶
          pdCohSub (TopCat.of Z.TotalSpace) A (Z.proj ⁻¹' P i) (k+1)) => f.hom τ)
        (pdCohRes_comp (TopCat.of Z.TotalSpace) A (V i) (Z.proj ⁻¹' P i) hUsub (k+1))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hc
      rw [← hc]
      exact hsmall
    have hpair2 : (pdCohMap (TopCat.of Z.TotalSpace) A (V i) (Z.proj ⁻¹' Z.baseSet i)
        hWsub (k+1)).hom ((pdCohRes (TopCat.of Z.TotalSpace) A (V i) (k+1)).hom τ) = 0 := by
      have hc := congrArg (fun (f : pdCoh (TopCat.of Z.TotalSpace) A (k+1) ⟶
          pdCohSub (TopCat.of Z.TotalSpace) A (Z.proj ⁻¹' Z.baseSet i) (k+1)) => f.hom τ)
        (pdCohRes_comp (TopCat.of Z.TotalSpace) A (V i) (Z.proj ⁻¹' Z.baseSet i) hWsub (k+1))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hc
      rw [← hc]
      exact hchart
    have hpair : ((pdCohMap (TopCat.of Z.TotalSpace) A (V i) (Z.proj ⁻¹' P i) hUsub (k+1)).hom
          ((pdCohRes (TopCat.of Z.TotalSpace) A (V i) (k+1)).hom τ),
        (pdCohMap (TopCat.of Z.TotalSpace) A (V i) (Z.proj ⁻¹' Z.baseSet i) hWsub (k+1)).hom
          ((pdCohRes (TopCat.of Z.TotalSpace) A (V i) (k+1)).hom τ)) = (0, 0) := by
      rw [hpair1, hpair2]
    have h0 : ((pdCohMap (TopCat.of Z.TotalSpace) A (V i) (Z.proj ⁻¹' P i) hUsub (k+1)).hom
          (0 : pdCohSub (TopCat.of Z.TotalSpace) A (V i) (k+1)),
        (pdCohMap (TopCat.of Z.TotalSpace) A (V i) (Z.proj ⁻¹' Z.baseSet i) hWsub (k+1)).hom
          (0 : pdCohSub (TopCat.of Z.TotalSpace) A (V i) (k+1))) = (0, 0) := by
      rw [map_zero, map_zero]
    exact hinj (hpair.trans h0.symm)
  have hfinal : (pdCohRes (TopCat.of Z.TotalSpace) A (⋃ i, V i) (k+1)).hom τ = 0 :=
    pdCohRes_iUnion_eq_zero A V hVopen hVmono (fun γ _ => hvan_aux ι Q γ) τ key
  have hunion : (⋃ i : ι, V i) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    refine Set.mem_iUnion.mpr ⟨Z.indexAt (Z.proj x), ?_⟩
    simp only [V, Q, Set.mem_preimage, Set.mem_iUnion]
    exact ⟨Z.indexAt (Z.proj x), le_rfl, Z.mem_baseSet_at (Z.proj x)⟩
  rw [hunion] at hfinal
  exact pdCohRes_univ_injective A (k+1) (hfinal.trans (map_zero _).symm)

end

end Work.Thom
