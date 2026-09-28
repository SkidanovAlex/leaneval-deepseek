import Mathlib
import Submission.Work.Thom.cupCmpRestrictTop
import Submission.Work.Thom.cupSESChain
import Submission.Work.Cohomology.relCupH
import Submission.Work.Cohomology.pd_us_cycles_eq_of_class_eq
import Submission.Work.Thom.MixedCup

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits Work.Cohomology
open scoped Simplicial

namespace Work.Thom

noncomputable section

variable {K L M : CochainComplex (ModuleCat ℤ) ℕ}

/-- The small-model absolute complex of the cover `(U,V)`. -/
abbrev tcycAbsDual (X : TopCat) (U V : Set X) : CochainComplex (ModuleCat ℤ) ℕ :=
  Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVTopC X ∅ U V)

/-- The small-model relative complex of the pair `(X,A)` for the cover `(U,V)`. -/
abbrev tcycRelDual (X : TopCat) (A U V : Set X) : CochainComplex (ModuleCat ℤ) ℕ :=
  Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVTopC X A U V)

/-- **The class of a cycle under a morphism of complexes.** -/
lemma tcycHomologyMapCocycleOfK (φ : K ⟶ L) (i : ℕ) (x : K.X i)
    (hx : ModuleCat.Hom.hom (K.d i (i+1)) x = 0)
    (hx' : ModuleCat.Hom.hom (L.d i (i+1)) (ModuleCat.Hom.hom (φ.f i) x) = 0) :
    ModuleCat.Hom.hom (HomologicalComplex.homologyMap φ i)
        ((K.homologyπ i) (Work.Cohomology.cocycleOfK K x hx))
      = (L.homologyπ i) (Work.Cohomology.cocycleOfK L (ModuleCat.Hom.hom (φ.f i) x) hx') := by
  have h1 : (K.homologyπ i ≫ HomologicalComplex.homologyMap φ i)
      = (HomologicalComplex.cyclesMap φ i ≫ L.homologyπ i) :=
    HomologicalComplex.homologyπ_naturality φ i
  have h2 := congrArg (fun (g : K.cycles i ⟶ L.homology i) =>
    ModuleCat.Hom.hom g (Work.Cohomology.cocycleOfK K x hx)) h1
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  rw [h2]
  congr 1
  have hkey : (ModuleCat.Hom.hom (L.iCycles i))
        ((ModuleCat.Hom.hom (HomologicalComplex.cyclesMap φ i))
          (Work.Cohomology.cocycleOfK K x hx))
      = (ModuleCat.Hom.hom (L.iCycles i))
          (Work.Cohomology.cocycleOfK L (ModuleCat.Hom.hom (φ.f i) x) hx') := by
    have hii := congrArg (fun (g : K.cycles i ⟶ L.X i) => ModuleCat.Hom.hom g
      (Work.Cohomology.cocycleOfK K x hx)) (HomologicalComplex.cyclesMap_i φ i)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hii
    rw [hii, Work.Cohomology.iCycles_cocycleOfK]
    exact (Work.Cohomology.iCycles_cocycleOfK L (ModuleCat.Hom.hom (φ.f i) x) hx').symm
  exact (ModuleCat.mono_iff_injective (L.iCycles i)).mp inferInstance hkey

/-- `Ttop` on the classes of honest relative cocycles is the honest mixed cup. -/
theorem tcycTtopRelClassOf (X : TopCat) (A U V : Set X) (n j : ℕ)
    (t : ↥((Work.Cohomology.relComplex ℤ X A).X n))
    (ht : Work.Cohomology.relDiffLM ℤ X A n t = 0)
    (α : ↥((Work.Cohomology.relComplex ℤ X ∅).X j))
    (hα : Work.Cohomology.relDiffLM ℤ X ∅ j α = 0) :
    TsqH.Ttop X A n (Work.Cohomology.relClassOf ℤ X A t ht) j
        (Work.Cohomology.relClassOf ℤ X ∅ α hα)
      = Work.Cohomology.relClassOf ℤ X A
          ⟨Work.Cohomology.cup ℤ (TopCat.toSSet.obj X) α.1 t.1,
            Work.Cohomology.cup_mem_relKern_right ℤ X A α.1 t.2⟩
          ((Work.Cohomology.mixedCup_apply (TopCat.of X) A j n α.1 t
            (Work.Cohomology.relClassOf_cochainDiff ℤ (TopCat.of X) ∅ α hα) ht).choose_spec.choose) := by
  show (LinearMap.applyₗ (Work.Cohomology.relClassOf ℤ X A t ht))
      (Work.Thom.mixedCupC ℤ A j n ((Work.Thom.pdCohIso X j).hom
        (Work.Cohomology.relClassOf ℤ X ∅ α hα)))
    = Work.Cohomology.relClassOf ℤ X A
        ⟨Work.Cohomology.cup ℤ (TopCat.toSSet.obj X) α.1 t.1,
          Work.Cohomology.cup_mem_relKern_right ℤ X A α.1 t.2⟩
        ((Work.Cohomology.mixedCup_apply (TopCat.of X) A j n α.1 t
          (Work.Cohomology.relClassOf_cochainDiff ℤ (TopCat.of X) ∅ α hα) ht).choose_spec.choose)
  rw [show (Work.Thom.pdCohIso X j).hom (Work.Cohomology.relClassOf ℤ X ∅ α hα)
      = Work.Cohomology.cohomologyClassOf ℤ (TopCat.toSSet.obj X) α.1
          (Work.Cohomology.relClassOf_cochainDiff ℤ (TopCat.of X) ∅ α hα) from
    Work.Thom.relToAbs_relClassOf (X := ↑X) (∅ : Set ↑X) α hα]
  rw [Work.Thom.mixedCupC_eq_mixedCup]
  exact (Work.Cohomology.mixedCup_apply (TopCat.of X) A j n α.1 t
    (Work.Cohomology.relClassOf_cochainDiff ℤ (TopCat.of X) ∅ α hα) ht).choose_spec.choose_spec

/-- `iCycles` of a difference of cycles. -/
lemma tcycICyclesSub (K : CochainComplex (ModuleCat ℤ) ℕ) (j : ℕ) (z z' : K.cycles j) :
    ModuleCat.Hom.hom (K.iCycles j) (z - z')
      = ModuleCat.Hom.hom (K.iCycles j) z - ModuleCat.Hom.hom (K.iCycles j) z' :=
  map_sub (ModuleCat.Hom.hom (K.iCycles j)) z z'

/-- `cupTop` of a difference of cochains. -/
lemma tcycCupTopSub (X : TopCat) (A U V : Set X) (n j : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n) (ht : t ∈ relKern ℤ X A n)
    (z z' : (tcycAbsDual X U V).X j) :
    ModuleCat.Hom.hom (Work.Thom.cupTop X A U V n j t ht) (z - z')
      = ModuleCat.Hom.hom (Work.Thom.cupTop X A U V n j t ht) z
        - ModuleCat.Hom.hom (Work.Thom.cupTop X A U V n j t ht) z' :=
  map_sub (ModuleCat.Hom.hom (Work.Thom.cupTop X A U V n j t ht)) z z'

/-- **A cycle with vanishing class is a boundary** (general form, in terms of `prev`). -/
lemma tcycExistsToCycles (K : CochainComplex (ModuleCat ℤ) ℕ) (j : ℕ)
    [K.HasHomology j] (z : K.cycles j) (h : ModuleCat.Hom.hom (K.homologyπ j) z = 0) :
    ∃ y : K.X ((ComplexShape.up ℕ).prev j),
      ModuleCat.Hom.hom (K.toCycles ((ComplexShape.up ℕ).prev j) j) y = z := by
  obtain ⟨a, ha⟩ := ModuleCat.exists_eq_sub_of_cokernel_π_eq
    (K.toCycles ((ComplexShape.up ℕ).prev j) j) (K.homologyπ j)
    (K.toCycles_comp_homologyπ ((ComplexShape.up ℕ).prev j) j)
    (K.homologyIsCokernel (i := (ComplexShape.up ℕ).prev j) (j := j) rfl)
    z 0 (by rw [h, map_zero])
  exact ⟨a, by simpa using ha⟩

/-- A cycle of a cochain complex with vanishing class has its `iCycles` image a boundary. -/
lemma tcycICyclesEqD (K : CochainComplex (ModuleCat ℤ) ℕ) (j : ℕ)
    [K.HasHomology j] (z : K.cycles j) (h : ModuleCat.Hom.hom (K.homologyπ j) z = 0) :
    ∃ y : K.X ((ComplexShape.up ℕ).prev j),
      ModuleCat.Hom.hom (K.iCycles j) z
        = ModuleCat.Hom.hom (K.d ((ComplexShape.up ℕ).prev j) j) y := by
  obtain ⟨y, hy⟩ := tcycExistsToCycles K j z h
  refine ⟨y, ?_⟩
  have h2 := congrArg (fun (g : K.X ((ComplexShape.up ℕ).prev j) ⟶ K.X j) =>
    ModuleCat.Hom.hom g y) (K.toCycles_i ((ComplexShape.up ℕ).prev j) j)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  rw [← h2, hy]

/-- A cycle of a cochain complex in positive degree with vanishing class is a boundary. -/
lemma tcycICyclesEqDSucc (K : CochainComplex (ModuleCat ℤ) ℕ) (k : ℕ) [K.HasHomology (k+1)]
    (z : K.cycles (k+1)) (h : ModuleCat.Hom.hom (K.homologyπ (k+1)) z = 0) :
    ∃ y : K.X k, ModuleCat.Hom.hom (K.iCycles (k+1)) z
      = ModuleCat.Hom.hom (K.d k (k+1)) y := by
  have hprev : (ComplexShape.up ℕ).prev (k+1) = k :=
    ComplexShape.prev_eq' (c := ComplexShape.up ℕ) (ComplexShape.up_mk k (k+1) rfl)
  obtain ⟨y, hy⟩ := ModuleCat.exists_eq_sub_of_cokernel_π_eq (K.toCycles k (k+1))
    (K.homologyπ (k+1)) (K.toCycles_comp_homologyπ k (k+1))
    (K.homologyIsCokernel (i := k) (j := k+1) hprev) z 0 (by rw [h, map_zero])
  refine ⟨y, ?_⟩
  have h2 := congrArg (fun (g : K.X k ⟶ K.X (k+1)) => ModuleCat.Hom.hom g y)
    (K.toCycles_i k (k+1))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  rw [← h2, hy]
  simp

/-- **Cup with a relative class respects homology classes on the small model.** -/
lemma tcycCupTopHomology (X : TopCat) (A U V : Set X) (n j : ℕ)
    (t : ↥((Work.Cohomology.relComplex ℤ X A).X n))
    (ht : Work.Cohomology.relDiffLM ℤ X A n t = 0)
    (w w' : (tcycAbsDual X U V).X j)
    (hw : (tcycAbsDual X U V).d j (j + 1) w = 0)
    (hw' : (tcycAbsDual X U V).d j (j + 1) w' = 0)
    (hcl : (tcycAbsDual X U V).homologyπ j
        (Work.Cohomology.cocycleOfK (tcycAbsDual X U V) w' hw')
        = (tcycAbsDual X U V).homologyπ j
          (Work.Cohomology.cocycleOfK (tcycAbsDual X U V) w hw))
    (hcw : (tcycRelDual X A U V).d (j + n) (j + n + 1)
        (Work.Thom.cupTop X A U V n j t.1 t.2 w) = 0)
    (hcw' : (tcycRelDual X A U V).d (j + n) (j + n + 1)
        (Work.Thom.cupTop X A U V n j t.1 t.2 w') = 0) :
    (tcycRelDual X A U V).homologyπ (j + n)
        (Work.Cohomology.cocycleOfK (tcycRelDual X A U V)
          (Work.Thom.cupTop X A U V n j t.1 t.2 w') hcw')
      = (tcycRelDual X A U V).homologyπ (j + n)
        (Work.Cohomology.cocycleOfK (tcycRelDual X A U V)
          (Work.Thom.cupTop X A U V n j t.1 t.2 w) hcw) := by
  have hdt : Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj X) t.1 = 0 :=
    Work.Cohomology.relClassOf_cochainDiff ℤ X A t ht
  rcases j with _ | k
  · -- j = 0
    obtain ⟨a, ha⟩ := ModuleCat.exists_eq_sub_of_cokernel_π_eq
      ((tcycAbsDual X U V).toCycles ((ComplexShape.up ℕ).prev 0) 0) ((tcycAbsDual X U V).homologyπ 0)
      ((tcycAbsDual X U V).toCycles_comp_homologyπ ((ComplexShape.up ℕ).prev 0) 0)
      ((tcycAbsDual X U V).homologyIsCokernel (i := (ComplexShape.up ℕ).prev 0) (j := 0) rfl)
      (Work.Cohomology.cocycleOfK (tcycAbsDual X U V) w' hw')
      (Work.Cohomology.cocycleOfK (tcycAbsDual X U V) w hw) hcl
    have hww : w' = w := by
      have h4 : ModuleCat.Hom.hom ((tcycAbsDual X U V).iCycles 0)
            (Work.Cohomology.cocycleOfK (tcycAbsDual X U V) w' hw'
              - Work.Cohomology.cocycleOfK (tcycAbsDual X U V) w hw) = 0 := by
        have h := congrArg (fun (g : (tcycAbsDual X U V).X ((ComplexShape.up ℕ).prev 0) ⟶
            (tcycAbsDual X U V).X 0) => ModuleCat.Hom.hom g a)
            ((tcycAbsDual X U V).toCycles_i ((ComplexShape.up ℕ).prev 0) 0)
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
        rw [ha] at h
        rw [(tcycAbsDual X U V).shape _ _ (by rw [ComplexShape.up_Rel]; omega)] at h
        simpa using h
      rw [map_sub, Work.Cohomology.iCycles_cocycleOfK,
        Work.Cohomology.iCycles_cocycleOfK] at h4
      exact sub_eq_zero.mp h4
    subst w'
    exact congrArg ((tcycRelDual X A U V).homologyπ (0 + n))
      (Work.Cohomology.cocycleOfK_proof_irrel _ _ hcw' hcw)
  · -- j = k + 1
    obtain ⟨y, hy⟩ := Work.Cohomology.pd_us_cycles_eq_of_class_eq (K := tcycAbsDual X U V) (n := k)
      (Work.Cohomology.cocycleOfK (tcycAbsDual X U V) w' hw')
      (Work.Cohomology.cocycleOfK (tcycAbsDual X U V) w hw) hcl
    have hww : w' - w = ModuleCat.Hom.hom ((tcycAbsDual X U V).d k (k + 1)) y := by
      rw [hy, Work.Cohomology.iCycles_cocycleOfK, Work.Cohomology.iCycles_cocycleOfK]
    have hcup : ModuleCat.Hom.hom ((tcycRelDual X A U V).d (k + n) ((k + 1) + n))
          (ModuleCat.Hom.hom (Work.Thom.cupTop X A U V n k t.1 t.2) y)
        = ModuleCat.Hom.hom (Work.Thom.cupTop X A U V n (k + 1) t.1 t.2) (w' - w) := by
      have h := congrArg (fun (g : (tcycAbsDual X U V).X k ⟶ (tcycRelDual X A U V).X ((k + 1) + n)) =>
        ModuleCat.Hom.hom g y) (Work.Thom.cupTop_d_comm X A U V n t.1 t.2 hdt k)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
      rw [h, hww]
    have hcyc : ModuleCat.Hom.hom ((tcycRelDual X A U V).iCycles ((k + 1) + n))
          (Work.Cohomology.cocycleOfK (tcycRelDual X A U V)
              (Work.Thom.cupTop X A U V n (k + 1) t.1 t.2 w') hcw'
            - Work.Cohomology.cocycleOfK (tcycRelDual X A U V)
              (Work.Thom.cupTop X A U V n (k + 1) t.1 t.2 w) hcw)
        = ModuleCat.Hom.hom ((tcycRelDual X A U V).d (k + n) ((k + 1) + n))
            (ModuleCat.Hom.hom (Work.Thom.cupTop X A U V n k t.1 t.2) y) := by
      rw [tcycICyclesSub, Work.Cohomology.iCycles_cocycleOfK,
        Work.Cohomology.iCycles_cocycleOfK, ← tcycCupTopSub]
      exact hcup.symm
    have hz : ModuleCat.Hom.hom ((tcycRelDual X A U V).homologyπ ((k + 1) + n))
          (Work.Cohomology.cocycleOfK (tcycRelDual X A U V)
              (Work.Thom.cupTop X A U V n (k + 1) t.1 t.2 w') hcw'
            - Work.Cohomology.cocycleOfK (tcycRelDual X A U V)
              (Work.Thom.cupTop X A U V n (k + 1) t.1 t.2 w) hcw) = 0 :=
      Work.Cohomology.homologyπ_eq_zero_of_d_K (tcycRelDual X A U V) ((k + 1) + n) (k + n) _ _ hcyc
    calc (tcycRelDual X A U V).homologyπ ((k + 1) + n)
          (Work.Cohomology.cocycleOfK (tcycRelDual X A U V)
            (Work.Thom.cupTop X A U V n (k + 1) t.1 t.2 w') hcw')
        = (tcycRelDual X A U V).homologyπ ((k + 1) + n)
            ((Work.Cohomology.cocycleOfK (tcycRelDual X A U V)
                (Work.Thom.cupTop X A U V n (k + 1) t.1 t.2 w') hcw'
              - Work.Cohomology.cocycleOfK (tcycRelDual X A U V)
                (Work.Thom.cupTop X A U V n (k + 1) t.1 t.2 w) hcw)
            + Work.Cohomology.cocycleOfK (tcycRelDual X A U V)
                (Work.Thom.cupTop X A U V n (k + 1) t.1 t.2 w) hcw) := by
              rw [sub_add_cancel]
      _ = (tcycRelDual X A U V).homologyπ ((k + 1) + n)
            (Work.Cohomology.cocycleOfK (tcycRelDual X A U V)
              (Work.Thom.cupTop X A U V n (k + 1) t.1 t.2 w) hcw) := by
              rw [map_add, hz, zero_add]

/-- `cocycleOfK` only depends on the cochain. -/
lemma tcycCocycleOfKCongr (K : CochainComplex (ModuleCat ℤ) ℕ) {n : ℕ} (α β : K.X n)
    (h : α = β) (hα : ModuleCat.Hom.hom (K.d n (n+1)) α = 0)
    (hβ : ModuleCat.Hom.hom (K.d n (n+1)) β = 0) :
    Work.Cohomology.cocycleOfK K α hα = Work.Cohomology.cocycleOfK K β hβ := by
  cases h
  exact Work.Cohomology.cocycleOfK_proof_irrel K α _ _

theorem Ttop_cyclesMk (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n j : ℕ)
    (t : ↥((Work.Cohomology.relComplex ℤ X A).X n))
    (ht : Work.Cohomology.relDiffLM ℤ X A n t = 0)
    (w : (Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVTopC X ∅ U V)).X j)
    (hw : (Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVTopC X ∅ U V)).d j (j + 1) w = 0)
    (hcw : (Work.Cohomology.dualComplex ℤ
      (Work.Cohomology.relMVTopC X A U V)).d (j + n) (j + n + 1)
        (Work.Thom.cupTop X A U V n j t.1 t.2 w) = 0) :
    Work.Thom.TsqH.Ttop X A n (Work.Cohomology.relClassOf ℤ X A t ht) j
        ((Work.Cohomology.cmpXIso X ∅ U V hU hV hcov j).inv
          ((Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVTopC X ∅ U V)).homologyπ j
            (Work.Cohomology.cocycleOfK _ w hw)))
      = (Work.Cohomology.cmpXIso X A U V hU hV hcov (j + n)).inv
          ((Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVTopC X A U V)).homologyπ (j + n)
            (Work.Cohomology.cocycleOfK _
              (Work.Thom.cupTop X A U V n j t.1 t.2 w) hcw)) := by
  set x := (Work.Cohomology.cmpXIso X ∅ U V hU hV hcov j).inv
      ((Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVTopC X ∅ U V)).homologyπ j
        (Work.Cohomology.cocycleOfK (Work.Cohomology.dualComplex ℤ
          (Work.Cohomology.relMVTopC X ∅ U V)) w hw)) with hx
  obtain ⟨α, hα, hαx⟩ := Work.Cohomology.exists_relClassOf ℤ X ∅ j x
  have hdt : Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj X) t.1 = 0 :=
    Work.Cohomology.relClassOf_cochainDiff ℤ X A t ht
  have hαc : ModuleCat.Hom.hom ((Work.Cohomology.relComplex ℤ X ∅).d j (j + 1)) α = 0 := by
    rw [Work.Cohomology.relComplex_d_apply]; exact hα
  have hw' : (tcycAbsDual X U V).d j (j + 1) ((Work.Cohomology.cmpX X ∅ U V).f j α) = 0 := by
    have hcomm := congrArg (fun (g : (Work.Cohomology.relComplex ℤ X ∅).X j ⟶
        (tcycAbsDual X U V).X (j + 1)) => ModuleCat.Hom.hom g α)
      (HomologicalComplex.Hom.comm (Work.Cohomology.cmpX X ∅ U V) j (j + 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hcomm
    rw [hαc] at hcomm
    rw [map_zero] at hcomm
    exact hcomm
  have hmid : (tcycRelDual X A U V).d (j + n) (j + n + 1)
      (Work.Thom.cupTop X A U V n j t.1 t.2 ((Work.Cohomology.cmpX X ∅ U V).f j α)) = 0 := by
    have h := congrArg (fun (g : (tcycAbsDual X U V).X j ⟶ (tcycRelDual X A U V).X ((j + 1) + n)) =>
      ModuleCat.Hom.hom g ((Work.Cohomology.cmpX X ∅ U V).f j α))
      (Work.Thom.cupTop_d_comm X A U V n t.1 t.2 hdt j)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rw [hw'] at h
    rw [map_zero] at h
    rw [Nat.add_right_comm j 1 n] at h
    exact h
  have hhomx : ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (Work.Cohomology.cmpX X ∅ U V) j) x
      = (tcycAbsDual X U V).homologyπ j
        (Work.Cohomology.cocycleOfK (tcycAbsDual X U V) w hw) := by
    rw [← Work.Cohomology.cmpXIso_hom X ∅ U V hU hV hcov j]
    rw [hx]
    exact Iso.inv_hom_id_apply _ _
  have hclass : ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (Work.Cohomology.cmpX X ∅ U V) j)
        (Work.Cohomology.relClassOf ℤ X ∅ α hα)
      = (tcycAbsDual X U V).homologyπ j
        (Work.Cohomology.cocycleOfK (tcycAbsDual X U V)
          ((Work.Cohomology.cmpX X ∅ U V).f j α) hw') := by
    rw [Work.Cohomology.relClassOf_eq_homologyπ_cocycleOfK ℤ X ∅ α hα hαc]
    exact tcycHomologyMapCocycleOfK (Work.Cohomology.cmpX X ∅ U V) j α hαc hw'
  have hcl : (tcycAbsDual X U V).homologyπ j
        (Work.Cohomology.cocycleOfK (tcycAbsDual X U V)
          ((Work.Cohomology.cmpX X ∅ U V).f j α) hw')
      = (tcycAbsDual X U V).homologyπ j
        (Work.Cohomology.cocycleOfK (tcycAbsDual X U V) w hw) := by
    rw [← hαx] at hhomx
    rw [hclass] at hhomx
    exact hhomx
  have hcomp : (tcycRelDual X A U V).homologyπ (j + n)
        (Work.Cohomology.cocycleOfK (tcycRelDual X A U V)
          (Work.Thom.cupTop X A U V n j t.1 t.2 ((Work.Cohomology.cmpX X ∅ U V).f j α)) hmid)
      = (tcycRelDual X A U V).homologyπ (j + n)
        (Work.Cohomology.cocycleOfK (tcycRelDual X A U V)
          (Work.Thom.cupTop X A U V n j t.1 t.2 w) hcw) :=
    tcycCupTopHomology X A U V n j t ht w _ hw hw' hcl hcw hmid
  have step1 : ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (Work.Cohomology.cmpX X A U V) (j + n))
        (Work.Thom.TsqH.Ttop X A n (Work.Cohomology.relClassOf ℤ X A t ht) j x)
      = ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (Work.Cohomology.cmpX X A U V) (j + n))
        (Work.Thom.TsqH.Ttop X A n (Work.Cohomology.relClassOf ℤ X A t ht) j
          (Work.Cohomology.relClassOf ℤ X ∅ α hα)) := by
    rw [← hαx]
  have hd0 : Work.Cohomology.relDiffLM ℤ X A (j + n)
      ⟨Work.Cohomology.cup ℤ (TopCat.toSSet.obj X) α.1 t.1,
        Work.Cohomology.cup_mem_relKern_right ℤ X A α.1 t.2⟩ = 0 :=
    (Work.Cohomology.mixedCup_apply (TopCat.of X) A j n α.1 t
      (Work.Cohomology.relClassOf_cochainDiff ℤ (TopCat.of X) ∅ α hα) ht).choose_spec.choose
  have hd0' : ModuleCat.Hom.hom ((Work.Cohomology.relComplex ℤ X A).d (j + n) (j + n + 1))
      ⟨Work.Cohomology.cup ℤ (TopCat.toSSet.obj X) α.1 t.1,
        Work.Cohomology.cup_mem_relKern_right ℤ X A α.1 t.2⟩ = 0 := by
    rw [Work.Cohomology.relComplex_d_apply]; exact hd0
  have hcupid : ModuleCat.Hom.hom ((Work.Cohomology.cmpX X A U V).f (j + n))
      ⟨Work.Cohomology.cup ℤ (TopCat.toSSet.obj X) α.1 t.1,
        Work.Cohomology.cup_mem_relKern_right ℤ X A α.1 t.2⟩
      = Work.Thom.cupTop X A U V n j t.1 t.2 ((Work.Cohomology.cmpX X ∅ U V).f j α) := by
    rw [show (⟨Work.Cohomology.cup ℤ (TopCat.toSSet.obj X) α.1 t.1,
          Work.Cohomology.cup_mem_relKern_right ℤ X A α.1 t.2⟩ :
            ↥((Work.Cohomology.relComplex ℤ X A).X (j + n)))
        = (Work.Thom.cupRightLM t ∅ j) α from by
          apply Subtype.ext
          rw [Work.Thom.cupRightLM_apply]]
    exact Work.Thom.cupCmpRestrictTop X A U V n j t α
  have himg : ModuleCat.Hom.hom ((tcycRelDual X A U V).d (j + n) (j + n + 1))
      (ModuleCat.Hom.hom ((Work.Cohomology.cmpX X A U V).f (j + n))
        ⟨Work.Cohomology.cup ℤ (TopCat.toSSet.obj X) α.1 t.1,
          Work.Cohomology.cup_mem_relKern_right ℤ X A α.1 t.2⟩) = 0 := by
    rw [hcupid]; exact hmid
  have hcup_top_id : Work.Cohomology.relClassOf ℤ X A
        ⟨Work.Cohomology.cup ℤ (TopCat.toSSet.obj X) α.1 t.1,
          Work.Cohomology.cup_mem_relKern_right ℤ X A α.1 t.2⟩ hd0
      = (Work.Cohomology.relComplex ℤ X A).homologyπ (j + n)
        (Work.Cohomology.cocycleOfK (Work.Cohomology.relComplex ℤ X A)
          ⟨Work.Cohomology.cup ℤ (TopCat.toSSet.obj X) α.1 t.1,
            Work.Cohomology.cup_mem_relKern_right ℤ X A α.1 t.2⟩ hd0') :=
    Work.Cohomology.relClassOf_eq_homologyπ_cocycleOfK ℤ X A _ hd0 hd0'
  have hmid2 : (tcycRelDual X A U V).homologyπ (j + n)
        (Work.Cohomology.cocycleOfK (tcycRelDual X A U V)
          (ModuleCat.Hom.hom ((Work.Cohomology.cmpX X A U V).f (j + n))
            ⟨Work.Cohomology.cup ℤ (TopCat.toSSet.obj X) α.1 t.1,
              Work.Cohomology.cup_mem_relKern_right ℤ X A α.1 t.2⟩) himg)
      = (tcycRelDual X A U V).homologyπ (j + n)
        (Work.Cohomology.cocycleOfK (tcycRelDual X A U V)
          (Work.Thom.cupTop X A U V n j t.1 t.2 ((Work.Cohomology.cmpX X ∅ U V).f j α)) hmid) := by
    congr 1
    exact tcycCocycleOfKCongr (tcycRelDual X A U V) _ _ hcupid himg hmid
  have step2 : ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (Work.Cohomology.cmpX X A U V) (j + n))
        (Work.Thom.TsqH.Ttop X A n (Work.Cohomology.relClassOf ℤ X A t ht) j
          (Work.Cohomology.relClassOf ℤ X ∅ α hα))
      = (tcycRelDual X A U V).homologyπ (j + n)
        (Work.Cohomology.cocycleOfK (tcycRelDual X A U V)
          (Work.Thom.cupTop X A U V n j t.1 t.2 w) hcw) := by
    rw [Work.Thom.tcycTtopRelClassOf X A U V n j t ht α hα]
    rw [show Work.Cohomology.relClassOf ℤ X A
          ⟨Work.Cohomology.cup ℤ (TopCat.toSSet.obj X) α.1 t.1,
            (Work.Cohomology.mixedCup_apply (TopCat.of X) A j n α.1 t
              (Work.Cohomology.relClassOf_cochainDiff ℤ (TopCat.of X) ∅ α hα) ht).choose⟩
          ((Work.Cohomology.mixedCup_apply (TopCat.of X) A j n α.1 t
            (Work.Cohomology.relClassOf_cochainDiff ℤ (TopCat.of X) ∅ α hα) ht).choose_spec.choose)
        = (Work.Cohomology.relComplex ℤ X A).homologyπ (j + n)
            (Work.Cohomology.cocycleOfK (Work.Cohomology.relComplex ℤ X A)
              ⟨Work.Cohomology.cup ℤ (TopCat.toSSet.obj X) α.1 t.1,
                (Work.Cohomology.mixedCup_apply (TopCat.of X) A j n α.1 t
                  (Work.Cohomology.relClassOf_cochainDiff ℤ (TopCat.of X) ∅ α hα) ht).choose⟩
              hd0') from
      Work.Cohomology.relClassOf_eq_homologyπ_cocycleOfK ℤ X A _ _ hd0']
    exact (tcycHomologyMapCocycleOfK (Work.Cohomology.cmpX X A U V) (j + n)
        ⟨Work.Cohomology.cup ℤ (TopCat.toSSet.obj X) α.1 t.1,
          (Work.Cohomology.mixedCup_apply (TopCat.of X) A j n α.1 t
            (Work.Cohomology.relClassOf_cochainDiff ℤ (TopCat.of X) ∅ α hα) ht).choose⟩
        hd0' himg).trans (hmid2.trans hcomp)
  have hmain : ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (Work.Cohomology.cmpX X A U V) (j + n))
        (Work.Thom.TsqH.Ttop X A n (Work.Cohomology.relClassOf ℤ X A t ht) j x)
      = (tcycRelDual X A U V).homologyπ (j + n)
        (Work.Cohomology.cocycleOfK (tcycRelDual X A U V)
          (Work.Thom.cupTop X A U V n j t.1 t.2 w) hcw) := step1.trans step2
  rw [← hmain]
  rw [← Work.Cohomology.cmpXIso_hom X A U V hU hV hcov (j + n)]
  exact (Iso.hom_inv_id_apply (Work.Cohomology.cmpXIso X A U V hU hV hcov (j + n))
    (Work.Thom.TsqH.Ttop X A n (Work.Cohomology.relClassOf ℤ X A t ht) j x)).symm

end

end Work.Thom
