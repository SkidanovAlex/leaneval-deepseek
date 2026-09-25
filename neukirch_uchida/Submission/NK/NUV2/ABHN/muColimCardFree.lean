import Mathlib
import Submission.NK.NUV2.ABHN.LocalBrauerAux
import Submission.NK.NUV2.ABHN.LocalBrauerCommons
import Submission.NK.HassePrinciple.MuColimit
import Submission.NK.HassePrinciple.kummerColim_injective
import Submission.NK.NUV2.ABHN.kummerColim_injective_field
import Submission.NK.NUV2.ABHN.unitsLevelH2_card
import Submission.NK.NUV2.ABHN.exists_level_dvd
import Submission.NK.NUV2.ABHN.unitsLevelMap_injective
import Submission.NK.HassePrinciple.kummerMap_range_eq_pTorsion
import Submission.NK.HassePrinciple.hilbert90_levelGroup
import Submission.Commons.NumberTheory.NumberField.charZero_adicCompletion
import Submission.NK.NUV2.ABHN.kummerColim_surjective_pTorsion
import Submission.NK.NUV2.LC.unitsLevelH2_addOrderOf_realization
import Submission.Commons.NumberTheory.NumberField.Completion.addEquiv_groupCohomology_two_units_topAlgEquiv
import Submission.Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg

namespace NK.NUV2.ABHN

open CategoryTheory
open NK.HassePrinciple

set_option autoImplicit false

variable {K K' : Type} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-! ## A. Elementary counting in a finite cyclic additive group -/

lemma isAddCyclic_of_addOrderOf_eq_natCard {A : Type*} [AddCommGroup A] {n : ℕ} (hn : 0 < n)
    (a : A) (ha : addOrderOf a = n) (hcard : Nat.card A = n) : IsAddCyclic A := by
  haveI : Finite ↥(AddSubgroup.zmultiples a) :=
    (Nat.card_pos_iff.mp (by rw [Nat.card_zmultiples, ha]; exact hn)).2
  rw [isAddCyclic_iff_exists_zmultiples_eq_top]
  exact ⟨a, AddSubgroup.eq_top_of_card_eq _ (by rw [Nat.card_zmultiples, ha, hcard])⟩

lemma natCard_pTorsion_le {A : Type*} [AddCommGroup A] [Finite A] [IsAddCyclic A] {p : ℕ}
    (hp : 0 < p) : Nat.card ↥(nsmulAddMonoidHom p : A →+ A).ker ≤ p := by
  rw [IsAddCyclic.card_nsmulAddMonoidHom_ker]
  exact Nat.gcd_le_right _ hp

lemma natCard_pTorsion_eq {A : Type*} [AddCommGroup A] [Finite A] [IsAddCyclic A] {p : ℕ}
    (hdvd : p ∣ Nat.card A) : Nat.card ↥(nsmulAddMonoidHom p : A →+ A).ker = p := by
  rw [IsAddCyclic.card_nsmulAddMonoidHom_ker, Nat.gcd_eq_right hdvd]

/-! ## B. The structure maps of the units colimit -/

noncomputable def ofLevelAddHom (V : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K') :
    ↥(UnitsLevelH2 V L) →+ H2Units V where
  toFun := H2Units.ofLevel V L
  map_zero' := by
    have h : (H2Units.ofLevel V L 0 : H2Units V) = H2Units.ofLevel V L 0 + H2Units.ofLevel V L 0 := by
      rw [← H2Units.ofLevel_add V L 0 0, add_zero]
    exact (add_left_cancel (show (H2Units.ofLevel V L 0 : H2Units V) + 0
      = H2Units.ofLevel V L 0 + H2Units.ofLevel V L 0 from by simpa using h)).symm
  map_add' := H2Units.ofLevel_add V L

lemma ofLevelAddHom_apply (V : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K')
    (x : ↥(UnitsLevelH2 V L)) :
    ofLevelAddHom V L x = H2Units.ofLevel V L x := rfl

lemma ofLevelAddHom_injective (L : FiniteGaloisIntermediateField K K') :
    Function.Injective (ofLevelAddHom (⊤ : Subgroup Gal(K'/K)) L) := by
  intro a b hab
  have hab' : H2Units.ofLevel (⊤ : Subgroup Gal(K'/K)) L a
      = H2Units.ofLevel (⊤ : Subgroup Gal(K'/K)) L b := hab
  obtain ⟨M, h₁, h₂, heq⟩ :=
    (unitsLevelSystem (⊤ : Subgroup Gal(K'/K))).ofLevel_eq_iff a b |>.mp hab'
  have h_eq : (unitsLevelSystem (⊤ : Subgroup Gal(K'/K))).map h₁ a
      = (unitsLevelSystem (⊤ : Subgroup Gal(K'/K))).map h₁ b :=
    heq.trans (congrArg (fun f => f b)
      (NK.BrauerTwist.LevelSystem.map_congr (S := unitsLevelSystem (⊤ : Subgroup Gal(K'/K)))
        (h := h₂) (h' := h₁)))
  exact unitsLevelMap_injective (K := K) (K' := K') h₁ h_eq

/-! ## C. The `p`-torsion of the units colimit -/

lemma ofLevel_unitsLevelMap {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L')
    (a : ↥(UnitsLevelH2 (⊤ : Subgroup Gal(K'/K)) L)) :
    ofLevelAddHom (⊤ : Subgroup Gal(K'/K)) L'
      ((unitsLevelMap (⊤ : Subgroup Gal(K'/K))
        ((FiniteGaloisIntermediateField.le_iff L L').mp h)).hom a)
      = ofLevelAddHom (⊤ : Subgroup Gal(K'/K)) L a :=
  (unitsLevelSystem (⊤ : Subgroup Gal(K'/K))).ofLevel_map h a

noncomputable def levelPTors (p : ℕ) (L : FiniteGaloisIntermediateField K K') :
    AddSubgroup ↥(UnitsLevelH2 (⊤ : Subgroup Gal(K'/K)) L) :=
  (nsmulAddMonoidHom p : ↥(UnitsLevelH2 (⊤ : Subgroup Gal(K'/K)) L) →+ _).ker

lemma mem_levelPTors {p : ℕ} {L : FiniteGaloisIntermediateField K K'}
    {x : ↥(UnitsLevelH2 (⊤ : Subgroup Gal(K'/K)) L)} :
    x ∈ levelPTors (K := K) (K' := K') p L ↔ p • x = 0 :=
  AddMonoidHom.mem_ker

noncomputable def colimImagePTors (p : ℕ) (L : FiniteGaloisIntermediateField K K') :
    AddSubgroup (H2Units (⊤ : Subgroup Gal(K'/K))) :=
  AddSubgroup.map (ofLevelAddHom (⊤ : Subgroup Gal(K'/K)) L)
    (levelPTors (K := K) (K' := K') p L)

noncomputable def colimPTors (p : ℕ) : AddSubgroup (H2Units (⊤ : Subgroup Gal(K'/K))) :=
  (nsmulAddMonoidHom p : H2Units (⊤ : Subgroup Gal(K'/K)) →+ _).ker

lemma mem_colimPTors {p : ℕ} {y : H2Units (⊤ : Subgroup Gal(K'/K))} :
    y ∈ colimPTors (K := K) (K' := K') p ↔ p • y = 0 :=
  AddMonoidHom.mem_ker

lemma mem_colimImagePTors {p : ℕ} {L : FiniteGaloisIntermediateField K K'}
    {y : H2Units (⊤ : Subgroup Gal(K'/K))} :
    y ∈ colimImagePTors (K := K) (K' := K') p L ↔
      ∃ x : ↥(UnitsLevelH2 (⊤ : Subgroup Gal(K'/K)) L),
        p • x = 0 ∧ ofLevelAddHom (⊤ : Subgroup Gal(K'/K)) L x = y := by
  rw [colimImagePTors, AddSubgroup.mem_map]
  constructor
  · rintro ⟨x, hx, hxy⟩
    exact ⟨x, (mem_levelPTors).mp hx, hxy⟩
  · rintro ⟨x, hx, hxy⟩
    exact ⟨x, (mem_levelPTors).mpr hx, hxy⟩

lemma colimImagePTors_mono {p : ℕ} {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L') :
    colimImagePTors (K := K) (K' := K') p L ≤ colimImagePTors (K := K) (K' := K') p L' := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (mem_colimImagePTors).mp hy
  refine (mem_colimImagePTors).mpr
    ⟨(unitsLevelMap (⊤ : Subgroup Gal(K'/K)) ((FiniteGaloisIntermediateField.le_iff L L').mp h)).hom x,
      ?_, ofLevel_unitsLevelMap (K := K) (K' := K') h x⟩
  rw [← map_nsmul, hx, map_zero]

lemma colimImagePTors_le_colimPTors {p : ℕ} {L : FiniteGaloisIntermediateField K K'} :
    colimImagePTors (K := K) (K' := K') p L ≤ colimPTors (K := K) (K' := K') p := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (mem_colimImagePTors).mp hy
  rw [mem_colimPTors, ← map_nsmul, hx, map_zero]

lemma exists_mem_colimImagePTors {p : ℕ} {y : H2Units (⊤ : Subgroup Gal(K'/K))}
    (hy : y ∈ colimPTors (K := K) (K' := K') p) :
    ∃ L : FiniteGaloisIntermediateField K K',
      y ∈ colimImagePTors (K := K) (K' := K') p L := by
  rw [mem_colimPTors] at hy
  obtain ⟨L, a, ha⟩ := (unitsLevelSystem (⊤ : Subgroup Gal(K'/K))).ofLevel_surjective y
  let a' : ↥(UnitsLevelH2 (⊤ : Subgroup Gal(K'/K)) L) := a
  have ha' : ofLevelAddHom (⊤ : Subgroup Gal(K'/K)) L a' = y := ha
  have h1 : ofLevelAddHom (⊤ : Subgroup Gal(K'/K)) L (p • a') = 0 := by
    rw [map_nsmul, ha']; exact hy
  have h2 : (unitsLevelSystem (⊤ : Subgroup Gal(K'/K))).ofLevel L (p • a')
      = (unitsLevelSystem (⊤ : Subgroup Gal(K'/K))).ofLevel L
        (0 : ↥(UnitsLevelH2 (⊤ : Subgroup Gal(K'/K)) L)) := by
    rw [show (unitsLevelSystem (⊤ : Subgroup Gal(K'/K))).ofLevel L
        (0 : ↥(UnitsLevelH2 (⊤ : Subgroup Gal(K'/K)) L))
      = ofLevelAddHom (⊤ : Subgroup Gal(K'/K)) L 0 from (ofLevelAddHom_apply _ _ _).symm,
      map_zero]
    exact h1
  obtain ⟨M, h₁, h₂, heq⟩ :=
    (unitsLevelSystem (⊤ : Subgroup Gal(K'/K))).ofLevel_eq_iff (p • a')
      (0 : ↥(UnitsLevelH2 (⊤ : Subgroup Gal(K'/K)) L)) |>.mp h2
  have hzero : (unitsLevelSystem (⊤ : Subgroup Gal(K'/K))).map h₂
      (0 : ↥(UnitsLevelH2 (⊤ : Subgroup Gal(K'/K)) L)) = 0 := by
    change (unitsLevelMap (⊤ : Subgroup Gal(K'/K))
      ((FiniteGaloisIntermediateField.le_iff L M).mp h₂)).hom 0 = 0
    rw [map_zero]
  have heq' : (unitsLevelSystem (⊤ : Subgroup Gal(K'/K))).map h₁ (p • a') = 0 := by
    rw [heq, hzero]
  refine ⟨M, ?_⟩
  refine (mem_colimImagePTors).mpr ⟨(unitsLevelMap (⊤ : Subgroup Gal(K'/K))
    ((FiniteGaloisIntermediateField.le_iff L M).mp h₁)).hom a', ?_, ?_⟩
  · rw [← map_nsmul]
    exact heq'
  · exact (ofLevel_unitsLevelMap (K := K) (K' := K') h₁ a').trans ha'

/-- The additive equivalence between the `p`-torsion of a level and its image in the colimit. -/
noncomputable def colimImagePTorsEquiv (p : ℕ) (L : FiniteGaloisIntermediateField K K') :
    ↥(levelPTors (K := K) (K' := K') p L) ≃ ↥(colimImagePTors (K := K) (K' := K') p L) :=
  Equiv.ofBijective
    (fun x => ⟨ofLevelAddHom (⊤ : Subgroup Gal(K'/K)) L x,
      AddSubgroup.mem_map.mpr ⟨x, x.2, rfl⟩⟩)
    ⟨fun a b hab => Subtype.ext (ofLevelAddHom_injective L (Subtype.ext_iff.mp hab)),
     fun b => by
      obtain ⟨x, hx, hxb⟩ := AddSubgroup.mem_map.mp b.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxb⟩⟩

lemma natCard_colimImagePTors (p : ℕ) (L : FiniteGaloisIntermediateField K K') :
    Nat.card ↥(colimImagePTors (K := K) (K' := K') p L)
      = Nat.card ↥(levelPTors (K := K) (K' := K') p L) :=
  (Nat.card_congr (colimImagePTorsEquiv (K := K) (K' := K') p L)).symm


/-! ## D0. Generic coefficient-morphism facts for `groupCohomology.map` -/

section Generic
variable {k : Type} [CommRing k] {G : Type} [Group G]

lemma gc_map_add {A B : Rep.{0,0,0} k G} (φ ψ : A ⟶ B) (n : ℕ) :
    groupCohomology.map (MonoidHom.id G) (φ + ψ) n
      = groupCohomology.map (MonoidHom.id G) φ n
        + groupCohomology.map (MonoidHom.id G) ψ n := by
  show HomologicalComplex.homologyMap
    (groupCohomology.cochainsMap (MonoidHom.id G) (φ + ψ)) n = _
  rw [show groupCohomology.cochainsMap (MonoidHom.id G) (φ + ψ)
        = groupCohomology.cochainsMap (MonoidHom.id G) φ
          + groupCohomology.cochainsMap (MonoidHom.id G) ψ from
      CategoryTheory.Functor.map_add
        (F := groupCohomology.cochainsFunctor k G) (f := φ) (g := ψ),
    HomologicalComplex.homologyMap_add]
  rfl

lemma gc_map_zero {A B : Rep.{0,0,0} k G} (n : ℕ) :
    groupCohomology.map (MonoidHom.id G) (0 : A ⟶ B) n = 0 := by
  show HomologicalComplex.homologyMap
    (groupCohomology.cochainsMap (MonoidHom.id G) (0 : A ⟶ B)) n = 0
  rw [groupCohomology.cochainsMap_zero]
  simp

lemma gc_map_nsmul {A B : Rep.{0,0,0} k G} (φ : A ⟶ B) (m n : ℕ) :
    groupCohomology.map (MonoidHom.id G) (m • φ) n
      = m • groupCohomology.map (MonoidHom.id G) φ n := by
  induction m with
  | zero => rw [zero_nsmul, gc_map_zero, zero_nsmul]
  | succ j ih => rw [succ_nsmul, gc_map_add, ih, succ_nsmul]

lemma gc_map_comp {A B C : Rep.{0,0,0} k G} (φ : A ⟶ B) (ψ : B ⟶ C) (n : ℕ) :
    groupCohomology.map (MonoidHom.id G) (φ ≫ ψ) n
      = groupCohomology.map (MonoidHom.id G) φ n
        ≫ groupCohomology.map (MonoidHom.id G) ψ n :=
  groupCohomology.map_comp (MonoidHom.id G) (MonoidHom.id G) φ ψ n

end Generic

/-! ## D1. The Kummer map lands in the `p`-torsion -/

section KummerImage

variable {k : Type} [CommRing k] {G : Type} [Group G] {A B : Rep.{0,0,0} k G}

lemma rep_nsmul_one_hom_apply (p : ℕ) (y : A.V) :
    (Rep.Hom.hom ((p : ℕ) • 𝟙 A)) y = p • y := by
  rw [Rep.nsmul_hom]
  change (p • (LinearMap.id : A.V →ₗ[k] A.V)) y = p • y
  rw [← Nat.cast_smul_eq_nsmul k p (LinearMap.id : A.V →ₗ[k] A.V)]
  rw [LinearMap.smul_apply]
  show (p : k) • y = p • y
  exact Nat.cast_smul_eq_nsmul k p y

lemma gc_map_apply_nsmul (m n : ℕ) (x : ↥(groupCohomology A n)) :
    (ModuleCat.Hom.hom (groupCohomology.map (MonoidHom.id G) (m • 𝟙 A) n)) x = m • x := by
  rw [gc_map_nsmul, groupCohomology.map_id]
  rfl

lemma gc_map_apply_zero (n : ℕ) (x : ↥(groupCohomology A n)) :
    (ModuleCat.Hom.hom (groupCohomology.map (MonoidHom.id G) (0 : A ⟶ A) n)) x = 0 := by
  rw [gc_map_zero]
  rfl

end KummerImage

section KummerImageLocal

variable {K K' : Type} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

lemma muToUnits_comp_nsmul_zero (p : ℕ) (L : FiniteGaloisIntermediateField K K') :
    (muToUnits p (⊤ : Subgroup Gal(K'/K)) L)
      ≫ ((p : ℕ) • 𝟙 (unitsLevelRep (⊤ : Subgroup Gal(K'/K)) L)) = 0 := by
  apply Rep.hom_injective
  rw [Rep.hom_comp]
  ext x
  let u : Additive ↥(rootsOfUnity p ↥L) := x
  change (p : ℕ) • (Additive.ofMul ((Additive.toMul u : rootsOfUnity p ↥L) : (↥L)ˣ)) = 0
  refine Additive.toMul.injective ?_
  rw [toMul_nsmul, toMul_ofMul, toMul_zero]
  exact (Additive.toMul u).2

lemma kummerColim_mem_colimPTors (p : ℕ) (x : MuColim (K := K) (K' := K') p ⊤) :
    kummerColim p (⊤ : Subgroup Gal(K'/K)) x ∈ colimPTors (K := K) (K' := K') p := by
  obtain ⟨L, a, ha⟩ := (muLevelSystem (K := K) (K' := K') p ⊤).ofLevel_surjective x
  let a' : ↥(MuLevelH2 p (⊤ : Subgroup Gal(K'/K)) L) := a
  have hx : kummerColim p (⊤ : Subgroup Gal(K'/K)) x
      = ofLevelAddHom (⊤ : Subgroup Gal(K'/K)) L
        ((kummerLevel p (⊤ : Subgroup Gal(K'/K)) L).hom a') := by
    rw [← ha]
    show kummerColim p (⊤ : Subgroup Gal(K'/K)) (MuColim.ofLevel p (⊤ : Subgroup Gal(K'/K)) L a') = _
    rw [kummerColim_ofLevel]
    rfl
  rw [mem_colimPTors, hx, ← map_nsmul]
  rw [show p • (kummerLevel p (⊤ : Subgroup Gal(K'/K)) L).hom a' = 0 from ?_, map_zero]
  have h1 : p • (kummerLevel p (⊤ : Subgroup Gal(K'/K)) L).hom a'
      = (ModuleCat.Hom.hom (groupCohomology.map (MonoidHom.id
          (NK.BrauerHasse.LevelGroup (⊤ : Subgroup Gal(K'/K)) L))
          (p • 𝟙 (unitsLevelRep (⊤ : Subgroup Gal(K'/K)) L)) 2))
        ((kummerLevel p (⊤ : Subgroup Gal(K'/K)) L).hom a') :=
    (gc_map_apply_nsmul (A := unitsLevelRep (⊤ : Subgroup Gal(K'/K)) L) p 2 ((kummerLevel p (⊤ : Subgroup Gal(K'/K)) L).hom a')).symm
  rw [h1]
  have h2 : (kummerLevel p (⊤ : Subgroup Gal(K'/K)) L)
      = groupCohomology.map (MonoidHom.id (NK.BrauerHasse.LevelGroup
          (⊤ : Subgroup Gal(K'/K)) L)) (muToUnits p (⊤ : Subgroup Gal(K'/K)) L) 2 := rfl
  rw [h2]
  rw [show (ModuleCat.Hom.hom (groupCohomology.map (MonoidHom.id
        (NK.BrauerHasse.LevelGroup (⊤ : Subgroup Gal(K'/K)) L))
        (p • 𝟙 (unitsLevelRep (⊤ : Subgroup Gal(K'/K)) L)) 2))
      ((ModuleCat.Hom.hom (groupCohomology.map (MonoidHom.id
        (NK.BrauerHasse.LevelGroup (⊤ : Subgroup Gal(K'/K)) L))
        (muToUnits p (⊤ : Subgroup Gal(K'/K)) L) 2)) a')
      = (ModuleCat.Hom.hom ((groupCohomology.map (MonoidHom.id
          (NK.BrauerHasse.LevelGroup (⊤ : Subgroup Gal(K'/K)) L))
          (muToUnits p (⊤ : Subgroup Gal(K'/K)) L) 2)
        ≫ (groupCohomology.map (MonoidHom.id (NK.BrauerHasse.LevelGroup
            (⊤ : Subgroup Gal(K'/K)) L))
          (p • 𝟙 (unitsLevelRep (⊤ : Subgroup Gal(K'/K)) L)) 2))) a' from
    (ModuleCat.comp_apply _ _ a').symm]
  rw [← gc_map_comp (muToUnits p (⊤ : Subgroup Gal(K'/K)) L)
    (p • 𝟙 (unitsLevelRep (⊤ : Subgroup Gal(K'/K)) L)) 2]
  rw [muToUnits_comp_nsmul_zero p L]
  rw [gc_map_zero]
  rfl

end KummerImageLocal

/-! ## C-local. The `p`-torsion of the units colimit has `p` elements -/

section CLocal

variable (K : Type) [Field K] [NumberField K]
variable (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))

lemma unitsLevelH2_isAddCyclic
    (L : FiniteGaloisIntermediateField (𝔮.adicCompletion K) (SeparableClosure (𝔮.adicCompletion K))) :
    IsAddCyclic ↥(UnitsLevelH2 (K := 𝔮.adicCompletion K)
      (K' := SeparableClosure (𝔮.adicCompletion K)) ⊤ L) := by
  obtain ⟨α, hα⟩ :=
    NK.NUV2.LC.exists_addOrderOf_eq_finrank_groupCohomology_two_units_local
      (K := K) 𝔮 (F := 𝔮.adicCompletion K) (E := ↑L)
  obtain ⟨e⟩ := NK.NUV2.LC.nonempty_addEquiv_unitsLevelH2_top
    (K := 𝔮.adicCompletion K) (K' := SeparableClosure (𝔮.adicCompletion K)) L
  refine isAddCyclic_of_addOrderOf_eq_natCard Module.finrank_pos (e.symm α) ?_
    (unitsLevelH2_card K 𝔮 L)
  have h1 : addOrderOf (e.symm α) = Module.finrank (𝔮.adicCompletion K) ↑L := by
    rw [show addOrderOf (e.symm α) = addOrderOf α from
      addOrderOf_injective (f := e.symm.toAddMonoidHom) e.symm.injective α, hα]
  exact h1

lemma unitsLevelH2_finite
    (L : FiniteGaloisIntermediateField (𝔮.adicCompletion K) (SeparableClosure (𝔮.adicCompletion K))) :
    Finite ↥(UnitsLevelH2 (K := 𝔮.adicCompletion K)
      (K' := SeparableClosure (𝔮.adicCompletion K)) ⊤ L) :=
  (Nat.card_pos_iff.mp (by rw [unitsLevelH2_card K 𝔮 L]; exact Module.finrank_pos)).2

lemma natCard_levelPTors_le (p : ℕ) (hp : p.Prime)
    (L : FiniteGaloisIntermediateField (𝔮.adicCompletion K) (SeparableClosure (𝔮.adicCompletion K))) :
    Nat.card ↥(levelPTors (K := 𝔮.adicCompletion K)
      (K' := SeparableClosure (𝔮.adicCompletion K)) p L) ≤ p := by
  haveI := unitsLevelH2_finite K 𝔮 L
  haveI := unitsLevelH2_isAddCyclic K 𝔮 L
  exact natCard_pTorsion_le hp.pos

lemma natCard_levelPTors_eq (p : ℕ) (hp : p.Prime)
    (L : FiniteGaloisIntermediateField (𝔮.adicCompletion K) (SeparableClosure (𝔮.adicCompletion K)))
    (hdvd : p ∣ Module.finrank (𝔮.adicCompletion K) ↥L) :
    Nat.card ↥(levelPTors (K := 𝔮.adicCompletion K)
      (K' := SeparableClosure (𝔮.adicCompletion K)) p L) = p := by
  haveI := unitsLevelH2_finite K 𝔮 L
  haveI := unitsLevelH2_isAddCyclic K 𝔮 L
  refine natCard_pTorsion_eq (A := ↥(UnitsLevelH2 (K := 𝔮.adicCompletion K)
    (K' := SeparableClosure (𝔮.adicCompletion K)) ⊤ L)) ?_
  rw [unitsLevelH2_card K 𝔮 L]
  exact hdvd

lemma finite_colimImagePTors (p : ℕ)
    (L : FiniteGaloisIntermediateField (𝔮.adicCompletion K) (SeparableClosure (𝔮.adicCompletion K))) :
    Finite ↥(colimImagePTors (K := 𝔮.adicCompletion K)
      (K' := SeparableClosure (𝔮.adicCompletion K)) p L) := by
  haveI := unitsLevelH2_finite K 𝔮 L
  refine Finite.of_injective (fun y => (colimImagePTorsEquiv (K := 𝔮.adicCompletion K)
      (K' := SeparableClosure (𝔮.adicCompletion K)) p L).symm y) (Equiv.injective _)

theorem natCard_colimPTors_eq (p : ℕ) (hp : p.Prime) :
    Nat.card ↥(colimPTors (K := 𝔮.adicCompletion K)
      (K' := SeparableClosure (𝔮.adicCompletion K)) p) = p := by
  obtain ⟨L₀, hdvd⟩ := exists_level_dvd K 𝔮 hp
  have himg : ∀ L, Nat.card ↥(colimImagePTors (K := 𝔮.adicCompletion K)
      (K' := SeparableClosure (𝔮.adicCompletion K)) p L) ≤ p := by
    intro L
    rw [natCard_colimImagePTors]
    exact natCard_levelPTors_le K 𝔮 p hp L
  have himg₀ : Nat.card ↥(colimImagePTors (K := 𝔮.adicCompletion K)
      (K' := SeparableClosure (𝔮.adicCompletion K)) p L₀) = p := by
    rw [natCard_colimImagePTors]
    exact natCard_levelPTors_eq K 𝔮 p hp L₀ hdvd
  have hsubset : colimPTors (K := 𝔮.adicCompletion K)
      (K' := SeparableClosure (𝔮.adicCompletion K)) p ≤
      colimImagePTors (K := 𝔮.adicCompletion K)
        (K' := SeparableClosure (𝔮.adicCompletion K)) p L₀ := by
    intro y hy
    obtain ⟨L, hyL⟩ := exists_mem_colimImagePTors (K := 𝔮.adicCompletion K)
      (K' := SeparableClosure (𝔮.adicCompletion K)) hy
    have h₁ : colimImagePTors (K := 𝔮.adicCompletion K)
        (K' := SeparableClosure (𝔮.adicCompletion K)) p L ≤
        colimImagePTors (K := 𝔮.adicCompletion K)
          (K' := SeparableClosure (𝔮.adicCompletion K)) p (L ⊔ L₀) :=
      colimImagePTors_mono le_sup_left
    have h₂ : colimImagePTors (K := 𝔮.adicCompletion K)
        (K' := SeparableClosure (𝔮.adicCompletion K)) p L₀ ≤
        colimImagePTors (K := 𝔮.adicCompletion K)
          (K' := SeparableClosure (𝔮.adicCompletion K)) p (L ⊔ L₀) :=
      colimImagePTors_mono le_sup_right
    have h₃ : colimImagePTors (K := 𝔮.adicCompletion K)
        (K' := SeparableClosure (𝔮.adicCompletion K)) p L₀ =
        colimImagePTors (K := 𝔮.adicCompletion K)
          (K' := SeparableClosure (𝔮.adicCompletion K)) p (L ⊔ L₀) := by
      haveI := finite_colimImagePTors K 𝔮 p (L ⊔ L₀)
      refine AddSubgroup.eq_of_le_of_card_ge h₂ ?_
      rw [himg₀]
      exact himg (L ⊔ L₀)
    rw [h₃]
    exact h₁ hyL
  have heq : colimPTors (K := 𝔮.adicCompletion K)
      (K' := SeparableClosure (𝔮.adicCompletion K)) p =
      colimImagePTors (K := 𝔮.adicCompletion K)
        (K' := SeparableClosure (𝔮.adicCompletion K)) p L₀ :=
    le_antisymm hsubset (colimImagePTors_le_colimPTors)
  rw [heq, himg₀]

end CLocal

/-- **The cardinality of the `μ_p`-colimit over the levels of a `p`-adic field.**

Let `K` be a number field, `𝔮` a finite prime of `K` and `κ = 𝔮.adicCompletion K` the
corresponding `p`-adic field; let `p` be a prime such that `κ` contains a primitive `p`-th root of
unity.  Then the filtered colimit

`NK.HassePrinciple.MuColim p ⊤ = colim_L H²(Gal(L/κ), μ_p(L))`

over the finite Galois levels `L` of `κ̄/κ` has exactly `p` elements.  Equivalently: the continuous
cohomology `H²(G_κ, μ_p) = Br(κ)[p]` is `ℤ/p`, the local Brauer group computation (Serre, *Local
Fields* XII–XIV; NSW (7.1.7), (7.2.6)).

Because `μ_p ⊆ κ`, the cyclotomic twist is trivial
(`NK.BrauerTwist.muRep_isTrivial_of_isPrimitiveRoot`), so all coefficient modules are the trivial
`ℤ/p`.  Roadmap:

1. level-wise, for a finite Galois `E/F` of `p`-adic fields,
   `Nat.card (H²(Gal(E/F), Eˣ)) = [E : F]` and `H²(Gal(E/F), Eˣ)` contains an element of additive
   order `[E : F]` — the union of
   `Commons.NumberTheory.NumberField.Completion.exists_addOrderOf_eq_finrank_groupCohomology_two_units_adicCompletion`
   (the local fundamental class, Milne *CFT* III.2) with the upper bound
   `Commons.NumberTheory.NumberField.Completion.natCard_groupCohomology_two_units_le_finrank_of_solvable`
   (Milne *CFT* III.1.7), the Galois group being solvable (the ramification filtration;
   `Commons.NumberTheory.NumberField.Completion.finite_groupCohomology_two_units_adicCompletion_of_isGalois`
   proves finiteness by proving exactly this solvability);
2. hence for every finite Galois level `L` the group `H²(Gal(L/κ), Lˣ)` is cyclic of order `[L : κ]`,
   so its `p`-torsion is `ℤ/p` if `p ∣ [L : κ]` and `0` otherwise; inflation between levels is
   injective (Hilbert 90), so inside a common larger level two `p`-torsion classes can be compared
   and are equal (a cyclic group has a unique subgroup of order `p`), which shows that the
   `p`-torsion of the units colimit `H2Units ⊤ = colim_L H²(Gal(L/κ), Lˣ)` is `ℤ/p`;
3. the Kummer map on the colimits
   `NK.HassePrinciple.kummerColim p ⊤ : MuColim p ⊤ → H2Units ⊤` is injective (proved in the
   workspace as `NK.HassePrinciple.kummerColim_injective`, specialised to fields in
   `NK.NUV2.ABHN.kummerColim_injective_field`), lands in the `p`-torsion (level-wise
   `p · kummerLevel a = map (unitsPow p) (kummerLevel a) = kummerLevel (map (muPow p) a) = 0`
   because `μ_p` is `p`-torsion), and in the limit its image *is* the `p`-torsion (the units of the
   separably closed `κ̄` are `p`-divisible, so the Kummer sequence is exact in the limit); hence
   `MuColim p ⊤ ≃ {x : H2Units ⊤ // p • x = 0}` as types, giving both cardinality bounds.

The additive group structure on `H2Units` and `MuColim` needed for `p • x` is the one supplied by
`NK.NUV2.ABHN.LocalBrauerAux` (`instAddCommGroupH2Units`, `instAddCommGroupMuColim`). -/
theorem muColimCardFree (K : Type) [Field K] [NumberField K]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p : ℕ}
    (hp : p.Prime) (hζ : ∃ ζ : 𝔮.adicCompletion K, IsPrimitiveRoot ζ p) :
    Nat.card (NK.HassePrinciple.MuColim (K := 𝔮.adicCompletion K)
      (K' := SeparableClosure (𝔮.adicCompletion K)) p ⊤) = p := by
  haveI hcz : CharZero (𝔮.adicCompletion K) :=
    Commons.NumberTheory.NumberField.charZero_adicCompletion 𝔮
  have hinj := kummerColim_injective_field (K := 𝔮.adicCompletion K)
    (K' := SeparableClosure (𝔮.adicCompletion K)) p hp ⊤
  have hcardT := natCard_colimPTors_eq K 𝔮 p hp
  have himage : ∀ x : MuColim (K := 𝔮.adicCompletion K)
      (K' := SeparableClosure (𝔮.adicCompletion K)) p ⊤,
      kummerColim p (⊤ : Subgroup Gal(SeparableClosure (𝔮.adicCompletion K) / 𝔮.adicCompletion K)) x ∈
        colimPTors (K := 𝔮.adicCompletion K) (K' := SeparableClosure (𝔮.adicCompletion K)) p :=
    fun x => kummerColim_mem_colimPTors p x
  have heq : Nat.card (MuColim (K := 𝔮.adicCompletion K)
      (K' := SeparableClosure (𝔮.adicCompletion K)) p ⊤)
      = Nat.card ↥(colimPTors (K := 𝔮.adicCompletion K)
        (K' := SeparableClosure (𝔮.adicCompletion K)) p) := by
    refine Nat.card_congr ?_
    refine Equiv.ofBijective
      (fun x => (⟨kummerColim p (⊤ : Subgroup Gal(SeparableClosure (𝔮.adicCompletion K) /
          𝔮.adicCompletion K)) x, himage x⟩ :
        ↥(colimPTors (K := 𝔮.adicCompletion K)
          (K' := SeparableClosure (𝔮.adicCompletion K)) p))) ⟨?_, ?_⟩
    · intro a b hab
      exact hinj (Subtype.ext_iff.mp hab)
    · intro y
      obtain ⟨x, hx⟩ := kummerColim_surjective_pTorsion (K := 𝔮.adicCompletion K)
        (K' := SeparableClosure (𝔮.adicCompletion K)) p hp y y.2
      exact ⟨x, Subtype.ext hx⟩
  rw [heq, hcardT]



end NK.NUV2.ABHN
