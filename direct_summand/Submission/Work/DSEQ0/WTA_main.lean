import Mathlib
import Submission.Work.DSF1.Sheaf.unit_isIso_of_isZero_rightDerived
import Submission.Work.DSG1.triangleHomOfCommShift
import Submission.Work.DSG1.homologyTriangleIso
import Submission.Work.DSG1.isIso_homologyFunctor_Q_map
import Submission.Work.DSG1.isZero_homology_rightDerivedFunctor_plus
import Submission.Work.DSG1.isIso_homologyMap_map_of_isIso_f
import Submission.Work.DSEQ0.WTA_trunc

namespace Work.DSEQ0

universe u v w x

open CategoryTheory CategoryTheory.Limits

namespace TA

open scoped Classical

section Aux

variable {C : Type*} [Category* C] {D : Type*} [Category* D]

/-- If a square `u ≫ β = α ≫ v` commutes and `α`, `β` are isomorphisms, then `u` is an
isomorphism iff `v` is. -/
lemma isIso_iff_of_iso_conj {A B A' B' : C} {u : A ⟶ B} {v : A' ⟶ B'}
    {α : A ⟶ A'} {β : B ⟶ B'} (h : u ≫ β = α ≫ v) [IsIso α] [IsIso β] :
    IsIso u ↔ IsIso v := by
  have hu : u = α ≫ v ≫ inv β := by
    rw [(IsIso.eq_comp_inv β).mpr h, Category.assoc]
  rw [hu]
  haveI := ‹IsIso β›
  constructor
  · intro hh
    haveI := hh
    have h2 : IsIso (v ≫ inv β) := IsIso.of_isIso_comp_left α (v ≫ inv β)
    exact IsIso.of_isIso_comp_right v (inv β)
  · intro hh
    haveI := hh
    infer_instance

/-- Components of a natural transformation at isomorphic objects are simultaneously
isomorphisms. -/
lemma isIso_app_iff_of_iso {F G : C ⥤ D} (τ : F ⟶ G) {X Y : C} (e : X ≅ Y) :
    IsIso (τ.app X) ↔ IsIso (τ.app Y) :=
  isIso_iff_of_iso_conj (u := τ.app X) (v := τ.app Y)
    (α := F.map e.hom) (β := G.map e.hom) (τ.naturality e.hom).symm

/-- If a natural transformation is compatible with the shift and its component at `X` is an
isomorphism, then so is its component at any shift of `X`. -/
lemma isIso_app_shift_of_isIso {A : Type*} [AddMonoid A] [HasShift C A] [HasShift D A]
    {F G : C ⥤ D} [F.CommShift A] [G.CommShift A] {τ : F ⟶ G} [NatTrans.CommShift τ A]
    {X : C} {a : A} (h : IsIso (τ.app X)) : IsIso (τ.app (X⟦a⟧)) := by
  rw [NatTrans.app_shift]
  have : IsIso ((shiftFunctor D a).map (τ.app X)) := Functor.map_isIso _ _
  infer_instance

end Aux

section Main

variable {C : Type*} [Category* C] [Abelian C] {D : Type*} [Category* D] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [EnoughInjectives C]

/-- A cochain complex concentrated in a single degree `n` is isomorphic to the corresponding
one-term complex. -/
lemma iso_single_of_isStrictlyGE_of_isStrictlyLE (K : CochainComplex C ℤ) (n : ℤ)
    [K.IsStrictlyGE n] [K.IsStrictlyLE n] :
    Nonempty (K ≅ (CochainComplex.singleFunctor C n).obj (K.X n)) := by
  obtain ⟨M, ⟨e⟩⟩ := CochainComplex.exists_iso_single (K := K) n
  have e2 : K.X n ≅ M := by
    simpa using (HomologicalComplex.eval C (ComplexShape.up ℤ) n).mapIso e
  exact ⟨e ≪≫ (CochainComplex.singleFunctor C n).mapIso e2.symm⟩

lemma isGE_of_isStrictlyGE (K : CochainComplex C ℤ) (n : ℤ) [K.IsStrictlyGE n] : K.IsGE n := by
  rw [CochainComplex.isGE_iff]
  intro i hi
  exact ShortComplex.exact_of_isZero_X₂ _ (K.isZero_of_isStrictlyGE n i hi)

/-- The one-term complex in degree `n`, as an object of `CochainComplex.Plus C`. -/
noncomputable def plusSingleObj (A : C) (n : ℤ) : CochainComplex.Plus C :=
  ⟨(CochainComplex.singleFunctor C n).obj A, ⟨n, inferInstance⟩⟩

/-- The hypothesis of the main theorem at a single degree. -/
def IsIsoUnitSingle (A : C) (n : ℤ) : Prop :=
  IsIso (F.rightDerivedFunctorPlusUnit.app (plusSingleObj A n))

theorem isIso_unit_iff_isIso_unit_h (K : CochainComplex.Plus C) :
    IsIso (F.rightDerivedFunctorPlusUnit.app K) ↔
      IsIso (F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient C).obj K)) := by
  rw [F.rightDerivedFunctorPlusUnit_app]
  have ha : IsIso ((DerivedCategory.Plus.quotientCompQhIso D).inv.app
      (F.mapCochainComplexPlus.obj K)) := inferInstance
  have hb : IsIso (DerivedCategory.Plus.Qh.map
      (F.quotientCompMapHomotopyCategoryPlusIso.inv.app K)) := inferInstance
  have hd : IsIso (F.rightDerivedFunctorPlus.map
      ((DerivedCategory.Plus.quotientCompQhIso C).hom.app K)) := inferInstance
  haveI := ha
  haveI := hb
  haveI := hd
  constructor
  · intro h
    haveI := h
    have h1 : IsIso (DerivedCategory.Plus.Qh.map (F.quotientCompMapHomotopyCategoryPlusIso.inv.app K)
        ≫ (F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient C).obj K)
          ≫ F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.quotientCompQhIso C).hom.app K))) :=
      IsIso.of_isIso_comp_left ((DerivedCategory.Plus.quotientCompQhIso D).inv.app
        (F.mapCochainComplexPlus.obj K)) _
    haveI := h1
    have h2 : IsIso (F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient C).obj K)
        ≫ F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.quotientCompQhIso C).hom.app K)) :=
      IsIso.of_isIso_comp_left (DerivedCategory.Plus.Qh.map
        (F.quotientCompMapHomotopyCategoryPlusIso.inv.app K)) _
    exact IsIso.of_isIso_comp_right
      (F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient C).obj K))
      (F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.quotientCompQhIso C).hom.app K))
  · intro h
    haveI := h
    infer_instance

theorem isIso_unit_of_iso {X Y : CochainComplex.Plus C} (e : X ≅ Y) :
    IsIso (F.rightDerivedFunctorPlusUnit.app X) ↔
      IsIso (F.rightDerivedFunctorPlusUnit.app Y) :=
  isIso_iff_of_iso_conj (u := F.rightDerivedFunctorPlusUnit.app X)
    (v := F.rightDerivedFunctorPlusUnit.app Y)
    (α := (F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q).map e.hom)
    (β := (DerivedCategory.Plus.Q ⋙ F.rightDerivedFunctorPlus).map e.hom)
    ((F.rightDerivedFunctorPlusUnit).naturality e.hom).symm

theorem isIso_unit_h_of_iso {X Y : HomotopyCategory.Plus C} (e : X ≅ Y) :
    IsIso (F.rightDerivedFunctorPlusUnith.app X) ↔
      IsIso (F.rightDerivedFunctorPlusUnith.app Y) :=
  isIso_iff_of_iso_conj (u := F.rightDerivedFunctorPlusUnith.app X)
    (v := F.rightDerivedFunctorPlusUnith.app Y)
    (α := (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map e.hom)
    (β := (DerivedCategory.Plus.Qh ⋙ F.rightDerivedFunctorPlus).map e.hom)
    ((F.rightDerivedFunctorPlusUnith).naturality e.hom).symm

lemma isIsoUnitSingle_congr {A B : C} (e : A ≅ B) (n : ℤ) :
    IsIsoUnitSingle F A n ↔ IsIsoUnitSingle F B n :=
  isIso_unit_of_iso F (ObjectProperty.isoMk _ ((CochainComplex.singleFunctor C n).mapIso e))

lemma isIsoUnitSingle_of_isZero {A : C} (hA : IsZero A) (n : ℤ) : IsIsoUnitSingle F A n := by
  have hXobj : IsZero (plusSingleObj (C := C) A n).obj :=
    Functor.map_isZero (CochainComplex.singleFunctor C n) hA
  have hX : IsZero (plusSingleObj (C := C) A n) :=
    IsZero.of_full_of_faithful_of_isZero (CochainComplex.Plus.ι C) _ hXobj
  have hFX : IsZero ((F.mapCochainComplexPlus).obj (plusSingleObj (C := C) A n)) := by
    refine IsZero.of_full_of_faithful_of_isZero (CochainComplex.Plus.ι D) _ ?_
    change IsZero ((F.mapCochainComplexPlus.obj (plusSingleObj (C := C) A n)).obj)
    rw [Functor.mapCochainComplexPlus_obj_obj]
    exact Functor.map_isZero _ hXobj
  have h₁ : IsZero ((DerivedCategory.Plus.Q).obj
      ((F.mapCochainComplexPlus).obj (plusSingleObj (C := C) A n))) :=
    Functor.map_isZero _ hFX
  have h₂ : IsZero ((F.rightDerivedFunctorPlus).obj
      ((DerivedCategory.Plus.Q).obj (plusSingleObj (C := C) A n))) :=
    Functor.map_isZero _ (Functor.map_isZero _ hX)
  exact isIso_of_source_target_iso_zero _ (IsZero.isoZero h₁) (IsZero.isoZero h₂)

/-- **The one-term criterion at an arbitrary degree.**  If `A` is `F`-acyclic then the unit of the
right derived functor of `F` is an isomorphism at the one-term complex `A[n]`. -/
lemma isIsoUnitSingle_of_acyclic (A : C)
    (h : ∀ q : ℕ, 0 < q → IsZero ((F.rightDerived q).obj A)) (n : ℤ) :
    IsIsoUnitSingle F A n := by
  -- the unit is an isomorphism at `A[0]`
  have h0 : IsIso (F.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.singleFunctor C 0).obj A)) :=
    Work.DSF1.Sheaf.unit_isIso_of_isZero_rightDerived F A h
  -- and hence at every shift of `A[0]`
  have h1 : IsIso (F.rightDerivedFunctorPlusUnith.app
      (((HomotopyCategory.Plus.singleFunctor C 0).obj A)⟦-n⟧)) :=
    isIso_app_shift_of_isIso (F := F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)
      (G := DerivedCategory.Plus.Qh ⋙ F.rightDerivedFunctorPlus)
      (τ := F.rightDerivedFunctorPlusUnith) h0
  -- which is `A[n]`, by the compatibility of the single functors with the shift
  have h2 : IsIso (F.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.singleFunctor C n).obj A)) :=
    (isIso_app_iff_of_iso (τ := F.rightDerivedFunctorPlusUnith)
      (((HomotopyCategory.Plus.singleFunctors C).shiftIso (-n) n 0 (by simp)).app A)).mp h1
  exact (isIso_unit_iff_isIso_unit_h F (plusSingleObj A n)).mpr h2

/-- **The bounded case**, by induction on the number of degrees. -/
theorem isIso_unit_of_bounded_aux (N : ℕ) :
    ∀ (K : CochainComplex.Plus C) (n₀ : ℤ), K.obj.IsStrictlyGE n₀ →
      K.obj.IsStrictlyLE (n₀ + N) → (∀ n, IsIsoUnitSingle F (K.obj.X n) n) →
      IsIso (F.rightDerivedFunctorPlusUnit.app K) := by
  induction N with
  | zero =>
    intro K n₀ hge hle hK
    have hle' : K.obj.IsStrictlyLE n₀ := by simpa using hle
    haveI : K.obj.IsStrictlyGE n₀ := hge
    haveI : K.obj.IsStrictlyLE n₀ := hle'
    obtain ⟨e⟩ := iso_single_of_isStrictlyGE_of_isStrictlyLE K.obj n₀
    exact (isIso_unit_of_iso F (ObjectProperty.isoMk _ e)).mpr (hK n₀)
  | succ N ih =>
    intro K n₀ hge hle hK
    have hcast : n₀ + ((N + 1 : ℕ) : ℤ) = n₀ + (N : ℤ) + 1 := by push_cast; ring
    rw [hcast] at hle
    obtain ⟨S, σ, hS₂, hz₁, hx₁, hz₃, hx₃, hg⟩ := truncSES K (n₀ + (N : ℤ) + 1)
    have hS₃ge : (S.X₃).obj.IsStrictlyGE n₀ := by
      rw [CochainComplex.isStrictlyGE_iff]
      intro i hi
      obtain ⟨e⟩ := hx₃ i (by omega)
      exact (CochainComplex.isZero_of_isStrictlyGE K.obj n₀ i hi).of_iso e
    have hS₃le : (S.X₃).obj.IsStrictlyLE (n₀ + (N : ℤ)) := by
      rw [CochainComplex.isStrictlyLE_iff]
      intro i hi
      exact hz₃ i (by omega)
    have hS₃K : ∀ i, IsIsoUnitSingle F ((S.X₃).obj.X i) i := by
      intro i
      by_cases hi : i ≤ n₀ + (N : ℤ) + 1 - 1
      · obtain ⟨e⟩ := hx₃ i hi
        exact (isIsoUnitSingle_congr F e i).mpr (hK i)
      · exact isIsoUnitSingle_of_isZero F (hz₃ i (by omega)) i
    have h1 : IsIso (F.rightDerivedFunctorPlusUnit.app S.X₃) := ih S.X₃ n₀ hS₃ge hS₃le hS₃K
    have hX₁ge : (S.X₁).obj.IsStrictlyGE (n₀ + (N : ℤ) + 1) := by
      rw [CochainComplex.isStrictlyGE_iff]
      intro i hi
      exact hz₁ i (by omega)
    have hX₁le : (S.X₁).obj.IsStrictlyLE (n₀ + (N : ℤ) + 1) := by
      rw [CochainComplex.isStrictlyLE_iff]
      intro i hi
      obtain ⟨e⟩ := hx₁ i (by omega)
      exact (CochainComplex.isZero_of_isStrictlyLE K.obj (n₀ + (N : ℤ) + 1) i hi).of_iso e
    haveI : (S.X₁).obj.IsStrictlyGE (n₀ + (N : ℤ) + 1) := hX₁ge
    haveI : (S.X₁).obj.IsStrictlyLE (n₀ + (N : ℤ) + 1) := hX₁le
    obtain ⟨e₁⟩ := iso_single_of_isStrictlyGE_of_isStrictlyLE (S.X₁).obj (n₀ + (N : ℤ) + 1)
    obtain ⟨e₂⟩ := hx₁ (n₀ + (N : ℤ) + 1) le_rfl
    have h2 : IsIso (F.rightDerivedFunctorPlusUnit.app S.X₁) :=
      (isIso_unit_of_iso F (ObjectProperty.isoMk _ e₁)).mpr
        ((isIsoUnitSingle_congr F e₂ _).mpr (hK _))
    obtain ⟨δ, hδ⟩ := sesTriangle S σ
    let T : Pretriangulated.Triangle (HomotopyCategory.Plus C) :=
      Pretriangulated.Triangle.mk ((HomotopyCategory.Plus.quotient C).map S.f)
        ((HomotopyCategory.Plus.quotient C).map S.g) δ
    obtain ⟨φ, hφ₁, hφ₂, hφ₃⟩ := Work.DSG1.triangleHomOfCommShift F.rightDerivedFunctorPlusUnith T
    have hφ1 : IsIso φ.hom₁ := hφ₁ ▸ (isIso_unit_iff_isIso_unit_h F S.X₁).mp h2
    have hφ3 : IsIso φ.hom₃ := hφ₃ ▸ (isIso_unit_iff_isIso_unit_h F S.X₃).mp h1
    have hmid : IsIso φ.hom₂ :=
      Pretriangulated.isIso₂_of_isIso₁₃ φ
        ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map_distinguished T hδ)
        ((DerivedCategory.Plus.Qh ⋙ F.rightDerivedFunctorPlus).map_distinguished T hδ) hφ1 hφ3
    have hmid' : IsIso (F.rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.quotient C).obj S.X₂)) := hφ₂ ▸ hmid
    rw [hS₂] at hmid'
    exact (isIso_unit_iff_isIso_unit_h F K).mpr hmid'

/-- **The reduction step**: it suffices to know the result in degree `i` for a bounded
truncation. -/
theorem isIso_homology_unit_of_bounded (K : CochainComplex.Plus C) (i : ℤ)
    (hK : ∀ n, IsIsoUnitSingle F (K.obj.X n) n)
    (hbdd : ∀ (M : CochainComplex.Plus C),
      (∃ a b : ℤ, M.obj.IsStrictlyGE a ∧ M.obj.IsStrictlyLE b) →
      (∀ n, IsIsoUnitSingle F (M.obj.X n) n) →
      IsIso (F.rightDerivedFunctorPlusUnit.app M)) :
    IsIso ((DerivedCategory.Plus.homologyFunctor D i).map
      (F.rightDerivedFunctorPlusUnit.app K)) := by
  obtain ⟨S, σ, hS₂, hz₁, hx₁, hz₃, hx₃, hg⟩ := truncSES K (i + 2)
  -- the bounded truncation `S.X₃`
  have hS₃bdd : ∃ a b : ℤ, (S.X₃).obj.IsStrictlyGE a ∧ (S.X₃).obj.IsStrictlyLE b := by
    obtain ⟨a, ha⟩ := K.property
    refine ⟨min a (i + 2), i + 1, ?_, ?_⟩
    · rw [CochainComplex.isStrictlyGE_iff]
      intro j hj
      obtain ⟨e⟩ := hx₃ j (by omega)
      exact (CochainComplex.isZero_of_isStrictlyGE K.obj a j (by omega)).of_iso e
    · rw [CochainComplex.isStrictlyLE_iff]
      intro j hj
      exact hz₃ j (by omega)
  have hS₃K : ∀ n, IsIsoUnitSingle F ((S.X₃).obj.X n) n := by
    intro n
    by_cases hn : n ≤ i + 2 - 1
    · obtain ⟨e⟩ := hx₃ n hn
      exact (isIsoUnitSingle_congr F e n).mpr (hK n)
    · exact isIsoUnitSingle_of_isZero F (hz₃ n (by omega)) n
  have hS₃unit : IsIso (F.rightDerivedFunctorPlusUnit.app S.X₃) := hbdd S.X₃ hS₃bdd hS₃K
  -- the geometric input: the triangle of the short exact sequence
  obtain ⟨δ, hδ⟩ := sesTriangle S σ
  let T : Pretriangulated.Triangle (HomotopyCategory.Plus C) :=
    Pretriangulated.Triangle.mk ((HomotopyCategory.Plus.quotient C).map S.f)
      ((HomotopyCategory.Plus.quotient C).map S.g) δ
  have hT' : (DerivedCategory.Plus.Qh ⋙ F.rightDerivedFunctorPlus).mapTriangle.obj T ∈
      Pretriangulated.distinguishedTriangles :=
    (DerivedCategory.Plus.Qh ⋙ F.rightDerivedFunctorPlus).map_distinguished T hδ
  -- vanishing of the homology of the first object below `i+2`
  have hX₁ge : (S.X₁).obj.IsStrictlyGE (i + 2) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro j hj
    exact hz₁ j hj
  have hgeX₁ : (S.X₁).obj.IsGE (i + 2) := by
    haveI := hX₁ge
    exact isGE_of_isStrictlyGE (S.X₁).obj (i + 2)
  have hzR : ∀ j : ℤ, j < i + 2 → IsZero ((DerivedCategory.Plus.homologyFunctor D j).obj
      ((DerivedCategory.Plus.Qh ⋙ F.rightDerivedFunctorPlus).mapTriangle.obj T).obj₁) := by
    intro j hj
    have h0 := Work.DSG1.isZero_homology_rightDerivedFunctor_plus F S.X₁ (i + 2) j hgeX₁ hj
    exact h0.of_iso ((DerivedCategory.Plus.homologyFunctor D j).mapIso
      (F.rightDerivedFunctorPlus.mapIso ((DerivedCategory.Plus.quotientCompQhIso C).app S.X₁)))
  have hisoT' : IsIso ((DerivedCategory.Plus.homologyFunctor D i).map
      ((DerivedCategory.Plus.Qh ⋙ F.rightDerivedFunctorPlus).mapTriangle.obj T).mor₂) :=
    Work.DSG1.homologyTriangleIso hT' i (hzR i (by omega)) (hzR (i + 1) (by omega))
  -- conjugation with `quotientCompQhIso`
  have hn : (DerivedCategory.Plus.Qh).map ((HomotopyCategory.Plus.quotient C).map S.g)
      ≫ (DerivedCategory.Plus.quotientCompQhIso C).hom.app S.X₃
      = (DerivedCategory.Plus.quotientCompQhIso C).hom.app S.X₂
        ≫ (DerivedCategory.Plus.Q).map S.g :=
    (DerivedCategory.Plus.quotientCompQhIso C).hom.naturality S.g
  have hsquare : (DerivedCategory.Plus.Qh ⋙ F.rightDerivedFunctorPlus).map
        ((HomotopyCategory.Plus.quotient C).map S.g)
      ≫ F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.quotientCompQhIso C).hom.app S.X₃)
      = F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.quotientCompQhIso C).hom.app S.X₂)
        ≫ F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.Q).map S.g) := by
    rw [Functor.comp_map, ← Functor.map_comp, ← Functor.map_comp, hn]
  have htarget : IsIso ((DerivedCategory.Plus.homologyFunctor D i).map
      (F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.Q).map S.g))) := by
    have hsq := congrArg (fun t => (DerivedCategory.Plus.homologyFunctor D i).map t) hsquare
    simp only [Functor.map_comp] at hsq
    exact (isIso_iff_of_iso_conj hsq).mp hisoT'
  -- the source side
  have hsource : IsIso ((DerivedCategory.Plus.homologyFunctor D i).map
      (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map S.g))) := by
    rw [Work.DSG1.isIso_homologyFunctor_Q_map]
    have hι : (CochainComplex.Plus.ι D).map (F.mapCochainComplexPlus.map S.g)
        = (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (S.g).hom := by
      change (F.mapCochainComplexPlus.map S.g).hom = _
      rw [Functor.mapCochainComplexPlus_map_hom]
    rw [hι]
    exact Work.DSG1.isIso_homologyMap_map_of_isIso_f F (S.g).hom i
      (hg (i - 1) (by omega)) (hg i (by omega)) (hg (i + 1) (by omega))
  -- naturality of the unit at `S.g`
  have hnat : (DerivedCategory.Plus.homologyFunctor D i).map
        (F.rightDerivedFunctorPlusUnit.app S.X₂)
      ≫ (DerivedCategory.Plus.homologyFunctor D i).map
        (F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.Q).map S.g))
      = (DerivedCategory.Plus.homologyFunctor D i).map
        (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map S.g))
      ≫ (DerivedCategory.Plus.homologyFunctor D i).map
        (F.rightDerivedFunctorPlusUnit.app S.X₃) := by
    have hn2 := (F.rightDerivedFunctorPlusUnit).naturality S.g
    have h2 := congrArg (fun t => (DerivedCategory.Plus.homologyFunctor D i).map t) hn2
    simp only [Functor.map_comp] at h2
    exact h2.symm
  rw [← hS₂]
  exact (isIso_iff_of_iso_conj hnat).mpr
    (inferInstanceAs (IsIso ((DerivedCategory.Plus.homologyFunctor D i).map
      (F.rightDerivedFunctorPlusUnit.app S.X₃))))

/-- **A bounded below complex of `F`-acyclic objects computes `R⁺F`.**  If every one-term complex
`single_n (K.obj.X n)` satisfies that the unit of the right derived functor of `F` is an
isomorphism, then so does `K`. -/
theorem unitIsoAcyclic (K : CochainComplex.Plus C)
    (hK : ∀ n : ℤ, IsIsoUnitSingle F (K.obj.X n) n) :
    IsIso (F.rightDerivedFunctorPlusUnit.app K) := by
  rw [DerivedCategory.Plus.isIso_iff]
  intro i
  have hbdd : ∀ (M : CochainComplex.Plus C),
      (∃ a b : ℤ, M.obj.IsStrictlyGE a ∧ M.obj.IsStrictlyLE b) →
      (∀ n, IsIsoUnitSingle F (M.obj.X n) n) →
      IsIso (F.rightDerivedFunctorPlusUnit.app M) := by
    intro M hM' hMu
    obtain ⟨a, b, ha, hb⟩ := hM'
    obtain ⟨N, hN⟩ : ∃ N : ℕ, b ≤ a + (N : ℤ) := ⟨(b - a).toNat, by omega⟩
    haveI := ha
    haveI := hb
    have hb' : M.obj.IsStrictlyLE (a + (N : ℤ)) := M.obj.isStrictlyLE_of_le b (a + (N : ℤ)) hN
    exact isIso_unit_of_bounded_aux F N M a ha hb' hMu
  exact isIso_homology_unit_of_bounded F K i (fun n => hK n) hbdd

end Main

end TA

end Work.DSEQ0
