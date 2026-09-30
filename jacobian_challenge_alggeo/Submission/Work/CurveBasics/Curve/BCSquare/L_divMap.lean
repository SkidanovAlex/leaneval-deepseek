import Mathlib
import Submission.Work.CurveBasics.BCSquare
import Submission.Work.CurveBasics.Linear
import Submission.Work.CurveBasics.BaseChange.divMap_div
import Submission.Work.CurveBasics.BaseChange.mem_range_germ_iff
import Submission.Work.CurveBasics.BaseChange.range_germ_baseChange
import Submission.Work.CurveBasics.Curve.exists_affine_principal
import Submission.Work.CurveBasics.Curve.L_eq_iInter_mul_range
import Submission.Work.CurveBasics.Curve.BCSquare.GermNaturality
import Submission.Work.CurveBasics.Curve.BCSquare.algebraMap_functionFieldMapIso
import Submission.Work.CurveBasics.Curve.BCSquare.fieldMapTensor
import Submission.Work.CurveBasics.Curve.BCSquare.tensorLift_injective
import Submission.Work.CurveBasics.Curve.BCSquare.fieldMap_injective
import Submission.Work.CurveBasics.Curve.BCSquare.ordAt_fieldMap

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct Classical

set_option maxHeartbeats 1000000


namespace Work.CurveBasics.Curve.BCSquare

section
universe u


variable {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]
variable {C : Curve k} {C' : Curve F}

noncomputable section

open scoped TensorProduct

theorem span_iInf_tmul_one {k F V W : Type u} [Field k] [Field F] [Algebra k F]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module F W]
    {ι : Type u} [Nonempty ι]
    (Φ : F ⊗[k] V →ₗ[F] W) (hΦ : Function.Injective Φ) (φ : V → W)
    (hφ : ∀ (c : F) (v : V), Φ (c ⊗ₜ[k] v) = c • φ v)
    (M : ι → Submodule k V) :
    Submodule.span F (φ '' ↑(⨅ i, M i)) = ⨅ i, Submodule.span F (φ '' ↑(M i)) := by
  classical
  haveI hfree : Module.Free k F := Module.Free.of_divisionRing k F
  obtain ⟨B, b⟩ := Module.Free.exists_basis k F
  haveI : DecidableEq B := Classical.decEq B
  let e : F ⊗[k] V ≃ₗ[k] (B →₀ V) := TensorProduct.equivFinsuppOfBasisLeft b
  have he_symm_single : ∀ (a : B) (m : V),
      e.symm (Finsupp.single a m) = b a ⊗ₜ[k] m := by
    intro a m
    show (TensorProduct.equivFinsuppOfBasisLeft b).symm (Finsupp.single a m) = _
    rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply]
    exact Finsupp.sum_single_index (by simp)
  -- Step 1: the coordinate of the transported scalar action
  have hstep : ∀ (M : Submodule k V) (y : B →₀ V), (∀ β, y β ∈ M) → ∀ (c : F) (β : B),
      (e (c • (e.symm y))) β ∈ M := by
    intro M y
    refine Finsupp.induction
      (motive := fun y => (∀ β, y β ∈ M) → ∀ (c : F) (β : B), (e (c • (e.symm y))) β ∈ M)
      y ?_ ?_
    · intro _ c β
      rw [LinearEquiv.map_zero, smul_zero, map_zero, Finsupp.zero_apply]
      exact Submodule.zero_mem _
    · intro a m f ham hm ih hy c β
      have hmM : m ∈ M := by
        have h1 := hy a
        rw [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.notMem_support_iff.mp ham,
          add_zero] at h1
        exact h1
      have hfM : ∀ β, f β ∈ M := by
        intro β
        by_cases hβ : β = a
        · subst hβ
          rw [Finsupp.notMem_support_iff.mp ham]
          exact Submodule.zero_mem _
        · have h1 := hy β
          rwa [Finsupp.add_apply, Finsupp.single_eq_of_ne hβ, zero_add] at h1
      rw [map_add, smul_add, map_add, Finsupp.add_apply]
      refine Submodule.add_mem _ ?_ (ih hfM c β)
      rw [he_symm_single a m, TensorProduct.smul_tmul', smul_eq_mul,
        TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
      exact Submodule.smul_mem _ ((b.repr (c * b a)) β) hmM
  -- Step 2: the characterisation
  have key : ∀ (M : Submodule k V) (u : F ⊗[k] V),
      Φ u ∈ Submodule.span F (φ '' ↑M) ↔ ∀ β, (e u) β ∈ M := by
    intro M u
    have hsub : Submodule.span F (φ '' ↑M) ≤ LinearMap.range Φ := by
      rw [Submodule.span_le]
      rintro z ⟨v, -, rfl⟩
      exact ⟨1 ⊗ₜ[k] v, by rw [hφ 1 v, one_smul]⟩
    constructor
    · intro hzu
      refine Submodule.span_induction
        (p := fun z _ => ∀ u, Φ u = z → ∀ β, (e u) β ∈ M) ?_ ?_ ?_ ?_ hzu u rfl
      · rintro v ⟨v₀, hv₀, rfl⟩ u hu β
        have h1 : u = 1 ⊗ₜ[k] v₀ := hΦ (by rw [hu, hφ 1 v₀, one_smul])
        rw [h1, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
        exact Submodule.smul_mem _ ((b.repr 1) β) hv₀
      · intro u hu β
        have h1 : u = 0 := hΦ (by rw [hu, map_zero])
        rw [h1, map_zero, Finsupp.zero_apply]
        exact Submodule.zero_mem _
      · intro z₁ z₂ hz₁ hz₂ ih₁ ih₂ u hu β
        obtain ⟨u₁, hu₁⟩ := hsub hz₁
        have hu₂ : Φ (u - u₁) = z₂ := by rw [map_sub, hu, hu₁, add_sub_cancel_left]
        rw [show u = u₁ + (u - u₁) from (add_sub_cancel u₁ u).symm, map_add, Finsupp.add_apply]
        exact Submodule.add_mem _ (ih₁ u₁ hu₁ β) (ih₂ (u - u₁) hu₂ β)
      · intro c z₁ hz₁ ih u hu β
        obtain ⟨u₁, hu₁⟩ := hsub hz₁
        have hu' : u = c • u₁ := hΦ (by rw [hu, map_smul, hu₁])
        rw [hu']
        simpa only [LinearEquiv.symm_apply_apply] using
          hstep M (e u₁) (fun β' => ih u₁ hu₁ β') c β
    · intro hy
      have h1 : Φ (e.symm (e u)) ∈ Submodule.span F (φ '' ↑M) := by
        refine Finsupp.induction
          (motive := fun y => (∀ β, y β ∈ M) →
            Φ (e.symm y) ∈ Submodule.span F (φ '' ↑M)) (e u) ?_ ?_ hy
        · intro _
          rw [LinearEquiv.map_zero, map_zero]
          exact Submodule.zero_mem _
        · intro a m f ham hm ihm hy'
          have hmM : m ∈ M := by
            have h2 := hy' a
            rw [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.notMem_support_iff.mp ham,
              add_zero] at h2
            exact h2
          have hfM : ∀ β, f β ∈ M := by
            intro β
            by_cases hβ : β = a
            · subst hβ
              rw [Finsupp.notMem_support_iff.mp ham]
              exact Submodule.zero_mem _
            · have h2 := hy' β
              rwa [Finsupp.add_apply, Finsupp.single_eq_of_ne hβ, zero_add] at h2
          rw [map_add, map_add]
          refine Submodule.add_mem _ ?_ (ihm hfM)
          rw [he_symm_single a m, hφ]
          exact Submodule.smul_mem _ (b a)
            (Submodule.subset_span ⟨m, hmM, rfl⟩)
      simpa only [LinearEquiv.symm_apply_apply] using h1
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro z ⟨v, hv, rfl⟩
    change φ v ∈ ⨅ i, Submodule.span F (φ '' ↑(M i))
    rw [Submodule.mem_iInf]
    intro i
    refine Submodule.subset_span ⟨v, ?_, rfl⟩
    exact (Submodule.mem_iInf M).mp hv i
  · intro z hz
    change z ∈ ⨅ i, Submodule.span F (φ '' ↑(M i)) at hz
    rw [Submodule.mem_iInf] at hz
    haveI hne : Nonempty ι := ‹Nonempty ι›
    obtain ⟨i₀⟩ := hne
    have hzr : z ∈ LinearMap.range Φ := by
      refine (Submodule.span_le.mpr ?_) (hz i₀)
      rintro z ⟨v, -, rfl⟩
      exact ⟨1 ⊗ₜ[k] v, by rw [hφ 1 v, one_smul]⟩
    obtain ⟨u, hu⟩ := hzr
    rw [← hu]
    refine (key (⨅ i, M i) u).mpr ?_
    intro β
    rw [Submodule.mem_iInf]
    intro i
    exact (key (M i) u).mp (by rw [hu]; exact hz i) β

/-! ## Local facts about the field map of a base-change square

These are the facts about `S.fieldMap` needed below, stated with names local to this file so
that the file is independent of the two variants of `fieldMap_germToFunctionField` present in
the repository. -/

/-- **The field map on germs.** -/
private theorem bc_fieldMap_germToFunctionField (S : BCSquare C C') (W : C.left.Opens) [Nonempty W]
    [Nonempty (S.preimage W)] (a : Γ(C.left, W)) :
    S.fieldMap.hom ((C.germToFunctionField W).hom a) =
      (C'.germToFunctionField (S.preimage W)).hom ((S.π.app W).hom a) := by
  have h : C.germToFunctionField W ≫ S.fieldMap
      = S.π.app W ≫ C'.germToFunctionField (S.preimage W) := by
    rw [Curve.BCSquare.fieldMap, ← Category.assoc, TopCat.Presheaf.germ_stalkSpecializes,
      Scheme.Hom.germ_stalkMap]
  simpa only [ConcreteCategory.comp_apply] using ConcreteCategory.congr_hom h a

/-- **The field map is compatible with the local rings.** -/
private theorem bc_fieldMap_algebraMap_stalk (S : BCSquare C C') (z : C'.left)
    (a : C.left.presheaf.stalk (S.π z)) :
    S.fieldMap.hom (algebraMap (C.left.presheaf.stalk (S.π z)) C.functionField a) =
      algebraMap (C'.left.presheaf.stalk z) C'.functionField (S.π.stalkMap z a) := by
  obtain ⟨U, hU, s, hs⟩ := C.left.presheaf.exists_germ_eq a
  rw [← hs]
  haveI : Nonempty U := ⟨⟨_, hU⟩⟩
  haveI : Nonempty (S.preimage U) := ⟨⟨z, hU⟩⟩
  rw [Scheme.algebraMap_germ_eq_germToFunctionField C.left hU s]
  erw [Scheme.Hom.germ_stalkMap_apply]
  erw [Scheme.algebraMap_germ_eq_germToFunctionField C'.left (U := S.preimage U) hU
    (S.π.app U s)]
  exact bc_fieldMap_germToFunctionField S U s

/-- **Regularity transfer.** -/
private theorem bc_ordAt_fieldMap_nonneg_of_mem_range (S : BCSquare C C') (Q' : C'.Place)
    {g : C.functionField}
    (hg : g ∈ (algebraMap (C.left.presheaf.stalk (S.π Q'.point)) C.functionField).range) :
    0 ≤ C'.ordAt (S.fieldMap.hom g) Q' := by
  obtain ⟨a, rfl⟩ := hg
  rw [bc_fieldMap_algebraMap_stalk S Q'.point a]
  exact (BaseChange.mem_range_algebraMap_stalk_iff C' Q' _).mp
    ⟨S.π.stalkMap Q'.point a, rfl⟩

/-- **Order over the generic point.**  If the image of a place of `C'` is the generic point of
`C`, the field map preserves orders, which are then zero. -/
private theorem bc_ordAt_fieldMap_of_not_isClosed (S : Curve.BCSquare C C')
    (Q' : Curve.Place C') (h : ¬ IsClosed ({S.π Q'.point} : Set C.left))
    {f : C.functionField} (hf : f ≠ 0) : C'.ordAt (S.fieldMap.hom f) Q' = 0 := by
  have hgen : S.π Q'.point = genericPoint C.left := by
    rcases C.eq_genericPoint_or_isClosed (S.π Q'.point) with hgen | hcl
    · exact hgen
    · exact absurd hcl h
  have hmem : f ∈ (algebraMap (C.left.presheaf.stalk (S.π Q'.point)) C.functionField).range :=
    BaseChange.mem_range_algebraMap_genericPoint hgen f
  have hmem' : f⁻¹ ∈
      (algebraMap (C.left.presheaf.stalk (S.π Q'.point)) C.functionField).range :=
    BaseChange.mem_range_algebraMap_genericPoint hgen f⁻¹
  have h1 : 0 ≤ C'.ordAt (S.fieldMap.hom f) Q' :=
    bc_ordAt_fieldMap_nonneg_of_mem_range S Q' hmem
  have h2 : 0 ≤ C'.ordAt (S.fieldMap.hom f⁻¹) Q' :=
    bc_ordAt_fieldMap_nonneg_of_mem_range S Q' hmem'
  have hne : S.fieldMap.hom f ≠ 0 := by
    intro h0
    have hone : S.fieldMap.hom f⁻¹ * S.fieldMap.hom f = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hf, map_one]
    rw [h0, mul_zero] at hone
    exact one_ne_zero hone.symm
  have h3 : C'.ordAt (S.fieldMap.hom f⁻¹) Q' = -C'.ordAt (S.fieldMap.hom f) Q' := by
    rw [map_inv₀]
    exact Curve.ordAt_inv C' hne Q'
  linarith

/-- The germ of a section at the generic point is independent of the proof of membership. -/
private theorem bc_germ_genericPoint_eq_germToFunctionField {X : Scheme.{u}} [IrreducibleSpace X]
    (U : X.Opens) [Nonempty U] (hU : genericPoint X ∈ U) (s : Γ(X, U)) :
    X.presheaf.germ U (genericPoint X) hU s = X.germToFunctionField U s := by
  simp only [Scheme.germToFunctionField]

/-- Two equal morphisms induce the same map on the germ at the generic point. -/
private theorem bc_germToFunctionField_congr_hom {X Y : Scheme.{u}} [IrreducibleSpace X] {k l : X ⟶ Y}
    (hk : k = l) (U : Y.Opens) [Nonempty (k ⁻¹ᵁ U)] [Nonempty (l ⁻¹ᵁ U)] (s : Γ(Y, U)) :
    X.germToFunctionField (k ⁻¹ᵁ U) (k.app U s) = X.germToFunctionField (l ⁻¹ᵁ U) (l.app U s) := by
  cases hk
  congr 1

/-- The field map of a base-change square is the base-change map composed with the
identification of the square with the tautological square. -/
private theorem bc_fieldMap_eq_functionFieldMapIso_apply (S : Curve.BCSquare C C')
    (x : C.functionField) :
    (functionFieldMapIso (isoBaseChange S)).hom ((C.functionFieldMap F).hom x)
      = S.fieldMap.hom x := by
  obtain ⟨U, hU, s, hs⟩ := C.left.presheaf.exists_germ_eq x
  haveI hUne : Nonempty U := ⟨⟨genericPoint C.left, hU⟩⟩
  have hgerm : C.left.presheaf.germ U (genericPoint C.left) hU s = C.germToFunctionField U s :=
    bc_germ_genericPoint_eq_germToFunctionField U hU s
  haveI hbc : Nonempty (C.bcOpens F U) := inferInstance
  haveI hpre : Nonempty ((isoBaseChange S).hom ⁻¹ᵁ (C.bcOpens F U)) :=
    nonempty_preimage_of_genericPoint (isoBaseChange S).hom (iso_genericPoint (isoBaseChange S))
      (C.bcOpens F U)
  haveI hSπ : Nonempty (S.π ⁻¹ᵁ U) := inferInstance
  haveI hcomp : Nonempty (((isoBaseChange S).hom ≫ Curve.baseChangeFst C F) ⁻¹ᵁ U) := hpre
  rw [← hs, hgerm, ← BaseChange.germToFunctionField_baseChangeFst_app C F U s,
    functionFieldMapIso_germToFunctionField (isoBaseChange S) (C.bcOpens F U)
      ((C.baseChangeFst F).app U s),
    bc_fieldMap_germToFunctionField S U s]
  exact bc_germToFunctionField_congr_hom (isoBaseChange_hom_fst S) U s

/-- **The regular functions on the preimage of an affine open are generated over `F` by the
images of the regular functions on the affine open** (G5). -/
private theorem bc_range_germ_baseChange (S : Curve.BCSquare C C') (W : C.left.Opens)
    (hW : AlgebraicGeometry.IsAffineOpen W) [Nonempty W] :
    ((C'.germToFunctionField (S.preimage W)).hom.range : Set C'.functionField) =
      Submodule.span F (S.fieldMap.hom '' ((C.germToFunctionField W).hom.range : Set C.functionField)) := by
  haveI hneW : Nonempty (S.preimage W) := inferInstance
  have hT := BaseChange.range_germ_baseChange F W hW
  have hπ : (isoBaseChange S).hom ≫ Curve.baseChangeFst C F = S.π := isoBaseChange_hom_fst S
  have hgen : (isoBaseChange S).hom (genericPoint C'.left) =
      genericPoint (C.baseChange F).left := iso_genericPoint (isoBaseChange S)
  haveI hneV : Nonempty (Curve.bcOpens C F W) := inferInstance
  haveI hneV' : Nonempty ((isoBaseChange S).hom ⁻¹ᵁ Curve.bcOpens C F W) :=
    nonempty_preimage_of_genericPoint (isoBaseChange S).hom hgen (Curve.bcOpens C F W)
  have hfieldMap : ∀ x : C.functionField,
      (functionFieldMapIso (isoBaseChange S)).hom ((C.functionFieldMap F).hom x) =
        S.fieldMap.hom x :=
    fun x => bc_fieldMap_eq_functionFieldMapIso_apply S x
  have halg : ∀ c : F,
      (functionFieldMapIso (isoBaseChange S)).hom
          (algebraMap F (C.baseChange F).functionField c) =
        algebraMap F C'.functionField c :=
    fun c => algebraMap_functionFieldMapIso S c
  let Φlin : (C.baseChange F).functionField →ₗ[F] C'.functionField :=
    { toFun := (functionFieldMapIso (isoBaseChange S)).hom
      map_add' := fun x y => map_add _ x y
      map_smul' := fun c x => by
        show (functionFieldMapIso (isoBaseChange S)).hom (c • x) =
          c • (functionFieldMapIso (isoBaseChange S)).hom x
        rw [Algebra.smul_def, map_mul, halg c, ← Algebra.smul_def] }
  have hV : (isoBaseChange S).hom ⁻¹ᵁ (Curve.bcOpens C F W) = S.preimage W := by
    rw [Curve.bcOpens, Curve.BCSquare.preimage, ← hπ]
    rfl
  have hH4 := functionFieldMapIso_image_range (isoBaseChange S) (Curve.bcOpens C F W)
  have himg : Φlin '' ((C.functionFieldMap F).hom ''
        ((C.germToFunctionField W).hom.range : Set C.functionField)) =
      S.fieldMap.hom '' ((C.germToFunctionField W).hom.range : Set C.functionField) := by
    ext x
    constructor
    · rintro ⟨y, ⟨f, ⟨a, rfl⟩, rfl⟩, rfl⟩
      exact ⟨(C.germToFunctionField W).hom a, ⟨a, rfl⟩, (hfieldMap _).symm⟩
    · rintro ⟨f, ⟨a, rfl⟩, rfl⟩
      exact ⟨(C.functionFieldMap F).hom ((C.germToFunctionField W).hom a),
        ⟨_, ⟨a, rfl⟩, rfl⟩, hfieldMap _⟩
  have hrange := range_germToFunctionField_congr (X := C'.left) hV
  rw [← hrange, ← hH4, hT]
  change (⇑Φlin '' ↑(Submodule.span F ((C.functionFieldMap F).hom ''
      ((C.germToFunctionField W).hom.range : Set C.functionField))) : Set C'.functionField) =
    ↑(Submodule.span F (S.fieldMap.hom ''
      ((C.germToFunctionField W).hom.range : Set C.functionField)))
  rw [← Submodule.map_coe (f := Φlin), ← Submodule.span_image (f := Φlin), himg]


/-- The constants are regular on every nonempty open set. -/
private theorem algebraMap_mem_germ_range (C : Curve k) (W : C.left.Opens) [Nonempty W] (c : k) :
    algebraMap k C.functionField c ∈ (C.germToFunctionField W).hom.range :=
  ⟨algebraMap k Γ(C.left, W) c, germToFunctionField_algebraMap C W c⟩

/-- The image of the germ map to the function field, as a submodule. -/
private def germRange (C : Curve k) (W : C.left.Opens) [Nonempty W] : Submodule k C.functionField :=
  { carrier := (C.germToFunctionField W).hom.range
    zero_mem' := (C.germToFunctionField W).hom.range.zero_mem
    add_mem' := fun ha hb => (C.germToFunctionField W).hom.range.add_mem ha hb
    smul_mem' := by
      intro c x hx
      rw [Algebra.smul_def]
      exact (C.germToFunctionField W).hom.range.mul_mem
        (algebraMap_mem_germ_range C W c) hx }

/-- `t` times the functions regular on `U`. -/
private def subM (C : Curve k) (U : C.left.Opens) (hU : Nonempty U) (t : C.functionField) :
    Submodule k C.functionField := by
  haveI := hU
  exact Submodule.map (LinearMap.mulLeft k t) (germRange C U)

private theorem mem_subM (C : Curve k) (U : C.left.Opens) (hU : Nonempty U) (t : C.functionField)
    (f : C.functionField) :
    f ∈ subM C U hU t ↔ ∃ g ∈ (C.germToFunctionField U).hom.range, f = t * g := by
  haveI := hU
  show f ∈ Submodule.map (LinearMap.mulLeft k t) (germRange C U) ↔ _
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨g, hg, hgf⟩
    refine ⟨g, hg, ?_⟩
    rw [← hgf, LinearMap.mulLeft_apply]
  · rintro ⟨g, hg, hfg⟩
    refine ⟨g, hg, ?_⟩
    rw [LinearMap.mulLeft_apply, hfg]

/-- The index type of pairs `(W, t)` realising `-D` on an affine open `W`. -/
private def G2Idx (C : Curve k) (D : Curve.Div C) : Type u :=
  {p : C.left.Opens × C.functionField //
    IsAffineOpen p.1 ∧ Nonempty p.1 ∧ p.2 ≠ 0 ∧
      ∀ Q : Curve.Place C, Q.point ∈ p.1 → C.ordAt p.2 Q = -D Q}

end

end

open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry in
universe u in
theorem L_divMap {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]
    {C : Curve k} {C' : Curve F} (S : Curve.BCSquare C C') (D : Curve.Div C) :
    C'.L (S.divMap D) = Submodule.span F (S.fieldMap.hom '' ↑(C.L D)) := by
  classical
  let ι := G2Idx C D
  let U : ι → C.left.Opens := fun p => p.1.1
  let t : ι → C.functionField := fun p => p.1.2
  have hU : ∀ p, IsAffineOpen (U p) := fun p => p.2.1
  have hUne : ∀ p, Nonempty (U p) := fun p => p.2.2.1
  have ht : ∀ p, t p ≠ 0 := fun p => p.2.2.2.1
  have htord : ∀ p, ∀ Q : C.Place, Q.point ∈ U p → C.ordAt (t p) Q = -D Q :=
    fun p => p.2.2.2.2
  have hcov : ∀ z : C.left, ∃ p, z ∈ U p := by
    intro z
    obtain ⟨W, t0, hW, hz, ht0, htord0⟩ := exists_affine_principal D z
    exact ⟨⟨(W, t0), hW, ⟨⟨z, hz⟩⟩, ht0, htord0⟩, hz⟩
  haveI hneι : Nonempty ι := by
    obtain ⟨W, t0, hW, hz, ht0, htord0⟩ := exists_affine_principal D (genericPoint C.left)
    exact ⟨⟨(W, t0), hW, ⟨⟨genericPoint C.left, hz⟩⟩, ht0, htord0⟩⟩
  have hL := L_eq_iInter_mul_range D U hU hUne hcov t ht htord
  have hM : (C.L D : Submodule k C.functionField) = ⨅ p, subM C (U p) (hUne p) (t p) := by
    apply SetLike.ext
    intro f
    rw [← SetLike.mem_coe, hL, Set.mem_iInter, Submodule.mem_iInf]
    exact forall_congr' (fun p => (mem_subM C (U p) (hUne p) (t p) f).symm)
  let U' : ι → C'.left.Opens := fun p => S.preimage (U p)
  let t' : ι → C'.functionField := fun p => S.fieldMap.hom (t p)
  have hU' : ∀ p, IsAffineOpen (U' p) := fun p => isAffineOpen_preimage S (U p) (hU p)
  have hUne' : ∀ p, Nonempty (U' p) := by
    intro p
    haveI := hUne p
    show Nonempty (S.preimage (U p))
    exact inferInstance
  have hcov' : ∀ z' : C'.left, ∃ p, z' ∈ U' p := by
    intro z'
    obtain ⟨p, hp⟩ := hcov (S.π z')
    exact ⟨p, hp⟩
  have ht' : ∀ p, t' p ≠ 0 := by
    intro p h0
    refine ht p (fieldMap_injective S ?_)
    rw [map_zero]
    exact h0
  have htord' : ∀ p, ∀ Q' : C'.Place, Q'.point ∈ U' p →
      C'.ordAt (t' p) Q' = -(S.divMap D) Q' := by
    intro p Q' hQ'
    by_cases hcl : IsClosed ({S.π Q'.point} : Set C.left)
    · have hcoeff : (S.divMap D) Q' = D (S.under Q' hcl) * S.ramIdx Q' := by
        rw [divMap_apply, divMapCoeff, dite_eq_left hcl]
      have h1 : C'.ordAt (S.fieldMap.hom (t p)) Q' =
          S.ramIdx Q' * C.ordAt (t p) (S.under Q' hcl) :=
        ordAt_fieldMap S Q' hcl (ht p)
      have h2 : C.ordAt (t p) (S.under Q' hcl) = -D (S.under Q' hcl) := htord p _ hQ'
      rw [show t' p = S.fieldMap.hom (t p) from rfl, h1, h2, hcoeff]
      ring
    · have hcoeff : (S.divMap D) Q' = 0 := by
        rw [divMap_apply, divMapCoeff, dite_eq_right hcl]
      have h1 : C'.ordAt (S.fieldMap.hom (t p)) Q' = 0 :=
        bc_ordAt_fieldMap_of_not_isClosed S Q' hcl (ht p)
      rw [show t' p = S.fieldMap.hom (t p) from rfl, h1, hcoeff]
      ring
  have hL' := L_eq_iInter_mul_range (k := F) (C := C') (S.divMap D) U' hU' hUne' hcov' t' ht' htord'
  have hM' : (C'.L (S.divMap D) : Submodule F C'.functionField) =
      ⨅ p, subM C' (U' p) (hUne' p) (t' p) := by
    apply SetLike.ext
    intro f
    rw [← SetLike.mem_coe, hL', Set.mem_iInter, Submodule.mem_iInf]
    exact forall_congr' (fun p => (mem_subM C' (U' p) (hUne' p) (t' p) f).symm)
  have hmemM' : ∀ p, germRange C' (U' p) =
      Submodule.span F (S.fieldMap.hom '' ↑(germRange C (U p))) := by
    intro p
    haveI := hUne p
    haveI := hUne' p
    apply SetLike.ext
    intro x
    exact (Set.ext_iff.mp (bc_range_germ_baseChange S (U p) (hU p))) x
  have hB : ∀ p, Submodule.span F (S.fieldMap.hom '' ↑(subM C (U p) (hUne p) (t p))) =
      subM C' (U' p) (hUne' p) (t' p) := by
    intro p
    haveI := hUne p
    haveI := hUne' p
    have hset : S.fieldMap.hom '' ↑(subM C (U p) (hUne p) (t p)) =
        (LinearMap.mulLeft F (S.fieldMap.hom (t p))) ''
          (S.fieldMap.hom '' ↑(germRange C (U p))) := by
      show S.fieldMap.hom ''
        ↑(Submodule.map (LinearMap.mulLeft k (t p)) (germRange C (U p))) = _
      rw [Submodule.map_coe]
      ext x
      constructor
      · rintro ⟨y, hy, hxy⟩
        have hy' : y ∈ Submodule.map (LinearMap.mulLeft k (t p)) (germRange C (U p)) := hy
        obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.mp hy'
        exact ⟨S.fieldMap.hom z, ⟨z, hz, rfl⟩, by
          rw [LinearMap.mulLeft_apply, ← hxy, ← hzy, LinearMap.mulLeft_apply, map_mul]⟩
      · rintro ⟨w, ⟨z, hz, rfl⟩, hwz⟩
        exact ⟨(LinearMap.mulLeft k (t p)) z, ⟨z, hz, rfl⟩, by
          rw [← hwz, LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, map_mul]⟩
    rw [hset, ← Submodule.map_span]
    show Submodule.map (LinearMap.mulLeft F (S.fieldMap.hom (t p)))
        (Submodule.span F (S.fieldMap.hom '' ↑(germRange C (U p)))) =
      Submodule.map (LinearMap.mulLeft F (S.fieldMap.hom (t p))) (germRange C' (U' p))
    rw [hmemM' p]
  let Φ : (F ⊗[k] C.functionField) →ₗ[F] C'.functionField :=
    { toFun := ⇑(tensorLift S)
      map_add' := fun x y => map_add (tensorLift S) x y
      map_smul' := fun c x => tensorLift_smul S c x }
  have hΦ : Function.Injective Φ := tensorLift_injective S
  have hφ : ∀ (c : F) (v : C.functionField), Φ (c ⊗ₜ[k] v) = c • S.fieldMap.hom v := by
    intro c v
    show tensorLift S (c ⊗ₜ[k] v) = c • S.fieldMap.hom v
    rw [tensorLift_tmul, Algebra.smul_def]
  calc C'.L (S.divMap D)
      = ⨅ p, subM C' (U' p) (hUne' p) (t' p) := hM'
    _ = ⨅ p, Submodule.span F (S.fieldMap.hom '' ↑(subM C (U p) (hUne p) (t p))) :=
          iInf_congr (fun p => (hB p).symm)
    _ = Submodule.span F (S.fieldMap.hom '' ↑(⨅ p, subM C (U p) (hUne p) (t p))) :=
          (span_iInf_tmul_one Φ hΦ S.fieldMap.hom hφ
            (fun p => subM C (U p) (hUne p) (t p))).symm
    _ = Submodule.span F (S.fieldMap.hom '' ↑(C.L D)) := by rw [hM]

end Work.CurveBasics.Curve.BCSquare

