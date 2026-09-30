import Mathlib
import Submission.Work.CurveBasics.BaseChangeFunctionField
import Submission.Work.CurveBasics.BaseChange.isPullback_spec_affine

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option backward.isDefEq.respectTransparency false

namespace Work.CurveBasics.BaseChange

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical
open Work.CurveBasics

universe u

variable {k : Type u} [Field k]

/-- The projection `C_F ⟶ C` is compatible with the canonical maps to the function field. -/
theorem germToFunctionField_baseChangeFst_app (C : Curve k) (F : Type u) [Field F]
    [Algebra k F] (W : C.left.Opens) [Nonempty W] (a : Γ(C.left, W)) :
    ((C.baseChange F).germToFunctionField (C.bcOpens F W)).hom ((C.baseChangeFst F).app W a)
      = (C.functionFieldMap F).hom ((C.germToFunctionField W).hom a) := by
  rw [Curve.functionFieldMap]
  erw [ConcreteCategory.comp_apply]
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply]
  erw [Scheme.Hom.germ_stalkMap_apply]
  rfl

/-- The `F`-algebra structure on the sections of `C_F` over the preimage of an affine open is a
`Γ(C,W)`-scalar tower. -/
theorem isScalarTower_bcOpens (C : Curve k) (F : Type u) [Field F] [Algebra k F]
    (W : C.left.Opens) [Nonempty W] :
    IsScalarTower F Γ((C.baseChange F).left, C.bcOpens F W) (C.baseChange F).functionField := by
  haveI : Nonempty ↑(C.bcOpens F W) := inferInstance
  haveI : Nonempty (⊤ : (C.baseChange F).left.Opens) :=
    ⟨⟨genericPoint (C.baseChange F).left, trivial⟩⟩
  have hgerm : (C.baseChange F).left.presheaf.map
        (homOfLE (le_top : (C.bcOpens F W) ≤ ⊤)).op ≫
        (C.baseChange F).left.germToFunctionField (C.bcOpens F W) =
      (C.baseChange F).left.germToFunctionField (⊤ : (C.baseChange F).left.Opens) :=
    TopCat.Presheaf.germ_res (C.baseChange F).left.presheaf (homOfLE le_top)
      (genericPoint (C.baseChange F).left) _
  have hgerm_apply (y : Γ((C.baseChange F).left, ⊤)) :
      (C.baseChange F).left.germToFunctionField (⊤ : (C.baseChange F).left.Opens) y =
      (C.baseChange F).left.germToFunctionField (C.bcOpens F W)
        ((C.baseChange F).left.presheaf.map
          (homOfLE (le_top : (C.bcOpens F W) ≤ ⊤)).op y) := by
    have h := congrArg (fun (f : Γ((C.baseChange F).left, ⊤) ⟶
        (C.baseChange F).left.functionField) => f y) hgerm
    simpa only [ConcreteCategory.comp_apply] using h.symm
  apply IsScalarTower.of_algebraMap_eq
  intro a
  have htop : (C.baseChange F).hom.appLE ⊤ (C.bcOpens F W)
      (le_top : (C.bcOpens F W) ≤ (C.baseChange F).hom ⁻¹ᵁ ⊤) =
      (C.baseChange F).hom.appTop ≫
        (C.baseChange F).left.presheaf.map
          (homOfLE (le_top : (C.bcOpens F W) ≤ ⊤)).op := rfl
  show (C.baseChange F).left.germToFunctionField (⊤ : (C.baseChange F).left.Opens)
      ((C.baseChange F).hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of F)).inv a)) =
    (C.baseChange F).left.germToFunctionField (C.bcOpens F W)
      ((C.baseChange F).hom.appLE ⊤ (C.bcOpens F W)
        (le_top : (C.bcOpens F W) ≤ (C.baseChange F).hom ⁻¹ᵁ ⊤)
        ((Scheme.ΓSpecIso (CommRingCat.of F)).inv a))
  rw [htop, ConcreteCategory.comp_apply]
  exact hgerm_apply _

/-- The canonical map to the function field sends the constants of `F` to the constants. -/
theorem germToFunctionField_baseChange_algebraMap (C : Curve k) (F : Type u) [Field F]
    [Algebra k F] (W : C.left.Opens) [Nonempty W] (c : F) :
    ((C.baseChange F).germToFunctionField (C.bcOpens F W)).hom
        (algebraMap F Γ((C.baseChange F).left, C.bcOpens F W) c) =
      algebraMap F (C.baseChange F).functionField c := by
  have hst : IsScalarTower F Γ((C.baseChange F).left, C.bcOpens F W)
      (C.baseChange F).functionField := isScalarTower_bcOpens C F W
  haveI := hst
  rw [IsScalarTower.algebraMap_apply F Γ((C.baseChange F).left, C.bcOpens F W)
    (C.baseChange F).functionField c]
  rfl

/-- The image in the function field of `C_F` of the regular functions on an open piece of `C`. -/
noncomputable abbrev rangeGermImage (C : Curve k) (F : Type u) [Field F] [Algebra k F]
    (W : C.left.Opens) [Nonempty W] : Set (C.baseChange F).functionField :=
  (C.functionFieldMap F).hom '' ((C.germToFunctionField W).hom.range : Set C.functionField)

/-- The `F`-span of the image of the regular functions on an open piece of `C`. -/
noncomputable abbrev spanRangeGerm (C : Curve k) (F : Type u) [Field F] [Algebra k F]
    (W : C.left.Opens) [Nonempty W] : Submodule F (C.baseChange F).functionField :=
  Submodule.span F (rangeGermImage C F W)


/-- The sections of `C_F` over the preimage of an affine open `W ⊆ C` are generated as a ring by
the image of the sections of `C` and by the constants. -/
theorem closure_range_union_range_eq_top_bcOpens (C : Curve k) (F : Type u) [Field F]
    [Algebra k F] (W : C.left.Opens) (hW : IsAffineOpen W) :
    Subring.closure (Set.range (((C.baseChangeFst F).app W).hom) ∪
      Set.range (algebraMap F ↑((C.baseChange F).left.presheaf.obj
        (Opposite.op (C.bcOpens F W))))) = ⊤ := by
  have h₁ : CategoryTheory.IsPullback (AlgebraicGeometry.Spec.map ((C.baseChangeFst F).app W))
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap F
        ((C.baseChange F).left.presheaf.obj (Opposite.op (C.bcOpens F W))))))
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k
        (C.left.presheaf.obj (Opposite.op W)))))
      (Curve.specMap k F) := isPullback_spec_affine (C := C) F W hW
  have h₂ : CategoryTheory.IsPullback
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom (R := k)
          (A := ↑(C.left.presheaf.obj (Opposite.op W))) (B := F))))
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        ((Algebra.TensorProduct.includeRight (R := k)
          (A := ↑(C.left.presheaf.obj (Opposite.op W))) (B := F)).toRingHom)))
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k
        (C.left.presheaf.obj (Opposite.op W)))))
      (Curve.specMap k F) :=
    isPullback_SpecMap_of_isPushout
      (CommRingCat.ofHom (algebraMap k (C.left.presheaf.obj (Opposite.op W))))
      (CommRingCat.ofHom (algebraMap k F))
      (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := k)
        (A := ↑(C.left.presheaf.obj (Opposite.op W))) (B := F)))
      (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight (R := k)
        (A := ↑(C.left.presheaf.obj (Opposite.op W))) (B := F)).toRingHom))
      (CommRingCat.isPushout_tensorProduct k ↑(C.left.presheaf.obj (Opposite.op W)) F)
  let u := h₁.isoIsPullback _ _ h₂
  have hfst : u.hom ≫ AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom (R := k)
        (A := ↑(C.left.presheaf.obj (Opposite.op W))) (B := F)))
      = AlgebraicGeometry.Spec.map ((C.baseChangeFst F).app W) := by
    change (h₁.isoIsPullback _ _ h₂).hom ≫ _ = _
    exact IsPullback.isoIsPullback_hom_fst _ _ h₁ h₂
  have hsnd : u.hom ≫ AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      ((Algebra.TensorProduct.includeRight (R := k)
        (A := ↑(C.left.presheaf.obj (Opposite.op W))) (B := F)).toRingHom))
      = AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap F
        ((C.baseChange F).left.presheaf.obj (Opposite.op (C.bcOpens F W))))) := by
    change (h₁.isoIsPullback _ _ h₂).hom ≫ _ = _
    exact IsPullback.isoIsPullback_hom_snd _ _ h₁ h₂
  have keyL : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := k)
      (A := ↑(C.left.presheaf.obj (Opposite.op W))) (B := F)) ≫ Spec.preimage u.hom
      = (C.baseChangeFst F).app W := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, hfst]
  have keyR : CommRingCat.ofHom ((Algebra.TensorProduct.includeRight (R := k)
      (A := ↑(C.left.presheaf.obj (Opposite.op W))) (B := F)).toRingHom) ≫ Spec.preimage u.hom
      = CommRingCat.ofHom (algebraMap F
        ↑((C.baseChange F).left.presheaf.obj (Opposite.op (C.bcOpens F W)))) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, hsnd]
  have hkeyL : ∀ x : ↑(C.left.presheaf.obj (Opposite.op W)),
      (Spec.preimage u.hom).hom ((Algebra.TensorProduct.includeLeftRingHom (R := k)
        (A := ↑(C.left.presheaf.obj (Opposite.op W))) (B := F)) x)
      = ((C.baseChangeFst F).app W).hom x := by
    intro x
    exact congrArg (fun (f : (C.left.presheaf.obj (Opposite.op W)) ⟶
      ((C.baseChange F).left.presheaf.obj (Opposite.op (C.bcOpens F W)))) => f.hom x) keyL
  have hkeyR : ∀ c : F, (Spec.preimage u.hom).hom
      (((Algebra.TensorProduct.includeRight (R := k)
        (A := ↑(C.left.presheaf.obj (Opposite.op W))) (B := F)).toRingHom) c)
      = (algebraMap F ↑((C.baseChange F).left.presheaf.obj
          (Opposite.op (C.bcOpens F W)))) c := by
    intro c
    exact congrArg (fun (f : CommRingCat.of F ⟶ ((C.baseChange F).left.presheaf.obj
      (Opposite.op (C.bcOpens F W)))) => f.hom c) keyR
  let T := Subring.closure (Set.range (((C.baseChangeFst F).app W).hom) ∪
      Set.range (algebraMap F ↑((C.baseChange F).left.presheaf.obj
        (Opposite.op (C.bcOpens F W)))))
  have hsurj : ∀ s : ↑((C.baseChange F).left.presheaf.obj (Opposite.op (C.bcOpens F W))),
      ∃ t, (Spec.preimage u.hom).hom t = s := by
    intro s
    refine ⟨(Spec.preimage u.inv).hom s, ?_⟩
    have h3 : Spec.preimage u.inv ≫ Spec.preimage u.hom = 𝟙 _ := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Iso.hom_inv_id, Spec.map_id]
    exact congrArg (fun (f : ((C.baseChange F).left.presheaf.obj
      (Opposite.op (C.bcOpens F W))) ⟶ ((C.baseChange F).left.presheaf.obj
      (Opposite.op (C.bcOpens F W)))) => f.hom s) h3
  have hmap : ∀ t ∈ Subring.closure (Set.range (Algebra.TensorProduct.includeLeftRingHom
      (R := k) (A := ↑(C.left.presheaf.obj (Opposite.op W))) (B := F)) ∪
      Set.range ((Algebra.TensorProduct.includeRight (R := k)
        (A := ↑(C.left.presheaf.obj (Opposite.op W))) (B := F)).toRingHom)),
      (Spec.preimage u.hom).hom t ∈ T := by
    intro t ht
    induction ht using Subring.closure_induction with
    | mem z hz =>
        rcases hz with ⟨x, rfl⟩ | ⟨c, rfl⟩
        · rw [hkeyL x]; exact Subring.subset_closure (Or.inl ⟨x, rfl⟩)
        · rw [hkeyR c]; exact Subring.subset_closure (Or.inr ⟨c, rfl⟩)
    | zero => rw [map_zero]; exact T.zero_mem'
    | one => rw [map_one]; exact T.one_mem'
    | add p q hp hq ihp ihq => rw [map_add]; exact T.add_mem' ihp ihq
    | neg p hp ihp => rw [map_neg]; exact T.neg_mem' ihp
    | mul p q hp hq ihp ihq => rw [map_mul]; exact T.mul_mem' ihp ihq
  refine le_antisymm le_top ?_
  intro s _
  obtain ⟨t, ht⟩ := hsurj s
  rw [← ht]
  refine hmap t ?_
  rw [show Subring.closure (Set.range (Algebra.TensorProduct.includeLeftRingHom (R := k)
      (A := ↑(C.left.presheaf.obj (Opposite.op W))) (B := F)) ∪
      Set.range ((Algebra.TensorProduct.includeRight (R := k)
        (A := ↑(C.left.presheaf.obj (Opposite.op W))) (B := F)).toRingHom)) = ⊤ from
    Algebra.TensorProduct.closure_range_union_range_eq_top (R := k)
      (A := ↑(C.left.presheaf.obj (Opposite.op W))) (B := F)]
  exact Subring.mem_top t

open Work.CurveBasics in
theorem range_germ_baseChange {k : Type u} [Field k] {C : Curve k} (F : Type u) [Field F]
    [Algebra k F] (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W) [Nonempty W] :
    (((C.baseChange F).germToFunctionField (C.bcOpens F W)).hom.range :
        Set (C.baseChange F).functionField) =
      Submodule.span F ((C.functionFieldMap F).hom ''
        ((C.germToFunctionField W).hom.range : Set C.functionField)) := by
  haveI : Nonempty ↑(C.bcOpens F W) := inferInstance
  change (((C.baseChange F).germToFunctionField (C.bcOpens F W)).hom.range :
      Set (C.baseChange F).functionField) = (spanRangeGerm C F W : Set _)
  refine le_antisymm ?_ ?_
  · -- the range is contained in the `F`-span
    intro x hx
    obtain ⟨s, rfl⟩ := hx
    have hSM : rangeGermImage C F W ⊆ (spanRangeGerm C F W : Set _) :=
      fun y hy => Submodule.subset_span hy
    have hone : (1 : (C.baseChange F).functionField) ∈ spanRangeGerm C F W :=
      hSM ⟨1, ⟨1, map_one _⟩, map_one _⟩
    have hSmul : ∀ y z : (C.baseChange F).functionField,
        y ∈ rangeGermImage C F W → z ∈ rangeGermImage C F W →
        y * z ∈ rangeGermImage C F W := by
      rintro y z ⟨f, ⟨a, rfl⟩, rfl⟩ ⟨g, ⟨b, rfl⟩, rfl⟩
      exact ⟨(C.germToFunctionField W).hom (a * b), ⟨a * b, rfl⟩, by simp only [map_mul]⟩
    have hM_mul : ∀ y z : (C.baseChange F).functionField,
        y ∈ spanRangeGerm C F W → z ∈ spanRangeGerm C F W →
        y * z ∈ spanRangeGerm C F W := by
      intro y z hy hz
      refine Submodule.span_induction (p := fun y _ => y * z ∈ spanRangeGerm C F W)
        ?_ ?_ ?_ ?_ hy
      · intro u hu
        refine Submodule.span_induction (p := fun w _ => u * w ∈ spanRangeGerm C F W)
          ?_ ?_ ?_ ?_ hz
        · intro v hv
          exact Submodule.subset_span (hSmul u v hu hv)
        · rw [mul_zero]; exact Submodule.zero_mem _
        · intro p q hp hq ihp ihq
          rw [mul_add]; exact Submodule.add_mem _ ihp ihq
        · intro c p hp ihp
          rw [mul_smul_comm]; exact Submodule.smul_mem _ c ihp
      · rw [zero_mul]; exact Submodule.zero_mem _
      · intro p q hp hq ihp ihq
        rw [add_mul]; exact Submodule.add_mem _ ihp ihq
      · intro c p hp ihp
        rw [smul_mul_assoc]; exact Submodule.smul_mem _ c ihp
    have hgen_app : ∀ a : Γ(C.left, W),
        ((C.baseChange F).germToFunctionField (C.bcOpens F W)).hom
          ((C.baseChangeFst F).app W a) ∈ spanRangeGerm C F W := by
      intro a
      rw [germToFunctionField_baseChangeFst_app C F W a]
      exact Submodule.subset_span ⟨(C.germToFunctionField W).hom a, ⟨a, rfl⟩, rfl⟩
    have hgen_const : ∀ c : F,
        ((C.baseChange F).germToFunctionField (C.bcOpens F W)).hom
          (algebraMap F Γ((C.baseChange F).left, C.bcOpens F W) c) ∈ spanRangeGerm C F W := by
      intro c
      rw [germToFunctionField_baseChange_algebraMap C F W c]
      have hs : algebraMap F (C.baseChange F).functionField c
          = c • (1 : (C.baseChange F).functionField) := by
        rw [Algebra.smul_def, mul_one]
      rw [hs]
      exact Submodule.smul_mem _ c hone
    have hgen_top : Subring.closure (Set.range (((C.baseChangeFst F).app W).hom) ∪
        Set.range (algebraMap F Γ((C.baseChange F).left, C.bcOpens F W))) = ⊤ :=
      closure_range_union_range_eq_top_bcOpens C F W hW
    have hfin : ∀ y ∈ Subring.closure (Set.range (((C.baseChangeFst F).app W).hom) ∪
        Set.range (algebraMap F Γ((C.baseChange F).left, C.bcOpens F W))),
        ((C.baseChange F).germToFunctionField (C.bcOpens F W)).hom y ∈ spanRangeGerm C F W := by
      intro y hy
      induction hy using Subring.closure_induction with
      | mem z hz =>
          rcases hz with ⟨a, rfl⟩ | ⟨c, rfl⟩
          · exact hgen_app a
          · exact hgen_const c
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | one => rw [map_one]; exact hone
      | add p q hp hq ihp ihq => rw [map_add]; exact Submodule.add_mem _ ihp ihq
      | neg p hp ihp => rw [map_neg]; exact Submodule.neg_mem _ ihp
      | mul p q hp hq ihp ihq => rw [map_mul]; exact hM_mul _ _ ihp ihq
    have hs' : ((C.baseChange F).germToFunctionField (C.bcOpens F W)).hom s
        ∈ spanRangeGerm C F W := by
      apply hfin
      rw [hgen_top]
      exact Subring.mem_top s
    exact hs'
  · -- the `F`-span is contained in the range
    intro x hx
    refine Submodule.span_induction (p := fun x _ =>
      x ∈ (((C.baseChange F).germToFunctionField (C.bcOpens F W)).hom.range :
        Set (C.baseChange F).functionField)) ?_ ?_ ?_ ?_ hx
    · rintro y ⟨f, ⟨a, rfl⟩, rfl⟩
      exact ⟨(C.baseChangeFst F).app W a, germToFunctionField_baseChangeFst_app C F W a⟩
    · exact ⟨0, by simp⟩
    · intro y z hy hz ihy ihz
      obtain ⟨s, hs⟩ := ihy
      obtain ⟨t, ht⟩ := ihz
      exact ⟨s + t, by rw [map_add, hs, ht]⟩
    · intro c y hy ihy
      obtain ⟨s, hs⟩ := ihy
      exact ⟨algebraMap F Γ((C.baseChange F).left, C.bcOpens F W) c * s,
        by rw [map_mul, hs, germToFunctionField_baseChange_algebraMap C F W c, Algebra.smul_def]⟩

end Work.CurveBasics.BaseChange
