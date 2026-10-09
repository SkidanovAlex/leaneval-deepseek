import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.ExtOneAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The cokernel description of `Ext¹`, explicitly and naturally

For a short exact complex `S : 0 → X₁ → X₂ → X₃ → 0` in an abelian category `C` with a projective
middle term `X₂`, the long exact sequence of `Ext(-,Y)` gives

`Ext¹(X₃,Y) ≅ Ext⁰(X₁,Y) / im(Ext⁰(X₂,Y) → Ext⁰(X₁,Y))`,

`Work.SSGRoute.ext_coker_LES` (in `ExtOneAux.lean`) states this as a `Nonempty`.  For the
naturality of the dictionary `Ext¹_G(M,N) ≅ Ext¹_G(ℤ, Hom_ℤ(M,N))` in the first variable `M` we
need the *explicit* equivalence, together with

* its computation rule on classes in the image of the connecting map
  (`extCokerEquiv_extClass`), which is what identifies the two routes around a naturality square;
* the fact that the connecting map is surjective (`extConn_surjective`), so that the computation
  rule determines the equivalence;
* the naturality statement itself (`extCokerEquiv_natural`), in the form that a morphism of short
  exact complexes `f : S₁ ⟶ S₂` induces the quotient map `extCokerMap f Y` on the cokernels.

The same is done covariantly (`extCokerEquivCov`, `extCokerEquivCov_natural`): for a short exact
complex whose middle term satisfies `Subsingleton (Ext X S.X₂ 1)`, the covariant sequence of
`Ext(X,-)` gives `Ext¹(X,X₁) ≅ Ext⁰(X,X₃) / im(Ext⁰(X,X₂) → Ext⁰(X,X₃))`.

Everything here is `sorry`-free; the statements are in an arbitrary abelian category with `HasExt`,
and are instantiated at `C = Rep Coeff G` in `ArchDictionary/extOneDictNatural.lean`.
-/

open CategoryTheory

namespace Work.SSGRoute.ArchDictionary

variable {C : Type*} [Category* C] [Abelian C] [HasExt C]

/-! ## The contravariant cokernel description -/

/-- The map `Ext⁰(X₂,Y) → Ext⁰(X₁,Y)` induced by `S.f` (restriction along `f`). -/
noncomputable def extRestrict (S : ShortComplex C) (Y : C) :
    Abelian.Ext S.X₂ Y 0 →+ Abelian.Ext S.X₁ Y 0 :=
  (Abelian.Ext.mk₀ S.f).precomp Y (zero_add 0)

@[simp] lemma extRestrict_apply (S : ShortComplex C) (Y : C) (w : Abelian.Ext S.X₂ Y 0) :
    extRestrict S Y w = (Abelian.Ext.mk₀ S.f).comp w (zero_add 0) :=
  ext_precomp_apply (Abelian.Ext.mk₀ S.f) Y (zero_add 0) w

/-- The connecting map `Ext⁰(X₁,Y) → Ext¹(X₃,Y)` (Yoneda product with the class of `S`). -/
noncomputable def extConn (S : ShortComplex C) (hS : S.ShortExact) (Y : C) :
    Abelian.Ext S.X₁ Y 0 →+ Abelian.Ext S.X₃ Y 1 :=
  hS.extClass.precomp Y (add_zero 1)

@[simp] lemma extConn_apply (S : ShortComplex C) (hS : S.ShortExact) (Y : C)
    (a : Abelian.Ext S.X₁ Y 0) :
    extConn S hS Y a = hS.extClass.comp a (add_zero 1) :=
  ext_precomp_apply (hS.extClass) Y (add_zero 1) a

/-- The connecting map is surjective when the middle term is projective. -/
lemma extConn_range (S : ShortComplex C) (hS : S.ShortExact) [Projective S.X₂] (Y : C) :
    (extConn S hS Y).range = ⊤ := by
  have hs : Subsingleton (Abelian.Ext S.X₂ Y 1) :=
    Abelian.Ext.subsingleton_of_projective S.X₂ Y 0
  rw [AddMonoidHom.range_eq_top]
  intro y
  have hzero : (Abelian.Ext.mk₀ S.g).comp y (zero_add 1) = 0 := hs.elim _ _
  obtain ⟨x, hx⟩ := Abelian.Ext.contravariant_sequence_exact₃ hS Y y hzero (n₀ := 0) (add_zero 1)
  exact ⟨x, by simpa only [extConn_apply] using hx⟩

theorem extConn_surjective (S : ShortComplex C) (hS : S.ShortExact) [Projective S.X₂] (Y : C) :
    Function.Surjective (extConn S hS Y) :=
  AddMonoidHom.range_eq_top.mp (extConn_range S hS Y)

/-- The kernel of the connecting map is the image of the restriction map. -/
lemma extConn_ker (S : ShortComplex C) (hS : S.ShortExact) [Projective S.X₂] (Y : C) :
    (extConn S hS Y).ker = (extRestrict S Y).range := by
  apply le_antisymm
  · intro x hx
    rw [AddMonoidHom.mem_ker] at hx
    obtain ⟨w, hw⟩ := Abelian.Ext.contravariant_sequence_exact₁ hS Y x (n₁ := 1)
      (add_zero 1) (by simpa only [extConn_apply] using hx)
    exact ⟨w, by simpa only [extRestrict_apply] using hw⟩
  · rintro x ⟨w, rfl⟩
    rw [AddMonoidHom.mem_ker, extConn_apply, extRestrict_apply]
    simpa using hS.extClass_comp_assoc (Y := Y) w

/-- The connecting map, as an isomorphism `Ext⁰(X₁,Y)/ker ≅ Ext¹(X₃,Y)`. -/
noncomputable def extCokerAux (S : ShortComplex C) (hS : S.ShortExact) [Projective S.X₂] (Y : C) :
    (Abelian.Ext S.X₁ Y 0 ⧸ (extConn S hS Y).ker) ≃+ Abelian.Ext S.X₃ Y 1 :=
  AddEquiv.ofBijective (QuotientAddGroup.lift (extConn S hS Y).ker (extConn S hS Y) le_rfl)
    ⟨fun a b h => by
      have hk : (QuotientAddGroup.lift (extConn S hS Y).ker (extConn S hS Y) le_rfl).ker = ⊥ := by
        rw [QuotientAddGroup.ker_lift, QuotientAddGroup.map_mk'_self]
      exact (AddMonoidHom.ker_eq_bot_iff _).mp hk h,
     fun y => by
      obtain ⟨a, ha⟩ := extConn_surjective S hS Y y
      exact ⟨QuotientAddGroup.mk a, by rw [QuotientAddGroup.lift_mk]; exact ha⟩⟩

@[simp] lemma extCokerAux_mk (S : ShortComplex C) (hS : S.ShortExact) [Projective S.X₂] (Y : C)
    (a : Abelian.Ext S.X₁ Y 0) :
    extCokerAux S hS Y (QuotientAddGroup.mk a) = extConn S hS Y a := by
  show (QuotientAddGroup.lift (extConn S hS Y).ker (extConn S hS Y) le_rfl
    (QuotientAddGroup.mk a)) = _
  rw [QuotientAddGroup.lift_mk]

/-- Replacing the kernel of the connecting map by the image of the restriction map. -/
noncomputable def extCokerMapId (S : ShortComplex C) (hS : S.ShortExact) [Projective S.X₂] (Y : C) :
    (Abelian.Ext S.X₁ Y 0 ⧸ (extConn S hS Y).ker) ≃+
      (Abelian.Ext S.X₁ Y 0 ⧸ (extRestrict S Y).range) :=
  QuotientAddGroup.congr (extConn S hS Y).ker (extRestrict S Y).range (AddEquiv.refl _) (by
    rw [extConn_ker S hS Y]; exact AddSubgroup.map_id _)

/-- **The explicit cokernel description** of `Ext¹(X₃,Y)`. -/
noncomputable def extCokerEquiv (S : ShortComplex C) (hS : S.ShortExact) [Projective S.X₂] (Y : C) :
    Abelian.Ext S.X₃ Y 1 ≃+
      (Abelian.Ext S.X₁ Y 0 ⧸ (extRestrict S Y).range) :=
  (extCokerAux S hS Y).symm.trans (extCokerMapId S hS Y)

/-- **Computation rule**: on a class in the image of the connecting map, `extCokerEquiv` is the
class of the preimage. -/
lemma extCokerEquiv_extClass (S : ShortComplex C) (hS : S.ShortExact) [Projective S.X₂] (Y : C)
    (a : Abelian.Ext S.X₁ Y 0) :
    extCokerEquiv S hS Y (hS.extClass.comp a (add_zero 1)) = QuotientAddGroup.mk a := by
  rw [← extConn_apply S hS Y a]
  show extCokerMapId S hS Y ((extCokerAux S hS Y).symm (extConn S hS Y a)) = _
  rw [show (extCokerAux S hS Y).symm (extConn S hS Y a) = QuotientAddGroup.mk a from by
    rw [← extCokerAux_mk S hS Y a, AddEquiv.symm_apply_apply]]
  rfl

/-- The map induced on the cokernel description by a morphism of short complexes. -/
noncomputable def extCokerMap {S₁ S₂ : ShortComplex C} (f : S₁ ⟶ S₂) (Y : C) :
    (Abelian.Ext S₂.X₁ Y 0 ⧸ (extRestrict S₂ Y).range) →+
      (Abelian.Ext S₁.X₁ Y 0 ⧸ (extRestrict S₁ Y).range) :=
  QuotientAddGroup.map (extRestrict S₂ Y).range (extRestrict S₁ Y).range
    ((Abelian.Ext.mk₀ f.τ₁).precomp Y (zero_add 0)) (by
      intro z hz
      rw [AddSubgroup.mem_comap]
      obtain ⟨w, rfl⟩ := hz
      refine ⟨(Abelian.Ext.mk₀ f.τ₂).comp w (zero_add 0), ?_⟩
      rw [extRestrict_apply, extRestrict_apply, ext_precomp_apply,
        Abelian.Ext.mk₀_comp_mk₀_assoc f.τ₁ S₂.f w, f.comm₁₂,
        ← Abelian.Ext.mk₀_comp_mk₀_assoc S₁.f f.τ₂ w])

@[simp] lemma extCokerMap_mk {S₁ S₂ : ShortComplex C} (f : S₁ ⟶ S₂) (Y : C)
    (z : Abelian.Ext S₂.X₁ Y 0) :
    extCokerMap f Y (QuotientAddGroup.mk z) =
      QuotientAddGroup.mk ((Abelian.Ext.mk₀ f.τ₁).precomp Y (zero_add 0) z) :=
  QuotientAddGroup.map_mk _ _ _ _ z

/-- **Naturality of the cokernel description** in the short complex. -/
theorem extCokerEquiv_natural {S₁ S₂ : ShortComplex C} (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)
    [Projective S₁.X₂] [Projective S₂.X₂] (f : S₁ ⟶ S₂) (Y : C) (x : Abelian.Ext S₂.X₃ Y 1) :
    extCokerEquiv S₁ hS₁ Y ((Abelian.Ext.mk₀ f.τ₃).comp x (zero_add 1))
      = extCokerMap f Y (extCokerEquiv S₂ hS₂ Y x) := by
  obtain ⟨a, rfl⟩ := extConn_surjective S₂ hS₂ Y x
  rw [extConn_apply S₂ hS₂ Y a, extCokerEquiv_extClass S₂ hS₂ Y a]
  have h1 : (Abelian.Ext.mk₀ f.τ₃).comp (hS₂.extClass.comp a (add_zero 1)) (zero_add 1)
      = hS₁.extClass.comp
          ((Abelian.Ext.mk₀ f.τ₁).precomp Y (zero_add 0) a) (add_zero 1) := by
    rw [ext_precomp_apply]
    rw [← Abelian.Ext.comp_assoc_of_third_deg_zero (Abelian.Ext.mk₀ f.τ₃) (hS₂.extClass) a]
    rw [← ShortComplex.ShortExact.extClass_naturality hS₁ hS₂ f]
    rw [Abelian.Ext.comp_assoc_of_third_deg_zero (hS₁.extClass) (Abelian.Ext.mk₀ f.τ₁) a]
  rw [h1, extCokerEquiv_extClass S₁ hS₁ Y ((Abelian.Ext.mk₀ f.τ₁).precomp Y (zero_add 0) a),
    extCokerMap_mk]

/-! ## The covariant cokernel description -/

/-- The map `Ext⁰(X,X₂) → Ext⁰(X,X₃)` induced by `S.g`. -/
noncomputable def extGMap (S : ShortComplex C) (X : C) :
    Abelian.Ext X S.X₂ 0 →+ Abelian.Ext X S.X₃ 0 :=
  (Abelian.Ext.mk₀ S.g).postcomp X (zero_add 0)

@[simp] lemma extGMap_apply (S : ShortComplex C) (X : C) (w : Abelian.Ext X S.X₂ 0) :
    extGMap S X w = w.comp (Abelian.Ext.mk₀ S.g) (zero_add 0) :=
  ext_postcomp_apply (Abelian.Ext.mk₀ S.g) X (zero_add 0) w

/-- The connecting map `Ext⁰(X,X₃) → Ext¹(X,X₁)` (Yoneda product with the class of `S`). -/
noncomputable def extDep (S : ShortComplex C) (hS : S.ShortExact) (X : C) :
    Abelian.Ext X S.X₃ 0 →+ Abelian.Ext X S.X₁ 1 :=
  hS.extClass.postcomp X (zero_add 1)

@[simp] lemma extDep_apply (S : ShortComplex C) (hS : S.ShortExact) (X : C)
    (a : Abelian.Ext X S.X₃ 0) :
    extDep S hS X a = a.comp hS.extClass (zero_add 1) :=
  ext_postcomp_apply (hS.extClass) X (zero_add 1) a

/-- The covariant connecting map is surjective when `Ext¹(X,X₂)` vanishes. -/
lemma extDep_range (S : ShortComplex C) (hS : S.ShortExact) (X : C)
    (hs : Subsingleton (Abelian.Ext X S.X₂ 1)) : (extDep S hS X).range = ⊤ := by
  rw [AddMonoidHom.range_eq_top]
  intro y
  have hzero : y.comp (Abelian.Ext.mk₀ S.f) (add_zero 1) = 0 := hs.elim _ _
  obtain ⟨x, hx⟩ := Abelian.Ext.covariant_sequence_exact₁ X hS y hzero (n₀ := 0) (zero_add 1)
  exact ⟨x, by simpa only [extDep_apply] using hx⟩

theorem extDep_surjective (S : ShortComplex C) (hS : S.ShortExact) (X : C)
    (hs : Subsingleton (Abelian.Ext X S.X₂ 1)) : Function.Surjective (extDep S hS X) :=
  AddMonoidHom.range_eq_top.mp (extDep_range S hS X hs)

/-- The kernel of the covariant connecting map is the image of `Ext⁰(X,X₂) → Ext⁰(X,X₃)`. -/
lemma extDep_ker (S : ShortComplex C) (hS : S.ShortExact) (X : C)
    (hs : Subsingleton (Abelian.Ext X S.X₂ 1)) : (extDep S hS X).ker = (extGMap S X).range := by
  apply le_antisymm
  · intro x hx
    rw [AddMonoidHom.mem_ker] at hx
    obtain ⟨w, hw⟩ := Abelian.Ext.covariant_sequence_exact₃ X hS x (n₁ := 1)
      (zero_add 1) (by simpa only [extDep_apply] using hx)
    exact ⟨w, by simpa only [extGMap_apply] using hw⟩
  · rintro x ⟨w, rfl⟩
    rw [AddMonoidHom.mem_ker, extDep_apply, extGMap_apply]
    have h3 : 0 + 0 + 1 = 1 := by omega
    show (w.comp (Abelian.Ext.mk₀ S.g) (zero_add 0)).comp hS.extClass h3 = 0
    rw [Abelian.Ext.comp_assoc (α := w) (β := Abelian.Ext.mk₀ S.g) (γ := hS.extClass)]
    · rw [hS.comp_extClass, Abelian.Ext.comp_zero]
    · rfl
    · rfl

/-- The covariant connecting map, as an isomorphism `Ext⁰(X,X₃)/ker ≅ Ext¹(X,X₁)`. -/
noncomputable def extCokerAuxCov (S : ShortComplex C) (hS : S.ShortExact) (X : C)
    (hs : Subsingleton (Abelian.Ext X S.X₂ 1)) :
    (Abelian.Ext X S.X₃ 0 ⧸ (extDep S hS X).ker) ≃+ Abelian.Ext X S.X₁ 1 :=
  AddEquiv.ofBijective (QuotientAddGroup.lift (extDep S hS X).ker (extDep S hS X) le_rfl)
    ⟨fun a b h => by
      have hk : (QuotientAddGroup.lift (extDep S hS X).ker (extDep S hS X) le_rfl).ker = ⊥ := by
        rw [QuotientAddGroup.ker_lift, QuotientAddGroup.map_mk'_self]
      exact (AddMonoidHom.ker_eq_bot_iff _).mp hk h,
     fun y => by
      obtain ⟨a, ha⟩ := extDep_surjective S hS X hs y
      exact ⟨QuotientAddGroup.mk a, by rw [QuotientAddGroup.lift_mk]; exact ha⟩⟩

@[simp] lemma extCokerAuxCov_mk (S : ShortComplex C) (hS : S.ShortExact) (X : C)
    (hs : Subsingleton (Abelian.Ext X S.X₂ 1)) (a : Abelian.Ext X S.X₃ 0) :
    extCokerAuxCov S hS X hs (QuotientAddGroup.mk a) = extDep S hS X a := by
  show (QuotientAddGroup.lift (extDep S hS X).ker (extDep S hS X) le_rfl
    (QuotientAddGroup.mk a)) = _
  rw [QuotientAddGroup.lift_mk]

/-- Replacing the kernel of the covariant connecting map by the image of the `g`-map. -/
noncomputable def extCokerMapIdCov (S : ShortComplex C) (hS : S.ShortExact) (X : C)
    (hs : Subsingleton (Abelian.Ext X S.X₂ 1)) :
    (Abelian.Ext X S.X₃ 0 ⧸ (extDep S hS X).ker) ≃+
      (Abelian.Ext X S.X₃ 0 ⧸ (extGMap S X).range) :=
  QuotientAddGroup.congr (extDep S hS X).ker (extGMap S X).range (AddEquiv.refl _) (by
    rw [extDep_ker S hS X hs]; exact AddSubgroup.map_id _)

/-- **The explicit covariant cokernel description** of `Ext¹(X,X₁)`. -/
noncomputable def extCokerEquivCov (S : ShortComplex C) (hS : S.ShortExact) (X : C)
    (hs : Subsingleton (Abelian.Ext X S.X₂ 1)) :
    Abelian.Ext X S.X₁ 1 ≃+ (Abelian.Ext X S.X₃ 0 ⧸ (extGMap S X).range) :=
  (extCokerAuxCov S hS X hs).symm.trans (extCokerMapIdCov S hS X hs)

/-- **Computation rule** for the covariant cokernel description. -/
lemma extCokerEquivCov_extClass (S : ShortComplex C) (hS : S.ShortExact) (X : C)
    (hs : Subsingleton (Abelian.Ext X S.X₂ 1)) (a : Abelian.Ext X S.X₃ 0) :
    extCokerEquivCov S hS X hs (a.comp hS.extClass (zero_add 1)) = QuotientAddGroup.mk a := by
  rw [← extDep_apply S hS X a]
  show extCokerMapIdCov S hS X hs ((extCokerAuxCov S hS X hs).symm (extDep S hS X a)) = _
  rw [show (extCokerAuxCov S hS X hs).symm (extDep S hS X a) = QuotientAddGroup.mk a from by
    rw [← extCokerAuxCov_mk S hS X hs a, AddEquiv.symm_apply_apply]]
  rfl

/-- Associativity bookkeeping for `extCokerMapCov`. -/
private lemma extCokerMapCov_key {S₁ S₂ : ShortComplex C} (f : S₁ ⟶ S₂) (X : C)
    (w : Abelian.Ext X S₁.X₂ 0) :
    (w.comp (Abelian.Ext.mk₀ f.τ₂) (zero_add 0)).comp (Abelian.Ext.mk₀ S₂.g) (zero_add 0)
      = (w.comp (Abelian.Ext.mk₀ S₁.g) (zero_add 0)).comp (Abelian.Ext.mk₀ f.τ₃) (zero_add 0) := by
  rw [Abelian.Ext.comp_assoc_of_third_deg_zero w (Abelian.Ext.mk₀ f.τ₂) (Abelian.Ext.mk₀ S₂.g)]
  rw [Abelian.Ext.mk₀_comp_mk₀, f.comm₂₃]
  rw [← Abelian.Ext.mk₀_comp_mk₀]
  rw [← Abelian.Ext.comp_assoc_of_third_deg_zero w (Abelian.Ext.mk₀ S₁.g) (Abelian.Ext.mk₀ f.τ₃)]

/-- The map induced on the covariant cokernel description by a morphism of short complexes. -/
noncomputable def extCokerMapCov {S₁ S₂ : ShortComplex C} (f : S₁ ⟶ S₂) (X : C) :
    (Abelian.Ext X S₁.X₃ 0 ⧸ (extGMap S₁ X).range) →+
      (Abelian.Ext X S₂.X₃ 0 ⧸ (extGMap S₂ X).range) :=
  QuotientAddGroup.map (extGMap S₁ X).range (extGMap S₂ X).range
    ((Abelian.Ext.mk₀ f.τ₃).postcomp X (zero_add 0)) (by
      intro z hz
      rw [AddSubgroup.mem_comap]
      obtain ⟨w, rfl⟩ := hz
      refine ⟨w.comp (Abelian.Ext.mk₀ f.τ₂) (zero_add 0), ?_⟩
      rw [extGMap_apply, extGMap_apply, ext_postcomp_apply]
      exact extCokerMapCov_key f X w)

@[simp] lemma extCokerMapCov_mk {S₁ S₂ : ShortComplex C} (f : S₁ ⟶ S₂) (X : C)
    (z : Abelian.Ext X S₁.X₃ 0) :
    extCokerMapCov f X (QuotientAddGroup.mk z) =
      QuotientAddGroup.mk ((Abelian.Ext.mk₀ f.τ₃).postcomp X (zero_add 0) z) :=
  QuotientAddGroup.map_mk _ _ _ _ z

/-- **Naturality of the covariant cokernel description** in the short complex. -/
theorem extCokerEquivCov_natural {S₁ S₂ : ShortComplex C} (hS₁ : S₁.ShortExact)
    (hS₂ : S₂.ShortExact) {X : C} (hs₁ : Subsingleton (Abelian.Ext X S₁.X₂ 1))
    (hs₂ : Subsingleton (Abelian.Ext X S₂.X₂ 1)) (f : S₁ ⟶ S₂)
    (α : Abelian.Ext X S₁.X₁ 1) :
    extCokerEquivCov S₂ hS₂ X hs₂ ((Abelian.Ext.mk₀ f.τ₁).postcomp X (add_zero 1) α)
      = extCokerMapCov f X (extCokerEquivCov S₁ hS₁ X hs₁ α) := by
  obtain ⟨a, rfl⟩ := extDep_surjective S₁ hS₁ X hs₁ α
  rw [extDep_apply S₁ hS₁ X a, extCokerEquivCov_extClass S₁ hS₁ X hs₁ a]
  have h1 : (Abelian.Ext.mk₀ f.τ₁).postcomp X (add_zero 1) (a.comp hS₁.extClass (zero_add 1))
      = (a.comp (Abelian.Ext.mk₀ f.τ₃) (zero_add 0)).comp hS₂.extClass (zero_add 1) := by
    rw [ext_postcomp_apply,
      Abelian.Ext.comp_assoc_of_third_deg_zero a (hS₁.extClass) (Abelian.Ext.mk₀ f.τ₁)]
    rw [ShortComplex.ShortExact.extClass_naturality hS₁ hS₂ f]
    rw [← Abelian.Ext.comp_assoc_of_second_deg_zero a (Abelian.Ext.mk₀ f.τ₃) (hS₂.extClass)]
  rw [h1, extCokerEquivCov_extClass S₂ hS₂ X hs₂ (a.comp (Abelian.Ext.mk₀ f.τ₃) (zero_add 0)),
    extCokerMapCov_mk, ext_postcomp_apply]

end Work.SSGRoute.ArchDictionary
