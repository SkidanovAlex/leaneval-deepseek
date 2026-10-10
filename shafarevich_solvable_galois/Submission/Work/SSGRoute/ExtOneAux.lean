import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliary lemmas for `Ext¹_G(M,N) ≅ Ext¹_G(ℤ, Hom_ℤ(M,N))` (`N` divisible)

* the two descriptions of `Ext¹` as a cokernel coming from the long exact sequences of `Ext`
  (contravariant and covariant);
* a divisible abelian group is an injective `ULift ℤ`-module;
* free presentations of a `Rep Coeff G`.
-/

open CategoryTheory

namespace Work.SSGRoute

/-- **Contravariant description of `Ext¹` as a cokernel.** -/
theorem ext_coker_LES {C : Type*} [Category* C] [Abelian C] [HasExt C]
    {S : ShortComplex C} (hS : S.ShortExact) [Projective S.X₂] (Y : C) :
    Nonempty (Abelian.Ext S.X₃ Y 1 ≃+
      (Abelian.Ext S.X₁ Y 0 ⧸
        ((Abelian.Ext.mk₀ S.f).precomp Y (zero_add 0)).range)) := by
  have hs : Subsingleton (Abelian.Ext S.X₂ Y 1) :=
    Abelian.Ext.subsingleton_of_projective S.X₂ Y 0
  have hrange : (hS.extClass.precomp Y (add_zero 1)).range = ⊤ := by
    rw [AddMonoidHom.range_eq_top]
    intro y
    have hzero : (Abelian.Ext.mk₀ S.g).comp y (zero_add 1) = 0 := hs.elim _ _
    obtain ⟨x, hx⟩ := Abelian.Ext.contravariant_sequence_exact₃ hS Y y hzero (n₀ := 0)
      (add_zero 1)
    exact ⟨x, by simpa using hx⟩
  have hker : (hS.extClass.precomp Y (add_zero 1)).ker =
      ((Abelian.Ext.mk₀ S.f).precomp Y (zero_add 0)).range := by
    apply le_antisymm
    · intro x hx
      rw [AddMonoidHom.mem_ker] at hx
      obtain ⟨w, hw⟩ := Abelian.Ext.contravariant_sequence_exact₁ hS Y x (n₁ := 1)
        (add_zero 1) hx
      exact ⟨w, by simpa using hw⟩
    · rintro x ⟨w, rfl⟩
      rw [AddMonoidHom.mem_ker]
      simpa using hS.extClass_comp_assoc (Y := Y) w
  refine ⟨?_⟩
  have e : (Abelian.Ext S.X₁ Y 0 ⧸ (hS.extClass.precomp Y (add_zero 1)).ker) ≃+
      Abelian.Ext S.X₃ Y 1 :=
    (QuotientAddGroup.quotientKerEquivRange (hS.extClass.precomp Y (add_zero 1))).trans
      (by rw [hrange]; exact AddSubgroup.topEquiv)
  exact e.symm.trans (QuotientAddGroup.congr _ _ (AddEquiv.refl _) (by simp [hker]))

/-- **Covariant description of `Ext¹` as a cokernel.** -/
theorem ext_coker_LES_covariant {C : Type*} [Category* C] [Abelian C] [HasExt C]
    {S : ShortComplex C} (hS : S.ShortExact) (X : C)
    [hs : Subsingleton (Abelian.Ext X S.X₂ 1)] :
    Nonempty (Abelian.Ext X S.X₁ 1 ≃+
      (Abelian.Ext X S.X₃ 0 ⧸
        ((Abelian.Ext.mk₀ S.g).postcomp X (zero_add 0)).range)) := by
  have hrange : (hS.extClass.postcomp X (zero_add 1)).range = ⊤ := by
    rw [AddMonoidHom.range_eq_top]
    intro y
    have hzero : y.comp (Abelian.Ext.mk₀ S.f) (add_zero 1) = 0 := hs.elim _ _
    obtain ⟨x, hx⟩ := Abelian.Ext.covariant_sequence_exact₁ X hS y hzero (n₀ := 0)
      (zero_add 1)
    exact ⟨x, by simpa using hx⟩
  have hker : (hS.extClass.postcomp X (zero_add 1)).ker =
      ((Abelian.Ext.mk₀ S.g).postcomp X (zero_add 0)).range := by
    apply le_antisymm
    · intro x hx
      rw [AddMonoidHom.mem_ker] at hx
      obtain ⟨w, hw⟩ := Abelian.Ext.covariant_sequence_exact₃ X hS x (n₁ := 1)
        (zero_add 1) hx
      exact ⟨w, by simpa using hw⟩
    · rintro x ⟨w, rfl⟩
      rw [AddMonoidHom.mem_ker]
      have h3 : 0 + 0 + 1 = 1 := by omega
      show (w.comp (Abelian.Ext.mk₀ S.g) (zero_add 0)).comp hS.extClass h3 = 0
      rw [Abelian.Ext.comp_assoc (α := w) (β := Abelian.Ext.mk₀ S.g) (γ := hS.extClass)]
      · rw [hS.comp_extClass, Abelian.Ext.comp_zero]
      · rfl
      · rfl
  refine ⟨?_⟩
  have e : (Abelian.Ext X S.X₃ 0 ⧸ (hS.extClass.postcomp X (zero_add 1)).ker) ≃+
      Abelian.Ext X S.X₁ 1 :=
    (QuotientAddGroup.quotientKerEquivRange (hS.extClass.postcomp X (zero_add 1))).trans
      (by rw [hrange]; exact AddSubgroup.topEquiv)
  exact e.symm.trans (QuotientAddGroup.congr _ _ (AddEquiv.refl _) (by simp [hker]))

/-! ## Transport of `Ext`-classes along isomorphisms -/

section ExtTransport

variable {C : Type*} [Category* C] [Abelian C] [HasExt C]

/-- `postcomp` of a class is composition with it. -/
lemma ext_postcomp_apply {Y Z : C} {n : ℕ} (β : Abelian.Ext Y Z n) (X : C) {a b : ℕ}
    (h : a + n = b) (x : Abelian.Ext X Y a) : β.postcomp X h x = x.comp β h := by
  simp [Abelian.Ext.postcomp, Abelian.Ext.bilinearComp_apply_apply]

/-- `precomp` of a class is composition with it. -/
lemma ext_precomp_apply {X Y : C} {n : ℕ} (α : Abelian.Ext X Y n) (Z : C) {a b : ℕ}
    (h : n + a = b) (y : Abelian.Ext Y Z a) : α.precomp Z h y = α.comp y h := by
  simp [Abelian.Ext.precomp, Abelian.Ext.bilinearComp_apply_apply]

/-- The inverse of `Ext.addEquiv₀` is `mk₀`. -/
lemma ext_addEquiv₀_mk₀ {X Y : C} (f : X ⟶ Y) :
    Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ f) = f := by
  rw [← Abelian.Ext.addEquiv₀_symm_apply f, AddEquiv.apply_symm_apply]

/-- The inverse of `Ext.addEquiv₀` at the level of elements. -/
lemma ext_eq_mk₀_addEquiv₀ {X Y : C} (a : Abelian.Ext X Y 0) :
    a = Abelian.Ext.mk₀ (Abelian.Ext.addEquiv₀ a) := by
  rw [← Abelian.Ext.addEquiv₀_symm_apply (Abelian.Ext.addEquiv₀ a), AddEquiv.symm_apply_apply]

/-- Postcomposition with `mk₀ g`, transported back to morphisms. -/
lemma ext_addEquiv₀_postcomp {X Y Z : C} (g : Y ⟶ Z) (x : Abelian.Ext X Y 0) :
    Abelian.Ext.addEquiv₀ ((Abelian.Ext.mk₀ g).postcomp X (zero_add 0) x) =
      Abelian.Ext.addEquiv₀ x ≫ g := by
  conv_lhs => rw [ext_eq_mk₀_addEquiv₀ x]
  rw [Abelian.Ext.postcomp, AddMonoidHom.flip_apply, Abelian.Ext.bilinearComp_apply_apply,
    Abelian.Ext.mk₀_comp_mk₀, ext_addEquiv₀_mk₀]

/-- Precomposition with `mk₀ f`, transported back to morphisms. -/
lemma ext_addEquiv₀_precomp {X Y Z : C} (f : X ⟶ Y) (y : Abelian.Ext Y Z 0) :
    Abelian.Ext.addEquiv₀ ((Abelian.Ext.mk₀ f).precomp Z (zero_add 0) y) =
      f ≫ Abelian.Ext.addEquiv₀ y := by
  conv_lhs => rw [ext_eq_mk₀_addEquiv₀ y]
  rw [Abelian.Ext.precomp, Abelian.Ext.bilinearComp_apply_apply, Abelian.Ext.mk₀_comp_mk₀,
    ext_addEquiv₀_mk₀]

/-- `Ext X Y n` is a subsingleton as soon as this holds after transporting `X` along an
isomorphism. -/
lemma subsingleton_ext_of_iso_fst {A A' Y : C} (e : A ≅ A') (n : ℕ)
    (h : Subsingleton (Abelian.Ext A Y n)) : Subsingleton (Abelian.Ext A' Y n) := by
  have hz : ∀ z : Abelian.Ext A' Y n,
      (Abelian.Ext.mk₀ e.inv).comp ((Abelian.Ext.mk₀ e.hom).comp z (zero_add n)) (zero_add n)
        = z := by
    intro z
    rw [Abelian.Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Abelian.Ext.mk₀_id_comp]
  refine ⟨fun x y => ?_⟩
  have hxy := congrArg (fun w => (Abelian.Ext.mk₀ e.inv).comp w (zero_add n))
    (h.elim ((Abelian.Ext.mk₀ e.hom).comp x (zero_add n))
            ((Abelian.Ext.mk₀ e.hom).comp y (zero_add n)))
  exact (hz x).symm.trans (hxy.trans (hz y))

/-- `Ext X Y n` is a subsingleton as soon as this holds after transporting `Y` along an
isomorphism. -/
lemma subsingleton_ext_of_iso_snd {X Y Y' : C} (e : Y ≅ Y') (n : ℕ)
    (h : Subsingleton (Abelian.Ext X Y n)) : Subsingleton (Abelian.Ext X Y' n) := by
  have hz : ∀ z : Abelian.Ext X Y' n,
      (z.comp (Abelian.Ext.mk₀ e.inv) (add_zero n)).comp (Abelian.Ext.mk₀ e.hom) (add_zero n)
        = z := by
    intro z
    rw [Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀, e.inv_hom_id,
      Abelian.Ext.comp_mk₀_id]
  refine ⟨fun x y => ?_⟩
  have hxy := congrArg (fun w => w.comp (Abelian.Ext.mk₀ e.hom) (add_zero n))
    (h.elim (x.comp (Abelian.Ext.mk₀ e.inv) (add_zero n))
            (y.comp (Abelian.Ext.mk₀ e.inv) (add_zero n)))
  exact (hz x).symm.trans (hxy.trans (hz y))

end ExtTransport

end Work.SSGRoute
