import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.freeRep_quot_nsmul_finite
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Finiteness of the `p`-quotient of `Ext⁰` out of a free representation

For a finite group `G` and a finite type `α`, the degree-zero `Ext`-group
`Ext⁰_{ℤ[G]}(ℤ[G]^{⊕α}, A)` is the group of `G`-equivariant maps `ℤ[G]^{⊕α} ⟶ A`, i.e. the
product `A^α` (`Rep.freeLiftLEquiv`), and multiplication by `p` on it is the pointwise
multiplication by `p`.  Hence

  `Ext⁰(free α, A) ⧸ p·Ext⁰(free α, A) ≅ (A ⧸ p·A)^α`,

which is finite as soon as `α` and `A ⧸ p·A` are finite.
-/

namespace Work.SSGRoute

noncomputable section

open CategoryTheory

/-- **Finiteness of the `p`-quotient of a product.** For a finite index type `ι` and an
abelian group `A`, the range of multiplication by `p` on `ι → A` is the pointwise product
`(p·A)^ι`, so `(ι → A) ⧸ p·(ι → A) ≅ (ι → A ⧸ p·A)`; a quotient of a finite product of
finite groups is finite. -/
theorem finite_quot_nsmul_pi_aux {ι A : Type} [Finite ι] [AddCommGroup A] (p : ℕ)
    (h : Finite (A ⧸ (nsmulAddHom p A).range)) :
    Finite ((ι → A) ⧸ (nsmulAddHom p (ι → A)).range) := by
  let H : AddSubgroup A := (nsmulAddHom p A).range
  haveI : Finite (A ⧸ H) := h
  haveI : Finite (ι → A ⧸ H) := inferInstance
  let Φ : (ι → A) →+ (ι → A ⧸ H) :=
    { toFun := fun x => fun i => QuotientAddGroup.mk' H (x i)
      map_zero' := by funext i; simp
      map_add' := by intro x y; funext i; simp }
  have hΦ : ∀ (x : ι → A) (i : ι), Φ x i = QuotientAddGroup.mk' H (x i) := fun x i => rfl
  have hle : (nsmulAddHom p (ι → A)).range ≤ Φ.ker := by
    rintro x ⟨y, rfl⟩
    rw [AddMonoidHom.mem_ker]
    funext i
    rw [hΦ, nsmulAddHom_apply, Pi.smul_apply, Pi.zero_apply, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.eq_zero_iff]
    exact AddMonoidHom.mem_range.mpr ⟨y i, by rw [nsmulAddHom_apply]⟩
  have hker : Φ.ker = (nsmulAddHom p (ι → A)).range := by
    refine le_antisymm ?_ hle
    intro x hx
    rw [AddMonoidHom.mem_ker] at hx
    have hmem : ∀ i, x i ∈ H := fun i => by
      have hi := congrFun hx i
      rw [hΦ, Pi.zero_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff] at hi
      exact hi
    have hmem' : ∀ i, ∃ z : A, nsmulAddHom p A z = x i := fun i =>
      AddMonoidHom.mem_range.mp (by simpa [H] using hmem i)
    choose y hy using hmem'
    exact AddMonoidHom.mem_range.mpr ⟨y, funext fun i => by
      rw [nsmulAddHom_apply, Pi.smul_apply]
      exact hy i⟩
  let g : (ι → A) ⧸ (nsmulAddHom p (ι → A)).range →+ (ι → A ⧸ H) :=
    QuotientAddGroup.lift _ Φ hle
  have hg : Function.Injective g := by
    intro a b hab
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective b
    rw [QuotientAddGroup.lift_mk, QuotientAddGroup.lift_mk] at hab
    refine QuotientAddGroup.eq_iff_sub_mem.mpr ?_
    rw [← hker, AddMonoidHom.mem_ker, map_sub, hab, sub_self]
  exact Finite.of_injective g hg

theorem ext0_freeRep_quot_nsmul_finite {G : Type} [Group G] [Finite G] (p : ℕ)
    (α : Type) [Finite α] (A : Rep.{0} SSGRoute.PTExt.Coeff G)
    (hAq : Finite (↥A ⧸ (Work.SSGRoute.nsmulAddHom p ↥A).range)) :
    Finite (CategoryTheory.Abelian.Ext (Rep.free SSGRoute.PTExt.Coeff G α) A 0 ⧸
      (Work.SSGRoute.nsmulAddHom p (CategoryTheory.Abelian.Ext (Rep.free SSGRoute.PTExt.Coeff G α) A 0)).range) := by
  -- `Ext⁰(free α, A) ≃+ Hom(free α, A) ≃+ (α → A)`
  have hh := Rep.freeLiftLEquiv SSGRoute.PTExt.Coeff G α A
  have hhA : (Rep.free SSGRoute.PTExt.Coeff G α ⟶ A) ≃+ (α → ↥A) :=
    AddEquiv.mk' hh.toEquiv (fun x y => hh.map_add x y)
  have he : CategoryTheory.Abelian.Ext (Rep.free SSGRoute.PTExt.Coeff G α) A 0 ≃+ (α → ↥A) :=
    (CategoryTheory.Abelian.Ext.addEquiv₀ (X := Rep.free SSGRoute.PTExt.Coeff G α) (Y := A)).trans hhA
  -- `(α → A) ⧸ p·(α → A)` is finite
  haveI : Finite ((α → ↥A) ⧸ (nsmulAddHom p (α → ↥A)).range) :=
    finite_quot_nsmul_pi_aux p hAq
  -- transfer back along the bijection `(α → A) → Ext⁰(free α, A)`
  let f : (α → ↥A) →+ CategoryTheory.Abelian.Ext (Rep.free SSGRoute.PTExt.Coeff G α) A 0 :=
    { toFun := he.symm, map_zero' := he.symm.map_zero, map_add' := he.symm.map_add }
  have hf : Function.Surjective f := fun z => ⟨he z, by simp [f]⟩
  exact FreeRepQuot.finite_quot_nsmul_of_surjective f hf p

end

end Work.SSGRoute
