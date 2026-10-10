import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.local_duality_ext
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

open CategoryTheory SSGRoute.PTExt

/-- **Dévissage of the level transport along a direct-sum decomposition of the module.**  Let
`P` and `X` be `Rep Coeff G`-objects with maps `he i : P ⟶ X` and `pr i : X ⟶ P` (`i : Fin n`)
satisfying `∑ i, pr i ≫ he i = 𝟙 X` (the coordinate inclusions and projections of a decomposition
`X ≅ Pⁿ`; for `P` the trivial `𝔽_p`-module and `X` a trivial finite `ZMod p`-module with a chosen
`ZMod p`-basis these exist).  If the transport `Ext¹_G(P, A) → Ext¹_H(res f P, B)`,
`x ↦ (extRes f x) ∘ mk₀ ι`, is injective, then so is the transport on `Ext¹_G(X, A)`.

Route (the one both reviewers confirmed; **no orthogonality** `pr i ≫ he j = δᵢⱼ` is needed).
Write `y j := (mk₀ (he j)).comp x ∈ Ext¹_G(P, A)` and use naturality +
`Abelian.Ext.mapExactFunctor_comp`/`_mk₀` to get
`(mk₀ ((Rep.resFunctor f).map (he j))).comp (levelTransport f ι x)
  = levelTransport f ι y j`;
so `levelTransport f ι x = 0` forces `levelTransport f ι y j = 0` for every `j`, whence `y j = 0` by
`hfp`.  On the other hand `hdecomp` gives, via `Abelian.Ext.mk₀_add`, `comp_add`, associativity and
`Abelian.Ext.comp_mk₀_id`/`mk₀_id_comp`,
`x = ∑ j, (mk₀ (pr j)).comp ((mk₀ (he j)).comp x) = ∑ j, (mk₀ (pr j)).comp (y j) = 0`. -/
theorem levelTransport_injective_of_components {G H : Type} [Group G] [Group H]
    (f : H →* G) {A : Rep Coeff G} {B : Rep Coeff H} (ι : Rep.res f A ⟶ B)
    {P X : Rep Coeff G} {n : ℕ}
    (he : Fin n → (P ⟶ X)) (pr : Fin n → (X ⟶ P))
    (hdecomp : (∑ i : Fin n, pr i ≫ he i) = 𝟙 X)
    (hfp : Function.Injective (fun x : CategoryTheory.Abelian.Ext P A 1 =>
      (SSGRoute.PTExt.extRes f x).comp (CategoryTheory.Abelian.Ext.mk₀ ι) (add_zero 1))) :
    Function.Injective (fun x : CategoryTheory.Abelian.Ext X A 1 =>
      (SSGRoute.PTExt.extRes f x).comp (CategoryTheory.Abelian.Ext.mk₀ ι) (add_zero 1)) := by
  -- Additivity of the transport on `Ext¹_G(X, A)`.
  have hadd : ∀ a b : CategoryTheory.Abelian.Ext X A 1,
      (SSGRoute.PTExt.extRes f (a + b)).comp (CategoryTheory.Abelian.Ext.mk₀ ι) (add_zero 1)
        = (SSGRoute.PTExt.extRes f a).comp (CategoryTheory.Abelian.Ext.mk₀ ι) (add_zero 1)
          + (SSGRoute.PTExt.extRes f b).comp (CategoryTheory.Abelian.Ext.mk₀ ι) (add_zero 1) := by
    intro a b
    simp only [SSGRoute.PTExt.extRes, CategoryTheory.Abelian.Ext.mapExactFunctor_add,
      CategoryTheory.Abelian.Ext.add_comp]
  have hzero : (SSGRoute.PTExt.extRes f (0 : CategoryTheory.Abelian.Ext X A 1)).comp
      (CategoryTheory.Abelian.Ext.mk₀ ι) (add_zero 1) = 0 := by
    simp only [SSGRoute.PTExt.extRes, CategoryTheory.Abelian.Ext.mapExactFunctor_zero,
      CategoryTheory.Abelian.Ext.zero_comp]
  -- Triviality of the kernel of the transport.
  have key : ∀ x : CategoryTheory.Abelian.Ext X A 1,
      (SSGRoute.PTExt.extRes f x).comp (CategoryTheory.Abelian.Ext.mk₀ ι) (add_zero 1) = 0 →
        x = 0 := by
    intro x hx
    -- Naturality: the transport of the `j`-th coordinate of `x`.
    have hrel : ∀ j : Fin n,
        (SSGRoute.PTExt.extRes f ((CategoryTheory.Abelian.Ext.mk₀ (he j)).comp x (zero_add 1))).comp
            (CategoryTheory.Abelian.Ext.mk₀ ι) (add_zero 1)
          = (CategoryTheory.Abelian.Ext.mk₀ ((Rep.resFunctor f).map (he j))).comp
              ((SSGRoute.PTExt.extRes f x).comp (CategoryTheory.Abelian.Ext.mk₀ ι) (add_zero 1))
              (zero_add 1) := by
      intro j
      simp only [SSGRoute.PTExt.extRes, CategoryTheory.Abelian.Ext.mapExactFunctor_comp,
        CategoryTheory.Abelian.Ext.mapExactFunctor_mk₀]
      exact CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero _ _ _ (zero_add 1)
    -- Each coordinate of `x` dies, by injectivity at the level of `P`.
    have hvec0 : ∀ j : Fin n,
        (CategoryTheory.Abelian.Ext.mk₀ (he j)).comp x (zero_add 1) = 0 := by
      intro j
      apply hfp
      show (SSGRoute.PTExt.extRes f ((CategoryTheory.Abelian.Ext.mk₀ (he j)).comp x (zero_add 1))).comp
              (CategoryTheory.Abelian.Ext.mk₀ ι) (add_zero 1)
            = (SSGRoute.PTExt.extRes f (0 : CategoryTheory.Abelian.Ext P A 1)).comp
              (CategoryTheory.Abelian.Ext.mk₀ ι) (add_zero 1)
      rw [hrel j, hx]
      simp only [SSGRoute.PTExt.extRes, CategoryTheory.Abelian.Ext.mapExactFunctor_zero,
        CategoryTheory.Abelian.Ext.zero_comp, CategoryTheory.Abelian.Ext.comp_zero]
    -- The decomposition of the identity gives `x` as a sum of its coordinates.
    have hstep : (∑ i : Fin n, CategoryTheory.Abelian.Ext.mk₀ (pr i ≫ he i))
        = CategoryTheory.Abelian.Ext.mk₀ (𝟙 X) := by
      rw [← CategoryTheory.Abelian.Ext.mk₀_sum]
      exact congrArg CategoryTheory.Abelian.Ext.mk₀ hdecomp
    have hsum :
        (∑ i : Fin n, (CategoryTheory.Abelian.Ext.mk₀ (pr i ≫ he i)).comp x (zero_add 1))
          = x := by
      have h2' :=
        congrArg (fun t : CategoryTheory.Abelian.Ext X X 0 => t.comp x (zero_add 1)) hstep
      rw [CategoryTheory.Abelian.Ext.sum_comp] at h2'
      simpa only [CategoryTheory.Abelian.Ext.mk₀_id_comp] using h2'
    have hsum' :
        (∑ i : Fin n, (CategoryTheory.Abelian.Ext.mk₀ (pr i ≫ he i)).comp x (zero_add 1))
          = ∑ j : Fin n, (CategoryTheory.Abelian.Ext.mk₀ (pr j)).comp
              ((CategoryTheory.Abelian.Ext.mk₀ (he j)).comp x (zero_add 1)) (zero_add 1) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← CategoryTheory.Abelian.Ext.mk₀_comp_mk₀ (pr j) (he j)]
      exact CategoryTheory.Abelian.Ext.comp_assoc_of_second_deg_zero _ _ _ (zero_add 1)
    calc x = ∑ j : Fin n, (CategoryTheory.Abelian.Ext.mk₀ (pr j)).comp
              ((CategoryTheory.Abelian.Ext.mk₀ (he j)).comp x (zero_add 1)) (zero_add 1) :=
            hsum.symm.trans hsum'
         _ = 0 := by
            apply Finset.sum_eq_zero
            intro j _
            rw [hvec0 j]
            simp
  intro x y hxy
  have hxy' : (SSGRoute.PTExt.extRes f x).comp (CategoryTheory.Abelian.Ext.mk₀ ι) (add_zero 1)
      = (SSGRoute.PTExt.extRes f y).comp (CategoryTheory.Abelian.Ext.mk₀ ι) (add_zero 1) := hxy
  have hneg : (SSGRoute.PTExt.extRes f (-y)).comp (CategoryTheory.Abelian.Ext.mk₀ ι) (add_zero 1)
      = - ((SSGRoute.PTExt.extRes f y).comp (CategoryTheory.Abelian.Ext.mk₀ ι) (add_zero 1)) := by
    have h2 := hadd y (-y)
    rw [add_neg_cancel, hzero] at h2
    exact eq_neg_of_add_eq_zero_right h2.symm
  have hsub : (SSGRoute.PTExt.extRes f (x - y)).comp (CategoryTheory.Abelian.Ext.mk₀ ι) (add_zero 1)
      = (SSGRoute.PTExt.extRes f x).comp (CategoryTheory.Abelian.Ext.mk₀ ι) (add_zero 1)
        - (SSGRoute.PTExt.extRes f y).comp (CategoryTheory.Abelian.Ext.mk₀ ι) (add_zero 1) := by
    rw [sub_eq_add_neg, hadd, hneg, sub_eq_add_neg]
  have hthis : (SSGRoute.PTExt.extRes f (x - y)).comp
      (CategoryTheory.Abelian.Ext.mk₀ ι) (add_zero 1) = 0 := by
    rw [hsub, hxy', sub_self]
  exact sub_eq_zero.mp (key (x - y) hthis)

end Work.SSGRoute.PT
