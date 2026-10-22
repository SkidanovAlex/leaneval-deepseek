import Mathlib
import Submission.Work.CWIND.Basic
import Submission.Work.CWIND.GClass.SigmaFst

/-!
# CWIND/GClass — the singular chains of a disjoint union

The `n`-chains of a disjoint union `⊔_j X j` of topological spaces are the coproduct of the
`n`-chains of the pieces.  The mathematical input is that every continuous map `Δⁿ ⟶ ⊔_j X j`
lands in a single piece (`Work.CWIND.GClass.singSpace_sigmaFst_eq`); the rest is the bookkeeping
that a coproduct of coproducts is a coproduct, using Mathlib's description of the singular chains
as a coproduct of copies of the coefficient object indexed by the simplices
(`SSet.chainComplexXCofan`, `SSet.ι_chainComplexMap_f`).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits LightCondensed LightProfinite
open LightCondensed.Solid Submission.Blueprint
open Opposite
open scoped Simplicial

namespace Work.CWIND.GClass

/-- The coefficient object `ℤ`, as an object of abelian groups. -/
abbrev Rz : ModuleCat ℤ := ModuleCat.of ℤ ℤ

/-- A basepoint of the standard simplex. -/
def simpPt (n : ℕ) : Δ n := Classical.arbitrary (Δ n)

/-- **Naturality of `TopCat.toSSetObjEquiv` in the space**, in the form used below: postcomposition
with an inclusion of a piece corresponds to composing the continuous map with that inclusion. -/
lemma toSSetObjEquiv_sigmaι_app {J : Type} {X : J → TopCat.{0}} (j : J)
    (n : SimplexCategoryᵒᵖ) (τ : (TopCat.toSSet.obj (X j)).obj n) :
    (TopCat.toSSetObjEquiv (TopCat.of (Σ j, (X j : Type))) n)
        ((TopCat.toSSet.map (TopCat.sigmaι X j)).app n τ) =
      (TopCat.sigmaι X j).hom.comp (TopCat.toSSetObjEquiv (X j) n τ) := rfl

lemma sigmaι_injective {J : Type} {X : J → TopCat.{0}} (j : J) :
    Function.Injective (⇑(TopCat.sigmaι X j)) := by
  intro a b h
  rw [sigmaι_apply, sigmaι_apply] at h
  exact (heq_eq_eq _ _).mp (Sigma.mk.inj_iff.mp h).2

/-- The canonical map from the simplices of the pieces of a disjoint union to the simplices of the
disjoint union. -/
def singSimpFun {J : Type} (X : J → TopCat.{0}) (n : ℕ)
    (p : (Σ j, (TopCat.toSSet.obj (X j)).obj (Opposite.op ⦋n⦌))) :
    (TopCat.toSSet.obj (TopCat.of (Σ j, (X j : Type)))).obj (Opposite.op ⦋n⦌) :=
  (TopCat.toSSet.map (TopCat.sigmaι X p.1)).app (Opposite.op ⦋n⦌) p.2

/-- **The simplices of a disjoint union.**  The canonical map `singSimpFun` is bijective. -/
theorem singSimpEquiv_bijective {J : Type} (X : J → TopCat.{0}) (n : ℕ) :
    Function.Bijective (singSimpFun X n) := by
  constructor
  · rintro ⟨j, τ⟩ ⟨k, υ⟩ hpq
    have h1 := congrArg (TopCat.toSSetObjEquiv (TopCat.of (Σ j, (X j : Type)))
      (Opposite.op ⦋n⦌)) hpq
    simp only [singSimpFun] at h1
    rw [toSSetObjEquiv_sigmaι_app, toSSetObjEquiv_sigmaι_app] at h1
    have hpt : j = k := by
      have h2 := congrFun (congrArg DFunLike.coe h1) (simpPt n)
      simp only [ContinuousMap.comp_apply, sigmaι_apply] at h2
      exact (Sigma.mk.inj_iff.mp h2).1
    subst k
    have h3 : (TopCat.toSSetObjEquiv (X j) (Opposite.op ⦋n⦌)) τ =
        (TopCat.toSSetObjEquiv (X j) (Opposite.op ⦋n⦌)) υ := by
      apply ContinuousMap.ext
      intro t
      have h4 := congrFun (congrArg DFunLike.coe h1) t
      simp only [ContinuousMap.comp_apply, sigmaι_apply] at h4
      exact (heq_eq_eq _ _).mp (Sigma.mk.inj_iff.mp h4).2
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
    exact (TopCat.toSSetObjEquiv (X j) (Opposite.op ⦋n⦌)).injective h3
  · intro x
    let f := TopCat.toSSetObjEquiv (TopCat.of (Σ j, (X j : Type))) (Opposite.op ⦋n⦌) x
    obtain ⟨j, hj⟩ := singSpace_sigmaFst_eq X n f
    refine ⟨⟨j, (TopCat.toSSetObjEquiv (X j) (Opposite.op ⦋n⦌)).symm
      (corestrict n f j hj)⟩, ?_⟩
    apply (TopCat.toSSetObjEquiv (TopCat.of (Σ j, (X j : Type))) (Opposite.op ⦋n⦌)).injective
    simp only [singSimpFun]
    rw [toSSetObjEquiv_sigmaι_app, Equiv.apply_symm_apply]
    exact sigmaι_corestrict n f j hj

/-- The equivalence of the simplices of a disjoint union with the disjoint union of the simplices
of the pieces; its inverse is the canonical map `singSimpFun`. -/
noncomputable def singSimpEquiv {J : Type} (X : J → TopCat.{0}) (n : ℕ) :
    (TopCat.toSSet.obj (TopCat.of (Σ j, (X j : Type)))).obj (Opposite.op ⦋n⦌) ≃
      (Σ j, (TopCat.toSSet.obj (X j)).obj (Opposite.op ⦋n⦌)) :=
  (Equiv.ofBijective (singSimpFun X n) (singSimpEquiv_bijective X n)).symm

lemma singSimpEquiv_symm_apply {J : Type} (X : J → TopCat.{0}) (n : ℕ)
    (p : (Σ j, (TopCat.toSSet.obj (X j)).obj (Opposite.op ⦋n⦌))) :
    (singSimpEquiv X n).symm p =
      (TopCat.toSSet.map (TopCat.sigmaι X p.1)).app (Opposite.op ⦋n⦌) p.2 := rfl

/-- **The singular chains of a disjoint union, degreewise.**  For every `n`, the `n`-chains of
`⊔_j X j` are the coproduct of the `n`-chains of the pieces. -/
theorem isColimit_singC_sigma (J : Type) (X : J → TopCat.{0}) (n : ℕ) :
    Nonempty (IsColimit (Cofan.mk
      (f := fun j => ((Submission.Blueprint.singC).obj (X j)).X n)
      (((Submission.Blueprint.singC).obj (TopCat.of (Σ j, (X j : Type)))).X n)
      (fun j => ((Submission.Blueprint.singC).map (TopCat.sigmaι X j)).f n))) := by
  classical
  let S := TopCat.of (Σ j, (X j : Type))
  have h : IsColimit (Cofan.mk (f := fun j =>
        (((TopCat.toSSet.obj (X j)).chainComplex Rz).X n))
      (((TopCat.toSSet.obj S).chainComplex Rz).X n)
      (fun j => (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.sigmaι X j)) Rz).f n)) := by
    let I := (TopCat.toSSet.obj S).obj (Opposite.op ⦋n⦌)
    let E := singSimpEquiv X n
    have hZ : IsColimit (Cofan.mk (f := fun _ : I => Rz)
        (((TopCat.toSSet.obj S).chainComplex Rz).X n)
        (fun x => (TopCat.toSSet.obj S).ιChainComplex (R := Rz) x)) :=
      SSet.isColimitChainComplexXCofan _ _ _
    have hfacZ : ∀ {W : ModuleCat ℤ} (g : I → (Rz ⟶ W)) (x : I),
        (TopCat.toSSet.obj S).ιChainComplex (R := Rz) x ≫
          hZ.desc (Cofan.mk (f := fun _ : I => Rz) W g) = g x := by
      intro W g x
      have h := IsColimit.fac hZ (Cofan.mk (f := fun _ : I => Rz) W g) (Discrete.mk x)
      rw [Cofan.mk_ι_app] at h
      exact h
    have hE : ∀ p : (Σ j, (TopCat.toSSet.obj (X j)).obj (Opposite.op ⦋n⦌)),
        E.symm p = (TopCat.toSSet.map (TopCat.sigmaι X p.1)).app (Opposite.op ⦋n⦌) p.2 :=
      fun p => rfl
    refine ⟨fun s => hZ.desc (Cofan.mk (f := fun _ : I => Rz) s.pt
          (fun x => show Rz ⟶ s.pt from
            (TopCat.toSSet.obj (X (E x).1)).ιChainComplex (R := Rz) (E x).2 ≫
              s.ι.app (Discrete.mk (E x).1))), ?_, ?_⟩
    · intro s j
      refine SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj (X j.as)) (R := Rz) (n := n) ?_
      intro τ
      rw [Cofan.mk_ι_app]
      have h1 : (TopCat.toSSet.obj (X j.as)).ιChainComplex (R := Rz) τ ≫
          (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.sigmaι X j.as)) Rz).f n =
          (TopCat.toSSet.obj S).ιChainComplex (R := Rz) (E.symm (Sigma.mk j.as τ)) := by
        rw [SSet.ι_chainComplexMap_f]
        exact congrArg _ (hE (Sigma.mk j.as τ))
      rw [← Category.assoc, h1, hfacZ (fun x => show Rz ⟶ s.pt from
        (TopCat.toSSet.obj (X (E x).1)).ιChainComplex (R := Rz) (E x).2 ≫
          s.ι.app (Discrete.mk (E x).1)) (E.symm (Sigma.mk j.as τ)),
        Equiv.apply_symm_apply E (Sigma.mk j.as τ)]
    · intro s m hm
      simp only [Cofan.mk_ι_app] at hm
      apply hZ.hom_ext
      rintro ⟨x⟩
      rw [Cofan.mk_ι_app]
      have hx : (TopCat.toSSet.obj S).ιChainComplex (R := Rz) x =
          (TopCat.toSSet.obj (X (E x).1)).ιChainComplex (R := Rz) (E x).2 ≫
            (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.sigmaι X (E x).1)) Rz).f n := by
        rw [SSet.ι_chainComplexMap_f]
        exact congrArg _ (Equiv.symm_apply_apply E x).symm
      rw [hx]
      conv_rhs => rw [← hx, hfacZ (fun x => show Rz ⟶ s.pt from
        (TopCat.toSSet.obj (X (E x).1)).ιChainComplex (R := Rz) (E x).2 ≫
          s.ι.app (Discrete.mk (E x).1)) x]
      conv_lhs => rw [Category.assoc, hm (Discrete.mk (E x).1)]
  exact ⟨h⟩

end Work.CWIND.GClass
