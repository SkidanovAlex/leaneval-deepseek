import Mathlib
import Submission.Work.DeltaHomology.SkelChainDefs
import Submission.Work.DeltaHomology.Realization
import Submission.Work.DeltaHomology.RealizationDefs
import Submission.Work.DeltaHomology.Skeleton
import Submission.Work.DeltaHomology.SkeletonDefs
import Submission.Work.DeltaHomology.SkelSet
import Submission.Work.DeltaHomology.Basic
import Submission.Work.Homology.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open Convexity
open Work.Homology

open scoped Simplicial

namespace Work.DeltaHomology

noncomputable section

variable {K : DeltaCx} {X : TopCat}

/-! ## The degree-`0` component of the comparison map on the `0`-skeleton

The `0`-skeleton `X⁰ = χ.skelSet 0` of a realized `Δ`-complex is the finite set of
vertices `χ.cls 0 σ b` (`b` the interior point of `Δ¹`), and the comparison map
`(K.skel 0).chainX 0 ⟶ C_0(X⁰)` is, on the coproduct of the vertices, the coproduct
of the inclusions along the bijection `σ ↦ χ.cls 0 σ b`.  Since `Σ.desc` of the
inclusions along an equivalence is an isomorphism, so is the comparison map.

This file proves the intermediate lemmas (the vertex map is a bijection, `skelMap K 0`
is a bijection, `Σ.desc` along an equivalence is an isomorphism) and assembles them. -/

/-- The interior point of the standard `1`-simplex used to identify the vertices of a
realization. -/
private def vertexPt : StdSimplex ℝ (Fin 1) := simplexBarycenter 0

private lemma isOpenSimplexPoint_vertexPt : IsOpenSimplexPoint 0 vertexPt :=
  isOpenSimplexPoint_simplexBarycenter 0

/-- The vertex of `X⁰` associated to a `0`-simplex of `K`. -/
private def vertexMap (χ : DeltaSimplexMap K X) (σ : Fin (K.card 0)) : ↥(χ.skelSet 0) :=
  ⟨(χ.cls 0 σ) vertexPt, χ.cls_mem_skelSet le_rfl σ vertexPt⟩

private lemma vertexMap_surjective (χ : DeltaSimplexMap K X) :
    Function.Surjective (vertexMap χ) := by
  intro x
  have hx := x.2
  simp only [DeltaSimplexMap.skelSet, Set.mem_iUnion, Set.mem_range] at hx
  obtain ⟨j, σ, y, hy⟩ := hx
  obtain ⟨j, hj⟩ := j
  obtain rfl : j = 0 := Nat.le_zero.mp hj
  refine ⟨σ, Subtype.ext ?_⟩
  rw [Subsingleton.elim y vertexPt] at hy
  exact hy

private lemma vertexMap_injective (χ : DeltaSimplexMap K X)
    (hbij : ∀ x : X, ∃! p : OpenSimplex K, χ.real p = x) :
    Function.Injective (vertexMap χ) := by
  intro σ σ' h
  have hx : χ.real (⟨0, σ, vertexPt, isOpenSimplexPoint_vertexPt⟩ : OpenSimplex K)
      = χ.real (⟨0, σ', vertexPt, isOpenSimplexPoint_vertexPt⟩ : OpenSimplex K) := by
    simpa [DeltaSimplexMap.real, vertexMap] using congrArg (fun x : ↥(χ.skelSet 0) => (x : X)) h
  obtain ⟨p, _, huniq⟩ := hbij (χ.real (⟨0, σ, vertexPt, isOpenSimplexPoint_vertexPt⟩ : OpenSimplex K))
  have h1 : (⟨0, σ, vertexPt, isOpenSimplexPoint_vertexPt⟩ : OpenSimplex K) = p := huniq _ rfl
  have h2 : (⟨0, σ', vertexPt, isOpenSimplexPoint_vertexPt⟩ : OpenSimplex K) = p :=
    huniq _ hx.symm
  have h3 : (⟨0, σ, vertexPt, isOpenSimplexPoint_vertexPt⟩ : OpenSimplex K)
      = ⟨0, σ', vertexPt, isOpenSimplexPoint_vertexPt⟩ := h1.trans h2.symm
  have h4 : (⟨0, σ, vertexPt, isOpenSimplexPoint_vertexPt⟩ : OpenSimplex K).idx
      = (⟨0, σ', vertexPt, isOpenSimplexPoint_vertexPt⟩ : OpenSimplex K).idx := by
    cases h3
    rfl
  exact h4

private lemma bijective_vertexMap (χ : DeltaSimplexMap K X)
    (hbij : ∀ x : X, ∃! p : OpenSimplex K, χ.real p = x) :
    Function.Bijective (vertexMap χ) :=
  ⟨vertexMap_injective χ hbij, vertexMap_surjective χ⟩

/-- The inclusion of the `0`-skeleton in `K`, on `0`-simplices, is a bijection. -/
private lemma bijective_skelMap_zero (K : DeltaCx) :
    Function.Bijective (fun σ : Fin ((K.skel 0).card 0) => @skelMap K 0 0 σ) := by
  have h : skelCard K 0 0 = K.card 0 := skelCard_eq K le_rfl
  have hfun : (fun σ : Fin ((K.skel 0).card 0) => @skelMap K 0 0 σ)
      = (Fin.cast h : Fin ((K.skel 0).card 0) → Fin (K.card 0)) := by
    funext σ
    exact skelMap_eq K 0 le_rfl σ
  rw [hfun]
  exact ⟨Fin.cast_injective h, fun b => ⟨Fin.cast h.symm b, Fin.rightInverse_cast h b⟩⟩

/-- Evaluation at the interior point, an equivalence because `Δ¹` is a subsingleton. -/
private def vertexEval (χ : DeltaSimplexMap K X) :
    C(StdSimplex ℝ (Fin 1), ↥(χ.skelSet 0)) ≃ ↥(χ.skelSet 0) where
  toFun f := f vertexPt
  invFun x := ContinuousMap.const (StdSimplex ℝ (Fin 1)) x
  left_inv f := ContinuousMap.ext fun y => by
    obtain rfl : y = vertexPt := Subsingleton.elim y vertexPt
    rfl
  right_inv x := rfl

/-- The `0`-simplices of `X⁰` are the points of `X⁰`, hence the vertices of `K`. -/
private def topEquiv (χ : DeltaSimplexMap K X) :
    (TopCat.toSSet.obj (TopCat.of (χ.skelSet 0))).obj
        (Opposite.op (SimplexCategory.mk 0)) ≃ ↥(χ.skelSet 0) :=
  (TopCat.toSSetObjEquiv (TopCat.of (χ.skelSet 0)) (Opposite.op (SimplexCategory.mk 0))).trans
    (vertexEval χ)

private lemma topEquiv_chiInSkelSet (χ : DeltaSimplexMap K X) (σ : Fin (K.card 0)) :
    topEquiv χ (χ.chiInSkelSet 0 le_rfl σ) = vertexMap χ σ := by
  simp only [topEquiv, vertexEval, Equiv.trans_apply, DeltaSimplexMap.chiInSkelSet,
    Equiv.apply_symm_apply, vertexMap, DeltaSimplexMap.clsInSkelSet]
  rfl

/-- Bijeсtivity transported across an equivalence. -/
private lemma bijective_of_comp_equiv {α β γ : Sort*} (e : β ≃ γ) {f : α → β}
    (h : Function.Bijective fun a => e (f a)) : Function.Bijective f :=
  ⟨fun a b hab => h.1 (congrArg e hab), fun b => by
    obtain ⟨a, ha⟩ := h.2 (e b)
    exact ⟨a, e.injective ha⟩⟩

/-- `Σ.desc` of the coproduct inclusions along an equivalence of the index types is an
isomorphism (with inverse `Σ.desc` of the inclusions along the inverse equivalence). -/
private lemma isIso_sigma_desc_equiv {α β : Type} (e : α ≃ β) :
    IsIso (Sigma.desc (fun a : α => Sigma.ι (fun _ : β => Work.Homology.ZMod) (e a))) := by
  refine IsIso.mk ⟨Sigma.desc (fun b : β =>
    Sigma.ι (fun _ : α => Work.Homology.ZMod) (e.symm b)), ?_, ?_⟩
  · apply Sigma.hom_ext
    intro a
    rw [← Category.assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc]
    simp
  · apply Sigma.hom_ext
    intro b
    rw [← Category.assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc]
    simp

/-- The degree-`0` component of the comparison map on the `0`-skeleton is an isomorphism.
`(K.skel 0).chainX 0` is free on the vertices `Fin ((K.skel 0).card 0)`, and
`(Work.Homology.singChain Work.Homology.ZMod (TopCat.of (χ.skelSet 0))).X 0` is free on the
singular `0`-simplices of `X⁰ = χ.skelSet 0`, which are the points of `X⁰` (a singular
`0`-simplex is determined by its value, via `TopCat.toSSetObjEquiv`).  The map is `Sigma.desc` of
`σ ↦ ι (χ.chiInSkelSet 0 le_rfl (skelMap K 0 σ))`, so it suffices that this family is a bijection
(`Sigma.desc` of coproduct inclusions along a bijection is an isomorphism, with inverse
`Sigma.desc` of `ι ∘ e.symm`).  Bijectivity: `skelMap K 0` is `Fin.cast (skelCard K 0 0 = K.card 0)`
(`skelMap_eq`), hence bijective; and `σ ↦ (χ.clsInSkelSet 0 le_rfl σ) b` is the vertex map
`σ ↦ ⟨χ.cls 0 σ b, _⟩ : ↥(χ.skelSet 0)`, which is bijective by `DeltaRealization.bij`
(surjective since `χ.skelSet 0 = ⋃_{j ≤ 0} ⋃_σ range (χ.cls j σ)` and `StdSimplex ℝ (Fin 1)` is a
subsingleton; injective because two open simplices `⟨0,σ,b,hb⟩`, `⟨0,σ',b,hb⟩` with the same image
are equal). -/
theorem isIso_deltaChainMapSkelFun_zero {K : DeltaCx} {X : TopCat} (R : DeltaRealization K X) :
    CategoryTheory.IsIso (R.toDeltaSimplexMap.deltaChainMapSkelFun 0 0) := by
  classical
  let χ : DeltaSimplexMap K X := R.toDeltaSimplexMap
  have hbij : Function.Bijective (fun σ : Fin ((K.skel 0).card 0) =>
      χ.chiInSkelSet 0 le_rfl (@skelMap K 0 0 σ)) := by
    refine bijective_of_comp_equiv (topEquiv χ) ?_
    have h1 : Function.Bijective
        (fun σ : Fin ((K.skel 0).card 0) => vertexMap χ (@skelMap K 0 0 σ)) :=
      (bijective_vertexMap χ R.bij).comp (bijective_skelMap_zero K)
    simpa only [topEquiv_chiInSkelSet] using h1
  let e : Fin ((K.skel 0).card 0) ≃
      (TopCat.toSSet.obj (TopCat.of (χ.skelSet 0))).obj
        (Opposite.op (SimplexCategory.mk 0)) :=
    Equiv.ofBijective _ hbij
  have hfun : R.toDeltaSimplexMap.deltaChainMapSkelFun 0 0 =
      Sigma.desc (fun σ : Fin ((K.skel 0).card 0) =>
        Sigma.ι (fun _ : (TopCat.toSSet.obj (TopCat.of (χ.skelSet 0))).obj
          (Opposite.op (SimplexCategory.mk 0)) => Work.Homology.ZMod) (e σ)) := by
    rw [DeltaSimplexMap.deltaChainMapSkelFun, dite_eq_left le_rfl]
    rfl
  rw [hfun]
  exact isIso_sigma_desc_equiv e

end

end Work.DeltaHomology
