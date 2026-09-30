import Mathlib
import Submission.Work.KeyLemma.Curve.genericSum
import Submission.Work.Descent.galoisDescent_point
import Submission.Work.GroupChunk.exists_factor_resPt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.KeyLemma.Curve

open CategoryTheory AlgebraicGeometry Limits
open Work.GCBasics
open scoped Classical MonObj MonoidalCategory CartesianMonoidalCategory

universe u

noncomputable section

/-- **Galois descent for field-valued points, over a general base field.**

Let `k ⊆ K ⊆ N` be fields with `N/K` Galois, `X` a `k`-scheme and `p` an `N`-point of `X` whose
class in `X(N)` is fixed by every element of `Gal(N/K)`.  Then `p` is the base change along
`K → N` of a `K`-point of `X` (over `Spec k`).

This is the pointwise form of Galois descent: the residue field `κ(x)` at the image point `x` of
`p` is a `k`-algebra and `p` factors as `Spec e ≫ resPt X x` for a `k`-algebra map
`e : κ(x) → N`; invariance of `p` under `Gal(N/K)` says exactly that `σ ∘ e = e` for all `σ`, so
the image of `e` lies in the fixed field `K` of `N`, and `e` corestricts to a `k`-algebra map
`κ(x) → K` whose associated point is the required descent of `p`. -/
theorem exists_pt_descend_of_isGalois {k K N : Type u} [Field k] [Field K] [Field N]
    [Algebra k K] [Algebra k N] [Algebra K N] [IsScalarTower k K N] [IsGalois K N]
    {X : Sch k} (p : FPt X N)
    (hinv : ∀ τ : N ≃ₐ[K] N,
      Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ p.left = p.left) :
    ∃ q : FPt X K, RPt.map (IsScalarTower.toAlgHom k K N) q = p := by
  let x : X.left := p.left (IsLocalRing.closedPoint N)
  obtain ⟨e, he⟩ := Work.GroupChunk.exists_factor_resPt p
  have he' : p = RPt.map e (resPt X x) := he
  -- `e : κ(x) →ₐ[k] N` is fixed by every Galois automorphism of `N/K`
  have hfix : ∀ (τ : N ≃ₐ[K] N) (a : resField X x), τ (e a) = e a := by
    intro τ a
    have h2 : RPt.map ((τ.toAlgHom.restrictScalars k).comp e) (resPt X x) = p := by
      rw [RPt.map_comp, ← he']
      apply Over.OverMorphism.ext
      rw [RPt.map, Over.comp_left, specOfMap_left]
      exact hinv τ
    have h1 : RPt.map ((τ.toAlgHom.restrictScalars k).comp e) (resPt X x)
        = RPt.map e (resPt X x) := h2.trans he'
    have h3 := congrArg Over.Hom.left h1
    simp only [RPt.map, Over.comp_left, specOfMap_left, resPt_left] at h3
    have h4 := (cancel_mono (X.left.fromSpecResidueField x)).mp h3
    have h5 := Spec.map_injective h4
    have h6 := congrArg (fun (φ : CommRingCat.of (resField X x) ⟶ CommRingCat.of N) =>
      φ.hom a) h5
    simpa using h6
  -- so `e` maps into the fixed field `K` of `Gal(N/K)` in `N`
  have hker : ∀ a : resField X x, e a ∈ (IsScalarTower.toAlgHom k K N).range := fun a =>
    (InfiniteGalois.mem_range_algebraMap_iff_fixed (e a)).mpr (fun g => hfix g a)
  -- corestrict `e` to a `k`-algebra map `κ(x) → K`
  let f : K →ₐ[k] N := IsScalarTower.toAlgHom k K N
  have hf : Function.Injective f := (algebraMap K N).injective
  let Φ : K ≃ₐ[k] f.range := AlgEquiv.ofInjective f hf
  have hΦ : ∀ y : f.range, f (Φ.symm y) = (y : N) := by
    intro y
    have h2 : Φ (Φ.symm y) = y := Φ.apply_symm_apply y
    have h3 := congrArg Subtype.val h2
    rw [AlgEquiv.ofInjective_apply] at h3
    exact h3
  let d : resField X x →ₐ[k] K := Φ.symm.toAlgHom.comp (AlgHom.codRestrict e f.range hker)
  have hd : f.comp d = e := by
    ext a
    rw [AlgHom.comp_apply]
    exact hΦ ((AlgHom.codRestrict e f.range hker) a)
  refine ⟨RPt.map d (resPt X x), ?_⟩
  rw [← RPt.map_comp, he']
  exact congrArg (fun g => RPt.map g (resPt X x)) hd

theorem exists_genericSum_descend {k : Type u} [Field k] (C : Work.CurveBasics.Curve k)
    (h : C.functionField)
    {A : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k))}
    [CategoryTheory.GrpObj A] [CategoryTheory.IsCommMonObj A]
    [AlgebraicGeometry.IsSeparated A.hom] (f : C.toOver ⟶ A)
    (N : Type u) [Field N] [Algebra ↥(Work.KeyLemma.Curve.baseField C h) N] [Algebra k N]
    [IsScalarTower k ↥(Work.KeyLemma.Curve.baseField C h) N]
    [FiniteDimensional ↥(Work.KeyLemma.Curve.baseField C h) ↥C.functionField]
    [Algebra.IsSeparable ↥(Work.KeyLemma.Curve.baseField C h) ↥C.functionField]
    [IsGalois ↥(Work.KeyLemma.Curve.baseField C h) N]
    (hinv : ∀ τ : N ≃ₐ[↥(Work.KeyLemma.Curve.baseField C h)] N,
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
        Work.KeyLemma.Curve.genericSum (C := C) (h := h) (N := N) f
      = Work.KeyLemma.Curve.genericSum (C := C) (h := h) (N := N) f) :
    ∃ a : AlgebraicGeometry.Spec (CommRingCat.of ↥(Work.KeyLemma.Curve.baseField C h)) ⟶ A.left,
      a ≫ A.hom = AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap k ↥(Work.KeyLemma.Curve.baseField C h))) ∧
      AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap ↥(Work.KeyLemma.Curve.baseField C h) N)) ≫ a
        = Work.KeyLemma.Curve.genericSum (C := C) (h := h) (N := N) f := by
  obtain ⟨q, hq⟩ := exists_pt_descend_of_isGalois (k := k)
    (K := ↥(Work.KeyLemma.Curve.baseField C h)) (N := N) (X := A)
    (Work.KeyLemma.Curve.genericSumOver (C := C) (h := h) (N := N) f)
    (fun τ => hinv τ)
  refine ⟨q.left, ?_, ?_⟩
  · exact Over.w q
  · have h1 := congrArg Over.Hom.left hq
    simp only [RPt.map, Over.comp_left, specOfMap_left] at h1
    exact h1

end

end Work.KeyLemma.Curve
