import Mathlib
import Submission.Work.GroupChunk.exists_factor_resPt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.Descent

open CategoryTheory AlgebraicGeometry
open Work.GCBasics

universe u

/-- **Galois descent for points.**  Let `N/F` be a Galois extension (possibly infinite), `X` a
scheme separated over `F`, and `g : Spec N ⟶ X` a point of `X` over `Spec F` which is fixed by
every Galois automorphism of `N/F`.  Then `g` descends to an `F`-point of `X`.

The proof factors `g` through the canonical point `Spec κ(x) ⟶ X` at its image point `x`
(`Work.GroupChunk.exists_factor_resPt`), so that `g` is the base change of `resPt X x` along an
`F`-algebra map `e : κ(x) → N`.  Fixing `g` by `σ` means precisely `σ ∘ e = e`, so the image of
`e` lies in the Galois fixed field of `N/F`, which is `F` (`InfiniteGalois.mem_range_algebraMap_iff_fixed`).
Hence `e` corestricts to an `F`-algebra map `d : κ(x) → F`, and `resPt X x` pushed forward along
`d` is the required `F`-point. -/
theorem galoisDescent_point {F N : Type u} [Field F] [Field N] [Algebra F N] [IsGalois F N]
    {X : AlgebraicGeometry.Scheme} (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of F))
    [AlgebraicGeometry.IsSeparated f]
    (g : AlgebraicGeometry.Spec (CommRingCat.of N) ⟶ X)
    (hg : CategoryTheory.CategoryStruct.comp g f =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap F N)))
    (hinv : ∀ σ : N ≃ₐ[F] N,
      CategoryTheory.CategoryStruct.comp
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom σ.toRingHom)) g = g) :
    ∃ y : AlgebraicGeometry.Spec (CommRingCat.of F) ⟶ X,
      CategoryTheory.CategoryStruct.comp y f = CategoryTheory.CategoryStruct.id _ ∧
      g = CategoryTheory.CategoryStruct.comp
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap F N))) y := by
  let X' : Sch F := Over.mk f
  let p : FPt X' N := Over.homMk g hg
  let x : X := p.left (IsLocalRing.closedPoint N)
  obtain ⟨e, he⟩ := Work.GroupChunk.exists_factor_resPt p
  have hp_left : p.left = g := rfl
  -- Galois invariance of `p`
  have hmap : ∀ σ : N ≃ₐ[F] N, RPt.map (σ : N →ₐ[F] N) p = p := by
    intro σ
    apply Over.OverMorphism.ext
    rw [RPt.map, Over.comp_left, specOfMap_left, hp_left]
    exact hinv σ
  -- hence `σ ∘ e = e` for every `σ`
  have hfix : ∀ σ : N ≃ₐ[F] N, ∀ a : resField X' x, σ (e a) = e a := by
    intro σ a
    have h1 : RPt.map ((σ : N →ₐ[F] N).comp e) (resPt X' x) = RPt.map e (resPt X' x) := by
      rw [RPt.map_comp e (σ : N →ₐ[F] N) (resPt X' x), ← he]
      exact hmap σ
    have h2 := congrArg Over.Hom.left h1
    simp only [RPt.map, Over.comp_left, specOfMap_left, resPt_left] at h2
    have h3 : Spec.map (CommRingCat.ofHom ((σ : N →ₐ[F] N).comp e).toRingHom)
        = Spec.map (CommRingCat.ofHom e.toRingHom) :=
      (cancel_mono (X.fromSpecResidueField x)).mp h2
    have h4 : CommRingCat.ofHom ((σ : N →ₐ[F] N).comp e).toRingHom
        = CommRingCat.ofHom e.toRingHom :=
      Spec.map_inj.mp h3
    have h5 := congrArg
      (fun (φ : CommRingCat.of (resField X' x) ⟶ CommRingCat.of N) => φ a) h4
    simpa using h5
  -- the image of `e` lies in the Galois fixed field, which is `F`
  have hmem : ∀ a : resField X' x, e a ∈ Set.range (algebraMap F N) := fun a =>
    (InfiniteGalois.mem_range_algebraMap_iff_fixed (e a)).mpr (fun σ => hfix σ a)
  have hker : ∀ a : resField X' x, e a ∈ (⊥ : Subalgebra F N) := fun a =>
    Algebra.mem_bot.mpr (hmem a)
  -- corestrict `e` to an `F`-algebra map `d : κ(x) → F`
  let e' : resField X' x →ₐ[F] (⊥ : Subalgebra F N) := AlgHom.codRestrict e ⊥ hker
  let d : resField X' x →ₐ[F] F := (Algebra.botEquiv F N).toAlgHom.comp e'
  have hkey : ∀ t : (⊥ : Subalgebra F N),
      algebraMap F N (Algebra.botEquiv F N t) = (t : N) := by
    intro t
    have h := (Algebra.botEquiv F N).symm_apply_apply t
    rw [Algebra.botEquiv_symm_apply] at h
    simpa using congrArg Subtype.val h
  have hd : (Algebra.ofId F N).comp d = e := by
    apply AlgHom.ext
    intro a
    rw [AlgHom.comp_apply, Algebra.ofId_apply]
    rw [show d a = Algebra.botEquiv F N (e' a) from rfl, hkey (e' a)]
    simp [e']
  -- the descended point
  let y : specOf F F ⟶ X' := RPt.map d (resPt X' x)
  have hqy : specOfMap (Algebra.ofId F N) ≫ y = p := by
    show specOfMap (Algebra.ofId F N) ≫ (specOfMap d ≫ resPt X' x) = p
    rw [← Category.assoc, ← specOfMap_comp, hd]
    exact he.symm
  refine ⟨y.left, ?_, ?_⟩
  · -- `y` is an `F`-point
    have hw := Over.w y
    have hFF : (specOf F F).hom = 𝟙 (Spec (CommRingCat.of F)) := by rw [specOf_hom]; simp
    rw [hFF] at hw
    exact hw
  · -- `g` is the base change of `y`
    have h1 := congrArg Over.Hom.left hqy
    rw [Over.comp_left, specOfMap_left] at h1
    rw [show (Algebra.ofId F N).toRingHom = algebraMap F N from rfl, hp_left] at h1
    exact h1.symm

end Work.Descent
