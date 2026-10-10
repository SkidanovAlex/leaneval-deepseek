import Mathlib.RepresentationTheory.Induced
import Mathlib.Tactic.Have
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Submission.Work.SSGRoute.E1cGeneric.freeCoverCompat_comp
import Submission.Work.SSGRoute.E1cGeneric.freeCoverCompat_single
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# (i) `PhiE`-compat: the comparison of the two canonical presentations along `φ : H →* G`

`freeCoverSES X` is the canonical presentation

    freeCoverSES X : 0 → R → F ⟶ X → 0
        (R = kernel (freeCover X),  F = Rep.free Coeff G X.V)

of a `G`-representation `X`, built from the canonical cover `freeCover X` (no `Classical.choose`,
so that it is functorial, see `Work.SSGRoute.ExtChain.FreeCover`).  For a group homomorphism
`φ : H →* G` there are two presentations of the same restricted module `Rep.res φ X`:

* `freeCoverSES (Rep.res φ X)` — the canonical presentation of the *restriction*, whose middle term
  is the free `ℤ[H]`-module `Rep.free Coeff H X.V`;
* `(freeCoverSES X).map (Rep.resFunctor φ)` — the *restriction* of the canonical presentation of
  `X`, whose middle term is `Rep.res φ (Rep.free Coeff G X.V)`, a different free `ℤ[H]`-module
  (measured in `PT/NOTE_e1aChainC_localComparison.md` §11.3).

The canonical comparison of these two presentations is the map of complexes which is given on the
middle terms by `freeCoverCompat φ X` (`PT/freeCoverCompat.lean`) and is the identity on the third
term.  This file constructs that map of complexes: its existence is what allows the connecting
classes of the two presentations (the `PhiE` of the E1a comparison square) to be compared, which
`bijective_extClass_precomp_map` reduces the `h1Transfer`-step of (i) to.

The only input needed besides the (already proved) cover-compatibility square
`freeCoverCompat_comp` is that restriction of representations is exact, so that the restriction of
the kernel of the canonical cover of `X` is (canonically) the kernel of the restriction of that
cover: Mathlib's `PreservesKernel.iso` for the exact functor `Rep.resFunctor φ`.  The left hand
column of the comparison is then produced by the universal property of the kernel
(`exists_tau1_of_kernel` below).
-/

namespace Work.SSGRoute.PT

open CategoryTheory CategoryTheory.Limits SSGRoute.PTExt

/-- **The third column of a morphism of short complexes, from the second and third ones.**
Given `τ₂ : S.X₂ ⟶ T.X₂` and `τ₃ : S.X₃ ⟶ T.X₃` with `τ₂ ≫ T.g = S.g ≫ τ₃`, and an
identification `e : T.X₁ ≅ kernel T.g` of the first term of `T` with the kernel of `T.g`
(compatible with `T.f`), there is a unique `τ₁ : S.X₁ ⟶ T.X₁` making the left square commute.
Indeed `S.f ≫ τ₂` is killed by `T.g`, because `S.f ≫ S.g = 0`: it therefore factors through
`kernel T.g`, and `e.inv` carries that factor back to `T.X₁`. -/
lemma exists_tau1_of_kernel {C : Type*} [Category C] [HasZeroMorphisms C]
    {S T : ShortComplex C} (τ₂ : S.X₂ ⟶ T.X₂) (τ₃ : S.X₃ ⟶ T.X₃)
    (h : τ₂ ≫ T.g = S.g ≫ τ₃) [HasKernel T.g]
    (e : T.X₁ ≅ kernel T.g) (he : e.inv ≫ T.f = kernel.ι T.g) :
    ∃ τ₁ : S.X₁ ⟶ T.X₁, τ₁ ≫ T.f = S.f ≫ τ₂ := by
  refine ⟨kernel.lift T.g (S.f ≫ τ₂) ?_ ≫ e.inv, ?_⟩
  · rw [Category.assoc, h, ← Category.assoc, S.zero, zero_comp]
  · rw [Category.assoc, he, kernel.lift_ι]

/-- **The canonical comparison of the two canonical presentations of `Rep.res φ X`.**  There is a
morphism of short complexes from the canonical presentation of the restricted module to the
restriction of the canonical presentation of `X`, whose middle component is the canonical
comparison of the two covers `freeCoverCompat φ X` and whose third component is the identity. -/
theorem freeCoverSES_res_comparison {G H : Type} [Group G] [Group H] (φ : H →* G)
    (X : Rep.{0} SSGRoute.PTExt.Coeff G) :
    ∃ Φ : CategoryTheory.ShortComplex.Hom (Work.SSGRoute.freeCoverSES (Rep.res φ X))
        ((Work.SSGRoute.freeCoverSES X).map (Rep.resFunctor φ)),
      Φ.τ₂ = Work.SSGRoute.PT.freeCoverCompat φ X ∧
        Φ.τ₃ = CategoryTheory.CategoryStruct.id (Rep.res φ X) := by
  let F : Rep.{0} Coeff G ⥤ Rep.{0} Coeff H := Rep.resFunctor (k := Coeff) φ
  let S : ShortComplex (Rep.{0} Coeff H) := Work.SSGRoute.freeCoverSES (Rep.res φ X)
  let T : ShortComplex (Rep.{0} Coeff H) := (Work.SSGRoute.freeCoverSES X).map F
  -- the right hand square: `freeCoverCompat_comp`
  have h23 : freeCoverCompat φ X ≫ T.g = S.g ≫ 𝟙 (Rep.res φ X) := by
    dsimp only [T, S]
    rw [Category.comp_id]
    exact E1cGeneric.freeCoverCompat_comp φ X
  -- the left hand column, from the kernel universal property: `T.X₁ = F (kernel (freeCover X))`
  -- is the kernel of `T.g = F (freeCover X)`, because `F = Rep.resFunctor φ` preserves limits.
  obtain ⟨τ₁, hτ₁⟩ : ∃ τ₁ : S.X₁ ⟶ T.X₁, τ₁ ≫ T.f = S.f ≫ freeCoverCompat φ X :=
    exists_tau1_of_kernel (S := S) (T := T) (freeCoverCompat φ X) (𝟙 (Rep.res φ X)) h23
      (e := PreservesKernel.iso F (Work.SSGRoute.freeCover X))
      (he := PreservesKernel.iso_inv_ι F (Work.SSGRoute.freeCover X))
  exact ⟨{ τ₁ := τ₁, τ₂ := freeCoverCompat φ X, τ₃ := 𝟙 (Rep.res φ X),
           comm₁₂ := hτ₁, comm₂₃ := h23 }, rfl, rfl⟩

end Work.SSGRoute.PT
