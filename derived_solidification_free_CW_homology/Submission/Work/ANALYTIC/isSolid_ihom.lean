import Mathlib
import Submission.Work.ANALYTIC.Basic
import Submission.Work.ANALYTIC.CatAux.Basic
import Submission.Work.ANALYTIC.CatAux.bijective_tensor_precomp_curry

/-!
# F8: solidity is stable under internal homs

If `M` is a solid light condensed abelian group then so is `X ⟹ M` for every light condensed
abelian group `X`.

By definition (`ChallengeDeps`) `isSolid N` is `IsIso ((pre oneMinusShift).app N)`, so it suffices
to prove the following statement about an arbitrary braided monoidal closed category `C`:

> if `(pre S).app M` is an isomorphism, then so is `(pre S).app (X ⟹ M)`.

The proof has two ingredients.

*Bridge.* `(pre S).app M` is an isomorphism iff precomposition by `S ▷ W` is bijective on
`Hom(P ⊗ W, M)` for every `W`: this is the currying isomorphism
`Hom(P ⊗ W, M) ≅ Hom(W, P ⟹ M)` (`MonoidalClosed.uncurry`) together with
`MonoidalClosed.uncurry_pre_app`, which identifies postcomposition with `(pre S).app M` with
precomposition by `S ▷ W` (see `isIso_pre_app_iff_tensor_precomp`).

*Rearrangement.* The source objects `P ⊗ (X ⊗ Z)` and `X ⊗ (P ⊗ Z)` — the latter being the source
of `Hom(P ⊗ Z, X ⟹ M)` after currying the target `X ⟹ M` out — are canonically isomorphic
(associator, braiding), and the relevant precomposition maps correspond under this isomorphism
(see `Work.ANALYTIC.CatAux.bijective_tensor_precomp_curry`).  Hence bijectivity of the `W = X ⊗ Z`
instance of the bridge for `M` gives bijectivity of the `W = Z` instance of the bridge for `X ⟹ M`.
-/

open CategoryTheory Limits LightCondensed MonoidalCategory MonoidalClosed

namespace Work.ANALYTIC

universe u v

/-! ## The currying bridge between `(pre S).app M` and precomposition by `S ▷ W` -/

/-- **Currying bridge.**  `(pre S).app M` is an isomorphism (equivalently, postcomposition with it
is bijective on `Hom(W, P ⟹ M)` for every `W`) iff precomposition by `S ▷ W` is bijective on
`Hom(P ⊗ W, M)` for every object `W`.  This is `MonoidalClosed.uncurry_pre_app` read through the
currying bijection `Hom(P ⊗ W, M) ≅ Hom(W, P ⟹ M)` (`MonoidalClosed.uncurry`). -/
lemma isIso_pre_app_iff_tensor_precomp {C : Type u} [Category.{v, u} C] [MonoidalCategory C]
    {P : C} [Closed P] (S : P ⟶ P) (M : C) :
    IsIso ((pre S).app M) ↔
      ∀ W : C, Function.Bijective (fun (t : P ⊗ W ⟶ M) => (S ▷ W) ≫ t) := by
  have huncurry : ∀ W : C,
      Function.Bijective (fun (k : W ⟶ (ihom P).obj M) => uncurry k) := by
    intro W
    exact ⟨fun k₁ k₂ h => by
        change uncurry k₁ = uncurry k₂ at h
        rw [← curry_uncurry k₁, ← curry_uncurry k₂, h],
      fun t => ⟨curry t, uncurry_curry t⟩⟩
  have hconj : ∀ W : C,
      Function.Bijective (fun (k : W ⟶ (ihom P).obj M) => k ≫ (pre S).app M) ↔
        Function.Bijective (fun (t : P ⊗ W ⟶ M) => (S ▷ W) ≫ t) := by
    intro W
    refine CatAux.bijective_of_conj (e := fun (k : W ⟶ (ihom P).obj M) => uncurry k)
      (huncurry W) ?_
    intro k
    exact uncurry_pre_app M k S
  rw [isIso_iff_yoneda_map_bijective]
  exact forall_congr' fun W => hconj W

/-! ## Solidity is stable under internal homs -/

/-- **F8, general form.**  In a braided monoidal closed category, if `(pre S).app M` is an
isomorphism then so is `(pre S).app (X ⟹ M)`.

The `W = X ⊗ Z` instance of the bridge `isIso_pre_app_iff_tensor_precomp` for `M` gives
bijectivity of precomposition by `S` in the first tensor factor on `Hom(P ⊗ (X ⊗ Z), M)`; the
rearrangement `Work.ANALYTIC.CatAux.bijective_tensor_precomp_curry` transports this to the `W = Z`
instance of the bridge for `X ⟹ M`, which is `IsIso ((pre S).app (X ⟹ M))`. -/
theorem isIso_pre_ihom {C : Type u} [Category.{v, u} C] [MonoidalCategory C] [BraidedCategory C]
    [MonoidalClosed C] (X P M : C) (S : P ⟶ P) (hM : IsIso ((pre S).app M)) :
    IsIso ((pre S).app ((ihom X).obj M)) := by
  refine (isIso_pre_app_iff_tensor_precomp (P := P) S ((ihom X).obj M)).mpr fun Z => ?_
  exact (CatAux.bijective_tensor_precomp_curry P X M Z S).mp
    ((isIso_pre_app_iff_tensor_precomp (P := P) S M).mp hM (X ⊗ Z))

/-- **F8 (REFS/01): solidity is stable under internal homs.**  If `M` is a solid light condensed
abelian group then `X ⟹ M` is solid for every light condensed abelian group `X`.

`isSolid N` is (by definition, `ChallengeDeps`) `IsIso ((MonoidalClosed.pre oneMinusShift).app N)`.
Writing `P` for `LightCondensed.P` and `S` for `oneMinusShift : P ⟶ P`, Mathlib's currying
isomorphism `Hom(P ⊗ Y, M) ≅ Hom(Y, P ⟹ M)` (`MonoidalClosed.curry`, `uncurry`,
`curry_pre_app`, `uncurry_pre_app`) turns postcomposition with `(pre S).app M` into precomposition
with `S ⊗ id_Y`.  Consequently an isomorphism `(pre S).app M` makes `S ⊗ id_Y` act bijectively on
`Hom(P ⊗ Y, M)` for every `Y`; running the same currying argument twice (with `Y = X ⊗ Z`) shows
that postcomposition with `(pre S).app (X ⟹ M)` is bijective on `Hom(Z, P ⟹ (X ⟹ M))` for every
`Z`, and a morphism `g` is an isomorphism as soon as postcomposition with it is bijective for the
sources/targets involved, which finishes the proof.

A useful equivalent intermediate step: `HasSubobject`-free swap iso
`MonoidalClosed.ihom (P ⊗ X) ≅ (ihom X) ⋙ (ihom P)` (equivalently `curry`/`uncurry` on
`P ⊗ X`) conjugates `pre (oneMinusShift ⊗ₘ 𝟙 X)` with `(ihom X).map (pre oneMinusShift)`, so the
`M`-component of the former is an isomorphism as soon as the latter is. -/
theorem isSolid_ihom (X M : LightCondAb) (hM : LightCondensed.isSolid M) :
    LightCondensed.isSolid ((ihom X).obj M) :=
  isIso_pre_ihom X P M oneMinusShift hM

end Work.ANALYTIC
