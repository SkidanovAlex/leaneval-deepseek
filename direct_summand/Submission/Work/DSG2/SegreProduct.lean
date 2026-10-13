import Mathlib
import Submission.Work.DSMap.Map
import Submission.Work.DSG2.Defs
import Submission.Work.DSG2.exists_segre_product_u

/-!
# DSG2: the ambient projective product of `m` copies of `ℙ^n_A`

This file packages the output of `Work.DSG2.exists_segre_product_u` as a structure, so that the
Chow construction can take a single object instead of repeatedly destructuring an existential.

`SegreProductData A n m` bundles a scheme `P` which is an `m`-fold product of `ℙ^n_A` over
`Spec A` (with its universal property and proper projections), together with a closed immersion
of `P` into a projective space `ℙ^N_A` over `Spec A`.  The existence statement
`nonempty_segreProductData` follows immediately from `Work.DSG2.exists_segre_product_u`
(applied to `HasSegre.toHyp`, which is `Work.DSG2.segreEmbedding` reindexed); it is stated in
`Submission/Work/DSG2/Chow.lean` once the two are available.

-/

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace Work.DSG2

open LeanEval.AlgebraicGeometry.DirectSummand

/-- A packaged `m`-fold product of `ℙ^n_A` over `Spec A`, embedded as a closed subscheme of a
projective space over `A`.  The `liftSpec` field is the (weak) universal property of the
product. -/
structure SegreProductData (A : Type u) [CommRing A] (n m : ℕ) where
  /-- the product scheme -/
  P : Scheme.{u}
  /-- its structure morphism -/
  π : P ⟶ Spec (.of A)
  /-- the projections -/
  p : Fin m → (P ⟶ DSMap.PSpace A n)
  /-- the projections are morphisms over `Spec A` -/
  proj_compat : ∀ j, p j ≫ DSMap.PSpace.toSpec A n = π
  /-- the projections are proper -/
  proj_proper : ∀ j, IsProper (p j)
  /-- the structure morphism is proper -/
  struct_proper : IsProper π
  /-- the universal property of the product (existence form) -/
  liftSpec : ∀ (Q : Scheme.{u}) (q : Fin m → (Q ⟶ DSMap.PSpace A n))
    (πQ : Q ⟶ Spec (.of A)), (∀ j, q j ≫ DSMap.PSpace.toSpec A n = πQ) →
    ∃ u : Q ⟶ P, u ≫ π = πQ ∧ ∀ j, u ≫ p j = q j
  /-- the target projective space -/
  N : ℕ
  /-- the closed immersion into projective space -/
  i : P ⟶ DSMap.PSpace A N
  /-- it is a closed immersion -/
  isClosed_proj : IsClosedImmersion i
  /-- it is a morphism over `Spec A` -/
  struct_compat : i ≫ DSMap.PSpace.toSpec A N = π

/-- The two-factor Segre embedding (`Work.DSG2.segreEmbedding`), in the exact shape needed to
build `SegreProductData`. -/
def HasSegre (A : Type u) [CommRing A] : Prop :=
  ∀ (a b : ℕ),
    ∃ (σ : Limits.pullback (DSMap.PSpace.toSpec A a) (DSMap.PSpace.toSpec A b) ⟶
        DSMap.PSpace A ((a + 1) * (b + 1) - 1)),
      IsClosedImmersion σ ∧
        σ ≫ DSMap.PSpace.toSpec A ((a + 1) * (b + 1) - 1) =
          Limits.pullback.fst (DSMap.PSpace.toSpec A a) (DSMap.PSpace.toSpec A b) ≫
            DSMap.PSpace.toSpec A a

/-- `m`-fold products of `ℙ^n_A` with a projective embedding exist, given the two-factor Segre
embedding. -/
theorem nonempty_segreProductData (A : Type u) [CommRing A] (n m : ℕ) (hm : 0 < m)
    (h2 : HasSegre A) : Nonempty (SegreProductData A n m) := by
  obtain ⟨P, π, p, hover, hproper, hproperπ, hlift, N, i, hclosed, hcompat⟩ :=
    exists_segre_product_u A n m hm h2
  refine ⟨⟨P, π, p, hover, hproper, hproperπ, fun Q q πQ hq => ?_, N, i, hclosed, hcompat⟩⟩
  obtain ⟨u, hu, _⟩ := hlift Q q πQ hq
  exact ⟨u, hu.1, hu.2⟩

end Work.DSG2
