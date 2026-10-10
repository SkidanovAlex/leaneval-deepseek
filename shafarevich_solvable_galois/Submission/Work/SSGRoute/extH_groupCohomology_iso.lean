import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Submission.Work.SSGRoute.eCoh_delta
import Submission.Work.SSGRoute.eCoh_map
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/SSGRoute/DESIGN_EXT.md (the lead's Ext-core design for Poitou–Tate) + DESIGN_PT.md. Definitions: Submission/Work/SSGRoute/PTDefs.lean (namespace SSGRoute.PTExt; do NOT edit). NK.* CFT library available. Siblings run in parallel.

# E0b `extH_groupCohomology_iso` — group cohomology is `Ext`-cohomology (Mathlib glue)

**Statement.** For every `n`, additive isomorphisms `e n G A : Hⁿ(G, A) ≃+ extH A n = Extⁿ_G(ℤ, A)`
(for `A : Rep Coeff G`, `Coeff = ULift ℤ`) that are
1. compatible with every change of group `f : H →* G` followed by a coefficient map `φ`, so
   `e (groupCohomology.map f φ n y) = extHMap f φ (e y)`;
2. compatible up to sign with connecting maps: `e (δ y) = ± (e y).comp hS.extClass`.

**Why it is needed.** NK proves everything about `C_L` in `groupCohomology`: `H¹ = 0` (H1All), the
fundamental class, `|H²| ≤ [L:k]`, and inflation–restriction (Commons). The `Ext` core computes with
Yoneda products. E3–E9 move between the two through this node.

**Route.**
- Mathlib already has `groupCohomologyIsoExt` (classical `Ext` via the bar resolution) and
  `ProjectiveResolution.extEquivCohomologyClass` (derived `Abelian.Ext` ≃ cohomology classes of
  `Hom(P, A)`). Compose them through `Rep.standardResolution`, identifying the homology of
  `linearYonedaObj` with `HomComplex.CohomologyClass`.
- Clause 1, coefficient part: naturality of both isomorphisms in `A`.
- Clause 1, group part: compare the bar resolutions along `f`. `extHMap` is `mapExactFunctor (res f)`
  followed by precomposition with `unitRes f`.
- Clause 2: `ShortExact.extClass` is the connecting map (`extClass_hom = singleδ`), and group
  cohomology's `δ` is the snake connecting map. The sign is allowed to go either way.

**Size.** 0.8–1.5k. **Risk:** medium, pure Mathlib API work (universe bookkeeping between
`Rep.{0}` and `HasExt.{0}`).

**Imports.** `Submission.Work.SSGRoute.PTDefs`.
-/

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

/-- **E0b.** Group cohomology is `Ext`-cohomology: for every `n` there are additive isomorphisms
`Hⁿ(G, A) ≃ Extⁿ_G(ℤ, A)` for all groups `G` and all `A : Rep ℤ G`, compatible with every change
of group `f : H →* G` followed by a coefficient map (so with coefficient maps, restriction and
inflation), and compatible up to sign with the connecting maps of short exact sequences. -/
theorem extH_groupCohomology_iso :
    ∃ e : ∀ (n : ℕ) (G : Type) [Group G] (A : Rep Coeff G), groupCohomology A n ≃+ extH A n,
      (∀ (n : ℕ) (G H : Type) [Group G] [Group H] (f : H →* G) (A : Rep Coeff G)
          (B : Rep Coeff H) (φ : Rep.res f A ⟶ B) (y : groupCohomology A n),
          e n H B ((groupCohomology.map f φ n).hom y) = extHMap f φ (e n G A y)) ∧
      ∀ (n : ℕ) (G : Type) [Group G] (S : ShortComplex (Rep Coeff G)) (hS : S.ShortExact)
          (y : groupCohomology S.X₃ n),
          e (n + 1) G S.X₁ ((groupCohomology.δ hS n (n + 1) rfl).hom y) =
              (e n G S.X₃ y).comp hS.extClass rfl ∨
            e (n + 1) G S.X₁ ((groupCohomology.δ hS n (n + 1) rfl).hom y) =
              -((e n G S.X₃ y).comp hS.extClass rfl) := by
  refine ⟨SSGRoute.PTExt.eCoh, ?_, ?_⟩
  · intro n G H _ _ f A B φ y
    exact eCoh_map n G H f A B φ y
  · intro n G _ S hS y
    exact eCoh_delta n G S hS y

end Work.SSGRoute
