/-
# Surjectivity of the Mayer–Vietoris comparison map onto the `(U,V)`-small chains

Let `X` be a topological space, `U V ⊆ X` subsets and `n : ℕ`.  The Mayer–Vietoris comparison map

`pushoutMap X U V : pushout (C(U∩V) → C(U)) (C(U∩V) → C(V)) ⟶ C(X)`

of `Submission.Work.SINGMV.Defs` is induced, on the pushout of the two inclusions
`C(U ∩ V) ⟶ C(U)` and `C(U ∩ V) ⟶ C(V)`, by the two maps `C(U) ⟶ C(X)` and `C(V) ⟶ C(X)`.

The present file proves that this map is *surjective* onto the subcomplex of `(U,V)`-small
chains `smallChain X n U V = smallSpan X n U ⊔ smallSpan X n V`, i.e. that every chain that is a
sum of simplices lying in `U` and simplices lying in `V` admits a lift through the pushout.  In
particular the comparison map is an isomorphism on small chains, which is the chain-level input
of the small-simplices Mayer–Vietoris theorem (Hatcher, Proposition 2.21).

## Contents

* `chainComplexMap_gen` : the chain map induced by a map of spaces `f : X ⟶ Y` sends the
  generator of a singular simplex `τ` to the generator of the composite `f ∘ τ`.
* `smallSpan_le_range` : every chain carried by `U` is the image of a chain of `U` under
  `C(U) ⟶ C(X)`; equivalently `smallSpan X n U ⊆ range (C_n(U) → C_n(X))`.
* `small_subset_pushout_range` : the target statement.

## Proof

The chain groups `C_n(X)` are the coproducts of one copy of `ℤ` per singular `n`-simplex, and
Mathlib's `SSet.ι_chainComplexMap_f` computes the induced chain map on the corresponding
coproduct inclusions.  Thus the generator attached to a simplex `σ : Δⁿ ⟶ X` with image in `U`
is the image of the generator attached to the corestriction `Δⁿ ⟶ U` of `σ`.  Writing
`z ∈ smallSpan X n U ⊔ smallSpan X n V` as `zU + zV`, one lifts `zU` and `zV` to `b ∈ C_n(U)` and
`c ∈ C_n(V)` and takes the pushout element `inl b + inr c`; the universal property
`pushout.inl_desc`/`pushout.inr_desc` identifies its image with `z`.
-/

import Mathlib
import Submission.Work.SINGMV.Defs
import Submission.Work.SingMV.smallSpan_inf

open CategoryTheory Limits Convexity
open scoped Simplicial

noncomputable section

namespace Work.SingMV

/-- The chain map induced by a morphism of spaces `f : X ⟶ Y` sends the generator of a singular
simplex `τ : Δⁿ ⟶ X` to the generator of the composite `f ∘ τ : Δⁿ ⟶ Y`. -/
lemma chainComplexMap_gen (X : TopCat) (n : ℕ) (U : Set X) (τ : singMap (TopCat.of U) n) :
    ((Submission.Blueprint.singC).map (Submission.Blueprint.inclTop U)).f n
        (gen (TopCat.of U) n τ)
      = gen X n ((Submission.Blueprint.inclTop U).hom.comp τ) := by
  change (SSet.chainComplexMap (TopCat.toSSet.map (Submission.Blueprint.inclTop U))
      (ModuleCat.of ℤ ℤ)).f n (gen (TopCat.of U) n τ)
    = gen X n ((Submission.Blueprint.inclTop U).hom.comp τ)
  have h := SSet.ι_chainComplexMap_f (X := TopCat.toSSet.obj (TopCat.of U))
    (Y := TopCat.toSSet.obj X) (f := TopCat.toSSet.map (Submission.Blueprint.inclTop U))
    (R := ModuleCat.of ℤ ℤ) ((singEquiv (TopCat.of U) n).symm τ)
  have h2 := congrArg (fun φ : (ModuleCat.of ℤ ℤ) ⟶
      (SSet.chainComplex (TopCat.toSSet.obj X) (ModuleCat.of ℤ ℤ)).X n =>
      ModuleCat.Hom.hom φ (1 : ℤ)) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  rw [gen, gen, h2]
  congr 1

/-- Every singular chain of `X` carried by `U` is the image of a singular chain of `U` under the
map `C_n(U) ⟶ C_n(X)` induced by the inclusion: `smallSpan X n U` is contained in the range of
`C_n(U) ⟶ C_n(X)`. -/
lemma smallSpan_le_range (X : TopCat) (n : ℕ) (U : Set X) :
    smallSpan X n U ≤
      LinearMap.range (((Submission.Blueprint.singC).map
        (Submission.Blueprint.inclTop U)).f n).hom := by
  rw [smallSpan, Submodule.span_le]
  rintro y ⟨σ, rfl⟩
  refine ⟨gen (TopCat.of U) n ⟨fun z => ⟨σ.1 z, σ.2 z⟩, by fun_prop⟩, ?_⟩
  rw [chainComplexMap_gen]
  congr 1

/-- **Small chains lie in the range of the Mayer–Vietoris comparison map.**  Every chain of `X`
that is a sum of simplices lying in `U` and simplices lying in `V` is the image, under
`pushoutMap X U V`, of a chain of the pushout
`pushout (C(U∩V) → C(U)) (C(U∩V) → C(V))`. -/
theorem small_subset_pushout_range (X : TopCat) (n : ℕ) (U V : Set X)
    (z : ((Submission.Blueprint.singC).obj X).X n)
    (hz : z ∈ Work.SingMV.smallChain X n U V) :
    ∃ w, (Work.SingMV.pushoutMap X U V).f n w = z := by
  rw [smallChain, Submodule.mem_sup] at hz
  obtain ⟨zU, hzU, zV, hzV, hsum⟩ := hz
  obtain ⟨b, hb⟩ := smallSpan_le_range X n U hzU
  obtain ⟨c, hc⟩ := smallSpan_le_range X n V hzV
  let F := (Submission.Blueprint.singC).map
    (Submission.Blueprint.incl (Set.inter_subset_left : U ∩ V ⊆ U))
  let G := (Submission.Blueprint.singC).map
    (Submission.Blueprint.incl (Set.inter_subset_right : U ∩ V ⊆ V))
  have h1 : CategoryTheory.Limits.pushout.inl F G ≫ (pushoutMap X U V)
      = (Submission.Blueprint.singC).map (Submission.Blueprint.inclTop U) :=
    CategoryTheory.Limits.pushout.inl_desc (f := F) (g := G) _ _ _
  have h2 : CategoryTheory.Limits.pushout.inr F G ≫ (pushoutMap X U V)
      = (Submission.Blueprint.singC).map (Submission.Blueprint.inclTop V) :=
    CategoryTheory.Limits.pushout.inr_desc (f := F) (g := G) _ _ _
  have h1n := congrArg (fun φ => φ.f n) h1
  have h2n := congrArg (fun φ => φ.f n) h2
  refine ⟨(pushout.inl F G).f n b + (pushout.inr F G).f n c, ?_⟩
  rw [map_add, ← hsum]
  have e1 : (pushoutMap X U V).f n ((pushout.inl F G).f n b) = zU := by
    rw [← ModuleCat.comp_apply, ← HomologicalComplex.comp_f, h1n, hb]
  have e2 : (pushoutMap X U V).f n ((pushout.inr F G).f n c) = zV := by
    rw [← ModuleCat.comp_apply, ← HomologicalComplex.comp_f, h2n, hc]
  rw [e1, e2]

end Work.SingMV
