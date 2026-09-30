import Mathlib
import Submission.Work.DeltaHomology.RealizationDefs
import Submission.Work.DeltaHomology.ChainDefs
import Submission.Work.DeltaHomology.chi_injective
import Submission.Work.Homology.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.DeltaHomology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Convexity Work.Homology
open scoped Simplicial

/-! ## An abstract monomorphism criterion for coproducts of `ℤ`

The comparison map of the next lemma is the `Sigma.desc` of a family of coprojections
`ι (f i)`, and such a morphism is (split) injective as soon as the indexing map `f`
is injective: the coproduct over `β` retracts onto the coproduct over `ι` by sending
the summand `b` either to the *unique* summand `i` with `f i = b` or to zero.  This is
the categorical form of "the images of distinct basis vectors are distinct basis
vectors", and it is the only ingredient of `deltaChainMapFun_mono`. -/

/-- **A `Sigma.desc` of coprojections along an injective family of indices is a mono.**
If `f : ι → β` is injective then the map `∐_{i} ℤ ⟶ ∐_{b} ℤ` sending the `i`-th copy
of `ℤ` isomorphically onto the `f i`-th copy of `ℤ` is a split monomorphism (the
coproduct over `ι` is a direct summand of the coproduct over `β`). -/
theorem sigma_desc_ι_mono {ι β : Type} (f : ι → β) (hf : Function.Injective f) :
    Mono (Sigma.desc (fun i : ι => Sigma.ι (fun _ : β => Work.Homology.ZMod) (f i))) := by
  classical
  -- The retraction: the `b`-th summand goes to the (unique) `i` with `f i = b`, or to `0`.
  let g : (∐ (fun _ : β => Work.Homology.ZMod)) ⟶ (∐ (fun _ : ι => Work.Homology.ZMod)) :=
    Sigma.desc (fun b : β => if h : ∃ i, f i = b
      then Sigma.ι (fun _ : ι => Work.Homology.ZMod) (Classical.choose h) else 0)
  have hsplit : Sigma.desc (fun i : ι => Sigma.ι (fun _ : β => Work.Homology.ZMod) (f i)) ≫ g
      = 𝟙 (∐ (fun _ : ι => Work.Homology.ZMod)) := by
    -- It suffices to check the composition on the coprojections.
    apply Sigma.hom_ext
    intro i
    rw [← Category.assoc, Sigma.ι_comp_desc]
    simp only [g, Sigma.ι_comp_desc]
    -- On the `i`-th summand the retraction selects `Classical.choose ⟨i, rfl⟩`, which
    -- is `i` by injectivity of `f`.
    rw [dite_eq_left (show ∃ i', f i' = f i from ⟨i, rfl⟩),
      hf (Classical.choose_spec (show ∃ i', f i' = f i from ⟨i, rfl⟩)), Category.comp_id]
  exact SplitMono.mono { retraction := g, id := hsplit }

/-- **The comparison map on chains is degreewise injective.**  For a *realization* `R`, the
degree-`k` component `deltaChainMapFun χ k : K.chainX k ⟶ C_k(X)` is the `Sigma.desc` of the
basis inclusions `σ ↦ χ σ`; since distinct simplices have distinct characteristic maps
(`chi_injective`), the images of the basis vectors are pairwise distinct basis elements of the
singular chain module, so the map is injective, i.e. a monomorphism in `ModuleCat ℤ`.

Route: prove `Function.Injective (ModuleCat.Hom.hom (R.toDeltaSimplexMap.deltaChainMapFun k))`
and use `ModuleCat.mono_iff_injective`.  Use `Limits.Sigma.ι_comp_desc` /
`deltaChainMapFun_chainι` to compute the map on basis elements and `chi_injective` to see that
distinct indices give distinct basis elements of the singular chain module; conclude by
expressing an element of the coproduct through its components
(`ModuleCat.coprodIsoDirectSum`, `DirectSum.ext_component`) or by linear independence of the
distinct basis elements. -/
theorem deltaChainMapFun_mono {K : DeltaCx} {X : TopCat} (R : DeltaRealization K X) (k : ℕ) :
    Mono (R.toDeltaSimplexMap.deltaChainMapFun k) := by
  -- Distinct simplices give distinct singular simplices of `X` (not merely distinct
  -- characteristic maps), because `cls` is `χ` read through the equivalence
  -- `TopCat.toSSetObjEquiv`.
  have hχ : Function.Injective (fun σ : Fin (K.card k) => R.toDeltaSimplexMap.χ k σ) := by
    intro σ τ h
    apply chi_injective R k
    exact congrArg (TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk k))) h
  -- `deltaChainMapFun` is by definition the `Sigma.desc` of the coprojections onto the
  -- corresponding summands of the singular chain module.
  have hmain : R.toDeltaSimplexMap.deltaChainMapFun k
      = Limits.Sigma.desc (fun σ : Fin (K.card k) =>
          Limits.Sigma.ι (fun _ : (TopCat.toSSet.obj X).obj
            (Opposite.op (SimplexCategory.mk k)) => Work.Homology.ZMod)
            (R.toDeltaSimplexMap.χ k σ)) := rfl
  rw [hmain]
  exact sigma_desc_ι_mono _ hχ

end Work.DeltaHomology
