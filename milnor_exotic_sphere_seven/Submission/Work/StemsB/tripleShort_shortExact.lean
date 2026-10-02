import Mathlib
import Submission.Work.StemsB.TripleSequence
import Submission.Work.Cohomology.pd_plumbing
import Submission.Work.Cohomology.HomologyPairSequence

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The short exact sequence of a triple of subsets

For `C ⊆ A ⊆ X` the relative singular chain complexes fit into the short exact sequence

`0 ⟶ C_*(A,C) ⟶ C_*(X,C) ⟶ C_*(X,A) ⟶ 0`

with the maps `Work.Cohomology.relChainsMap X A C` and `Work.Cohomology.relChainsSubMap X C A hCA`
of the workspace's `Submission/Work/StemsB/TripleSequence.lean`.  Here

* `C_*(X,C) = coker (inclChains X C)`,
* `C_*(X,A) = coker (inclChains X A)`,
* `C_*(A,C) = coker (inclChains (TopCat.of A) {y : A | (y : X) ∈ C})`

(the two models `{y : A | (y : X) ∈ C}` and `C` of the relative chains of the pair `(A,C)` are
related by the canonical homeomorphism `{y : A | (y : X) ∈ C} ≅ C`).

## Main results

* `shortExact_of_cokernelMap` — the general abelian-category statement: for morphisms
  `α : K' ⟶ P`, `p : K' ⟶ K` (`p` an isomorphism), `γ : P ⟶ L` (a mono) and `β : K ⟶ L` with
  `α ≫ γ = p ≫ β`, the cokernel sequence `coker α ⟶ coker β ⟶ coker γ` is short exact;
* `tripleShort_shortExact` — the statement for a triple of subsets.
-/

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.StemsB

noncomputable section

/-! ## 1. The general lemma -/

/-- **The cokernel sequence of a "triple" of morphisms.**  For an abelian category `C` and
morphisms `α : K' ⟶ P`, `p : K' ⟶ K` (an isomorphism), `γ : P ⟶ L` (a monomorphism) and
`β : K ⟶ L` with `α ≫ γ = p ≫ β`, the sequence

`coker α ⟶ coker β ⟶ coker γ`

(induced by `γ` and by the identity of `L`) is short exact.  This is the general form of the exact
sequence of a triple: the point is that the first object is `coker α` itself, with the isomorphism
`p` relating `α` to the "honest" inclusion `K ⟶ P`.

The comparison with `Work.Cohomology.shortExact_cokernel_map` is that there the first leg is an
identity, so that the first term is `coker (inclChainsSub X A B hAB)`; here an isomorphism on the
first leg is allowed, which is what is needed for the model
`C_*(A,C) = coker (inclChains (TopCat.of A) {y : A | (y : X) ∈ C})`. -/
theorem shortExact_of_cokernelMap {C : Type*} [Category C] [Abelian C]
    {K' P K L : C} (α : K' ⟶ P) (p : K' ⟶ K) [IsIso p] (γ : P ⟶ L) [Mono γ]
    (β : K ⟶ L) (w : α ≫ γ = p ≫ β) (hβ : β ≫ cokernel.π γ = 0) :
    (ShortComplex.mk (cokernel.map α β p γ w) (cokernel.desc β (cokernel.π γ) hβ)
      (by
        apply (cancel_epi (cokernel.π α)).mp
        rw [← Category.assoc, cokernel.map, cokernel.π_desc, Category.assoc, cokernel.π_desc,
          cokernel.condition, comp_zero])).ShortExact := by
  let f : cokernel α ⟶ cokernel β := cokernel.map α β p γ w
  let g : cokernel β ⟶ cokernel γ := cokernel.desc β (cokernel.π γ) hβ
  have hfπ : cokernel.π α ≫ f = γ ≫ cokernel.π β := by
    change cokernel.π α ≫ cokernel.map α β p γ w = γ ≫ cokernel.π β
    rw [cokernel.map, cokernel.π_desc]
  have hgπ : cokernel.π β ≫ g = cokernel.π γ := by
    change cokernel.π β ≫ cokernel.desc β (cokernel.π γ) hβ = cokernel.π γ
    rw [cokernel.π_desc]
  have hzero : f ≫ g = 0 := by
    change cokernel.map α β p γ w ≫ cokernel.desc β (cokernel.π γ) hβ = 0
    apply (cancel_epi (cokernel.π α)).mp
    rw [← Category.assoc, cokernel.map, cokernel.π_desc, Category.assoc, cokernel.π_desc,
      cokernel.condition, comp_zero]
  -- the square `K' ⟶ P ⟶ L`, `K' ⟶ K ⟶ L` is a pullback: `p` is an isomorphism and `γ` a mono
  have hpb : IsPullback α p γ β := by
    refine IsPullback.mk' w ?_ ?_
    · intro T φ φ' h1 h2
      exact (cancel_mono p).mp h2
    · intro T a b hab
      refine ⟨b ≫ inv p, ?_, ?_⟩
      · apply (cancel_mono γ).mp
        rw [Category.assoc]
        rw [w]
        rw [Category.assoc b (inv p) (p ≫ β)]
        rw [IsIso.inv_hom_id_assoc, hab.symm]
      · rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hmono : Mono f := Abelian.mono_cokernel_map_of_isPullback hpb
  have hepi : Epi g := cokernel.desc_epi β (cokernel.π γ) hβ
  have hcolim : IsColimit (CokernelCofork.ofπ g hzero) := by
    refine Cofork.IsColimit.mk _ (fun s => cokernel.desc γ (cokernel.π β ≫ s.π) ?_) ?_ ?_
    · rw [← Category.assoc, ← hfπ, Category.assoc, s.condition, zero_comp, comp_zero]
    · intro s
      rw [show Cofork.π (CokernelCofork.ofπ g hzero) = g from rfl]
      apply (cancel_epi (cokernel.π β)).mp
      simp only [← Category.assoc, hgπ, cokernel.π_desc]
    · intro s m hm
      rw [show Cofork.π (CokernelCofork.ofπ g hzero) = g from rfl] at hm
      apply (cancel_epi (cokernel.π γ)).mp
      rw [cokernel.π_desc, ← hgπ, Category.assoc, hm]
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ hcolim) hmono hepi

/-! ## 2. The canonical homeomorphism `{y : A | (y : X) ∈ C} ≅ C` -/

/-- The canonical map `{y : A | (y : X) ∈ C} ⟶ C` is an isomorphism of topological spaces (both
are the subspace `C` of `X`, one of them regarded as a subspace of `A`). -/
theorem isIso_inclInterA (X : TopCat) (C A : Set X) (hCA : C ⊆ A) :
    IsIso (Work.Cohomology.inclInterA X A C) := by
  let qfun : ↥C → {y : ↥A | (y : X) ∈ C} := fun c => ⟨⟨(c : X), hCA c.2⟩, c.2⟩
  have hqcont : Continuous qfun :=
    Continuous.subtype_mk
      (Continuous.subtype_mk continuous_subtype_val (fun c : ↥C => hCA c.2))
      (fun c : ↥C => c.2)
  let q : TopCat.of C ⟶ TopCat.of {y : ↥A | (y : X) ∈ C} := TopCat.ofHom ⟨qfun, hqcont⟩
  refine ⟨⟨q, ?_, ?_⟩⟩
  · ext y
    rfl
  · ext c
    rfl

/-- The induced map on singular chains is an isomorphism. -/
theorem isIso_chainMap_inclInterA (X : TopCat) (C A : Set X) (hCA : C ⊆ A) :
    IsIso (Work.Cohomology.chainMap ℤ (TopCat.of {y : ↥A | (y : X) ∈ C}) (TopCat.of C)
      (Work.Cohomology.inclInterA X A C)) := by
  haveI : IsIso (Work.Cohomology.inclInterA X A C) := isIso_inclInterA X C A hCA
  exact Functor.map_isIso _ _

/-! ## 3. The comparison of the two models of `C_*(A,C)` -/

/-- The chain-level compatibility of the two models of the relative chains of `(A,C)`: the
inclusion `C_*(C) ⟶ C_*(X)` is the composite of `C_*(C) ⟶ C_*(A)` with the inclusion
`C_*(A) ⟶ C_*(X)`, and the same holds with `{y : A | (y : X) ∈ C}` in place of `C`. -/
theorem tripleShort_w (X : TopCat) (C A : Set X) (hCA : C ⊆ A) :
    Work.Cohomology.inclChains (TopCat.of A) {y : ↥A | (y : X) ∈ C}
      ≫ Work.Cohomology.inclChains X A
      = Work.Cohomology.chainMap ℤ (TopCat.of {y : ↥A | (y : X) ∈ C}) (TopCat.of C)
          (Work.Cohomology.inclInterA X A C)
        ≫ Work.Cohomology.inclChains X C := by
  rw [Work.Cohomology.inclChains, Work.Cohomology.inclChains, Work.Cohomology.chainMap,
    Work.Cohomology.chainMap, ← Functor.map_comp, ← Functor.map_comp]
  congr 1

/-! ## 4. The statement -/

/-- **The short complex of the triple `C ⊆ A ⊆ X` is short exact.** -/
theorem tripleShort_shortExact {X : TopCat} (C A : Set X) (hCA : C ⊆ A) :
    (Work.StemsB.tripleShort X C A hCA).ShortExact := by
  set α := Work.Cohomology.inclChains (TopCat.of A) {y : ↥A | (y : X) ∈ C} with hα
  set β := Work.Cohomology.inclChains X C with hβ
  set γ := Work.Cohomology.inclChains X A with hγ
  set p := Work.Cohomology.chainMap ℤ (TopCat.of {y : ↥A | (y : X) ∈ C}) (TopCat.of C)
      (Work.Cohomology.inclInterA X A C) with hp
  haveI hγmono : Mono γ := by
    rw [hγ]
    exact Work.Cohomology.mono_chainMap_subtypeIncl X A
  haveI hpiso : IsIso p := by
    rw [hp]
    exact isIso_chainMap_inclInterA X C A hCA
  have w : α ≫ γ = p ≫ β := by
    rw [hα, hγ, hp, hβ]
    exact tripleShort_w X C A hCA
  have hβz : β ≫ cokernel.π γ = 0 := by
    rw [hβ, hγ]
    rw [← Work.Cohomology.inclChainsSub_comp X C A hCA, Category.assoc, cokernel.condition,
      comp_zero]
  exact shortExact_of_cokernelMap α p γ β w hβz

end

end Work.StemsB
