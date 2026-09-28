import Submission.Work.Cohomology.pd_plumbing

/-!
# The short exact sequence of a triple of subsets

For an abelian category `C` and morphisms `f : A ⟶ B`, `p : B ⟶ X` (with `p` a monomorphism) and
`g : A ⟶ X` with `f ≫ p = g`, the natural sequence of cokernels

`0 ⟶ coker f ⟶ coker g ⟶ coker p ⟶ 0`

is short exact.  Applied to the filtrations `C_*(A) ⊆ C_*(B) ⊆ C_*(X)` of the singular chain
complexes of a space `X` and subsets `A ⊆ B ⊆ X`, this is the short exact sequence of the triple,

`0 ⟶ C_*(B,A) ⟶ C_*(X,A) ⟶ C_*(X,B) ⟶ 0`,

the input for the long exact sequence of a triple.

## Main results

* `shortExact_cokernel_map` — the general abelian-category statement;
* `tripleShort` — the `ShortComplex` of a triple of subsets;
* `relChains_triple_shortExact` — it is short exact.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-! ## The general abelian-category statement -/

/-- **The short exact sequence `0 ⟶ coker f ⟶ coker g ⟶ coker p ⟶ 0` of a "triple"** of
morphisms `A --f--> B --p--> X` with `f ≫ p = g` (`p` a monomorphism).  The first map is induced
by `p` and the second by the identity of `X`; exactness is the statement that `coker f` embeds in
`coker g` as the kernel of `coker g ⟶ coker p`. -/
theorem shortExact_cokernel_map {C : Type*} [Category C] [Abelian C]
    {A B X : C} (f : A ⟶ B) (p : B ⟶ X) [Mono p] (g : A ⟶ X) (w : f ≫ p = g) :
    (ShortComplex.mk
      (cokernel.map f g (𝟙 A) p (by rw [Category.id_comp]; exact w))
      (cokernel.desc g (cokernel.π p)
        (by rw [← w, Category.assoc, cokernel.condition, comp_zero]))
      (by
        apply (cancel_epi (cokernel.π f)).mp
        rw [← Category.assoc, cokernel.map, cokernel.π_desc, Category.assoc, cokernel.π_desc,
          cokernel.condition, comp_zero])).ShortExact := by
  let α : cokernel f ⟶ cokernel g := cokernel.map f g (𝟙 A) p (by rw [Category.id_comp]; exact w)
  let β : cokernel g ⟶ cokernel p :=
    cokernel.desc g (cokernel.π p) (by rw [← w, Category.assoc, cokernel.condition, comp_zero])
  have hα : cokernel.π f ≫ α = p ≫ cokernel.π g := by
    change cokernel.π f ≫ cokernel.map f g (𝟙 A) p _ = p ≫ cokernel.π g
    rw [cokernel.map, cokernel.π_desc]
  have hβ : cokernel.π g ≫ β = cokernel.π p := by
    change cokernel.π g ≫ cokernel.desc g (cokernel.π p) _ = cokernel.π p
    rw [cokernel.π_desc]
  -- the square `A --f--> B --p--> X` with `A` below `A` is a pullback because `p` is a mono
  have hpb : IsPullback f (𝟙 A) p g := by
    refine IsPullback.mk' ?_ ?_ ?_
    · rw [Category.id_comp]; exact w
    · intro T φ φ' _ h2
      simpa using h2
    · intro T a b hab
      exact ⟨b, by
        apply (cancel_mono p).mp
        rw [Category.assoc, w]
        exact hab.symm, by rw [Category.comp_id]⟩
  have hzero : α ≫ β = 0 := by
    rw [← cancel_epi (cokernel.π f), comp_zero, ← Category.assoc, hα, Category.assoc, hβ,
      cokernel.condition]
  have hmono : Mono α := by
    change Mono (cokernel.map f g (𝟙 A) p _)
    exact Abelian.mono_cokernel_map_of_isPullback hpb
  have hepi : Epi β := by
    change Epi (cokernel.desc g (cokernel.π p) _)
    exact cokernel.desc_epi g (cokernel.π p) _
  -- `β` is the cokernel of `α`
  have hcolim : IsColimit (CokernelCofork.ofπ β hzero) := by
    refine Cofork.IsColimit.mk _ (fun s => cokernel.desc p (cokernel.π g ≫ s.π) ?_) ?_ ?_
    · rw [← Category.assoc, ← hα, Category.assoc, s.condition, zero_comp, comp_zero]
    · intro s
      rw [show Cofork.π (CokernelCofork.ofπ β hzero) = β from rfl]
      apply (cancel_epi (cokernel.π g)).mp
      simp only [← Category.assoc, hβ, cokernel.π_desc]
    · intro s m hm
      rw [show Cofork.π (CokernelCofork.ofπ β hzero) = β from rfl] at hm
      apply (cancel_epi (cokernel.π p)).mp
      rw [cokernel.π_desc, ← hm, ← Category.assoc, hβ]
  have hexact : (ShortComplex.mk α β hzero).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ hcolim
  exact ShortComplex.ShortExact.mk' hexact hmono hepi

/-! ## The triple of subsets of a space -/

/-- **The short complex of a triple of subsets** `A ⊆ B ⊆ X`:
`0 ⟶ C_*(B,A) ⟶ C_*(X,A) ⟶ C_*(X,B) ⟶ 0`, built from the filtration
`C_*(A) ⊆ C_*(B) ⊆ C_*(X)` of the singular chain complexes.  The first term is
`coker (C_*(A) ⟶ C_*(B))` (the relative chains of the pair `(B,A)` up to the homeomorphism
`{y : B | (y : X) ∈ A} ≅ A`) and the last two are `relChains X A`, `relChains X B`. -/
def tripleShort (X : TopCat) (A B : Set X) (hAB : A ⊆ B) :
    ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk
    (cokernel.map (inclChainsSub X A B hAB) (inclChains X A) (𝟙 _) (inclChains X B)
      (by rw [Category.id_comp]; exact inclChainsSub_comp X A B hAB))
    (cokernel.desc (inclChains X A) (cokernel.π (inclChains X B))
      (by rw [← inclChainsSub_comp X A B hAB, Category.assoc, cokernel.condition, comp_zero]))
    (by
      apply (cancel_epi (cokernel.π (inclChainsSub X A B hAB))).mp
      rw [← Category.assoc, cokernel.map, cokernel.π_desc, Category.assoc, cokernel.π_desc,
        cokernel.condition, comp_zero])

/-- **The short exact sequence of a triple of subsets** `A ⊆ B ⊆ X`. -/
theorem relChains_triple_shortExact (X : TopCat) (A B : Set X) (hAB : A ⊆ B) :
    (tripleShort X A B hAB).ShortExact := by
  haveI := mono_chainMap_subtypeIncl X B
  exact shortExact_cokernel_map (inclChainsSub X A B hAB) (inclChains X B) (inclChains X A)
    (inclChainsSub_comp X A B hAB)

/-- The first map of the triple sequence is the cokernel map induced by the inclusion of pairs
`(A,A) ⊆ (B,A)`; it is stated here as a `cokernel.map`. -/
theorem tripleShort_f (X : TopCat) (A B : Set X) (hAB : A ⊆ B) :
    (tripleShort X A B hAB).f = cokernel.map (inclChainsSub X A B hAB) (inclChains X A)
      (𝟙 _) (inclChains X B) (by rw [Category.id_comp]; exact inclChainsSub_comp X A B hAB) :=
  rfl

/-- **The second map of the triple sequence is `relCokerMap`**: the map `C_*(X,A) ⟶ C_*(X,B)`
of relative chain complexes induced by `A ⊆ B`. -/
theorem tripleShort_g (X : TopCat) (A B : Set X) (hAB : A ⊆ B) :
    (tripleShort X A B hAB).g = relCokerMap X A B hAB := by
  show cokernel.desc (inclChains X A) (cokernel.π (inclChains X B)) _ = relCokerMap X A B hAB
  rw [relCokerMap, cokernel.map]
  simp only [Category.id_comp]

/-- The first term of the triple sequence is `coker (C_*(A) ⟶ C_*(B))`, i.e. a model of the
relative chains `C_*(B,A)` (the honest relative chain complex of the pair is obtained by
transporting along the homeomorphism `A ≅ {y : B | (y : X) ∈ A}`). -/
theorem tripleShort_X1 (X : TopCat) (A B : Set X) (hAB : A ⊆ B) :
    (tripleShort X A B hAB).X₁ = cokernel (inclChainsSub X A B hAB) := rfl

/-- The first term of the triple sequence for the triple `Kᶜ ⊆ {z}ᶜ ⊆ M` (`z ∈ K`): the relative
chain complex `C_*(M∖{z}, M∖K)` in the form in which the triple sequence of `tripleShort` uses
it. -/
def relSubPunctured (M : TopCat) (z : M) (K : Set M) (hzK : z ∈ K) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  cokernel (inclChainsSub M Kᶜ ({z} : Set M)ᶜ
    (fun x hx hxz => hx (Set.mem_singleton_iff.mp hxz ▸ hzK)))

/-- **The homology of `relSubPunctured` is the relative homology `H_i(M∖{z}, M∖K)`**, via the
identification of the chains of a subspace with the chains of the ambient space supported in it. -/
theorem relSubPunctured_eq (M : TopCat) (z : M) (K : Set M) (hzK : z ∈ K) :
    relSubPunctured M z K hzK = (tripleShort M Kᶜ ({z} : Set M)ᶜ
      (fun x hx hxz => hx (Set.mem_singleton_iff.mp hxz ▸ hzK))).X₁ := rfl

end

end Work.Cohomology
