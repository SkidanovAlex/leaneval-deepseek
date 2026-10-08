import Mathlib
import Submission.Work.Clifford.Orbit
import Submission.Work.Clifford.card_charOrbit

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Clifford.inertia_subgroupOf_eq_top`

Let `N ⊴ G` and let `θ` be an irreducible character of `N`.  Then `N ≤ I_G(θ)`
(`Work.Clifford.le_inertia_of_mem_Irr`), so that `N` may be regarded — via
`Subgroup.subgroupOfEquivOfLe` — as a subgroup of the inertia group `I = I_G(θ)`, and `θ`
pulled back along that isomorphism is a function on `N.subgroupOf I`.

The point of this file is that this pulled-back function has *full* inertia group inside `I`:

  `I_I(θ) = ⊤`,

i.e. restricting the whole Clifford setting from `G` down to `I_G(θ)` makes `θ`
invariant.  This is the trivial half of the Clifford correspondence: every element of `I_G(θ)`
fixes `θ` by definition of `I_G(θ)`, and conjugating inside `I` is conjugating inside `G` with
the same element, transported across the canonical identification `N.subgroupOf I ≃* N`.

The only real computation is the transport lemma `conjFun_subgroupOfEquivOfLe`: for any
`g : I` and any `f : N → ℂ`, conjugating the pullback of `f` by `g` inside `I` is the same as
conjugating `f` by `(g : G)` inside `G`, then pulling back.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Classical

namespace Work.Clifford

universe u

/-- Conjugation inside the inertia group transports across `N.subgroupOf I ≃* N`: for `g : I`
and any function `f` on `N`, conjugating the pullback `x ↦ f (e x)` by `g` is the pullback of
the conjugate of `f` by the underlying element `(g : G)`. -/
theorem conjFun_subgroupOfEquivOfLe {G : Type*} [Group G] {N I : Subgroup G} [N.Normal]
    (h : N ≤ I) (g : I) (f : N → ℂ) :
    conjFun (N.subgroupOf I) g (fun x => f (Subgroup.subgroupOfEquivOfLe h x))
      = fun x => conjFun N (g : G) f (Subgroup.subgroupOfEquivOfLe h x) := by
  ext x
  simp only [conjFun, Subgroup.subgroupOfEquivOfLe]
  congr 1

/-- The inertia group inside the inertia group is everything: if `θ` is an irreducible character
of `N ⊴ G` and `I = I_G(θ)`, then the pullback of `θ` to `N.subgroupOf I` is `I`-invariant, so
its inertia group in `I` is `⊤`. -/
theorem inertia_subgroupOf_eq_top {G : Type*} [Group G] [Fintype G] {N : Subgroup G} [N.Normal]
    {θ : N → ℂ} (hθ : θ ∈ Work.Clifford.Irr N) :
    Work.Clifford.inertia (N.subgroupOf (Work.Clifford.inertia N θ))
      (fun x => θ (Subgroup.subgroupOfEquivOfLe (Work.Clifford.le_inertia_of_mem_Irr hθ) x)) = ⊤ := by
  rw [eq_top_iff]
  intro g _
  rw [mem_inertia]
  rw [conjFun_subgroupOfEquivOfLe (le_inertia_of_mem_Irr hθ) g θ]
  have hg : conjFun N (g : G) θ = θ := (mem_inertia N θ (g : G)).mp g.2
  rw [hg]

end Work.Clifford
