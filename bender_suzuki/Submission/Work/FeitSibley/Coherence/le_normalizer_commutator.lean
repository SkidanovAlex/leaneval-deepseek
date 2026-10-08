import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped commutatorElement

namespace Work.FeitSibley.Coherence

/-- If a subgroup `T` normalizes both `B` and `C`, then it normalizes their commutator
`⁅B, C⁆`.

The commutator `⁅B, C⁆` is the `Subgroup.closure` of the set of elements `⁅b, c⁆` with `b ∈ B`,
`c ∈ C`. Conjugation by any `t ∈ T` maps such a generator to `⁅t * b * t⁻¹, t * c * t⁻¹⁆`, which
is again a generator because `t` normalizes `B` and `C`. Hence `T` stabilizes the generating set's
closure, i.e. `T ≤ normalizer ⁅B, C⁆`. -/
theorem le_normalizer_commutator {G : Type*} [Group G] {B C T : Subgroup G}
    (hB : T ≤ Subgroup.normalizer (B : Set G)) (hC : T ≤ Subgroup.normalizer (C : Set G)) :
    T ≤ Subgroup.normalizer ((⁅B, C⁆ : Subgroup G) : Set G) := by
  apply Subgroup.le_normalizer_closure_iff.mpr
  intro t ht g hg
  obtain ⟨b, hb, c, hc, rfl⟩ := hg
  rw [conjugate_commutatorElement]
  exact Subgroup.subset_closure
    ⟨_, (Subgroup.le_normalizer_iff.mp hB) t ht b hb,
     _, (Subgroup.le_normalizer_iff.mp hC) t ht c hc, rfl⟩

end Work.FeitSibley.Coherence
