import Mathlib
import Submission.Work.ZASS.Defs
import Submission.Work.Zassenhaus.Basic

namespace Work.ZASS

/-- Conjugation by an element `b ∈ B = G_∞` of the Borel subgroup preserves the set
`fixesOnly G inf` of elements of `B` whose only fixed point is `∞`: the fixed-point set of
`b * g * b⁻¹` is the image under `b` of the fixed-point set of `g`, and `b` fixes `∞`. -/
lemma conjBy_mem_fixesOnly_of_mem_borel {G X : Type} [Group G] [MulAction G X] {inf : X}
    {b g : G} (hb : b ∈ Work.Zassenhaus.borel G inf)
    (hg : g ∈ Work.Zassenhaus.fixesOnly G inf) :
    conjBy b g ∈ Work.Zassenhaus.fixesOnly G inf := by
  have hb' : b • inf = inf := Work.Zassenhaus.mem_borel_iff.mp hb
  have hbinf : b⁻¹ • inf = inf :=
    Work.Zassenhaus.mem_borel_iff.mp ((Work.Zassenhaus.borel G inf).inv_mem hb)
  rw [Work.Zassenhaus.mem_fixesOnly_iff] at hg ⊢
  obtain ⟨hgB, hgnf⟩ := hg
  have hgB' : g • inf = inf := Work.Zassenhaus.mem_borel_iff.mp hgB
  refine ⟨?_, ?_⟩
  · simpa using (show conjBy b g • inf = inf by simp [conjBy, mul_smul, hb', hbinf, hgB'])
  · intro x hx hfix
    have h1 : g • (b⁻¹ • x) = b⁻¹ • x := by
      have h2 := congrArg (fun y => b⁻¹ • y) hfix
      simpa [conjBy, mul_smul] using h2
    have hy : b⁻¹ • x ≠ inf := by
      intro hyeq
      have h3 := congrArg (fun y => b • y) hyeq
      have : x = inf := by simpa [mul_smul, hb'] using h3
      exact hx this
    exact hgnf (b⁻¹ • x) hy h1

/-- **Z2 (blueprint §ZASS).** If `U ≤ B`, `|U| = q`, every nonidentity element of `U` fixes
only `∞`, and there are exactly `q - 1` such elements altogether, then `U ⊴ B`.  Reason:
conjugation by `b ∈ B` preserves the set of elements fixing only `∞`, so it maps `U` onto a
subgroup `U' ≤ B` with the same `q - 1` nonidentity elements, whence `U' = U`; conclude with
`Work.ZASS.subgroupOf_normal_of_mem_conjBy`. -/
theorem normal_of_card_eq_mem_fixesOnly {G X : Type} [Group G] [Finite G] [MulAction G X]
    {q : ℕ} {inf : X} {U : Subgroup G}
    (hUB : U ≤ Work.Zassenhaus.borel G inf) (hcardU : Nat.card U = q)
    (hUfix : ∀ u ∈ U, u ≠ 1 → u ∈ Work.Zassenhaus.fixesOnly G inf)
    (hfix : (Work.Zassenhaus.fixesOnly G inf).ncard = q - 1) :
    (U.subgroupOf (Work.Zassenhaus.borel G inf)).Normal := by
  -- The nonidentity elements of `U` are `q - 1` in number and all lie in `fixesOnly`, which
  -- has exactly `q - 1` elements; hence `fixesOnly` is *precisely* `U \ {1}`.
  have hcoe : (U : Set G).ncard = Nat.card U := rfl
  have hA : ((U : Set G) \ {1}).ncard = q - 1 := by
    rw [Set.ncard_sdiff (by simp : ({1} : Set G) ⊆ (U : Set G)), hcoe, Set.ncard_singleton,
      hcardU]
  have hsub : (U : Set G) \ {1} ⊆ Work.Zassenhaus.fixesOnly G inf := by
    intro g hg
    rw [Set.mem_sdiff, Set.mem_singleton_iff] at hg
    exact hUfix g hg.1 hg.2
  have hTsub : Work.Zassenhaus.fixesOnly G inf ⊆ (U : Set G) := by
    have heq : (U : Set G) \ {1} = Work.Zassenhaus.fixesOnly G inf :=
      Set.eq_of_subset_of_ncard_le hsub (le_of_eq (by rw [hA, hfix]))
    rw [← heq]
    exact Set.sdiff_subset
  -- Conjugation by `b ∈ B` fixes the identity and preserves `fixesOnly`, hence normalizes `U`.
  apply subgroupOf_normal_of_mem_conjBy hUB
  intro b hb u hu
  by_cases h1 : u = 1
  · subst h1
    simp
  · exact hTsub (conjBy_mem_fixesOnly_of_mem_borel hb (hUfix u hu h1))

end Work.ZASS
