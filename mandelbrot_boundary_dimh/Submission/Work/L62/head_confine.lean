import Mathlib
import Submission.Work.L62.continuousOn_iterate_family

/-!
# L62 — a compact confinement for a uniformly bounded family of chains

Let `Ω ⊆ ℂ` be a set, `Λ` compact, `σ : ℂ → ℂ → ℂ` a family with every `σ β`, `β ∈ Λ`, mapping
`Ω` into itself and with `(β, z) ↦ σ β z` continuous on `Λ × Ω`.  If all the starting sets
`W₁ β` (`β ∈ Λ`) lie in one *fixed* compact `K₁ ⊆ Ω` and the chain has at most `J` steps
(`J` independent of `β`), then all the discs of all the chains lie in one fixed compact `K ⊆ Ω`.

This is the topological mechanism that turns the `β`-uniform location of the *first* disc of the
head chain of Lemma 6.2 (proved in `Work.L62HD.section_over_ball_in_compact`) plus the joint
continuity of the (lifted) section family into the `K ⊆ hd.Bl` containment clause of the head.
No analytic input is used.
-/

namespace Work.L62

open Set Function

/-- **Confinement of a uniformly long chain in one compact.** -/
theorem chain_in_compact {Ω Λ K₁ : Set ℂ} {σ : ℂ → ℂ → ℂ} {W₁ : ℂ → Set ℂ} {J : ℕ}
    (hΛ : IsCompact Λ) (hK₁ : IsCompact K₁) (hK₁Ω : K₁ ⊆ Ω)
    (hcont : ContinuousOn (fun p : ℂ × ℂ => σ p.1 p.2) (Λ ×ˢ Ω))
    (hmap : ∀ β ∈ Λ, Set.MapsTo (σ β) Ω Ω)
    (hW₁ : ∀ β ∈ Λ, W₁ β ⊆ K₁) :
    ∃ K : Set ℂ, IsCompact K ∧ K ⊆ Ω ∧
      ∀ β ∈ Λ, ∀ j ≤ J, (σ β)^[j] '' W₁ β ⊆ K := by
  -- the `j`-th iterate is continuous on `Λ × Ω`
  have hiter : ∀ j : ℕ, ContinuousOn (fun p : ℂ × ℂ => (σ p.1)^[j] p.2) (Λ ×ˢ Ω) :=
    fun j => continuousOn_iterate_family j hmap hcont
  -- the image of the fixed starting compact at time `j` is compact and inside `Ω`
  have hcomp : ∀ j : ℕ, IsCompact ((fun p : ℂ × ℂ => (σ p.1)^[j] p.2) '' (Λ ×ˢ K₁)) := by
    intro j
    exact (hΛ.prod hK₁).image_of_continuousOn (hiter j |>.mono (Set.prod_mono_right hK₁Ω))
  have hsub : ∀ j : ℕ, ((fun p : ℂ × ℂ => (σ p.1)^[j] p.2) '' (Λ ×ˢ K₁)) ⊆ Ω := by
    rintro j x ⟨p, hp, rfl⟩
    exact (hmap p.1 hp.1).iterate j (hK₁Ω hp.2)
  refine ⟨⋃ j ∈ Finset.range (J + 1), (fun p : ℂ × ℂ => (σ p.1)^[j] p.2) '' (Λ ×ˢ K₁), ?_, ?_, ?_⟩
  · refine Finset.isCompact_biUnion _ (fun j _ => hcomp j)
  · exact Set.iUnion_subset (fun j => Set.iUnion_subset (fun _ => hsub j))
  · intro β hβ j hj
    refine subset_trans (Set.image_mono (hW₁ β hβ)) ?_
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact Set.mem_biUnion (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)) ⟨(β, y), ⟨hβ, hy⟩, rfl⟩

end Work.L62
