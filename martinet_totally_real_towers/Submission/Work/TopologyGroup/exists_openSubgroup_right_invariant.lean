import Mathlib

namespace Work.TopologyGroup

open Filter
open scoped Topology

/-- A locally constant function on a compact topological group is invariant under right translation
by some open subgroup.  Route: the subgroup `K = {g | ∀ x, b (x * g) = b x}` (the elements acting
trivially on `b` by right translation) contains a neighbourhood of `1`.  Indeed, for each `y` the
set `{x | b (y * x) = b y}` is a neighbourhood of `1` by local constancy of `b`, and the tube lemma
over the compact group (`IsCompact.eventually_forall_of_forall_eventually`, with `K = univ`) upgrades
this pointwise statement to the uniform one `∀ᶠ x in 𝓝 1, ∀ y, b (y * x) = b y`.  As `K` is a
subgroup of a topological group containing a neighbourhood of `1`, it is open, and
`b (x * h) = b x` for `h ∈ K` by definition. -/
theorem exists_openSubgroup_right_invariant {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] {M : Type*} (b : G → M) (hb : IsLocallyConstant b) :
    ∃ H : OpenSubgroup G, ∀ (x : G) (h : H), b (x * (h : G)) = b x := by
  -- Every `x` close enough to `1` acts trivially on `b` on the right, uniformly in the argument.
  have key : ∀ᶠ x in 𝓝 (1 : G), ∀ y : G, b (y * x) = b y := by
    have hmain := IsCompact.eventually_forall_of_forall_eventually (Y := G) (x₀ := (1 : G))
      (K := (Set.univ : Set G)) (P := fun x y => b (y * x) = b y) isCompact_univ ?_
    · simpa using hmain
    · intro y _
      have h1 : ∀ᶠ z : G × G in 𝓝 ((1 : G), y), b (z.2 * z.1) = b y := by
        have ht : Filter.Tendsto (fun z : G × G => z.2 * z.1) (𝓝 ((1 : G), y)) (𝓝 y) :=
          (continuous_snd.mul continuous_fst).tendsto' _ _ (by simp)
        exact ht.eventually (hb.eventually_eq y)
      have h2 : ∀ᶠ z : G × G in 𝓝 ((1 : G), y), b z.2 = b y := by
        have ht : Filter.Tendsto (fun z : G × G => z.2) (𝓝 ((1 : G), y)) (𝓝 y) :=
          continuous_snd.tendsto' _ _ (by simp)
        exact ht.eventually (hb.eventually_eq y)
      filter_upwards [h1, h2] with z hz1 hz2
      rw [hz1, hz2]
  let H : Subgroup G :=
    { carrier := {x : G | ∀ y : G, b (y * x) = b y}
      mul_mem' := by
        intro a c ha hc y
        rw [← mul_assoc, hc (y * a), ha y]
      one_mem' := by intro y; simp
      inv_mem' := by
        intro a ha y
        have h := ha (y * a⁻¹)
        have h2 : (y * a⁻¹) * a = y := by group
        rw [h2] at h
        exact h.symm }
  have hH : (H : Set G) ∈ 𝓝 (1 : G) := by
    have := Filter.eventually_iff.mp key
    simpa [H] using this
  have hOpen : IsOpen (H : Set G) := H.isOpen_of_mem_nhds hH
  exact ⟨⟨H, hOpen⟩, fun x h => h.property x⟩

end Work.TopologyGroup
