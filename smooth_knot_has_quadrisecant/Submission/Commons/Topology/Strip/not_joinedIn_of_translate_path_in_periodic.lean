import Mathlib
import Submission.Commons.Topology.Strip.wall_blocks_translate_path
import Submission.Commons.Topology.Jordan.bounded_component_winding_loop

namespace Commons.Topology.Strip

/-- **A translate-path inside a closed, periodic set in the strip is a bottom–top barrier.**

Let `Z ⊆ ℝ × ℝ` be a closed-in-the-strip, `p`-periodic set contained in the open horizontal strip
`0 < q.2 < 1`, and suppose `Z` contains a path `γ` joining `z` to `z + (p,0)`.  Then the strip
`0 ≤ q.2 ≤ 1` minus `Z` cannot join the bottom point `(0,0)` to the top point `(0,1)`.

The argument is the planar barrier/crossing argument: the translates of `γ` form a `T`-equivariant
"staircase" `G : ℝ → Z` running from `x = -∞` to `x = +∞` inside the open strip; any path from the
bottom line to the top line must cross it (this is `no_bottom_top_path_of_staircase`, the
`ℝ×ℝ`-model of Maehara's crossing lemma / the two-dimensional Brouwer theorem). -/
theorem not_joinedIn_of_translate_path_in_periodic {p : ℝ} (hp : 0 < p) {Z : Set (ℝ × ℝ)}
    (hZclosed : IsClosed (Z ∪ {q : ℝ × ℝ | q.2 ≤ 0 ∨ 1 ≤ q.2}))
    (hZsub : Z ⊆ {q : ℝ × ℝ | 0 < q.2 ∧ q.2 < 1})
    (hZper : ∀ q : ℝ × ℝ, q ∈ Z ↔ (q.1 + p, q.2) ∈ Z)
    {z : ℝ × ℝ} (hz : z ∈ Z) {γ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ)}
    (hγ0 : γ 0 = z) (hγ1 : γ 1 = ((z.1 + p, z.2) : ℝ × ℝ)) (hγZ : ∀ t, γ t ∈ Z) :
    ¬ JoinedIn ((({q : ℝ × ℝ | 0 ≤ q.2 ∧ q.2 ≤ 1}) \ Z))
      ((0:ℝ), (0:ℝ)) ((0:ℝ), (1:ℝ)) := by
  intro hjoin
  obtain ⟨δ, hδmem⟩ := hjoin
  have hδ0 : δ 0 = ((0:ℝ), (0:ℝ)) := δ.source
  have hδ1 : δ 1 = ((0:ℝ), (1:ℝ)) := δ.target
  -- the given path is a translate path
  have hγ : γ 1 = ((γ 0).1 + p, (γ 0).2) := by rw [hγ0, hγ1]
  -- its `p`-periodic staircase lies in `Z`
  obtain ⟨G, -, hGper, hGform⟩ := exists_staircase p (ne_of_gt hp) γ hγ
  have hGrange : Set.range G ⊆ Z := by
    rintro q ⟨t, rfl⟩
    obtain ⟨s, n, hs⟩ := hGform t
    rw [hs]
    exact (Commons.Topology.Jordan.mem_add_intCast_mul hZper n (γ s)).mp (hγZ s)
  have hGstrip : ∀ t, (0:ℝ) ≤ (G t).2 ∧ (G t).2 ≤ 1 := by
    intro t
    have h := hZsub (hGrange ⟨t, rfl⟩)
    exact ⟨h.1.le, h.2.le⟩
  have hδstrip : ∀ t, (0:ℝ) ≤ (δ t).2 ∧ (δ t).2 ≤ 1 := fun t => (hδmem t).1
  have hδavoid : ∀ t, δ t ∉ Set.range G := fun t ht => (hδmem t).2 (hGrange ht)
  exact no_bottom_top_path_of_staircase hp (by norm_num) G.continuous hGper hGstrip
    hδstrip (by simpa using congrArg (fun q : ℝ × ℝ => q.2) δ.source)
    (by simpa using congrArg (fun q : ℝ × ℝ => q.2) δ.target) hδavoid

end Commons.Topology.Strip
