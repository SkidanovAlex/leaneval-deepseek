import Mathlib
import Submission.Work.Whitney.CutPush.Assembly

/-!
# The arc neighbourhood lemma of the cut push

A continuous arc `γ '' [0,1]` in a locally compact Hausdorff space, lying in an open set `W`
and avoiding two points `p, q`, admits an open neighbourhood `W₀` with `closure W₀ ⊆ W`, still
containing the arc and still avoiding `p` and `q`.

This is the elementary topological input that lets the cut push localise a Whitney finger around
an arc inside a prescribed open set, keeping the two double-point values `f p₂`, `f q₂` out of the
cut region.

The proof is the standard "shrink a compact set inside an open set" argument
(`IsCompact.exists_isOpen_closure_subset`, available in a locally compact Hausdorff space because
such a space is regular): the compact set `γ '' [0,1]` is shrunk inside `W \ {p, q}`, which is open
and still contains it since `p, q` are not on the arc.
-/

namespace Work.Whitney.CutPush

open Set

/-- Shrinking a compact set inside an open set, with two points avoided: if `K` is compact,
`U` is open, `K ⊆ U` and `p, q ∉ K`, then there is an open `V` with `K ⊆ V`, `closure V ⊆ U`
and `p, q ∉ V`. -/
theorem exists_isOpen_closure_subset_sdiff_pair {X : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] {K U : Set X} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (p q : X) (hp : p ∉ K) (hq : q ∉ K) :
    ∃ V : Set X, IsOpen V ∧ K ⊆ V ∧ closure V ⊆ U ∧ p ∉ V ∧ q ∉ V := by
  have hpair : IsClosed ({p, q} : Set X) := by
    rw [show ({p, q} : Set X) = {p} ∪ {q} by ext x; simp [or_comm, eq_comm]]
    exact isClosed_singleton.union isClosed_singleton
  have hmem : U \ ({p, q} : Set X) ∈ nhdsSet K := by
    rw [mem_nhdsSet_iff_exists]
    refine ⟨U \ {p, q}, hU.sdiff hpair, ?_, Subset.rfl⟩
    intro x hx
    refine ⟨hKU hx, ?_⟩
    rintro (h | h)
    · exact hp (h ▸ hx)
    · exact hq (h ▸ hx)
  obtain ⟨V, hV, hKV, hcl⟩ := hK.exists_isOpen_closure_subset hmem
  refine ⟨V, hV, hKV, Subset.trans hcl Set.sdiff_subset, ?_, ?_⟩
  · intro hpV
    exact (hcl (subset_closure hpV)).2 (by simp)
  · intro hqV
    exact (hcl (subset_closure hqV)).2 (by simp)

theorem exists_arc_neighbourhood {M : Type*} [TopologicalSpace M] [T2Space M] [LocallyCompactSpace M] (γ : ℝ → M) (hγ : Continuous γ) (W : Set M) (hW : IsOpen W) (hsub : γ '' Set.Icc 0 1 ⊆ W) (p q : M) (hp : p ∉ γ '' Set.Icc 0 1) (hq : q ∉ γ '' Set.Icc 0 1) : ∃ W₀ : Set M, IsOpen W₀ ∧ γ '' Set.Icc 0 1 ⊆ W₀ ∧ W₀ ⊆ W ∧ closure W₀ ⊆ W ∧ p ∉ W₀ ∧ q ∉ W₀ := by
  have hK : IsCompact (γ '' Set.Icc 0 1) := isCompact_Icc.image hγ
  obtain ⟨W₀, hW₀, hsub₀, hcl, hp₀, hq₀⟩ :=
    exists_isOpen_closure_subset_sdiff_pair hK hW hsub p q hp hq
  exact ⟨W₀, hW₀, hsub₀, fun x hx => hcl (subset_closure hx), hcl, hp₀, hq₀⟩

end Work.Whitney.CutPush
