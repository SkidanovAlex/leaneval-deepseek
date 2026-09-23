import Mathlib

namespace Work.OddBound.mountainPass

/-- On a set `A` which is covered by `U ∪ V` and on which `U` and `V` are disjoint, membership
in `U` is equivalent to non-membership in `V`. -/
private lemma eq_inter_compl_of_subset_union_of_inter_eq_empty {α : Type*} {A U V : Set α}
    (hsub : A ⊆ U ∪ V) (hzero : A ∩ (U ∩ V) = ∅) : A ∩ U = A ∩ Vᶜ := by
  ext x
  constructor
  · rintro ⟨hxA, hxU⟩
    refine ⟨hxA, fun hxV => ?_⟩
    have hx : x ∈ A ∩ (U ∩ V) := ⟨hxA, hxU, hxV⟩
    rw [hzero] at hx
    exact hx
  · rintro ⟨hxA, hxV⟩
    rcases hsub hxA with hxU | hxV'
    · exact ⟨hxA, hxU⟩
    · exact absurd hxV' hxV

/-- The intersection of a decreasing sequence of compact connected subsets of a Hausdorff
space is connected. -/
theorem isConnected_iInter_of_antitone
    {E : Type*} [TopologicalSpace E] [T2Space E] {S : ℕ → Set E}
    (hcomp : ∀ n, IsCompact (S n)) (hconn : ∀ n, IsConnected (S n))
    (hmono : ∀ n, S (n + 1) ⊆ S n) : IsConnected (⋂ n, S n) := by
  have hclosed : ∀ n, IsClosed (S n) := fun n => (hcomp n).isClosed
  -- Nonemptiness: Cantor's intersection theorem for the decreasing family `S`.
  have hne : (⋂ n, S n).Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hmono
      (fun n => (hconn n).nonempty) (hcomp 0) hclosed
  refine ⟨hne, ?_⟩
  -- Preconnectedness: suppose the intersection is split by two open sets.
  intro U V hU hV hsub hUn hVn
  by_contra hcon
  have hzero : (⋂ n, S n) ∩ (U ∩ V) = ∅ := Set.not_nonempty_iff_eq_empty.mp hcon
  have hpt : ∀ x ∈ (⋂ n, S n), x ∈ U → x ∈ V → False := by
    intro x hxA hxU hxV
    have hx : x ∈ (⋂ n, S n) ∩ (U ∩ V) := ⟨hxA, hxU, hxV⟩
    rw [hzero] at hx
    exact hx
  have hAclosed : IsClosed (⋂ n, S n) := isClosed_iInter hclosed
  have hAcomp : IsCompact (⋂ n, S n) :=
    (hcomp 0).of_isClosed_subset hAclosed fun x hx => Set.mem_iInter.mp hx 0
  -- The two halves are closed in the compact set `⋂ n, S n`, hence compact.
  have hPd : (⋂ n, S n) ∩ U = (⋂ n, S n) ∩ Vᶜ :=
    eq_inter_compl_of_subset_union_of_inter_eq_empty hsub hzero
  have hQd : (⋂ n, S n) ∩ V = (⋂ n, S n) ∩ Uᶜ :=
    eq_inter_compl_of_subset_union_of_inter_eq_empty
      (by rw [Set.union_comm]; exact hsub)
      (by rw [Set.inter_comm V U]; exact hzero)
  have hPc : IsCompact ((⋂ n, S n) ∩ U) := by
    rw [hPd]
    exact hAcomp.of_isClosed_subset (hAclosed.inter hV.isClosed_compl) Set.inter_subset_left
  have hQc : IsCompact ((⋂ n, S n) ∩ V) := by
    rw [hQd]
    exact hAcomp.of_isClosed_subset (hAclosed.inter hU.isClosed_compl) Set.inter_subset_left
  have hdisj : Disjoint ((⋂ n, S n) ∩ U) ((⋂ n, S n) ∩ V) :=
    Set.disjoint_left.mpr fun x hxU hxV => hpt x hxU.1 hxU.2 hxV.2
  -- Separate the two compact halves by disjoint open sets.
  obtain ⟨U', V', hU'o, hV'o, hPU', hQV', hUV'⟩ :=
    SeparatedNhds.of_isCompact_isCompact hPc hQc hdisj
  -- Each `S n` must leave the separating open sets, otherwise it would be disconnected.
  have hKclosed : ∀ n, IsClosed (S n ∩ (U' ∪ V')ᶜ) :=
    fun n => (hclosed n).inter (hU'o.union hV'o).isClosed_compl
  have hKmono : ∀ n, S (n + 1) ∩ (U' ∪ V')ᶜ ⊆ S n ∩ (U' ∪ V')ᶜ :=
    fun n x hx => ⟨hmono n hx.1, hx.2⟩
  have hKne : ∀ n, (S n ∩ (U' ∪ V')ᶜ).Nonempty := by
    intro n
    by_contra h
    have hsub' : S n ⊆ U' ∪ V' := by
      intro x hx
      by_contra hx'
      exact h ⟨x, hx, hx'⟩
    obtain ⟨p, hpA, hpU⟩ := hUn
    obtain ⟨q, hqA, hqV⟩ := hVn
    have hp' : p ∈ S n := Set.mem_iInter.mp hpA n
    have hq' : q ∈ S n := Set.mem_iInter.mp hqA n
    have hpre := (hconn n).isPreconnected U' V' hU'o hV'o hsub'
      ⟨p, hp', hPU' ⟨hpA, hpU⟩⟩ ⟨q, hq', hQV' ⟨hqA, hqV⟩⟩
    obtain ⟨x, -, hxUV⟩ := hpre
    exact Set.disjoint_left.mp hUV' hxUV.1 hxUV.2
  -- Cantor again, now on the pieces outside `U' ∪ V'`.
  have hKi : (⋂ n, S n ∩ (U' ∪ V')ᶜ).Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      (fun n => S n ∩ (U' ∪ V')ᶜ) hKmono hKne
      ((hcomp 0).of_isClosed_subset (hKclosed 0) Set.inter_subset_left) hKclosed
  obtain ⟨x, hx⟩ := hKi
  have hxA : x ∈ ⋂ n, S n := Set.mem_iInter.mpr fun n => (Set.mem_iInter.mp hx n).1
  have hout : x ∉ U' ∪ V' := (Set.mem_iInter.mp hx 0).2
  refine hout ?_
  rcases hsub hxA with hxU | hxV
  · exact Or.inl (hPU' ⟨hxA, hxU⟩)
  · exact Or.inr (hQV' ⟨hxA, hxV⟩)

end Work.OddBound.mountainPass
