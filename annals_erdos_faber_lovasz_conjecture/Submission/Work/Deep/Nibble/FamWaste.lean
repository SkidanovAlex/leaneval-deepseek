import Submission.Work.Deep.Nibble.FamEst

/-!
# The matched coverage and the waste of one round

In the "wasteful" Rödl nibble a round keeps each edge with probability `p`, its
matching is the family `isoFam 𝓖 ω` of *isolated* kept edges, and the residual
vertex set is `U ∖ covX`.  A vertex of a prescribed set `S` is therefore

* *uncovered* (`uncovFam`), or
* *matched* (`matchedFam`, covered by an isolated kept edge), or
* *wasted* (`wasteFam`, covered by a kept edge but by no isolated one).

This module adds `matchedFam` and proves

* `wasteFam_add_matchedFam` — the three-way decomposition
  `wasteFam + matchedFam + uncovFam = |S|`;
* `wasteFam_le_badSum` — the waste is dominated by the edge-charged `badSum`,
  whose mean is bounded by `r2_Wfam_mean`.

The tail bounds are `r2_Mfam_tail` (matched coverage, certificate size `O(rD|S|)`)
and `r2_Yfam_tail` (uncovered count, certificate size `|S|`).
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Deep.Nibble

open Work.Deep.Reed

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The vertices of the finite set `S` covered by an *isolated* kept edge of the
round: the part of `S` that the round's matching covers. -/
noncomputable def matchedFam (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) (S : Finset V) : ℕ := by
  classical
  exact (S.filter (fun v => v ∈ ⋃ e ∈ isoFam 𝓖 ω, (e : Set V))).card

/-- The three-way decomposition of a prescribed set by one round. -/
theorem wasteFam_add_matchedFam (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) (S : Finset V) :
    wasteFam 𝓖 ω S + matchedFam 𝓖 ω S + uncovFam 𝓖 ω S = S.card := by
  classical
  have hiso_sub : (⋃ e ∈ isoFam 𝓖 ω, (e : Set V)) ⊆ covX 𝓖 ω := by
    intro v hv
    obtain ⟨e, he, hve⟩ := Set.mem_iUnion₂.mp hv
    exact (mem_covX_iff 𝓖 ω v).mpr ⟨e, he.1, hve⟩
  have hsplit : (S.filter (fun v => v ∈ covX 𝓖 ω)).card
      = (S.filter (fun v => v ∈ covX 𝓖 ω ∧ v ∉ ⋃ e ∈ isoFam 𝓖 ω, (e : Set V))).card
        + (S.filter (fun v => v ∈ ⋃ e ∈ isoFam 𝓖 ω, (e : Set V))).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext v
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro ⟨hvS, hcov⟩
        by_cases hi : v ∈ ⋃ e ∈ isoFam 𝓖 ω, (e : Set V)
        · exact Or.inr ⟨hvS, hi⟩
        · exact Or.inl ⟨hvS, hcov, hi⟩
      · rintro (⟨hvS, hcov', -⟩ | ⟨hvS, hi⟩)
        · exact ⟨hvS, hcov'⟩
        · exact ⟨hvS, hiso_sub hi⟩
    · rw [Finset.disjoint_left]
      intro v hv1 hv2
      rw [Finset.mem_filter] at hv1 hv2
      exact absurd hv2.2 hv1.2.2
  have hsplit2 : (S.filter (fun v => v ∈ covX 𝓖 ω)).card
      + (S.filter (fun v => v ∉ covX 𝓖 ω)).card = S.card :=
    Finset.card_filter_add_card_filter_not (s := S) (p := fun v => v ∈ covX 𝓖 ω)
  rw [wasteFam, matchedFam, uncovFam, ← hsplit2, hsplit]

/-- **The waste is dominated by the edge-charged `badSum`**: every vertex of `S`
covered but unmatched lies in a kept edge meeting some other kept edge. -/
theorem wasteFam_le_badSum (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) (S : Finset V) :
    wasteFam 𝓖 ω S ≤ badSum 𝓖 ω S := by
  classical
  set W : Finset V := S.filter (fun v => v ∈ covX 𝓖 ω ∧ v ∉ ⋃ e ∈ isoFam 𝓖 ω, (e : Set V))
    with hW
  have hWc : wasteFam 𝓖 ω S = W.card := by rw [wasteFam, hW]
  have hwit : ∀ v ∈ W, ∃ e : 𝓖, badAt 𝓖 ω e ∧ v ∈ (e.1 : Set V) := by
    intro v hv
    rw [hW, Finset.mem_filter] at hv
    obtain ⟨hvS, hvcov, hvnot⟩ := hv
    obtain ⟨e, he, hve⟩ := (mem_covX_iff 𝓖 ω v).mp hvcov
    refine ⟨e, ⟨he, ?_⟩, hve⟩
    by_contra hcon
    push_neg at hcon
    have hiso : e ∈ isoFam 𝓖 ω := by
      refine ⟨he, fun f hf hfw => ?_⟩
      have h1 : (f.1 ∩ e.1).Nonempty = False := by
        rw [hcon f hf hfw]
        simp
      exact h1
    exact hvnot (Set.mem_iUnion₂.mpr ⟨e, hiso, hve⟩)
  rw [hWc]
  by_cases hG : 𝓖.Nonempty
  · obtain ⟨e₀, he₀⟩ := hG
    set g : V → 𝓖 := fun v => if h : v ∈ W then Classical.choose (hwit v h) else ⟨e₀, he₀⟩ with hg
    have hg_bad : ∀ v ∈ W, badAt 𝓖 ω (g v) := by
      intro v hv
      rw [hg]
      simp only [dif_pos hv]
      exact (Classical.choose_spec (hwit v hv)).1
    have hg_mem : ∀ v ∈ W, v ∈ ((g v).1 : Set V) := by
      intro v hv
      rw [hg]
      simp only [dif_pos hv]
      exact (Classical.choose_spec (hwit v hv)).2
    have hfiber : ∀ e : 𝓖, (W.filter (fun v => g v = e)).card
        ≤ (e.1 ∩ (S : Set V)).ncard := by
      intro e
      have hsub : ((W.filter (fun v => g v = e) : Finset V) : Set V) ⊆ e.1 ∩ (S : Set V) := by
        intro v hv
        rw [Finset.coe_filter] at hv
        obtain ⟨hvW, hgv⟩ := hv
        refine ⟨?_, ?_⟩
        · rw [← hgv]; exact hg_mem v hvW
        · exact (Finset.mem_filter.mp hvW).1
      have h2 : ((W.filter (fun v => g v = e) : Finset V) : Set V).ncard
          ≤ (e.1 ∩ (S : Set V)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      have h3 : ((W.filter (fun v => g v = e) : Finset V) : Set V).ncard
          = (W.filter (fun v => g v = e)).card := by
        rw [Set.ncard_eq_toFinset_card]
        congr 1
        ext v
        simp
      rw [h3] at h2
      exact h2
    have hfiber0 : ∀ e : 𝓖, ¬ badAt 𝓖 ω e → (W.filter (fun v => g v = e)).card = 0 := by
      intro e he
      rw [Finset.card_eq_zero, ← Finset.not_nonempty_iff_eq_empty]
      rintro ⟨v, hv⟩
      rw [Finset.mem_filter] at hv
      exact he (hv.2 ▸ hg_bad v hv.1)
    have hdec := Finset.card_eq_sum_card_fiberwise (s := W) (t := (Finset.univ : Finset 𝓖))
      (f := g) (fun v _ => Finset.mem_univ _)
    calc W.card = ∑ e : 𝓖, (W.filter (fun v => g v = e)).card := hdec
      _ ≤ ∑ e : 𝓖, (if badAt 𝓖 ω e then (e.1 ∩ (S : Set V)).ncard else 0) := by
          refine Finset.sum_le_sum fun e _ => ?_
          by_cases h : badAt 𝓖 ω e
          · rw [if_pos h]; exact hfiber e
          · rw [if_neg h]; exact le_of_eq (hfiber0 e h)
      _ = badSum 𝓖 ω S := rfl
  · rw [Set.not_nonempty_iff_eq_empty] at hG
    have hcov : covX 𝓖 ω = ∅ := by
      rw [covX]
      simp [kept, hG]
    have hW0 : W.card = 0 := by
      rw [Finset.card_eq_zero, ← Finset.not_nonempty_iff_eq_empty]
      rintro ⟨v, hv⟩
      rw [hW, Finset.mem_filter] at hv
      rw [hcov] at hv
      exact Set.notMem_empty v hv.2.1
    rw [hW0]
    exact Nat.zero_le _

end Work.Deep.Nibble
