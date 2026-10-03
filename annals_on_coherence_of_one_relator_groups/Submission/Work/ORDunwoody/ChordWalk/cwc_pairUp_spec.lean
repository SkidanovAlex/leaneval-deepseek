import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.Chord

namespace Work.ORDunwoody.ChordWalk

/-! ## The bookkeeping for `pairUp` -/

/-- Every pair produced by `pairUp L` consists of two consecutive entries of `L`. -/
private lemma cwc_aux_pairUp_decomp : ∀ (L : List ℕ) (p q : ℕ),
    (p, q) ∈ Work.ORDunwoody.Dunwoody.pairUp L →
      ∃ L1 L2 : List ℕ, L = L1 ++ p :: q :: L2
  | [], _, _, h => by simp at h
  | [x], _, _, h => by simp at h
  | x :: y :: rest, p, q, h => by
      rw [Work.ORDunwoody.Dunwoody.pairUp_cons_cons] at h
      rcases List.mem_cons.mp h with h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h
        exact ⟨[], rest, rfl⟩
      · obtain ⟨L1, L2, hL⟩ := cwc_aux_pairUp_decomp rest p q h
        exact ⟨x :: y :: L1, L2, by rw [hL]; rfl⟩

theorem cwc_pairUp_spec {L : List ℕ} (hs : L.Pairwise (· < ·)) {p q : ℕ} (h : (p, q) ∈ Work.ORDunwoody.Dunwoody.pairUp L) : p < q ∧ ∀ c ∈ L, p < c → c < q → False := by
  obtain ⟨L1, L2, hL⟩ := cwc_aux_pairUp_decomp L p q h
  rw [hL] at hs
  rw [← List.singleton_append, ← List.append_assoc] at hs
  obtain ⟨h1, h2, h3⟩ := List.pairwise_append.mp hs
  obtain ⟨-, -, h1'⟩ := List.pairwise_append.mp h1
  obtain ⟨h2', -⟩ := List.pairwise_cons.mp h2
  refine ⟨?_, ?_⟩
  · exact h3 p (List.mem_append_right L1 (List.mem_singleton_self p)) q List.mem_cons_self
  · intro c hc hpc hcq
    rw [hL, ← List.singleton_append, ← List.append_assoc] at hc
    rcases List.mem_append.mp hc with hc | hc
    · rcases List.mem_append.mp hc with hc | hc
      · have := h1' c hc p (List.mem_singleton_self p)
        omega
      · rw [List.mem_singleton] at hc
        omega
    · rcases List.mem_cons.mp hc with hc | hc
      · rw [hc] at hcq
        omega
      · have := h2' c hc
        omega

end Work.ORDunwoody.ChordWalk
