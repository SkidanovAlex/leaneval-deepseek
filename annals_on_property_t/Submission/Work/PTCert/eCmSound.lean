import Mathlib
import Submission.Work.PTCert.eAux

namespace Work.PTCert

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D Submission.PTCert.C

/-- Membership in a two-element list reduces to being one of the two elements. -/
private theorem mem_pair {k a b : ℕ} (h : k ∈ [a, b]) : k = a ∨ k = b := by
  rw [List.mem_cons] at h
  rcases h with h | h
  · exact Or.inl h
  · rw [List.mem_cons] at h
    rcases h with h | h
    · exact Or.inr h
    · exact absurd h (List.not_mem_nil)

/-- `CmSound` for the concrete commutation table `cmT`: the letters whose commute bit is set
really commute.  From `C.cm_ok : cmOK cmT = true` (module `Submission.Work.PTCert.Checks.G2`),
`List.all_eq_true`, `Bool.or_eq_true`, `Bool.not_eq_true`, `Nat.beq_eq`, then
`Work.PTCert.modelSound 5 : ModelSound 5` with the letter bound `NB1 5 = 81`
(`Work.PTCert.NB1_eq`, module `Submission.Work.PTCert.letterAction`).  All of these are already
imported transitively by `Submission.Work.PTCert.eAux`. -/
theorem eCmSound : Submission.PTCert.CmSound Submission.PTCert.D.cmT := by
  intro a ha b hb hcomm
  -- `NB1 5 = 81`, the bound entering `ModelSound 5`.
  have hNB : NB1 5 = 81 := by rw [NB1_eq]
  -- Unfold the kernel check `cmOK cmT` into its `∀ a < 81, ∀ b < 81` form.
  have hok := C.cm_ok
  simp only [cmOK] at hok
  have ha' := (List.all_eq_true.mp hok) a (List.mem_range.mpr ha)
  have hb' := (List.all_eq_true.mp ha') b (List.mem_range.mpr hb)
  rw [Bool.or_eq_true] at hb'
  rcases hb' with h2 | h2
  · -- The first disjunct would say `commB cmT a b = false`, contradicting `hcomm`.
    rw [Bool.not_eq_true'] at h2
    rw [h2] at hcomm
    exact Bool.noConfusion hcomm
  · -- The second disjunct is the word-model equality of `[a, b]` and `[b, a]`.
    have hmem1 : ∀ k ∈ [a, b], k < NB1 5 := by
      intro k hk
      rcases mem_pair hk with rfl | rfl
      · rw [hNB]; exact ha
      · rw [hNB]; exact hb
    have hmem2 : ∀ k ∈ [b, a], k < NB1 5 := by
      intro k hk
      rcases mem_pair hk with rfl | rfl
      · rw [hNB]; exact hb
      · rw [hNB]; exact ha
    have hmodel := modelSound 5 [a, b] [b, a] hmem1 hmem2 h2
    simpa [lprod] using hmodel

end Work.PTCert
