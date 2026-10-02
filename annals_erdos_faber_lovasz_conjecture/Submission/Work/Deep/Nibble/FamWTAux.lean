import Submission.Work.Deep.Nibble.FamW

/-!
# Elementary bounds on the edge-charged waste

Helpers for `r2_Wfam_tail`: the witness of a bad kept edge, the domination of
`badSum` by the weighted kept count `Z` and by the degree sum `∑_{v ∈ S} hd 𝓖 v`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped BigOperators

namespace Work.Deep.Nibble

open Work.Deep.Reed

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A chosen kept edge meeting a bad edge (`e` itself if there is none). -/
noncomputable def witE (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) (e : 𝓖) : 𝓖 := by
  classical
  exact if h : ∃ f : 𝓖, f ≠ e ∧ ω f = true ∧ ((f : Set V) ∩ (e : Set V)).Nonempty
    then Classical.choose h else e

lemma witE_spec {𝓖 : Set (Set V)} {ω : 𝓖 → Bool} {e : 𝓖} (h : badAt 𝓖 ω e) :
    witE 𝓖 ω e ≠ e ∧ ω (witE 𝓖 ω e) = true
      ∧ ((witE 𝓖 ω e : Set V) ∩ (e : Set V)).Nonempty := by
  obtain ⟨-, f, hf⟩ := h
  have h' : ∃ f : 𝓖, f ≠ e ∧ ω f = true ∧ ((f : Set V) ∩ (e : Set V)).Nonempty := ⟨f, hf⟩
  rw [witE, dif_pos h']
  exact Classical.choose_spec h'

/-- The edge-charged waste is dominated by the weighted kept count
`Z ω = ∑_e |e ∩ S| · 1[ω e]`. -/
lemma badSum_le_Zsum (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) (S : Finset V) :
    badSum 𝓖 ω S
      ≤ ∑ e : 𝓖, if ω e then ((e : Set V) ∩ (S : Set V)).ncard else 0 := by
  classical
  rw [badSum]
  refine Finset.sum_le_sum fun e _ => ?_
  by_cases h : badAt 𝓖 ω e
  · rw [if_pos h, if_pos h.1]
  · rw [if_neg h]
    split_ifs <;> omega

/-- The edge-charged waste is at most the degree sum over `S`. -/
lemma badSum_le_sum_hd (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) (S : Finset V) :
    badSum 𝓖 ω S ≤ ∑ v ∈ S, hd 𝓖 v := by
  classical
  have h3 : (∑ e : 𝓖, ((e : Set V) ∩ (S : Set V)).ncard) = ∑ v ∈ S, hd 𝓖 v := by
    exact_mod_cast sum_ncard_inter_eq_sum_hd 𝓖 S
  calc badSum 𝓖 ω S
      ≤ ∑ e : 𝓖, (if ω e then ((e : Set V) ∩ (S : Set V)).ncard else 0) :=
        badSum_le_Zsum 𝓖 ω S
    _ ≤ ∑ e : 𝓖, ((e : Set V) ∩ (S : Set V)).ncard := by
        refine Finset.sum_le_sum fun e _ => ?_
        split_ifs <;> omega
    _ = ∑ v ∈ S, hd 𝓖 v := h3

end Work.Deep.Nibble
