import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.Defs

namespace Work.ORHughesFree.NaturalExtension

theorem blim_lower_approx (ω : Ultrafilter ℕ) {f : ℕ → ℝ} {M : ℝ} (hf : ∀ i, |f i| ≤ M)
    {ε : ℝ} (hε : 0 < ε) : {i : ℕ | blim ω f - ε ≤ f i} ∈ ω := by
  set S : Set ℝ := {r : ℝ | {i | r ≤ f i} ∈ ω} with hS
  have hblim : blim ω f = sSup S := rfl
  have hbdd : BddAbove S := by
    refine ⟨M, fun r hr => ?_⟩
    change {i | r ≤ f i} ∈ ω at hr
    obtain ⟨i, hi⟩ := Filter.nonempty_of_mem hr
    exact le_trans hi (le_trans (le_abs_self (f i)) (hf i))
  have hne : S.Nonempty := by
    refine ⟨-M, ?_⟩
    change {i : ℕ | -M ≤ f i} ∈ ω
    have h0 : {i : ℕ | -M ≤ f i} = Set.univ := by
      ext i; exact iff_true_intro (neg_le_of_abs_le (hf i))
    rw [h0]; exact Filter.univ_mem
  have hlt : blim ω f - ε < sSup S := by rw [hblim]; linarith
  obtain ⟨r, hrS, hrg⟩ := (lt_csSup_iff hbdd hne).mp hlt
  change {i | r ≤ f i} ∈ ω at hrS
  exact Filter.mem_of_superset hrS (fun i hi => le_trans (le_of_lt hrg) hi)

end Work.ORHughesFree.NaturalExtension
