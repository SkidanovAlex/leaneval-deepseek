import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.Defs

namespace Work.ORHughesFree.NaturalExtension

theorem blim_mono (ω : Ultrafilter ℕ) {f g : ℕ → ℝ} {M M' : ℝ}
    (hf : ∀ i, |f i| ≤ M) (hg : ∀ i, |g i| ≤ M') (h : ∀ i, f i ≤ g i) :
    blim ω f ≤ blim ω g := by
  rw [blim, blim]
  -- `blim` is `sSup {r | {i | r ≤ f i} ∈ ω}`; the hypothesis `f ≤ g` makes the set for `f`
  -- a subset of the set for `g`, and the bounds make the latter bounded above.
  apply csSup_le_csSup
  · refine ⟨M', fun r hr => ?_⟩
    obtain ⟨i, hi⟩ := Filter.nonempty_of_mem (f := (ω : Filter ℕ)) hr
    exact le_trans hi (abs_le.mp (hg i)).2
  · refine ⟨-M - 1, ?_⟩
    apply Filter.mem_of_superset Filter.univ_mem
    intro i _
    show -M - 1 ≤ f i
    linarith [(abs_le.mp (hf i)).1]
  · intro r hr
    exact Filter.mem_of_superset hr (fun i hi => le_trans hi (h i))

end Work.ORHughesFree.NaturalExtension
