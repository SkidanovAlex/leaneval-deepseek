import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.Defs

namespace Work.ORHughesFree.NaturalExtension

/-- The ultralimit `blim ω` depends only on the class of the sequence modulo the ultrafilter `ω`.
When `ω` contains all cofinite sets, two sequences that agree eventually along `Filter.atTop`
have the same ultralimit. -/
theorem blim_congr (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.atTop)
    {f g : ℕ → ℝ} (h : ∀ᶠ i in Filter.atTop, f i = g i) : blim ω f = blim ω g := by
  have hE : {i | f i = g i} ∈ (ω : Filter ℕ) := hω h
  unfold blim
  apply congrArg sSup
  ext r
  constructor
  · intro hr
    exact Filter.mem_of_superset (Filter.inter_mem hr hE)
      (fun i hi => le_trans hi.1 (le_of_eq hi.2))
  · intro hr
    exact Filter.mem_of_superset (Filter.inter_mem hr hE)
      (fun i hi => le_trans hi.1 (le_of_eq hi.2.symm))

end Work.ORHughesFree.NaturalExtension
