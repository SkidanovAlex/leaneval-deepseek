import Mathlib
import Submission.Work.WilE5.Sys
import Submission.Work.WilE5.Strat.stSemiPf_subset_flatSemiPf_union_children
import Submission.Work.WilE5.Strat.opVal_eq_zero_of_not_valid

namespace Work.WilE5.Cells

/-- A child of the state `σ` at a test `t` is disjoint from the flat leaf of `σ`.

There are two cases.

* `t` is valid: the flat leaf forces `opVal X.c σ t` to vanish (it is one of the flat equations),
  while every point of the child satisfies the strict sign condition of `childν`, i.e.
  `opVal X.c σ t` is nonzero there.

* `t` is not valid: then `opVal X.c σ t = 0` as a polynomial, so again the strict sign
  condition of the child is impossible. -/
theorem child_disjoint_flat {p q : ℕ} (X : WilkiesDesign.E.SemiPf (p + q)) (M NΦ : ℕ)
    (σ : Work.WilE5.St p q X.r) {t : Work.WilE5.Test q} {s : Bool}
    (ht : t ∈ Work.WilE5.testL q M NΦ) :
    Disjoint (Work.WilE5.stSemiPf X (Work.WilE5.childSt X.c M NΦ σ t s)).set
      (Work.WilE5.flatSemiPf X M NΦ σ).set := by
  classical
  rw [Set.disjoint_left]
  intro z hzC hzF
  -- spell out the two membership conditions
  rw [Work.WilE5.Strat.stSemiPf_child_set_eq X M NΦ σ t s] at hzC
  rw [Work.WilE5.Strat.flatSemiPf_set_eq X M NΦ σ] at hzF
  obtain ⟨-, -, -, -, hsign⟩ := hzC
  obtain ⟨-, -, hflat⟩ := hzF
  -- the operator value of `t` vanishes at `z`
  have hzero : WilkiesDesign.E.eaEval X.c (Work.WilE5.opVal X.c σ t) z = 0 := by
    by_cases hv : Work.WilE5.valid σ t
    · -- a valid test contributes a flat equation
      have hmem : Work.WilE5.opVal X.c σ t ∈ Work.WilE5.flatEqs X.c M NΦ σ := by
        rw [Work.WilE5.flatEqs, List.mem_map]
        exact ⟨t, by
          rw [List.mem_filter]
          exact ⟨ht, decide_eq_true_eq.mpr hv⟩, rfl⟩
      exact hflat _ hmem
    · -- an invalid test has vanishing operator value
      rw [Work.WilE5.Strat.opVal_eq_zero_of_not_valid X.c σ t hv]
      simp [WilkiesDesign.E.eaEval]
  rcases s with _ | _
  · have hs : WilkiesDesign.E.eaEval X.c (Work.WilE5.opVal X.c σ t) z < 0 := by
      simpa using hsign
    exact (ne_of_lt hs) hzero
  · have hs : 0 < WilkiesDesign.E.eaEval X.c (Work.WilE5.opVal X.c σ t) z := by
      simpa using hsign
    exact (ne_of_gt hs) hzero

end Work.WilE5.Cells
