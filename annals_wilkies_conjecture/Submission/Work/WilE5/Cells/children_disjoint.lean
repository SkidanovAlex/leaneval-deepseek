import Mathlib
import Submission.Work.WilE5.Sys
import Submission.Work.WilE5.Strat.stSemiPf_subset_flatSemiPf_union_children
import Submission.Work.WilE5.Strat.opVal_eq_zero_of_not_valid

namespace Work.WilE5.Cells

/-- Two distinct children of one state are disjoint: the children `(t, s)` and `(t', s')` with
`(t, s) ≠ (t', s')` have disjoint sets.

* If `t = t'` the two children differ in the sign `s ≠ s'`, and both carry the strict sign
  condition on the very same polynomial `opVal X.c σ t`, with opposite signs.
* If `t ≠ t'`, then (`hcmp`) one of `testLt t t'`, `testLt t' t` holds; say the former.  The child
  at `t` carries the strict sign condition on `opVal X.c σ t` (so its value at `z` is nonzero),
  while the child at `t'` has `opVal X.c σ t''` in its `Ξ` for every *valid* earlier test
  `t'' ∈ prec M NΦ σ t'`; if `t` is valid then `t ∈ prec M NΦ σ t'` and the value vanishes at
  `z`, and if `t` is invalid then `opVal X.c σ t = 0` as a polynomial, so it vanishes anyway. -/
theorem children_disjoint {p q : ℕ} (X : WilkiesDesign.E.SemiPf (p + q)) (M NΦ : ℕ)
    (σ : Work.WilE5.St p q X.r) {t t' : Work.WilE5.Test q} {s s' : Bool}
    (ht : t ∈ Work.WilE5.testL q M NΦ) (ht' : t' ∈ Work.WilE5.testL q M NΦ)
    (h : t ≠ t' ∨ s ≠ s')
    (hcmp : t ≠ t' → Work.WilE5.testLt t t' = true ∨ Work.WilE5.testLt t' t = true) :
    Disjoint (Work.WilE5.stSemiPf X (Work.WilE5.childSt X.c M NΦ σ t s)).set
      (Work.WilE5.stSemiPf X (Work.WilE5.childSt X.c M NΦ σ t' s')).set := by
  rw [Set.disjoint_left]
  intro z hz hz'
  rw [Work.WilE5.Strat.stSemiPf_child_set_eq] at hz hz'
  obtain ⟨-, -, hprec, -, hsign⟩ := hz
  obtain ⟨-, -, hprec', -, hsign'⟩ := hz'
  by_cases htt : t = t'
  · -- same test, opposite signs
    have hss : s ≠ s' := by
      rcases h with h | h
      · exact absurd htt h
      · exact h
    subst t'
    rcases s with _ | _ <;> rcases s' with _ | _ <;> simp_all <;> linarith
  · -- distinct tests: a sign condition of one meets a vanishing condition of the other
    have hsign_ne : WilkiesDesign.E.eaEval X.c (Work.WilE5.opVal X.c σ t) z ≠ 0 := by
      rcases s with _ | _
      · exact ne_of_lt (by simpa using hsign)
      · exact ne_of_gt (by simpa using hsign)
    have hsign'_ne : WilkiesDesign.E.eaEval X.c (Work.WilE5.opVal X.c σ t') z ≠ 0 := by
      rcases s' with _ | _
      · exact ne_of_lt (by simpa using hsign')
      · exact ne_of_gt (by simpa using hsign')
    rcases hcmp htt with hlt | hlt
    · by_cases hv : Work.WilE5.valid σ t
      · refine hsign_ne (hprec' t ?_)
        exact (Work.WilE5.Strat.mem_prec_iff (σ := σ) (t := t') (t' := t)).mpr ⟨ht, hv, hlt⟩
      · have h0 : Work.WilE5.opVal X.c σ t = 0 :=
          Work.WilE5.Strat.opVal_eq_zero_of_not_valid X.c σ t hv
        refine hsign_ne ?_
        rw [h0]; simp [WilkiesDesign.E.eaEval]
    · by_cases hv : Work.WilE5.valid σ t'
      · refine hsign'_ne (hprec t' ?_)
        exact (Work.WilE5.Strat.mem_prec_iff (σ := σ) (t := t) (t' := t')).mpr ⟨ht', hv, hlt⟩
      · have h0 : Work.WilE5.opVal X.c σ t' = 0 :=
          Work.WilE5.Strat.opVal_eq_zero_of_not_valid X.c σ t' hv
        refine hsign'_ne ?_
        rw [h0]; simp [WilkiesDesign.E.eaEval]

end Work.WilE5.Cells
