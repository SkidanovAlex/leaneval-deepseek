import Mathlib
import Submission.Work.WilE7.DimOneCells

namespace Work.WilE7

/-- Real-analysis ingredient for compatibility: if `J ⊆ ℝ` is nonempty, order-convex
(`OrdConnected`) and bounded, then the whole open interval between the infimum and the
supremum of `J` is contained in `J`.

Indeed, if `x` lies strictly between `sInf J` and `sSup J`, then (as `sInf J < x`) some
element `j₁ ∈ J` is `< x`, and (as `x < sSup J`) some element `j₂ ∈ J` is `> x`; order
convexity of `J` then forces `x ∈ J`.  Boundedness is only needed so that `sInf`/`sSup`
behave as the true infimum/supremum. -/
theorem interval_subset_of_ordConnected {J : Set ℝ} (hbdd₁ : BddBelow J) (hbdd₂ : BddAbove J)
    (hJne : J.Nonempty) (hJ : J.OrdConnected) :
    Set.Ioo (sInf J) (sSup J) ⊆ J := by
  intro x hx
  rw [Set.mem_Ioo] at hx
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨j1, hj1, hj1lt⟩ := (csInf_lt_iff hbdd₁ hJne).mp h1
  obtain ⟨j2, hj2, hj2lt⟩ := (lt_csSup_iff hbdd₂ hJne).mp h2
  exact hJ.out hj1 hj2 (Set.mem_Icc.mpr ⟨le_of_lt hj1lt, le_of_lt hj2lt⟩)

set_option linter.unusedVariables false in
/-- Compatibility of the open cells `(a,b)` cut out by a finite set `U` with the order-convex
set `J ⊆ [-1,1]` whose infimum and supremum lie in `U`: if `J` meets `(a,b)`, then `(a,b)`
is entirely contained in `J`.

Because `sInf J ∈ U` is *below* the meeting point `< b` and no element of `U` lies strictly
in `(a,b)`, we get `sInf J ≤ a`; symmetrically `sSup J ≥ b`.  Since `(sInf J, sSup J) ⊆ J`
by `interval_subset_of_ordConnected`, and `(a,b) ⊆ (sInf J, sSup J)`, the claim follows. -/
theorem DimOneCellsCompat {U : Finset ℝ} {a b : ℝ} {J : Set ℝ}
    (hab : a < b) (hnb : ∀ u ∈ U, ¬ (a < u ∧ u < b))
    (hJsub : J ⊆ Set.Icc (-1 : ℝ) 1) (hJ : J.OrdConnected) (hJne : J.Nonempty)
    (hInf : sInf J ∈ U) (hSup : sSup J ∈ U)
    (hmeet : ∃ y, a < y ∧ y < b ∧ y ∈ J) :
    Set.Ioo a b ⊆ J := by
  obtain ⟨y, hay, hyb, hyJ⟩ := hmeet
  have hbdd₁ : BddBelow J := ⟨-1, fun x hx => (hJsub hx).1⟩
  have hbdd₂ : BddAbove J := ⟨1, fun x hx => (hJsub hx).2⟩
  have hInf_le_y : sInf J ≤ y := csInf_le hbdd₁ hyJ
  have hy_le_sSup : y ≤ sSup J := le_csSup hbdd₂ hyJ
  -- `sInf J ∈ U` and `sInf J < b`, so `¬ (a < sInf J)`, i.e. `sInf J ≤ a`.
  have hInf_lt_b : sInf J < b := lt_of_le_of_lt hInf_le_y hyb
  have hInf_le_a : sInf J ≤ a := le_of_not_gt (fun h => hnb (sInf J) hInf ⟨h, hInf_lt_b⟩)
  -- `sSup J ∈ U` and `a < sSup J`, so `¬ (sSup J < b)`, i.e. `b ≤ sSup J`.
  have ha_lt_sSup : a < sSup J := lt_of_lt_of_le hay hy_le_sSup
  have hb_le_sSup : b ≤ sSup J := le_of_not_gt (fun h => hnb (sSup J) hSup ⟨ha_lt_sSup, h⟩)
  intro x hx
  rw [Set.mem_Ioo] at hx
  obtain ⟨hax, hxb⟩ := hx
  exact interval_subset_of_ordConnected hbdd₁ hbdd₂ hJne hJ
    (Set.mem_Ioo.mpr ⟨lt_of_le_of_lt hInf_le_a hax, lt_of_lt_of_le hxb hb_le_sSup⟩)

end Work.WilE7
