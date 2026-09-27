import Mathlib
import Submission.Work.Mostow.LinAlgMatrixIneqAux

namespace Work.Mostow

open scoped BigOperators

/-- `matF x = (∏ i, √(x i)) / (∏ i, (1 - x i))` is continuous on the box
`Kset n δ = {x | ∀ i, δ ≤ x i ∧ ∑ i, x i = 1}`.

Both the numerator and the denominator are (globally) continuous; the only point is that
on `Kset n δ` the denominator does not vanish.  For `n ≥ 2` and `x ∈ Kset n δ` we have
`1 - x i = ∑_{j ≠ i} x j ≥ (n-1) δ > 0`, so `∏ i, (1 - x i) ≠ 0`, and the quotient of
continuous functions is continuous.  The degenerate dimensions `n = 0, 1` are handled
directly: `Kset 0 δ = ∅`, while `Kset 1 δ` is a subsingleton. -/
theorem continuousOn_matF_Kset (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ContinuousOn (fun x : Fin n → ℝ => matF x) (Kset n δ) := by
  by_cases hn : n < 2
  · interval_cases n
    · -- `n = 0`: `Kset 0 δ` is empty because `∑ i : Fin 0, x i = 0 ≠ 1`.
      have h : Kset 0 δ = ∅ := by
        ext x
        simp [Kset]
      rw [h]
      exact continuousOn_empty _
    · -- `n = 1`: `Kset 1 δ` is a subsingleton.
      refine Set.Subsingleton.continuousOn ?_ _
      intro x hx y hy
      funext i
      fin_cases i
      have h1 := hx.2
      have h2 := hy.2
      simp only [Fin.sum_univ_one] at h1 h2
      exact h1.trans h2.symm
  · -- `n ≥ 2`: the quotient of two globally continuous functions.
    rw [not_lt] at hn
    refine ContinuousOn.div ?_ ?_ ?_
    · exact (continuous_finsetProd Finset.univ
        (fun i _ => Real.continuous_sqrt.comp (continuous_apply i))).continuousOn
    · exact (continuous_finsetProd Finset.univ
        (fun i _ => continuous_const.sub (continuous_apply i))).continuousOn
    · intro x hx
      rw [Finset.prod_ne_zero_iff]
      intro i _
      have hne : (Finset.univ.erase i).Nonempty := by
        obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card (by rw [Fintype.card_fin]; omega) i
        exact ⟨j, Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩⟩
      have hsum : ∑ j ∈ Finset.univ.erase i, x j = 1 - x i := by
        have h := Finset.add_sum_erase Finset.univ x (Finset.mem_univ i)
        rw [hx.2] at h
        linarith
      have hpos : 0 < ∑ j ∈ Finset.univ.erase i, x j :=
        Finset.sum_pos (fun j _ => lt_of_lt_of_le hδ (hx.1 j)) hne
      rw [hsum] at hpos
      exact ne_of_gt hpos

end Work.Mostow
