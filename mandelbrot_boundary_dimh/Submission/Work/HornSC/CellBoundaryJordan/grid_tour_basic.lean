import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.grid_tour

/-!
# Elementary properties of the polygonal tour

`tourOn u k` is continuous, starts at `lpt (u 0)`, ends at `lpt (u k)`, is affine on each step
interval `[j/k, (j+1)/k]`, and the `1`-periodic version `tour` agrees with it on `[0,1)`.
-/

namespace Work.HornSC.CellBoundaryJordan

open Set

lemma continuous_stepFrac (i : ℕ) : Continuous (stepFrac i) := by
  unfold stepFrac
  fun_prop

lemma stepFrac_nonneg (i : ℕ) (s : ℝ) : 0 ≤ stepFrac i s := le_max_left _ _

lemma stepFrac_le_one (i : ℕ) (s : ℝ) : stepFrac i s ≤ 1 :=
  max_le zero_le_one (min_le_right _ _)

lemma stepFrac_eq_one {i : ℕ} {s : ℝ} (h : (i : ℝ) + 1 ≤ s) : stepFrac i s = 1 := by
  unfold stepFrac
  rw [min_eq_right (by linarith : (1 : ℝ) ≤ s - (i : ℝ)), max_eq_right zero_le_one]

lemma stepFrac_eq_zero {i : ℕ} {s : ℝ} (h : s ≤ (i : ℝ)) : stepFrac i s = 0 := by
  unfold stepFrac
  rw [min_eq_left (by linarith : s - (i : ℝ) ≤ 1),
    max_eq_left (by linarith : s - (i : ℝ) ≤ 0)]

lemma stepFrac_eq_self {i : ℕ} {s : ℝ} (h1 : (i : ℝ) ≤ s) (h2 : s ≤ (i : ℝ) + 1) :
    stepFrac i s = s - i := by
  unfold stepFrac
  rw [min_eq_left (by linarith : s - (i : ℝ) ≤ 1),
    max_eq_right (by linarith : (0 : ℝ) ≤ s - (i : ℝ))]

lemma continuous_tourOn (u : ℕ → ℤ × ℤ) (k : ℕ) : Continuous (tourOn u k) := by
  unfold tourOn
  refine continuous_const.add (continuous_finset_sum (Finset.range k) (fun i _ => ?_))
  exact ((continuous_stepFrac i).comp (continuous_const.mul continuous_id)).smul continuous_const

lemma tourOn_zero (u : ℕ → ℤ × ℤ) (k : ℕ) : tourOn u k 0 = lpt (u 0) := by
  have h : ∀ i ∈ Finset.range k,
      (stepFrac i ((k : ℝ) * 0)) • (lpt (u (i + 1)) - lpt (u i)) = 0 := by
    intro i _
    rw [stepFrac_eq_zero (by simp)]
    simp
  simp only [tourOn, Finset.sum_congr rfl h, Finset.sum_const_zero, add_zero]

lemma tourOn_one (u : ℕ → ℤ × ℤ) (k : ℕ) : tourOn u k 1 = lpt (u k) := by
  have h : ∀ i ∈ Finset.range k, stepFrac i ((k : ℝ) * 1) = 1 := by
    intro i hi
    have hi' : (i : ℝ) + 1 ≤ (k : ℝ) := by
      have := Finset.mem_range.mp hi
      have : i + 1 ≤ k := this
      exact_mod_cast this
    exact stepFrac_eq_one (by linarith)
  rw [tourOn]
  have h2 : (∑ i ∈ Finset.range k,
      (stepFrac i ((k : ℝ) * 1)) • (lpt (u (i + 1)) - lpt (u i)))
      = ∑ i ∈ Finset.range k, (lpt (u (i + 1)) - lpt (u i)) :=
    Finset.sum_congr rfl (fun i hi => by rw [h i hi, one_smul])
  rw [h2]
  have h3 := Finset.sum_range_sub (fun i => lpt (u i)) k
  rw [h3]
  ring

/-- The walk restricted to the step interval is the affine parametrisation of that step. -/
lemma tourOn_affine {u : ℕ → ℤ × ℤ} {k j : ℕ} (hj : j < k) {t : ℝ}
    (h1 : (j : ℝ) ≤ (k : ℝ) * t) (h2 : (k : ℝ) * t ≤ (j : ℝ) + 1) :
    tourOn u k t = lpt (u j) + ((k : ℝ) * t - (j : ℝ)) • (lpt (u (j + 1)) - lpt (u j)) := by
  rw [tourOn]
  set F : ℕ → ℂ := fun i => (stepFrac i ((k : ℝ) * t)) • (lpt (u (i + 1)) - lpt (u i)) with hF
  have hsplit1 : ∑ i ∈ Finset.range k, F i
      = (∑ i ∈ Finset.range j, F i) + ∑ i ∈ Finset.range (k - j), F (j + i) := by
    conv_lhs => rw [show k = j + (k - j) by omega]
    exact Finset.sum_range_add F j (k - j)
  have hsplit2 : ∑ i ∈ Finset.range (k - j), F (j + i)
      = F j + ∑ i ∈ Finset.range (k - j - 1), F (j + (i + 1)) := by
    conv_lhs => rw [show k - j = (k - j - 1) + 1 by omega]
    rw [Finset.sum_range_succ']
    rw [show j + 0 = j by omega, add_comm]
  have htail : ∑ i ∈ Finset.range (k - j - 1), F (j + (i + 1)) = 0 := by
    refine Finset.sum_eq_zero (fun i hi => ?_)
    have hi' : i < k - j - 1 := Finset.mem_range.mp hi
    have hle : (k : ℝ) * t ≤ ((j + (i + 1) : ℕ) : ℝ) := by
      have h5 : (j : ℝ) + 1 ≤ ((j + (i + 1) : ℕ) : ℝ) := by
        have h6 : j + 1 ≤ j + (i + 1) := by omega
        calc (j : ℝ) + 1 = ((j + 1 : ℕ) : ℝ) := by push_cast; ring
          _ ≤ ((j + (i + 1) : ℕ) : ℝ) := by exact_mod_cast h6
      linarith
    rw [hF]
    simp only
    rw [stepFrac_eq_zero hle, zero_smul]
  have hhead : ∑ i ∈ Finset.range j, F i = lpt (u j) - lpt (u 0) := by
    have hcongr : ∑ i ∈ Finset.range j, F i
        = ∑ i ∈ Finset.range j, (lpt (u (i + 1)) - lpt (u i)) := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hi' : i < j := Finset.mem_range.mp hi
      have hgoal : stepFrac i ((k : ℝ) * t) = 1 := by
        refine stepFrac_eq_one ?_
        have : ((i : ℝ) + 1) ≤ (j : ℝ) := by
          exact_mod_cast Nat.succ_le_of_lt hi'
        linarith
      rw [hF]
      simp only
      rw [hgoal, one_smul]
    rw [hcongr]
    exact Finset.sum_range_sub (fun i => lpt (u i)) j
  rw [hsplit1, hsplit2, htail, add_zero, hhead]
  rw [hF]
  simp only
  rw [stepFrac_eq_self h1 h2]
  abel

end Work.HornSC.CellBoundaryJordan
