import Mathlib
import Submission.Work.WilG3.Defs

namespace Work.WilG3

theorem ForwardGrowth {v v' v'' : ℝ → ℝ} {M C a : ℝ}
    (hv : ∀ x ∈ Set.Ioo (0:ℝ) 1, HasDerivAt v (v' x) x)
    (hv' : ∀ x ∈ Set.Ioo (0:ℝ) 1, HasDerivAt v' (v'' x) x)
    (hv'' : ∀ x ∈ Set.Ioo (0:ℝ) 1, 0 ≤ v'' x)
    (hM : 0 < M) (ha : 0 < a) (hab : a + 1 / M < 1)
    (Ca : C ≤ v' a) :
    C / M ≤ v (a + 1 / M) - v a := by
  have hMpos : 0 < 1 / M := one_div_pos.mpr hM
  have hlt : a < a + 1 / M := lt_add_of_pos_right a hMpos
  have ha1 : a < 1 := by linarith
  have haIoo : a ∈ Set.Ioo (0:ℝ) 1 := ⟨ha, ha1⟩
  -- `v'` is monotone on `(0,1)` because `v'' ≥ 0` there.
  have hmono : MonotoneOn v' (Set.Ioo (0:ℝ) 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (D := Set.Ioo (0:ℝ) 1) (f := v') (f' := v'')
      (convex_Ioo 0 1) ?_ ?_ ?_
    · intro x hx
      exact (hv' x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioo] at hx
      exact (hv' x hx).hasDerivWithinAt
    · intro x hx
      rw [interior_Ioo] at hx
      exact hv'' x hx
  -- hence `v' ≥ v' a ≥ C` on the whole interval `(a, a+1/M)`.
  have hC : ∀ x ∈ Set.Ioo a (a + 1 / M), C ≤ v' x := by
    intro x hx
    have hxIoo : x ∈ Set.Ioo (0:ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact Ca.trans (hmono haIoo hxIoo (le_of_lt hx.1))
  have hcont : ContinuousOn v (Set.Icc a (a + 1 / M)) := by
    intro x hx
    have hxIoo : x ∈ Set.Ioo (0:ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact (hv x hxIoo).continuousAt.continuousWithinAt
  have hder : ∀ x ∈ Set.Ioo a (a + 1 / M), HasDerivAt v (v' x) x := by
    intro x hx
    exact hv x ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have h := LeSubOfLeDeriv v v' C a (a + 1 / M) (le_of_lt hlt) hcont hder hC
  have hsub : a + 1 / M - a = 1 / M := by ring
  rw [hsub, mul_one_div] at h
  exact h

end Work.WilG3
