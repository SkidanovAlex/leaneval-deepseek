import Mathlib
import Submission.Work.WilG3.Defs

namespace Work.WilG3

theorem BackwardGrowth {v v' v'' : ℝ → ℝ} {M C a : ℝ}
    (hv : ∀ x ∈ Set.Ioo (0:ℝ) 1, HasDerivAt v (v' x) x)
    (hv' : ∀ x ∈ Set.Ioo (0:ℝ) 1, HasDerivAt v' (v'' x) x)
    (hv'' : ∀ x ∈ Set.Ioo (0:ℝ) 1, v'' x ≤ 0)
    (hM : 0 < M) (ha : 0 < a - 1 / M) (ha1 : a < 1)
    (Ca : C ≤ v' a) :
    C / M ≤ v a - v (a - 1 / M) := by
  -- `1/M > 0`, so both endpoints `a - 1/M` and `a` lie in `(0,1)`.
  have hMpos : (0:ℝ) < 1 / M := one_div_pos.mpr hM
  have hle : a - 1 / M ≤ a := by linarith
  have ha_pos : (0:ℝ) < a := by linarith
  -- `v'' ≤ 0` on `(0,1)` makes `v'` antitone there.
  have hdiff' : DifferentiableOn ℝ v' (Set.Ioo (0:ℝ) 1) :=
    fun x hx => (hv' x hx).differentiableAt.differentiableWithinAt
  have hanti : AntitoneOn v' (Set.Ioo (0:ℝ) 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioo (0:ℝ) 1) hdiff'.continuousOn ?_ ?_
    · rw [interior_Ioo]; exact hdiff'
    · intro x hx
      rw [interior_Ioo] at hx
      rw [(hv' x hx).deriv]
      exact hv'' x hx
  -- Hence on `[a - 1/M, a]` the derivative is bounded below by `C ≤ v' a`.
  have hbound : ∀ x ∈ Set.Ioo (a - 1 / M) a, C ≤ v' x := by
    intro x hx
    have hx1 : x ∈ Set.Ioo (0:ℝ) 1 := ⟨by linarith [hx.1, ha], by linarith [hx.2, ha1]⟩
    have ha_mem : a ∈ Set.Ioo (0:ℝ) 1 := ⟨ha_pos, ha1⟩
    have h : v' a ≤ v' x := hanti hx1 ha_mem (le_of_lt hx.2)
    linarith [Ca]
  have hsub : Set.Icc (a - 1 / M) a ⊆ Set.Ioo (0:ℝ) 1 := by
    intro x hx
    exact ⟨by linarith [hx.1, ha], by linarith [hx.2, ha1]⟩
  have hcont : ContinuousOn v (Set.Icc (a - 1 / M) a) :=
    fun x hx => ((hv x (hsub hx)).continuousAt).continuousWithinAt
  have hder : ∀ x ∈ Set.Ioo (a - 1 / M) a, HasDerivAt v (v' x) x :=
    fun x hx => hv x ⟨by linarith [hx.1, ha], by linarith [hx.2, ha1]⟩
  -- Quantitative mean value estimate on the interval of length `1/M`.
  have key : C * (a - (a - 1 / M)) ≤ v a - v (a - 1 / M) :=
    LeSubOfLeDeriv v v' C (a - 1 / M) a hle hcont hder hbound
  have h1 : a - (a - 1 / M) = 1 / M := by ring
  rw [h1] at key
  have h2 : C / M = C * (1 / M) := by ring
  rw [h2]
  exact key

end Work.WilG3
