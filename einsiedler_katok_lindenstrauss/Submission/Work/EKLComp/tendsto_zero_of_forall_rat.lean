import Mathlib

namespace Work.EKLComp

/-- A real sequence whose eventual upper bounds include every positive rational and whose
eventual lower bounds include every negative rational converges to `0`.  (Used to convert
"`∀ q ∈ ℚ_{>0}`, eventually `-q ≤ u_n ≤ q`" into `Tendsto u atTop (𝓝 0)`.) -/
theorem tendsto_zero_of_forall_rat (u : ℕ → ℝ)
    (h₁ : ∀ q : ℚ, 0 < q → ∀ᶠ n in Filter.atTop, u n ≤ (q : ℝ))
    (h₂ : ∀ q : ℚ, 0 < q → ∀ᶠ n in Filter.atTop, -(q : ℝ) ≤ u n) :
    Filter.Tendsto u Filter.atTop (nhds 0) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    obtain ⟨q, hq, hqa⟩ := exists_rat_btwn (show (0 : ℝ) < -a by linarith)
    filter_upwards [h₂ q (by exact_mod_cast hq)] with n hn
    linarith
  · intro b hb
    obtain ⟨q, hq, hqb⟩ := exists_rat_btwn (show (0 : ℝ) < b by linarith)
    filter_upwards [h₁ q (by exact_mod_cast hq)] with n hn
    linarith

end Work.EKLComp
