import Mathlib.Analysis.Convex.Deriv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1B

theorem secant_div_le_of_concaveOn {U : ℝ → ℝ} {R : ℝ} (hR : 0 < R)
    (hconc : ConcaveOn ℝ (Set.Icc 0 R) U) (h0 : U 0 = 0) {r : ℝ} (hr0 : 0 < r) (hrR : r < R) :
    U R / R ≤ U r / r := by
  -- Slopes of secants through `0` are antitone on `(Icc 0 R) \ {0}`.
  have hanti := hconc.slope_anti (show (0 : ℝ) ∈ Set.Icc 0 R from ⟨le_refl 0, le_of_lt hR⟩)
  have hmr : r ∈ Set.Icc (0 : ℝ) R \ {0} :=
    ⟨⟨le_of_lt hr0, le_of_lt hrR⟩, by simpa using hr0.ne'⟩
  have hmR : R ∈ Set.Icc (0 : ℝ) R \ {0} :=
    ⟨⟨le_of_lt hR, le_refl R⟩, by simpa using hR.ne'⟩
  -- `r ≤ R` therefore gives `slope U 0 R ≤ slope U 0 r`.
  have hle := hanti hmr hmR (le_of_lt hrR)
  rw [slope_def_field, slope_def_field] at hle
  -- Unfold the slopes at `0` and use `U 0 = 0`.
  simp only [h0, sub_zero] at hle
  exact hle

end Work.BoseFixB1B
