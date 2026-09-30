import Mathlib
import Submission.Work.BMF.Ceps2_add_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- Adding the `(T₂-T₁)/(2π)·log` correction (bounded via `|T₁-T₂| ≤ 4πC₀·C2c·N` and
`t ≥ NL/C₀`) to a bound `|e| ≤ Ceps2/L` keeps the total `≤ C1c/L`. -/
theorem eps2_final_bound (k : ℕ) (C₀ L N t Δ e : ℝ) (hC₀ : 1 ≤ C₀) (hL : 0 < L)
    (hC2c : 0 ≤ C2c k C₀)
    (hDelta : |Δ| ≤ 4 * Real.pi * C₀ * C2c k C₀ * N)
    (ht : N * L / C₀ ≤ t) (ht0 : 0 < t) (he : |e| ≤ Ceps2 k C₀ / L) :
    |e - Δ / (2 * Real.pi) / t| ≤ C1c k C₀ / L := by
  have hC0pos : 0 < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have h2pit : (0 : ℝ) < 2 * Real.pi * t := mul_pos h2pi ht0
  -- ## The correction term.
  have hcorr : |Δ / (2 * Real.pi) / t| ≤ 2 * C₀ ^ 2 * C2c k C₀ / L := by
    have hrew : |Δ / (2 * Real.pi) / t| = |Δ| / (2 * Real.pi * t) := by
      rw [abs_div, abs_div, abs_of_pos h2pi, abs_of_pos ht0, div_div]
    rw [hrew]
    -- `N / t ≤ C₀ / L` from the hypothesis `N * L / C₀ ≤ t`.
    have hNL : N * L ≤ C₀ * t := by
      have h1 : (N * L / C₀) * C₀ ≤ t * C₀ :=
        mul_le_mul_of_nonneg_right ht (le_of_lt hC0pos)
      rw [div_mul_cancel₀ _ (ne_of_gt hC0pos)] at h1
      linarith
    have hNt : N / t ≤ C₀ / L := (div_le_div_iff₀ ht0 hL).mpr hNL
    have hfac : (0 : ℝ) ≤ 2 * C₀ * C2c k C₀ :=
      mul_nonneg (by positivity) hC2c
    have hb1 : |Δ| / (2 * Real.pi * t) ≤
        (4 * Real.pi * C₀ * C2c k C₀ * N) / (2 * Real.pi * t) :=
      div_le_div_of_nonneg_right hDelta (le_of_lt h2pit)
    have hmid : (4 * Real.pi * C₀ * C2c k C₀ * N) / (2 * Real.pi * t) =
        2 * C₀ * C2c k C₀ * (N / t) := by
      field_simp
      ring
    have hb2 : 2 * C₀ * C2c k C₀ * (N / t) ≤ 2 * C₀ * C2c k C₀ * (C₀ / L) :=
      mul_le_mul_of_nonneg_left hNt hfac
    have hfin : 2 * C₀ * C2c k C₀ * (C₀ / L) = 2 * C₀ ^ 2 * C2c k C₀ / L := by
      field_simp
    calc |Δ| / (2 * Real.pi * t)
        ≤ (4 * Real.pi * C₀ * C2c k C₀ * N) / (2 * Real.pi * t) := hb1
      _ = 2 * C₀ * C2c k C₀ * (N / t) := hmid
      _ ≤ 2 * C₀ * C2c k C₀ * (C₀ / L) := hb2
      _ = 2 * C₀ ^ 2 * C2c k C₀ / L := hfin
  -- ## Triangle inequality and the joint constant estimate.
  have htri : |e - Δ / (2 * Real.pi) / t| ≤ |e| + |Δ / (2 * Real.pi) / t| := by
    have h := abs_add_le e (-(Δ / (2 * Real.pi) / t))
    rw [abs_neg] at h
    simpa [sub_eq_add_neg] using h
  have hsum : Ceps2 k C₀ + 2 * C₀ ^ 2 * C2c k C₀ ≤ C1c k C₀ := Ceps2_add_le k C₀ hC₀
  calc |e - Δ / (2 * Real.pi) / t|
      ≤ |e| + |Δ / (2 * Real.pi) / t| := htri
    _ ≤ Ceps2 k C₀ / L + 2 * C₀ ^ 2 * C2c k C₀ / L := add_le_add he hcorr
    _ = (Ceps2 k C₀ + 2 * C₀ ^ 2 * C2c k C₀) / L := by rw [add_div]
    _ ≤ C1c k C₀ / L := (div_le_div_iff_of_pos_right hL).mpr hsum

end Work.BMF
