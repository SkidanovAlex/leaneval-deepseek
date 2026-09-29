import Mathlib

namespace Work.Holonomy3

/-- For a fixed `a > 0` and `ε > 0`, eventually `log (a·D) ≤ ε·D` along `ℕ`. -/
lemma eventually_log_mul_le {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    ∀ᶠ D : ℕ in Filter.atTop, Real.log (a * (D : ℝ)) ≤ ε * (D : ℝ) := by
  have hk : Filter.Tendsto (fun D : ℕ => a * (D : ℝ)) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop ha tendsto_natCast_atTop_atTop
  have hlit : (fun D : ℕ => Real.log (a * (D:ℝ))) =o[Filter.atTop] (fun D : ℕ => (D:ℝ)) :=
    (Real.isLittleO_log_id_atTop.comp_tendsto hk).trans_isBigO
      (Asymptotics.isBigO_const_mul_self a (fun D : ℕ => (D:ℝ)) Filter.atTop)
  filter_upwards [hlit.def hε] with D hD
  have hD' : |Real.log (a * (D:ℝ))| ≤ ε * (D:ℝ) := by simpa using hD
  exact le_trans (le_abs_self _) hD'

/-- Absorption of a fixed constant `A ≥ 0` and of a multiple `B ≥ 0` of `log(4mD)` into the
linear growth `(m·d·D/2)·(η/3)`, for all large `D`. -/
theorem log_absorb {m d : ℕ} (hm : 0 < m) (hd : 0 < d) {η : ℝ} (hη : 0 < η) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      A + B * Real.log (4 * (m : ℝ) * (D : ℝ)) ≤ ((m : ℝ) * d * D / 2) * (η / 3) := by
  have hmR : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  set c : ℝ := (m:ℝ) * (d:ℝ) * η / 6 with hcdef
  have hc : 0 < c := by rw [hcdef]; positivity
  have hεpos : 0 < c / (2 * (B + 1)) := by positivity
  obtain ⟨D₁, hD₁⟩ := Filter.eventually_atTop.1
    (eventually_log_mul_le (a := 4 * (m:ℝ)) (ε := c / (2 * (B + 1))) (by positivity) hεpos)
  refine ⟨max D₁ (Nat.ceil (2 * A / c)), fun D hD => ?_⟩
  have hD₁' : Real.log (4 * (m:ℝ) * (D:ℝ)) ≤ (c / (2 * (B + 1))) * (D:ℝ) :=
    hD₁ D (le_trans (le_max_left _ _) hD)
  have hA' : A ≤ (c/2) * (D:ℝ) := by
    have hDge : (Nat.ceil (2 * A / c) : ℝ) ≤ (D:ℝ) := by
      exact_mod_cast (le_trans (le_max_right _ _) hD)
    have hceil : 2 * A / c ≤ (Nat.ceil (2 * A / c) : ℝ) := Nat.le_ceil _
    have hAc : (c/2) * (2 * A / c) = A := by field_simp
    calc A = (c/2) * (2 * A / c) := hAc.symm
      _ ≤ (c/2) * (D:ℝ) := mul_le_mul_of_nonneg_left (le_trans hceil hDge) (by positivity)
  have hlog' : B * Real.log (4 * (m:ℝ) * (D:ℝ)) ≤ (c/2) * (D:ℝ) := by
    have hfrac : B / (B + 1) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    have hkey : B * (c / (2 * (B + 1))) = (c/2) * (B / (B + 1)) := by
      field_simp
    have hb1 : B * (c / (2 * (B + 1))) ≤ c/2 := by
      rw [hkey]
      calc (c/2) * (B / (B + 1)) ≤ (c/2) * 1 :=
            mul_le_mul_of_nonneg_left hfrac (by positivity)
        _ = c/2 := by ring
    calc B * Real.log (4 * (m:ℝ) * (D:ℝ))
        ≤ B * ((c / (2 * (B + 1))) * (D:ℝ)) := mul_le_mul_of_nonneg_left hD₁' hB
      _ = (B * (c / (2 * (B + 1)))) * (D:ℝ) := by ring
      _ ≤ (c/2) * (D:ℝ) := mul_le_mul_of_nonneg_right hb1 (Nat.cast_nonneg D)
  have hRHS : ((m:ℝ) * d * D / 2) * (η / 3) = c * (D:ℝ) := by
    rw [hcdef]; ring
  rw [hRHS]
  nlinarith [hA', hlog']

end Work.Holonomy3
