import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

namespace Commons.Analysis.Real

open Filter

theorem tendsto_halfway {s y : ℝ} (hs : 0 < s) :
    Filter.Tendsto
      (fun u : ℝ => u / ((u + y) ^ 2 + s ^ 2))
      Filter.atTop (nhds 0) := by
  have hnonneg : ∀ᶠ u : ℝ in atTop, 0 ≤ u / ((u + y) ^ 2 + s ^ 2) := by
    filter_upwards [eventually_ge_atTop 0] with u hu using div_nonneg hu (by positivity)
  have hbound : ∀ᶠ u : ℝ in atTop, u / ((u + y) ^ 2 + s ^ 2) ≤ 4 / u := by
    filter_upwards [eventually_ge_atTop (max (2 * |y|) 1)] with u hu
    have hu1 : (1:ℝ) ≤ u := le_trans (le_max_right _ _) hu
    have hu0 : (0:ℝ) < u := lt_of_lt_of_le one_pos hu1
    have h2y : 2 * |y| ≤ u := le_trans (le_max_left _ _) hu
    have hy_le : |y| ≤ u / 2 := by linarith
    have hy_ge : -(u/2) ≤ y := (abs_le.mp hy_le).1
    have hupos : (0:ℝ) < u + y := by linarith
    have hle : u / 2 ≤ u + y := by linarith
    have hx : (0:ℝ) < u / 2 := by linarith
    have hsq : (u / 2) ^ 2 ≤ (u + y) ^ 2 := by
      have := mul_self_le_mul_self hx.le hle
      nlinarith [this]
    have hs2 : (0:ℝ) < s ^ 2 := by positivity
    have hden : u ^ 2 / 4 ≤ (u + y) ^ 2 + s ^ 2 := by nlinarith [hsq, hs2]
    have hquarter : (0:ℝ) < u ^ 2 / 4 := by positivity
    have hb : u / ((u + y) ^ 2 + s ^ 2) ≤ u / (u ^ 2 / 4) :=
      div_le_div_of_nonneg_left hu0.le hquarter hden
    have hcalc : u / (u ^ 2 / 4) = 4 / u := by
      have hne : u ≠ 0 := ne_of_gt hu0
      field_simp
    linarith [hb, hcalc.le, hcalc.ge]
  have hg : Filter.Tendsto (fun u : ℝ => 4 / u) Filter.atTop (nhds 0) := by
    have hinv : Filter.Tendsto (fun u : ℝ => u⁻¹) Filter.atTop (nhds 0) :=
      Filter.Tendsto.inv_tendsto_atTop tendsto_id
    have := Filter.Tendsto.const_mul (4:ℝ) hinv
    simpa [div_eq_mul_inv] using this
  exact squeeze_zero' hnonneg hbound hg

theorem tendsto_poisson_hilbert_antideriv {s y : ℝ} (hs : 0 < s) :
    Filter.Tendsto
      (fun u : ℝ =>
        -(s / (2 * (y ^ 2 + s ^ 2))) *
            (Real.log ((u - y) ^ 2 + s ^ 2) - Real.log ((u + y) ^ 2 + s ^ 2))
          + (y / (y ^ 2 + s ^ 2)) *
            (Real.arctan ((u - y) / s) + Real.arctan ((u + y) / s)))
      Filter.atTop (nhds (Real.pi * y / (y ^ 2 + s ^ 2))) := by
  have hA_ne : ∀ u : ℝ, (u - y) ^ 2 + s ^ 2 ≠ 0 := fun u => by positivity
  have hB_ne : ∀ u : ℝ, (u + y) ^ 2 + s ^ 2 ≠ 0 := fun u => by positivity
  -- The ratio tends to 1
  have hu : Filter.Tendsto (fun u : ℝ => u / ((u + y) ^ 2 + s ^ 2)) Filter.atTop (nhds 0) :=
    tendsto_halfway hs
  have hcm : Filter.Tendsto
      (fun u : ℝ => (-(4*y)) * (u / ((u + y) ^ 2 + s ^ 2))) Filter.atTop (nhds 0) := by
    have h := Filter.Tendsto.const_mul (-(4*y)) hu
    simpa using h
  have hnum : Filter.Tendsto
      (fun u : ℝ => (-(4*y) * u) / ((u + y) ^ 2 + s ^ 2)) Filter.atTop (nhds 0) :=
    Filter.Tendsto.congr (fun u => (mul_div_assoc _ _ _).symm) hcm
  have hconst : Filter.Tendsto (fun _ : ℝ => (1:ℝ)) Filter.atTop (nhds 1) := tendsto_const_nhds
  have hkey : Filter.Tendsto
      (fun u : ℝ => 1 + (-(4*y) * u) / ((u + y) ^ 2 + s ^ 2)) Filter.atTop (nhds 1) := by
    have := Filter.Tendsto.add hconst hnum
    simpa using this
  have hcongr : ∀ u : ℝ,
      1 + (-(4*y) * u) / ((u + y) ^ 2 + s ^ 2)
        = ((u - y) ^ 2 + s ^ 2) / ((u + y) ^ 2 + s ^ 2) := by
    intro u
    have hb : (u + y) ^ 2 + s ^ 2 ≠ 0 := hB_ne u
    have heq : (u - y) ^ 2 + s ^ 2 = ((u + y) ^ 2 + s ^ 2) + (-(4*y) * u) := by ring
    rw [heq, add_div, div_self hb]
  have hratio : Filter.Tendsto
      (fun u : ℝ => ((u - y) ^ 2 + s ^ 2) / ((u + y) ^ 2 + s ^ 2)) Filter.atTop (nhds 1) :=
    Filter.Tendsto.congr hcongr hkey
  -- log difference tends to 0
  have hlogdiv : Filter.Tendsto
      (fun u : ℝ => Real.log (((u - y) ^ 2 + s ^ 2) / ((u + y) ^ 2 + s ^ 2)))
      Filter.atTop (nhds 0) := by
    have := hratio.log (by norm_num : (1:ℝ) ≠ 0)
    simpa using this
  have hlogdiff : Filter.Tendsto
      (fun u : ℝ => Real.log ((u - y) ^ 2 + s ^ 2) - Real.log ((u + y) ^ 2 + s ^ 2))
      Filter.atTop (nhds 0) := by
    refine hlogdiv.congr' ?_
    filter_upwards with u
    rw [Real.log_div (hA_ne u) (hB_ne u)]
  have hterm1 : Filter.Tendsto
      (fun u : ℝ => -(s / (2 * (y ^ 2 + s ^ 2))) *
            (Real.log ((u - y) ^ 2 + s ^ 2) - Real.log ((u + y) ^ 2 + s ^ 2)))
      Filter.atTop (nhds 0) := by
    have := Filter.Tendsto.const_mul (-(s / (2 * (y ^ 2 + s ^ 2)))) hlogdiff
    simpa using this
  -- arctan pieces
  have hcompA : Filter.Tendsto (fun u : ℝ => (u - y) / s) Filter.atTop Filter.atTop := by
    have h := Filter.Tendsto.atTop_mul_const (inv_pos.mpr hs)
      (tendsto_atTop_add_const_right atTop (-y) tendsto_id)
    simpa [div_eq_mul_inv, sub_eq_add_neg] using h
  have hcompB : Filter.Tendsto (fun u : ℝ => (u + y) / s) Filter.atTop Filter.atTop := by
    have h := Filter.Tendsto.atTop_mul_const (inv_pos.mpr hs)
      (tendsto_atTop_add_const_right atTop y tendsto_id)
    simpa [div_eq_mul_inv] using h
  have harcA : Filter.Tendsto (fun u : ℝ => Real.arctan ((u - y) / s)) Filter.atTop
      (nhds (Real.pi / 2)) :=
    (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp hcompA
  have harcB : Filter.Tendsto (fun u : ℝ => Real.arctan ((u + y) / s)) Filter.atTop
      (nhds (Real.pi / 2)) :=
    (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp hcompB
  have hsum : Filter.Tendsto
      (fun u : ℝ => Real.arctan ((u - y) / s) + Real.arctan ((u + y) / s))
      Filter.atTop (nhds (Real.pi / 2 + Real.pi / 2)) := harcA.add harcB
  have hterm2 : Filter.Tendsto
      (fun u : ℝ => (y / (y ^ 2 + s ^ 2)) *
            (Real.arctan ((u - y) / s) + Real.arctan ((u + y) / s)))
      Filter.atTop (nhds ((y / (y ^ 2 + s ^ 2)) * (Real.pi / 2 + Real.pi / 2))) :=
    Filter.Tendsto.const_mul (y / (y ^ 2 + s ^ 2)) hsum
  -- combine
  have htotal : Filter.Tendsto
      (fun u : ℝ => -(s / (2 * (y ^ 2 + s ^ 2))) *
            (Real.log ((u - y) ^ 2 + s ^ 2) - Real.log ((u + y) ^ 2 + s ^ 2))
          + (y / (y ^ 2 + s ^ 2)) *
            (Real.arctan ((u - y) / s) + Real.arctan ((u + y) / s)))
      Filter.atTop (nhds (0 + (y / (y ^ 2 + s ^ 2)) * (Real.pi / 2 + Real.pi / 2))) :=
    hterm1.add hterm2
  have hlim : (0:ℝ) + (y / (y ^ 2 + s ^ 2)) * (Real.pi / 2 + Real.pi / 2)
      = Real.pi * y / (y ^ 2 + s ^ 2) := by ring
  rw [hlim] at htotal
  exact htotal

end Commons.Analysis.Real