import Mathlib.NumberTheory.NumberField.DedekindZeta

namespace Commons.NumberTheory.NumberField.DedekindZeta

open Filter Topology

/-- The real part of the Dedekind zeta function of a number field tends to `+∞` as `s → 1⁺`.
This is the "simple pole at `s = 1`" in the form needed for Dirichlet density arguments: it
follows immediately from the Dirichlet class number formula
`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT` together with the positivity of the
residue `NumberField.dedekindZeta_residue_pos`. -/
theorem tendsto_re_nhdsGT_atTop (K : Type*) [Field K] [NumberField K] :
    Filter.Tendsto (fun s : ℝ => (NumberField.dedekindZeta K (s : ℂ)).re) (𝓝[>] 1) atTop := by
  -- The residue `c` at `s = 1` is positive.
  have hc : 0 < NumberField.dedekindZeta_residue K := NumberField.dedekindZeta_residue_pos K
  -- Dirichlet class number formula, after taking real parts: `(s - 1) * re ζ(s) → c`.
  have hA : Tendsto (fun s : ℝ => ((s - 1 : ℂ) * NumberField.dedekindZeta K (s : ℂ)).re)
      (𝓝[>] (1 : ℝ)) (𝓝 (NumberField.dedekindZeta_residue K)) := by
    have h := NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K
    have h2 : Tendsto (fun s : ℝ => ((s - 1 : ℂ) * NumberField.dedekindZeta K (s : ℂ)).re)
        (𝓝[>] (1 : ℝ)) (𝓝 ((NumberField.dedekindZeta_residue K : ℂ)).re) := by
      have hcomp :=
        (Complex.continuous_re.tendsto ((NumberField.dedekindZeta_residue K : ℝ) : ℂ)).comp h
      simpa only [Function.comp_def] using hcomp
    simpa using h2
  -- `s - 1 → 0⁺` as `s → 1⁺`.
  have hf : Tendsto (fun s : ℝ => s - 1) (𝓝[>] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    have h1 : Tendsto (fun s : ℝ => s - 1) (𝓝 (1 : ℝ)) (𝓝 (0 : ℝ)) := by
      simpa using (continuous_sub_right (1 : ℝ)).tendsto (1 : ℝ)
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (h1.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact sub_pos.mpr (Set.mem_Ioi.mp hs)
  -- Hence `re ζ(s) = ((s - 1) * re ζ(s)) / (s - 1)` tends to `+∞`.
  have hdiv : Tendsto
      (fun s : ℝ => ((s - 1 : ℂ) * NumberField.dedekindZeta K (s : ℂ)).re / (s - 1))
      (𝓝[>] (1 : ℝ)) atTop := by
    simp only [div_eq_mul_inv]
    exact hA.pos_mul_atTop hc hf.inv_tendsto_nhdsGT_zero
  refine Tendsto.congr' ?_ hdiv
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hsne : s - 1 ≠ 0 := ne_of_gt (sub_pos.mpr (Set.mem_Ioi.mp hs))
  have hAeq : ((s - 1 : ℂ) * NumberField.dedekindZeta K (s : ℂ)).re
      = (s - 1) * (NumberField.dedekindZeta K (s : ℂ)).re := by
    simp [Complex.mul_re]
  rw [hAeq, mul_div_cancel_left₀ _ hsne]

end Commons.NumberTheory.NumberField.DedekindZeta