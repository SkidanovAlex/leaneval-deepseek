import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXR1Aux

theorem intervalIntegrable_of_tendsto {R : ℝ → ℝ → ℝ} {Nz τ : ℝ} (hNz : 0 ≤ Nz)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hlip : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ x ∈ Set.Ioi (0:ℝ), ∀ y ∈ Set.Ioi (0:ℝ),
      |R x s - R y s| ≤ Nz * |x - y|)
    {z' : ℝ} (hz' : 0 < z')
    {u : ℕ → ℝ} (htu : Filter.Tendsto u Filter.atTop (nhds z')) (hu : ∀ n, 0 < u n)
    (hgood : ∀ n, IntervalIntegrable (fun s => R (u n) s) MeasureTheory.volume (0:ℝ) τ) :
    IntervalIntegrable (fun s => R z' s) MeasureTheory.volume (0:ℝ) τ := by
  -- `R (u n) s - R z' s` is bounded by `Nz * |u n - z'|`, which tends to `0`.
  have hlim0 : Filter.Tendsto (fun n => Nz * |u n - z'|) Filter.atTop (nhds 0) := by
    have h2 : Filter.Tendsto (fun n : ℕ => |u n - z'|) Filter.atTop (nhds 0) := by
      have h3 := (htu.sub (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℕ => z') Filter.atTop (nhds z'))).abs
      simpa using h3
    simpa using h2.const_mul Nz
  -- pick one index for which the displacement is at most `1`
  obtain ⟨N, hN⟩ : ∃ N : ℕ, Nz * |u N - z'| < 1 :=
    (hlim0.eventually (Iio_mem_nhds zero_lt_one)).exists
  have hsubset : Set.Ioc (0:ℝ) τ ⊆ Set.Icc (0:ℝ) 1 :=
    fun s hs => ⟨le_of_lt hs.1, le_trans hs.2 hτ1⟩
  -- pointwise convergence on the integration interval
  have hconv : ∀ s ∈ Set.Ioc (0:ℝ) τ,
      Filter.Tendsto (fun n => R (u n) s) Filter.atTop (nhds (R z' s)) := by
    intro s hs
    have hs' : s ∈ Set.Icc (0:ℝ) 1 := hsubset hs
    have hb : ∀ n, |R (u n) s - R z' s| ≤ Nz * |u n - z'| :=
      fun n => hlip s hs' (u n) (hu n) z' hz'
    have habs : Filter.Tendsto (fun n => |R (u n) s - R z' s|) Filter.atTop (nhds 0) :=
      squeeze_zero (fun n => abs_nonneg _) hb hlim0
    have hsub : Filter.Tendsto (fun n => R (u n) s - R z' s) Filter.atTop (nhds 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa [Real.norm_eq_abs] using habs)
    have h4 := hsub.add (tendsto_const_nhds :
      Filter.Tendsto (fun _ : ℕ => R z' s) Filter.atTop (nhds (R z' s)))
    simpa using h4
  -- hence `R z'` is measurable, as an a.e. limit of the integrable `R (u n)`
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun s => R z' s)
      (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) τ)) :=
    aestronglyMeasurable_of_tendsto_ae Filter.atTop
      (fun n => (hgood n).1.aestronglyMeasurable)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc hconv)
  have hconst : MeasureTheory.Integrable (fun _ : ℝ => (1:ℝ))
      (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) τ)) :=
    (intervalIntegrable_const (μ := MeasureTheory.volume) (a := (0:ℝ)) (b := τ)
      (c := (1:ℝ))).1
  have hdom : MeasureTheory.Integrable (fun s => ‖R (u N) s‖ + 1)
      (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) τ)) :=
    ((hgood N).1.norm).add hconst
  -- and it is dominated by the integrable function `|R (u N)| + 1`
  have hbdry : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) τ)),
      ‖R z' s‖ ≤ ‖R (u N) s‖ + 1 :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun s hs => by
      have hs' : s ∈ Set.Icc (0:ℝ) 1 := hsubset hs
      have h1 : |R (u N) s - R z' s| ≤ Nz * |u N - z'| := hlip s hs' (u N) (hu N) z' hz'
      have h2 : |R z' s - R (u N) s| < 1 := by
        rw [abs_sub_comm]; exact lt_of_le_of_lt h1 hN
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      have h3 : |R z' s| ≤ |R z' s - R (u N) s| + |R (u N) s| :=
        calc |R z' s| = |(R z' s - R (u N) s) + R (u N) s| := by congr 1; ring
          _ ≤ _ := abs_add_le _ _
      linarith)
  constructor
  · exact MeasureTheory.Integrable.mono' hdom hmeas hbdry
  · rw [Set.Ioc_eq_empty_iff.mpr (not_lt.mpr hτ0)]
    exact MeasureTheory.integrableOn_empty

end Work.FTS_RegExport.RXR1Aux
