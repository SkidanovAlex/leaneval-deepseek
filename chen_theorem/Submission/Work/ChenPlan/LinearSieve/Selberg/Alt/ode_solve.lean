import Mathlib

namespace Work.ChenPlan.LinearSieve.Selberg.Alt

open Filter Topology MeasureTheory intervalIntegral Set

/-- The continuous extension of `s ↦ (1 - exp (-s)) / s` at `s = 0`, where the value is `1`. -/
private noncomputable def odeFt (s : ℝ) : ℝ := if s = 0 then 1 else (1 - Real.exp (-s)) / s

private lemma odeFt_eq (s : ℝ) (hs : s ≠ 0) : odeFt s = (1 - Real.exp (-s)) / s := by
  rw [odeFt, if_neg hs]

private lemma continuous_odeFt : Continuous odeFt := by
  rw [continuous_iff_continuousAt]
  intro s
  by_cases hs : s = 0
  · subst hs
    rw [ContinuousAt, odeFt, if_pos rfl]
    have hg : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-1) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => -t) (-1) 0 := by simpa using hasDerivAt_neg (0:ℝ)
      simpa using h1.exp
    have hslope :
        Tendsto (fun t : ℝ => - slope (fun t : ℝ => Real.exp (-t)) 0 t) (𝓝[≠] 0) (𝓝 1) := by
      simpa using hg.tendsto_slope.neg
    have hbase : Tendsto (fun t : ℝ => (1 - Real.exp (-t)) / t) (𝓝[≠] 0) (𝓝 1) := by
      refine hslope.congr' ?_
      filter_upwards with t
      rw [slope_def_field]; simp only [sub_zero, Real.exp_zero, neg_zero]; ring
    have hne : Tendsto odeFt (𝓝[≠] 0) (𝓝 1) := by
      refine hbase.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [odeFt, if_neg (by simpa using ht)]
    rw [← nhdsNE_sup_pure (0:ℝ), tendsto_sup]
    exact ⟨hne, by simpa [odeFt] using tendsto_pure_nhds odeFt (0:ℝ)⟩
  · have hbase : ContinuousAt (fun t : ℝ => (1 - Real.exp (-t)) / t) s := by
      apply ContinuousAt.div
      · fun_prop
      · fun_prop
      · exact hs
    refine hbase.congr_of_eventuallyEq ?_
    filter_upwards [eventually_ne_nhds hs] with t ht
    rw [odeFt, if_neg ht]

private lemma integral_base_odeFt (L : ℝ) :
    (∫ s in (0:ℝ)..L, (1 - Real.exp (-s)) / s) = ∫ s in (0:ℝ)..L, odeFt s := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [MeasureTheory.Measure.ae_ne (volume : Measure ℝ) 0] with x hx _
  exact (odeFt_eq x hx).symm

theorem ode_solve (φ : ℝ → ℝ) (hcont : ContinuousOn φ (Set.Ici 0)) (h0 : φ 0 = 1)
    (hode : ∀ L : ℝ, 0 ≤ L → L * φ L = ∫ s in (0:ℝ)..L, Real.exp (-s) * φ s) :
    ∀ L : ℝ, 0 ≤ L → φ L = Real.exp (-(∫ s in (0:ℝ)..L, (1 - Real.exp (-s))/s)) := by
  intro L hL
  -- `G u = ∫₀ᵘ (1 - e^{-s})/s ds`, the continuous version of the exponent.
  set G : ℝ → ℝ := fun u => ∫ s in (0:ℝ)..u, odeFt s with hG
  have hGderiv : ∀ u, HasDerivAt G (odeFt u) u := by
    intro u
    simpa [hG] using (continuous_odeFt.integral_hasStrictDerivAt (0:ℝ) u).hasDerivAt
  have hGcont : Continuous G := continuous_iff_continuousAt.mpr fun u => (hGderiv u).continuousAt
  -- `ψ u = φ u * exp (G u)`; we show it is constantly `1`.
  set ψ : ℝ → ℝ := fun u => φ u * Real.exp (G u) with hψ
  have hψcont : ContinuousOn ψ (Set.Ici 0) := by
    rw [hψ]
    exact hcont.mul ((Real.continuous_exp.comp hGcont).continuousOn)
  -- Derivative of `φ` on `(0, ∞)`.
  have hφderiv : ∀ u, 0 < u → HasDerivAt φ ((Real.exp (-u) - 1) * φ u / u) u := by
    intro u hu
    have hEcont : ContinuousOn (fun s => Real.exp (-s) * φ s) (Set.Icc 0 u) :=
      ((Real.continuous_exp.comp continuous_neg).continuousOn).mul (hcont.mono (fun x hx => hx.1))
    have hEint : IntervalIntegrable (fun s => Real.exp (-s) * φ s) volume 0 u :=
      hEcont.intervalIntegrable_of_Icc hu.le
    have hφc : ContinuousAt φ u := hcont.continuousAt (Ici_mem_nhds hu)
    have hEcontAt : ContinuousAt (fun s => Real.exp (-s) * φ s) u :=
      ((Real.continuous_exp.comp continuous_neg).continuousAt).mul hφc
    have hEcontIoi : ContinuousOn (fun s => Real.exp (-s) * φ s) (Set.Ioi 0) :=
      ((Real.continuous_exp.comp continuous_neg).continuousOn).mul
        (hcont.mono (fun x hx => le_of_lt (Set.mem_Ioi.mp hx)))
    have hEsm : StronglyMeasurableAtFilter (fun s => Real.exp (-s) * φ s) (𝓝 u) volume :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hEcontIoi u hu
    have hF : HasDerivAt (fun x => ∫ s in (0:ℝ)..x, Real.exp (-s) * φ s) (Real.exp (-u) * φ u) u :=
      integral_hasDerivAt_right hEint hEsm hEcontAt
    have hquot := hF.div (hasDerivAt_id u) hu.ne'
    have hφderiv_raw :
        HasDerivAt φ ((Real.exp (-u) * φ u * u - (∫ s in (0:ℝ)..u, Real.exp (-s) * φ s)) / u ^ 2) u := by
      have h := hquot.congr_of_eventuallyEq
        (show φ =ᶠ[𝓝 u] (fun x => (∫ s in (0:ℝ)..x, Real.exp (-s) * φ s) / x) from by
          filter_upwards [isOpen_Ioi.mem_nhds hu] with x hx
          have hx' := hode x (le_of_lt hx)
          rw [eq_div_iff (ne_of_gt hx), mul_comm]
          exact hx')
      simpa only [id_eq, mul_one] using h
    have hFu : (∫ s in (0:ℝ)..u, Real.exp (-s) * φ s) = u * φ u := (hode u (le_of_lt hu)).symm
    have hval : (Real.exp (-u) * φ u * u - (∫ s in (0:ℝ)..u, Real.exp (-s) * φ s)) / u ^ 2
        = (Real.exp (-u) - 1) * φ u / u := by
      rw [hFu]; field_simp
    rw [hval] at hφderiv_raw
    exact hφderiv_raw
  -- `ψ` has vanishing derivative on `(0, ∞)`.
  have hψderiv : ∀ u, 0 < u → HasDerivAt ψ 0 u := by
    intro u hu
    have h1 : HasDerivAt (fun x => Real.exp (G x)) (Real.exp (G u) * odeFt u) u := (hGderiv u).exp
    have h2 : HasDerivAt (fun x => φ x * Real.exp (G x))
        (((Real.exp (-u) - 1) * φ u / u) * Real.exp (G u)
          + φ u * (Real.exp (G u) * odeFt u)) u :=
      (hφderiv u hu).mul h1
    have hzero : ((Real.exp (-u) - 1) * φ u / u) * Real.exp (G u)
        + φ u * (Real.exp (G u) * odeFt u) = 0 := by
      rw [odeFt_eq u hu.ne']
      field_simp
      ring
    rw [hzero] at h2
    rw [hψ]
    exact h2
  have hG0 : G 0 = 0 := by simp [hG]
  have hψ0 : ψ 0 = 1 := by simp [hψ, hG0, h0]
  rcases eq_or_lt_of_le hL with hL0 | hLpos
  · subst hL0
    simp [h0]
  · -- `ψ` is constant on `[ε, L]` for every `ε ∈ (0, L)`, hence `ψ L = ψ 0 = 1`.
    have hEq : ∀ ε, 0 < ε → ε < L → ψ L = ψ ε := by
      intro ε hε hεL
      have hcont' : ContinuousOn ψ (Set.Icc ε L) := hψcont.mono (fun x hx => le_trans hε.le hx.1)
      have hderiv' : ∀ x ∈ Set.Ico ε L, HasDerivWithinAt ψ 0 (Set.Ici x) x := by
        intro x hx
        exact (hψderiv x (lt_of_lt_of_le hε hx.1)).hasDerivWithinAt
      exact constant_of_has_deriv_right_zero hcont' hderiv' L ⟨hεL.le, le_rfl⟩
    have htendψL : Tendsto ψ (𝓝[>] 0) (𝓝 (ψ L)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hLpos)] with ε hε hεL
      exact hEq ε hε hεL
    have htendψ0 : Tendsto ψ (𝓝[>] 0) (𝓝 (ψ 0)) :=
      (hψcont.continuousWithinAt (Set.mem_Ici.mpr le_rfl)).mono_left
        (nhdsWithin_mono 0 Set.Ioi_subset_Ici_self)
    have hψL : ψ L = 1 := (tendsto_nhds_unique htendψL htendψ0).trans hψ0
    have hthis : φ L * Real.exp (G L) = 1 := by simpa [hψ] using hψL
    have hφL : φ L = Real.exp (-(G L)) := by
      rw [Real.exp_neg, eq_inv_of_mul_eq_one_left hthis]
    have hGL : G L = ∫ s in (0:ℝ)..L, odeFt s := congrFun hG L
    rw [hφL, hGL, ← integral_base_odeFt L]

end Work.ChenPlan.LinearSieve.Selberg.Alt
