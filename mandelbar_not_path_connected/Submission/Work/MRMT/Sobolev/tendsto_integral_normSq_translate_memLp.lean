import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Sobolev

open MeasureTheory Filter Set
open scoped Topology Pointwise

/-- Continuity of translation in `L²` for a continuous compactly supported function on `ℂ`:
`∫ z, ‖φ (z - t) - φ z‖ ^ 2 → 0` as `t → 0`.  This is proved by dominated convergence: the
pointwise difference is dominated, uniformly for small `t`, by a constant on a compact set
(namely the support of `φ` thickened by the unit ball). -/
lemma tendsto_integral_normSq_translate_continuous_hasCompactSupport {φ : ℂ → ℂ}
    (hcont : Continuous φ) (hsupp : HasCompactSupport φ) :
    Filter.Tendsto (fun t : ℂ => ∫ z, ‖φ (z - t) - φ z‖ ^ 2) (nhds 0) (nhds (0 : ℝ)) := by
  obtain ⟨M, hM⟩ := (hsupp.isCompact_range hcont).isBounded.exists_norm_le
  have hKc : IsCompact (tsupport φ + Metric.closedBall (0:ℂ) 1) :=
    hsupp.isCompact.add (isCompact_closedBall 0 1)
  have hbound_int : Integrable
      ((tsupport φ + Metric.closedBall (0:ℂ) 1).indicator fun _ => (2 * M) ^ 2)
      (volume : Measure ℂ) := by
    rw [integrable_indicator_iff hKc.measurableSet]
    exact integrableOn_const hKc.measure_lt_top.ne (by simp [ENNReal.mul_ne_top])
  have hsm : ∀ᶠ t in nhds (0:ℂ),
      AEStronglyMeasurable (fun z => ‖φ (z - t) - φ z‖ ^ 2) volume := by
    filter_upwards with t
    fun_prop
  have hdom : ∀ᶠ t in nhds (0:ℂ), ∀ᵐ z ∂(volume : Measure ℂ),
      ‖(‖φ (z - t) - φ z‖ ^ 2)‖ ≤
        ((tsupport φ + Metric.closedBall (0:ℂ) 1).indicator fun _ => (2 * M) ^ 2) z := by
    filter_upwards [Metric.closedBall_mem_nhds (0:ℂ) (by norm_num : (0:ℝ) < 1)] with t ht
    filter_upwards with z
    by_cases hz : z ∈ tsupport φ + Metric.closedBall (0:ℂ) 1
    · rw [Set.indicator_of_mem hz, Real.norm_of_nonneg (by positivity)]
      have h1 : ‖φ (z - t)‖ ≤ M := hM _ (Set.mem_range_self _)
      have h2 : ‖φ z‖ ≤ M := hM _ (Set.mem_range_self _)
      have hle : ‖φ (z - t) - φ z‖ ≤ 2 * M := by
        calc ‖φ (z - t) - φ z‖ ≤ ‖φ (z - t)‖ + ‖φ z‖ := norm_sub_le _ _
          _ ≤ M + M := add_le_add h1 h2
          _ = 2 * M := by ring
      exact pow_le_pow_left₀ (norm_nonneg _) hle 2
    · rw [Set.indicator_of_notMem hz, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hzt : z - t ∉ tsupport φ := fun hcon =>
        hz (Set.mem_add.mpr ⟨z - t, hcon, t, ht, by ring⟩)
      have hz0 : z ∉ tsupport φ := fun hcon =>
        hz (Set.mem_add.mpr ⟨z, hcon, 0, by simp [Metric.mem_closedBall], by ring⟩)
      rw [image_eq_zero_of_notMem_tsupport hzt, image_eq_zero_of_notMem_tsupport hz0, sub_zero,
        norm_zero, zero_pow (by norm_num)]
  have hconv : ∀ᵐ z ∂(volume : Measure ℂ),
      Tendsto (fun t : ℂ => ‖φ (z - t) - φ z‖ ^ 2) (nhds 0) (nhds 0) := by
    filter_upwards with z
    have h1 : Tendsto (fun t : ℂ => z - t) (nhds 0) (nhds z) := by
      simpa using (tendsto_const_nhds.sub tendsto_id :
        Tendsto (fun t : ℂ => z - t) (nhds (0:ℂ)) (nhds (z - 0)))
    have h2 : Tendsto (fun t : ℂ => φ (z - t)) (nhds 0) (nhds (φ z)) :=
      hcont.continuousAt.tendsto.comp h1
    have h3 : Tendsto (fun t : ℂ => ‖φ (z - t) - φ z‖ ^ 2) (nhds 0) (nhds (‖φ z - φ z‖ ^ 2)) :=
      ((by fun_prop : Continuous fun y : ℂ => ‖y - φ z‖ ^ 2)).continuousAt.tendsto.comp h2
    simpa using h3
  have := tendsto_integral_filter_of_dominated_convergence
    ((tsupport φ + Metric.closedBall (0:ℂ) 1).indicator fun _ => (2 * M) ^ 2) hsm hdom hbound_int hconv
  simpa using this

theorem tendsto_integral_normSq_translate_memLp {G : ℂ → ℂ} (hG : MeasureTheory.MemLp G 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : Filter.Tendsto (fun t : ℂ => ∫ z, ‖G (z - t) - G z‖ ^ 2) (nhds 0) (nhds (0 : ℝ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε12 : (0:ℝ) < ε / 12 := by positivity
  have hG' : MemLp G (ENNReal.ofReal 2) volume := by simpa using hG
  obtain ⟨φ, hφsupp, hφapx, hφcont, hφmem⟩ :=
    hG'.exists_hasCompactSupport_integral_rpow_sub_le (p := 2) (by norm_num) hε12
  have hφmem' : MemLp φ 2 volume := by simpa using hφmem
  have hφapx' : ∫ x, ‖G x - φ x‖ ^ 2 ≤ ε / 12 := by simpa using hφapx
  have hB := tendsto_integral_normSq_translate_continuous_hasCompactSupport hφcont hφsupp
  have hevB : ∀ᶠ t in nhds (0:ℂ), (∫ z, ‖φ (z - t) - φ z‖ ^ 2) < ε / 6 := by
    have h6 : (0:ℝ) < ε / 6 := by positivity
    have := (Metric.tendsto_nhds.mp hB) (ε/6) h6
    filter_upwards [this] with t ht
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (fun z => by positivity))] at ht
    exact ht
  filter_upwards [hevB] with t htB
  have hA0 : 0 ≤ ∫ z, ‖G (z - t) - G z‖ ^ 2 := integral_nonneg (fun z => by positivity)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hA0]
  have hInt1 : Integrable (fun z => ‖G (z - t) - φ (z - t)‖ ^ 2) volume := by
    have h : MemLp (fun z : ℂ => G (z - t) - φ (z - t)) 2 volume := by
      have := (hG.sub hφmem').comp_measurePreserving (measurePreserving_sub_right volume t)
      simpa [Function.comp_def, Pi.sub_apply] using this
    simpa using h.integrable_norm_rpow (by norm_num) (by norm_num)
  have hInt2 : Integrable (fun z => ‖φ (z - t) - φ z‖ ^ 2) volume := by
    have hc : Continuous (fun z : ℂ => φ (z - t) - φ z) :=
      (hφcont.comp (continuous_id.sub continuous_const)).sub hφcont
    have hs : HasCompactSupport (fun z : ℂ => φ (z - t) - φ z) := by
      have h := (hφsupp.comp_homeomorph (Homeomorph.subRight t)).sub hφsupp
      have heq : (φ ∘ ⇑(Homeomorph.subRight t)) - φ = (fun z : ℂ => φ (z - t) - φ z) := by
        ext z; simp [Function.comp_def]
      rwa [heq] at h
    have h : MemLp (fun z : ℂ => φ (z - t) - φ z) 2 volume := hc.memLp_of_hasCompactSupport hs
    simpa using h.integrable_norm_rpow (by norm_num) (by norm_num)
  have hInt3 : Integrable (fun z => ‖G z - φ z‖ ^ 2) volume := by
    have := (hG.sub hφmem').integrable_norm_rpow (by norm_num) (by norm_num)
    simpa using this
  have hPt : ∀ z : ℂ, ‖G (z - t) - G z‖ ^ 2 ≤
      3 * (‖G (z - t) - φ (z - t)‖ ^ 2 + ‖φ (z - t) - φ z‖ ^ 2 + ‖G z - φ z‖ ^ 2) := by
    intro z
    set a := G (z - t) - φ (z - t) with ha
    set b := φ (z - t) - φ z with hb
    set c := φ z - G z with hc
    have hsum : G (z - t) - G z = a + b + c := by rw [ha, hb, hc]; ring
    rw [hsum]
    have h1 : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
      calc ‖a + b + c‖ = ‖(a + b) + c‖ := by rw [add_assoc]
        _ ≤ ‖a + b‖ + ‖c‖ := norm_add_le _ _
        _ ≤ (‖a‖ + ‖b‖) + ‖c‖ := by linarith [norm_add_le a b]
        _ = ‖a‖ + ‖b‖ + ‖c‖ := by ring
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 : (‖a‖ + ‖b‖ + ‖c‖) ^ 2 ≤ 3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := by
      nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖b‖ - ‖c‖), sq_nonneg (‖c‖ - ‖a‖)]
    have h4 : ‖c‖ ^ 2 = ‖G z - φ z‖ ^ 2 := by
      rw [hc, show φ z - G z = -(G z - φ z) by ring, norm_neg]
    linarith
  have hIntAll : Integrable (fun z => 3 * (‖G (z - t) - φ (z - t)‖ ^ 2 + ‖φ (z - t) - φ z‖ ^ 2 + ‖G z - φ z‖ ^ 2)) volume :=
    ((hInt1.add hInt2).add hInt3).const_mul 3
  have hle : ∫ z, ‖G (z - t) - G z‖ ^ 2 ≤
      ∫ z, 3 * (‖G (z - t) - φ (z - t)‖ ^ 2 + ‖φ (z - t) - φ z‖ ^ 2 + ‖G z - φ z‖ ^ 2) :=
    integral_mono_of_nonneg (Eventually.of_forall (fun z => by positivity)) hIntAll
      (Eventually.of_forall hPt)
  have hcv : ∫ z, ‖G (z - t) - φ (z - t)‖ ^ 2 = ∫ z, ‖G z - φ z‖ ^ 2 :=
    integral_sub_right_eq_self (fun u => ‖G u - φ u‖ ^ 2) t
  calc ∫ z, ‖G (z - t) - G z‖ ^ 2
      ≤ ∫ z, 3 * (‖G (z - t) - φ (z - t)‖ ^ 2 + ‖φ (z - t) - φ z‖ ^ 2 + ‖G z - φ z‖ ^ 2) := hle
    _ = 3 * ((∫ z, ‖G (z - t) - φ (z - t)‖ ^ 2) + (∫ z, ‖φ (z - t) - φ z‖ ^ 2)
            + (∫ z, ‖G z - φ z‖ ^ 2)) := by
        rw [integral_const_mul]
        have hAB : Integrable (fun z => ‖G (z - t) - φ (z - t)‖ ^ 2 + ‖φ (z - t) - φ z‖ ^ 2) volume :=
          hInt1.add hInt2
        rw [integral_add hAB hInt3, integral_add hInt1 hInt2]
    _ = 3 * ((∫ z, ‖G z - φ z‖ ^ 2) + (∫ z, ‖φ (z - t) - φ z‖ ^ 2)
            + (∫ z, ‖G z - φ z‖ ^ 2)) := by rw [hcv]
    _ < ε := by linarith

end Work.MRMT.Sobolev
