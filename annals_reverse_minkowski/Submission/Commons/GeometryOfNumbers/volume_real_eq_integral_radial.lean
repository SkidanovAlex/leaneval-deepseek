import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Commons.Analysis.MeasureTheory.polar_integral

set_option linter.style.haveILetI false

noncomputable section
open Set Function MeasureTheory Metric
open scoped Classical ENNReal NNReal Pointwise

namespace Commons.GeometryOfNumbers

/-- For a compact convex set `C` with `0` in its interior and a nonzero direction `θ`,
the slice of `C` along the ray `t ↦ t • θ` is the closed segment `[0, sSup S]`, where
`S = {t | 0 ≤ t ∧ t • θ ∈ C}` is the set of nonnegative parameters landing in `C`. -/
theorem ray_slice_eq_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : Set E} (hCcvx : Convex ℝ C) (hCcpt : IsCompact C)
    (h0 : (0 : E) ∈ interior C) {θ : E} (hθ : θ ≠ 0) :
    {t : ℝ | 0 ≤ t ∧ t • θ ∈ C} =
      Set.Icc 0 (sSup {t : ℝ | 0 ≤ t ∧ t • θ ∈ C}) := by
  set S : Set ℝ := {t : ℝ | 0 ≤ t ∧ t • θ ∈ C} with hSdef
  have hCclosed : IsClosed C := hCcpt.isClosed
  have h0C : (0 : E) ∈ C := interior_subset h0
  have hSne : S.Nonempty := ⟨0, le_refl 0, by simpa using h0C⟩
  have hθpos : 0 < ‖θ‖ := norm_pos_iff.mpr hθ
  have hSbdd : BddAbove S := by
    obtain ⟨M, hM⟩ := (isBounded_iff_subset_closedBall (0 : E)).1 hCcpt.isBounded
    refine ⟨M / ‖θ‖, fun t ht => ?_⟩
    have htC : t • θ ∈ C := ht.2
    have hnorm : ‖t • θ‖ ≤ M := by
      have := hM htC
      rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at this
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at hnorm
    exact (le_div_iff₀ hθpos).2 hnorm
  have hSclosed : IsClosed S := by
    rw [hSdef]
    exact isClosed_Ici.inter (hCclosed.preimage (continuous_id.smul continuous_const))
  have hρS : sSup S ∈ S := by
    have hmem : sSup S ∈ closure S := csSup_mem_closure hSne hSbdd
    rwa [hSclosed.closure_eq] at hmem
  ext r
  constructor
  · intro hr
    exact ⟨hr.1, le_csSup hSbdd hr⟩
  · intro hr
    obtain ⟨hr0, hrρ⟩ := hr
    refine ⟨hr0, ?_⟩
    rcases lt_or_eq_of_le hrρ with hlt | heq
    · obtain ⟨b, hbS, hrb⟩ := (lt_csSup_iff hSbdd hSne).1 hlt
      have hbθC : b • θ ∈ C := hbS.2
      have hbpos : 0 < b := lt_of_le_of_lt hr0 hrb
      have hcoe : r / b ∈ Set.Icc (0:ℝ) 1 := by
        refine ⟨div_nonneg hr0 hbpos.le, ?_⟩
        rw [div_le_one hbpos]
        exact le_of_lt hrb
      have hkey : (r / b) • (b • θ) = r • θ := by
        rw [smul_smul, div_mul_cancel₀ _ hbpos.ne']
      rw [← hkey]
      exact hCcvx.smul_mem_of_zero_mem h0C hbθC hcoe
    · rw [heq]
      exact hρS.2

/-- The integral, with respect to the measure `volumeIoiPow m` on `(0, +∞)` (density `r ↦ r ^ m`),
of the indicator of `(0, ρ]` equals `ρ ^ (m + 1) / (m + 1)`. -/
theorem integral_volumeIoiPow_indicator_Iic
    (m : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∫ r : Set.Ioi (0 : ℝ), ((Set.Iic ρ).indicator (fun _ : ℝ => (1 : ℝ))) (r : ℝ)
        ∂(MeasureTheory.Measure.volumeIoiPow m)
      = ρ ^ (m + 1) / (m + 1) := by
  simp only [MeasureTheory.Measure.volumeIoiPow]
  rw [integral_withDensity_eq_integral_toReal_smul
    (f := fun r : Set.Ioi (0:ℝ) => ENNReal.ofReal ((r:ℝ) ^ m))]
  · have hcongr : (fun r : Set.Ioi (0:ℝ) =>
        (ENNReal.ofReal ((r:ℝ) ^ m)).toReal • ((Set.Iic ρ).indicator (fun _ : ℝ => (1:ℝ))) (r:ℝ))
      = (fun r : Set.Ioi (0:ℝ) =>
        (r:ℝ) ^ m * ((Set.Iic ρ).indicator (fun _ : ℝ => (1:ℝ))) (r:ℝ)) := by
      funext r
      rw [ENNReal.toReal_ofReal (pow_nonneg (le_of_lt r.2) m), smul_eq_mul]
    rw [hcongr, integral_subtype_comap (μ := MeasureTheory.volume) (s := Set.Ioi (0:ℝ))
          measurableSet_Ioi
          (f := fun s : ℝ => s ^ m * ((Set.Iic ρ).indicator (fun _ : ℝ => (1:ℝ))) s)]
    have hpt : ∀ x : ℝ, x ^ m * ((Set.Iic ρ).indicator (fun _ : ℝ => (1:ℝ))) x
        = ((Set.Iic ρ).indicator (fun x : ℝ => x ^ m)) x := by
      intro x
      by_cases hx : x ∈ Set.Iic ρ
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
    simp_rw [hpt]
    rw [MeasureTheory.setIntegral_indicator measurableSet_Iic, Set.Ioi_inter_Iic,
      ← intervalIntegral.integral_of_le hρ, integral_pow]
    simp
  · fun_prop
  · filter_upwards with r
    exact ENNReal.ofReal_lt_top

/-- **Polar-coordinate formula for the volume of a convex body.** For a compact convex set `C` in
`ℝⁿ` (`n ≥ 1`) containing the origin in its interior, the Lebesgue volume of `C` equals
`1/n` times the integral over the unit sphere of the `n`-th power of the radial function
`θ ↦ sSup {r ≥ 0 | r • θ ∈ C}`. -/
theorem volume_real_eq_integral_radial {n : ℕ} (hn : 0 < n)
    (C : Set (EuclideanSpace ℝ (Fin n)))
    (hCcvx : Convex ℝ C) (hCcpt : IsCompact C)
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior C) :
    MeasureTheory.volume.real C =
      (1 / (n : ℝ)) * ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        (sSup {r : ℝ | 0 ≤ r ∧ r • (θ : EuclideanSpace ℝ (Fin n)) ∈ C}) ^ n
        ∂(MeasureTheory.volume.toSphere) := by
  haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
    haveI : NeZero n := ⟨Nat.pos_iff_ne_zero.mp hn⟩
    infer_instance
  let V := EuclideanSpace ℝ (Fin n)
  have hCmeas : MeasurableSet C := hCcpt.isClosed.measurableSet
  have hCvol : MeasureTheory.volume C < ∞ := hCcpt.measure_lt_top
  have hint : Integrable (C.indicator (1 : V → ℝ)) MeasureTheory.volume := by
    rw [integrable_indicator_iff hCmeas]
    exact integrableOn_const
  have hfin : Module.finrank ℝ V = n := by
    rw [finrank_euclideanSpace, Fintype.card_fin]
  have hinner : ∀ θ : Metric.sphere (0 : V) 1,
      ∫ r : Set.Ioi (0 : ℝ), (C.indicator (1 : V → ℝ)) (r.1 • (θ : V))
          ∂MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ V - 1)
        = (sSup {r : ℝ | 0 ≤ r ∧ r • (θ : V) ∈ C}) ^ n / n := by
    intro θ
    have hθne : (θ : V) ≠ 0 := ne_of_mem_sphere θ.2 one_ne_zero
    have hslice : {t : ℝ | 0 ≤ t ∧ t • (θ : V) ∈ C} =
        Set.Icc 0 (sSup {t : ℝ | 0 ≤ t ∧ t • (θ : V) ∈ C}) :=
      ray_slice_eq_Icc hCcvx hCcpt h0 hθne
    have hρnn : 0 ≤ sSup {r : ℝ | 0 ≤ r ∧ r • (θ : V) ∈ C} := by
      have h0Icc : (0 : ℝ) ∈ Set.Icc 0 (sSup {r : ℝ | 0 ≤ r ∧ r • (θ : V) ∈ C}) := by
        rw [← hslice]
        exact ⟨le_refl 0, by simpa using interior_subset h0⟩
      exact h0Icc.2
    have hx_iff : ∀ x : ℝ, 0 ≤ x →
        (x • (θ : V) ∈ C ↔ x ≤ sSup {r : ℝ | 0 ≤ r ∧ r • (θ : V) ∈ C}) := by
      intro x hx0
      have hmem := (Set.ext_iff.mp hslice) x
      simp only [Set.mem_Icc] at hmem
      exact ⟨fun hxc => (hmem.mp ⟨hx0, hxc⟩).2, fun hle => (hmem.mpr ⟨hx0, hle⟩).2⟩
    have hfun : (fun r : Set.Ioi (0 : ℝ) => (C.indicator (1 : V → ℝ)) (r.1 • (θ : V)))
        = (fun r : Set.Ioi (0 : ℝ) =>
            ((Set.Iic (sSup {r : ℝ | 0 ≤ r ∧ r • (θ : V) ∈ C})).indicator
              (fun _ : ℝ => (1 : ℝ))) r.1) := by
      funext r
      have hr0 : 0 ≤ (r : ℝ) := le_of_lt r.2
      have hx := hx_iff (r : ℝ) hr0
      by_cases h : (r : ℝ) ≤ sSup {r : ℝ | 0 ≤ r ∧ r • (θ : V) ∈ C}
      · simp [Set.indicator_of_mem (hx.mpr h), Set.indicator_of_mem (Set.mem_Iic.mpr h)]
      · simp [Set.indicator_of_notMem (fun hc => h (hx.mp hc)),
              Set.indicator_of_notMem (fun hmem => h (Set.mem_Iic.mp hmem))]
    rw [hfun, hfin, integral_volumeIoiPow_indicator_Iic (n - 1) _ hρnn,
      Nat.sub_add_cancel hn]
    have hden : (↑(n - 1) + 1 : ℝ) = (n : ℝ) := by
      rw [Nat.cast_sub (Nat.succ_le_of_lt hn)]
      ring
    rw [hden]
  have hpolar := Commons.Analysis.MeasureTheory.polar_integral V (C.indicator (1 : V → ℝ)) hint
  calc
    MeasureTheory.volume.real C
        = ∫ x : V, (C.indicator (1 : V → ℝ)) x ∂MeasureTheory.volume :=
          (integral_indicator_one hCmeas).symm
    _ = ∫ θ : Metric.sphere (0 : V) 1,
          ∫ r : Set.Ioi (0 : ℝ), (C.indicator (1 : V → ℝ)) (r.1 • (θ : V))
            ∂MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ V - 1)
          ∂MeasureTheory.volume.toSphere := hpolar
    _ = ∫ θ : Metric.sphere (0 : V) 1,
          (sSup {r : ℝ | 0 ≤ r ∧ r • (θ : V) ∈ C}) ^ n / n
          ∂MeasureTheory.volume.toSphere := by
        apply integral_congr_ae
        filter_upwards with θ
        exact hinner θ
    _ = (1 / (n : ℝ)) * ∫ θ : Metric.sphere (0 : V) 1,
          (sSup {r : ℝ | 0 ≤ r ∧ r • (θ : V) ∈ C}) ^ n
          ∂MeasureTheory.volume.toSphere := by
        rw [MeasureTheory.integral_div]
        ring

end Commons.GeometryOfNumbers