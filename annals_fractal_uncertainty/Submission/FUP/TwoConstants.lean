import ChallengeDeps

open MeasureTheory Metric Set Complex Filter
open scoped ENNReal BigOperators Topology

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# The interval form of the Cartan/Riesz estimate

See `Submission/FUP/ROADMAP.md`, Session 56 (S3) and (B1).

`Commons.Analysis.Complex.riesz_cartan_disk` gives, for a holomorphic `G` bounded by `M` on the
closed unit disk and with `log ‖G‖ ≥ m` at a point of the disk of radius `1 - 3δ`, the lower bound
`log ‖G z‖ ≥ m - (log M - m) K`, `K = 2δ⁻³ log(2/δ) + δ⁻² log(2e/H)`, outside disks of total
radius `≤ 5H`, for `‖z‖ ≤ 1 - 2δ`.

Here we draw the consequences needed for the single-scale localisation (Han–Schlag `prop:B1B2`):

* `volume_bad_trace_le` — the trace on `ℝ` of a finite union of disks of total radius `≤ 5H` has
  one-dimensional measure `≤ 10H`;
* `two_constants_interval` — the **two-constants estimate on a real interval**: for
  `J ⊆ [a,b] ⊆ (-(1-2δ), 1-2δ)` measurable with `|J| > 20H`,
  `‖G‖_{L²([a,b])} ≤ 2^κ M^{1-κ} |[a,b]|^{1/2} |J|^{-κ/2} ‖G‖^κ_{L²(J)}`,
  with `κ := (1 + 2δ⁻³ log(2/δ) + δ⁻² log(2e/H))⁻¹`.

The constants depend only on `δ, H` — **not** on `G`, `M`, `m`.
-/

namespace Submission.FUP

/-- The trace on `ℝ` of the open disk `D(w, r)` is contained in `(w.re - r, w.re + r)`. -/
lemma disk_trace_subset (w : ℂ) (r : ℝ) :
    {x : ℝ | ‖(x : ℂ) - w‖ < r} ⊆ Set.Ioo (w.re - r) (w.re + r) := by
  intro x hx
  have h1 : |((x : ℂ) - w).re| ≤ ‖(x : ℂ) - w‖ := Complex.abs_re_le_norm _
  have h2 : ((x : ℂ) - w).re = x - w.re := by simp
  rw [h2] at h1
  have h3 : |x - w.re| < r := lt_of_le_of_lt h1 hx
  have h4 := abs_lt.mp h3
  simp only [Set.mem_Ioo]
  exact ⟨by linarith [h4.1], by linarith [h4.2]⟩

/-- The one-dimensional measure of the trace on `ℝ` of a finite union of disks of total radius
at most `∑ r z` is at most `2 ∑ r z`. -/
lemma volume_bad_trace_le (s : Finset ℂ) (r : ℂ → ℝ) (hpos : ∀ z ∈ s, 0 < r z) :
    volume {x : ℝ | ∃ w ∈ s, ‖(x : ℂ) - w‖ < r w} ≤ ENNReal.ofReal (2 * ∑ z ∈ s, r z) := by
  classical
  have hset : {x : ℝ | ∃ w ∈ s, ‖(x : ℂ) - w‖ < r w}
      = ⋃ w ∈ s, {x : ℝ | ‖(x : ℂ) - w‖ < r w} := by
    ext x
    simp only [Set.mem_ofPred_eq, mem_iUnion]
    exact ⟨fun ⟨w, hws, hw⟩ => ⟨w, hws, hw⟩, fun ⟨w, hws, hw⟩ => ⟨w, hws, hw⟩⟩
  rw [hset]
  calc volume (⋃ w ∈ s, {x : ℝ | ‖(x : ℂ) - w‖ < r w})
      ≤ ∑ w ∈ s, volume {x : ℝ | ‖(x : ℂ) - w‖ < r w} := measure_biUnion_finset_le _ _
    _ ≤ ∑ w ∈ s, ENNReal.ofReal (2 * r w) := by
        apply Finset.sum_le_sum
        intro w hw
        calc volume {x : ℝ | ‖(x : ℂ) - w‖ < r w}
            ≤ volume (Set.Ioo (w.re - r w) (w.re + r w)) :=
              measure_mono (disk_trace_subset w (r w))
          _ = ENNReal.ofReal (2 * r w) := by
              rw [Real.volume_Ioo]
              congr 1
              ring
    _ = ENNReal.ofReal (∑ w ∈ s, 2 * r w) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro w hw
        exact mul_nonneg (by norm_num) (le_of_lt (hpos w hw))
    _ = ENNReal.ofReal (2 * ∑ z ∈ s, r z) := by
        congr 1
        rw [Finset.mul_sum]

/-- The exponent `K` of the Cartan/Riesz estimate (Han–Schlag `cor:vRiesz`). -/
noncomputable def twoConstK (δ H : ℝ) : ℝ :=
  2 * δ⁻¹ ^ 3 * Real.log (2 / δ) + δ⁻¹ ^ 2 * Real.log (2 * Real.exp 1 / H)

/-- The interpolation exponent `κ = (1+K)⁻¹` of the two-constants estimate. -/
noncomputable def twoConstKappa (δ H : ℝ) : ℝ := (1 + twoConstK δ H)⁻¹

lemma twoConstK_nonneg {δ H : ℝ} (hδ0 : 0 < δ) (hδ3 : δ < 1 / 3) (hH0 : 0 < H) (hH1 : H ≤ 1) :
    0 ≤ twoConstK δ H := by
  rw [twoConstK]
  have h1 : 0 < Real.log (2 / δ) := Real.log_pos (by rw [one_lt_div hδ0]; linarith)
  have h2 : 0 ≤ Real.log (2 * Real.exp 1 / H) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hH0]
    nlinarith [Real.one_le_exp (by norm_num : (0:ℝ) ≤ 1)]
  have h3 : 0 < δ⁻¹ := by positivity
  nlinarith [pow_pos h3 3, pow_pos h3 2]

/-- `κ = (1+K)⁻¹` lies in `(0,1]`. -/
lemma twoConstKappa_mem {δ H : ℝ} (hδ0 : 0 < δ) (hδ3 : δ < 1 / 3) (hH0 : 0 < H) (hH1 : H ≤ 1) :
    0 < twoConstKappa δ H ∧ twoConstKappa δ H ≤ 1 := by
  have hK := twoConstK_nonneg hδ0 hδ3 hH0 hH1
  constructor
  · rw [twoConstKappa]; positivity
  · rw [twoConstKappa, inv_le_one₀ (by linarith : (0:ℝ) < 1 + twoConstK δ H)]
    linarith

/-- **The elementary integral bound.**  If `f ≥ 0` on `J`, `f ≥ c` a.e. on `J \ bad`, and
`bad` has measure at most `β ≤ |J|`, then `∫_J f ≥ c (|J| - β)`.

This is the `d`-dimensional (`Fin d → ℝ`) version of
`Commons.Analysis.Complex.two_constants_integral_ge_of_const_off_small_set`. -/
lemma integral_ge_of_const_off_small_set_pi {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    {J bad : Set (Fin d → ℝ)} {c β : ℝ}
    (hJmeas : MeasurableSet J) (hbadmeas : MeasurableSet bad)
    (hJfin : volume J < ⊤) (hβ : 0 ≤ β) (hc : 0 ≤ c)
    (hbadvol : volume bad ≤ ENNReal.ofReal β)
    (hβv : ENNReal.ofReal β ≤ volume J)
    (hintJ : IntegrableOn f J volume)
    (hfnn : ∀ᵐ x ∂(volume.restrict J), (0:ℝ) ≤ f x)
    (hae : ∀ᵐ x ∂(volume.restrict (J \ bad)), c ≤ f x) :
    c * ((volume J).toReal - β) ≤ ∫ x in J, f x := by
  have hJbadmeas : MeasurableSet (J \ bad) := hJmeas.diff hbadmeas
  have hfinJbad : volume (J \ bad) < ⊤ := lt_of_le_of_lt (measure_mono Set.sdiff_subset) hJfin
  have hconstInt : IntegrableOn (fun _ : Fin d → ℝ => c) (J \ bad) volume :=
    integrableOn_const (ne_of_lt hfinJbad)
  have hIntJbad : IntegrableOn f (J \ bad) volume := hintJ.mono_set Set.sdiff_subset
  have hstep1 : ∫ x in (J \ bad), (fun _ : Fin d → ℝ => c) x ≤ ∫ x in (J \ bad), f x :=
    setIntegral_mono_ae_restrict hconstInt hIntJbad hae
  have hconst : ∫ x in (J \ bad), (fun _ : Fin d → ℝ => c) x = (volume (J \ bad)).toReal * c := by
    rw [setIntegral_const, Measure.real_def, smul_eq_mul]
  have hstep1' : (volume (J \ bad)).toReal * c ≤ ∫ x in (J \ bad), f x := hconst ▸ hstep1
  have hstep2 : ∫ x in (J \ bad), f x ≤ ∫ x in J, f x :=
    setIntegral_mono_set hintJ hfnn (Filter.Eventually.of_forall (fun x hx => hx.1))
  have hvolJbad : volume (J \ bad) = volume J - volume (J ∩ bad) := by
    have h := measure_sdiff_add_inter (μ := volume) J hbadmeas
    exact ENNReal.eq_sub_of_add_eq
      (ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_left) hJfin)) h
  have hge : volume J - ENNReal.ofReal β ≤ volume (J \ bad) := by
    rw [hvolJbad]
    exact tsub_le_tsub_left (le_trans (measure_mono Set.inter_subset_right) hbadvol) _
  have htoReal : (volume J).toReal - β ≤ (volume (J \ bad)).toReal := by
    have h1 : (volume J - ENNReal.ofReal β).toReal ≤ (volume (J \ bad)).toReal :=
      ENNReal.toReal_mono (ne_of_lt hfinJbad) hge
    rwa [ENNReal.toReal_sub_of_le hβv (ne_of_lt hJfin), ENNReal.toReal_ofReal hβ] at h1
  calc c * ((volume J).toReal - β) ≤ c * (volume (J \ bad)).toReal :=
        mul_le_mul_of_nonneg_left htoReal hc
    _ = (volume (J \ bad)).toReal * c := by ring
    _ ≤ ∫ x in (J \ bad), f x := hstep1'
    _ ≤ ∫ x in J, f x := hstep2

end Submission.FUP

