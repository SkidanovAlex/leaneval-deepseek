import Mathlib.Algebra.Order.Star.Real
import Submission.Commons.Analysis.MeasureTheory.polar_integral
import Submission.Commons.GeometryOfNumbers.volume_real_eq_integral_radial

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

noncomputable section
open Set Function MeasureTheory Metric
open scoped Classical ENNReal NNReal Pointwise

namespace Commons.GeometryOfNumbers

variable {n : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin n)

/-! ### Auxiliary facts about the support function of a compact set -/

lemma exists_norm_bound_of_isCompact {C : Set V} (hC : IsCompact C) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ y ∈ C, ‖y‖ ≤ R := by
  obtain ⟨M, hM⟩ := (isBounded_iff_subset_closedBall (0 : V)).1 hC.isBounded
  refine ⟨max M 0, le_max_right _ _, fun y hy => ?_⟩
  have h := hM hy
  rw [Metric.mem_closedBall, dist_zero_right] at h
  exact le_trans h (le_max_left _ _)

lemma bddAbove_inner_image {C : Set V} (hC : IsCompact C) (u : V) :
    BddAbove ((fun y => inner ℝ y u) '' C) := by
  obtain ⟨R, _hR0, hR⟩ := exists_norm_bound_of_isCompact hC
  refine ⟨R * ‖u‖, ?_⟩
  rintro b ⟨y, hy, rfl⟩
  exact le_trans (real_inner_le_norm y u) (mul_le_mul_of_nonneg_right (hR y hy) (norm_nonneg u))

lemma abs_sSup_inner_sub_le {C : Set V} (hne : C.Nonempty) {R : ℝ}
    (hR : ∀ y ∈ C, ‖y‖ ≤ R) (u v : V) :
    |sSup ((fun y => inner ℝ y u) '' C) - sSup ((fun y => inner ℝ y v) '' C)|
      ≤ R * ‖u - v‖ := by
  have hbdd : ∀ w : V, BddAbove ((fun y => inner ℝ y w) '' C) := fun w =>
    ⟨R * ‖w‖, by
      rintro b ⟨y, hy, rfl⟩
      exact le_trans (real_inner_le_norm y w) (mul_le_mul_of_nonneg_right (hR y hy) (norm_nonneg w))⟩
  rw [abs_sub_le_iff]
  constructor
  · rw [sub_le_iff_le_add]
    refine csSup_le (hne.image _) ?_
    rintro b ⟨y, hy, rfl⟩
    change inner ℝ y u ≤ R * ‖u - v‖ + sSup ((fun y => inner ℝ y v) '' C)
    have h1 : inner ℝ y u = inner ℝ y v + inner ℝ y (u - v) := by
      rw [inner_sub_right]; ring
    have h2 : inner ℝ y (u - v) ≤ ‖y‖ * ‖u - v‖ := real_inner_le_norm y (u - v)
    have h3 : ‖y‖ * ‖u - v‖ ≤ R * ‖u - v‖ :=
      mul_le_mul_of_nonneg_right (hR y hy) (norm_nonneg _)
    have h4 : inner ℝ y v ≤ sSup ((fun y => inner ℝ y v) '' C) :=
      le_csSup (hbdd v) ⟨y, hy, rfl⟩
    rw [h1]; linarith
  · rw [sub_le_iff_le_add]
    refine csSup_le (hne.image _) ?_
    rintro b ⟨y, hy, rfl⟩
    change inner ℝ y v ≤ R * ‖u - v‖ + sSup ((fun y => inner ℝ y u) '' C)
    have h1 : inner ℝ y v = inner ℝ y u + inner ℝ y (v - u) := by
      rw [inner_sub_right]; ring
    have h2 : inner ℝ y (v - u) ≤ ‖y‖ * ‖v - u‖ := real_inner_le_norm y (v - u)
    have h3 : ‖y‖ * ‖v - u‖ ≤ R * ‖u - v‖ := by
      rw [norm_sub_rev v u]
      exact mul_le_mul_of_nonneg_right (hR y hy) (norm_nonneg _)
    have h4 : inner ℝ y u ≤ sSup ((fun y => inner ℝ y u) '' C) :=
      le_csSup (hbdd u) ⟨y, hy, rfl⟩
    rw [h1]; linarith

lemma continuous_sSup_inner_image {C : Set V} (hC : IsCompact C) (hne : C.Nonempty) :
    Continuous (fun u : V => sSup ((fun y => inner ℝ y u) '' C)) := by
  obtain ⟨R, hR0, hR⟩ := exists_norm_bound_of_isCompact hC
  refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal R) ?_).continuous
  intro u v
  rw [Real.dist_eq, dist_eq_norm]
  calc |sSup ((fun y => inner ℝ y u) '' C) - sSup ((fun y => inner ℝ y v) '' C)|
      ≤ R * ‖u - v‖ := abs_sSup_inner_sub_le hne hR u v
    _ = (Real.toNNReal R : ℝ) * ‖u - v‖ := by rw [Real.coe_toNNReal R hR0]

lemma norm_coe_sphere_one (θ : Metric.sphere (0 : V) 1) : ‖(θ : V)‖ = 1 := by
  have h := θ.2
  rwa [Metric.mem_sphere, dist_eq_norm, sub_zero] at h

/-! ### A finiteness fact for the radial measure `volumeIoiPow` -/

lemma volumeIoiPow_setOf_le_lt_top (m : ℕ) (ρ : ℝ) :
    MeasureTheory.Measure.volumeIoiPow m ({r : Ioi (0 : ℝ) | (r : ℝ) ≤ ρ}) < ⊤ := by
  have hpos : (0 : ℝ) < max ρ 0 + 1 := by
    have : (0 : ℝ) ≤ max ρ 0 := le_max_right _ _
    linarith
  have hsub : {r : Ioi (0 : ℝ) | (r : ℝ) ≤ ρ} ⊆ Set.Iio (⟨max ρ 0 + 1, hpos⟩ : Ioi (0 : ℝ)) := by
    intro r hr
    change (r : ℝ) ≤ ρ at hr
    simp only [Set.mem_Iio]
    have h1 : ρ ≤ max ρ 0 := le_max_left _ _
    have h2 : (0 : ℝ) < (r : ℝ) := r.2
    show (r : ℝ) < max ρ 0 + 1
    linarith
  calc MeasureTheory.Measure.volumeIoiPow m ({r : Ioi (0 : ℝ) | (r : ℝ) ≤ ρ})
      ≤ MeasureTheory.Measure.volumeIoiPow m (Set.Iio (⟨max ρ 0 + 1, hpos⟩ : Ioi (0 : ℝ))) :=
        measure_mono hsub
    _ = ENNReal.ofReal ((max ρ 0 + 1) ^ (m + 1) / (m + 1)) :=
        Measure.volumeIoiPow_apply_Iio m ⟨max ρ 0 + 1, hpos⟩
    _ < ⊤ := ENNReal.ofReal_lt_top

/-! ### Monotonicity for integrals of indicator functions -/

lemma integral_indicator_one_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {s t : Set α} (hst : s ⊆ t) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (htfin : μ t < ⊤) :
    ∫ x, s.indicator (fun _ => (1 : ℝ)) x ∂μ ≤ ∫ x, t.indicator (fun _ => (1 : ℝ)) x ∂μ := by
  have h1 : ∫ x, s.indicator (fun _ => (1 : ℝ)) x ∂μ = μ.real s := by
    rw [show s.indicator (fun _ => (1 : ℝ)) = s.indicator (1 : α → ℝ) from rfl]
    exact integral_indicator_one (μ := μ) hs
  have h2 : ∫ x, t.indicator (fun _ => (1 : ℝ)) x ∂μ = μ.real t := by
    rw [show t.indicator (fun _ => (1 : ℝ)) = t.indicator (1 : α → ℝ) from rfl]
    exact integral_indicator_one (μ := μ) ht
  rw [h1, h2]
  exact MeasureTheory.measureReal_mono hst htfin.ne

/-! ### The pointwise (in the direction) bound -/

lemma inner_integral_le_sSup {n : ℕ} (hn : 0 < n) {C : Set (EuclideanSpace ℝ (Fin n))}
    (hCcpt : IsCompact C) (h0C : (0 : EuclideanSpace ℝ (Fin n)) ∈ C)
    (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    (∫ r : Ioi (0 : ℝ), (C.indicator (fun _ => (1 : ℝ))) (r.1 • (θ : EuclideanSpace ℝ (Fin n)))
        ∂MeasureTheory.Measure.volumeIoiPow (n - 1))
      ≤ (sSup ((fun y => inner ℝ y (θ : EuclideanSpace ℝ (Fin n))) '' C)) ^ n / (n : ℝ) := by
  have hθnorm : ‖(θ : EuclideanSpace ℝ (Fin n))‖ = 1 := norm_coe_sphere_one θ
  have hbdd : BddAbove ((fun y => inner ℝ y (θ : EuclideanSpace ℝ (Fin n))) '' C) :=
    bddAbove_inner_image hCcpt _
  set h : ℝ := sSup ((fun y => inner ℝ y (θ : EuclideanSpace ℝ (Fin n))) '' C) with hhdef
  have hh0 : 0 ≤ h := by
    rw [hhdef]
    exact le_csSup hbdd ⟨0, h0C, by simp⟩
  let s : Set (Ioi (0 : ℝ)) := (fun r : Ioi (0 : ℝ) => (r : ℝ) • (θ : EuclideanSpace ℝ (Fin n))) ⁻¹' C
  let t : Set (Ioi (0 : ℝ)) := {r | (r : ℝ) ∈ Set.Iic h}
  have hs : MeasurableSet s := by
    have hc : Continuous (fun r : Ioi (0 : ℝ) => (r : ℝ) • (θ : EuclideanSpace ℝ (Fin n))) :=
      continuous_subtype_val.smul continuous_const
    exact hCcpt.isClosed.measurableSet.preimage hc.measurable
  have ht : MeasurableSet t := isClosed_Iic.measurableSet.preimage measurable_subtype_coe
  have htfin : MeasureTheory.Measure.volumeIoiPow (n - 1) t < ⊤ := by
    show MeasureTheory.Measure.volumeIoiPow (n - 1) ({r : Ioi (0 : ℝ) | (r : ℝ) ≤ h}) < ⊤
    exact volumeIoiPow_setOf_le_lt_top (n - 1) h
  have hst : s ⊆ t := by
    intro r hr
    have hinner : inner ℝ ((r : ℝ) • (θ : EuclideanSpace ℝ (Fin n)))
        (θ : EuclideanSpace ℝ (Fin n)) = (r : ℝ) := by
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq, hθnorm]; ring
    have hle : inner ℝ ((r : ℝ) • (θ : EuclideanSpace ℝ (Fin n)))
        (θ : EuclideanSpace ℝ (Fin n)) ≤ h := by
      rw [hhdef]
      exact le_csSup hbdd ⟨(r : ℝ) • (θ : EuclideanSpace ℝ (Fin n)), hr, rfl⟩
    show (r : ℝ) ≤ h
    rw [← hinner]; exact hle
  have hfun_C : (fun r : Ioi (0 : ℝ) =>
        (C.indicator (fun _ => (1 : ℝ))) (r.1 • (θ : EuclideanSpace ℝ (Fin n))))
      = s.indicator (fun _ => (1 : ℝ)) := by
    funext r
    by_cases hr : (r : ℝ) • (θ : EuclideanSpace ℝ (Fin n)) ∈ C
    · rw [Set.indicator_of_mem hr, Set.indicator_of_mem (show r ∈ s from hr)]
    · rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem (show r ∉ s from hr)]
  have hfun_t : (fun r : Ioi (0 : ℝ) => (Set.Iic h).indicator (fun _ => (1 : ℝ)) (r : ℝ))
      = t.indicator (fun _ => (1 : ℝ)) := by
    funext r
    by_cases hr : (r : ℝ) ∈ Set.Iic h
    · rw [Set.indicator_of_mem hr, Set.indicator_of_mem (show r ∈ t from hr)]
    · rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem (show r ∉ t from hr)]
  calc (∫ r : Ioi (0 : ℝ), (C.indicator (fun _ => (1 : ℝ)))
          (r.1 • (θ : EuclideanSpace ℝ (Fin n)))
          ∂MeasureTheory.Measure.volumeIoiPow (n - 1))
      = ∫ r : Ioi (0 : ℝ), s.indicator (fun _ => (1 : ℝ)) r
          ∂MeasureTheory.Measure.volumeIoiPow (n - 1) := by rw [hfun_C]
    _ ≤ ∫ r : Ioi (0 : ℝ), t.indicator (fun _ => (1 : ℝ)) r
          ∂MeasureTheory.Measure.volumeIoiPow (n - 1) :=
        integral_indicator_one_le _ hst hs ht htfin
    _ = ∫ r : Ioi (0 : ℝ), (Set.Iic h).indicator (fun _ => (1 : ℝ)) (r : ℝ)
          ∂MeasureTheory.Measure.volumeIoiPow (n - 1) := by rw [hfun_t]
    _ = h ^ n / (n : ℝ) := by
        rw [integral_volumeIoiPow_indicator_Iic (n - 1) h hh0, Nat.sub_add_cancel hn]
        have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
          rw [Nat.cast_sub (Nat.succ_le_of_lt hn)]; ring
        rw [hcast]
    _ = (sSup ((fun y => inner ℝ y (θ : EuclideanSpace ℝ (Fin n))) '' C)) ^ n / (n : ℝ) := by
        rw [hhdef]

/-! ### The main inequality -/

/-- **Reverse-Minkowski-type volume bound.** For a compact set `C ⊆ ℝⁿ` (`n ≥ 1`) containing the
origin, the Lebesgue volume of `C` is at most `1/n` times the integral over the unit sphere of the
`n`-th power of the support function `θ ↦ sSup {⟪y, θ⟫ | y ∈ C}`.

This is the "Urysohn-type" volume comparison used in the proof of the reverse Minkowski theorem:
every point of `C` lies on the ray `r • θ` with `r = ⟪r • θ, θ⟫ ≤ sSup{⟪y, θ⟫ | y ∈ C}`, hence `C`
is contained in the star body whose radial function is the support function, and the volume of that
star body is exactly the right-hand side (polar coordinates). -/
theorem volume_real_le_integral_support {n : ℕ} (hn : 0 < n)
    {C : Set (EuclideanSpace ℝ (Fin n))} (hCcpt : IsCompact C)
    (h0C : (0 : EuclideanSpace ℝ (Fin n)) ∈ C) :
    MeasureTheory.volume.real C ≤ (1 / (n : ℝ)) * ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        (sSup ((fun y => inner ℝ y (θ : EuclideanSpace ℝ (Fin n))) '' C)) ^ n
        ∂(MeasureTheory.volume.toSphere) := by
  haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
    haveI : NeZero n := ⟨Nat.pos_iff_ne_zero.mp hn⟩
    infer_instance
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by
    rw [finrank_euclideanSpace, Fintype.card_fin]
  have hCmeas : MeasurableSet C := hCcpt.isClosed.measurableSet
  have hCfin : MeasureTheory.volume C < ⊤ := hCcpt.measure_lt_top
  have hint : Integrable (C.indicator (fun _ => (1 : ℝ))) MeasureTheory.volume := by
    rw [integrable_indicator_iff hCmeas]
    exact integrableOn_const
  have hpolar := Commons.Analysis.MeasureTheory.polar_integral (EuclideanSpace ℝ (Fin n))
    (C.indicator (fun _ => (1 : ℝ))) hint
  rw [hfin] at hpolar
  set H : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ :=
    fun θ => sSup ((fun y => inner ℝ y (θ : EuclideanSpace ℝ (Fin n))) '' C) with Hdef
  have hCne : C.Nonempty := ⟨0, h0C⟩
  have H_nonneg : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, 0 ≤ H θ := by
    intro θ
    rw [Hdef]
    exact le_csSup (bddAbove_inner_image hCcpt (θ : EuclideanSpace ℝ (Fin n))) ⟨0, h0C, by simp⟩
  have hinner : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      (∫ r : Ioi (0 : ℝ), (C.indicator (fun _ => (1 : ℝ))) (r.1 • (θ : EuclideanSpace ℝ (Fin n)))
        ∂MeasureTheory.Measure.volumeIoiPow (n - 1)) ≤ H θ ^ n / (n : ℝ) := by
    intro θ
    simpa only [Hdef] using inner_integral_le_sSup hn hCcpt h0C θ
  have hcontH : Continuous H := by
    rw [Hdef]
    exact (continuous_sSup_inner_image hCcpt hCne).comp continuous_subtype_val
  obtain ⟨R, hR0, hR⟩ := exists_norm_bound_of_isCompact hCcpt
  have H_le : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, H θ ≤ R := by
    intro θ
    rw [Hdef]
    refine csSup_le (hCne.image _) ?_
    rintro b ⟨y, hy, rfl⟩
    change inner ℝ y (θ : EuclideanSpace ℝ (Fin n)) ≤ R
    calc inner ℝ y (θ : EuclideanSpace ℝ (Fin n)) ≤ ‖y‖ * ‖(θ : EuclideanSpace ℝ (Fin n))‖ := real_inner_le_norm _ _
      _ ≤ R * 1 := by
          refine mul_le_mul (hR y hy) ?_ (norm_nonneg _) hR0
          rw [norm_coe_sphere_one θ]
      _ = R := mul_one R
  have hInt_g : Integrable (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 => H θ ^ n / (n : ℝ)) MeasureTheory.volume.toSphere := by
    have hcont' : Continuous (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 => H θ ^ n / (n : ℝ)) :=
      (hcontH.pow n).div_const _
    refine Integrable.of_bound hcont'.aestronglyMeasurable (R ^ n / (n : ℝ)) ?_
    filter_upwards with θ
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hnum : 0 ≤ H θ ^ n := pow_nonneg (H_nonneg θ) n
    have hval : 0 ≤ H θ ^ n / (n : ℝ) := div_nonneg hnum hnpos.le
    rw [Real.norm_eq_abs, abs_of_nonneg hval]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (H_nonneg θ) (H_le θ) n) hnpos.le
  have houter : (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        ∫ r : Ioi (0 : ℝ), (C.indicator (fun _ => (1 : ℝ))) (r.1 • (θ : EuclideanSpace ℝ (Fin n)))
          ∂MeasureTheory.Measure.volumeIoiPow (n - 1) ∂MeasureTheory.volume.toSphere)
      ≤ ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, H θ ^ n / (n : ℝ) ∂MeasureTheory.volume.toSphere := by
    refine integral_mono_of_nonneg ?_ hInt_g ?_
    · filter_upwards with θ
      refine integral_nonneg_of_ae (ae_of_all _ (fun r => ?_))
      by_cases hr : (r : ℝ) • (θ : EuclideanSpace ℝ (Fin n)) ∈ C
      · simp [Set.indicator_of_mem hr]
      · simp [Set.indicator_of_notMem hr]
    · filter_upwards with θ
      exact hinner θ
  calc MeasureTheory.volume.real C
      = ∫ x : EuclideanSpace ℝ (Fin n), (C.indicator (fun _ => (1 : ℝ))) x ∂MeasureTheory.volume :=
          (integral_indicator_one hCmeas).symm
    _ = ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          ∫ r : Ioi (0 : ℝ), (C.indicator (fun _ => (1 : ℝ))) (r.1 • (θ : EuclideanSpace ℝ (Fin n)))
            ∂MeasureTheory.Measure.volumeIoiPow (n - 1) ∂MeasureTheory.volume.toSphere := hpolar
    _ ≤ ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, H θ ^ n / (n : ℝ) ∂MeasureTheory.volume.toSphere := houter
    _ = (1 / (n : ℝ)) * ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, H θ ^ n ∂MeasureTheory.volume.toSphere := by
        rw [integral_div]; ring
    _ = (1 / (n : ℝ)) * ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          (sSup ((fun y => inner ℝ y (θ : EuclideanSpace ℝ (Fin n))) '' C)) ^ n
          ∂MeasureTheory.volume.toSphere := by
        rw [Hdef]

end Commons.GeometryOfNumbers