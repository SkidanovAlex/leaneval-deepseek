import Mathlib
import Submission.Work.EQ.FatouDefs
import Submission.Work.EQ.Fatou.log_norm_le_integral
import Submission.Work.EQ.Fatou.exists_factor_order
import Submission.Work.EQ.Fatou.measure_zero_zeroSet_circle
import Submission.Work.EQ.Fatou.radial_limit_factor
import Submission.Work.EQ.Fatou.measure_zero_of_tendsto_atTop_of_lintegral_bound
import Submission.Work.EQ.Fatou.integrable_log_sub_log_norm
import Submission.Work.EQ.Fatou.integral_log_sub_log_norm_le
import Submission.Work.EQ.Fatou.volume_eq_zero_of_periodic

namespace Work.EQ.Fatou

open Filter Metric MeasureTheory
open scoped Topology

/-- Periodicity of the exponential: `exp ((θ + 2π) i) = exp (θ i)`. -/
private lemma exp_period (θ : ℝ) :
    Complex.exp ((((θ + 2 * Real.pi : ℝ)) : ℂ) * Complex.I)
      = Complex.exp ((θ : ℂ) * Complex.I) := by
  have hcast : (((θ + 2 * Real.pi : ℝ)) : ℂ) = (θ : ℂ) + ((2 * Real.pi : ℝ) : ℂ) := by
    push_cast; ring
  rw [hcast, add_mul, Complex.exp_add]
  have h1 : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [show (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = 2 * (Real.pi : ℂ) * Complex.I by
      push_cast; ring]
    exact Complex.exp_two_pi_mul_I
  rw [h1, mul_one]

/--
If `h` is holomorphic on the unit disc and nonzero at `0`, and `(r n)` tends to `1` from below
with `r n ∈ (1/2, 1)` and `‖h (r n e^{iθ})‖ ≤ B` (with `B ≥ 1`), then the set of directions `θ`
at which the radial limit of `h` is `0` is Lebesgue-null.

This is the Fatou/Jensen argument: `log B - log ‖h (r n e^{i·})‖` is nonnegative and its integral
over `(0, 2π)` is bounded above by `2π log B - 2π log ‖h 0‖` (Jensen), so Fatou's lemma forces
the set where it tends to `+∞` to be null.
-/
theorem radial_limit_zero_measure_zero {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (Metric.ball 0 1))
    (h0 : h 0 ≠ 0) (r : ℕ → ℝ) (hr : ∀ n, r n ∈ Set.Ioo (1/2 : ℝ) 1)
    (hrt : Filter.Tendsto r Filter.atTop (nhdsWithin 1 (Set.Iio 1)))
    {B : ℝ} (hB1 : 1 ≤ B) (hBb : ∀ n (θ : ℝ), ‖h (r n * Complex.exp ((θ:ℂ) * Complex.I))‖ ≤ B) :
    volume {θ : ℝ | Filter.Tendsto (fun ρ : ℝ => h (ρ * Complex.exp ((θ:ℂ) * Complex.I)))
      (nhdsWithin 1 (Set.Iio 1)) (nhds 0)} = 0 := by
  set S : Set ℝ := {θ : ℝ | Filter.Tendsto (fun ρ : ℝ => h (ρ * Complex.exp ((θ:ℂ) * Complex.I)))
      (nhdsWithin 1 (Set.Iio 1)) (nhds 0)} with hSdef
  set Z : ℕ → Set ℝ := fun n => {θ : ℝ | h (r n * Complex.exp ((θ:ℂ) * Complex.I)) = 0} with hZdef
  set Seq : Set ℝ := {θ : ℝ | Filter.Tendsto (fun n : ℕ => ‖h (r n * Complex.exp ((θ:ℂ) * Complex.I))‖)
      Filter.atTop (nhds 0)} with hSeqdef
  have hr0 : ∀ n, 0 < r n := fun n => lt_trans (by norm_num) (hr n).1
  have hr1 : ∀ n, r n < 1 := fun n => (hr n).2
  have hcont : ∀ n, Continuous (fun θ : ℝ => h (r n * Complex.exp ((θ:ℂ) * Complex.I))) := by
    intro n
    refine hh.continuousOn.comp_continuous ?_ ?_
    · fun_prop
    · intro θ
      rw [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
        Complex.norm_of_nonneg (le_of_lt (hr0 n))]
      exact hr1 n
  have hS_seq : S ⊆ Seq := by
    intro θ hθ
    rw [hSdef] at hθ
    simp only [Set.mem_ofPred_eq] at hθ
    rw [hSeqdef]
    simp only [Set.mem_ofPred_eq]
    exact tendsto_zero_iff_norm_tendsto_zero.mp (hθ.comp hrt)
  have hSeq_meas : MeasurableSet Seq := by
    rw [hSeqdef]
    exact measurableSet_tendsto (nhds (0:ℝ)) (fun n => (hcont n).measurable.norm)
  have hZ_meas : ∀ n, MeasurableSet (Z n) := by
    intro n
    rw [hZdef]
    exact (isClosed_singleton.preimage (hcont n)).measurableSet
  have hZ_null : ∀ n, volume (Z n) = 0 := by
    intro n
    rw [hZdef]
    exact measure_zero_zeroSet_circle hh h0 (show r n ∈ Set.Ioo (0:ℝ) 1 from ⟨hr0 n, hr1 n⟩)
  set g : ℕ → ℝ → ENNReal := fun n θ =>
      ENNReal.ofReal (Real.log B - Real.log ‖h (r n * Complex.exp ((θ:ℂ) * Complex.I))‖) with hgdef
  have hg_meas : ∀ n, Measurable (g n) := by
    intro n
    simp only [hgdef]
    exact (measurable_const.sub (((hcont n).measurable.norm).log)).ennreal_ofReal
  have hg_tendsto : ∀ θ ∈ Seq ∩ (⋃ n, Z n)ᶜ,
      Filter.Tendsto (fun n => g n θ) Filter.atTop (nhds ⊤) := by
    intro θ hθ
    have hθseq : θ ∈ Seq := hθ.1
    have hθnot : θ ∉ ⋃ n, Z n := hθ.2
    rw [hSeqdef] at hθseq
    simp only [Set.mem_ofPred_eq] at hθseq
    have hne : ∀ n, h (r n * Complex.exp ((θ:ℂ) * Complex.I)) ≠ 0 := by
      intro n hn
      exact hθnot (Set.mem_iUnion.mpr ⟨n, by rw [hZdef]; exact hn⟩)
    have hlog : Filter.Tendsto (fun n => Real.log ‖h (r n * Complex.exp ((θ:ℂ) * Complex.I))‖)
        Filter.atTop Filter.atBot := by
      apply Real.tendsto_log_nhdsGT_zero.comp
      rw [tendsto_nhdsWithin_iff]
      refine ⟨hθseq, ?_⟩
      filter_upwards with n
      exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm (norm_ne_zero_iff.mpr (hne n)))
    have h2 : Filter.Tendsto
        (fun n => Real.log B - Real.log ‖h (r n * Complex.exp ((θ:ℂ) * Complex.I))‖)
        Filter.atTop Filter.atTop := by
      rw [Filter.tendsto_atTop]
      intro a
      filter_upwards [Filter.tendsto_atBot.1 hlog (Real.log B - a)] with n hn
      linarith
    simp only [hgdef]
    exact ENNReal.tendsto_ofReal_atTop.comp h2
  have hbound : ∀ n, ∫⁻ θ, g n θ ∂(volume.restrict (Set.Ioc 0 (2 * Real.pi)))
      ≤ ENNReal.ofReal (2 * Real.pi * Real.log B - 2 * Real.pi * Real.log ‖h 0‖) := by
    intro n
    have hinte : Integrable (fun θ : ℝ => Real.log B
        - Real.log ‖h (r n * Complex.exp ((θ:ℂ) * Complex.I))‖)
        (volume.restrict (Set.Ioc 0 (2 * Real.pi))) :=
      integrable_log_sub_log_norm hh (show r n ∈ Set.Ioo (0:ℝ) 1 from ⟨hr0 n, hr1 n⟩)
    have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc 0 (2 * Real.pi))]
        (fun θ : ℝ => Real.log B - Real.log ‖h (r n * Complex.exp ((θ:ℂ) * Complex.I))‖) := by
      filter_upwards with θ
      rcases eq_or_lt_of_le (norm_nonneg (h (r n * Complex.exp ((θ:ℂ) * Complex.I)))) with hz | hpos
      · rw [← hz, Real.log_zero, sub_zero]
        exact Real.log_nonneg hB1
      · exact sub_nonneg.mpr (Real.log_le_log hpos (hBb n θ))
    rw [hgdef]
    simp only
    rw [← ofReal_integral_eq_lintegral_ofReal hinte hnonneg]
    apply ENNReal.ofReal_le_ofReal
    exact integral_log_sub_log_norm_le hh h0 (ρ := r n)
      (show r n ∈ Set.Ioo (0:ℝ) 1 from ⟨hr0 n, hr1 n⟩)
  have hTmeas : MeasurableSet (Seq ∩ (⋃ n, Z n)ᶜ) :=
    hSeq_meas.inter (MeasurableSet.iUnion hZ_meas).compl
  have hTzero : (volume.restrict (Set.Ioc 0 (2 * Real.pi))) (Seq ∩ (⋃ n, Z n)ᶜ) = 0 :=
    measure_zero_of_tendsto_atTop_of_lintegral_bound hTmeas hg_meas hg_tendsto
      ENNReal.ofReal_ne_top hbound
  have hZall_null : (volume.restrict (Set.Ioc 0 (2 * Real.pi))) (⋃ n, Z n) = 0 := by
    have hZn : ∀ n, (volume.restrict (Set.Ioc 0 (2 * Real.pi))) (Z n) = 0 := by
      intro n
      rw [Measure.restrict_apply (hZ_meas n)]
      exact le_antisymm (le_of_le_of_eq (measure_mono (Set.inter_subset_left)) (hZ_null n)) bot_le
    refine le_antisymm ?_ bot_le
    calc (volume.restrict (Set.Ioc 0 (2 * Real.pi))) (⋃ n, Z n)
        ≤ ∑' n, (volume.restrict (Set.Ioc 0 (2 * Real.pi))) (Z n) := measure_iUnion_le _
      _ = 0 := by simp [hZn]
  have hSeq_null : (volume.restrict (Set.Ioc 0 (2 * Real.pi))) Seq = 0 := by
    have hsub : Seq ⊆ (Seq ∩ (⋃ n, Z n)ᶜ) ∪ (⋃ n, Z n) := by
      intro θ hθ
      by_cases h : θ ∈ ⋃ n, Z n
      · exact Set.mem_union_right _ h
      · exact Set.mem_union_left _ ⟨hθ, h⟩
    refine le_antisymm ?_ bot_le
    calc (volume.restrict (Set.Ioc 0 (2 * Real.pi))) Seq
        ≤ (volume.restrict (Set.Ioc 0 (2 * Real.pi))) ((Seq ∩ (⋃ n, Z n)ᶜ) ∪ (⋃ n, Z n)) :=
          measure_mono hsub
      _ ≤ (volume.restrict (Set.Ioc 0 (2 * Real.pi))) (Seq ∩ (⋃ n, Z n)ᶜ)
            + (volume.restrict (Set.Ioc 0 (2 * Real.pi))) (⋃ n, Z n) := measure_union_le _ _
      _ = 0 := by rw [hTzero, hZall_null, add_zero]
  have hSeqIoc : volume (Seq ∩ Set.Ioc 0 (2 * Real.pi)) = 0 := by
    have h1 : volume (Seq ∩ Set.Ioc 0 (2 * Real.pi))
        = (volume.restrict (Set.Ioc 0 (2 * Real.pi))) Seq :=
      (Measure.restrict_apply hSeq_meas).symm
    rw [h1]; exact hSeq_null
  have hSIoc : volume (S ∩ Set.Ioc 0 (2 * Real.pi)) = 0 := by
    refine le_antisymm ?_ bot_le
    calc volume (S ∩ Set.Ioc 0 (2 * Real.pi))
        ≤ volume (Seq ∩ Set.Ioc 0 (2 * Real.pi)) :=
          measure_mono (fun x hx => ⟨hS_seq hx.1, hx.2⟩)
      _ = 0 := hSeqIoc
  have hper : ∀ θ : ℝ, θ + 2 * Real.pi ∈ S ↔ θ ∈ S := by
    intro θ
    rw [hSdef]
    simp only [Set.mem_ofPred_eq]
    rw [show (fun ρ : ℝ => h (ρ * Complex.exp ((((θ + 2 * Real.pi : ℝ)) : ℂ) * Complex.I)))
          = (fun ρ : ℝ => h (ρ * Complex.exp ((θ:ℂ) * Complex.I))) from
        funext (fun ρ => by rw [exp_period])]
  exact volume_eq_zero_of_periodic hper hSIoc

theorem volume_radial_limit_eq_zero {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (Metric.ball 0 1))
    {M : ℝ} (hM : ∀ z ∈ Metric.ball (0:ℂ) 1, ‖g z‖ ≤ M) {c : ℂ}
    (hne : ∃ z ∈ Metric.ball (0:ℂ) 1, g z ≠ c) :
    MeasureTheory.volume {θ : ℝ | Filter.Tendsto (fun r : ℝ => Work.EQ.discVal g r θ)
      (nhdsWithin 1 (Set.Iio 1)) (nhds c)} = 0 := by
  obtain ⟨k, h, hhd, hfh, hh0⟩ := exists_factor_order g hg hne
  have hr : ∀ n : ℕ, (1 - (((n:ℝ) + 3))⁻¹) ∈ Set.Ioo (1/2 : ℝ) 1 := by
    intro n
    have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    have hpos : (0:ℝ) < (n:ℝ) + 3 := by positivity
    have hlt : (((n:ℝ) + 3))⁻¹ < 1/2 := by
      rw [inv_lt_iff_one_lt_mul₀ hpos]
      nlinarith
    refine ⟨by linarith, ?_⟩
    have : 0 < (((n:ℝ)+3))⁻¹ := by positivity
    linarith
  have hrt : Filter.Tendsto (fun n : ℕ => 1 - (((n:ℝ)+3))⁻¹) Filter.atTop
      (nhdsWithin 1 (Set.Iio 1)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Filter.Eventually.of_forall (fun n => (hr n).2)⟩
    have hinv : Filter.Tendsto (fun n : ℕ => (((n:ℝ)+3))⁻¹) Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun n : ℕ => (n:ℝ) + 3) Filter.atTop Filter.atTop :=
        Filter.tendsto_atTop_add_const_right Filter.atTop (3:ℝ) tendsto_natCast_atTop_atTop
      exact h1.inv_tendsto_atTop
    have h3 : Filter.Tendsto (fun n : ℕ => (1:ℝ) - (((n:ℝ)+3))⁻¹) Filter.atTop (nhds (1 - 0)) :=
      tendsto_const_nhds.sub hinv
    simpa using h3
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (g 0)) (hM 0 (by simp [Metric.mem_ball]))
  have hMc : 0 ≤ M + ‖c‖ := add_nonneg hM0 (norm_nonneg c)
  set B : ℝ := max ((M + ‖c‖) * 2^k) 1 with hBdef
  have hB1 : 1 ≤ B := le_max_right _ _
  have hBb : ∀ n (θ : ℝ),
      ‖h ((fun m : ℕ => 1 - (((m:ℝ)+3))⁻¹) n * Complex.exp ((θ:ℂ) * Complex.I))‖ ≤ B := by
    intro n θ
    dsimp only
    set z : ℂ := ((1 - (((n:ℝ)+3))⁻¹) : ℝ) * Complex.exp ((θ:ℂ) * Complex.I) with hz
    have hr0n : 0 < 1 - (((n:ℝ)+3))⁻¹ := by have := (hr n).1; linarith
    have hr1n : 1 - (((n:ℝ)+3))⁻¹ < 1 := (hr n).2
    have hznorm : ‖z‖ = 1 - (((n:ℝ)+3))⁻¹ := by
      rw [hz, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
        Complex.norm_of_nonneg (le_of_lt hr0n)]
    have hzmem : z ∈ Metric.ball (0:ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right, hznorm]; exact hr1n
    have hident : g z - c = z ^ k * h z := hfh z hzmem
    have hprod : ‖g z - c‖ = ‖z‖ ^ k * ‖h z‖ := by rw [hident, norm_mul, norm_pow]
    have hgnorm : ‖g z - c‖ ≤ M + ‖c‖ :=
      le_trans (norm_sub_le _ _) (add_le_add_left (hM z hzmem) ‖c‖)
    have hrk : 0 < ‖z‖ ^ k := pow_pos (by rw [hznorm]; exact hr0n) k
    have hle : ‖h z‖ ≤ (M + ‖c‖) / ‖z‖ ^ k := by
      rw [le_div_iff₀ hrk, mul_comm, ← hprod]
      exact hgnorm
    have hhalf : (1/2:ℝ) ^ k ≤ ‖z‖ ^ k := by
      rw [hznorm]
      exact pow_le_pow_left₀ (by norm_num) (le_of_lt (hr n).1) k
    have hinv : (‖z‖ ^ k)⁻¹ ≤ ((1/2:ℝ) ^ k)⁻¹ := by
      rw [inv_le_inv₀ (pow_pos (by rw [hznorm]; exact hr0n) k) (pow_pos (by norm_num) k)]
      exact hhalf
    have hB2 : (M + ‖c‖) / ‖z‖ ^ k ≤ B := by
      rw [div_eq_mul_inv]
      calc (M + ‖c‖) * (‖z‖^k)⁻¹ ≤ (M + ‖c‖) * (((1/2:ℝ)^k)⁻¹) :=
            mul_le_mul_of_nonneg_left hinv hMc
        _ = (M + ‖c‖) * 2^k := by rw [← inv_pow]; norm_num
        _ ≤ B := le_max_left _ _
    exact le_trans hle hB2
  have hcore := radial_limit_zero_measure_zero hhd hh0 (fun m : ℕ => 1 - (((m:ℝ)+3))⁻¹)
    hr hrt hB1 hBb
  have hS_eq : {θ : ℝ | Filter.Tendsto (fun r : ℝ => Work.EQ.discVal g r θ)
        (nhdsWithin 1 (Set.Iio 1)) (nhds c)}
      = {θ : ℝ | Filter.Tendsto (fun ρ : ℝ => h (ρ * Complex.exp ((θ:ℂ) * Complex.I)))
        (nhdsWithin 1 (Set.Iio 1)) (nhds 0)} := by
    ext θ
    simp only [Set.mem_ofPred_eq]
    show Filter.Tendsto (fun r : ℝ => g (r * Complex.exp ((θ:ℂ) * Complex.I)))
        (nhdsWithin 1 (Set.Iio 1)) (nhds c) ↔
      Filter.Tendsto (fun ρ : ℝ => h (ρ * Complex.exp ((θ:ℂ) * Complex.I)))
        (nhdsWithin 1 (Set.Iio 1)) (nhds 0)
    constructor
    · intro hgt
      have h1 : Filter.Tendsto (fun r : ℝ => g (r * Complex.exp ((θ:ℂ) * Complex.I)) - c)
          (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := by simpa using hgt.sub_const c
      exact (radial_limit_factor (f := fun z => g z - c) (h := h) (k := k) hfh θ).mp h1
    · intro hht
      have hh2 : Filter.Tendsto (fun ρ : ℝ => g (ρ * Complex.exp ((θ:ℂ) * Complex.I)) - c)
          (nhdsWithin 1 (Set.Iio 1)) (nhds 0) :=
        (radial_limit_factor (f := fun z => g z - c) (h := h) (k := k) hfh θ).mpr hht
      have h3 := hh2.add_const c
      simpa using h3
  rw [hS_eq]; exact hcore

end Work.EQ.Fatou
