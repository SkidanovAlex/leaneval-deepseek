import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Topology.Separation.CompletelyRegular

set_option linter.style.haveILetI false

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

namespace Commons.Measure.EuclideanSpace

/-- Volume of the sub-level set `{z : Fin d → ℂ | ∑ j, ‖z j‖ ^ 2 < r ^ 2}`:
it is `r ^ (2 d)` times the volume of the unit `L²`-ball in `ℂ^d`. -/
theorem volume_sum_sq_lt {d : ℕ} (hd : 1 ≤ d) (r : ℝ) (hr : 0 ≤ r) :
    MeasureTheory.volume {z : Fin d → ℂ | ∑ j, ‖z j‖ ^ 2 < r ^ 2} =
      ENNReal.ofReal (r ^ (2 * d)) *
        ENNReal.ofReal ((Real.pi * Real.Gamma (2 / (2 : ℝ) + 1)) ^ d /
          Real.Gamma (2 * (d : ℝ) / (2 : ℝ) + 1)) := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (by omega)
  have hset : {z : Fin d → ℂ | (∑ j, ‖z j‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) < r}
      = {z : Fin d → ℂ | ∑ j, ‖z j‖ ^ 2 < r ^ 2} := by
    ext z
    simp only [Set.mem_ofPred_eq]
    have hA : 0 ≤ ∑ j, ‖z j‖ ^ 2 := by positivity
    have hsum : (∑ j, ‖z j‖ ^ (2 : ℝ)) = ∑ j, ‖z j‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hsum, ← Real.sqrt_eq_rpow, Real.sqrt_lt hA hr]
  rw [← hset, Complex.volume_sum_rpow_lt (Fin d) (p := 2) (by norm_num : (1 : ℝ) ≤ 2) r,
    Fintype.card_fin, ← ENNReal.ofReal_pow hr]

/-- The positive part `(- log (∑ j, ‖z j‖ ^ 2))⁺` is integrable on `Fin d → ℂ`:
the logarithmic singularity of the norm at the origin is integrable in every positive
dimension. -/
theorem integrable_max_zero_neg_log_sum_sq {d : ℕ} (hd : 1 ≤ d) :
    Integrable (fun z : Fin d → ℂ => max 0 (- Real.log (∑ j, ‖z j‖ ^ 2))) volume := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hφnn : ∀ z : Fin d → ℂ, 0 ≤ max 0 (- Real.log (∑ j, ‖z j‖ ^ 2)) :=
    fun z => le_max_left _ _
  have hφmeas : Measurable fun z : Fin d → ℂ => max 0 (- Real.log (∑ j, ‖z j‖ ^ 2)) := by
    measurability
  -- the constant multiplying the tail measures
  set C : ℝ≥0∞ := ENNReal.ofReal ((Real.pi * Real.Gamma (2 / (2 : ℝ) + 1)) ^ d /
      Real.Gamma (2 * (d : ℝ) / (2 : ℝ) + 1)) with hC
  have hexp2 : ∀ t : ℝ, Real.exp (-t) = (Real.exp (-t / 2)) ^ 2 := by
    intro t
    rw [← Real.exp_nat_mul (-t / 2) 2]
    congr 1
    push_cast
    ring
  have hexp : ∀ t : ℝ, (Real.exp (-t / 2)) ^ (2 * d) = Real.exp (-(d : ℝ) * t) := by
    intro t
    rw [← Real.exp_nat_mul (-t / 2) (2 * d)]
    congr 1
    push_cast
    ring
  have hbound : ∀ t ∈ Set.Ioi (0 : ℝ),
      volume {a : Fin d → ℂ | t < max 0 (- Real.log (∑ j, ‖a j‖ ^ 2))}
        ≤ C * ENNReal.ofReal (Real.exp (-(d : ℝ) * t)) := by
    intro t ht
    have ht0 : 0 < t := ht
    have hsub : {a : Fin d → ℂ | t < max 0 (- Real.log (∑ j, ‖a j‖ ^ 2))}
        ⊆ {a : Fin d → ℂ | ∑ j, ‖a j‖ ^ 2 < Real.exp (-t)} := by
      intro z hz
      simp only [Set.mem_ofPred_eq] at hz ⊢
      have hneg : 0 < - Real.log (∑ j, ‖z j‖ ^ 2) := by
        by_contra hle
        rw [not_lt] at hle
        have : max 0 (- Real.log (∑ j, ‖z j‖ ^ 2)) ≤ 0 := max_le le_rfl hle
        linarith
      have hm : max 0 (- Real.log (∑ j, ‖z j‖ ^ 2)) = - Real.log (∑ j, ‖z j‖ ^ 2) :=
        max_eq_right hneg.le
      have hlog : Real.log (∑ j, ‖z j‖ ^ 2) < -t := by linarith
      have hg0 : 0 ≤ ∑ j, ‖z j‖ ^ 2 := by positivity
      have hgpos : 0 < ∑ j, ‖z j‖ ^ 2 := by
        rcases eq_or_lt_of_le hg0 with h | h
        · rw [← h, Real.log_zero] at hlog; linarith
        · exact h
      exact (Real.log_lt_iff_lt_exp hgpos).mp hlog
    have hvol : volume {a : Fin d → ℂ | ∑ j, ‖a j‖ ^ 2 < Real.exp (-t)}
        = C * ENNReal.ofReal (Real.exp (-(d : ℝ) * t)) := by
      rw [hexp2 t, volume_sum_sq_lt hd (Real.exp (-t / 2)) (Real.exp_pos _).le,
        hexp t, hC, mul_comm]
    exact le_trans (measure_mono hsub) hvol.le
  have hmeas_exp : Measurable fun t : ℝ => ENNReal.ofReal (Real.exp (-(d : ℝ) * t)) := by
    exact ENNReal.measurable_ofReal.comp (by fun_prop)
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-(d : ℝ) * t)) (Set.Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 hd0
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] (fun t : ℝ => Real.exp (-(d : ℝ) * t)) :=
    Eventually.of_forall (fun t => (Real.exp_pos _).le)
  refine ⟨hφmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hφnn)]
  rw [lintegral_eq_lintegral_meas_lt volume (Eventually.of_forall hφnn) hφmeas.aemeasurable]
  calc ∫⁻ t in Set.Ioi (0 : ℝ), volume {a : Fin d → ℂ | t < max 0 (- Real.log (∑ j, ‖a j‖ ^ 2))}
      ≤ ∫⁻ t in Set.Ioi (0 : ℝ), C * ENNReal.ofReal (Real.exp (-(d : ℝ) * t)) :=
        setLIntegral_mono' measurableSet_Ioi hbound
    _ = C * ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(d : ℝ) * t)) :=
        lintegral_const_mul C hmeas_exp
    _ = C * ENNReal.ofReal (∫ t in Set.Ioi (0 : ℝ), Real.exp (-(d : ℝ) * t)) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint hnn]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- In every dimension `d ≥ 1`, `z ↦ |log (∑ j, ‖z j‖ ^ 2)|` is integrable on every
closed ball of `ℂ^d`. -/
theorem integrableOn_abs_log_sum_sq {d : ℕ} (hd : 1 ≤ d) (R : ℝ) :
    MeasureTheory.IntegrableOn (fun z : Fin d → ℂ => |Real.log (∑ j, ‖z j‖ ^ 2)|)
      (Metric.closedBall (0 : Fin d → ℂ) R) (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) := by
  rcases lt_or_ge R 0 with hR | hR
  · rw [Metric.closedBall_eq_empty.mpr hR]
    exact integrableOn_empty
  · set φ : (Fin d → ℂ) → ℝ := fun z => max 0 (- Real.log (∑ j, ‖z j‖ ^ 2)) with hφ
    set C : ℝ := max 0 (Real.log ((d : ℝ) * R ^ 2)) with hC
    have hCnn : 0 ≤ C := le_max_left _ _
    have hφ_int : IntegrableOn φ (Metric.closedBall (0 : Fin d → ℂ) R) volume :=
      (integrable_max_zero_neg_log_sum_sq hd).integrableOn
    have hC_int : IntegrableOn (fun _ : Fin d → ℂ => C) (Metric.closedBall (0 : Fin d → ℂ) R) volume := by
      refine IntegrableOn.of_bound (isCompact_closedBall (0 : Fin d → ℂ) R).measure_lt_top
        aestronglyMeasurable_const C ?_
      filter_upwards with z
      rw [Real.norm_of_nonneg hCnn]
    have hFmeas : AEStronglyMeasurable (fun z : Fin d → ℂ => |Real.log (∑ j, ‖z j‖ ^ 2)|)
        (volume.restrict (Metric.closedBall (0 : Fin d → ℂ) R)) := by
      apply Measurable.aestronglyMeasurable
      measurability
    refine Integrable.mono' (hφ_int.add hC_int) hFmeas ?_
    filter_upwards [ae_restrict_mem (measurableSet_closedBall)] with z hz
    have hzR : ‖z‖ ≤ R := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      simpa using hz
    have hgsq_le : ∑ j, ‖z j‖ ^ 2 ≤ (d : ℝ) * R ^ 2 := by
      calc ∑ j, ‖z j‖ ^ 2 ≤ ∑ _j : Fin d, R ^ 2 := by
            refine Finset.sum_le_sum (fun j _ => ?_)
            exact pow_le_pow_left₀ (norm_nonneg _) (le_trans (norm_le_pi_norm z j) hzR) 2
        _ = (d : ℝ) * R ^ 2 := by simp [Finset.sum_const, nsmul_eq_mul]
    have hbound : ‖|Real.log (∑ j, ‖z j‖ ^ 2)|‖ ≤ φ z + C := by
      rw [Real.norm_of_nonneg (abs_nonneg _)]
      rcases lt_or_ge (1 : ℝ) (∑ j, ‖z j‖ ^ 2) with h1 | h1
      · have hg0 : 0 < ∑ j, ‖z j‖ ^ 2 := one_pos.trans h1
        have hlog : Real.log (∑ j, ‖z j‖ ^ 2) ≤ C := by
          have h1' : Real.log (∑ j, ‖z j‖ ^ 2) ≤ Real.log ((d : ℝ) * R ^ 2) :=
            Real.log_le_log hg0 hgsq_le
          exact le_trans h1' (le_max_right _ _)
        rw [abs_of_nonneg (Real.log_nonneg h1.le)]
        linarith [le_max_left (0:ℝ) (-Real.log (∑ j, ‖z j‖ ^ 2))]
      · have hlog : Real.log (∑ j, ‖z j‖ ^ 2) ≤ 0 := Real.log_nonpos (by positivity) h1
        have hφz : φ z = - Real.log (∑ j, ‖z j‖ ^ 2) := by
          rw [hφ]; exact max_eq_right (neg_nonneg.mpr hlog)
        rw [abs_of_nonpos hlog, hφz]
        linarith [le_max_left (0:ℝ) (-Real.log (∑ j, ‖z j‖ ^ 2))]
    simpa [Pi.add_apply] using hbound

end Commons.Measure.EuclideanSpace