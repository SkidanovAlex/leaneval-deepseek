import Mathlib
import Submission.Work.Mostow.thickPart_cocompact

/-!
# A lower bound for the volume of a hyperbolic ball

For every `n` there is a positive constant `c` with

`volH n (hBall 0 r) ≥ ofReal (c * r ^ n)`   for all `0 < r ≤ 1`.

The proof compares the hyperbolic ball with a Euclidean ball: the hyperbolic density
`hdens u = 1 / √(1+‖u‖²)` is at least `1/√2` on the Euclidean ball of radius `r ≤ 1`, and
the Euclidean ball of radius `r` is contained in the hyperbolic ball of radius `r` because
the hyperbolic distance to the origin is `arsinh ‖u‖`.
-/

namespace Work.Mostow

open Submission.Mostow MeasureTheory
open scoped ENNReal Topology

noncomputable section

set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

variable {n : ℕ}

/-- The hyperbolic ball about the base point is the Euclidean ball of radius `sinh r`. -/
lemma hBall_zero_eq_metricBall (r : ℝ) :
    hBall (0 : E n) r = Metric.ball 0 (Real.sinh r) := by
  ext x
  simp only [hBall, Set.mem_ofPred_eq, Metric.mem_ball, dist_zero_right]
  constructor
  · intro h
    rw [← Work.Mostow.sinh_hdist_zero x]
    exact Real.sinh_lt_sinh.mpr h
  · intro h
    exact Real.sinh_lt_sinh.mp (by rw [Work.Mostow.sinh_hdist_zero x]; exact h)

/-- On the Euclidean ball of radius `r ≤ 1` the hyperbolic density is at least `1/√2`. -/
lemma ofReal_inv_sqrt_two_le_hdens (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) {u : E n}
    (hu : u ∈ Metric.ball (0 : E n) r) : ENNReal.ofReal ((√2)⁻¹) ≤ hdens u := by
  have hnorm : ‖u‖ < r := by
    rw [Metric.mem_ball, dist_zero_right] at hu; exact hu
  have hnorm1 : ‖u‖ < 1 := lt_of_lt_of_le hnorm hr1
  have hlt : tpart u < √2 := by
    rw [tpart]
    apply Real.sqrt_lt_sqrt (by positivity)
    nlinarith [norm_nonneg u]
  have hinv : (√2)⁻¹ ≤ (tpart u)⁻¹ :=
    (inv_le_inv₀ (Real.sqrt_pos.mpr (by norm_num)) (Work.Mostow.tpart_pos u)).mpr hlt.le
  rw [Work.Mostow.hdens_apply]
  exact ENNReal.ofReal_le_ofReal hinv

/-- In dimension `0` the chart is a single point, so the whole space has measure `1`. -/
lemma volume_univ_fin_zero : (volume : Measure (E 0)) Set.univ = 1 := by
  have h := PiLp.volume_preserving_toLp (Fin 0)
  have h2 := h.measure_preimage (MeasurableSet.univ.nullMeasurableSet :
    NullMeasurableSet (Set.univ : Set (E 0)) volume)
  rw [Set.preimage_univ] at h2
  rw [← h2, MeasureTheory.volume_pi, Measure.pi_univ]
  simp

/-- The (explicit) lower bound in positive dimension. -/
lemma hBallVolumeLower_pos (n : ℕ) (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      ENNReal.ofReal (c * r ^ n) ≤ volH n (hBall (0 : E n) r) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hG : 0 < Real.Gamma ((n:ℝ)/2 + 1) := Real.Gamma_pos_of_pos (by positivity)
  have hp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hvpos : 0 < Real.sqrt Real.pi ^ n / Real.Gamma ((n:ℝ)/2 + 1) := by positivity
  refine ⟨(√2)⁻¹ * (Real.sqrt Real.pi ^ n / Real.Gamma ((n:ℝ)/2 + 1)), by positivity, ?_⟩
  intro r hr hr1
  have hmeas : MeasurableSet (hBall (0 : E n) r) := by
    rw [hBall_zero_eq_metricBall r]; exact Metric.isOpen_ball.measurableSet
  have hvolH : volH n (hBall (0 : E n) r) = ∫⁻ u in hBall (0 : E n) r, hdens u :=
    Work.Mostow.volHApply n hmeas
  have hsub : Metric.ball (0 : E n) r ⊆ hBall (0 : E n) r := by
    rw [hBall_zero_eq_metricBall r]
    exact Metric.ball_subset_ball (Real.self_le_sinh_iff.mpr hr.le)
  have hvol : volume (Metric.ball (0 : E n) r)
      = ENNReal.ofReal (r ^ n) *
        ENNReal.ofReal (Real.sqrt Real.pi ^ n / Real.Gamma ((n:ℝ)/2 + 1)) := by
    rw [EuclideanSpace.volume_ball (Fin n) (0 : E n) r]
    simp only [Fintype.card_fin]
    rw [ENNReal.ofReal_pow hr.le]
  have hd : ENNReal.ofReal ((√2)⁻¹) = (ENNReal.ofReal (√2))⁻¹ :=
    ENNReal.ofReal_inv_of_pos (show (0:ℝ) < √2 by norm_num)
  have key : ENNReal.ofReal
        (((√2)⁻¹ * (Real.sqrt Real.pi ^ n / Real.Gamma ((n:ℝ)/2 + 1))) * r ^ n)
      = ENNReal.ofReal ((√2)⁻¹) *
        (ENNReal.ofReal (r ^ n) *
          ENNReal.ofReal (Real.sqrt Real.pi ^ n / Real.Gamma ((n:ℝ)/2 + 1))) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      mul_assoc, mul_comm (ENNReal.ofReal (Real.sqrt Real.pi ^ n / Real.Gamma ((n:ℝ)/2 + 1)))]
  calc ENNReal.ofReal
        (((√2)⁻¹ * (Real.sqrt Real.pi ^ n / Real.Gamma ((n:ℝ)/2 + 1))) * r ^ n)
      = ENNReal.ofReal ((√2)⁻¹) * volume (Metric.ball (0 : E n) r) := by rw [key, hvol]
    _ = (ENNReal.ofReal (√2))⁻¹ * volume (Metric.ball (0 : E n) r) := by rw [hd]
    _ ≤ ∫⁻ u in Metric.ball (0 : E n) r, hdens u := by
        rw [← setLIntegral_const]
        refine setLIntegral_mono Work.Mostow.measurable_hdens (fun u hu => ?_)
        rw [← hd]
        exact ofReal_inv_sqrt_two_le_hdens r hr hr1 hu
    _ ≤ volH n (hBall (0 : E n) r) := by rw [hvolH]; exact lintegral_mono_set hsub

/-- The dimension-`0` lower bound. -/
lemma hBallVolumeLower_zero :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      ENNReal.ofReal (c * r ^ 0) ≤ volH 0 (hBall (0 : E 0) r) := by
  refine ⟨1, one_pos, ?_⟩
  intro r hr hr1
  have hball : hBall (0 : E 0) r = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    rw [hBall, Set.mem_ofPred_eq]
    have hx : x = 0 := Subsingleton.elim x 0
    rw [hx]
    have h0 : hdist (0 : E 0) 0 = 0 := by rw [hdist, tpart]; simp [Real.arcosh_zero]
    rw [h0]; exact hr
  have hdens1 : (hdens : E 0 → ℝ≥0∞) = fun _ => 1 := by
    funext u
    have ht : tpart u = 1 := by
      rw [tpart]
      have : ‖u‖ = 0 := norm_eq_zero.mpr (Subsingleton.elim u 0)
      rw [this]; norm_num
    rw [Work.Mostow.hdens_apply, ht]
    simp
  have hvolH : volH 0 (hBall (0 : E 0) r) = 1 := by
    rw [hball, Work.Mostow.volH_def, hdens1]
    change ((volume : Measure (E 0)).withDensity (1 : E 0 → ℝ≥0∞)) Set.univ = 1
    rw [withDensity_one]
    exact volume_univ_fin_zero
  rw [hvolH]
  simp

theorem hBallVolumeLower (n : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      ENNReal.ofReal (c * r ^ n) ≤
        Submission.Mostow.volH n (Work.Mostow.hBall (0 : Submission.Mostow.E n) r) := by
  rcases n with _ | m
  · exact hBallVolumeLower_zero
  · exact hBallVolumeLower_pos (m + 1) (Nat.succ_pos m)

end

end Work.Mostow
