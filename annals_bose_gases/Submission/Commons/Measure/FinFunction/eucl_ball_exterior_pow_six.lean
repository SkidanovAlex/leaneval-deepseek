import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Order.Interval.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory Metric Filter Set
open scoped Topology ENNReal Real BigOperators Interval

noncomputable section

namespace Commons.Measure.FinFunction

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

private lemma eucl_ball_exterior_finrank : Module.finrank ℝ E3 = 3 := by
  simp

private lemma eucl_ball_exterior_measureReal_unitBall :
    (volume : Measure E3).real (Metric.ball (0 : E3) 1) = (4 / 3 : ℝ) * Real.pi := by
  unfold Measure.real
  rw [EuclideanSpace.volume_ball_fin_three]
  simp
  rw [ENNReal.toReal_ofReal]
  · ring
  · positivity

-- Radial integration on ℝ³ : ∫ x, f ‖x‖ = 4π ∫₀^∞ r² f r, unconditionally.
private lemma eucl_ball_exterior_radial (f : ℝ → ℝ) :
    (∫ x : E3, f ‖x‖) = 4 * Real.pi * (∫ r in Ioi (0 : ℝ), r ^ 2 * f r) := by
  rw [MeasureTheory.integral_fun_norm_addHaar (μ := (volume : Measure E3)) (f := f)]
  rw [eucl_ball_exterior_finrank, eucl_ball_exterior_measureReal_unitBall]
  simp only [nsmul_eq_mul, smul_eq_mul]
  norm_num
  ring

-- derivative of r ↦ -1/(3 r³) is r ↦ (r⁴)⁻¹, at any nonzero point.
private lemma eucl_ball_exterior_deriv_tail (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => -((3 * y ^ 3)⁻¹)) ((x ^ 4)⁻¹) x := by
  have hx3 : (3 * x ^ 3) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (pow_ne_zero 3 hx)
  have hpow : HasDerivAt (fun y : ℝ => 3 * y ^ 3) (3 * (3 * x ^ 2)) x := by
    simpa using (hasDerivAt_pow (3 : ℕ) x).const_mul (3 : ℝ)
  have hinv := hpow.inv hx3
  have hneg := hinv.neg
  have hval : -(-(3 * (3 * x ^ 2)) / (3 * x ^ 3) ^ 2) = (x ^ 4)⁻¹ := by
    field_simp [hx]
  rw [show (-(fun y : ℝ => 3 * y ^ 3)⁻¹) = (fun y : ℝ => -((3 * y ^ 3)⁻¹)) by
        funext y
        rfl] at hneg
  rw [hval] at hneg
  exact hneg

private lemma eucl_ball_exterior_tendsto_zero :
    Tendsto (fun x : ℝ => -((3 * x ^ 3)⁻¹)) atTop (𝓝 (0 : ℝ)) := by
  have hp : Tendsto (fun x : ℝ => x ^ 3) atTop atTop := by
    exact tendsto_pow_atTop (n := 3) (by norm_num)
  have htop : Tendsto (fun x : ℝ => 3 * x ^ 3) atTop atTop := by
    exact hp.const_mul_atTop (by norm_num : (0 : ℝ) < 3)
  have hinv0 : Tendsto (fun x : ℝ => (3 * x ^ 3)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp htop
  simpa using hinv0.neg

-- ∫_R^∞ r⁻⁴ dr = 1/(3 R³)  (for R > 0)
private lemma eucl_ball_exterior_tail_integral (R : ℝ) (hR : 0 < R) :
    (∫ r in Ioi R, (r ^ 4)⁻¹) = (1 / 3 : ℝ) * (R ^ 3)⁻¹ := by
  let g : ℝ → ℝ := fun x => -((3 * x ^ 3)⁻¹)
  let g' : ℝ → ℝ := fun x => (x ^ 4)⁻¹
  have hR0 : R ≠ 0 := ne_of_gt hR
  have hcont : ContinuousWithinAt g (Ici R) R := by
    apply ContinuousAt.continuousWithinAt
    have hc1 : ContinuousAt (fun x : ℝ => 3 * x ^ 3) R := by fun_prop
    have hc2 : ContinuousAt (fun x : ℝ => (3 * x ^ 3)⁻¹) R :=
      hc1.inv₀ (mul_ne_zero (by norm_num) (pow_ne_zero 3 hR0))
    have hc3 : ContinuousAt (fun x : ℝ => -((3 * x ^ 3)⁻¹)) R := hc2.neg
    simpa [g] using hc3
  have hderiv : ∀ x ∈ Ioi R, HasDerivAt g (g' x) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_trans hR hx)
    simpa [g, g'] using eucl_ball_exterior_deriv_tail x hx0
  have hg'pos : ∀ x ∈ Ioi R, 0 ≤ g' x := by
    intro x hx
    have hxpos : 0 < x := lt_trans hR hx
    dsimp [g']
    positivity
  have hg : Tendsto g atTop (𝓝 (0 : ℝ)) := by
    simpa [g] using eucl_ball_exterior_tendsto_zero
  have hmain := integral_Ioi_of_hasDerivAt_of_nonneg (g := g) (g' := g') (a := R)
    (l := (0 : ℝ)) hcont hderiv hg'pos hg
  calc
    (∫ r in Ioi R, (r ^ 4)⁻¹) = ∫ x in Ioi R, g' x := by simp [g']
    _ = 0 - g R := hmain
    _ = (1 / 3 : ℝ) * (R ^ 3)⁻¹ := by
      simp [g]
      field_simp [hR0]

theorem eucl_ball_exterior_pow_six (R : ℝ) (hR : 0 < R) :
    (∫ p : EuclideanSpace ℝ (Fin 3) in {p : EuclideanSpace ℝ (Fin 3) | R ≤ ‖p‖}, ((‖p‖) ^ 6)⁻¹)
      = (4 / 3 : ℝ) * Real.pi * (R ^ 3)⁻¹ := by
  let S : Set E3 := {p : E3 | R ≤ ‖p‖}
  let g : ℝ → ℝ := (Set.Ici R).indicator (fun r : ℝ => (r ^ 6)⁻¹)
  have hmeas : MeasurableSet S := by
    dsimp [S]
    measurability
  have hpoint : (fun p : E3 => g ‖p‖) = S.indicator (fun p : E3 => (‖p‖ ^ 6)⁻¹) := by
    funext p
    by_cases hp : R ≤ ‖p‖
    · have hmemS : p ∈ S := hp
      have hmemR : ‖p‖ ∈ Set.Ici R := hp
      simp [S, g, hmemS, hmemR]
    · have hmemS : p ∉ S := by
        intro hs
        exact hp hs
      have hmemR : ‖p‖ ∉ Set.Ici R := by
        intro hs
        exact hp hs
      simp [S, g, hmemS, hmemR]
  have hfull : (∫ p : E3, g ‖p‖) = (∫ p in S, (‖p‖ ^ 6)⁻¹) := by
    calc
      (∫ p : E3, g ‖p‖) = ∫ p : E3, S.indicator (fun p : E3 => (‖p‖ ^ 6)⁻¹) p := by
        rw [hpoint]
      _ = ∫ p in S, (‖p‖ ^ 6)⁻¹ := integral_indicator hmeas
  have hJ2 : (∫ r in Ioi (0 : ℝ), r ^ 2 * g r) = (1 / 3 : ℝ) * (R ^ 3)⁻¹ := by
    have hind : (fun r : ℝ => r ^ 2 * g r) =
        (Set.Ici R).indicator (fun r : ℝ => r ^ 2 * (r ^ 6)⁻¹) := by
      funext r
      by_cases hr : R ≤ r
      · have hmem : r ∈ Set.Ici R := hr
        simp [g, hmem]
      · have hmem : r ∉ Set.Ici R := by
          intro hs
          exact hr hs
        simp [g, hmem]
    have h_int_ind : (∫ r in Ioi (0 : ℝ), r ^ 2 * g r) =
        ∫ r in Ioi (0 : ℝ), (Set.Ici R).indicator (fun r : ℝ => r ^ 2 * (r ^ 6)⁻¹) r := by
      rw [hind]
    have h_step2 : (∫ r in Ioi (0 : ℝ),
        (Set.Ici R).indicator (fun r : ℝ => r ^ 2 * (r ^ 6)⁻¹) r) =
        ∫ r in Ioi (0 : ℝ) ∩ Set.Ici R, r ^ 2 * (r ^ 6)⁻¹ := by
      rw [setIntegral_indicator (s := Ioi (0 : ℝ)) (t := Set.Ici R)
        (f := fun r : ℝ => r ^ 2 * (r ^ 6)⁻¹) (by measurability : MeasurableSet (Set.Ici R))]
    have h_inter : Ioi (0 : ℝ) ∩ Set.Ici R = Set.Ici R := by
      ext r
      constructor
      · intro hr
        exact hr.2
      · intro hr
        have hrpos : (0 : ℝ) < r := lt_of_lt_of_le hR hr
        exact ⟨hrpos, hr⟩
    have h_step3 : (∫ r in Ioi (0 : ℝ) ∩ Set.Ici R, r ^ 2 * (r ^ 6)⁻¹) =
        ∫ r in Set.Ici R, r ^ 2 * (r ^ 6)⁻¹ := by
      rw [h_inter]
    have h_step4 : (∫ r in Set.Ici R, r ^ 2 * (r ^ 6)⁻¹) =
        ∫ r in Ioi R, r ^ 2 * (r ^ 6)⁻¹ := by
      rw [integral_Ici_eq_integral_Ioi (f := fun r : ℝ => r ^ 2 * (r ^ 6)⁻¹)]
    have h_step5 : (∫ r in Ioi R, r ^ 2 * (r ^ 6)⁻¹) = ∫ r in Ioi R, (r ^ 4)⁻¹ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      have hRr : R < r := hr
      have hr0 : r ≠ 0 := ne_of_gt (lt_trans hR hRr)
      field_simp [hr0]
    calc
      (∫ r in Ioi (0 : ℝ), r ^ 2 * g r)
          = ∫ r in Ioi (0 : ℝ) ∩ Set.Ici R, r ^ 2 * (r ^ 6)⁻¹ := by
            rw [h_int_ind, h_step2]
      _ = ∫ r in Set.Ici R, r ^ 2 * (r ^ 6)⁻¹ := h_step3
      _ = ∫ r in Ioi R, r ^ 2 * (r ^ 6)⁻¹ := h_step4
      _ = ∫ r in Ioi R, (r ^ 4)⁻¹ := h_step5
      _ = (1 / 3 : ℝ) * (R ^ 3)⁻¹ := eucl_ball_exterior_tail_integral R hR
  calc
    (∫ p in S, (‖p‖ ^ 6)⁻¹) = ∫ p : E3, g ‖p‖ := hfull.symm
    _ = 4 * Real.pi * (∫ r in Ioi (0 : ℝ), r ^ 2 * g r) := eucl_ball_exterior_radial g
    _ = 4 * Real.pi * ((1 / 3 : ℝ) * (R ^ 3)⁻¹) := by rw [hJ2]
    _ = (4 / 3 : ℝ) * Real.pi * (R ^ 3)⁻¹ := by ring

end Commons.Measure.FinFunction