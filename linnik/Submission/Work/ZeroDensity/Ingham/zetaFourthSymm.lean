import Mathlib
import Submission.Work.ZeroDensity.Ingham.zetaFourthMomentIntegral
import Submission.Work.ZeroDensity.Ingham.AfeClean.zetaAfeSharp

namespace Work.ZeroDensity.Ingham

open MeasureTheory

/-- **Ingham's integral fourth-moment bound on the critical line, one-sided form**, proved from
the (clean) sharp approximate functional equation
`Work.ZeroDensity.Ingham.AfeClean.zetaAfeSharp`, the fourth-moment bound for the step-truncated
Dirichlet polynomial (`stepPoly_fourthMoment`) and the crude bound near the origin
(`exists_bound_zeta_small`). -/
theorem zetaFourthMomentCleanAux : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
    (∫ t in (0:ℝ)..T, ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 4)
      ≤ C * T * (Real.log T) ^ 4 := by
  obtain ⟨C0, hC0pos, hAFE⟩ := AfeClean.zetaAfeSharp
  obtain ⟨C2, hC2pos, hpoly⟩ := stepPoly_fourthMoment
  obtain ⟨C1, hC1pos, hcrude⟩ := exists_bound_zeta_small
  refine ⟨256 * C0 ^ 4 + 16 * C1 ^ 4 + 16 * C0 ^ 4 * C2 + 16, by positivity, ?_⟩
  intro T hT
  set M : ℕ := ⌊Real.sqrt (T / (2 * Real.pi))⌋₊ + 1 with hMdef
  have hT0 : (0:ℝ) ≤ T := by linarith
  have hM1 : 1 ≤ M := by rw [hMdef]; exact Nat.le_add_left _ _
  have hlog2 : (0.5:ℝ) ≤ Real.log T := by
    have h2 : (0.5:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    exact le_trans h2 (Real.log_le_log (by norm_num) hT)
  have hlog4 : (0.0625:ℝ) ≤ (Real.log T) ^ 4 := by
    have h5 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 0.5) hlog2 4
    norm_num at h5 ⊢
    linarith [h5]
  have hTlog : (1/8:ℝ) ≤ T * (Real.log T) ^ 4 := by nlinarith [hT, hlog4]
  have hM4T : (M:ℝ) ^ 2 ≤ 4 * T := by
    have hfloor : ((⌊Real.sqrt (T / (2 * Real.pi))⌋₊ : ℕ) : ℝ)
        ≤ Real.sqrt (T / (2 * Real.pi)) := Nat.floor_le (by positivity)
    have hle : Real.sqrt (T / (2 * Real.pi)) ≤ Real.sqrt T := by
      refine Real.sqrt_le_sqrt ?_
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi)]
      nlinarith [Real.pi_gt_three, hT0]
    have hMl : (M:ℝ) = ((⌊Real.sqrt (T / (2 * Real.pi))⌋₊ : ℕ) : ℝ) + 1 := by
      rw [hMdef]; push_cast; ring
    have hfnn : (0:ℝ) ≤ ((⌊Real.sqrt (T / (2 * Real.pi))⌋₊ : ℕ) : ℝ) := Nat.cast_nonneg _
    have h1 : (M:ℝ) ≤ Real.sqrt T + 1 := by
      rw [hMl]
      linarith [hfloor, hle]
    have hMnn : (0:ℝ) ≤ (M:ℝ) := by rw [hMl]; linarith
    have hsq : Real.sqrt T ^ 2 = T := Real.sq_sqrt hT0
    have hT1 : (1:ℝ) ≤ T := by linarith
    have hsT : (1:ℝ) ≤ Real.sqrt T := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hT1
    have hsqle : Real.sqrt T ≤ T := by nlinarith [hsq, hsT, Real.sqrt_nonneg T]
    have hsq2 : (M:ℝ) ^ 2 ≤ (Real.sqrt T + 1) ^ 2 := pow_le_pow_left₀ hMnn h1 2
    have hexp : (Real.sqrt T + 1) ^ 2 = T + 2 * Real.sqrt T + 1 := by rw [add_sq, hsq]; ring
    rw [hexp] at hsq2
    nlinarith [hsq2, hsT, hsqle, hT1]
  have hpoint : ∀ t ∈ Set.Icc (2:ℝ) T,
      ‖riemannZeta ((1/2:ℂ) + (t:ℂ)*Complex.I)‖ ^ 4 ≤ 16 * C0 ^ 4 * (1 + ‖stepPoly M t‖ ^ 4) := by
    intro t ht
    have ht1 : (1:ℝ) ≤ t := by linarith [ht.1]
    have hafe := hAFE t ht1
    have hfloor2 : ⌊Real.sqrt (t / (2 * Real.pi))⌋₊ + 1 ≤ M := by
      rw [hMdef]
      refine Nat.add_le_add_right (Nat.floor_mono ?_) 1
      refine Real.sqrt_le_sqrt ?_
      rw [div_le_div_iff_of_pos_right (by positivity : (0:ℝ) < 2 * Real.pi)]
      exact ht.2
    have hsum := stepPoly_eq_dirichletSum M t (by linarith) hfloor2
    have hstep : (1 + ‖∑ n ∈ Finset.Icc 1 (⌊Real.sqrt (t / (2 * Real.pi))⌋₊ + 1),
          (n : ℂ) ^ (-((1 / 2 : ℂ) + (t : ℂ) * Complex.I))‖) = 1 + ‖stepPoly M t‖ := by
      rw [hsum]
    rw [hstep] at hafe
    calc ‖riemannZeta ((1/2:ℂ) + (t:ℂ)*Complex.I)‖ ^ 4
        ≤ (C0 * (1 + ‖stepPoly M t‖)) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) hafe 4
      _ = C0 ^ 4 * (1 + ‖stepPoly M t‖) ^ 4 := by ring
      _ ≤ C0 ^ 4 * (16 * (1 + ‖stepPoly M t‖ ^ 4)) :=
          mul_le_mul_of_nonneg_left (one_add_pow_four_le (norm_nonneg _)) (by positivity)
      _ = 16 * C0 ^ 4 * (1 + ‖stepPoly M t‖ ^ 4) := by ring
  have hcontζ : Continuous (fun t : ℝ => ‖riemannZeta ((1/2:ℂ) + (t:ℂ)*Complex.I)‖ ^ 4) := by
    refine Continuous.pow ?_ 4
    refine Continuous.norm ?_
    refine continuous_iff_continuousAt.mpr (fun t => ?_)
    have hs : ((1/2 : ℂ) + (t:ℂ)*Complex.I) ≠ 1 := by
      intro h
      have h2 := congrArg Complex.re h
      norm_num at h2
    exact ContinuousAt.comp ((differentiableAt_riemannZeta hs).continuousAt) (by fun_prop)
  have hsplit : (∫ t in (0:ℝ)..T, ‖riemannZeta ((1/2:ℂ) + (t:ℂ)*Complex.I)‖ ^ 4)
      = (∫ t in (0:ℝ)..2, ‖riemannZeta ((1/2:ℂ) + (t:ℂ)*Complex.I)‖ ^ 4)
        + (∫ t in (2:ℝ)..T, ‖riemannZeta ((1/2:ℂ) + (t:ℂ)*Complex.I)‖ ^ 4) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hcontζ.intervalIntegrable (0:ℝ) 2) (hcontζ.intervalIntegrable (2:ℝ) T)).symm
  have hfirst : (∫ t in (0:ℝ)..2, ‖riemannZeta ((1/2:ℂ) + (t:ℂ)*Complex.I)‖ ^ 4)
      ≤ C1 ^ 4 * 2 := by
    have hmono : (∫ t in (0:ℝ)..2, ‖riemannZeta ((1/2:ℂ) + (t:ℂ)*Complex.I)‖ ^ 4)
        ≤ ∫ _t in (0:ℝ)..2, C1 ^ 4 :=
      intervalIntegral.integral_mono_on (by norm_num)
        (hcontζ.intervalIntegrable (0:ℝ) 2) (intervalIntegrable_const (c := (C1 ^ 4)))
        (fun t ht => pow_le_pow_left₀ (norm_nonneg _) (hcrude t ht) 4)
    calc (∫ t in (0:ℝ)..2, ‖riemannZeta ((1/2:ℂ) + (t:ℂ)*Complex.I)‖ ^ 4)
        ≤ ∫ _t in (0:ℝ)..2, C1 ^ 4 := hmono
      _ = C1 ^ 4 * 2 := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          ring
  have hsecond : (∫ t in (2:ℝ)..T, ‖riemannZeta ((1/2:ℂ) + (t:ℂ)*Complex.I)‖ ^ 4)
      ≤ 16 * C0 ^ 4 * (T + C2 * T * (Real.log T) ^ 4) := by
    have hstep1 : (∫ t in (2:ℝ)..T, ‖riemannZeta ((1/2:ℂ) + (t:ℂ)*Complex.I)‖ ^ 4)
        ≤ ∫ t in (2:ℝ)..T, 16 * C0 ^ 4 * (1 + ‖stepPoly M t‖ ^ 4) := by
      refine intervalIntegral.integral_mono_on (by linarith)
        (hcontζ.intervalIntegrable (2:ℝ) T)
        (((intervalIntegrable_const (c := (1:ℝ))).add
          (intervalIntegrable_stepPoly_pow_four M 2 T)).const_mul (16 * C0 ^ 4)) hpoint
    have hstep2 : (∫ t in (2:ℝ)..T, 16 * C0 ^ 4 * (1 + ‖stepPoly M t‖ ^ 4))
        = 16 * C0 ^ 4 * ∫ t in (2:ℝ)..T, (1 + ‖stepPoly M t‖ ^ 4) :=
      intervalIntegral.integral_const_mul _ _
    have hstep3 : (∫ t in (2:ℝ)..T, (1 + ‖stepPoly M t‖ ^ 4))
        = (T - 2) + ∫ t in (2:ℝ)..T, ‖stepPoly M t‖ ^ 4 := by
      rw [intervalIntegral.integral_add
        (intervalIntegrable_const (c := (1:ℝ))) (intervalIntegrable_stepPoly_pow_four M 2 T),
        intervalIntegral.integral_const]
      norm_num
    have hstep4 : (∫ t in (2:ℝ)..T, ‖stepPoly M t‖ ^ 4)
        ≤ ∫ t in (0:ℝ)..T, ‖stepPoly M t‖ ^ 4 := by
      have hadj : (∫ t in (0:ℝ)..T, ‖stepPoly M t‖ ^ 4)
          = (∫ t in (0:ℝ)..2, ‖stepPoly M t‖ ^ 4)
            + (∫ t in (2:ℝ)..T, ‖stepPoly M t‖ ^ 4) :=
        (intervalIntegral.integral_add_adjacent_intervals
          (intervalIntegrable_stepPoly_pow_four M 0 2)
          (intervalIntegrable_stepPoly_pow_four M 2 T)).symm
      have hnn : 0 ≤ ∫ t in (0:ℝ)..2, ‖stepPoly M t‖ ^ 4 :=
        intervalIntegral.integral_nonneg (by norm_num) (fun t _ => by positivity)
      linarith
    have hstep5 : (∫ t in (0:ℝ)..T, ‖stepPoly M t‖ ^ 4) ≤ C2 * T * (Real.log T) ^ 4 :=
      hpoly T M hM1 hM4T hT
    calc (∫ t in (2:ℝ)..T, ‖riemannZeta ((1/2:ℂ) + (t:ℂ)*Complex.I)‖ ^ 4)
        ≤ ∫ t in (2:ℝ)..T, 16 * C0 ^ 4 * (1 + ‖stepPoly M t‖ ^ 4) := hstep1
      _ = 16 * C0 ^ 4 * ∫ t in (2:ℝ)..T, (1 + ‖stepPoly M t‖ ^ 4) := hstep2
      _ = 16 * C0 ^ 4 * ((T - 2) + ∫ t in (2:ℝ)..T, ‖stepPoly M t‖ ^ 4) := by rw [hstep3]
      _ ≤ 16 * C0 ^ 4 * (T + C2 * T * (Real.log T) ^ 4) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith [hstep4, hstep5]
  rw [hsplit]
  refine le_trans (add_le_add hfirst hsecond) ?_
  have hC0p : (0:ℝ) ≤ C0 ^ 4 := by positivity
  have hC1p : (0:ℝ) ≤ C1 ^ 4 := by positivity
  have hprod : (0:ℝ) ≤ T * ((Real.log T) ^ 4 - 0.0625) :=
    mul_nonneg hT0 (by linarith [hlog4])
  have e1 : C1 ^ 4 * 2 ≤ 16 * C1 ^ 4 * (T * (Real.log T) ^ 4) := by nlinarith [hC1p, hTlog]
  have e2 : 16 * C0 ^ 4 * T ≤ 256 * C0 ^ 4 * (T * (Real.log T) ^ 4) := by nlinarith [hC0p, hprod]
  have e3 : 16 * C0 ^ 4 * (C2 * T * (Real.log T) ^ 4)
      ≤ 16 * C0 ^ 4 * C2 * (T * (Real.log T) ^ 4) := le_of_eq (by ring)
  rw [show (256 * C0 ^ 4 + 16 * C1 ^ 4 + 16 * C0 ^ 4 * C2 + 16) * T * (Real.log T) ^ 4
      = (256 * C0 ^ 4 + 16 * C1 ^ 4 + 16 * C0 ^ 4 * C2 + 16) * (T * (Real.log T) ^ 4) from by
        ring]
  linarith [e1, e2, e3, hC0p, hC1p, hC2pos]

/-- The critical-line integrand is continuous. -/
private lemma zetaLine_continuous :
    Continuous (fun t : ℝ => ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 4) := by
  refine Continuous.pow ?_ 4
  refine Continuous.norm ?_
  refine continuous_iff_continuousAt.mpr (fun t => ?_)
  have hs : ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) ≠ 1 := by
    intro h
    have h2 := congrArg Complex.re h
    norm_num at h2
  exact ContinuousAt.comp ((differentiableAt_riemannZeta hs).continuousAt) (by fun_prop)

/-- The critical-line integrand is even: `‖ζ(1/2-it)‖ = ‖ζ(1/2+it)‖`. -/
private lemma zetaLine_even (t : ℝ) :
    ‖riemannZeta ((1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)‖ ^ 4
      = ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 4 := by
  have h : ((1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)
      = (starRingEnd ℂ) ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) := by
    apply Complex.ext <;> simp [Complex.conj_ofReal]
  rw [h, riemannZeta_conj, Complex.norm_conj]

theorem zetaFourthSymm : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
    (∫ t in (-T)..T, ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 4)
      ≤ C * T * (Real.log T) ^ 4 := by
  obtain ⟨C0, hC0pos, hC0⟩ := zetaFourthMomentCleanAux
  refine ⟨2 * C0, by positivity, ?_⟩
  intro T hT
  let F : ℝ → ℝ := fun t => ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 4
  have hFcont : Continuous F := zetaLine_continuous
  have hFeven : ∀ t, F (-t) = F t := fun t => zetaLine_even t
  have hleft : IntervalIntegrable F volume (-T) 0 := hFcont.intervalIntegrable _ _
  have hright : IntervalIntegrable F volume 0 T := hFcont.intervalIntegrable _ _
  have hneg : (∫ x in (-T)..0, F x) = (∫ x in 0..T, F x) := by
    have heq : (∫ x in (-T)..0, F (-x)) = (∫ x in (-T)..0, F x) :=
      intervalIntegral.integral_congr (fun x _ => hFeven x)
    rw [← heq, intervalIntegral.integral_comp_neg (a := -T) (b := 0) F]
    simp
  have hsum := intervalIntegral.integral_add_adjacent_intervals hleft hright
  have hsym : (∫ x in (-T)..T, F x) = 2 * (∫ x in 0..T, F x) := by
    rw [← hsum, hneg]; ring
  change (∫ x in (-T)..T, F x) ≤ (2 * C0) * T * (Real.log T) ^ 4
  rw [hsym]
  have hC' : (∫ x in 0..T, F x) ≤ C0 * T * (Real.log T) ^ 4 := hC0 T hT
  calc 2 * (∫ x in 0..T, F x) ≤ 2 * (C0 * T * (Real.log T) ^ 4) := by linarith
    _ = (2 * C0) * T * (Real.log T) ^ 4 := by ring

end Work.ZeroDensity.Ingham
