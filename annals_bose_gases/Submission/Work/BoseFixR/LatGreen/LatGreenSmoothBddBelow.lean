import Mathlib.Tactic.Have
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseFixR.LatGreen.PeriodIntegrable
import Submission.Work.BoseFixR.LatGreen.heatK3_head_le
import Submission.Work.BoseFixR.LatGreen.heatK3_tail_ge
import Submission.Work.BoseFixR.LatGreen.tailIntegral_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open scoped Real BigOperators
open MeasureTheory Set

namespace Work.BoseFixR.LatGreen

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## Auxiliary estimates

The main theorem below is proved by the Ewald splitting at `η = 1/10` of the theta-integral
representation of `latGreen`.  Two estimates are needed that do not exist yet in the workspace:

* `tail_abs_le_ten` : the *two-sided* far-time bound `∫_{t > 1/10} |heatPeriod t u − 1| ≤ 1/250`,
  obtained by running the proof of `tailIntegral_le` against the absolute-value majorant
  `3ρ + 3ρ² + ρ³` of `md_tail_pointwise` (which is two-sided), unchanged;
* `heatK3_tail_upper_aux` : the *uniform* crude upper bound
  `∫_{t > η} heatK3 t u ≤ 1/(4π^{3/2}√η)` (drop the Gaussian factor, integrate `(4πt)^{−3/2}`). -/

/-- **Two-sided far-time bound.**  For every `u`, the mean-zero periodised heat kernel has total
variation at most `1/250` on `t > 1/10`:
`∫_{t > 1/10} |heatPeriod t u − 1| ≤ 1/250`.  (Same proof as `tailIntegral_le`: the pointwise
majorant `3ρ + 3ρ² + ρ³` is already a bound on the absolute value.) -/
theorem tail_abs_le_ten (u : ℝ³) :
    ∫ t in Ioi (1 / 10), |heatPeriod t u - 1| ≤ 1 / 250 := by
  set η : ℝ := 1 / 10 with hη
  set a : ℝ := 4 * Real.pi ^ 2 with ha
  set R : ℝ := 25 / 594 with hR
  have hηpos : (0 : ℝ) < η := by rw [hη]; norm_num
  have hηetaZ : etaZ ≤ η := by rw [hη, etaZ]; norm_num
  have hapos : (0 : ℝ) < a := by rw [ha]; positivity
  have ha39 : (39 : ℝ) ≤ a := by rw [ha]; nlinarith [Real.pi_gt_d2, Real.pi_pos]
  have hSZη : SZ η ≤ 25 / 1188 := by rw [hη]; exact SZ_ten_le
  -- the Fourier tail decays exponentially from the splitting time
  have hrho : ∀ t : ℝ, η ≤ t → rhoZ t ≤ Real.exp (-(a * (t - η))) * R := by
    intro t ht
    have h1 : SZ t ≤ Real.exp (-(a * (t - η))) * SZ η := by
      have h := SZDecay hηpos ht
      rwa [← ha] at h
    have h2 : (2 : ℝ) * SZ η ≤ R := by rw [hR]; linarith
    calc rhoZ t = 2 * SZ t := rfl
      _ ≤ 2 * (Real.exp (-(a * (t - η))) * SZ η) := by linarith
      _ = Real.exp (-(a * (t - η))) * (2 * SZ η) := by ring
      _ ≤ Real.exp (-(a * (t - η))) * R := mul_le_mul_of_nonneg_left h2 (Real.exp_nonneg _)
  -- the pointwise cubic majorant, two-sided
  have hbnd : ∀ t : ℝ, t ∈ Ioi η → |heatPeriod t u - 1| ≤ tailMajor a R η t := by
    intro t ht
    have htge : η ≤ t := le_of_lt ht
    have hpt : |heatPeriod t u - 1| ≤ 3 * rhoZ t + 3 * (rhoZ t) ^ 2 + (rhoZ t) ^ 3 :=
      md_tail_pointwise (le_trans hηetaZ htge) u
    have hρ0 : 0 ≤ rhoZ t := rhoZ_nonneg t
    have hdec := hrho t htge
    have hE2 : (Real.exp (-(a * (t - η)))) ^ 2 = Real.exp (-((2 * a) * (t - η))) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hE3 : (Real.exp (-(a * (t - η)))) ^ 3 = Real.exp (-((3 * a) * (t - η))) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hp2 := pow_le_pow_left₀ hρ0 hdec 2
    have hp3 := pow_le_pow_left₀ hρ0 hdec 3
    rw [mul_pow, hE2] at hp2
    rw [mul_pow, hE3] at hp3
    simp only [tailMajor]
    nlinarith [hp2, hp3, hdec]
  -- integration
  have hint : IntegrableOn (fun t : ℝ => |heatPeriod t u - 1|) (Ioi η) :=
    ((md_integrableOn_tail u).mono_set (Ioi_subset_Ioi hηetaZ)).abs
  have hGint : IntegrableOn (fun t : ℝ => tailMajor a R η t) (Ioi η) :=
    integrableOn_tailMajor hapos
  have hle_ae : (fun t : ℝ => |heatPeriod t u - 1|) ≤ᵐ[volume.restrict (Ioi η)]
      (fun t : ℝ => tailMajor a R η t) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact hbnd t ht
  have hmono := integral_mono_ae hint hGint hle_ae
  have hGval : ∫ t in Ioi η, tailMajor a R η t
      = 3 * R / a + 3 * R ^ 2 / (2 * a) + R ^ 3 / (3 * a) := integral_tailMajor hapos
  have harith : 3 * R / a + 3 * R ^ 2 / (2 * a) + R ^ 3 / (3 * a) ≤ 1 / 250 := by
    rw [hR]
    exact tailMajor_arith_ten ha39
  calc ∫ t in Ioi (1 / 10), |heatPeriod t u - 1|
      = ∫ t in Ioi η, |heatPeriod t u - 1| := by rw [← hη]
    _ ≤ ∫ t in Ioi η, tailMajor a R η t := hmono
    _ = 3 * R / a + 3 * R ^ 2 / (2 * a) + R ^ 3 / (3 * a) := hGval
    _ ≤ 1 / 250 := harith

/-- **Crude uniform heat-kernel tail bound.**  For `η > 0` and every `u`,
`∫_{t > η} heatK3 t u ≤ 1/(4π^{3/2}√η)`: the Gaussian factor is at most `1`, and
`∫_{t > η} (4πt)^{−3/2} dt = 1/(4π^{3/2}√η)`. -/
theorem heatK3_tail_upper_aux {η : ℝ} (hη : 0 < η) (u : ℝ³) :
    ∫ t in Ioi η, heatK3 t u ≤ 1 / (4 * Real.pi ^ (3 / 2 : ℝ) * Real.sqrt η) := by
  set a : ℝ := ‖u‖ ^ 2 / 4 with ha
  have han : 0 ≤ a := by rw [ha]; positivity
  have hint : IntegrableOn (fun t : ℝ => heatK3 t u) (Ioi η) := by
    refine (heatK3_tail_integrable han hη).congr_fun ?_ measurableSet_Ioi
    intro t ht
    simp only [heatK3, ha]
    congr 1
    congr 1
    ring_nf
  have hg : IntegrableOn (fun t : ℝ => (4 * Real.pi * t) ^ (-(3 / 2 : ℝ))) (Ioi η) := by
    have h := heatK3_tail_integrable (a := 0) le_rfl hη
    simpa using h
  have hpoint : ∀ t ∈ Ioi η, heatK3 t u ≤ (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) := by
    intro t ht
    have ht0 : 0 < t := hη.trans ht
    have h4 : (0 : ℝ) < 4 * Real.pi * t := by positivity
    have hexp : Real.exp (-‖u‖ ^ 2 / (4 * t)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      rw [show -‖u‖ ^ 2 / (4 * t) = -(‖u‖ ^ 2 / (4 * t)) by ring]
      exact neg_nonpos.mpr (div_nonneg (sq_nonneg _) (by positivity))
    rw [heatK3]
    nlinarith [Real.rpow_nonneg h4.le (-(3 / 2 : ℝ)), hexp]
  have hmono : (∫ t in Ioi η, heatK3 t u)
      ≤ ∫ t in Ioi η, (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) :=
    integral_mono_ae hint hg (by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact hpoint t ht)
  have hval : ∫ t in Ioi η, (4 * Real.pi * t) ^ (-(3 / 2 : ℝ))
      = 1 / (4 * Real.pi ^ (3 / 2 : ℝ) * Real.sqrt η) := by
    have h4π : (0 : ℝ) < 4 * Real.pi := by positivity
    have hcongr : ∫ t in Ioi η, (4 * Real.pi * t) ^ (-(3 / 2 : ℝ))
        = ∫ t in Ioi η, (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * t ^ (-(3 / 2 : ℝ)) :=
      setIntegral_congr_fun measurableSet_Ioi (fun t ht => by
        rw [Real.mul_rpow h4π.le (le_of_lt (hη.trans ht))])
    have hpow : ∫ t in Ioi η, t ^ (-(3 / 2 : ℝ)) = 2 * η ^ (-(1 / 2 : ℝ)) := by
      rw [integral_Ioi_rpow_of_lt (by norm_num : (-(3 / 2 : ℝ)) < -1) hη]
      rw [show (-(3 / 2 : ℝ) + 1) = -(1 / 2 : ℝ) by norm_num]
      ring
    rw [hcongr, integral_const_mul, hpow, four_pi_rpow_neg_three_halves]
    have hηr : η ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt η := by
      rw [Real.sqrt_eq_rpow, Real.rpow_neg hη.le]
      norm_num
    rw [hηr]
    have hb : (0 : ℝ) < Real.pi ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos Real.pi_pos _
    have hc : (0 : ℝ) < Real.sqrt η := Real.sqrt_pos.mpr hη
    field_simp
    ring
  linarith [hmono, hval.le, hval.ge]

/-- **`latGreenSmooth` is bounded below off the lattice** (piece of
`Work.BoseFixR.LatGreen.LatGreenParsevalB`).

With `latGreen u = ∫_0^∞ (heatPeriod t u − 1) dt` and `latGreenSmooth u = latGreen u − 1/(4π‖u‖)`,
there is `M` with `−M ≤ latGreenSmooth u` for every `u` that is not a lattice vector.

This is the one-sided companion of the already proved `madelung_smooth_nonpos`
(`latGreenSmooth ≤ 0` on the Voronoi cell) and turns the Coulomb-type bound on the periodic
kernel `K_♯(z) = ℓ²·latGreen(ℓ⁻¹z)` into a *lower* bound, which the absolutely integrable
hypothesis **(B)** of the target then controls.

Route (Ewald split at `η = 1/10`, uniform in `u`, `u` off-lattice).  With
`latGreenSmooth u = ∫_0^η (heatPeriod t u − heatK3 t u) dt − η + ∫_η^∞ (heatPeriod t u − 1) dt
   − ∫_η^∞ heatK3 t u dt`, which holds because `∫_0^∞ heatK3 t u dt = 1/(4π‖u‖)` (`HeatIntegral`),
`∫_0^η = ∫_0^∞ − ∫_η^∞` and `∫_0^η 1 dt = η`:

* the first term is `≥ 0`: `heatPeriod t u = Σ_n heatK3 t (u − n) ≥ heatK3 t u` (all terms
  nonnegative); it is integrable on `(0,η]` by `heatPeriod_le_small` (`PeriodIntegrable`);
* the third term is `≥ −1/250`: the `tailIntegral_le` majorant `3ρ + 3ρ² + ρ³` bounds
  `|heatPeriod t u − 1|` for `t ≥ 1/10`, so the same proof gives the two-sided bound;
* the fourth term is at most `1/(4π^{3/2}√η)`: bound
  `∫_η^∞ (4πt)^{−3/2}e^{−a/t}dt ≤ ∫_η^∞ (4πt)^{−3/2}dt = 1/(4π^{3/2}√η)`, valid uniformly in
  `u` (`heatK3_tail_bound` is *not* uniform near `u = 0`, so use this crude bound, or
  `heatK3_tail_ge` for the reverse direction).

So `latGreenSmooth u ≥ −1/10 − 1/250 − 0.15 ≥ −0.3`; take `M = 1/2`. -/
theorem LatGreenSmoothBddBelow :
    ∃ M : ℝ, ∀ u : EuclideanSpace ℝ (Fin 3),
      (∀ n : Fin 3 → ℤ, u ≠ Work.BoseFixR.LatGreen.latVec n) →
        -M ≤ Work.BoseFixR.LatGreen.latGreenSmooth u := by
  refine ⟨1 / 2, fun u hu => ?_⟩
  set η : ℝ := 1 / 10 with hηdef
  have hη : (0 : ℝ) < η := by rw [hηdef]; norm_num
  have hη1 : η ≤ 1 := by rw [hηdef]; norm_num
  have hlat0 : latVec (0 : Fin 3 → ℤ) = (0 : ℝ³) := by
    ext i; simp [latVec]
  have hu0 : u ≠ 0 := by
    intro h
    exact hu 0 (by rw [h, hlat0])
  -- ## Integrability bookkeeping
  have hInt : IntegrableOn (fun t : ℝ => heatPeriod t u - 1) (Ioi 0) := PeriodIntegrable hu
  have hsmall_int : IntegrableOn (fun t : ℝ => heatPeriod t u - 1) (Ioc 0 η) :=
    hInt.mono_set Ioc_subset_Ioi_self
  have htail_int : IntegrableOn (fun t : ℝ => heatPeriod t u - 1) (Ioi η) :=
    hInt.mono_set (Ioi_subset_Ioi hη.le)
  have hK0 : IntegrableOn (fun t : ℝ => heatK3 t u) (Ioi 0) :=
    md_integrableOn_heatK3_Ioi u hu0
  have hKsmall : IntegrableOn (fun t : ℝ => heatK3 t u) (Ioc 0 η) :=
    hK0.mono_set Ioc_subset_Ioi_self
  have hKtail : IntegrableOn (fun t : ℝ => heatK3 t u) (Ioi η) :=
    hK0.mono_set (Ioi_subset_Ioi hη.le)
  have h1int : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc 0 η) :=
    integrableOn_const (by rw [Real.volume_Ioc]; simp)
  have hHPsmall : IntegrableOn (fun t : ℝ => heatPeriod t u) (Ioc 0 η) := by
    refine (hsmall_int.add h1int).congr_fun ?_ measurableSet_Ioc
    intro t ht
    simp only [Pi.add_apply]
    ring
  -- ## The split of `latGreen` at `η`
  have hsplit : latGreen u
      = (∫ t in Ioc 0 η, (heatPeriod t u - 1)) + ∫ t in Ioi η, (heatPeriod t u - 1) := by
    rw [latGreen, ← Set.Ioc_union_Ioi_eq_Ioi hη.le]
    rw [setIntegral_union (disjoint_left.mpr fun x hx => by
      simp only [Set.mem_Ioi, not_lt]
      exact hx.2) measurableSet_Ioi hsmall_int htail_int]
  -- ## The value of `1/(4π‖u‖)` as the full heat-kernel integral
  have hKsplit : 1 / (4 * Real.pi * ‖u‖)
      = (∫ t in Ioc 0 η, heatK3 t u) + ∫ t in Ioi η, heatK3 t u := by
    rw [← HeatIntegral hu0, ← Set.Ioc_union_Ioi_eq_Ioi hη.le]
    rw [setIntegral_union (disjoint_left.mpr fun x hx => by
      simp only [Set.mem_Ioi, not_lt]
      exact hx.2) measurableSet_Ioi hKsmall hKtail]
  -- ## The short-time algebra
  have hone : (∫ t in Ioc (0 : ℝ) η, (1 : ℝ)) = η := by
    rw [← intervalIntegral.integral_of_le hη.le, intervalIntegral.integral_const]
    simp
  have hAB : (∫ t in Ioc 0 η, heatPeriod t u)
      = (∫ t in Ioc 0 η, (heatPeriod t u - heatK3 t u)) + ∫ t in Ioc 0 η, heatK3 t u := by
    have hcongr : (fun t : ℝ => (heatPeriod t u - heatK3 t u) + heatK3 t u)
        = fun t : ℝ => heatPeriod t u := by
      funext t; ring
    calc (∫ t in Ioc 0 η, heatPeriod t u)
        = ∫ t in Ioc 0 η, ((heatPeriod t u - heatK3 t u) + heatK3 t u) := by rw [← hcongr]
      _ = (∫ t in Ioc 0 η, (heatPeriod t u - heatK3 t u)) + ∫ t in Ioc 0 η, heatK3 t u :=
          integral_add (hHPsmall.sub hKsmall) hKsmall
  have hsmallval : (∫ t in Ioc 0 η, (heatPeriod t u - 1))
      = (∫ t in Ioc 0 η, (heatPeriod t u - heatK3 t u)) + (∫ t in Ioc 0 η, heatK3 t u) - η := by
    rw [integral_sub hHPsmall h1int, hone, hAB]
  -- ## The three estimates
  have hA : 0 ≤ ∫ t in Ioc 0 η, (heatPeriod t u - heatK3 t u) := by
    rw [integral_sub hHPsmall hKsmall]
    have hmono : (∫ t in Ioc 0 η, heatK3 t u) ≤ ∫ t in Ioc 0 η, heatPeriod t u :=
      integral_mono_ae hKsmall hHPsmall (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact md_heatPeriod_ge_heatK3 ht.1 u)
    linarith
  have htail_lb : -(1 / 250 : ℝ) ≤ ∫ t in Ioi η, (heatPeriod t u - 1) := by
    have hb : (∫ t in Ioi η, |heatPeriod t u - 1|) ≤ 1 / 250 := by
      rw [hηdef]
      exact tail_abs_le_ten u
    have h2 := norm_integral_le_integral_norm (μ := volume.restrict (Ioi η))
      (f := fun t : ℝ => heatPeriod t u - 1)
    simp only [Real.norm_eq_abs] at h2
    linarith [neg_abs_le (∫ t in Ioi η, (heatPeriod t u - 1)), h2, hb]
  have hKtail_ub : (∫ t in Ioi η, heatK3 t u) ≤ 1 / (4 * Real.pi ^ (3 / 2 : ℝ) * Real.sqrt η) :=
    heatK3_tail_upper_aux hη u
  -- ## Numerical finish
  have harith : -(1 / 2 : ℝ) ≤ -η - 1 / (4 * Real.pi ^ (3 / 2 : ℝ) * Real.sqrt η) - 1 / 250 := by
    rw [hηdef]
    have hπ : (3 : ℝ) ^ (3 / 2 : ℝ) ≤ Real.pi ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) Real.pi_gt_three.le (by norm_num)
    have h3 : (3 : ℝ) ^ (3 / 2 : ℝ) = 3 * Real.sqrt 3 := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by norm_num),
        Real.rpow_one, Real.sqrt_eq_rpow]
    have hπ' : 3 * Real.sqrt 3 ≤ Real.pi ^ (3 / 2 : ℝ) := by
      rw [← h3]; exact hπ
    have hs : (1 : ℝ) / (2 * Real.sqrt 3) ≤ Real.sqrt (1 / 10) := by
      have hsq : ((1 : ℝ) / (2 * Real.sqrt 3)) ^ 2 ≤ 1 / 10 := by
        rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
        norm_num
      calc (1 : ℝ) / (2 * Real.sqrt 3)
          = Real.sqrt (((1 : ℝ) / (2 * Real.sqrt 3)) ^ 2) :=
            (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt (1 / 10) := Real.sqrt_le_sqrt hsq
    have hprod : (3 : ℝ) / 2 ≤ Real.pi ^ (3 / 2 : ℝ) * Real.sqrt (1 / 10) := by
      have h1 : 3 * Real.sqrt 3 * (1 / (2 * Real.sqrt 3))
          ≤ Real.pi ^ (3 / 2 : ℝ) * Real.sqrt (1 / 10) :=
        mul_le_mul hπ' hs (by positivity) (by positivity)
      have h2 : 3 * Real.sqrt 3 * (1 / (2 * Real.sqrt 3)) = 3 / 2 := by
        field_simp
      linarith [h1, h2.le, h2.ge]
    have hkey : (6 : ℝ) ≤ 4 * Real.pi ^ (3 / 2 : ℝ) * Real.sqrt (1 / 10) := by
      linarith [hprod]
    have hb : 1 / (4 * Real.pi ^ (3 / 2 : ℝ) * Real.sqrt (1 / 10)) ≤ 1 / 6 :=
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 6) hkey
    linarith [hb]
  rw [latGreenSmooth, hsplit, hsmallval, hKsplit]
  linarith [hA, hKtail_ub, htail_lb, harith]

end Work.BoseFixR.LatGreen
