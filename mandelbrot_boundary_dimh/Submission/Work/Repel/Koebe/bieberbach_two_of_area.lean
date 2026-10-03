import Mathlib
import Submission.Work.Repel.Koebe.area_theorem
import Submission.Work.Escape.exists_differentiableOn_ball_clog

/-!
# Bieberbach's second coefficient inequality from Grönwall's area theorem

This file derives `‖f''(0)‖ ≤ 4` for a univalent normalized function on the unit disc from the
first-coefficient form of Grönwall's area inequality (taken as the hypothesis `harea`).

The classical argument is applied to the odd exterior function `ψ(w) = 1/√(f(w⁻²))`.  Since the
exterior `{1 < ‖w‖}` is not simply connected, we build `ψ` by descending from the disc: `f`
factors uniquely as `f(z) = z · F(z)` with `F` holomorphic and non-vanishing on the disc, and a
holomorphic square root `P` of `1/F` (with `P 0 = 1`) exists because the disc is simply connected.
Then `ψ(w) = w · P(w⁻²)` is odd, univalent on the exterior, and has Laurent coefficient
`-F'(0)/2 = -f''(0)/4` at `1/w`; the area inequality gives `‖f''(0)/4‖ ≤ 1`.
-/

open Filter Topology Metric
open scoped Topology

namespace Work.Repel.Koebe

/-- Factorization of an analytic function vanishing at the origin: `f z = z * F z` globally, with
`F` analytic at `0`.  (Taylor's theorem with remainder at order `1`.) -/
theorem exists_factor_of_analyticAt {f : ℂ → ℂ} (han : AnalyticAt ℂ f 0) (h0 : f 0 = 0) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F 0 ∧ ∀ z, f z = z * F z := by
  obtain ⟨F, hFan, hF⟩ := AnalyticAt.exists_eq_sum_add_pow_mul han 1
  refine ⟨F, hFan, fun z => ?_⟩
  have hsum : (∑ i ∈ Finset.range 1, (z ^ i / ((i.factorial : ℕ) : ℂ)) • iteratedDeriv i f 0) = 0 := by
    simp [h0]
  rw [hF z, hsum, zero_add]
  simp [smul_eq_mul]

/-- Derivative at the origin of `z ↦ z * F z`. -/
theorem deriv_mul_id {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) :
    deriv (fun z : ℂ => z * F z) 0 = F 0 := by
  have h := deriv_fun_mul (c := (fun z : ℂ => z)) (d := F) differentiableAt_id hF.differentiableAt
  simpa [deriv_id] using h

/-- Second derivative at the origin of `z ↦ z * F z`. -/
theorem iteratedDeriv_two_mul {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) :
    iteratedDeriv 2 (fun z : ℂ => z * F z) 0 = 2 * deriv F 0 := by
  have hev : deriv (fun z : ℂ => z * F z) =ᶠ[𝓝 (0:ℂ)] fun z => F z + z * deriv F z := by
    filter_upwards [hF.eventually_analyticAt] with z hz
    have h := deriv_fun_mul (c := (fun z : ℂ => z)) (d := F) differentiableAt_id hz.differentiableAt
    simpa [deriv_id] using h
  have hstep : iteratedDeriv 2 (fun z : ℂ => z * F z) 0
      = deriv (fun z : ℂ => F z + z * deriv F z) 0 := by
    rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    exact EventuallyEq.deriv_eq hev
  rw [hstep]
  have hgderiv : deriv (fun z : ℂ => z * deriv F z) 0 = deriv F 0 := by
    have h := deriv_fun_mul (c := (fun z : ℂ => z)) (d := deriv F) differentiableAt_id
      hF.deriv.differentiableAt
    simpa [deriv_id] using h
  have hsum : deriv (fun z : ℂ => F z + z * deriv F z) 0 = deriv F 0 + deriv F 0 := by
    have h' : (fun z : ℂ => F z + z * deriv F z) = F + (fun z : ℂ => z * deriv F z) := rfl
    rw [h']
    have hg2 : DifferentiableAt ℂ (fun z : ℂ => z * deriv F z) 0 :=
      differentiableAt_id.mul hF.deriv.differentiableAt
    rw [deriv_add (f := F) (g := fun z : ℂ => z * deriv F z) hF.differentiableAt hg2, hgderiv]
  rw [hsum]
  ring

/-- The relation `P'(0) = -F'(0)/2` obtained by differentiating `P² = 1/F` at the origin. -/
theorem deriv_eq_neg_deriv_div_two {F P : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) (hP : AnalyticAt ℂ P 0)
    (hF0 : F 0 = 1) (hP0 : P 0 = 1)
    (hsq : ∀ᶠ z in 𝓝 (0:ℂ), P z ^ 2 = (F z)⁻¹) :
    deriv P 0 = -deriv F 0 / 2 := by
  have h1 : deriv (fun z : ℂ => P z ^ 2) 0 = deriv (fun z : ℂ => (F z)⁻¹) 0 :=
    EventuallyEq.deriv_eq hsq
  have hl : deriv (fun z : ℂ => P z ^ 2) 0 = 2 * deriv P 0 := by
    rw [show (fun z : ℂ => P z ^ 2) = P ^ 2 from rfl, deriv_pow hP.differentiableAt 2, hP0]
    norm_num
  have hr : deriv (fun z : ℂ => (F z)⁻¹) 0 = -deriv F 0 := by
    have hd : HasDerivAt (fun z : ℂ => (F z)⁻¹) (-deriv F 0 / (F 0)^2) 0 :=
      (hF.hasStrictDerivAt.hasDerivAt).inv (by rw [hF0]; norm_num)
    rw [hd.deriv, hF0]
    norm_num
  rw [hl, hr] at h1
  rw [← h1]
  ring

/-- Injectivity of the exterior function `w ↦ w * P(w⁻¹²)` on `{1 < ‖w‖}`. -/
theorem injOn_w_mul_of_sq_eq_inv {f F P : ℂ → ℂ}
    (hFfac : ∀ z, f z = z * F z)
    (hPsq : ∀ z ∈ Metric.ball (0 : ℂ) 1, P z ^ 2 = (F z)⁻¹)
    (hinj : Set.InjOn f (Metric.ball (0 : ℂ) 1))
    (hPne : ∀ z ∈ Metric.ball (0 : ℂ) 1, P z ≠ 0) :
    Set.InjOn (fun w : ℂ => w * P (w⁻¹ ^ 2)) {w : ℂ | 1 < ‖w‖} := by
  intro w1 h1 w2 h2 heq
  change w1 * P (w1⁻¹ ^ 2) = w2 * P (w2⁻¹ ^ 2) at heq
  have hw1 : w1 ≠ 0 := by
    intro h; rw [h] at h1; norm_num at h1
  have hw2 : w2 ≠ 0 := by
    intro h; rw [h] at h2; norm_num at h2
  have hb1 : w1⁻¹ ^ 2 ∈ Metric.ball (0:ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right, norm_pow, norm_inv]
    have hlt : ‖w1‖⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
    have hnn : (0:ℝ) ≤ ‖w1‖⁻¹ := inv_nonneg.mpr (norm_nonneg w1)
    nlinarith [hlt, hnn]
  have hb2 : w2⁻¹ ^ 2 ∈ Metric.ball (0:ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right, norm_pow, norm_inv]
    have hlt : ‖w2‖⁻¹ < 1 := inv_lt_one_of_one_lt₀ h2
    have hnn : (0:ℝ) ≤ ‖w2‖⁻¹ := inv_nonneg.mpr (norm_nonneg w2)
    nlinarith [hlt, hnn]
  have hkey : ∀ w : ℂ, w ≠ 0 → w^2 * (F (w⁻¹ ^ 2))⁻¹ = (f (w⁻¹ ^ 2))⁻¹ := by
    intro w hw
    rw [hFfac (w⁻¹^2), mul_inv, inv_pow w 2, inv_inv]
  have hsq : (f (w1⁻¹^2))⁻¹ = (f (w2⁻¹^2))⁻¹ := by
    have h2' : (w1 * P (w1⁻¹^2))^2 = (w2 * P (w2⁻¹^2))^2 := by rw [heq]
    rw [mul_pow, mul_pow, hPsq (w1⁻¹^2) hb1, hPsq (w2⁻¹^2) hb2] at h2'
    calc (f (w1⁻¹^2))⁻¹ = w1^2 * (F (w1⁻¹^2))⁻¹ := (hkey w1 hw1).symm
      _ = w2^2 * (F (w2⁻¹^2))⁻¹ := h2'
      _ = (f (w2⁻¹^2))⁻¹ := hkey w2 hw2
  have hfinj : f (w1⁻¹ ^ 2) = f (w2⁻¹ ^ 2) := by
    have := congrArg Inv.inv hsq
    rwa [inv_inv, inv_inv] at this
  have hww : w1⁻¹ ^ 2 = w2⁻¹ ^ 2 := hinj hb1 hb2 hfinj
  have hsq2 : w1^2 = w2^2 := by
    have := congrArg (fun t : ℂ => t⁻¹) hww
    simpa [inv_pow] using this
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq2 with h | h
  · exact h
  · exfalso
    -- `ψ` is odd, so `w1 = -w2` would force `ψ w1 = 0`, impossible on the exterior
    have hodd : w2 * P (w2⁻¹^2) = -(w1 * P (w1⁻¹^2)) := by
      have hw2eq : w2 = -w1 := by rw [h]; ring
      rw [hw2eq, show (-w1)⁻¹ ^ 2 = w1⁻¹ ^ 2 by rw [inv_neg, neg_sq]]
      ring
    have hne0 : w1 * P (w1⁻¹^2) ≠ 0 :=
      mul_ne_zero hw1 (hPne (w1⁻¹^2) hb1)
    have hgoal : w1 * P (w1⁻¹^2) = -(w1 * P (w1⁻¹^2)) := by
      calc w1 * P (w1⁻¹^2) = w2 * P (w2⁻¹^2) := heq
        _ = -(w1 * P (w1⁻¹^2)) := hodd
    have hz : w1 * P (w1⁻¹^2) = 0 := by
      have h2 := hgoal
      rw [eq_neg_iff_add_eq_zero] at h2
      have : (2:ℂ) * (w1 * P (w1⁻¹^2)) = 0 := by rw [two_mul]; exact h2
      exact (mul_eq_zero.mp this).resolve_left (by norm_num)
    exact hne0 hz

/-- Bieberbach's second coefficient inequality, derived from Grönwall's area inequality (taken
as a hypothesis).  The area inequality is applied to the odd exterior function `ψ(w) = 1/√(f(w⁻²))`,
whose Laurent coefficient at `1/w` is `-a₂/2`; hence `|a₂| ≤ 2`, i.e. `‖f''(0)‖ ≤ 4`. -/
theorem bieberbach_two_of_area
    (harea : ∀ {g : ℂ → ℂ} {b : ℂ}, (∀ z : ℂ, 1 < ‖z‖ → AnalyticAt ℂ g z) →
      Set.InjOn g {z : ℂ | 1 < ‖z‖} →
      Filter.Tendsto (fun u : ℂ => (g u⁻¹ - u⁻¹) / u) (nhdsWithin (0 : ℂ) ({0}ᶜ)) (nhds b) →
      ‖b‖ ≤ 1)
    {f : ℂ → ℂ} (han : ∀ z ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ f z)
    (hinj : Set.InjOn f (Metric.ball (0 : ℂ) 1)) (h0 : f 0 = 0) (h1 : deriv f 0 = 1) :
    ‖iteratedDeriv 2 f 0‖ ≤ 4 := by
  have h0mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp
  have han0 : AnalyticAt ℂ f 0 := han 0 h0mem
  -- factor `f z = z * F z`
  obtain ⟨F, hFan0, hFfac⟩ := exists_factor_of_analyticAt han0 h0
  have hfeq : f = fun z : ℂ => z * F z := funext hFfac
  have hF0 : F 0 = 1 := by
    have hd := deriv_mul_id hFan0
    rw [hfeq] at h1
    rw [hd] at h1
    exact h1
  have hFan_ball : ∀ z ∈ Metric.ball (0:ℂ) 1, AnalyticAt ℂ F z := by
    intro z hz
    rcases eq_or_ne z 0 with rfl | hzne
    · exact hFan0
    · have hane : AnalyticAt ℂ (fun w : ℂ => f w / w) z :=
        (han z hz).div (analyticAt_id (z := z)) hzne
      refine hane.congr ?_
      filter_upwards [eventually_ne_nhds hzne] with w hw
      rw [hFfac w, mul_div_cancel_left₀ (F w) hw]
  have hFne : ∀ z ∈ Metric.ball (0:ℂ) 1, F z ≠ 0 := by
    intro z hz
    rcases eq_or_ne z 0 with rfl | hzne
    · rw [hF0]; norm_num
    · intro hFz
      exact hzne (hinj hz h0mem (by rw [hFfac z, hFz, mul_zero, h0]))
  -- holomorphic square root `P` of `1/F` with `P 0 = 1`
  have hFdiff : DifferentiableOn ℂ F (Metric.ball (0:ℂ) 1) :=
    AnalyticOnNhd.differentiableOn (fun z hz => hFan_ball z hz)
  have hgdiff : DifferentiableOn ℂ (fun z : ℂ => (F z)⁻¹) (Metric.ball (0:ℂ) 1) :=
    hFdiff.inv hFne
  have hgne : ∀ z ∈ Metric.ball (0:ℂ) 1, (F z)⁻¹ ≠ 0 := fun z hz => inv_ne_zero (hFne z hz)
  obtain ⟨L, hLdiff, hLexp, -⟩ := Work.Escape.exists_differentiableOn_ball_clog hgdiff hgne
  set P : ℂ → ℂ := fun z => Complex.exp ((L z - L 0) / 2) with hPdef
  have hPdiff : DifferentiableOn ℂ P (Metric.ball (0:ℂ) 1) := by
    rw [hPdef]
    exact ((hLdiff.sub_const (L 0)).div_const 2).cexp
  have hP0 : P 0 = 1 := by
    simp [hPdef]
  have hPsq : ∀ z ∈ Metric.ball (0:ℂ) 1, P z ^ 2 = (F z)⁻¹ := by
    intro z hz
    have hLz : Complex.exp (L z) = (F z)⁻¹ := hLexp z hz
    have hL0 : Complex.exp (L 0) = (F 0)⁻¹ := hLexp 0 h0mem
    rw [hPdef]
    simp only
    rw [sq, ← Complex.exp_add,
      show (L z - L 0) / 2 + (L z - L 0) / 2 = L z - L 0 from by ring,
      Complex.exp_sub, hLz, hL0, hF0, inv_one, div_one]
  have hPan0 : AnalyticAt ℂ P 0 :=
    AnalyticOn.analyticAt (Metric.isOpen_ball.mem_nhds h0mem)
      (hPdiff.analyticOn Metric.isOpen_ball)
  have hPne : ∀ z ∈ Metric.ball (0:ℂ) 1, P z ≠ 0 := by
    intro z hz hPz
    have h2 := hPsq z hz
    rw [hPz, zero_pow (by norm_num : (2:ℕ) ≠ 0)] at h2
    exact hFne z hz (inv_eq_zero.mp h2.symm)
  -- the exterior function `ψ w = w * P (w⁻¹²)`
  have hψan : ∀ z : ℂ, 1 < ‖z‖ → AnalyticAt ℂ (fun w : ℂ => w * P (w⁻¹ ^ 2)) z := by
    intro w hw
    have hwne : w ≠ 0 := by
      intro h; rw [h] at hw; norm_num at hw
    have hmem : w⁻¹ ^ 2 ∈ Metric.ball (0:ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right, norm_pow, norm_inv]
      have hlt : ‖w‖⁻¹ < 1 := inv_lt_one_of_one_lt₀ hw
      have hnn : (0:ℝ) ≤ ‖w‖⁻¹ := inv_nonneg.mpr (norm_nonneg w)
      nlinarith [hlt, hnn]
    have hPan : AnalyticAt ℂ P (w⁻¹ ^ 2) :=
      AnalyticOn.analyticAt (Metric.isOpen_ball.mem_nhds hmem)
        (hPdiff.analyticOn Metric.isOpen_ball)
    have hinner : AnalyticAt ℂ (fun w : ℂ => w⁻¹ ^ 2) w :=
      ((analyticAt_id (z := w)).inv hwne).pow 2
    have hcomp : AnalyticAt ℂ (fun w : ℂ => P (w⁻¹ ^ 2)) w :=
      AnalyticAt.comp (f := (fun w : ℂ => w⁻¹ ^ 2)) hPan hinner
    have hres : AnalyticAt ℂ (fun w : ℂ => w * P (w⁻¹ ^ 2)) w :=
      AnalyticAt.mul (analyticAt_id (z := w)) hcomp
    exact hres
  have hψinj : Set.InjOn (fun w : ℂ => w * P (w⁻¹ ^ 2)) {w : ℂ | 1 < ‖w‖} :=
    injOn_w_mul_of_sq_eq_inv hFfac hPsq hinj hPne
  -- the Laurent coefficient at `1/w` of `ψ` is `P'(0)`
  have hpt : ∀ u : ℂ, slope P 0 (u^2) = ((fun w : ℂ => w * P (w⁻¹^2)) u⁻¹ - u⁻¹) / u := by
    intro u
    simp only [slope, vsub_eq_sub, smul_eq_mul, inv_inv]
    rw [hP0, sub_zero]
    rw [show (u^2)⁻¹ = u⁻¹ * u⁻¹ by rw [← inv_pow, ← pow_two]]
    ring
  have hψlim : Tendsto (fun u : ℂ => ((fun w : ℂ => w * P (w⁻¹^2)) u⁻¹ - u⁻¹) / u)
      (nhdsWithin (0:ℂ) ({0}ᶜ)) (nhds (deriv P 0)) := by
    have hslope : Tendsto (slope P 0) (nhdsWithin (0:ℂ) ({0}ᶜ)) (nhds (deriv P 0)) :=
      hPan0.hasStrictDerivAt.hasDerivAt.tendsto_slope
    have hsqu : Tendsto (fun u : ℂ => u^2) (nhdsWithin (0:ℂ) ({0}ᶜ)) (nhdsWithin (0:ℂ) ({0}ᶜ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have hcont : Continuous (fun u : ℂ => u^2) := continuous_id.pow 2
        have h := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (a := (0:ℂ)) (s := {0}ᶜ))
        simpa using h
      · filter_upwards [self_mem_nhdsWithin] with u hu
        exact pow_ne_zero 2 hu
    exact (hslope.comp hsqu).congr hpt
  have hB : ‖deriv P 0‖ ≤ 1 := harea hψan hψinj hψlim
  have hderivrel : deriv P 0 = -deriv F 0 / 2 :=
    deriv_eq_neg_deriv_div_two hFan0 hPan0 hF0 hP0
      (by filter_upwards [Metric.isOpen_ball.mem_nhds h0mem] with z hz; exact hPsq z hz)
  have hit : iteratedDeriv 2 f 0 = 2 * deriv F 0 := by
    rw [hfeq]
    exact iteratedDeriv_two_mul hFan0
  have hF' : ‖deriv F 0‖ = 2 * ‖deriv P 0‖ := by
    have h2 : deriv F 0 = (-2 : ℂ) * deriv P 0 := by rw [hderivrel]; ring
    rw [h2, norm_mul, show ‖(-2:ℂ)‖ = 2 from by norm_num]
  rw [hit, norm_mul, show ‖(2:ℂ)‖ = 2 from by norm_num, hF']
  linarith [hB]

end Work.Repel.Koebe
