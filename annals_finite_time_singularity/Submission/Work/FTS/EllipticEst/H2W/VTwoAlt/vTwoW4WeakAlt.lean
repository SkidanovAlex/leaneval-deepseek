import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.Tactic.Have
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.remov.interval_integral_sq_le_mul
import Submission.Work.FTS.EllipticEst.remov.slice5_rel

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.VTwoAlt

open MeasureTheory Set Filter
open scoped Real Topology Interval

set_option maxHeartbeats 1000000

/-! ## Elementary trigonometric facts -/

lemma sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

lemma sEta_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  exact Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _

lemma one_le_sEta_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.sEta θ := by
  have h2θ : 0 < 2 * θ := by linarith [hθ.1]
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi h2θ (by linarith [hθ.2, Real.pi_pos])
  have h1 : (Real.sin (2 * θ)) ^ Work.Spaces.eta ≤ 1 :=
    Real.rpow_le_one hs.le (Real.sin_le_one _) (le_of_lt Work.Spaces.eta_pos)
  have hpos : 0 < (Real.sin (2 * θ)) ^ Work.Spaces.eta := Real.rpow_pos_of_pos hs _
  rw [Work.FTS.EllipticEst.sEta, Real.rpow_neg hs.le]
  exact (one_le_inv₀ hpos).mpr h1

lemma cos_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < Real.cos θ :=
  Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩

lemma cos_le_sub {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.cos θ ≤ Real.pi / 2 - θ := by
  have h := Real.sin_le (x := Real.pi / 2 - θ) (by linarith [hθ.2])
  rwa [Real.sin_pi_div_two_sub] at h

lemma two_div_pi_mul_sub_le_cos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    2 / Real.pi * (Real.pi / 2 - θ) ≤ Real.cos θ := by
  have h := Real.mul_le_sin (x := Real.pi / 2 - θ) (by linarith [hθ.2]) (by linarith [hθ.1])
  rwa [Real.sin_pi_div_two_sub] at h

lemma sin_two_eq_sin_two_sub {θ : ℝ} :
    Real.sin (2 * θ) = Real.sin (2 * (Real.pi / 2 - θ)) := by
  rw [show 2 * θ = Real.pi - 2 * (Real.pi / 2 - θ) by ring, Real.sin_pi_sub]

lemma sin_le_two_sub {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.sin (2 * θ) ≤ 2 * (Real.pi / 2 - θ) := by
  rw [sin_two_eq_sin_two_sub]
  exact Real.sin_le (by linarith [hθ.2])

lemma two_div_pi_mul_le_sin_sub {θ : ℝ} (hθ : θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2)) :
    2 / Real.pi * (2 * (Real.pi / 2 - θ)) ≤ Real.sin (2 * θ) := by
  rw [sin_two_eq_sin_two_sub]
  exact Real.mul_le_sin (by linarith [hθ.2]) (by linarith [hθ.1])

/-! ## The weighted Hardy (Agmon) inequality

With `y = π/2 - θ` we prove `(2+γ) ∫ G²y^{-4-γ} ≤ ∫ (G')²y^{-2-γ}` on `(θ₀,π/2)`,
assuming only the *finiteness* of the left integral (and of the right one, so that the
statement is not vacuous). -/

/-- The weighted flux `G² y^{-3-γ}` whose derivative is the sum of the two weights. -/
noncomputable def agFlux (γ : ℝ) (G : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => G θ ^ 2 * (Real.pi / 2 - θ) ^ (-3 - γ)

/-- The derivative of `agFlux`. -/
noncomputable def agFluxDeriv (γ : ℝ) (G : ℝ → ℝ) : ℝ → ℝ := fun θ =>
  2 * G θ * deriv G θ * (Real.pi / 2 - θ) ^ (-3 - γ)
    + G θ ^ 2 * ((3 + γ) * (Real.pi / 2 - θ) ^ (-4 - γ))

/-- The left integrand `G² y^{-4-γ}`. -/
noncomputable def agF (γ : ℝ) (G : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => G θ ^ 2 * (Real.pi / 2 - θ) ^ (-4 - γ)

/-- The right integrand `(G')² y^{-2-γ}`. -/
noncomputable def agFd (γ : ℝ) (G : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => (deriv G θ) ^ 2 * (Real.pi / 2 - θ) ^ (-2 - γ)

lemma agF_nonneg (γ : ℝ) (G : ℝ → ℝ) {θ : ℝ} (hθ : θ < Real.pi / 2) :
    0 ≤ agF γ G θ := by
  rw [agF]
  exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by linarith) _)

lemma agFd_nonneg (γ : ℝ) (G : ℝ → ℝ) {θ : ℝ} (hθ : θ < Real.pi / 2) :
    0 ≤ agFd γ G θ := by
  rw [agFd]
  exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by linarith) _)

lemma agFlux_nonneg (γ : ℝ) (G : ℝ → ℝ) {θ : ℝ} (hθ : θ < Real.pi / 2) :
    0 ≤ agFlux γ G θ := by
  rw [agFlux]
  exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by linarith) _)

/-- The Agmon inequality on a compact subinterval `[a,t]`, `θ₀ < a ≤ t < π/2`, without any
integrability hypothesis (all integrands are continuous on `[a,t]`):

  `(2+γ) ∫_a^t G²y^{-4-γ} ≤ (G t)²y_t^{-3-γ} + ∫_a^t (G')²y^{-2-γ}`. -/
lemma agmon_interval (γ θ₀ : ℝ) (hγ1 : 1 ≤ γ) {G : ℝ → ℝ}
    (hG : ContDiffOn ℝ 1 G (Set.Ioo θ₀ (Real.pi / 2)))
    {a t : ℝ} (ha : θ₀ < a) (hat : a ≤ t) (ht : t < Real.pi / 2) :
    (2 + γ) * (∫ x in a..t, agF γ G x) ≤ agFlux γ G t + ∫ x in a..t, agFd γ G x := by
  have hsub : Set.uIcc a t ⊆ Set.Ioo θ₀ (Real.pi / 2) := by
    rw [Set.uIcc_of_le hat]
    exact fun x hx => ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 ht⟩
  have hGc : ContinuousOn G (Set.uIcc a t) := hG.continuousOn.mono hsub
  have hGd : ContinuousOn (deriv G) (Set.uIcc a t) :=
    (hG.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl).mono hsub
  have hpos : ∀ x ∈ Set.uIcc a t, 0 < Real.pi / 2 - x := by
    intro x hx
    rw [Set.uIcc_of_le hat] at hx
    linarith [hx.2, ht]
  have hyc : ContinuousOn (fun x : ℝ => (Real.pi / 2 - x) ^ (-3 - γ)) (Set.uIcc a t) :=
    (continuousOn_const.sub continuousOn_id).rpow_const
      (fun x hx => Or.inl (ne_of_gt (hpos x hx)))
  have hy4c : ContinuousOn (fun x : ℝ => (Real.pi / 2 - x) ^ (-4 - γ)) (Set.uIcc a t) :=
    (continuousOn_const.sub continuousOn_id).rpow_const
      (fun x hx => Or.inl (ne_of_gt (hpos x hx)))
  have hy2c : ContinuousOn (fun x : ℝ => (Real.pi / 2 - x) ^ (-2 - γ)) (Set.uIcc a t) :=
    (continuousOn_const.sub continuousOn_id).rpow_const
      (fun x hx => Or.inl (ne_of_gt (hpos x hx)))
  -- the derivative of the flux
  have hderiv : ∀ x ∈ Set.uIcc a t, HasDerivAt (agFlux γ G) (agFluxDeriv γ G x) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo θ₀ (Real.pi / 2) := hsub hx
    have hy : 0 < Real.pi / 2 - x := hpos x hx
    have hGat : HasDerivAt G (deriv G x) x :=
      ((hG.differentiableOn one_ne_zero).differentiableAt (isOpen_Ioo.mem_nhds hx')).hasDerivAt
    have h1 : HasDerivAt (fun θ => G θ ^ 2) (2 * G x * deriv G x) x := by
      have h := hGat.pow 2
      convert h using 1
      ring
    have h2 : HasDerivAt (fun θ : ℝ => (Real.pi / 2 - θ) ^ (-3 - γ))
        ((-3 - γ) * (Real.pi / 2 - x) ^ (-3 - γ - 1) * (-1)) x := by
      have hinner : HasDerivAt (fun θ : ℝ => Real.pi / 2 - θ) (-1) x := by
        simpa using (hasDerivAt_id x).const_sub (Real.pi / 2)
      have hout := Real.hasDerivAt_rpow_const (x := Real.pi / 2 - x) (p := -3 - γ)
        (Or.inl (ne_of_gt hy))
      exact hout.comp x hinner
    have hprod : HasDerivAt (fun θ : ℝ => G θ ^ 2 * (Real.pi / 2 - θ) ^ (-3 - γ))
        (2 * G x * deriv G x * (Real.pi / 2 - x) ^ (-3 - γ)
          + G x ^ 2 * ((3 + γ) * (Real.pi / 2 - x) ^ (-4 - γ))) x := by
      have hp := h1.mul h2
      have hval : 2 * G x * deriv G x * (Real.pi / 2 - x) ^ (-3 - γ)
          + G x ^ 2 * ((-3 - γ) * (Real.pi / 2 - x) ^ (-3 - γ - 1) * (-1))
          = 2 * G x * deriv G x * (Real.pi / 2 - x) ^ (-3 - γ)
            + G x ^ 2 * ((3 + γ) * (Real.pi / 2 - x) ^ (-4 - γ)) := by
        rw [show (-3 : ℝ) - γ - 1 = -4 - γ by ring]
        ring
      rw [hval] at hp
      exact hp
    exact hprod
  have hFluxInt : IntervalIntegrable (agFluxDeriv γ G) volume a t := by
    refine ContinuousOn.intervalIntegrable ?_
    show ContinuousOn _ (Set.uIcc a t)
    exact ((((continuousOn_const.mul hGc).mul hGd).mul hyc)).add
      ((hGc.pow 2).mul (continuousOn_const.mul hy4c))
  have hFInt : IntervalIntegrable (agF γ G) volume a t := by
    refine ContinuousOn.intervalIntegrable ?_
    show ContinuousOn _ (Set.uIcc a t)
    exact (hGc.pow 2).mul hy4c
  have hFdInt : IntervalIntegrable (agFd γ G) volume a t := by
    refine ContinuousOn.intervalIntegrable ?_
    show ContinuousOn _ (Set.uIcc a t)
    exact (hGd.pow 2).mul hy2c
  -- pointwise arithmetic–geometric mean
  have hpt : ∀ x ∈ Set.Icc a t, (2 + γ) * agF γ G x ≤ agFluxDeriv γ G x + agFd γ G x := by
    intro x hx
    have hxu : x ∈ Set.uIcc a t := by rwa [Set.uIcc_of_le hat]
    have hy : 0 < Real.pi / 2 - x := hpos x hxu
    set y := Real.pi / 2 - x with hydef
    have e1 : y ^ (-2 - γ / 2) * y ^ (-2 - γ / 2) = y ^ (-4 - γ) := by
      rw [← Real.rpow_add hy]
      congr 1
      ring
    have e2 : y ^ (-1 - γ / 2) * y ^ (-1 - γ / 2) = y ^ (-2 - γ) := by
      rw [← Real.rpow_add hy]
      congr 1
      ring
    have e3 : y ^ (-2 - γ / 2) * y ^ (-1 - γ / 2) = y ^ (-3 - γ) := by
      rw [← Real.rpow_add hy]
      congr 1
      ring
    have hsq : 0 ≤ (G x * y ^ (-2 - γ / 2) + deriv G x * y ^ (-1 - γ / 2)) ^ 2 := sq_nonneg _
    have hexp : (G x * y ^ (-2 - γ / 2) + deriv G x * y ^ (-1 - γ / 2)) ^ 2
        = G x ^ 2 * y ^ (-4 - γ) + 2 * (G x * deriv G x * y ^ (-3 - γ))
          + (deriv G x) ^ 2 * y ^ (-2 - γ) := by
      rw [add_sq, mul_pow, mul_pow, pow_two (y ^ (-2 - γ / 2)), pow_two (y ^ (-1 - γ / 2)), e1, e2]
      rw [show 2 * (G x * y ^ (-2 - γ / 2)) * (deriv G x * y ^ (-1 - γ / 2))
          = 2 * (G x * deriv G x * y ^ (-3 - γ)) by rw [← e3]; ring]
    rw [hexp] at hsq
    have hA : 0 ≤ G x ^ 2 * y ^ (-4 - γ) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hy.le _)
    have hC : 0 ≤ (deriv G x) ^ 2 * y ^ (-2 - γ) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hy.le _)
    have h3 : 0 ≤ (3 + γ) * y ^ (-4 - γ) :=
      mul_nonneg (by linarith) (Real.rpow_nonneg hy.le _)
    have hB : 0 ≤ G x ^ 2 * ((3 + γ) * y ^ (-4 - γ)) := mul_nonneg (sq_nonneg _) h3
    rw [agF, agFluxDeriv, agFd, ← hydef]
    nlinarith [hsq]
  have hstep : (2 + γ) * (∫ x in a..t, agF γ G x)
      ≤ (∫ x in a..t, agFluxDeriv γ G x) + (∫ x in a..t, agFd γ G x) := by
    have h1 : (∫ x in a..t, (2 + γ) * agF γ G x)
        ≤ ∫ x in a..t, (agFluxDeriv γ G x + agFd γ G x) :=
      intervalIntegral.integral_mono_on hat (hFInt.const_mul (2 + γ))
        (hFluxInt.add hFdInt) hpt
    rwa [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hFluxInt hFdInt] at h1
  have hFTC : ∫ x in a..t, agFluxDeriv γ G x = agFlux γ G t - agFlux γ G a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hFluxInt
  have hUa : 0 ≤ agFlux γ G a := agFlux_nonneg γ G (by linarith)
  linarith [hstep, hFTC, hUa]

/-- `(π/2 - θ)^{-1}` is not integrable near `π/2`. -/
lemma not_integrableOn_sub_inv (T : ℝ) (hT : T < Real.pi / 2) :
    ¬ IntegrableOn (fun θ => (Real.pi / 2 - θ) ^ (-1 : ℝ)) (Set.Ioo T (Real.pi / 2)) := by
  intro hI
  have hb : 0 < Real.pi / 2 - T := by linarith
  set K : ℝ := ∫ θ in Set.Ioo T (Real.pi / 2), (Real.pi / 2 - θ) ^ (-1 : ℝ) with hK
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo T (Real.pi / 2))]
      (fun θ => (Real.pi / 2 - θ) ^ (-1 : ℝ)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    exact Real.rpow_nonneg (by linarith [hθ.2]) _
  -- bound by the full set integral and compute by the fundamental theorem of calculus
  have hkey : ∀ s ∈ Set.Ioo T (Real.pi / 2),
      Real.log (Real.pi / 2 - T) - Real.log (Real.pi / 2 - s) ≤ K := by
    intro s hs
    have hTs : T ≤ s := hs.1.le
    have h1 : (∫ x in T..s, (Real.pi / 2 - x) ^ (-1 : ℝ))
        = ∫ x in Set.Ioo T s, (Real.pi / 2 - x) ^ (-1 : ℝ) := by
      rw [intervalIntegral.integral_of_le hTs, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    have h2 : (∫ x in T..s, (Real.pi / 2 - x) ^ (-1 : ℝ)) ≤ K := by
      rw [h1, hK]
      exact MeasureTheory.setIntegral_mono_set hI hnn
        (Filter.Eventually.of_forall (fun θ hθ => ⟨hθ.1, lt_trans hθ.2 hs.2⟩))
    have h3 : (∫ x in T..s, (Real.pi / 2 - x) ^ (-1 : ℝ))
        = Real.log (Real.pi / 2 - T) - Real.log (Real.pi / 2 - s) := by
      have hderiv : ∀ x ∈ Set.uIcc T s,
          HasDerivAt (fun θ : ℝ => -Real.log (Real.pi / 2 - θ)) ((Real.pi / 2 - x) ^ (-1 : ℝ)) x := by
        intro x hx
        rw [Set.uIcc_of_le hTs] at hx
        have hx2 : Real.pi / 2 - x ≠ 0 := ne_of_gt (by linarith [hx.2, hs.2])
        have hinner : HasDerivAt (fun θ : ℝ => Real.pi / 2 - θ) (-1) x := by
          simpa using (hasDerivAt_id x).const_sub (Real.pi / 2)
        have hlog := (hinner.log hx2).neg
        convert hlog using 1
        rw [Real.rpow_neg_one]
        ring
      have hint : IntervalIntegrable (fun x : ℝ => (Real.pi / 2 - x) ^ (-1 : ℝ)) volume T s := by
        refine ContinuousOn.intervalIntegrable ?_
        refine (continuousOn_const.sub continuousOn_id).rpow_const (fun x hx => Or.inl ?_)
        have hpx : 0 < Real.pi / 2 - x := by
          rw [Set.uIcc_of_le hTs] at hx
          linarith [hx.2, hs.2]
        exact ne_of_gt hpx
      have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
      rw [this]
      ring
    linarith [h2, h3]
  -- take `s = π/2 - 1/(n+1)` and let `n → ∞`: the logarithm diverges
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      K - Real.log (Real.pi / 2 - T) < Real.log ((n : ℝ) + 1) := by
    have h3 : ∀ᶠ x : ℝ in Filter.atTop,
        K - Real.log (Real.pi / 2 - T) < Real.log x ∧ (1 : ℝ) ≤ x :=
      (Real.tendsto_log_atTop.eventually (eventually_gt_atTop _)).and (eventually_ge_atTop 1)
    filter_upwards [Filter.Tendsto.eventually tendsto_natCast_atTop_atTop h3] with n hn
    have h4 : Real.log ((n : ℝ)) ≤ Real.log ((n : ℝ) + 1) :=
      Real.log_le_log (by linarith [hn.2]) (by linarith)
    linarith [hn.1, h4]
  obtain ⟨N₀, hN₀⟩ := exists_nat_one_div_lt hb
  obtain ⟨n, hn, hnN⟩ := (hev.and (eventually_ge_atTop N₀)).exists
  have hlog1 : Real.log (1 / ((n : ℝ) + 1)) = -Real.log ((n : ℝ) + 1) := by
    rw [Real.log_div one_ne_zero (by positivity), Real.log_one]
    ring
  have hmem : Real.pi / 2 - 1 / ((n : ℝ) + 1) ∈ Set.Ioo T (Real.pi / 2) := by
    have hpos : 0 < (n : ℝ) + 1 := by positivity
    refine ⟨?_, by linarith [show (0:ℝ) < 1 / ((n:ℝ)+1) by positivity]⟩
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 / ((N₀ : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (N₀ : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hnN
      linarith
    linarith [hN₀, hle]
  have hle := hkey _ hmem
  have hs_eq : Real.pi / 2 - (Real.pi / 2 - 1 / ((n : ℝ) + 1)) = 1 / ((n : ℝ) + 1) := by ring
  rw [hs_eq, hlog1] at hle
  linarith [hle, hn]


/-- The weighted Hardy (Agmon) inequality.  See the module docstring. -/
theorem agmonWeightedHardy (γ θ₀ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) (hθ₀ : θ₀ < Real.pi / 2)
    (G : ℝ → ℝ) (hG : ContDiffOn ℝ 1 G (Set.Ioo θ₀ (Real.pi / 2)))
    (hInt : IntegrableOn (agF γ G) (Set.Ioo θ₀ (Real.pi / 2)))
    (hInt' : IntegrableOn (agFd γ G) (Set.Ioo θ₀ (Real.pi / 2))) :
    (2 + γ) * (∫ θ in Set.Ioo θ₀ (Real.pi / 2), agF γ G θ)
      ≤ ∫ θ in Set.Ioo θ₀ (Real.pi / 2), agFd γ G θ := by

  have hII : ∀ t, θ₀ < t → t < Real.pi / 2 →
      (2 + γ) * (∫ x in Set.Ioo θ₀ t, agF γ G x)
        ≤ agFlux γ G t + (∫ x in Set.Ioo θ₀ t, agFd γ G x) := by
    intro t ht0 ht1
    set aSeq : ℕ → ℝ := fun n => θ₀ + (t - θ₀) / ((n : ℝ) + 2) with haSeq
    have hd : 0 < t - θ₀ := by linarith
    have hmono_a : Monotone (fun n => Set.Ioo (aSeq n) t) := by
      intro i j hij
      refine Set.Ioo_subset_Ioo_left ?_
      have hij' : ((i : ℝ) + 2) ≤ ((j : ℝ) + 2) := by
        have : (i : ℝ) ≤ (j : ℝ) := Nat.cast_le.mpr hij
        linarith
      have h1 : (t - θ₀) / ((j : ℝ) + 2) ≤ (t - θ₀) / ((i : ℝ) + 2) :=
        div_le_div_of_nonneg_left hd.le (by positivity) hij'
      simp only [haSeq]
      linarith
    have hlt_t : ∀ n, aSeq n < t := by
      intro n
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
      have hpos : 0 < ((n : ℝ) + 2) := by positivity
      have h1 : (t - θ₀) / ((n : ℝ) + 2) < t - θ₀ := by
        rw [div_lt_iff₀ hpos]
        nlinarith [hd, hn0]
      simp only [haSeq]
      linarith
    have hgt_0 : ∀ n, θ₀ < aSeq n := by
      intro n
      have hpos : 0 < ((n : ℝ) + 2) := by positivity
      have h1 : 0 < (t - θ₀) / ((n : ℝ) + 2) := div_pos hd hpos
      simp only [haSeq]
      linarith
    have hUnion : (⋃ n, Set.Ioo (aSeq n) t) = Set.Ioo θ₀ t := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_Ioo]
      constructor
      · rintro ⟨n, h1, h2⟩
        exact ⟨lt_trans (hgt_0 n) h1, h2⟩
      · rintro ⟨hx1, hx2⟩
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < (x - θ₀) / (t - θ₀) by positivity)
        refine ⟨n, ?_, hx2⟩
        have hpos : 0 < ((n : ℝ) + 1) := by positivity
        have h2 : (t - θ₀) / ((n : ℝ) + 1) < x - θ₀ := by
          have h4 : (1 / ((n : ℝ) + 1)) * (t - θ₀) < ((x - θ₀) / (t - θ₀)) * (t - θ₀) :=
            mul_lt_mul_of_pos_right hn hd
          rw [div_mul_cancel₀ (x - θ₀) (ne_of_gt hd)] at h4
          rwa [one_div_mul_eq_div] at h4
        have h3 : (t - θ₀) / ((n : ℝ) + 2) ≤ (t - θ₀) / ((n : ℝ) + 1) := by
          apply div_le_div_of_nonneg_left hd.le (by positivity)
          linarith
        simp only [haSeq]
        linarith
    have hstep : ∀ n, (2 + γ) * (∫ x in Set.Ioo (aSeq n) t, agF γ G x)
        ≤ agFlux γ G t + (∫ x in Set.Ioo (aSeq n) t, agFd γ G x) := by
      intro n
      have h := agmon_interval γ θ₀ hγ1 hG (hgt_0 n) (le_of_lt (hlt_t n)) ht1
      have e1 : (∫ x in aSeq n..t, agF γ G x) = ∫ x in Set.Ioo (aSeq n) t, agF γ G x := by
        rw [intervalIntegral.integral_of_le (le_of_lt (hlt_t n)), MeasureTheory.integral_Ioc_eq_integral_Ioo]
      have e2 : (∫ x in aSeq n..t, agFd γ G x) = ∫ x in Set.Ioo (aSeq n) t, agFd γ G x := by
        rw [intervalIntegral.integral_of_le (le_of_lt (hlt_t n)), MeasureTheory.integral_Ioc_eq_integral_Ioo]
      rw [e1, e2] at h
      exact h
    have hIntU : IntegrableOn (agF γ G) (⋃ n, Set.Ioo (aSeq n) t) := by
      rw [hUnion]; exact hInt.mono_set (Set.Ioo_subset_Ioo_right ht1.le)
    have hIntU' : IntegrableOn (agFd γ G) (⋃ n, Set.Ioo (aSeq n) t) := by
      rw [hUnion]; exact hInt'.mono_set (Set.Ioo_subset_Ioo_right ht1.le)
    have hT1 := MeasureTheory.tendsto_setIntegral_of_monotone (f := agF γ G) (μ := volume)
      (s := fun n : ℕ => Set.Ioo (aSeq n) t) (fun n => measurableSet_Ioo) hmono_a hIntU
    have hT2 := MeasureTheory.tendsto_setIntegral_of_monotone (f := agFd γ G) (μ := volume)
      (s := fun n : ℕ => Set.Ioo (aSeq n) t) (fun n => measurableSet_Ioo) hmono_a hIntU'
    rw [hUnion] at hT1 hT2
    refine le_of_tendsto_of_tendsto (hT1.const_mul (2 + γ)) (tendsto_const_nhds.add hT2) ?_
    exact Filter.Eventually.of_forall hstep

  set A : ℝ := ∫ x in Set.Ioo θ₀ (Real.pi / 2), agF γ G x with hA
  set B : ℝ := ∫ x in Set.Ioo θ₀ (Real.pi / 2), agFd γ G x with hB
  have hmono : ∀ {s t : ℝ}, s ≤ t → t ≤ Real.pi / 2 →
      (∫ x in Set.Ioo θ₀ s, agF γ G x) ≤ ∫ x in Set.Ioo θ₀ t, agF γ G x := by
    intro s t hst ht
    refine MeasureTheory.setIntegral_mono_set (hInt.mono_set (Set.Ioo_subset_Ioo_right ht)) ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
      exact agF_nonneg γ G (by linarith [hx.2, hst, ht])
    · exact Filter.Eventually.of_forall fun x hx => ⟨hx.1, lt_of_lt_of_le hx.2 hst⟩
  have hmonod : ∀ {s t : ℝ}, s ≤ t → t ≤ Real.pi / 2 →
      (∫ x in Set.Ioo θ₀ s, agFd γ G x) ≤ ∫ x in Set.Ioo θ₀ t, agFd γ G x := by
    intro s t hst ht
    refine MeasureTheory.setIntegral_mono_set (hInt'.mono_set (Set.Ioo_subset_Ioo_right ht)) ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
      exact agFd_nonneg γ G (by linarith [hx.2, hst, ht])
    · exact Filter.Eventually.of_forall fun x hx => ⟨hx.1, lt_of_lt_of_le hx.2 hst⟩
  have hleA : ∀ t, t ≤ Real.pi / 2 → (∫ x in Set.Ioo θ₀ t, agF γ G x) ≤ A := by
    intro t ht
    rw [hA]
    refine MeasureTheory.setIntegral_mono_set hInt ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
      exact agF_nonneg γ G (by linarith [hx.2])
    · exact Filter.Eventually.of_forall fun x hx => ⟨hx.1, lt_of_lt_of_le hx.2 ht⟩
  have hleB : ∀ t, t ≤ Real.pi / 2 → (∫ x in Set.Ioo θ₀ t, agFd γ G x) ≤ B := by
    intro t ht
    rw [hB]
    refine MeasureTheory.setIntegral_mono_set hInt' ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
      exact agFd_nonneg γ G (by linarith [hx.2])
    · exact Filter.Eventually.of_forall fun x hx => ⟨hx.1, lt_of_lt_of_le hx.2 ht⟩
  set cs : ℕ → ℝ := fun n => Real.pi / 2 - 1 / ((n : ℝ) + 1) with hcs
  have hcs_lt : ∀ n, cs n < Real.pi / 2 := by
    intro n; have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    simp only [hcs]; linarith
  have hcs_mono : Monotone cs := by
    intro i j hij
    have hij' : ((i : ℝ) + 1) ≤ ((j : ℝ) + 1) := by
      have : (i : ℝ) ≤ (j : ℝ) := Nat.cast_le.mpr hij
      linarith
    have h1 : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) hij'
    simp only [hcs]; linarith
  have hcs_tend : Tendsto cs Filter.atTop (𝓝 (Real.pi / 2)) := by
    have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [hcs] using tendsto_const_nhds.sub h1
  have hUnion_cs : (⋃ n, Set.Ioo θ₀ (cs n)) = Set.Ioo θ₀ (Real.pi / 2) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_Ioo]
    constructor
    · rintro ⟨n, h1, h2⟩; exact ⟨h1, lt_of_lt_of_le h2 (le_of_lt (hcs_lt n))⟩
    · rintro ⟨hx1, hx2⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < Real.pi / 2 - x by linarith)
      refine ⟨n, hx1, ?_⟩
      simp only [hcs]; linarith
  have hA_tend : Tendsto (fun n => ∫ x in Set.Ioo θ₀ (cs n), agF γ G x) Filter.atTop (𝓝 A) := by
    have h := MeasureTheory.tendsto_setIntegral_of_monotone (f := agF γ G) (μ := volume)
      (s := fun n : ℕ => Set.Ioo θ₀ (cs n)) (fun n => measurableSet_Ioo)
      (fun i j hij => Set.Ioo_subset_Ioo_right (hcs_mono hij)) (by rw [hUnion_cs]; exact hInt)
    rwa [hUnion_cs, ← hA] at h
  have hB_tend : Tendsto (fun n => ∫ x in Set.Ioo θ₀ (cs n), agFd γ G x) Filter.atTop (𝓝 B) := by
    have h := MeasureTheory.tendsto_setIntegral_of_monotone (f := agFd γ G) (μ := volume)
      (s := fun n : ℕ => Set.Ioo θ₀ (cs n)) (fun n => measurableSet_Ioo)
      (fun i j hij => Set.Ioo_subset_Ioo_right (hcs_mono hij)) (by rw [hUnion_cs]; exact hInt')
    rwa [hUnion_cs, ← hB] at h
  have hA_lim : Tendsto (fun t => ∫ x in Set.Ioo θ₀ t, agF γ G x) (𝓝[<] (Real.pi / 2)) (𝓝 A) := by
    rw [tendsto_order]
    constructor
    · intro a' ha'
      obtain ⟨N, hN⟩ := eventually_atTop.mp (hA_tend.eventually (eventually_gt_nhds ha'))
      obtain ⟨N₀, hN₀⟩ := (hcs_tend.eventually (IsOpen.mem_nhds isOpen_Ioi hθ₀)).exists
      set M := max N N₀ with hM
      have hMa : a' < ∫ x in Set.Ioo θ₀ (cs M), agF γ G x := hN M (le_max_left _ _)
      rw [eventually_nhdsWithin_iff]
      filter_upwards [IsOpen.mem_nhds isOpen_Ioi (show cs M < Real.pi / 2 from hcs_lt M)] with t ht htlt
      exact lt_of_lt_of_le hMa (hmono ht.le htlt.le)
    · intro a' ha'
      rw [eventually_nhdsWithin_iff]
      filter_upwards with t ht
      exact lt_of_le_of_lt (hleA t ht.le) ha'
  have hB_lim : Tendsto (fun t => ∫ x in Set.Ioo θ₀ t, agFd γ G x) (𝓝[<] (Real.pi / 2)) (𝓝 B) := by
    rw [tendsto_order]
    constructor
    · intro a' ha'
      obtain ⟨N, hN⟩ := eventually_atTop.mp (hB_tend.eventually (eventually_gt_nhds ha'))
      obtain ⟨N₀, hN₀⟩ := (hcs_tend.eventually (IsOpen.mem_nhds isOpen_Ioi hθ₀)).exists
      set M := max N N₀ with hM
      have hMa : a' < ∫ x in Set.Ioo θ₀ (cs M), agFd γ G x := hN M (le_max_left _ _)
      rw [eventually_nhdsWithin_iff]
      filter_upwards [IsOpen.mem_nhds isOpen_Ioi (show cs M < Real.pi / 2 from hcs_lt M)] with t ht htlt
      exact lt_of_lt_of_le hMa (hmonod ht.le htlt.le)
    · intro a' ha'
      rw [eventually_nhdsWithin_iff]
      filter_upwards with t ht
      exact lt_of_le_of_lt (hleB t ht.le) ha'
  by_contra hcon
  have hc : 0 < (2 + γ) * A - B := by
    have h' : B < (2 + γ) * A := not_le.mp hcon
    linarith
  by_cases hcase : ∀ T, T < Real.pi / 2 → ∃ t ∈ Set.Ioo T (Real.pi / 2), agFlux γ G t ≤ ((2 + γ) * A - B) / 2
  · choose tS htS using fun n : ℕ => hcase (cs n) (hcs_lt n)
    have htS_tend : Tendsto tS Filter.atTop (𝓝[<] (Real.pi / 2)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · refine tendsto_of_tendsto_of_tendsto_of_le_of_le hcs_tend tendsto_const_nhds ?_ ?_
        · exact fun n => (htS n).1.1.le
        · exact fun n => (htS n).1.2.le
      · exact Filter.Eventually.of_forall fun n => (htS n).1.2
    have hlimA : Tendsto (fun n => (2 + γ) * (∫ x in Set.Ioo θ₀ (tS n), agF γ G x)) Filter.atTop (𝓝 ((2 + γ) * A)) := by
      simpa only [Function.comp_apply] using (hA_lim.comp htS_tend).const_mul (2 + γ)
    have hlimB : Tendsto (fun n => ((2 + γ) * A - B) / 2 + (∫ x in Set.Ioo θ₀ (tS n), agFd γ G x))
        Filter.atTop (𝓝 (((2 + γ) * A - B) / 2 + B)) :=
      tendsto_const_nhds.add (hB_lim.comp htS_tend)
    obtain ⟨N₀, hN₀⟩ := (hcs_tend.eventually (IsOpen.mem_nhds isOpen_Ioi hθ₀)).exists
    have hfin : (2 + γ) * A ≤ ((2 + γ) * A - B) / 2 + B := by
      refine le_of_tendsto_of_tendsto hlimA hlimB ?_
      refine (eventually_ge_atTop N₀).mono ?_
      intro n hn
      have hgt : θ₀ < tS n := lt_trans (lt_of_lt_of_le hN₀ (hcs_mono hn)) (htS n).1.1
      have h1 := hII (tS n) hgt (htS n).1.2
      have h2 : agFlux γ G (tS n) ≤ ((2 + γ) * A - B) / 2 := (htS n).2
      linarith
    linarith [hc, hfin]
  · push_neg at hcase
    obtain ⟨T, hTπ, hT2⟩ := hcase
    set T' : ℝ := (max T θ₀ + Real.pi / 2) / 2 with hT'def
    have hmax : max T θ₀ < Real.pi / 2 := max_lt hTπ hθ₀
    have hT'θ : θ₀ < T' := by rw [hT'def]; linarith [le_max_right T θ₀, hθ₀]
    have hT'π : T' < Real.pi / 2 := by rw [hT'def]; linarith [hmax]
    have hT'T : T < T' := by rw [hT'def]; linarith [le_max_left T θ₀, hTπ]
    have hpt : ∀ θ ∈ Set.Ioo T' (Real.pi / 2),
        ((2 + γ) * A - B) / 2 * (Real.pi / 2 - θ) ^ (-1 : ℝ) ≤ agF γ G θ := by
      intro θ hθ
      have hy : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
      have h1 : ((2 + γ) * A - B) / 2 ≤ agFlux γ G θ :=
        le_of_lt (hT2 θ ⟨lt_trans hT'T hθ.1, hθ.2⟩)
      have h2 : agFlux γ G θ * (Real.pi / 2 - θ) ^ (-1 : ℝ) = agF γ G θ := by
        rw [agFlux, agF, mul_assoc, ← Real.rpow_add hy]
        congr 1
        ring_nf
      calc ((2 + γ) * A - B) / 2 * (Real.pi / 2 - θ) ^ (-1 : ℝ)
          ≤ agFlux γ G θ * (Real.pi / 2 - θ) ^ (-1 : ℝ) :=
            mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hy.le _)
        _ = agF γ G θ := h2
    have hbase : IntegrableOn (fun θ => ((2 + γ) * A - B) / 2 * (Real.pi / 2 - θ) ^ (-1 : ℝ))
        (Set.Ioo T' (Real.pi / 2)) := by
      refine MeasureTheory.Integrable.mono (hInt.mono_set (Set.Ioo_subset_Ioo_left hT'θ.le)) ?_ ?_
      · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
        refine ((continuousOn_const.sub continuousOn_id).rpow_const (fun θ hθ => Or.inl ?_)).const_mul _
        have hpx : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
        exact ne_of_gt hpx
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
        rw [Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (by linarith [hc]) (Real.rpow_nonneg (by linarith [hθ.2]) _)),
          abs_of_nonneg (agF_nonneg γ G (by linarith [hθ.2]))]
        exact hpt θ hθ
    have h2 := hbase.const_mul (2 / ((2 + γ) * A - B))
    have h3 : (fun θ : ℝ => (2 / ((2 + γ) * A - B)) *
        (((2 + γ) * A - B) / 2 * (Real.pi / 2 - θ) ^ (-1 : ℝ)))
        = fun θ => (Real.pi / 2 - θ) ^ (-1 : ℝ) := by
      funext θ
      have hne : (2 + γ) * A - B ≠ 0 := ne_of_gt hc
      field_simp
    exact not_integrableOn_sub_inv T' hT'π (by rwa [h3] at h2)

/-- The pointwise Hardy bound near `π/2`: `u(θ)² ≤ (π/2 - θ)·∫(u')²` for `u` continuous on
`[0,π/2]`, of class `C¹` on the open interval, with `u(π/2) = 0`. -/
theorem sq_le_weight_mul (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 1 u (Set.Ioo 0 (Real.pi / 2)))
    (hcont : ContinuousOn u (Set.Icc 0 (Real.pi / 2)))
    (hπ : u (Real.pi / 2) = 0)
    (hInt : IntegrableOn (fun θ => (deriv u θ) ^ 2) (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      (u θ) ^ 2 ≤ (Real.pi / 2 - θ) * ∫ θ in Set.Ioo 0 (Real.pi / 2), (deriv u θ) ^ 2 := by
  have hc0 : 0 < Real.pi / 2 := by positivity
  set A : ℝ := ∫ θ in Set.Ioo 0 (Real.pi / 2), (deriv u θ) ^ 2 with hA
  have hderiv_cont : ContinuousOn (deriv u) (Set.Ioo 0 (Real.pi / 2)) := by
    have h1 : ContinuousOn (derivWithin u (Set.Ioo 0 (Real.pi / 2)))
        (Set.Ioo 0 (Real.pi / 2)) :=
      hu.continuousOn_derivWithin (uniqueDiffOn_Ioo 0 (Real.pi / 2)) le_rfl
    refine h1.congr (fun x hx => ?_)
    exact (derivWithin_of_mem_nhds (isOpen_Ioo.mem_nhds hx)).symm
  have htend : Tendsto u (𝓝[<] (Real.pi / 2)) (𝓝 (u (Real.pi / 2))) := by
    have hle : 𝓝[Set.Iio (Real.pi / 2)] (Real.pi / 2)
        ≤ 𝓝[Set.Icc 0 (Real.pi / 2)] (Real.pi / 2) := by
      rw [nhdsWithin_le_iff, mem_nhdsWithin_iff_eventually]
      filter_upwards [Ioi_mem_nhds hc0] with y hy hyc
      exact ⟨le_of_lt hy, le_of_lt hyc⟩
    exact ((hcont.continuousWithinAt ⟨hc0.le, le_rfl⟩).tendsto).mono_left hle
  intro θ hθ
  have hθ0 : 0 < θ := by linarith [Real.pi_pos, hθ.1]
  have hθc : θ < Real.pi / 2 := hθ.2
  have hlim : Tendsto (fun t => |u t - u θ| ^ 2) (𝓝[<] (Real.pi / 2))
      (𝓝 ((u θ) ^ 2)) := by
    have h2 : Tendsto (fun t => u t - u θ) (𝓝[<] (Real.pi / 2))
        (𝓝 (u (Real.pi / 2) - u θ)) := htend.sub tendsto_const_nhds
    have h3 := h2.abs.pow 2
    rw [hπ, zero_sub, abs_neg, sq_abs] at h3
    exact h3
  refine le_of_tendsto hlim ?_
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Ioi_mem_nhds hθc] with t ht htc
  have ht1 : θ < t := ht
  have ht2 : t < Real.pi / 2 := htc
  have hθt : θ ≤ t := le_of_lt ht1
  have hsub : Set.uIcc θ t ⊆ Set.Ioo 0 (Real.pi / 2) := by
    intro x hx
    rw [Set.uIcc_of_le hθt, Set.mem_Icc] at hx
    exact ⟨lt_of_lt_of_le hθ0 hx.1, lt_of_le_of_lt hx.2 ht2⟩
  have hsubIoc : Set.Ioc θ t ⊆ Set.Ioo 0 (Real.pi / 2) := fun x hx =>
    ⟨lt_trans hθ0 hx.1, lt_of_le_of_lt hx.2 ht2⟩
  have hderiv : ∀ x ∈ Set.uIcc θ t, HasDerivAt u (deriv u x) x := fun x hx =>
    (hu.contDiffAt (isOpen_Ioo.mem_nhds (hsub hx))).differentiableAt_one.hasDerivAt
  have hInt1 : IntervalIntegrable (deriv u) volume θ t :=
    (hderiv_cont.mono hsub).intervalIntegrable
  have hftc : ∫ x in θ..t, deriv u x = u t - u θ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hInt1
  have h1 : |u t - u θ| ≤ ∫ x in θ..t, |deriv u x| := by
    have h := intervalIntegral.abs_integral_le_integral_abs (f := deriv u) (μ := volume) hθt
    rwa [hftc] at h
  have hfi : IntegrableOn (fun x => |deriv u x| ^ 2 * 1) (Set.Ioc θ t) := by
    simpa only [mul_one, sq_abs] using hInt.mono_set hsubIoc
  have hsi : IntegrableOn (fun _ : ℝ => (1 : ℝ)⁻¹) (Set.Ioc θ t) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hθt]
    simpa using (continuousOn_const (c := (1 : ℝ)) (s := Set.uIcc θ t)).intervalIntegrable
  have hcs := Work.FTS.EllipticEst.remov.interval_integral_sq_le_mul
    (f := fun x => |deriv u x|) (σ := fun _ => (1 : ℝ)) hθt (fun s _ => zero_lt_one) hfi hsi
  have hc1 : (∫ x in θ..t, |deriv u x| ^ 2 * 1) = ∫ x in θ..t, (deriv u x) ^ 2 := by
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    rw [mul_one, sq_abs]
  have hc2 : (∫ x in θ..t, (1 : ℝ)⁻¹) = t - θ := by
    have h : (∫ x in θ..t, (1 : ℝ)) = t - θ := by
      simpa using intervalIntegral.integral_const (1 : ℝ) (a := θ) (b := t)
    simpa [inv_one] using h
  rw [hc1, hc2] at hcs
  have hInt2 : (∫ x in θ..t, (deriv u x) ^ 2) ≤ A := by
    rw [hA, intervalIntegral.integral_of_le hθt, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    exact setIntegral_mono_set hInt (Filter.Eventually.of_forall (fun x => sq_nonneg _))
      (Filter.Eventually.of_forall (fun x hx => hsubIoc ⟨hx.1, le_of_lt hx.2⟩))
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun θ _ => sq_nonneg _)
  have h2 : |u t - u θ| ^ 2 ≤ (∫ x in θ..t, |deriv u x|) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h1 2
  have htθ : 0 ≤ t - θ := sub_nonneg.mpr hθt
  have hcle : t - θ ≤ Real.pi / 2 - θ := by linarith
  have h3 : (∫ x in θ..t, (deriv u x) ^ 2) * (t - θ) ≤ A * (Real.pi / 2 - θ) :=
    calc (∫ x in θ..t, (deriv u x) ^ 2) * (t - θ)
        ≤ A * (t - θ) := mul_le_mul_of_nonneg_right hInt2 htθ
      _ ≤ A * (Real.pi / 2 - θ) := mul_le_mul_of_nonneg_left hcle hA0
  calc |u t - u θ| ^ 2 ≤ (∫ x in θ..t, |deriv u x|) ^ 2 := h2
    _ ≤ (∫ x in θ..t, (deriv u x) ^ 2) * (t - θ) := hcs
    _ ≤ A * (Real.pi / 2 - θ) := h3
    _ = (Real.pi / 2 - θ) * A := by ring

/-- Integrability of `u² (π/2-θ)^{-γ}` near `π/2`, `1 ≤ γ < 2`. -/
theorem integrableOn_sq_mul_sub_rpow (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 1 u (Set.Ioo 0 (Real.pi / 2)))
    (hcont : ContinuousOn u (Set.Icc 0 (Real.pi / 2)))
    (hπ : u (Real.pi / 2) = 0)
    (hInt : IntegrableOn (fun θ => (deriv u θ) ^ 2) (Set.Ioo 0 (Real.pi / 2))) :
    IntegrableOn (fun θ => (u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-γ))
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
  set A : ℝ := ∫ θ in Set.Ioo 0 (Real.pi / 2), (deriv u θ) ^ 2 with hA
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun θ _ => sq_nonneg _)
  have hkey := sq_le_weight_mul u hu hcont hπ hInt
  set maj : ℝ → ℝ := fun θ => A * (Real.pi / 2 - θ) ^ (1 - γ) with hmaj
  have hmajInt : IntegrableOn maj (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
    rw [hmaj]
    have h1 : IntervalIntegrable (fun x : ℝ => x ^ (1 - γ)) volume 0 (Real.pi / 4) :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    have h2 : IntervalIntegrable (fun θ : ℝ => (Real.pi / 2 - θ) ^ (1 - γ))
        volume (Real.pi / 4) (Real.pi / 2) := by
      have h := IntervalIntegrable.comp_sub_left (f := fun x : ℝ => x ^ (1 - γ)) h1.symm (Real.pi / 2)
      have e1 : Real.pi / 2 - Real.pi / 4 = Real.pi / 4 := by ring
      have e2 : Real.pi / 2 - 0 = Real.pi / 2 := by ring
      rw [e1, e2] at h
      exact h
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [Real.pi_pos])] at h2
    exact (h2.mono_set Set.Ioo_subset_Ioc_self).const_mul A
  refine Integrable.mono' hmajInt ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
    refine ((hcont.mono ?_).pow 2).mul
      ((continuousOn_const.sub continuousOn_id).rpow_const (fun x hx => Or.inl (by
        have hpx : (0:ℝ) < Real.pi / 2 - x := by linarith [hx.2]
        simpa using ne_of_gt hpx)))
    intro x hx
    exact ⟨le_of_lt (by linarith [Real.pi_pos, hx.1]), hx.2.le⟩
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have hy : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
    have h1 : (u θ) ^ 2 ≤ (Real.pi / 2 - θ) * A := by
      have := hkey θ hθ
      rwa [← hA] at this
    have hrw : Real.rpow (Real.pi / 2 - θ) (1 - γ)
        = (Real.pi / 2 - θ) * Real.rpow (Real.pi / 2 - θ) (-γ) := by
      have h := Real.rpow_add hy 1 (-γ)
      rw [show (1 : ℝ) + (-γ) = 1 - γ by ring, Real.rpow_one] at h
      exact h
    calc ‖(u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-γ)‖
        = (u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-γ) := by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hy.le _))]
      _ ≤ ((Real.pi / 2 - θ) * A) * (Real.pi / 2 - θ) ^ (-γ) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hy.le _)
      _ = maj θ := by
          rw [hmaj]
          change (Real.pi / 2 - θ) * A * Real.rpow (Real.pi / 2 - θ) (-γ)
            = A * Real.rpow (Real.pi / 2 - θ) (1 - γ)
          rw [show (Real.pi / 2 - θ) * A * Real.rpow (Real.pi / 2 - θ) (-γ)
              = A * ((Real.pi / 2 - θ) * Real.rpow (Real.pi / 2 - θ) (-γ)) by ring, ← hrw]

theorem hardyUDivY (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 1 u (Set.Ioo 0 (Real.pi / 2)))
    (hcont : ContinuousOn u (Set.Icc 0 (Real.pi / 2)))
    (hπ : u (Real.pi / 2) = 0)
    (hInt : IntegrableOn (fun θ => (deriv u θ) ^ 2) (Set.Ioo 0 (Real.pi / 2))) :
    (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), (u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-γ))
      ≤ 2 * ∫ θ in Set.Ioo 0 (Real.pi / 2), (deriv u θ) ^ 2 := by
  have hc0 : 0 < Real.pi / 2 := by positivity
  set A : ℝ := ∫ θ in Set.Ioo 0 (Real.pi / 2), (deriv u θ) ^ 2 with hA
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact setIntegral_nonneg measurableSet_Ioo (fun θ _ => sq_nonneg _)
  have hderiv_cont : ContinuousOn (deriv u) (Set.Ioo 0 (Real.pi / 2)) := by
    have h1 : ContinuousOn (derivWithin u (Set.Ioo 0 (Real.pi / 2)))
        (Set.Ioo 0 (Real.pi / 2)) :=
      hu.continuousOn_derivWithin (uniqueDiffOn_Ioo 0 (Real.pi / 2)) le_rfl
    refine h1.congr (fun x hx => ?_)
    exact (derivWithin_of_mem_nhds (isOpen_Ioo.mem_nhds hx)).symm
  have htend : Tendsto u (𝓝[<] (Real.pi / 2)) (𝓝 (u (Real.pi / 2))) := by
    have hle : 𝓝[Set.Iio (Real.pi / 2)] (Real.pi / 2)
        ≤ 𝓝[Set.Icc 0 (Real.pi / 2)] (Real.pi / 2) := by
      rw [nhdsWithin_le_iff, mem_nhdsWithin_iff_eventually]
      filter_upwards [Ioi_mem_nhds hc0] with y hy hyc
      exact ⟨le_of_lt hy, le_of_lt hyc⟩
    exact ((hcont.continuousWithinAt ⟨hc0.le, le_rfl⟩).tendsto).mono_left hle
  -- the pointwise Hardy bound
  have hkey : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), (u θ) ^ 2 ≤ (Real.pi / 2 - θ) * A := by
    intro θ hθ
    have hθ0 : 0 < θ := hθ.1
    have hθc : θ < Real.pi / 2 := hθ.2
    have hlim : Tendsto (fun t => |u t - u θ| ^ 2) (𝓝[<] (Real.pi / 2))
        (𝓝 ((u θ) ^ 2)) := by
      have h2 : Tendsto (fun t => u t - u θ) (𝓝[<] (Real.pi / 2))
          (𝓝 (u (Real.pi / 2) - u θ)) := htend.sub tendsto_const_nhds
      have h3 := h2.abs.pow 2
      rw [hπ, zero_sub, abs_neg, sq_abs] at h3
      exact h3
    refine le_of_tendsto hlim ?_
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Ioi_mem_nhds hθc] with t ht htc
    have ht1 : θ < t := ht
    have ht2 : t < Real.pi / 2 := htc
    have hθt : θ ≤ t := le_of_lt ht1
    have hsub : Set.uIcc θ t ⊆ Set.Ioo 0 (Real.pi / 2) := by
      intro x hx
      rw [Set.uIcc_of_le hθt, Set.mem_Icc] at hx
      exact ⟨lt_of_lt_of_le hθ0 hx.1, lt_of_le_of_lt hx.2 ht2⟩
    have hsubIoc : Set.Ioc θ t ⊆ Set.Ioo 0 (Real.pi / 2) := fun x hx =>
      ⟨lt_trans hθ0 hx.1, lt_of_le_of_lt hx.2 ht2⟩
    have hderiv : ∀ x ∈ Set.uIcc θ t, HasDerivAt u (deriv u x) x := fun x hx =>
      (hu.contDiffAt (isOpen_Ioo.mem_nhds (hsub hx))).differentiableAt_one.hasDerivAt
    have hInt1 : IntervalIntegrable (deriv u) volume θ t :=
      (hderiv_cont.mono hsub).intervalIntegrable
    have hftc : ∫ x in θ..t, deriv u x = u t - u θ :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hInt1
    have h1 : |u t - u θ| ≤ ∫ x in θ..t, |deriv u x| := by
      have h := intervalIntegral.abs_integral_le_integral_abs (f := deriv u) (μ := volume) hθt
      rwa [hftc] at h
    have hfi : IntegrableOn (fun x => |deriv u x| ^ 2 * 1) (Set.Ioc θ t) := by
      simpa only [mul_one, sq_abs] using hInt.mono_set hsubIoc
    have hsi : IntegrableOn (fun _ : ℝ => (1 : ℝ)⁻¹) (Set.Ioc θ t) := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hθt]
      simpa using (continuousOn_const (c := (1 : ℝ)) (s := Set.uIcc θ t)).intervalIntegrable
    have hcs := Work.FTS.EllipticEst.remov.interval_integral_sq_le_mul
      (f := fun x => |deriv u x|) (σ := fun _ => (1 : ℝ)) hθt (fun s _ => zero_lt_one) hfi hsi
    have hc1 : (∫ x in θ..t, |deriv u x| ^ 2 * 1) = ∫ x in θ..t, (deriv u x) ^ 2 := by
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      rw [mul_one, sq_abs]
    have hc2 : (∫ x in θ..t, (1 : ℝ)⁻¹) = t - θ := by
      have h : (∫ x in θ..t, (1 : ℝ)) = t - θ := by
        simpa using intervalIntegral.integral_const (1 : ℝ) (a := θ) (b := t)
      simpa [inv_one] using h
    rw [hc1, hc2] at hcs
    have hInt2 : (∫ x in θ..t, (deriv u x) ^ 2) ≤ A := by
      rw [hA, intervalIntegral.integral_of_le hθt, MeasureTheory.integral_Ioc_eq_integral_Ioo]
      exact setIntegral_mono_set hInt (Filter.Eventually.of_forall (fun x => sq_nonneg _))
        (Filter.Eventually.of_forall (fun x hx => hsubIoc ⟨hx.1, le_of_lt hx.2⟩))
    have h2 : |u t - u θ| ^ 2 ≤ (∫ x in θ..t, |deriv u x|) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) h1 2
    have htθ : 0 ≤ t - θ := sub_nonneg.mpr hθt
    have hcle : t - θ ≤ Real.pi / 2 - θ := by linarith
    have h3 : (∫ x in θ..t, (deriv u x) ^ 2) * (t - θ) ≤ A * (Real.pi / 2 - θ) :=
      calc (∫ x in θ..t, (deriv u x) ^ 2) * (t - θ)
          ≤ A * (t - θ) := mul_le_mul_of_nonneg_right hInt2 htθ
        _ ≤ A * (Real.pi / 2 - θ) := mul_le_mul_of_nonneg_left hcle hA0
    calc |u t - u θ| ^ 2 ≤ (∫ x in θ..t, |deriv u x|) ^ 2 := h2
      _ ≤ (∫ x in θ..t, (deriv u x) ^ 2) * (t - θ) := hcs
      _ ≤ A * (Real.pi / 2 - θ) := h3
      _ = (Real.pi / 2 - θ) * A := by ring
  -- the value of the weight integral
  have hInt' : (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), (Real.pi / 2 - θ) ^ (1 - γ))
      = (Real.pi / 4) ^ (2 - γ) / (2 - γ) := by
    have h1 : (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), (Real.pi / 2 - θ) ^ (1 - γ))
        = ∫ θ in (Real.pi / 4)..(Real.pi / 2), (Real.pi / 2 - θ) ^ (1 - γ) := by
      rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
        MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rw [h1, intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (1 - γ)) (Real.pi / 2)]
    have hsubv : Real.pi / 2 - Real.pi / 2 = 0 := by ring
    have hsubv2 : Real.pi / 2 - Real.pi / 4 = Real.pi / 4 := by ring
    rw [hsubv, hsubv2]
    have hderiv : ∀ x ∈ Set.Ioo (0:ℝ) (Real.pi / 4),
        HasDerivAt (fun y : ℝ => y ^ (2 - γ) / (2 - γ)) (x ^ (1 - γ)) x := by
      intro x hx
      have hx0 : x ≠ 0 := ne_of_gt hx.1
      have h1 := (Real.hasDerivAt_rpow_const (x := x) (p := 2 - γ) (Or.inl hx0)).div_const (2 - γ)
      have h2 : (2 - γ) * x ^ (2 - γ - 1) / (2 - γ) = x ^ (1 - γ) := by
        rw [show (2:ℝ) - γ - 1 = 1 - γ by ring,
          mul_div_cancel_left₀ _ (by linarith : (2:ℝ) - γ ≠ 0)]
      rw [← h2]
      exact h1
    have hcont' : ContinuousOn (fun y : ℝ => y ^ (2 - γ) / (2 - γ))
        (Set.Icc 0 (Real.pi / 4)) :=
      (continuousOn_id.rpow_const (fun y hy => Or.inr (by linarith))).div_const _
    have hint' : IntervalIntegrable (fun x : ℝ => x ^ (1 - γ)) volume 0 (Real.pi / 4) :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (a := 0)
      (b := Real.pi / 4) (by positivity) hcont' hderiv hint'
    rw [hFTC]
    have hzero : (0 : ℝ) ^ (2 - γ) / (2 - γ) = 0 := by
      rw [Real.zero_rpow (by linarith)]
      simp
    rw [hzero]
    ring
  -- bound the weight integral
  have hbnd : (Real.pi / 4) ^ (2 - γ) / (2 - γ) ≤ 2 := by
    have h1 : (Real.pi / 4) ^ (2 - γ) ≤ (1:ℝ) := by
      have hπ4 : (0:ℝ) < Real.pi / 4 := by positivity
      have hle1 : Real.pi / 4 ≤ 1 := by linarith [Real.pi_lt_four]
      have h2 : (1/2 : ℝ) ≤ 2 - γ := by linarith
      calc (Real.pi / 4) ^ (2 - γ) ≤ (Real.pi / 4) ^ (1/2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_ge hπ4 hle1 h2
        _ ≤ 1 := Real.rpow_le_one (le_of_lt hπ4) hle1 (by norm_num)
    have h3 : (0:ℝ) < 2 - γ := by linarith
    rw [div_le_iff₀ h3]
    nlinarith [h1, h3, hγ2]
  have hIntW : IntegrableOn (fun θ => (Real.pi / 2 - θ) ^ (1 - γ))
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
    have h1 : IntervalIntegrable (fun x : ℝ => x ^ (1 - γ)) volume 0 (Real.pi / 4) :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    have h2 : IntervalIntegrable (fun θ : ℝ => (Real.pi / 2 - θ) ^ (1 - γ))
        volume (Real.pi / 4) (Real.pi / 2) := by
      have h := IntervalIntegrable.comp_sub_left (f := fun x : ℝ => x ^ (1 - γ)) h1.symm (Real.pi / 2)
      have e1 : Real.pi / 2 - Real.pi / 4 = Real.pi / 4 := by ring
      have e2 : Real.pi / 2 - 0 = Real.pi / 2 := by ring
      rw [e1, e2] at h
      exact h
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [Real.pi_pos])] at h2
    exact h2.mono_set Set.Ioo_subset_Ioc_self
  have hmaj : IntegrableOn (fun θ => A * (Real.pi / 2 - θ) ^ (1 - γ))
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := hIntW.const_mul A
  -- pointwise comparison with the majorant
  have hpt : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      (u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-γ) ≤ A * (Real.pi / 2 - θ) ^ (1 - γ) := by
    intro θ hθ
    have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
    have hy : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
    have h1 : (u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-γ)
        ≤ ((Real.pi / 2 - θ) * A) * (Real.pi / 2 - θ) ^ (-γ) :=
      mul_le_mul_of_nonneg_right (hkey θ hθ') (Real.rpow_nonneg hy.le _)
    have h2 : ((Real.pi / 2 - θ) * A) * (Real.pi / 2 - θ) ^ (-γ)
        = A * (Real.pi / 2 - θ) ^ (1 - γ) := by
      rw [show (1 : ℝ) - γ = 1 + (-γ) by ring, Real.rpow_add hy, Real.rpow_one]
      ring
    linarith [h1, h2]
  have hLHSint : IntegrableOn (fun θ => (u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-γ))
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
    refine Integrable.mono hmaj ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
      refine ((hcont.mono ?_).pow 2).mul
        ((continuousOn_const.sub continuousOn_id).rpow_const
          (fun x hx => Or.inl (by
            have hpx : 0 < Real.pi / 2 - x := by linarith [hx.2]
            exact ne_of_gt hpx)))
      intro x hx
      exact ⟨le_of_lt (by linarith [Real.pi_pos, hx.1]), hx.2.le⟩
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      have hfnn : 0 ≤ (u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-γ) :=
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by linarith [hθ.2]) _)
      have hgnn : 0 ≤ A * (Real.pi / 2 - θ) ^ (1 - γ) :=
        mul_nonneg hA0 (Real.rpow_nonneg (by linarith [hθ.2]) _)
      calc ‖(u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-γ)‖ = (u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-γ) := by
            rw [Real.norm_eq_abs, abs_of_nonneg hfnn]
        _ ≤ A * (Real.pi / 2 - θ) ^ (1 - γ) := hpt θ hθ
        _ = ‖A * (Real.pi / 2 - θ) ^ (1 - γ)‖ := by
            rw [Real.norm_eq_abs, abs_of_nonneg hgnn]
  have hmain : (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
        (u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-γ))
      ≤ ∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), A * (Real.pi / 2 - θ) ^ (1 - γ) :=
    MeasureTheory.integral_mono_ae hLHSint hmaj
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
        exact hpt θ hθ)
  rw [MeasureTheory.integral_const_mul] at hmain
  calc (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), (u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-γ))
      ≤ A * (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), (Real.pi / 2 - θ) ^ (1 - γ)) := hmain
    _ = A * ((Real.pi / 4) ^ (2 - γ) / (2 - γ)) := by rw [hInt']
    _ ≤ A * 2 := mul_le_mul_of_nonneg_left hbnd hA0
    _ = 2 * A := by ring
    _ = 2 * ∫ θ in Set.Ioo 0 (Real.pi / 2), (deriv u θ) ^ 2 := by rw [hA]

theorem vTwoW4NIdents (u : ℝ → ℝ) (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2))) :
    (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Real.cos θ) ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ
        = (Real.cos θ) ^ 2 * deriv (deriv u) θ + 2 * Real.cos θ * Real.sin θ * deriv u θ
          + ((Real.cos θ) ^ 2 + 2 * (Real.sin θ) ^ 2) * u θ)
    ∧ (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv (fun θ => (Real.cos θ) ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ) θ
        = (Real.cos θ) ^ 2 * (deriv (deriv (deriv u)) θ + 3 * deriv u θ)
          + 2 * Real.cos θ * Real.sin θ * u θ)
    ∧ ContDiffOn ℝ 1
        (fun θ => (Real.cos θ) ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ)
        (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
  have hCpos : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 < Real.cos θ :=
    fun θ hθ => Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  -- ## Conjunct 1
  have hconj1 : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Real.cos θ) ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ
        = (Real.cos θ) ^ 2 * deriv (deriv u) θ + 2 * Real.cos θ * Real.sin θ * deriv u θ
          + ((Real.cos θ) ^ 2 + 2 * (Real.sin θ) ^ 2) * u θ := by
    intro θ hθ
    have hC := (hCpos θ hθ).ne'
    have h1 := (Work.FTS.EllipticEst.remov.slice5_v_rel_pure u hu θ hθ).1
    have h2 := Work.FTS.EllipticEst.remov.slice5_v_rel_one u hu θ hθ
    have ha : Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ
        - deriv (deriv u) θ - 2 * Real.sin θ * deriv (fun t => u t / Real.cos t) θ
        - Real.cos θ * (u θ / Real.cos θ) = 0 := by linarith [h1]
    have hb : Real.cos θ * deriv (fun t => u t / Real.cos t) θ
        - deriv u θ - Real.sin θ * (u θ / Real.cos θ) = 0 := by linarith [h2]
    have hc : Real.cos θ * (u θ / Real.cos θ) - u θ = 0 := by
      field_simp
      ring
    have hCv : Real.cos θ * deriv (fun t => u t / Real.cos t) θ
        = deriv u θ + Real.sin θ * (u θ / Real.cos θ) := by linarith [h2]
    have hCu : Real.cos θ * (u θ / Real.cos θ) = u θ := by field_simp
    have hCv2 : Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ
        = deriv (deriv u) θ + 2 * Real.sin θ * deriv (fun t => u t / Real.cos t) θ
          + Real.cos θ * (u θ / Real.cos θ) := by linarith [h1]
    have step3 : (Real.cos θ) ^ 2 * deriv (fun t => u t / Real.cos t) θ
        = Real.cos θ * deriv u θ + Real.sin θ * u θ := by
      rw [show (Real.cos θ) ^ 2 * deriv (fun t => u t / Real.cos t) θ
          = Real.cos θ * (Real.cos θ * deriv (fun t => u t / Real.cos t) θ) by ring, hCv,
        mul_add]
      rw [show Real.cos θ * (Real.sin θ * (u θ / Real.cos θ)) = Real.sin θ * (Real.cos θ * (u θ / Real.cos θ)) by ring,
        hCu]
    rw [show (Real.cos θ) ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ
        = (Real.cos θ) ^ 2 * (Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ) by ring,
      hCv2]
    rw [show (Real.cos θ) ^ 2 * (deriv (deriv u) θ + 2 * Real.sin θ * deriv (fun t => u t / Real.cos t) θ
          + Real.cos θ * (u θ / Real.cos θ))
        = (Real.cos θ) ^ 2 * deriv (deriv u) θ
          + 2 * Real.sin θ * ((Real.cos θ) ^ 2 * deriv (fun t => u t / Real.cos t) θ)
          + (Real.cos θ) ^ 2 * (Real.cos θ * (u θ / Real.cos θ)) by ring]
    rw [step3, hCu]
    ring
  refine ⟨hconj1, ?_, ?_⟩
  · intro θ hθ
    have hmem : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
    have hev : (fun θ' => (Real.cos θ') ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ')
        =ᶠ[𝓝 θ] fun θ' => (Real.cos θ') ^ 2 * deriv (deriv u) θ'
            + 2 * Real.cos θ' * Real.sin θ' * deriv u θ'
            + ((Real.cos θ') ^ 2 + 2 * (Real.sin θ') ^ 2) * u θ' := by
      filter_upwards [hmem] with t ht
      exact hconj1 t ht
    have h1 : ContDiffOn ℝ 3 (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
      hu.deriv_of_isOpen isOpen_Ioo (by norm_num)
    have h2 : ContDiffOn ℝ 2 (deriv (deriv u)) (Set.Ioo 0 (Real.pi / 2)) :=
      h1.deriv_of_isOpen isOpen_Ioo (by norm_num)
    have h1d : DifferentiableAt ℝ (deriv u) θ :=
      (h1.differentiableOn (by norm_num)).differentiableAt hmem
    have h2d : DifferentiableAt ℝ (deriv (deriv u)) θ :=
      (h2.differentiableOn (by norm_num)).differentiableAt hmem
    have hud : DifferentiableAt ℝ u θ :=
      (hu.differentiableOn (by norm_num)).differentiableAt hmem
    have hd1 : HasDerivAt (fun θ' => (Real.cos θ') ^ 2 * deriv (deriv u) θ')
        ((Real.cos θ) ^ 2 * deriv (deriv (deriv u)) θ
          + (2 * Real.cos θ * (-Real.sin θ)) * deriv (deriv u) θ) θ := by
      refine (((Real.hasDerivAt_cos θ).pow 2).mul h2d.hasDerivAt).congr_deriv ?_
      simp only [Pi.pow_apply]
      ring
    have hd2 : HasDerivAt (fun θ' => 2 * Real.cos θ' * Real.sin θ' * deriv u θ')
        (2 * (Real.cos θ * Real.cos θ - Real.sin θ * Real.sin θ) * deriv u θ
          + (2 * Real.cos θ * Real.sin θ) * deriv (deriv u) θ) θ := by
      refine ((((Real.hasDerivAt_cos θ).const_mul 2).mul (Real.hasDerivAt_sin θ)).mul
        h1d.hasDerivAt).congr_deriv ?_
      simp only [Pi.mul_apply]
      ring
    have hd3 : HasDerivAt (fun θ' => ((Real.cos θ') ^ 2 + 2 * (Real.sin θ') ^ 2) * u θ')
        ((2 * Real.cos θ * Real.sin θ) * u θ
          + ((Real.cos θ) ^ 2 + 2 * (Real.sin θ) ^ 2) * deriv u θ) θ := by
      refine ((((Real.hasDerivAt_cos θ).pow 2).add
        (((Real.hasDerivAt_sin θ).pow 2).const_mul 2)).mul hud.hasDerivAt).congr_deriv ?_
      simp only [Pi.pow_apply, Pi.add_apply]
      ring
    have hfun : (fun θ' => (Real.cos θ') ^ 2 * deriv (deriv u) θ'
          + 2 * Real.cos θ' * Real.sin θ' * deriv u θ'
          + ((Real.cos θ') ^ 2 + 2 * (Real.sin θ') ^ 2) * u θ')
        = ((fun θ' => (Real.cos θ') ^ 2 * deriv (deriv u) θ')
            + fun θ' => 2 * Real.cos θ' * Real.sin θ' * deriv u θ')
          + fun θ' => ((Real.cos θ') ^ 2 + 2 * (Real.sin θ') ^ 2) * u θ' := by
      funext x
      simp only [Pi.add_apply]
    rw [hev.deriv_eq, hfun, ((hd1.add hd2).add hd3).deriv]
    ring
  · -- ## Conjunct 3
    have hsub : Set.Ioo (Real.pi / 4) (Real.pi / 2) ⊆ Set.Ioo 0 (Real.pi / 2) :=
      fun x hx => ⟨by linarith [Real.pi_pos, hx.1], hx.2⟩
    have hv : ContDiffOn ℝ 4 (fun t => u t / Real.cos t) (Set.Ioo 0 (Real.pi / 2)) :=
      hu.div Real.contDiff_cos.contDiffOn (fun t ht => (hCpos t ht).ne')
    have hv1 : ContDiffOn ℝ 3 (deriv (fun t => u t / Real.cos t)) (Set.Ioo 0 (Real.pi / 2)) :=
      hv.deriv_of_isOpen isOpen_Ioo (by norm_num)
    have hv2 : ContDiffOn ℝ 2 (deriv (deriv (fun t => u t / Real.cos t)))
        (Set.Ioo 0 (Real.pi / 2)) :=
      hv1.deriv_of_isOpen isOpen_Ioo (by norm_num)
    have hC3 : ContDiffOn ℝ 1 (fun θ : ℝ => (Real.cos θ) ^ 3) (Set.Ioo 0 (Real.pi / 2)) := by
      have h : ContDiffOn ℝ 1 (Real.cos ^ 3) (Set.Ioo 0 (Real.pi / 2)) :=
        ((Real.contDiff_cos (n := 1)) |>.contDiffOn).pow 3
      exact h.congr (fun x hx => by simp only [Pi.pow_apply])
    have hN : ContDiffOn ℝ 1
        (fun θ : ℝ => (Real.cos θ) ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ)
        (Set.Ioo 0 (Real.pi / 2)) := by
      refine ((hC3.mul (hv2.of_le (by norm_num))).congr ?_)
      intro x hx
      simp only [Pi.mul_apply]
    exact hN.mono hsub

lemma near_weight_id (γ : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2)) :
    (Real.sin (2 * θ)) ^ (4 - γ) / (Real.cos θ) ^ 8
      = (2 : ℝ) ^ (4 - γ) * (Real.sin θ) ^ (4 - γ) * (Real.cos θ) ^ (-4 - γ) := by
  have hθ0 : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ0.1, Real.pi_pos], by linarith [hθ0.2, Real.pi_pos]⟩
  have hSp : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0.1 (by linarith [hθ0.2, Real.pi_pos])
  have hid1 : (2 * Real.sin θ * Real.cos θ) ^ (4 - γ)
      = (2 * Real.sin θ) ^ (4 - γ) * (Real.cos θ) ^ (4 - γ) :=
    Real.mul_rpow (by positivity) hc.le
  have hid2 : (2 * Real.sin θ) ^ (4 - γ) = (2 : ℝ) ^ (4 - γ) * (Real.sin θ) ^ (4 - γ) :=
    Real.mul_rpow (by norm_num) hSp.le
  have hden : (Real.cos θ) ^ 8 = (Real.cos θ) ^ (8 : ℝ) := (Real.rpow_natCast (Real.cos θ) 8).symm
  rw [Real.sin_two_mul, hid1, hid2, hden,
    show (2 : ℝ) ^ (4 - γ) * (Real.sin θ) ^ (4 - γ) * (Real.cos θ) ^ (4 - γ) / (Real.cos θ) ^ (8 : ℝ)
        = (2 : ℝ) ^ (4 - γ) * (Real.sin θ) ^ (4 - γ)
          * ((Real.cos θ) ^ (4 - γ) / (Real.cos θ) ^ (8 : ℝ)) by ring,
    ← Real.rpow_sub hc, show (4 : ℝ) - γ - 8 = -4 - γ by ring]

lemma near_weight_le (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2)) :
    (Real.sin (2 * θ)) ^ (4 - γ) / (Real.cos θ) ^ 8
      ≤ 512 * (Real.pi / 2 - θ) ^ (-4 - γ) := by
  have hθ0 : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ0.1, Real.pi_pos], by linarith [hθ0.2, Real.pi_pos]⟩
  have hSp : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0.1 (by linarith [hθ0.2, Real.pi_pos])
  have hy : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
  have hCl : 2 / Real.pi * (Real.pi / 2 - θ) ≤ Real.cos θ := two_div_pi_mul_sub_le_cos hθ0
  have hhalf : (1/2 : ℝ) * (Real.pi / 2 - θ) ≤ Real.cos θ := by
    have hpi : (1/2 : ℝ) ≤ 2 / Real.pi := by
      rw [le_div_iff₀ (by linarith [Real.pi_pos])]; linarith [Real.pi_lt_four]
    nlinarith [hCl, hpi, hy]
  rw [near_weight_id γ hθ]
  have hS1 : (Real.sin θ) ^ (4 - γ) ≤ 1 :=
    Real.rpow_le_one hSp.le (Real.sin_le_one _) (by linarith)
  have h2g : (2 : ℝ) ^ (4 - γ) ≤ 8 := by
    have h1 : (2 : ℝ) ^ (4 - γ) ≤ (2 : ℝ) ^ (3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h3 : (2 : ℝ) ^ (3 : ℝ) = 8 := by norm_num
    linarith [h1, h3]
  have hCb : (Real.cos θ) ^ (-4 - γ) ≤ (2 : ℝ) ^ (4 + γ) * (Real.pi / 2 - θ) ^ (-4 - γ) := by
    have h1 : (Real.cos θ) ^ (-4 - γ) ≤ ((1/2 : ℝ) * (Real.pi / 2 - θ)) ^ (-4 - γ) :=
      Real.rpow_le_rpow_of_nonpos (z := -4 - γ) (by positivity) hhalf (by linarith)
    have h2 : ((1/2 : ℝ) * (Real.pi / 2 - θ)) ^ (-4 - γ)
        = (1/2 : ℝ) ^ (-4 - γ) * (Real.pi / 2 - θ) ^ (-4 - γ) :=
      Real.mul_rpow (by norm_num) hy.le
    have h3 : (1/2 : ℝ) ^ (-4 - γ) = (2 : ℝ) ^ (4 + γ) := by
      rw [show (1/2 : ℝ) = (2:ℝ)⁻¹ by norm_num, Real.inv_rpow (by norm_num : (0:ℝ) ≤ 2),
        show (-4 : ℝ) - γ = -(4 + γ) by ring, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      exact inv_inv _
    rw [h2, h3] at h1
    exact h1
  have hpi : (2 : ℝ) ^ (4 + γ) ≤ 64 := by
    have h1 : (2 : ℝ) ^ (4 + γ) ≤ (2 : ℝ) ^ (6 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h3 : (2 : ℝ) ^ (6 : ℝ) = 64 := by norm_num
    linarith [h1, h3]
  have hSnn : 0 ≤ (Real.sin θ) ^ (4 - γ) := Real.rpow_nonneg hSp.le _
  have hCnn : 0 ≤ (Real.cos θ) ^ (-4 - γ) := Real.rpow_nonneg hc.le _
  have h2nn : 0 ≤ (2 : ℝ) ^ (4 - γ) := Real.rpow_nonneg (by norm_num) _
  have hyn : 0 ≤ (Real.pi / 2 - θ) ^ (-4 - γ) := Real.rpow_nonneg hy.le _
  have h64 : 0 ≤ (2 : ℝ) ^ (4 + γ) := Real.rpow_nonneg (by norm_num) _
  calc (2 : ℝ) ^ (4 - γ) * (Real.sin θ) ^ (4 - γ) * (Real.cos θ) ^ (-4 - γ)
      ≤ 8 * 1 * ((2 : ℝ) ^ (4 + γ) * (Real.pi / 2 - θ) ^ (-4 - γ)) := by
        have h1 : (2 : ℝ) ^ (4 - γ) * (Real.sin θ) ^ (4 - γ) ≤ 8 * 1 :=
          mul_le_mul h2g hS1 hSnn (by norm_num)
        exact mul_le_mul h1 hCb hCnn (by positivity)
    _ ≤ 512 * (Real.pi / 2 - θ) ^ (-4 - γ) := by
        have h1 := mul_le_mul_of_nonneg_right hpi hyn
        linarith [h1]

lemma near_weight_ge (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2)) :
    (Real.pi / 2 - θ) ^ (-4 - γ)
      ≤ (Real.sin (2 * θ)) ^ (4 - γ) / (Real.cos θ) ^ 8 := by
  have hθ0 : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ0.1, Real.pi_pos], by linarith [hθ0.2, Real.pi_pos]⟩
  have hSp : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0.1 (by linarith [hθ0.2, Real.pi_pos])
  have hy : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
  have hCu : Real.cos θ ≤ Real.pi / 2 - θ := cos_le_sub hθ0
  have hSge : Real.sqrt 2 / 2 ≤ Real.sin θ := by
    have h := Real.sin_le_sin_of_le_of_le_pi_div_two (x := Real.pi / 4) (y := θ)
      (by linarith [Real.pi_pos]) hθ.2.le hθ.1.le
    rwa [Real.sin_pi_div_four] at h
  have hCge : (Real.pi / 2 - θ) ^ (-4 - γ) ≤ (Real.cos θ) ^ (-4 - γ) :=
    Real.rpow_le_rpow_of_nonpos (z := -4 - γ) hc hCu (by linarith)
  have h2S : Real.sqrt 2 ≤ (2 : ℝ) * Real.sin θ := by nlinarith [hSge]
  have hkey : 1 ≤ (2 : ℝ) ^ (4 - γ) * (Real.sin θ) ^ (4 - γ) := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hSp.le]
    calc (1 : ℝ) = (Real.sqrt 2) ^ (0 : ℝ) := by rw [Real.rpow_zero]
      _ ≤ (Real.sqrt 2) ^ (4 - γ) :=
          Real.rpow_le_rpow_of_exponent_le (by
            rw [← Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num) (by linarith)
      _ ≤ ((2 : ℝ) * Real.sin θ) ^ (4 - γ) :=
          Real.rpow_le_rpow (z := 4 - γ) (by norm_num) h2S (by linarith)
  have hCnn : 0 ≤ (Real.cos θ) ^ (-4 - γ) := Real.rpow_nonneg hc.le _
  rw [near_weight_id γ hθ]
  calc (Real.pi / 2 - θ) ^ (-4 - γ)
      ≤ (Real.cos θ) ^ (-4 - γ) := hCge
    _ = 1 * (Real.cos θ) ^ (-4 - γ) := by ring
    _ ≤ ((2 : ℝ) ^ (4 - γ) * (Real.sin θ) ^ (4 - γ)) * (Real.cos θ) ^ (-4 - γ) :=
        mul_le_mul_of_nonneg_right hkey hCnn
    _ = (2 : ℝ) ^ (4 - γ) * (Real.sin θ) ^ (4 - γ) * (Real.cos θ) ^ (-4 - γ) := by ring

/-- `cos θ ≥ √2/2` on `(0,π/4]`. -/
lemma half_le_cos_sq {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 4)) :
    (1 : ℝ) / 2 ≤ (Real.cos θ) ^ 2 := by
  have h1 : Real.cos θ ≥ Real.cos (Real.pi / 4) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (le_of_lt hθ.1) (by linarith [hθ.2, Real.pi_pos]) hθ.2.le
  rw [Real.cos_pi_div_four] at h1
  have h2 : (1 : ℝ) / 2 = (Real.sqrt 2 / 2) ^ 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [h2]
  exact pow_le_pow_left₀ (by positivity) h1 2

/-! ### Three weight comparisons on the near field `(π/4, π/2)` -/

/-- On the near field, `cos⁴θ · (π/2-θ)^{-2-γ} ≤ 2 (sin 2θ)^{2-γ}`. -/
lemma cos4_mul_sub_rpow_le_two (θ γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2)
    (hc : 0 < Real.cos θ) (hy : 0 < Real.pi / 2 - θ)
    (hCu : Real.cos θ ≤ Real.pi / 2 - θ)
    (hCy : Real.pi / 2 - θ ≤ Real.pi / 2 * Real.cos θ)
    (hCS : Real.cos θ ≤ Real.sin (2 * θ)) (hs : 0 < Real.sin (2 * θ)) :
    (Real.cos θ) ^ 4 * (Real.pi / 2 - θ) ^ (-2 - γ) ≤ 2 * (Real.sin (2 * θ)) ^ (2 - γ) := by
  have hyl : 0 ≤ Real.pi / 2 - θ := hy.le
  have hc4 : (Real.cos θ) ^ 4 ≤ (Real.pi / 2 - θ) ^ 4 := pow_le_pow_left₀ hc.le hCu 4
  have hy4 : (Real.pi / 2 - θ) ^ 4 = (Real.pi / 2 - θ) ^ (4 : ℝ) := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hstep1 : (Real.cos θ) ^ 4 * (Real.pi / 2 - θ) ^ (-2 - γ)
      ≤ (Real.pi / 2 - θ) ^ 4 * (Real.pi / 2 - θ) ^ (-2 - γ) :=
    mul_le_mul_of_nonneg_right hc4 (Real.rpow_nonneg hyl _)
  have hstep2 : (Real.pi / 2 - θ) ^ 4 * (Real.pi / 2 - θ) ^ (-2 - γ)
      = (Real.pi / 2 - θ) ^ (2 - γ) := by
    rw [hy4, ← Real.rpow_add hy]
    congr 1
    ring
  have hstep3 : (Real.pi / 2 - θ) ^ (2 - γ) ≤ (Real.pi / 2 * Real.cos θ) ^ (2 - γ) :=
    Real.rpow_le_rpow hyl hCy (by linarith)
  have hstep4 : (Real.pi / 2 * Real.cos θ) ^ (2 - γ)
      = (Real.pi / 2) ^ (2 - γ) * (Real.cos θ) ^ (2 - γ) :=
    Real.mul_rpow (by linarith [Real.pi_pos]) hc.le
  have h4 : (Real.pi / 2) ^ (2 - γ) ≤ 2 := by
    have h5 : (Real.pi / 2) ^ (2 - γ) ≤ (2 : ℝ) ^ (2 - γ) :=
      Real.rpow_le_rpow (by linarith [Real.pi_pos]) (by linarith [Real.pi_lt_four]) (by linarith)
    have h6 : (2 : ℝ) ^ (2 - γ) ≤ 2 := by
      have h7 : (2 : ℝ) ^ (2 - γ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      rwa [Real.rpow_one] at h7
    linarith
  have h5 : (Real.cos θ) ^ (2 - γ) ≤ (Real.sin (2 * θ)) ^ (2 - γ) :=
    Real.rpow_le_rpow hc.le hCS (by linarith)
  have hstep5 : (Real.pi / 2) ^ (2 - γ) * (Real.cos θ) ^ (2 - γ)
      ≤ 2 * (Real.sin (2 * θ)) ^ (2 - γ) :=
    mul_le_mul h4 h5 (Real.rpow_nonneg hc.le _) (by norm_num)
  linarith [hstep1, hstep2, hstep3, hstep4, hstep5]

/-- On the near field, `cos⁴θ · (π/2-θ)^{-2-γ} ≤ 1`. -/
lemma cos4_mul_sub_rpow_le_one (θ γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2)
    (hc : 0 < Real.cos θ) (hy : 0 < Real.pi / 2 - θ)
    (hCu : Real.cos θ ≤ Real.pi / 2 - θ) (hy1 : Real.pi / 2 - θ ≤ 1) :
    (Real.cos θ) ^ 4 * (Real.pi / 2 - θ) ^ (-2 - γ) ≤ 1 := by
  have hyl : 0 ≤ Real.pi / 2 - θ := hy.le
  have hc4 : (Real.cos θ) ^ 4 ≤ (Real.pi / 2 - θ) ^ 4 := pow_le_pow_left₀ hc.le hCu 4
  have hy4 : (Real.pi / 2 - θ) ^ 4 = (Real.pi / 2 - θ) ^ (4 : ℝ) := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hstep1 : (Real.cos θ) ^ 4 * (Real.pi / 2 - θ) ^ (-2 - γ)
      ≤ (Real.pi / 2 - θ) ^ 4 * (Real.pi / 2 - θ) ^ (-2 - γ) :=
    mul_le_mul_of_nonneg_right hc4 (Real.rpow_nonneg hyl _)
  have hstep2 : (Real.pi / 2 - θ) ^ 4 * (Real.pi / 2 - θ) ^ (-2 - γ)
      = (Real.pi / 2 - θ) ^ (2 - γ) := by
    rw [hy4, ← Real.rpow_add hy]
    congr 1
    ring
  have hstep3 : (Real.pi / 2 - θ) ^ (2 - γ) ≤ 1 := Real.rpow_le_one hyl hy1 (by linarith)
  linarith [hstep1, hstep2, hstep3]

/-- On the near field, `cos²θ · (π/2-θ)^{-2-γ} ≤ (π/2-θ)^{-γ}`. -/
lemma cos2_mul_sub_rpow_le (θ γ : ℝ)
    (hc : 0 < Real.cos θ) (hy : 0 < Real.pi / 2 - θ)
    (hCu : Real.cos θ ≤ Real.pi / 2 - θ) :
    (Real.cos θ) ^ 2 * (Real.pi / 2 - θ) ^ (-2 - γ) ≤ (Real.pi / 2 - θ) ^ (-γ) := by
  have hyl : 0 ≤ Real.pi / 2 - θ := hy.le
  have hc2 : (Real.cos θ) ^ 2 ≤ (Real.pi / 2 - θ) ^ 2 := pow_le_pow_left₀ hc.le hCu 2
  have hy2 : (Real.pi / 2 - θ) ^ 2 = (Real.pi / 2 - θ) ^ (2 : ℝ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hstep1 : (Real.cos θ) ^ 2 * (Real.pi / 2 - θ) ^ (-2 - γ)
      ≤ (Real.pi / 2 - θ) ^ 2 * (Real.pi / 2 - θ) ^ (-2 - γ) :=
    mul_le_mul_of_nonneg_right hc2 (Real.rpow_nonneg hyl _)
  have hstep2 : (Real.pi / 2 - θ) ^ 2 * (Real.pi / 2 - θ) ^ (-2 - γ)
      = (Real.pi / 2 - θ) ^ (-γ) := by
    rw [hy2, ← Real.rpow_add hy]
    congr 1
    ring
  linarith [hstep1, hstep2]

/-- The global identity `(v'')²·σ₄/cos²θ = (cos³θ v'')²·σ₄/cos⁸θ`. -/
lemma F_eq_N (u : ℝ → ℝ) (γ : ℝ) (θ : ℝ) :
    (deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2
        * ((Real.sin (2 * θ)) ^ (4 - γ) / (Real.cos θ) ^ 2)
      = ((Real.cos θ) ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2
        * ((Real.sin (2 * θ)) ^ (4 - γ) / (Real.cos θ) ^ 8) := by
  by_cases hc : Real.cos θ = 0
  · simp [hc]
  · field_simp

/-- The far-field pointwise bound, with the weight `sEta` absorbed in the `u''`-term. -/
lemma far_F_le (u : ℝ → ℝ) (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2)
    (hu4 : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2))) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 4)) :
    (deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2
        * ((Real.sin (2 * θ)) ^ (4 - γ) / (Real.cos θ) ^ 2)
      ≤ 48 * ((deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        + 192 * (deriv u θ) ^ 2 + 432 * (u θ) ^ 2 := by
  have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hsnn : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hc2 : (1 : ℝ) / 2 ≤ (Real.cos θ) ^ 2 := half_le_cos_sq hθ
  have hsEta : 1 ≤ Work.FTS.EllipticEst.sEta θ := one_le_sEta_Ioo hθ'
  have hN1 := (vTwoW4NIdents u hu4).1 θ hθ'
  have hw : (Real.sin (2 * θ)) ^ (4 - γ) / (Real.cos θ) ^ 8 ≤ 16 := by
    have h1 : (Real.sin (2 * θ)) ^ (4 - γ) ≤ 1 :=
      Real.rpow_le_one hsnn (Real.sin_le_one _) (by linarith)
    have h2 : (1 : ℝ) / 16 ≤ (Real.cos θ) ^ 8 := by
      have h3 : ((1 : ℝ) / 2) ^ 4 ≤ ((Real.cos θ) ^ 2) ^ 4 := pow_le_pow_left₀ (by norm_num) hc2 4
      calc (1 : ℝ) / 16 = ((1 : ℝ) / 2) ^ 4 := by norm_num
        _ ≤ ((Real.cos θ) ^ 2) ^ 4 := h3
        _ = (Real.cos θ) ^ 8 := by ring
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (Real.cos θ) ^ 8)]
    linarith [h1, h2]
  rw [F_eq_N u γ θ]
  have hN2 : ((Real.cos θ) ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2
      ≤ 3 * ((deriv (deriv u) θ) ^ 2 + 4 * (deriv u θ) ^ 2 + 9 * (u θ) ^ 2) := by
    rw [hN1]
    have hsq : ((Real.cos θ) ^ 2 * deriv (deriv u) θ + 2 * Real.cos θ * Real.sin θ * deriv u θ
          + ((Real.cos θ) ^ 2 + 2 * (Real.sin θ) ^ 2) * u θ) ^ 2
        ≤ 3 * (((Real.cos θ) ^ 2 * deriv (deriv u) θ) ^ 2
          + (2 * Real.cos θ * Real.sin θ * deriv u θ) ^ 2
          + (((Real.cos θ) ^ 2 + 2 * (Real.sin θ) ^ 2) * u θ) ^ 2) := by
      nlinarith [sq_nonneg ((Real.cos θ) ^ 2 * deriv (deriv u) θ
            - 2 * Real.cos θ * Real.sin θ * deriv u θ),
        sq_nonneg (2 * Real.cos θ * Real.sin θ * deriv u θ
            - ((Real.cos θ) ^ 2 + 2 * (Real.sin θ) ^ 2) * u θ),
        sq_nonneg (((Real.cos θ) ^ 2 + 2 * (Real.sin θ) ^ 2) * u θ
            - (Real.cos θ) ^ 2 * deriv (deriv u) θ)]
    have hC2 : (Real.cos θ) ^ 2 ≤ 1 := by nlinarith [Real.cos_sq_le_one θ]
    have hCS : (2 * Real.cos θ * Real.sin θ) ^ 2 ≤ 1 := by
      nlinarith [Real.cos_sq_add_sin_sq θ, hC2, Real.sin_sq_le_one θ]
    have hCoef : ((Real.cos θ) ^ 2 + 2 * (Real.sin θ) ^ 2) ^ 2 ≤ 9 := by
      have h1 : (Real.cos θ) ^ 2 + 2 * (Real.sin θ) ^ 2 ≤ 3 := by
        nlinarith [Real.cos_sq_add_sin_sq θ, hC2, Real.sin_sq_le_one θ]
      nlinarith [h1, show (0 : ℝ) ≤ (Real.cos θ) ^ 2 + 2 * (Real.sin θ) ^ 2 by positivity]
    have ha : ((Real.cos θ) ^ 2 * deriv (deriv u) θ) ^ 2 ≤ (deriv (deriv u) θ) ^ 2 * 1 := by
      have hC4 : ((Real.cos θ) ^ 2) ^ 2 ≤ 1 := by nlinarith [hC2, sq_nonneg ((Real.cos θ) ^ 2)]
      calc ((Real.cos θ) ^ 2 * deriv (deriv u) θ) ^ 2
          = ((Real.cos θ) ^ 2) ^ 2 * (deriv (deriv u) θ) ^ 2 := by ring
        _ ≤ 1 * (deriv (deriv u) θ) ^ 2 := mul_le_mul_of_nonneg_right hC4 (sq_nonneg _)
        _ = (deriv (deriv u) θ) ^ 2 * 1 := by ring
    have hb : (2 * Real.cos θ * Real.sin θ * deriv u θ) ^ 2 ≤ 4 * (deriv u θ) ^ 2 := by
      nlinarith [hCS, sq_nonneg (deriv u θ)]
    have hcc : (((Real.cos θ) ^ 2 + 2 * (Real.sin θ) ^ 2) * u θ) ^ 2 ≤ 9 * (u θ) ^ 2 := by
      nlinarith [hCoef, sq_nonneg (u θ)]
    linarith [hsq, ha, hb, hcc]
  have hstep : ((Real.cos θ) ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2
        * ((Real.sin (2 * θ)) ^ (4 - γ) / (Real.cos θ) ^ 8)
      ≤ (3 * ((deriv (deriv u) θ) ^ 2 + 4 * (deriv u θ) ^ 2 + 9 * (u θ) ^ 2)) * 16 := by
    refine mul_le_mul hN2 hw (by positivity) (by positivity)
  have hbig : (3 * ((deriv (deriv u) θ) ^ 2 + 4 * (deriv u θ) ^ 2 + 9 * (u θ) ^ 2)) * 16
      ≤ 48 * ((deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        + 192 * (deriv u θ) ^ 2 + 432 * (u θ) ^ 2 := by
    have h1 : (deriv (deriv u) θ) ^ 2 ≤ (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
      nlinarith [sq_nonneg (deriv (deriv u) θ), hsEta]
    nlinarith [h1, sq_nonneg (deriv u θ), sq_nonneg (u θ), hsEta]
  linarith [hstep, hbig]

/-- Near-field comparison of the left-hand integrand with the Agmon weight. -/
lemma near_F_le (u : ℝ → ℝ) (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2)) :
    (deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2
        * ((Real.sin (2 * θ)) ^ (4 - γ) / (Real.cos θ) ^ 2)
      ≤ 512 * (((Real.cos θ) ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2
        * (Real.pi / 2 - θ) ^ (-4 - γ)) := by
  rw [F_eq_N u γ θ]
  have hw := near_weight_le γ hγ1 hγ2 hθ
  have hnn : 0 ≤ ((Real.cos θ) ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 :=
    sq_nonneg _
  calc ((Real.cos θ) ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2
        * ((Real.sin (2 * θ)) ^ (4 - γ) / (Real.cos θ) ^ 8)
      ≤ ((Real.cos θ) ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2
        * (512 * (Real.pi / 2 - θ) ^ (-4 - γ)) := mul_le_mul_of_nonneg_left hw hnn
    _ = 512 * (((Real.cos θ) ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2
        * (Real.pi / 2 - θ) ^ (-4 - γ)) := by ring

/-- Near-field bound for `(deriv N)²` with the Agmon weight. -/
lemma near_Nd_le (u : ℝ → ℝ) (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2)
    (hu4 : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2))) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2)) :
    (deriv (fun θ' => (Real.cos θ') ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ') θ) ^ 2
        * (Real.pi / 2 - θ) ^ (-2 - γ)
      ≤ 8 * ((deriv (deriv (deriv u)) θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ))
        + 64 * (deriv u θ) ^ 2 + 8 * ((u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-γ)) := by
  have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
  have hc : 0 < Real.cos θ := cos_pos_of_mem_Ioo hθ'
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos]) (by linarith [hθ.2, Real.pi_pos])
  have hy : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
  have hyl : 0 ≤ Real.pi / 2 - θ := hy.le
  have hy1 : Real.pi / 2 - θ ≤ 1 := by linarith [Real.pi_lt_four, hθ.1]
  have hCu : Real.cos θ ≤ Real.pi / 2 - θ := cos_le_sub hθ'
  have hCy : Real.pi / 2 - θ ≤ Real.pi / 2 * Real.cos θ := by
    have h := two_div_pi_mul_sub_le_cos hθ'
    have h2 : Real.pi / 2 * (2 / Real.pi * (Real.pi / 2 - θ)) ≤ Real.pi / 2 * Real.cos θ :=
      mul_le_mul_of_nonneg_left h (by linarith [Real.pi_pos])
    have h3 : Real.pi / 2 * (2 / Real.pi * (Real.pi / 2 - θ)) = Real.pi / 2 - θ := by
      field_simp
    linarith [h2, h3]
  have hSge : Real.sqrt 2 / 2 ≤ Real.sin θ := by
    have h := Real.sin_le_sin_of_le_of_le_pi_div_two (x := Real.pi / 4) (y := θ)
      (by linarith [Real.pi_pos]) hθ.2.le hθ.1.le
    rwa [Real.sin_pi_div_four] at h
  have hCS : Real.cos θ ≤ Real.sin (2 * θ) := by
    have h1 : (1:ℝ) ≤ 2 * Real.sin θ := by
      have h2 : Real.sqrt 2 ≤ 2 * Real.sin θ := by nlinarith [hSge, Real.one_le_sqrt.mpr (by norm_num : (1:ℝ) ≤ 2)]
      nlinarith [h2, Real.one_le_sqrt.mpr (by norm_num : (1:ℝ) ≤ 2)]
    rw [Real.sin_two_mul]
    nlinarith [h1, hc]
  set C4 : ℝ := (Real.cos θ) ^ 4 * (Real.pi / 2 - θ) ^ (-2 - γ) with hC4def
  set C2 : ℝ := (Real.cos θ) ^ 2 * (Real.pi / 2 - θ) ^ (-2 - γ) with hC2def
  set S2 : ℝ := (Real.sin (2 * θ)) ^ (2 - γ) with hS2def
  set Y : ℝ := (Real.pi / 2 - θ) ^ (-γ) with hYdef
  have hkey1 : C4 ≤ 2 * S2 :=
    cos4_mul_sub_rpow_le_two θ γ hγ1 hγ2 hc hy hCu hCy hCS hs
  have hkey2 : C4 ≤ 1 := cos4_mul_sub_rpow_le_one θ γ hγ1 hγ2 hc hy hCu hy1
  have hkey3 : C2 ≤ Y := cos2_mul_sub_rpow_le θ γ hc hy hCu
  have hy2g : 0 ≤ (Real.pi / 2 - θ) ^ (-2 - γ) := Real.rpow_nonneg hyl _
  rw [show (deriv (fun θ' => (Real.cos θ') ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ') θ)
      = (Real.cos θ) ^ 2 * (deriv (deriv (deriv u)) θ + 3 * deriv u θ)
        + 2 * Real.cos θ * Real.sin θ * u θ from (vTwoW4NIdents u hu4).2.1 θ hθ']
  have hsq : ((Real.cos θ) ^ 2 * (deriv (deriv (deriv u)) θ + 3 * deriv u θ)
        + 2 * Real.cos θ * Real.sin θ * u θ) ^ 2
      ≤ 2 * ((Real.cos θ) ^ 2 * (deriv (deriv (deriv u)) θ + 3 * deriv u θ)) ^ 2
        + 2 * (2 * Real.cos θ * Real.sin θ * u θ) ^ 2 := by
    nlinarith [sq_nonneg ((Real.cos θ) ^ 2 * (deriv (deriv (deriv u)) θ + 3 * deriv u θ)
      - 2 * Real.cos θ * Real.sin θ * u θ)]
  have hsqm : ((Real.cos θ) ^ 2 * (deriv (deriv (deriv u)) θ + 3 * deriv u θ)
        + 2 * Real.cos θ * Real.sin θ * u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-2 - γ)
      ≤ 2 * ((Real.cos θ) ^ 2 * (deriv (deriv (deriv u)) θ + 3 * deriv u θ)) ^ 2
          * (Real.pi / 2 - θ) ^ (-2 - γ)
        + 2 * (2 * Real.cos θ * Real.sin θ * u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-2 - γ) := by
    have := mul_le_mul_of_nonneg_right hsq hy2g
    linarith [this]
  have hA : 2 * ((Real.cos θ) ^ 2 * (deriv (deriv (deriv u)) θ + 3 * deriv u θ)) ^ 2
        * (Real.pi / 2 - θ) ^ (-2 - γ)
      ≤ 8 * ((deriv (deriv (deriv u)) θ) ^ 2 * S2) + 36 * (deriv u θ) ^ 2 := by
    have e1 : 2 * ((Real.cos θ) ^ 2 * (deriv (deriv (deriv u)) θ + 3 * deriv u θ)) ^ 2
        * (Real.pi / 2 - θ) ^ (-2 - γ)
      = 2 * C4 * (deriv (deriv (deriv u)) θ + 3 * deriv u θ) ^ 2 := by
      rw [hC4def]
      ring
    rw [e1]
    have hC4nn : 0 ≤ C4 := by rw [hC4def]; positivity
    have h3u : (deriv (deriv (deriv u)) θ + 3 * deriv u θ) ^ 2
        ≤ 2 * ((deriv (deriv (deriv u)) θ) ^ 2 + 9 * (deriv u θ) ^ 2) := by
      nlinarith [sq_nonneg (deriv (deriv (deriv u)) θ - 3 * deriv u θ)]
    have hstep : 2 * C4 * (deriv (deriv (deriv u)) θ + 3 * deriv u θ) ^ 2
        ≤ 2 * C4 * (2 * ((deriv (deriv (deriv u)) θ) ^ 2 + 9 * (deriv u θ) ^ 2)) :=
      mul_le_mul_of_nonneg_left h3u (by linarith)
    have hfin : 2 * C4 * (2 * ((deriv (deriv (deriv u)) θ) ^ 2 + 9 * (deriv u θ) ^ 2))
        ≤ 8 * ((deriv (deriv (deriv u)) θ) ^ 2 * S2) + 36 * (deriv u θ) ^ 2 := by
      have h1 : 4 * C4 * (deriv (deriv (deriv u)) θ) ^ 2
          ≤ 8 * S2 * (deriv (deriv (deriv u)) θ) ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith [hkey1]) (sq_nonneg _)
      have h2 : 36 * C4 * (deriv u θ) ^ 2 ≤ 36 * (deriv u θ) ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith [hkey2]) (sq_nonneg _)
      nlinarith [h1, h2]
    linarith [hstep, hfin]
  have hB : 2 * (2 * Real.cos θ * Real.sin θ * u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-2 - γ)
      ≤ 8 * ((u θ) ^ 2 * Y) := by
    have e1 : 2 * (2 * Real.cos θ * Real.sin θ * u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-2 - γ)
      = 8 * C2 * ((Real.sin θ) ^ 2 * (u θ) ^ 2) := by
      rw [hC2def]
      ring
    rw [e1]
    have hs1 : (Real.sin θ) ^ 2 ≤ 1 := Real.sin_sq_le_one θ
    have hu2 : 0 ≤ (u θ) ^ 2 := sq_nonneg _
    calc 8 * C2 * ((Real.sin θ) ^ 2 * (u θ) ^ 2)
        ≤ 8 * C2 * (1 * (u θ) ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs1 hu2) (by positivity)
      _ = 8 * (C2 * (u θ) ^ 2) := by ring
      _ ≤ 8 * (Y * (u θ) ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hkey3 hu2) (by norm_num)
      _ = 8 * ((u θ) ^ 2 * Y) := by ring
  linarith [hsqm, hA, hB, sq_nonneg (deriv u θ)]

/-! ### Integrability of the Agmon integrands on the near field -/

/-- `N² y^{-4-γ}` (`N = cos³θ v''`) is integrable on the near field. -/
lemma integrableOn_agF_near (u : ℝ → ℝ) (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2)
    (hu4 : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)))
    (hIntF : MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
        (Real.rpow (Real.sin (2 * θ)) (4 - γ) / (Real.cos θ) ^ 2))
      (Set.Ioo (Real.pi / 4) (Real.pi / 2))) :
    MeasureTheory.IntegrableOn
      (fun θ => ((Real.cos θ) ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
        (Real.pi / 2 - θ) ^ (-4 - γ)) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
  set s : Set ℝ := Set.Ioo (Real.pi / 4) (Real.pi / 2) with hs
  have hae : (fun θ => (Real.cos θ) ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ)
      =ᵐ[volume.restrict s]
      (fun θ => (Real.cos θ) ^ 2 * deriv (deriv u) θ + 2 * Real.cos θ * Real.sin θ * deriv u θ
        + ((Real.cos θ) ^ 2 + 2 * (Real.sin θ) ^ 2) * u θ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    exact (vTwoW4NIdents u hu4).1 θ ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hcos : AEStronglyMeasurable (fun θ : ℝ => Real.cos θ) (volume.restrict s) :=
    (Real.continuous_cos.continuousOn).aestronglyMeasurable measurableSet_Ioo
  have hsin : AEStronglyMeasurable (fun θ : ℝ => Real.sin θ) (volume.restrict s) :=
    (Real.continuous_sin.continuousOn).aestronglyMeasurable measurableSet_Ioo
  have hcc : AEStronglyMeasurable (fun θ : ℝ => (Real.cos θ) ^ 2) (volume.restrict s) := hcos.pow 2
  have hss : AEStronglyMeasurable (fun θ : ℝ => (Real.sin θ) ^ 2) (volume.restrict s) := hsin.pow 2
  have hu : AEStronglyMeasurable u (volume.restrict s) :=
    (hu4.continuousOn.mono (by
      intro x hx; exact ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩)).aestronglyMeasurable measurableSet_Ioo
  have hdu : AEStronglyMeasurable (deriv u) (volume.restrict s) :=
    (measurable_deriv u).aestronglyMeasurable
  have hddu : AEStronglyMeasurable (deriv (deriv u)) (volume.restrict s) :=
    (measurable_deriv (deriv u)).aestronglyMeasurable
  have hr1 : AEStronglyMeasurable (fun θ : ℝ => (Real.cos θ) ^ 2 * deriv (deriv u) θ)
      (volume.restrict s) := hcc.mul hddu
  have hr2 : AEStronglyMeasurable (fun θ : ℝ => 2 * Real.cos θ * Real.sin θ * deriv u θ)
      (volume.restrict s) := ((hcos.const_mul 2).mul hsin).mul hdu
  have hr3 : AEStronglyMeasurable (fun θ : ℝ => ((Real.cos θ) ^ 2 + 2 * (Real.sin θ) ^ 2) * u θ)
      (volume.restrict s) := (hcc.add (hss.const_mul 2)).mul hu
  have hrs : AEStronglyMeasurable
      (fun θ : ℝ => (Real.cos θ) ^ 2 * deriv (deriv u) θ + 2 * Real.cos θ * Real.sin θ * deriv u θ
        + ((Real.cos θ) ^ 2 + 2 * (Real.sin θ) ^ 2) * u θ) (volume.restrict s) := (hr1.add hr2).add hr3
  have hN : AEStronglyMeasurable
      (fun θ : ℝ => (Real.cos θ) ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ)
      (volume.restrict s) := (aestronglyMeasurable_congr hae).mpr hrs
  have hY : AEStronglyMeasurable (fun θ : ℝ => (Real.pi / 2 - θ) ^ (-4 - γ)) (volume.restrict s) :=
    ((continuousOn_const.sub continuousOn_id).rpow_const (fun x hx => Or.inl (by
      show ((Real.pi : ℝ) / 2 - x) ≠ 0
      linarith [hx.2]))).aestronglyMeasurable measurableSet_Ioo
  have hagF : AEStronglyMeasurable
      (fun θ : ℝ => ((Real.cos θ) ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2
        * (Real.pi / 2 - θ) ^ (-4 - γ)) (volume.restrict s) := (hN.pow 2).mul hY
  refine Integrable.mono' hIntF hagF ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
  have hN2 : 0 ≤ ((Real.cos θ) ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 := sq_nonneg _
  have hyn : 0 ≤ (Real.pi / 2 - θ) ^ (-4 - γ) := Real.rpow_nonneg (by linarith [hθ.2]) _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hN2 hyn)]
  calc ((Real.cos θ) ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2
        * (Real.pi / 2 - θ) ^ (-4 - γ)
      ≤ ((Real.cos θ) ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2
          * ((Real.sin (2 * θ)) ^ (4 - γ) / (Real.cos θ) ^ 8) :=
        mul_le_mul_of_nonneg_left (near_weight_ge γ hγ1 hγ2 hθ) hN2
    _ = (deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2
          * ((Real.sin (2 * θ)) ^ (4 - γ) / (Real.cos θ) ^ 2) := (F_eq_N u γ θ).symm

/-- `(deriv N)² y^{-2-γ}` is integrable on the near field. -/
lemma integrableOn_agFd_near (N : ℝ → ℝ) (γ : ℝ) (M : ℝ → ℝ)
    (hNd : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      (deriv N θ) ^ 2 * (Real.pi / 2 - θ) ^ (-2 - γ) ≤ M θ)
    (hMint : MeasureTheory.IntegrableOn M (Set.Ioo (Real.pi / 4) (Real.pi / 2))) :
    MeasureTheory.IntegrableOn (fun θ => (deriv N θ) ^ 2 * (Real.pi / 2 - θ) ^ (-2 - γ))
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
  set s : Set ℝ := Set.Ioo (Real.pi / 4) (Real.pi / 2) with hs
  have hY : AEStronglyMeasurable (fun θ : ℝ => (Real.pi / 2 - θ) ^ (-2 - γ)) (volume.restrict s) :=
    ((continuousOn_const.sub continuousOn_id).rpow_const (fun x hx => Or.inl (by
      show ((Real.pi : ℝ) / 2 - x) ≠ 0
      linarith [hx.2]))).aestronglyMeasurable measurableSet_Ioo
  have hf : AEStronglyMeasurable
      (fun θ : ℝ => (deriv N θ) ^ 2 * (Real.pi / 2 - θ) ^ (-2 - γ)) (volume.restrict s) :=
    ((measurable_deriv N).aestronglyMeasurable.pow 2).mul hY
  refine Integrable.mono' hMint hf ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
  have hd2 : 0 ≤ (deriv N θ) ^ 2 := sq_nonneg _
  have hyn : 0 ≤ (Real.pi / 2 - θ) ^ (-2 - γ) := Real.rpow_nonneg (by linarith [hθ.2]) _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hd2 hyn)]
  exact hNd θ hθ

/-! ### Splitting the `Iθ`-integral and the far-field estimate -/

/-- Split `∫_{[0,π/2]}` at `π/4`. -/
lemma integral_Iθ_split (f : ℝ → ℝ) (hf : MeasureTheory.IntegrableOn f Work.Spaces.Iθ) :
    ∫ θ in Work.Spaces.Iθ, f θ
      = (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 4), f θ)
        + (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), f θ) := by
  have hae : Set.Ioo (0 : ℝ) (Real.pi / 2) =ᵐ[volume]
      (Set.Ioo 0 (Real.pi / 4) ∪ Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
    rw [MeasureTheory.ae_eq_set]
    refine ⟨?_, ?_⟩
    · refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_singleton (Real.pi / 4))
      intro x hx
      simp only [Set.mem_sdiff, Set.mem_Ioo, Set.mem_union, Set.mem_singleton_iff] at hx ⊢
      obtain ⟨⟨h1, h2⟩, h3⟩ := hx
      rcases lt_trichotomy x (Real.pi / 4) with hlt | heq | hgt
      · exact absurd (Or.inl ⟨h1, hlt⟩) h3
      · exact heq
      · exact absurd (Or.inr ⟨hgt, h2⟩) h3
    · have hsub : (Set.Ioo 0 (Real.pi / 4) ∪ Set.Ioo (Real.pi / 4) (Real.pi / 2))
          ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
        intro x hx
        rcases hx with hx | hx
        · exact ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
        · exact ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩
      rw [Set.sdiff_eq_empty.mpr hsub]
      simp
  have h1 : ∫ θ in Work.Spaces.Iθ, f θ = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), f θ :=
    MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioo_ae_eq_Icc (μ := volume)).symm
  have h2 : ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), f θ
      = ∫ θ in (Set.Ioo 0 (Real.pi / 4) ∪ Set.Ioo (Real.pi / 4) (Real.pi / 2)), f θ :=
    MeasureTheory.setIntegral_congr_set hae
  have h3 : ∫ θ in (Set.Ioo 0 (Real.pi / 4) ∪ Set.Ioo (Real.pi / 4) (Real.pi / 2)), f θ
      = (∫ θ in Set.Ioo 0 (Real.pi / 4), f θ) + (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), f θ) := by
    refine MeasureTheory.setIntegral_union ?_ measurableSet_Ioo ?_ ?_
    · rw [Set.disjoint_left]; intro x hx1 hx2; linarith [hx1.2, hx2.1]
    · exact hf.mono_set (fun x hx => ⟨hx.1.le, by linarith [hx.2, Real.pi_pos]⟩)
    · exact hf.mono_set (fun x hx => ⟨by linarith [hx.1, Real.pi_pos], hx.2.le⟩)
  linarith [h1, h2, h3]

/-- Far-field integral bound for the left-hand side. -/
lemma farIntegral_le (u : ℝ → ℝ) (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2)
    (hu4 : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)))
    (hI2 : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 *
      Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ)
    (hI1 : MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ)
    (hI0 : MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ)
    (hFint : MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
        (Real.rpow (Real.sin (2 * θ)) (4 - γ) / (Real.cos θ) ^ 2)) (Set.Ioo 0 (Real.pi / 4))) :
    (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
        (deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
          (Real.rpow (Real.sin (2 * θ)) (4 - γ) / (Real.cos θ) ^ 2))
      ≤ 48 * (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        + 192 * (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
        + 432 * (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2) := by
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := by rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  have hsub : Set.Ioo (0 : ℝ) (Real.pi / 4) ⊆ Work.Spaces.Iθ := by
    intro x hx; refine ⟨hx.1.le, ?_⟩; have := Real.pi_pos; linarith [hx.2]
  have hAint : MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (Set.Ioo 0 (Real.pi / 4)) := hI2.mono_set hsub
  have hBint : MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 4)) := hI1.mono_set hsub
  have hCint : MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 4)) := hI0.mono_set hsub
  set M : ℝ → ℝ := fun θ => 48 * ((deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        + 192 * (deriv u θ) ^ 2 + 432 * (u θ) ^ 2 with hM
  have h1 : MeasureTheory.IntegrableOn
      (fun θ => 48 * ((deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      (Set.Ioo 0 (Real.pi / 4)) := hAint.const_mul 48
  have h2 : MeasureTheory.IntegrableOn (fun θ => 192 * (deriv u θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 4)) := hBint.const_mul 192
  have h3 : MeasureTheory.IntegrableOn (fun θ => 432 * (u θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 4)) := hCint.const_mul 432
  have h12 : MeasureTheory.IntegrableOn
      (fun θ => 48 * ((deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        + 192 * (deriv u θ) ^ 2) (Set.Ioo 0 (Real.pi / 4)) := h1.add h2
  have hMint : MeasureTheory.IntegrableOn M (Set.Ioo 0 (Real.pi / 4)) := by
    rw [hM]; exact h12.add h3
  have hmono : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
        (deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
          (Real.rpow (Real.sin (2 * θ)) (4 - γ) / (Real.cos θ) ^ 2))
      ≤ ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 4), M θ := by
    refine MeasureTheory.integral_mono_ae hFint hMint ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    exact far_F_le u γ hγ1 hγ2 hu4 hθ
  have hMval : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 4), M θ)
      = 48 * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
            (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        + 192 * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 4), (deriv u θ) ^ 2)
        + 432 * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 4), (u θ) ^ 2) := by
    simp only [hM]
    rw [MeasureTheory.integral_add h12 h3, MeasureTheory.integral_add h1 h2,
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul]
  have hnonnegA : ∀ x ∈ Work.Spaces.Iθ,
      0 ≤ (deriv (deriv u) x) ^ 2 * Work.FTS.EllipticEst.sEta x := fun x hx =>
    mul_nonneg (sq_nonneg _) (sEta_nonneg_Iθ hx)
  have e1 : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
        (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      ≤ ∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
    MeasureTheory.setIntegral_mono_set hI2
      (by filter_upwards [MeasureTheory.ae_restrict_mem hIθ_meas] with x hx; exact hnonnegA x hx)
      (Filter.Eventually.of_forall (fun x hx => hsub hx))
  have e2 : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 4), (deriv u θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 :=
    MeasureTheory.setIntegral_mono_set hI1
      (by filter_upwards [MeasureTheory.ae_restrict_mem hIθ_meas] with x hx; exact sq_nonneg _)
      (Filter.Eventually.of_forall (fun x hx => hsub hx))
  have e3 : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 4), (u θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 :=
    MeasureTheory.setIntegral_mono_set hI0
      (by filter_upwards [MeasureTheory.ae_restrict_mem hIθ_meas] with x hx; exact sq_nonneg _)
      (Filter.Eventually.of_forall (fun x hx => hsub hx))
  linarith [hmono, hMval, e1, e2, e3]

/-- Near-field integral estimate for the left-hand side. -/
lemma nearIntegral_le (u : ℝ → ℝ) (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2)
    (hu4 : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)))
    (huc : ContinuousOn u (Set.Icc 0 (Real.pi / 2))) (hπ : u (Real.pi / 2) = 0)
    (hI3 : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (deriv u)) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ)
    (hI1 : MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ)
    (hIntF : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
      (Real.rpow (Real.sin (2 * θ)) (4 - γ) / (Real.cos θ) ^ 2))
      (Set.Ioo (Real.pi / 4) (Real.pi / 2))) :
    (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
        (deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
        (Real.rpow (Real.sin (2 * θ)) (4 - γ) / (Real.cos θ) ^ 2))
      ≤ 2000 * (∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv u)) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (2 - γ))
        + 20000 * (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2) := by
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := by rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  have hsub : Set.Ioo (Real.pi / 4) (Real.pi / 2) ⊆ Work.Spaces.Iθ := fun x hx =>
    ⟨by linarith [hx.1, Real.pi_pos], hx.2.le⟩
  have hI1' : MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) :=
    hI1.mono_set (fun x hx => ⟨hx.1.le, hx.2.le⟩)
  have hu1 : ContDiffOn ℝ 1 u (Set.Ioo 0 (Real.pi / 2)) := hu4.of_le (by norm_num)
  set N : ℝ → ℝ := fun θ => (Real.cos θ) ^ 3 * deriv (deriv (fun t => u t / Real.cos t)) θ with hN
  set A3 : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv u)) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - γ) with hA3
  set A1 : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 with hA1
  set X : ℝ := ∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
      (N θ) ^ 2 * (Real.pi / 2 - θ) ^ (-4 - γ) with hX
  set Z : ℝ := ∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
      (deriv N θ) ^ 2 * (Real.pi / 2 - θ) ^ (-2 - γ) with hZ
  set U : ℝ := ∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
      (u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-γ) with hU
  set P : ℝ := ∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
      (deriv (deriv (deriv u)) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ) with hP
  set Q : ℝ := ∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), (deriv u θ) ^ 2 with hQ
  have hA3int : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (deriv u)) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - γ)) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
    hI3.mono_set hsub
  have hA1int : MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2)
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := hI1.mono_set hsub
  -- the pointwise bounds
  have hFpt : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      (deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
          (Real.rpow (Real.sin (2 * θ)) (4 - γ) / (Real.cos θ) ^ 2)
        ≤ 512 * ((N θ) ^ 2 * (Real.pi / 2 - θ) ^ (-4 - γ)) :=
    fun θ hθ => near_F_le u γ hγ1 hγ2 hθ
  have hNd : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      (deriv N θ) ^ 2 * (Real.pi / 2 - θ) ^ (-2 - γ)
        ≤ 8 * ((deriv (deriv (deriv u)) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
          + 64 * (deriv u θ) ^ 2 + 8 * ((u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-γ)) :=
    fun θ hθ => near_Nd_le u γ hγ1 hγ2 hu4 hθ
  -- integrability of the Agmon integrands
  have hNint : MeasureTheory.IntegrableOn (agF γ N) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
    integrableOn_agF_near u γ hγ1 hγ2 hu4 hIntF
  have hUint : MeasureTheory.IntegrableOn
      (fun θ => (u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-γ)) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
    integrableOn_sq_mul_sub_rpow γ hγ1 hγ2 u hu1 huc hπ hI1'
  have hM2int : MeasureTheory.IntegrableOn
      (fun θ => 8 * ((deriv (deriv (deriv u)) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
        + 64 * (deriv u θ) ^ 2 + 8 * ((u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-γ)))
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
    have h12 : MeasureTheory.IntegrableOn
        (fun θ => 8 * ((deriv (deriv (deriv u)) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
          + 64 * (deriv u θ) ^ 2) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
      (hA3int.const_mul 8).add (hA1int.const_mul 64)
    exact h12.add (hUint.const_mul 8)
  have hNdint : MeasureTheory.IntegrableOn
      (fun θ => (deriv N θ) ^ 2 * (Real.pi / 2 - θ) ^ (-2 - γ))
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
    integrableOn_agFd_near N γ
      (fun θ => 8 * ((deriv (deriv (deriv u)) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
        + 64 * (deriv u θ) ^ 2 + 8 * ((u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-γ))) hNd hM2int
  -- the Agmon inequality
  have hagmon : (2 + γ) * X ≤ Z := by
    have h := agmonWeightedHardy γ (Real.pi / 4) hγ1 hγ2 (by linarith [Real.pi_pos]) N
      (vTwoW4NIdents u hu4).2.2 hNint hNdint
    rw [hX, hZ]
    simpa only [agF, agFd] using h
  -- step 1: `∫ F ≤ 512 X`
  have hM1int : MeasureTheory.IntegrableOn
      (fun θ => 512 * ((N θ) ^ 2 * (Real.pi / 2 - θ) ^ (-4 - γ)))
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := hNint.const_mul 512
  have hmono1 : (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
        (deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
          (Real.rpow (Real.sin (2 * θ)) (4 - γ) / (Real.cos θ) ^ 2))
      ≤ ∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
          512 * ((N θ) ^ 2 * (Real.pi / 2 - θ) ^ (-4 - γ)) := by
    refine MeasureTheory.integral_mono_ae hIntF hM1int ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    exact hFpt θ hθ
  have hM1val : (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
        512 * ((N θ) ^ 2 * (Real.pi / 2 - θ) ^ (-4 - γ))) = 512 * X := by
    rw [hX, MeasureTheory.integral_const_mul]
  -- step 2: `X ≤ Z/3`
  have hXnn : 0 ≤ X := by
    rw [hX]
    refine MeasureTheory.setIntegral_nonneg measurableSet_Ioo ?_
    intro θ hθ
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by linarith [hθ.2]) _)
  have h2 : X ≤ Z / 3 := by
    have hm := hagmon
    rw [hX, hZ] at hm
    have h3 : (3 : ℝ) ≤ 2 + γ := by linarith
    nlinarith [hm, hXnn, h3]
  -- step 3: `Z ≤ 8 A3 + 64 A1 + 8 U`
  have hmono2 : Z ≤ ∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
      8 * ((deriv (deriv (deriv u)) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
        + 64 * (deriv u θ) ^ 2 + 8 * ((u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-γ)) := by
    rw [hZ]
    refine MeasureTheory.integral_mono_ae hNdint hM2int ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    exact hNd θ hθ
  have hM2val : (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
      8 * ((deriv (deriv (deriv u)) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
        + 64 * (deriv u θ) ^ 2 + 8 * ((u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-γ)))
      = 8 * P + 64 * Q + 8 * U := by
    have h8 : MeasureTheory.IntegrableOn
        (fun θ => 8 * ((u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-γ)))
        (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := hUint.const_mul 8
    have h12 : MeasureTheory.IntegrableOn
        (fun θ => 8 * ((deriv (deriv (deriv u)) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
          + 64 * (deriv u θ) ^ 2) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
      (hA3int.const_mul 8).add (hA1int.const_mul 64)
    rw [MeasureTheory.integral_add h12 h8,
        MeasureTheory.integral_add (hA3int.const_mul 8) (hA1int.const_mul 64),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul, hP, hQ, hU]
  have eP : P ≤ A3 := by
    rw [hP, hA3]
    refine MeasureTheory.setIntegral_mono_set hI3 ?_
      (Filter.Eventually.of_forall (fun x hx => hsub hx))
    filter_upwards [MeasureTheory.ae_restrict_mem hIθ_meas] with x hx
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hx) _)
  have eQ : Q ≤ A1 := by
    rw [hQ, hA1]
    refine MeasureTheory.setIntegral_mono_set hI1 ?_
      (Filter.Eventually.of_forall (fun x hx => hsub hx))
    filter_upwards [MeasureTheory.ae_restrict_mem hIθ_meas] with x hx
    exact sq_nonneg _
  have h4 : U ≤ 2 * A1 := by
    have hhardy := hardyUDivY γ hγ1 hγ2 u hu1 huc hπ hI1'
    have hupper : (∫ θ in Set.Ioo 0 (Real.pi / 2), (deriv u θ) ^ 2) ≤ A1 := by
      rw [hA1]
      refine MeasureTheory.setIntegral_mono_set hI1 ?_
        (Filter.Eventually.of_forall (fun x hx => ⟨hx.1.le, hx.2.le⟩))
      filter_upwards [MeasureTheory.ae_restrict_mem hIθ_meas] with x hx
      exact sq_nonneg _
    rw [← hU] at hhardy
    linarith [hhardy, hupper]
  linarith [hmono1, hM1val, h2, hmono2, hM2val, eP, eQ, h4]

theorem vTwoW4WeakAlt : ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u : ℝ → ℝ),
    1 ≤ γ → γ ≤ 3 / 2 →
    ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)) →
    ContinuousOn u (Set.Icc 0 (Real.pi / 2)) →
    u 0 = 0 → u (Real.pi / 2) = 0 →
    MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (deriv u)) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 *
      Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ →
    (∫ θ in Work.Spaces.Iθ, (deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
        (Real.rpow (Real.sin (2 * θ)) (4 - γ) / (Real.cos θ) ^ 2))
      ≤ C * ((∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv u)) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (2 - γ))
          + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
              Work.FTS.EllipticEst.sEta θ)
          + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
          + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)) := by
  refine ⟨1000000, by norm_num, ?_⟩
  intro γ u hγ1 hγ2 hu4 huc hu0 huπ hI3 hI2 hI1 hI0
  set F : ℝ → ℝ := fun θ => (deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
      (Real.rpow (Real.sin (2 * θ)) (4 - γ) / (Real.cos θ) ^ 2) with hF
  set A3 : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv u)) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - γ) with hA3
  set A2 : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
      Work.FTS.EllipticEst.sEta θ with hA2
  set A1 : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 with hA1
  set A0 : ℝ := ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 with hA0
  change (∫ θ in Work.Spaces.Iθ, F θ) ≤ 1000000 * (A3 + A2 + A1 + A0)
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := by rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  have hA3nn : 0 ≤ A3 := by
    rw [hA3]
    exact MeasureTheory.setIntegral_nonneg hIθ_meas
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _))
  have hA2nn : 0 ≤ A2 := by
    rw [hA2]
    exact MeasureTheory.setIntegral_nonneg hIθ_meas
      (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg_Iθ hθ))
  have hA1nn : 0 ≤ A1 := by
    rw [hA1]; exact MeasureTheory.setIntegral_nonneg hIθ_meas (fun θ _ => sq_nonneg _)
  have hA0nn : 0 ≤ A0 := by
    rw [hA0]; exact MeasureTheory.setIntegral_nonneg hIθ_meas (fun θ _ => sq_nonneg _)
  by_cases hInt : MeasureTheory.IntegrableOn F Work.Spaces.Iθ
  · rw [integral_Iθ_split F hInt]
    have hFintFar : MeasureTheory.IntegrableOn F (Set.Ioo (0 : ℝ) (Real.pi / 4)) :=
      hInt.mono_set (fun x hx => ⟨hx.1.le, by linarith [hx.2, Real.pi_pos]⟩)
    have hFintNear : MeasureTheory.IntegrableOn F (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
      hInt.mono_set (fun x hx => ⟨by linarith [hx.1, Real.pi_pos], hx.2.le⟩)
    have hnear := nearIntegral_le u γ hγ1 hγ2 hu4 huc huπ hI3 hI1 hFintNear
    have hfar := farIntegral_le u γ hγ1 hγ2 hu4 hI2 hI1 hI0 hFintFar
    have hnear' : (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), F θ)
        ≤ 2000 * A3 + 20000 * A1 := by
      rw [hF, hA3, hA1]; exact hnear
    have hfar' : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 4), F θ)
        ≤ 48 * A2 + 192 * A1 + 432 * A0 := by
      rw [hF, hA2, hA1, hA0]; exact hfar
    linarith [hnear', hfar', hA3nn, hA2nn, hA1nn, hA0nn]
  · rw [MeasureTheory.integral_undef hInt]
    nlinarith [hA3nn, hA2nn, hA1nn, hA0nn]

end Work.FTS.EllipticEst.H2W.VTwoAlt
