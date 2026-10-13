import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FTS_EllLimOK/ProducerH/BoxAux/th2Ident` — the closed form of `Φ = (S'' + 4S + G)`

For a function `S` of class `C²` on `(0, π/2)` whose second derivative solves the slice equation

`S'' = tan θ · S' + (cos θ)⁻² · S − 6 S − G`

one has, on `(0, π/2)`,

`(cos θ)^3 · (S''(θ) + 4 S(θ) + G(θ)) = ∫_θ^{π/2} sin t · (cos t)^2 · G(t) dt`.

## Proof

Write `Φ := S'' + 4S + G`.  The equation turns `Φ` into `Φ = tan θ · S' + ((cos θ)⁻² − 2)·S`, and the
elementary identity

`(cos^3 θ · (tan θ · S' + ((cos θ)⁻² − 2) · S))' = − sin θ · (cos θ)^2 · G θ`

holds on `(0, π/2)` (everything cancels except `− sin θ (cos θ)^2 G θ`, using the equation to eliminate
`S''`).  Since the whole expression is `O((cos θ)^3)` near `π/2` (here the hypothesis `|Φ| ≤ MW` is
used), the function `cos^3 θ · Φ(θ)` has the left limit `0` at `π/2`, and the fundamental theorem of
calculus (in the form `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto`) on `[θ, π/2]` gives
the claim.
-/

open scoped Topology
open MeasureTheory Filter

namespace Work.FTS_EllLimOK.ProducerH.BoxAux

theorem th2Ident {S G : ℝ → ℝ} {MG MW : ℝ}
    (hS : ContDiffOn ℝ 2 S (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hG : ContinuousOn G (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hGb : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |G t| ≤ MG)
    (hode : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      deriv (deriv S) θ
        = Real.tan θ * deriv S θ + ((Real.cos θ) ^ 2)⁻¹ * S θ - 6 * S θ - G θ)
    (hWb : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |deriv (deriv S) θ + 4 * S θ + G θ| ≤ MW) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Real.cos θ) ^ 3 * (deriv (deriv S) θ + 4 * S θ + G θ)
        = ∫ t in θ..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 * G t := by
  intro θ hθ
  have hθ0 : 0 < θ := hθ.1
  have hθ1 : θ < Real.pi / 2 := hθ.2
  -- ## Regularity of `S` and of `deriv S` on the open interval
  have hS1 : ContDiffOn ℝ 1 (deriv S) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h := hS.derivWithin (uniqueDiffOn_Ioo 0 (Real.pi / 2))
      (show (1 : WithTop ℕ∞) + 1 ≤ 2 from by norm_num)
    exact h.congr (fun x hx => (derivWithin_of_mem_nhds (isOpen_Ioo.mem_nhds hx)).symm)
  have hdC : ContinuousOn (deriv S) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hS1.continuousOn
  have hSd : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt S (deriv S t) t := fun t ht =>
    (hS.differentiableOn (by norm_num)).hasDerivAt (isOpen_Ioo.mem_nhds ht)
  have hS2d : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (deriv S) (deriv (deriv S) t) t := fun t ht =>
    (hS1.differentiableOn (by norm_num)).hasDerivAt (isOpen_Ioo.mem_nhds ht)
  -- ## The explicit primitive `F` of the integrand
  set F : ℝ → ℝ := fun u => Real.sin u * (Real.cos u)^2 * deriv S u
      + (Real.cos u - 2*(Real.cos u)^3) * S u with hF
  -- `F` agrees with `cos^3 θ · Φ(θ)` on the interval (this is the ODE)
  have hPF : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Real.cos t)^3 * (deriv (deriv S) t + 4*S t + G t) = F t := by
    intro t ht
    rw [hF]
    have hcos : Real.cos t ≠ 0 := by
      have h : 0 < Real.cos t :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2]⟩
      exact ne_of_gt h
    rw [hode t ht, Real.tan_eq_sin_div_cos]
    field_simp
    ring
  -- ## `F` has the desired derivative on the interval
  have hFderiv : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt F (-(Real.sin t * (Real.cos t)^2 * G t)) t := by
    intro t ht
    have h1 : HasDerivAt (fun u : ℝ => Real.sin u * (Real.cos u)^2 * deriv S u)
        ((Real.cos t ^ 3 - 2 * Real.sin t ^ 2 * Real.cos t) * deriv S t
          + Real.sin t * (Real.cos t)^2 * deriv (deriv S) t) t := by
      have ha : HasDerivAt (fun u : ℝ => Real.sin u) (Real.cos t) t := Real.hasDerivAt_sin t
      have hb : HasDerivAt (fun u : ℝ => Real.cos u ^ 2)
          (2 * Real.cos t^(2-1) * -Real.sin t) t := (Real.hasDerivAt_cos t).pow 2
      have hab : HasDerivAt (fun u : ℝ => Real.sin u * Real.cos u ^ 2)
          (Real.cos t ^ 3 - 2 * Real.sin t ^ 2 * Real.cos t) t := by
        have h := ha.mul hb
        convert h using 1
        simp only [Nat.reduceSub]
        ring
      exact hab.mul (hS2d t ht)
    have h2 : HasDerivAt (fun u : ℝ => (Real.cos u - 2 * Real.cos u ^ 3) * S u)
        ((-Real.sin t + 6 * Real.cos t ^ 2 * Real.sin t) * S t
          + (Real.cos t - 2 * Real.cos t ^ 3) * deriv S t) t := by
      have ha : HasDerivAt (fun u : ℝ => Real.cos u - 2 * Real.cos u ^ 3)
          (-Real.sin t + 6 * Real.cos t ^ 2 * Real.sin t) t := by
        have hc : HasDerivAt (fun u : ℝ => Real.cos u) (-Real.sin t) t := Real.hasDerivAt_cos t
        have hd : HasDerivAt (fun u : ℝ => Real.cos u ^ 3)
            (3 * Real.cos t^(3-1) * -Real.sin t) t := (Real.hasDerivAt_cos t).pow 3
        have h := hc.sub (hd.const_mul 2)
        convert h using 1
        simp only [Nat.reduceSub]
        ring
      exact ha.mul (hSd t ht)
    have hD : (Real.cos t ^ 3 - 2 * Real.sin t ^ 2 * Real.cos t) * deriv S t
          + Real.sin t * (Real.cos t)^2 * deriv (deriv S) t
          + ((-Real.sin t + 6 * Real.cos t ^ 2 * Real.sin t) * S t
              + (Real.cos t - 2 * Real.cos t ^ 3) * deriv S t)
        = -(Real.sin t * (Real.cos t)^2 * G t) := by
      have hcos : Real.cos t ≠ 0 := by
        have h : 0 < Real.cos t :=
          Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2]⟩
        exact ne_of_gt h
      have hsq : Real.sin t ^ 2 = 1 - Real.cos t ^ 2 := by
        linarith [Real.sin_sq_add_cos_sq t]
      rw [hode t ht, Real.tan_eq_sin_div_cos, hsq]
      field_simp
      ring_nf
      linear_combination (Real.cos t * deriv S t) * Real.sin_sq_add_cos_sq t
    have hsum := h1.add h2
    rw [hD] at hsum
    rw [hF]
    exact hsum
  -- ## Integrability of the integrand on `[θ, π/2]`
  have hint : IntervalIntegrable (fun t => -(Real.sin t * (Real.cos t)^2 * G t))
      volume θ (Real.pi/2) := by
    have hGae : AEMeasurable G (volume.restrict (Set.Ioo (0:ℝ) (Real.pi/2))) :=
      hG.aemeasurable measurableSet_Ioo
    have hmono : volume.restrict (Set.Ioo θ (Real.pi/2))
        ≤ volume.restrict (Set.Ioo (0:ℝ) (Real.pi/2)) :=
      Measure.restrict_mono (s := Set.Ioo θ (Real.pi/2))
        (s' := Set.Ioo (0:ℝ) (Real.pi/2)) (μ := volume) (ν := volume)
        (fun x hx => ⟨lt_trans hθ0 hx.1, hx.2⟩) le_rfl
    have hGae' : AEMeasurable G (volume.restrict (Set.Ioo θ (Real.pi/2))) :=
      hGae.mono_measure hmono
    have hcae : AEMeasurable (fun t : ℝ => Real.sin t * (Real.cos t)^2)
        (volume.restrict (Set.Ioo θ (Real.pi/2))) :=
      (Real.continuous_sin.mul (Real.continuous_cos.pow 2)).aemeasurable
    have hmeas : AEStronglyMeasurable (fun t : ℝ => -(Real.sin t * (Real.cos t)^2 * G t))
        (volume.restrict (Set.Ioo θ (Real.pi/2))) :=
      ((hcae.mul hGae').neg).aestronglyMeasurable
    have hbdd : ∀ᶠ t in ae (volume.restrict (Set.Ioo θ (Real.pi/2))),
        ‖-(Real.sin t * (Real.cos t)^2 * G t)‖ ≤ MG := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      have hGt : |G t| ≤ MG := hGb t ⟨lt_trans hθ0 ht.1, ht.2⟩
      have hcos2 : |(Real.cos t)^2| ≤ 1 := by
        rw [abs_pow]
        exact pow_le_one₀ (abs_nonneg _) (Real.abs_cos_le_one t)
      rw [norm_neg, Real.norm_eq_abs, abs_mul, abs_mul]
      calc |Real.sin t| * |(Real.cos t)^2| * |G t| ≤ 1 * 1 * |G t| :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul (Real.abs_sin_le_one t) hcos2 (abs_nonneg _) zero_le_one) (abs_nonneg _)
        _ = |G t| := by ring
        _ ≤ MG := hGt
    have hIoo : IntegrableOn (fun t : ℝ => -(Real.sin t * (Real.cos t)^2 * G t))
        (Set.Ioo θ (Real.pi/2)) volume :=
      MeasureTheory.IntegrableOn.of_bound (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top)
        hmeas MG hbdd
    refine ⟨?_, ?_⟩
    · exact IntegrableOn.congr_set_ae hIoo (MeasureTheory.Ioo_ae_eq_Ioc.symm)
    · rw [Set.Ioc_eq_empty_of_le (le_of_lt hθ1)]
      exact MeasureTheory.integrableOn_empty
  -- ## The left limit of `F` at `π/2` is `0`
  have hmem : Set.Ioo (0:ℝ) (Real.pi/2) ∈ 𝓝[<] (Real.pi/2) := by
    have h1 : Set.Ioi (0:ℝ) ∈ 𝓝[<] (Real.pi/2) :=
      nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds Real.pi_div_two_pos)
    have h2 : Set.Iio (Real.pi/2) ∈ 𝓝[<] (Real.pi/2) := self_mem_nhdsWithin
    have h3 : Set.Ioi (0:ℝ) ∩ Set.Iio (Real.pi/2) ∈ 𝓝[<] (Real.pi/2) := Filter.inter_mem h1 h2
    have hinter : Set.Ioi (0:ℝ) ∩ Set.Iio (Real.pi/2) = Set.Ioo (0:ℝ) (Real.pi/2) := by
      ext x; exact Iff.rfl
    rwa [hinter] at h3
  have hEvF : F =ᶠ[𝓝[<] (Real.pi/2)]
      (fun t => (Real.cos t)^3 * (deriv (deriv S) t + 4*S t + G t)) := by
    filter_upwards [hmem] with t ht
    rw [hF]
    exact (hPF t ht).symm
  have hzero : Tendsto (fun t : ℝ => (Real.cos t)^3 * MW) (𝓝[<] (Real.pi/2)) (𝓝 0) := by
    have hc : Tendsto (fun t : ℝ => Real.cos t) (𝓝[<] (Real.pi/2))
        (𝓝 (Real.cos (Real.pi/2))) :=
      Real.continuous_cos.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    rw [Real.cos_pi_div_two] at hc
    have hc3 : Tendsto (fun t : ℝ => (Real.cos t)^3) (𝓝[<] (Real.pi/2)) (𝓝 0) := by
      simpa using hc.pow 3
    simpa using hc3.mul_const MW
  have hboundF : ∀ᶠ t in 𝓝[<] (Real.pi/2), ‖F t‖ ≤ (Real.cos t)^3 * MW := by
    filter_upwards [hmem] with t ht
    have hΦ : |deriv (deriv S) t + 4*S t + G t| ≤ MW := hWb t ht
    have hcos0 : 0 ≤ (Real.cos t)^3 := by
      have h : 0 < Real.cos t :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2]⟩
      positivity
    rw [← hPF t ht, Real.norm_eq_abs, abs_mul, abs_of_nonneg hcos0]
    exact mul_le_mul_of_nonneg_left hΦ hcos0
  have htend_pi : Tendsto F (𝓝[<] (Real.pi/2)) (𝓝 0) := by
    have hnorm : Tendsto (fun t : ℝ => ‖F t‖) (𝓝[<] (Real.pi/2)) (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hzero
        (by filter_upwards with t; exact norm_nonneg _) hboundF
    exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  -- ## The right limit of `F` at `θ` is `F θ` (continuity)
  have hcd : ContinuousAt (deriv S) θ := hdC.continuousAt (isOpen_Ioo.mem_nhds hθ)
  have hcs : ContinuousAt S θ := hS.continuousOn.continuousAt (isOpen_Ioo.mem_nhds hθ)
  have hcontF : ContinuousAt F θ := by
    rw [hF]
    fun_prop
  have htend_θ : Tendsto F (𝓝[>] θ) (𝓝 (F θ)) :=
    hcontF.tendsto.mono_left nhdsWithin_le_nhds
  -- ## The fundamental theorem of calculus
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (f := F)
    (f' := fun t => -(Real.sin t * (Real.cos t)^2 * G t)) hθ1
    (fun t ht => hFderiv t ⟨lt_trans hθ0 ht.1, ht.2⟩) hint htend_θ htend_pi
  rw [intervalIntegral.integral_neg, zero_sub] at hFTC
  have hInt : (∫ t in θ..(Real.pi/2), Real.sin t * (Real.cos t)^2 * G t) = F θ := by
    linarith
  rw [hInt]
  rw [hF]
  exact hPF θ hθ

end Work.FTS_EllLimOK.ProducerH.BoxAux
