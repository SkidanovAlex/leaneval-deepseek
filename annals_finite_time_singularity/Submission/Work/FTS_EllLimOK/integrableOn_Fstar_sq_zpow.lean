/-
Copyright: work module for the Elgindi finite-time singularity project.

# Integrability of `z ↦ (F_*(z))² z^{-4}` under `HkMem α 0`

`F_*(z) = ∫_0^{π/2} Ψ(z,θ) sin θ cos²θ dθ` is the angular moment of the solvability
condition of Proposition `prop:L2`.  The lemma below shows that if `Ψ ∈ H⁰(α)` in the
sense of `Work.Spaces.HkMem α 0 Ψ` (i.e. the single weighted slice integral
`z ↦ ∫_θ Ψ(z,θ)² w(z)² sin(2θ)^{-η}` is integrable in `z` on `[0,∞)`), then

  `z ↦ (F_*(z))² · z^{-4}`  is integrable on `(0,∞)`.

The two ingredients are

* the *weighted* Cauchy--Schwarz inequality for the angular moment,
  `F_*(z)² ≤ (π/2) ∫_θ Ψ(z,θ)² sin(2θ)^{-η}`
  (`Fstar_sq_le_sig`: the reciprocal weight `sin(2θ)^η` on the second factor is bounded by
  `1`, so the constant is `π/2`), and
* the pointwise weight bookkeeping `z^{-4} · Ψ² sin(2θ)^{-η} ≤ HkIntegrand α 0 Ψ z θ`,
  which is just `z^{-4} ≤ w z² = (1+z)⁴/z⁴` for `z > 0`.

The measurability of the integrand is *not* proved here; it is an explicit hypothesis (the
totalised integral `F_*` is only measurable under extra assumptions on `Ψ`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Elliptic.Fstar_sq_le
import Submission.Work.FTS.EllipticEst.AngSecond.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

set_option autoImplicit false

/-- At level `k = 0` the `H^k`-integrand collapses to a single square: the `D_z`-sum has the
one term `i = 0` and the mixed double sum is empty. -/
private lemma HkIntegrand_zero_eq (α : ℝ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 F z θ
      = (F z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand]

/-- The auxiliary angular function `sin(2θ)^η · (sin θ cos²θ)²`, the reciprocal weight of the
second factor in the weighted Cauchy--Schwarz inequality. -/
private def Cfun (θ : ℝ) : ℝ :=
  (Work.Elliptic.sinCos2 θ) ^ 2 * (Real.sin (2 * θ)) ^ (Work.Spaces.eta)

/-- `Cfun` is bounded by `1` on the angular interval: both factors are squares (resp.
nonnegative powers) of numbers in `[0,1]`. -/
private lemma Cfun_le_one {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : Cfun θ ≤ 1 := by
  have hθ1 : (0 : ℝ) ≤ θ := hθ.1
  have hθ2 : θ ≤ π / 2 := hθ.2
  have hsin0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have hsin1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hcos0 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩
  have hcos1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hc2 : Real.cos θ ^ 2 ≤ 1 := by nlinarith
  have hsc : Work.Elliptic.sinCos2 θ ^ 2 ≤ 1 := by
    rw [Work.Elliptic.sinCos2]
    have hprod : Real.sin θ * Real.cos θ ^ 2 ≤ 1 := by nlinarith
    have hprod0 : 0 ≤ Real.sin θ * Real.cos θ ^ 2 := mul_nonneg hsin0 (sq_nonneg _)
    nlinarith [hprod, hprod0]
  have hr : (Real.sin (2 * θ)) ^ Work.Spaces.eta ≤ 1 :=
    Real.rpow_le_one (Work.FTS.EllipticEst.AngSecond.sin_two_nonneg hθ)
      (Real.sin_le_one _) Work.Spaces.eta_nonneg
  rw [Cfun]
  calc (Work.Elliptic.sinCos2 θ) ^ 2 * (Real.sin (2 * θ)) ^ Work.Spaces.eta
      ≤ 1 * 1 := mul_le_mul hsc hr
        (Real.rpow_nonneg (Work.FTS.EllipticEst.AngSecond.sin_two_nonneg hθ) _) zero_le_one
    _ = 1 := one_mul 1

/-- `Cfun` is continuous, being a product of continuous functions (`t ↦ t^η` is continuous for
`η ≥ 0`). -/
private lemma Cfun_cont : Continuous Cfun := by
  rw [show Cfun = fun θ => (Work.Elliptic.sinCos2 θ) ^ 2
    * (Real.sin (2 * θ)) ^ Work.Spaces.eta from rfl]
  exact ((Real.continuous_sin.mul (Real.continuous_cos.pow 2)).pow 2).mul
    (Continuous.rpow_const (Real.continuous_sin.comp (continuous_const.mul continuous_id))
      (fun θ => Or.inr Work.Spaces.eta_nonneg))

/-- **Pointwise discriminant identity.**  For `θ ∈ Iθ`,
`(Ψ σ - t sinθcos²θ)²/σ = Ψ²σ - 2t Ψ sinθcos²θ + t² Cfun θ` where `σ = sin(2θ)^{-η}`:
multiplying by `σ = (sin(2θ)^η)^{-1}` clears the denominator.  At the two endpoints of `Iθ`
both sides vanish (every factor occurring is `0` there). -/
private lemma Cfun_pt (Ψ : ℝ → ℝ → ℝ) (z t : ℝ) : ∀ θ ∈ Work.Spaces.Iθ,
    (Ψ z θ * Work.FTS.EllipticEst.AngSecond.sig θ - t * Work.Elliptic.sinCos2 θ) ^ 2
        / Work.FTS.EllipticEst.AngSecond.sig θ
      = (Ψ z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ
        - 2 * t * (Ψ z θ * Work.Elliptic.sinCos2 θ) + t ^ 2 * Cfun θ := by
  intro θ hθ
  rcases eq_or_lt_of_le (Work.FTS.EllipticEst.AngSecond.sin_two_nonneg hθ) with hs | hs
  · -- endpoint of `Iθ`: everything vanishes
    have heta : -(Work.Spaces.eta) ≠ 0 := by rw [Work.Spaces.eta]; norm_num
    have hσ0 : Work.FTS.EllipticEst.AngSecond.sig θ = 0 := by
      rw [Work.FTS.EllipticEst.AngSecond.sig, ← hs, Real.zero_rpow heta]
    have hsc : Work.Elliptic.sinCos2 θ = 0 := by
      have h2 : 2 * Real.sin θ * Real.cos θ = 0 := by rw [← Real.sin_two_mul, hs]
      rcases mul_eq_zero.mp h2 with h | h
      · have : Real.sin θ = 0 := by linarith
        rw [Work.Elliptic.sinCos2, this]; ring
      · rw [Work.Elliptic.sinCos2, h]; ring
    simp only [hσ0, hsc, Cfun]
    rw [← hs]
    simp
  · -- interior: clear the denominator `σ = (sin 2θ)^{-η}`
    have hsig : Work.FTS.EllipticEst.AngSecond.sig θ
        = ((Real.sin (2 * θ)) ^ Work.Spaces.eta)⁻¹ := by
      rw [Work.FTS.EllipticEst.AngSecond.sig, Real.rpow_neg (le_of_lt hs)]
    rw [hsig]
    simp only [Cfun]
    field_simp
    ring

/-- **Weighted Cauchy--Schwarz for the angular moment.**  If the `σ`-weighted slice mass of
`Ψ(·,z)` is integrable on `Iθ`, then
`F_*(z)² ≤ (π/2) ∫_θ Ψ(z,θ)² sin(2θ)^{-η}`.

The proof follows the discriminant argument of `Work.Elliptic.Fstar_sq_le`: for every `t` the
integral `∫_θ (Ψσ - t sinθcos²θ)²/σ` is nonnegative, and expanding it gives the nonnegative
quadratic `t ↦ A - 2tB + t²Cf` with `A = ∫Ψ²σ`, `B = F_*`, `Cf = ∫Cfun`; hence `B² ≤ A·Cf`,
and `Cf ≤ π/2` since `Cfun ≤ 1` on `Iθ`.  When `Ψ·sinθcos²θ` is not integrable its integral
is `0` and the inequality is trivial. -/
private lemma Fstar_sq_le_sig {Ψ : ℝ → ℝ → ℝ} {z : ℝ}
    (h : IntegrableOn (fun θ => (Ψ z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
      Work.Spaces.Iθ) :
    (Work.Elliptic.Fstar Ψ z) ^ 2
      ≤ (π / 2) * ∫ θ in Work.Spaces.Iθ,
          (Ψ z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ := by
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  rw [Work.Elliptic.Fstar]
  set A := ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ
  set B := ∫ θ in Work.Spaces.Iθ, Ψ z θ * Work.Elliptic.sinCos2 θ
  set Cf := ∫ θ in Work.Spaces.Iθ, Cfun θ
  have hCint : IntegrableOn Cfun Work.Spaces.Iθ :=
    Cfun_cont.continuousOn.integrableOn_compact isCompact_Icc
  have hA0 : 0 ≤ A :=
    setIntegral_nonneg hIθ (fun θ hθ => mul_nonneg (sq_nonneg _)
      (Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ))
  have hCf0 : 0 ≤ Cf :=
    setIntegral_nonneg hIθ (fun θ hθ => mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (Work.FTS.EllipticEst.AngSecond.sin_two_nonneg hθ) _))
  have hCle : Cf ≤ π / 2 := by
    have hInt1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
      integrableOn_const (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    have hmono : ∫ θ in Work.Spaces.Iθ, Cfun θ ≤ ∫ θ in Work.Spaces.Iθ, (1 : ℝ) :=
      setIntegral_mono_on hCint hInt1 hIθ (fun θ hθ => Cfun_le_one hθ)
    have hvol : volume.real Work.Spaces.Iθ = π / 2 := by
      rw [MeasureTheory.measureReal_def, Work.Spaces.Iθ, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
      ring
    have hconst : ∫ θ in Work.Spaces.Iθ, (1 : ℝ) = π / 2 := by
      rw [MeasureTheory.setIntegral_const]
      simp only [smul_eq_mul, mul_one]
      rw [hvol]
    linarith
  have hCS : B ^ 2 ≤ A * Cf := by
    by_cases huw : IntegrableOn (fun θ => Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ
    · have hquad : ∀ t : ℝ, 0 ≤ A - 2 * t * B + t ^ 2 * Cf := by
        intro t
        have hexp : ∫ θ in Work.Spaces.Iθ,
              ((Ψ z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ
                - 2 * t * (Ψ z θ * Work.Elliptic.sinCos2 θ) + t ^ 2 * Cfun θ)
            = A - 2 * t * B + t ^ 2 * Cf := by
          have hi12 : IntegrableOn (fun θ => (Ψ z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ
              - 2 * t * (Ψ z θ * Work.Elliptic.sinCos2 θ)) Work.Spaces.Iθ :=
            h.sub (huw.const_mul (2 * t))
          rw [integral_add hi12 (hCint.const_mul (t ^ 2)),
            integral_sub h (huw.const_mul (2 * t)), integral_const_mul, integral_const_mul]
        have hcongr : ∫ θ in Work.Spaces.Iθ,
              (Ψ z θ * Work.FTS.EllipticEst.AngSecond.sig θ - t * Work.Elliptic.sinCos2 θ) ^ 2
                / Work.FTS.EllipticEst.AngSecond.sig θ
            = ∫ θ in Work.Spaces.Iθ,
              ((Ψ z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ
                - 2 * t * (Ψ z θ * Work.Elliptic.sinCos2 θ) + t ^ 2 * Cfun θ) :=
          setIntegral_congr_fun hIθ (fun θ hθ => Cfun_pt Ψ z t θ hθ)
        have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
              (Ψ z θ * Work.FTS.EllipticEst.AngSecond.sig θ - t * Work.Elliptic.sinCos2 θ) ^ 2
                / Work.FTS.EllipticEst.AngSecond.sig θ :=
          setIntegral_nonneg hIθ (fun θ hθ =>
            div_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ))
        rw [hcongr, hexp] at hnn
        exact hnn
      exact Work.Elliptic.sq_le_mul_of_quadratic_nonneg hquad
    · have hB0 : B = 0 := integral_undef huw
      rw [hB0]
      simpa using mul_nonneg hA0 hCf0
  calc B ^ 2 ≤ A * Cf := hCS
    _ ≤ A * (π / 2) := mul_le_mul_of_nonneg_left hCle hA0
    _ = (π / 2) * A := by ring

theorem integrableOn_Fstar_sq_zpow {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hHk : Work.Spaces.HkMem α 0 Ψ)
    (hmeas : AEMeasurable (fun z => (Work.Elliptic.Fstar Ψ z) ^ 2 * z ^ (-4 : ℝ))
      (MeasureTheory.volume.restrict (Set.Ioi 0))) :
    MeasureTheory.IntegrableOn (fun z => (Work.Elliptic.Fstar Ψ z) ^ 2 * z ^ (-4 : ℝ))
      (Set.Ioi (0 : ℝ)) := by
  -- The dominating function: the (integrable) slice integral of the `H⁰`-integrand.
  have hH : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ z θ)
      (Set.Ioi 0) :=
    hHk.2.mono_set (fun z hz => Set.mem_Ici.mpr (le_of_lt hz))
  refine (hH.const_mul (π / 2)).mono' hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  have hz0 : 0 < z := hz
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hsliceH : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 Ψ z θ) Work.Spaces.Iθ :=
    hHk.1 z (Set.mem_Ici.mpr (le_of_lt hz0))
  -- the `H⁰`-integrand is `w z²` times the `σ`-weighted slice mass
  have hpt : ∀ θ ∈ Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ z θ
      = (Work.Spaces.w z) ^ 2
        * ((Ψ z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) := by
    intro θ hθ
    rw [HkIntegrand_zero_eq α Ψ z θ, Work.FTS.EllipticEst.AngSecond.sq_mul_W Ψ hθ]
    simp only [Work.FTS.EllipticEst.AngSecond.w2, Work.FTS.EllipticEst.AngSecond.sig, sq]
    ring
  have hw2ne : (Work.Spaces.w z) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.AngSecond.w_pos hz0))
  -- integrability of the `σ`-weighted slice mass, by dividing the integrand by `w z²`
  have hsliceσ : IntegrableOn (fun θ => (Ψ z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
      Work.Spaces.Iθ := by
    have h1 : IntegrableOn (fun θ => (Work.Spaces.w z) ^ 2
        * ((Ψ z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)) Work.Spaces.Iθ :=
      hsliceH.congr_fun (fun θ hθ => hpt θ hθ) hIθ
    have h2 : IntegrableOn (fun θ => ((Work.Spaces.w z) ^ 2)⁻¹
        * ((Work.Spaces.w z) ^ 2
          * ((Ψ z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ))) Work.Spaces.Iθ :=
      h1.const_mul _
    refine h2.congr_fun (fun θ _ => ?_) hIθ
    exact inv_mul_cancel_left₀ hw2ne _
  -- the weighted Cauchy--Schwarz bound for `F_*`
  have hCS := Fstar_sq_le_sig hsliceσ
  -- `z^{-4} ≤ w z²` for `z > 0`
  have hzpow_eq : z ^ (-4 : ℝ) = (z ^ 4)⁻¹ := by
    rw [show (-4 : ℝ) = -(4 : ℝ) by norm_num, Real.rpow_neg (le_of_lt hz0)]
    simp
  have hw2_eq : (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 * (z ^ 4)⁻¹ := by
    rw [Work.Spaces.w, div_pow, ← pow_mul, ← pow_mul, div_eq_mul_inv]
  have hzpow_le : z ^ (-4 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := by
    have h1 : (1 : ℝ) ≤ (1 + z) ^ 4 := one_le_pow₀ (by linarith)
    have h2 : 0 < (z ^ 4)⁻¹ := inv_pos.mpr (pow_pos hz0 4)
    rw [hzpow_eq, hw2_eq]
    calc (z ^ 4)⁻¹ = 1 * (z ^ 4)⁻¹ := (one_mul _).symm
      _ ≤ (1 + z) ^ 4 * (z ^ 4)⁻¹ := mul_le_mul_of_nonneg_right h1 (le_of_lt h2)
  -- the pointwise weight bookkeeping
  have hkey : (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
      * z ^ (-4 : ℝ) ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ z θ := by
    have hmono := setIntegral_mono_on (hsliceσ.mul_const (z ^ (-4 : ℝ))) hsliceH hIθ
      (fun θ hθ => by
        rw [hpt θ hθ]
        have hu : 0 ≤ (Ψ z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ :=
          mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ)
        calc (Ψ z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ * z ^ (-4 : ℝ)
            ≤ (Ψ z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ
              * (Work.Spaces.w z) ^ 2 := mul_le_mul_of_nonneg_left hzpow_le hu
          _ = (Work.Spaces.w z) ^ 2
              * ((Ψ z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) := by ring)
    rwa [MeasureTheory.integral_mul_const] at hmono
  -- assemble
  have hzpow_nonneg : 0 ≤ z ^ (-4 : ℝ) := Real.rpow_nonneg (le_of_lt hz0) _
  calc ‖(Work.Elliptic.Fstar Ψ z) ^ 2 * z ^ (-4 : ℝ)‖
      = (Work.Elliptic.Fstar Ψ z) ^ 2 * z ^ (-4 : ℝ) := by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hzpow_nonneg)]
    _ ≤ ((π / 2) * ∫ θ in Work.Spaces.Iθ,
          (Ψ z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) * z ^ (-4 : ℝ) :=
        mul_le_mul_of_nonneg_right hCS hzpow_nonneg
    _ = (π / 2) * ((∫ θ in Work.Spaces.Iθ,
          (Ψ z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) * z ^ (-4 : ℝ)) := by ring
    _ ≤ (π / 2) * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ z θ :=
        mul_le_mul_of_nonneg_left hkey (by positivity)

end Work.FTS_EllLimOK
