/-
Copyright: work module for the Elgindi finite-time singularity project.

# The left endpoint of a slice under the vanishing first moment of `Lzero1`

`Lzero1 u = -u'' + ∂_θ(tan θ · u) - 6u` is the angular operator of the elliptic section and
`sinCos2 θ = sin θ cos²θ` is an eigenfunction of its formal adjoint `LzeroAdj`:

  `LzeroAdj (sinCos2) = -(sinCos2)'' - tan θ (sinCos2)' - 6 sinCos2 = 0`.

Consequently the function

  `Φ θ = - sinCos2 θ · u'(θ) + cos θ · cos (2θ) · u(θ)`

is a primitive of `θ ↦ (Lzero1 u θ) · sinCos2 θ` on `(0, π/2)`
(`Work.FTS.EllipticEst.remov.coerc.phi_slice_hasDerivAt`), and the fundamental theorem of
calculus on `[0, π/2]` identifies the integral with the boundary values of `Φ`:

  `∫_θ Lzero1 u · sinCos2 = Φ((π/2)⁻) - Φ(0⁺) = 0 - lim_{θ→0⁺} u θ`.

This file makes that identity (`sliceMoment_eq_neg_limit`) available with the weak hypotheses
of the `Honest` workstream — `u` merely `C²` on the open interval, bounded with bounded
derivative, and `Lzero1 u · sinCos2` integrable — and deduces the target

  `HonSliceLimitZero`:  the vanishing of the first moment `∫_θ Lzero1 u · sinCos2 = 0` forces
  `u θ → 0` as `θ → 0⁺`.

The existence of the limit `L = lim_{θ→0⁺} u θ` is a consequence of `|u'| ≤ C`: `u` is
Lipschitz there, so its derivative is integrable and
`Work.FTS.EllipticEst.exists_tendsto_nhdsGT_zero_of_integrableOn_deriv` applies.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.remov.coerc.phi_slice_hasDerivAt
import Submission.Work.FTS.EllipticEst.remov.coerc.hasDerivAt_tendsto_at_ends
import Submission.Work.FTS.EllipticEst.remov.coerc.mul_sq_vanishing
import Submission.Work.FTS.EllipticEst.remov.coerc.mul_sq_vanishing_right
import Submission.Work.FTS.EllipticEst.exists_tendsto_nhdsGT_zero_of_integrableOn_deriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

open scoped Real Topology Interval
open MeasureTheory Set Filter

set_option autoImplicit false

/-- **The moment identity at the left endpoint.**  Let `u` be `C²` on `(0, π/2)`, bounded there
together with `deriv u` by `C`, with `Lzero1 u · sinCos2` integrable on `Iθ` and with limit `L`
at `0⁺`.  Then

  `∫_θ (Lzero1 u)(θ) · sin θ cos²θ = -L`.

The proof integrates the primitive `Φ θ = -sinCos2 θ · u'(θ) + cos θ cos(2θ) · u(θ)` of the
integrand and evaluates the boundary terms: the one at `π/2` vanishes (the factor `cos θ`
vanishes, and `sinCos2 · u'` is a bounded function times a vanishing one) while the one at `0⁺`
is `L`; the fact that no *interior* term survives is exactly `LzeroAdj (sinCos2) = 0`. -/
theorem sliceMoment_eq_neg_limit {u : ℝ → ℝ} {C L : ℝ} (hC : 0 ≤ C)
    (hsm : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hb : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |u θ| ≤ C ∧ |deriv u θ| ≤ C)
    (hL : MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.EllipticEst.Lzero1 u θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (hlim : Filter.Tendsto u (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L)) :
    (∫ θ in Work.Spaces.Iθ,
      Work.FTS.EllipticEst.Lzero1 u θ * Work.Elliptic.sinCos2 θ) = -L := by
  -- the primitive `Φ` and the integrand `ψ`
  set ψ : ℝ → ℝ := fun θ => Work.FTS.EllipticEst.Lzero1 u θ * Work.Elliptic.sinCos2 θ
    with hψ
  set Φ : ℝ → ℝ := fun θ => -(Work.Elliptic.sinCos2 θ) * deriv u θ
      + Real.cos θ * Real.cos (2 * θ) * u θ with hΦ
  have hder : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), HasDerivAt Φ (ψ θ) θ := by
    intro θ hθ
    rw [hΦ, hψ]
    exact Work.FTS.EllipticEst.remov.coerc.phi_slice_hasDerivAt hsm θ hθ
  have hpsiIcc : MeasureTheory.IntegrableOn ψ (Set.Icc 0 (Real.pi / 2)) := by
    rw [hψ]
    simpa only [Work.Spaces.Iθ] using hL
  -- `Φ` has one-sided limits at both endpoints
  obtain ⟨⟨β, hβ⟩, ⟨γ, hγ⟩⟩ :=
    Work.FTS.EllipticEst.remov.coerc.hasDerivAt_tendsto_at_ends (L := Real.pi / 2)
      (by positivity) hder hpsiIcc
  -- the "good" term `θ ↦ cos θ cos(2θ) u θ` tends to `L` at `0⁺`
  have hcosu0 : Filter.Tendsto (fun θ : ℝ => Real.cos θ * Real.cos (2 * θ) * u θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L) := by
    have hc : ContinuousAt (fun θ : ℝ => Real.cos θ * Real.cos (2 * θ)) 0 := by fun_prop
    have h1 : Filter.Tendsto (fun θ : ℝ => Real.cos θ * Real.cos (2 * θ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (Real.cos 0 * Real.cos (2 * 0))) :=
      hc.continuousWithinAt
    have h2 := h1.mul hlim
    have h3 : Real.cos 0 * Real.cos (2 * 0) * L = L := by simp
    simpa [h3] using h2
  -- hence `sinCos2 θ · u'(θ) → L - β` at `0⁺`
  have hw0 : Filter.Tendsto (fun θ : ℝ => Work.Elliptic.sinCos2 θ * deriv u θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (L - β)) := by
    have hdiff : Filter.Tendsto
        (fun θ : ℝ => Real.cos θ * Real.cos (2 * θ) * u θ - Φ θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (L - β)) := hcosu0.sub hβ
    rw [show (fun θ : ℝ => Work.Elliptic.sinCos2 θ * deriv u θ)
        = fun θ : ℝ => Real.cos θ * Real.cos (2 * θ) * u θ - Φ θ from by
      funext θ; rw [hΦ]; ring]
    exact hdiff
  -- `|sinCos2 θ| ≤ θ` near `0⁺`
  have hbound0 : ∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      |Work.Elliptic.sinCos2 θ| ≤ (1 : ℝ) * θ := by
    have hlt1 : ∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0), θ < 1 :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [self_mem_nhdsWithin, hlt1] with θ hθ hθ1
    have hθ0 : 0 < θ := hθ
    have hsin : Real.sin θ ≤ θ := Real.sin_le hθ0.le
    have hc2 : Real.cos θ ^ 2 ≤ 1 := by
      nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sin θ)]
    rw [Work.Elliptic.sinCos2, abs_mul, abs_of_nonneg (sq_nonneg (Real.cos θ))]
    have hsinabs : |Real.sin θ| = Real.sin θ :=
      abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ0.le
        (by linarith [hθ1, Real.pi_gt_three]))
    rw [hsinabs]
    calc Real.sin θ * Real.cos θ ^ 2 ≤ θ * 1 :=
          mul_le_mul hsin hc2 (sq_nonneg _) hθ0.le
      _ = 1 * θ := by ring
  -- integrability of `(u')²` on `(0, π/2)` from the bound on `u'`
  have hsq_oo : MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine MeasureTheory.IntegrableOn.of_bound (s := Set.Ioo (0 : ℝ) (Real.pi / 2)) ?_
      ?_ (C ^ 2) ?_
    · rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
    · exact ((measurable_deriv u).pow_const 2).aestronglyMeasurable
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (deriv u θ))]
      calc (deriv u θ) ^ 2 = |deriv u θ| ^ 2 := (sq_abs (deriv u θ)).symm
        _ ≤ C ^ 2 := by
            rw [pow_two, pow_two]
            exact mul_self_le_mul_self (abs_nonneg (deriv u θ)) ((hb θ hθ).2)
  have hf_int0 : MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) (Set.Ioo 0 1) :=
    hsq_oo.mono_set (fun θ hθ => ⟨hθ.1, by linarith [hθ.2, Real.pi_gt_three]⟩)
  have hLβ : L - β = 0 :=
    Work.FTS.EllipticEst.remov.coerc.mul_sq_vanishing (f := fun θ => deriv u θ)
      (φ := Work.Elliptic.sinCos2) (C := 1) (by norm_num) hbound0 hf_int0 hw0
  have hΦ0 : Filter.Tendsto Φ (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L) := by
    have hβeq : β = L := by linarith
    rw [hβeq] at hβ
    exact hβ
  -- at `(π/2)⁻`: `cos θ cos(2θ) u θ → 0` because `u` is bounded and `cos θ → 0`
  have hcosu1 : Filter.Tendsto (fun θ : ℝ => Real.cos θ * Real.cos (2 * θ) * u θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have hc : Filter.Tendsto (fun θ : ℝ => |Real.cos θ|)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      have hcont : ContinuousAt (fun θ : ℝ => Real.cos θ) (Real.pi / 2) :=
        Real.continuous_cos.continuousAt
      have h1 : Filter.Tendsto Real.cos
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
          (nhds (Real.cos (Real.pi / 2))) := hcont.continuousWithinAt
      have h2 : Filter.Tendsto (fun θ : ℝ => |Real.cos θ|)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
          (nhds |Real.cos (Real.pi / 2)|) := by
        simpa only [Real.norm_eq_abs] using h1.norm
      simpa [Real.cos_pi_div_two] using h2
    have ha : Filter.Tendsto (fun θ : ℝ => C * |Real.cos θ|)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      simpa using hc.const_mul C
    refine squeeze_zero_norm' ?_ ha
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Ioi_mem_nhds (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 2))]
      with θ hθhi hθlo
    have hbθ : |u θ| ≤ C := (hb θ ⟨hθlo, hθhi⟩).1
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have hcos2 : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one (2 * θ)
    calc |Real.cos θ| * |Real.cos (2 * θ)| * |u θ| ≤ |Real.cos θ| * 1 * C :=
          mul_le_mul (mul_le_mul le_rfl hcos2 (abs_nonneg _) (abs_nonneg _)) hbθ
            (abs_nonneg _) (by positivity)
      _ = C * |Real.cos θ| := by ring
  have hw1 : Filter.Tendsto (fun θ : ℝ => Work.Elliptic.sinCos2 θ * deriv u θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (0 - γ)) := by
    have hdiff : Filter.Tendsto
        (fun θ : ℝ => Real.cos θ * Real.cos (2 * θ) * u θ - Φ θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (0 - γ)) := hcosu1.sub hγ
    rw [show (fun θ : ℝ => Work.Elliptic.sinCos2 θ * deriv u θ)
        = fun θ : ℝ => Real.cos θ * Real.cos (2 * θ) * u θ - Φ θ from by
      funext θ; rw [hΦ]; ring]
    exact hdiff
  -- `|sinCos2 θ| ≤ π/2 - θ` near `(π/2)⁻`
  have hbound1 : ∀ᶠ θ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
      |Work.Elliptic.sinCos2 θ| ≤ (1 : ℝ) * (Real.pi / 2 - θ) := by
    have hgt : ∀ᶠ θ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
        Real.pi / 2 - 1 < θ :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Ioi_mem_nhds (by linarith [Real.pi_gt_three] : Real.pi / 2 - 1 < Real.pi / 2))
    filter_upwards [self_mem_nhdsWithin, hgt] with θ hθ hθ1
    have hθlt : θ < Real.pi / 2 := hθ
    have ht : 0 < Real.pi / 2 - θ := by linarith
    have ht1 : Real.pi / 2 - θ ≤ 1 := by linarith
    have hcos : Real.cos θ = Real.sin (Real.pi / 2 - θ) := (Real.sin_pi_div_two_sub θ).symm
    have hsin_le1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
    have hsin_nn : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ1, Real.pi_gt_three])
        (by linarith [hθlt, Real.pi_pos])
    rw [Work.Elliptic.sinCos2, abs_mul, abs_of_nonneg (sq_nonneg (Real.cos θ))]
    rw [abs_of_nonneg hsin_nn]
    have h2 : Real.cos θ ^ 2 = Real.sin (Real.pi / 2 - θ) ^ 2 := by rw [hcos]
    have hsin_le : Real.sin (Real.pi / 2 - θ) ≤ Real.pi / 2 - θ := Real.sin_le ht.le
    have hsin_nn2 : 0 ≤ Real.sin (Real.pi / 2 - θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi ht.le (by linarith [hθ1, Real.pi_gt_three])
    have h3 : Real.sin (Real.pi / 2 - θ) ^ 2 ≤ (Real.pi / 2 - θ) ^ 2 := by
      nlinarith [hsin_le, hsin_nn2]
    have h4 : (Real.pi / 2 - θ) ^ 2 ≤ Real.pi / 2 - θ := by nlinarith [ht, ht1]
    have h5 : Real.sin θ * Real.cos θ ^ 2 ≤ 1 * Real.sin (Real.pi / 2 - θ) ^ 2 := by
      rw [h2]
      exact mul_le_mul hsin_le1 le_rfl (sq_nonneg _) zero_le_one
    calc Real.sin θ * Real.cos θ ^ 2 ≤ 1 * Real.sin (Real.pi / 2 - θ) ^ 2 := h5
      _ ≤ 1 * (Real.pi / 2 - θ) ^ 2 := by linarith
      _ ≤ 1 * (Real.pi / 2 - θ) := by linarith
  have hf_int1 : MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2)
      (Set.Ioo (Real.pi / 2 - 1) (Real.pi / 2)) :=
    hsq_oo.mono_set (fun θ hθ => ⟨by linarith [hθ.1, Real.pi_gt_three], hθ.2⟩)
  have hγ0 : 0 - γ = 0 :=
    Work.FTS.EllipticEst.remov.coerc.mul_sq_vanishing_right (f := fun θ => deriv u θ)
      (φ := Work.Elliptic.sinCos2) (b := Real.pi / 2) (C := 1) (by norm_num)
      hbound1 hf_int1 hw1
  have hΦ1 : Filter.Tendsto Φ (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have hγeq : γ = 0 := by linarith
    rw [hγeq] at hγ
    exact hγ
  -- the fundamental theorem of calculus on `0..π/2`
  have hInt : IntervalIntegrable ψ volume 0 (Real.pi / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
    exact hpsiIcc.mono_set Set.Ioc_subset_Icc_self
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (a := (0 : ℝ)) (b := Real.pi / 2) (f := Φ) (f' := ψ)
    (by positivity : (0 : ℝ) < Real.pi / 2) hder hInt hΦ0 hΦ1
  have hmain : (∫ θ in Work.Spaces.Iθ, ψ θ) = -L := by
    have h1 : (∫ θ in Work.Spaces.Iθ, ψ θ) = ∫ y in (0 : ℝ)..Real.pi / 2, ψ y := by
      rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2),
        Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [h1, hFTC]; ring
  rwa [hψ] at hmain

theorem HonSliceLimitZero (u : ℝ → ℝ)
    (hsm : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (h2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv u t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ)
    (hbdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |u θ| ≤ C ∧ |deriv u θ| ≤ C)
    (hL : MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.EllipticEst.Lzero1 u θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (hmom : (∫ θ in Work.Spaces.Iθ,
      Work.FTS.EllipticEst.Lzero1 u θ * Work.Elliptic.sinCos2 θ) = 0) :
    Filter.Tendsto u (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  obtain ⟨C, hC, hb⟩ := hbdd
  -- `u` is differentiable on `(0, π/4)` with bounded derivative, hence has a limit at `0⁺`
  have hder_u : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 4), HasDerivAt u (deriv u x) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
    exact ((hsm.contDiffAt (isOpen_Ioo.mem_nhds hx')).differentiableAt (by norm_num)).hasDerivAt
  have hint_deriv : MeasureTheory.IntegrableOn (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 4)) := by
    refine MeasureTheory.IntegrableOn.of_bound (s := Set.Ioo (0 : ℝ) (Real.pi / 4)) ?_ ?_ C ?_
    · rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
    · exact (measurable_deriv u).aestronglyMeasurable
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      have hθ' : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
      rw [Real.norm_eq_abs]
      exact (hb θ hθ').2
  obtain ⟨L, hlim⟩ :=
    Work.FTS.EllipticEst.exists_tendsto_nhdsGT_zero_of_integrableOn_deriv
      (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 4) hder_u hint_deriv
  -- the vanishing moment forces `L = 0`
  have hmoment := sliceMoment_eq_neg_limit hC hsm hb hL hlim
  have hL0 : L = 0 := by linarith [hmoment, hmom]
  rwa [hL0] at hlim

end Work.FTS.EllipticEst.Honest
