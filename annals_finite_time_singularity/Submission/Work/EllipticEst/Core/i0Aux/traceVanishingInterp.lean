import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.hardy_shift_two_same_weight
import Submission.Work.EllipticEst.Core.sliceBoundaryLimit
import Submission.Work.FTS.EllipticEst.Honest.sliceInterp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 20000000

/-!
## Auxiliary calculus for the weighted angular interpolation inequality

This file proves `traceVanishingInterp`: the one-dimensional weighted interpolation
inequality

  `∫_{Iθ} (f')² σ ≤ C (∫_{Iθ} f² σ + √(∫_{Iθ} f² σ · ∫_{Iθ} (f'')² σ))`

for `σ = thEta = sin(2θ)^{-η}`, `η = 99/100`, and `f` of class `C²` on the open interval
`(0, π/2)` whose two endpoint traces vanish and whose three weighted `L²`-norms are finite.

The proof has three layers.

* **The interior integration by parts** (`ibp_main`, `ibp_cot`): for `0 < a < b < π/2`,
  ```
  ∫_a^b (f')² σ = [f f' σ + η f² c σ]_a^b - ∫_a^b f f'' σ + 2η ∫_a^b f² σ
                    + 2η(1+η) ∫_a^b f² c² σ,
  ∫_a^b f f' c σ = ∫_a^b f² σ + (1+η) ∫_a^b f² c² σ + (1/2) [f² c σ]_a^b,
  ```
  where `c = cot(2·)`; everything is written with the auxiliary weight
  `cs1 θ = cos(2θ) sin(2θ)^{-(1+η)}` (equal to `cot(2θ) σ θ` on `(0,π/2)`) and
  `csq θ = cos²(2θ) sin(2θ)^{-(2+η)}` (equal to `cot²(2θ) σ θ`), so that no derivative of
  `cot` and no Pythagorean identity is needed: the rpow bookkeeping is pure
  `Real.rpow_add`.

* **The completed square**: eliminating `∫ f² c² σ` between the two identities via
  `0 ≤ ∫_a^b (f' - (1+η) f c)² σ` gives, on `[a,b]`,
  ```
  (1/199) ∫_a^b (f')² σ = [f f' σ - η f² c σ]_a^b - ∫_a^b f f'' σ
      - 2η ∫_a^b f² σ - (2η/(1+η)) ∫_a^b (f' - (1+η) f c)² σ,
  ```
  with `1 - 2η/(1+η) = (1-η)/(1+η) = 1/199`.

* **The endpoint analysis**: the four boundary terms tend to `0` along the truncating
  sequence (`traceBoundarySeq`), the Cauchy–Schwarz bound `|∫ f f'' σ| ≤ √(P E)` and the
  monotone convergence of `∫_{a_n}^{b_n} (f')² σ` to `∫_{Iθ} (f')² σ` (`expandingIntegral`)
  finish the proof.
-/

/-! ## §1. Elementary facts about the weight -/

/-- `sin (2θ) > 0` on the open angular interval. -/
private theorem sin_two_pos_of_mem {θ : ℝ} (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) :
    0 < Real.sin (2*θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- The weight `thEta` is positive on the open angular interval. -/
private theorem thEta_pos_of_mem {θ : ℝ} (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) :
    0 < Work.FTS.EllipticEst.thEta θ :=
  Real.rpow_pos_of_pos (sin_two_pos_of_mem hθ) _

/-- The auxiliary weight `cos(2θ) sin(2θ)^{-(1+η)}`, which equals `cot(2θ) * thEta θ` on the
open angular interval. -/
private def cs1 (θ : ℝ) : ℝ := Real.cos (2*θ) * Real.sin (2*θ) ^ (-(1 + Work.Spaces.eta))

/-- The auxiliary weight `cos²(2θ) sin(2θ)^{-(2+η)}`, which equals `cot²(2θ) * thEta θ` on the
open angular interval. -/
private def csq (θ : ℝ) : ℝ := Real.cos (2*θ) ^ 2 * Real.sin (2*θ) ^ (-(2 + Work.Spaces.eta))

/-- `(cos(2θ)/sin(2θ)) * thEta θ = cs1 θ`: the rpow identity behind the cross term. -/
private theorem cossin_mul_thEta {θ : ℝ} (hsin : 0 < Real.sin (2*θ)) :
    (Real.cos (2*θ) / Real.sin (2*θ)) * Work.FTS.EllipticEst.thEta θ = cs1 θ := by
  rw [cs1, Work.FTS.EllipticEst.thEta, div_mul_eq_mul_div, div_eq_mul_inv, mul_assoc,
    ← Real.rpow_neg_one (Real.sin (2*θ)), ← Real.rpow_add hsin,
    show -(Work.Spaces.eta) + (-1:ℝ) = -(1 + Work.Spaces.eta) by ring]

/-- `(cos(2θ)/sin(2θ))^2 * thEta θ = csq θ`: the rpow identity behind the squared term. -/
private theorem cossin_sq_mul_thEta {θ : ℝ} (hsin : 0 < Real.sin (2*θ)) :
    (Real.cos (2*θ) / Real.sin (2*θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ = csq θ := by
  have h1 : ((Real.sin (2*θ)) ^ 2)⁻¹ = Real.sin (2*θ) ^ (-(2:ℝ)) := by
    rw [Real.rpow_neg hsin.le, Real.rpow_two]
  rw [csq, Work.FTS.EllipticEst.thEta, div_pow, div_eq_mul_inv, mul_assoc, h1,
    ← Real.rpow_add hsin,
    show (-(2:ℝ)) + -(Work.Spaces.eta) = -(2 + Work.Spaces.eta) by ring]

/-! ## §2. The Jordan-type bounds at the two endpoints -/

/-- `thEta θ ≤ ((4/π) θ)^{-η}` for `0 < θ ≤ π/4`. -/
private theorem thEta_le_left {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ Real.pi/4) :
    Work.FTS.EllipticEst.thEta θ ≤ ((4/Real.pi) * θ) ^ (-(Work.Spaces.eta)) := by
  have hs : (4/Real.pi) * θ ≤ Real.sin (2*θ) := by
    have h := Real.mul_le_sin (x := 2*θ) (by linarith) (by linarith [hθ1, Real.pi_pos])
    calc (4/Real.pi) * θ = 2/Real.pi * (2*θ) := by ring
      _ ≤ Real.sin (2*θ) := h
  have hpos : 0 < (4/Real.pi) * θ := by positivity
  have hz : (-(Work.Spaces.eta)) ≤ 0 := by
    have := Work.Spaces.eta_pos; linarith
  rw [Work.FTS.EllipticEst.thEta]
  exact Real.rpow_le_rpow_of_nonpos hpos hs hz

/-- `cs1 θ ≤ ((4/π) θ)^{-(1+η)}` for `0 < θ ≤ π/4`. -/
private theorem cs1_le_left {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ Real.pi/4) :
    cs1 θ ≤ ((4/Real.pi) * θ) ^ (-(1 + Work.Spaces.eta)) := by
  have hs : (4/Real.pi) * θ ≤ Real.sin (2*θ) := by
    have h := Real.mul_le_sin (x := 2*θ) (by linarith) (by linarith [hθ1, Real.pi_pos])
    calc (4/Real.pi) * θ = 2/Real.pi * (2*θ) := by ring
      _ ≤ Real.sin (2*θ) := h
  have hpos : 0 < (4/Real.pi) * θ := by positivity
  have hz : (-(1 + Work.Spaces.eta)) ≤ 0 := by
    have := Work.Spaces.eta_pos; linarith
  have h1 : Real.sin (2*θ) ^ (-(1 + Work.Spaces.eta))
      ≤ ((4/Real.pi) * θ) ^ (-(1 + Work.Spaces.eta)) :=
    Real.rpow_le_rpow_of_nonpos hpos hs hz
  have hsin0 : 0 ≤ Real.sin (2*θ) := le_of_lt (by
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hθ1, Real.pi_pos]))
  have h2 : Real.cos (2*θ) ≤ 1 := Real.cos_le_one _
  rw [cs1]
  calc Real.cos (2*θ) * Real.sin (2*θ) ^ (-(1 + Work.Spaces.eta))
      ≤ 1 * Real.sin (2*θ) ^ (-(1 + Work.Spaces.eta)) :=
        mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hsin0 _)
    _ = Real.sin (2*θ) ^ (-(1 + Work.Spaces.eta)) := one_mul _
    _ ≤ ((4/Real.pi) * θ) ^ (-(1 + Work.Spaces.eta)) := h1

/-- `thEta θ ≤ ((4/π) (π/2 - θ))^{-η}` for `π/4 ≤ θ < π/2`. -/
private theorem thEta_le_right {θ : ℝ} (hθ0 : Real.pi/4 ≤ θ) (hθ1 : θ < Real.pi/2) :
    Work.FTS.EllipticEst.thEta θ ≤ ((4/Real.pi) * (Real.pi/2 - θ)) ^ (-(Work.Spaces.eta)) := by
  have hδ0 : 0 < Real.pi/2 - θ := by linarith
  have hδ1 : Real.pi/2 - θ ≤ Real.pi/4 := by linarith
  have hsin : Real.sin (2*θ) = Real.sin (2*(Real.pi/2 - θ)) := by
    rw [show 2*θ = Real.pi - 2*(Real.pi/2 - θ) by ring, Real.sin_pi_sub]
  rw [Work.FTS.EllipticEst.thEta, hsin]
  exact thEta_le_left hδ0 hδ1

/-- `cs1 θ ≤ ((4/π) (π/2 - θ))^{-(1+η)}` for `π/4 ≤ θ < π/2`. -/
private theorem cs1_le_right {θ : ℝ} (hθ0 : Real.pi/4 ≤ θ) (hθ1 : θ < Real.pi/2) :
    cs1 θ ≤ ((4/Real.pi) * (Real.pi/2 - θ)) ^ (-(1 + Work.Spaces.eta)) := by
  have hδ0 : 0 < Real.pi/2 - θ := by linarith
  have hδ1 : Real.pi/2 - θ ≤ Real.pi/4 := by linarith
  have hsin : Real.sin (2*θ) = Real.sin (2*(Real.pi/2 - θ)) := by
    rw [show 2*θ = Real.pi - 2*(Real.pi/2 - θ) by ring, Real.sin_pi_sub]
  have hcos : Real.cos (2*θ) = -Real.cos (2*(Real.pi/2 - θ)) := by
    rw [show 2*θ = Real.pi - 2*(Real.pi/2 - θ) by ring, Real.cos_pi_sub]
  have hδ12 : 2*(Real.pi/2 - θ) ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) :=
    ⟨by linarith [Real.pi_pos], by linarith⟩
  have hcs1nn : 0 ≤ cs1 (Real.pi/2 - θ) := by
    rw [cs1]
    refine mul_nonneg (Real.cos_nonneg_of_mem_Icc hδ12) ?_
    exact Real.rpow_nonneg (le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith)
      (by linarith [hδ1, Real.pi_pos]))) _
  have hneg : cs1 θ = - cs1 (Real.pi/2 - θ) := by
    rw [cs1, cs1, hcos, hsin]; ring
  rw [hneg]
  exact le_trans (neg_le_self hcs1nn) (cs1_le_left hδ0 hδ1)

/-! ## §3. Derivatives of the weights -/

/-- `HasDerivAt` of `sin (2 ·)`. -/
private theorem hasDerivAt_sin_two (θ : ℝ) :
    HasDerivAt (fun θ' : ℝ => Real.sin (2*θ')) (2 * Real.cos (2*θ)) θ := by
  have h1 : HasDerivAt (fun θ' : ℝ => 2*θ') (2 : ℝ) θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  exact ((Real.hasDerivAt_sin (2*θ)).comp θ h1).congr_deriv (by ring)

/-- `HasDerivAt` of `cos (2 ·)`. -/
private theorem hasDerivAt_cos_two (θ : ℝ) :
    HasDerivAt (fun θ' : ℝ => Real.cos (2*θ')) (-(2 * Real.sin (2*θ))) θ := by
  have h1 : HasDerivAt (fun θ' : ℝ => 2*θ') (2 : ℝ) θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  exact ((Real.hasDerivAt_cos (2*θ)).comp θ h1).congr_deriv (by ring)

/-- `HasDerivAt` of `thEta θ' = sin(2θ')^{-η}`, with the value written through `cs1`. -/
private theorem hasDerivAt_thEta {θ : ℝ} (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) :
    HasDerivAt Work.FTS.EllipticEst.thEta (-(2 * Work.Spaces.eta) * cs1 θ) θ := by
  have hsin := sin_two_pos_of_mem hθ
  have hbase : HasDerivAt (fun θ' : ℝ => Real.sin (2*θ') ^ (-(Work.Spaces.eta)))
      (-(2 * Work.Spaces.eta) * (Real.cos (2*θ) * Real.sin (2*θ) ^ (-(1 + Work.Spaces.eta)))) θ := by
    have h0 := (Real.hasDerivAt_rpow_const (x := Real.sin (2*θ)) (p := -(Work.Spaces.eta))
      (Or.inl hsin.ne')).comp θ (hasDerivAt_sin_two θ)
    have h1 : HasDerivAt (fun θ' : ℝ => Real.sin (2*θ') ^ (-(Work.Spaces.eta)))
        ((-(Work.Spaces.eta)) * Real.sin (2*θ) ^ (-(Work.Spaces.eta) - 1)
          * (2 * Real.cos (2*θ))) θ := by
      simpa [Function.comp_def] using h0
    refine h1.congr_deriv ?_
    rw [show -(Work.Spaces.eta) - 1 = -(1 + Work.Spaces.eta) by ring]
    ring
  rw [show Work.FTS.EllipticEst.thEta
    = (fun θ' : ℝ => Real.sin (2*θ') ^ (-(Work.Spaces.eta))) from rfl]
  simpa only [cs1] using hbase

/-- `HasDerivAt` of `cs1`, with value `-2 thEta θ - 2(1+η) csq θ`. -/
private theorem hasDerivAt_cs1 {θ : ℝ} (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) :
    HasDerivAt cs1 (-2 * Work.FTS.EllipticEst.thEta θ
      - 2*(1 + Work.Spaces.eta) * csq θ) θ := by
  have hsin := sin_two_pos_of_mem hθ
  have hbase : HasDerivAt (fun θ' : ℝ => Real.cos (2*θ') * Real.sin (2*θ') ^ (-(1 + Work.Spaces.eta)))
      (-2 * (Real.sin (2*θ) ^ (-(Work.Spaces.eta)))
        - 2*(1 + Work.Spaces.eta) * ((Real.cos (2*θ))^2 * Real.sin (2*θ) ^ (-(2 + Work.Spaces.eta)))) θ := by
    have h0 := (Real.hasDerivAt_rpow_const (x := Real.sin (2*θ)) (p := -(1 + Work.Spaces.eta))
      (Or.inl hsin.ne')).comp θ (hasDerivAt_sin_two θ)
    have hp : HasDerivAt (fun θ' : ℝ => Real.sin (2*θ') ^ (-(1 + Work.Spaces.eta)))
        ((-(1 + Work.Spaces.eta)) * Real.sin (2*θ) ^ (-(1 + Work.Spaces.eta) - 1)
          * (2 * Real.cos (2*θ))) θ := by
      simpa [Function.comp_def] using h0
    have hmul := (hasDerivAt_cos_two θ).mul hp
    refine hmul.congr_deriv ?_
    have hsinpow : Real.sin (2*θ) * Real.sin (2*θ) ^ (-(1 + Work.Spaces.eta))
        = Real.sin (2*θ) ^ (-(Work.Spaces.eta)) := by
      nth_rewrite 1 [← Real.rpow_one (Real.sin (2*θ))]
      rw [← Real.rpow_add hsin,
        show (1:ℝ) + -(1 + Work.Spaces.eta) = -(Work.Spaces.eta) by ring]
    rw [show -(1 + Work.Spaces.eta) - 1 = -(2 + Work.Spaces.eta) by ring]
    rw [show (-(2 * Real.sin (2*θ))) * Real.sin (2*θ) ^ (-(1 + Work.Spaces.eta))
        = -2 * (Real.sin (2*θ) * Real.sin (2*θ) ^ (-(1 + Work.Spaces.eta))) by ring]
    rw [hsinpow]
    ring
  rw [show cs1 = (fun θ' : ℝ => Real.cos (2*θ') * Real.sin (2*θ') ^ (-(1 + Work.Spaces.eta)))
    from rfl]
  simpa only [csq, Work.FTS.EllipticEst.thEta] using hbase

/-! ## §4. The primitives of the two integrations by parts -/

/-- The derivative of the primitive `f f' σ + η f² cs1`. -/
private theorem hasDerivAt_prim1 {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo (0:ℝ) (Real.pi/2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) :
    HasDerivAt (fun θ' : ℝ => f θ' * deriv f θ' * Work.FTS.EllipticEst.thEta θ'
        + Work.Spaces.eta * (f θ')^2 * cs1 θ')
      (((deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ
          + f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ)
        - (2 * Work.Spaces.eta) * ((f θ)^2 * Work.FTS.EllipticEst.thEta θ)
        - (2 * Work.Spaces.eta * (1 + Work.Spaces.eta)) * ((f θ)^2 * csq θ)) θ := by
  have hcd2 : ContDiffAt ℝ 2 f θ := hf.contDiffAt (Ioo_mem_nhds hθ.1 hθ.2)
  have hdf : HasDerivAt f (deriv f θ) θ := (hcd2.differentiableAt two_ne_zero).hasDerivAt
  have hdf' : HasDerivAt (deriv f) (deriv (deriv f) θ) θ :=
    ((hcd2.derivWithin (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasDerivAt
  have hσ := hasDerivAt_thEta hθ
  have hcs := hasDerivAt_cs1 hθ
  have h1 : HasDerivAt (fun θ' : ℝ => f θ' * deriv f θ' * Work.FTS.EllipticEst.thEta θ')
      ((deriv f θ * deriv f θ + f θ * deriv (deriv f) θ) * Work.FTS.EllipticEst.thEta θ
        + (f θ * deriv f θ) * (-(2 * Work.Spaces.eta) * cs1 θ)) θ :=
    (hdf.mul hdf').mul hσ
  have hp : HasDerivAt (fun θ' : ℝ => (f θ')^2) (2 * f θ * deriv f θ) θ :=
    (hdf.pow 2).congr_deriv (by ring)
  have h2 : HasDerivAt (fun θ' : ℝ => Work.Spaces.eta * (f θ')^2 * cs1 θ')
      (Work.Spaces.eta * (2 * f θ * deriv f θ) * cs1 θ
        + Work.Spaces.eta * (f θ)^2 * (-2 * Work.FTS.EllipticEst.thEta θ
          - 2*(1 + Work.Spaces.eta) * csq θ)) θ :=
    (hp.const_mul Work.Spaces.eta).mul hcs
  refine (h1.add h2).congr_deriv ?_
  simp only [cs1, csq, Work.FTS.EllipticEst.thEta]
  ring

/-- The derivative of the primitive `(1/2) f² cs1`. -/
private theorem hasDerivAt_prim2 {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo (0:ℝ) (Real.pi/2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) :
    HasDerivAt (fun θ' : ℝ => (1/2) * (f θ')^2 * cs1 θ')
      (f θ * deriv f θ * cs1 θ - (f θ)^2 * Work.FTS.EllipticEst.thEta θ
        - (1 + Work.Spaces.eta) * ((f θ)^2 * csq θ)) θ := by
  have hcd2 : ContDiffAt ℝ 2 f θ := hf.contDiffAt (Ioo_mem_nhds hθ.1 hθ.2)
  have hdf : HasDerivAt f (deriv f θ) θ := (hcd2.differentiableAt two_ne_zero).hasDerivAt
  have hcs := hasDerivAt_cs1 hθ
  have hp : HasDerivAt (fun θ' : ℝ => (f θ')^2) (2 * f θ * deriv f θ) θ :=
    (hdf.pow 2).congr_deriv (by ring)
  have h2 : HasDerivAt (fun θ' : ℝ => (1/2 : ℝ) * (f θ')^2 * cs1 θ')
      ((1/2 : ℝ) * (2 * f θ * deriv f θ) * cs1 θ
        + (1/2 : ℝ) * (f θ)^2 * (-2 * Work.FTS.EllipticEst.thEta θ
          - 2*(1 + Work.Spaces.eta) * csq θ)) θ :=
    (hp.const_mul (1/2 : ℝ)).mul hcs
  refine h2.congr_deriv ?_
  simp only [cs1, csq, Work.FTS.EllipticEst.thEta]
  ring

/-! ## §5. The two integrations by parts on an interior sub-interval -/

/-- The first integration by parts: on an interior sub-interval `[a,b]`,

`∫_a^b (f')² σ = [f f' σ + η f² cs1]_a^b - ∫_a^b f f'' σ + 2η ∫_a^b f² σ
  + 2η(1+η) ∫_a^b f² csq`. -/
private theorem ibp_main {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo (0:ℝ) (Real.pi/2)))
    {a b : ℝ} (ha : 0 < a) (hb : b < Real.pi/2) (hab : a ≤ b) :
    (∫ θ in a..b, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      = (f b * deriv f b * Work.FTS.EllipticEst.thEta b
            + Work.Spaces.eta * (f b) ^ 2 * cs1 b)
        - (f a * deriv f a * Work.FTS.EllipticEst.thEta a
            + Work.Spaces.eta * (f a) ^ 2 * cs1 a)
        - (∫ θ in a..b, f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ)
        + 2 * Work.Spaces.eta * (∫ θ in a..b, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        + 2 * Work.Spaces.eta * (1 + Work.Spaces.eta)
            * (∫ θ in a..b, (f θ) ^ 2 * csq θ) := by
  have hmem : ∀ x ∈ Set.uIcc a b, x ∈ Set.Ioo (0:ℝ) (Real.pi/2) := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩
  have hIoo : IsOpen (Set.Ioo (0:ℝ) (Real.pi/2)) := isOpen_Ioo
  have hcf : ContinuousOn f (Set.uIcc a b) := hf.continuousOn.mono hmem
  have hcf' : ContinuousOn (deriv f) (Set.uIcc a b) :=
    (hf.continuousOn_deriv_of_isOpen hIoo (by norm_num)).mono hmem
  have hcf'' : ContinuousOn (deriv (deriv f)) (Set.uIcc a b) := by
    have h1 : ContDiffOn ℝ 1 (deriv f) (Set.Ioo (0:ℝ) (Real.pi/2)) :=
      hf.deriv_of_isOpen hIoo (by norm_num)
    exact (contDiffOn_zero.1 (h1.deriv_of_isOpen hIoo (by norm_num))).mono hmem
  have hsinC : ContinuousOn (fun θ : ℝ => Real.sin (2*θ)) (Set.uIcc a b) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hsinne : ∀ θ ∈ Set.uIcc a b, Real.sin (2*θ) ≠ 0 := fun θ hθ =>
    (sin_two_pos_of_mem (hmem θ hθ)).ne'
  have hσC : ContinuousOn Work.FTS.EllipticEst.thEta (Set.uIcc a b) :=
    hsinC.rpow_const (fun θ hθ => Or.inl (hsinne θ hθ))
  have hcsqC : ContinuousOn csq (Set.uIcc a b) := by
    have h1 : ContinuousOn (fun θ : ℝ => (Real.cos (2*θ))^2) (Set.uIcc a b) :=
      ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn).pow 2
    have h2 : ContinuousOn (fun θ : ℝ => Real.sin (2*θ) ^ (-(2 + Work.Spaces.eta)))
        (Set.uIcc a b) := hsinC.rpow_const (fun θ hθ => Or.inl (hsinne θ hθ))
    exact h1.mul h2
  have hIA : IntervalIntegrable (fun θ : ℝ => (deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ)
      volume a b := ((hcf'.pow 2).mul hσC).intervalIntegrable
  have hIB : IntervalIntegrable
      (fun θ : ℝ => f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ) volume a b :=
    ((hcf.mul hcf'').mul hσC).intervalIntegrable
  have hIC : IntervalIntegrable (fun θ : ℝ => (f θ)^2 * Work.FTS.EllipticEst.thEta θ)
      volume a b := ((hcf.pow 2).mul hσC).intervalIntegrable
  have hID : IntervalIntegrable (fun θ : ℝ => (f θ)^2 * csq θ) volume a b :=
    ((hcf.pow 2).mul hcsqC).intervalIntegrable
  set G : ℝ → ℝ := fun θ : ℝ => ((deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ
        + f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ)
      - (2 * Work.Spaces.eta) * ((f θ)^2 * Work.FTS.EllipticEst.thEta θ)
      - (2 * Work.Spaces.eta * (1 + Work.Spaces.eta)) * ((f θ)^2 * csq θ) with hGdef
  set F : ℝ → ℝ := fun θ : ℝ => f θ * deriv f θ * Work.FTS.EllipticEst.thEta θ
      + Work.Spaces.eta * (f θ)^2 * cs1 θ with hFdef
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt F (G x) x := by
    intro x hx
    rw [hFdef, hGdef]
    exact hasDerivAt_prim1 hf (hmem x hx)
  have hAB : IntervalIntegrable (fun θ : ℝ => (deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ
      + f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ) volume a b := hIA.add hIB
  have h2C : IntervalIntegrable
      (fun θ : ℝ => (2 * Work.Spaces.eta) * ((f θ)^2 * Work.FTS.EllipticEst.thEta θ))
      volume a b := hIC.const_mul (2 * Work.Spaces.eta)
  have hAB2C : IntervalIntegrable
      (fun θ : ℝ => ((deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ
          + f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ)
        - (2 * Work.Spaces.eta) * ((f θ)^2 * Work.FTS.EllipticEst.thEta θ)) volume a b :=
    hAB.sub h2C
  have h2D : IntervalIntegrable
      (fun θ : ℝ => (2 * Work.Spaces.eta * (1 + Work.Spaces.eta)) * ((f θ)^2 * csq θ))
      volume a b := hID.const_mul _
  have hGint : IntervalIntegrable G volume a b := by
    rw [hGdef]; exact hAB2C.sub h2D
  have hFTC : (∫ θ in a..b, G θ) = F b - F a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hGint
  have hFb : F b = f b * deriv f b * Work.FTS.EllipticEst.thEta b
      + Work.Spaces.eta * (f b) ^ 2 * cs1 b := rfl
  have hFa : F a = f a * deriv f a * Work.FTS.EllipticEst.thEta a
      + Work.Spaces.eta * (f a) ^ 2 * cs1 a := rfl
  rw [hFb, hFa] at hFTC
  have hGval : (∫ θ in a..b, G θ)
      = (∫ θ in a..b, (deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ)
        + (∫ θ in a..b, f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ)
        - (2 * Work.Spaces.eta) * (∫ θ in a..b, (f θ)^2 * Work.FTS.EllipticEst.thEta θ)
        - (2 * Work.Spaces.eta * (1 + Work.Spaces.eta)) * (∫ θ in a..b, (f θ)^2 * csq θ) := by
    rw [hGdef]
    rw [intervalIntegral.integral_sub hAB2C h2D, intervalIntegral.integral_sub hAB h2C,
      intervalIntegral.integral_add hIA hIB, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  linarith [hFTC, hGval]

/-- The second integration by parts (the `cot`-primitive).

`∫_a^b f f' cs1 = ∫_a^b f² σ + (1+η) ∫_a^b f² csq + (1/2)[f² cs1]_a^b`. -/
private theorem ibp_cot {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo (0:ℝ) (Real.pi/2)))
    {a b : ℝ} (ha : 0 < a) (hb : b < Real.pi/2) (hab : a ≤ b) :
    (∫ θ in a..b, f θ * deriv f θ * cs1 θ)
      = (∫ θ in a..b, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        + (1 + Work.Spaces.eta) * (∫ θ in a..b, (f θ) ^ 2 * csq θ)
        + (1/2) * ((f b) ^ 2 * cs1 b - (f a) ^ 2 * cs1 a) := by
  have hmem : ∀ x ∈ Set.uIcc a b, x ∈ Set.Ioo (0:ℝ) (Real.pi/2) := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩
  have hIoo : IsOpen (Set.Ioo (0:ℝ) (Real.pi/2)) := isOpen_Ioo
  have hcf : ContinuousOn f (Set.uIcc a b) := hf.continuousOn.mono hmem
  have hcf' : ContinuousOn (deriv f) (Set.uIcc a b) :=
    (hf.continuousOn_deriv_of_isOpen hIoo (by norm_num)).mono hmem
  have hsinC : ContinuousOn (fun θ : ℝ => Real.sin (2*θ)) (Set.uIcc a b) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hsinne : ∀ θ ∈ Set.uIcc a b, Real.sin (2*θ) ≠ 0 := fun θ hθ =>
    (sin_two_pos_of_mem (hmem θ hθ)).ne'
  have hσC : ContinuousOn Work.FTS.EllipticEst.thEta (Set.uIcc a b) :=
    hsinC.rpow_const (fun θ hθ => Or.inl (hsinne θ hθ))
  have hcs1C : ContinuousOn cs1 (Set.uIcc a b) := by
    have h1 : ContinuousOn (fun θ : ℝ => Real.cos (2*θ)) (Set.uIcc a b) :=
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
    have h2 : ContinuousOn (fun θ : ℝ => Real.sin (2*θ) ^ (-(1 + Work.Spaces.eta)))
        (Set.uIcc a b) := hsinC.rpow_const (fun θ hθ => Or.inl (hsinne θ hθ))
    exact h1.mul h2
  have hcsqC : ContinuousOn csq (Set.uIcc a b) := by
    have h1 : ContinuousOn (fun θ : ℝ => (Real.cos (2*θ))^2) (Set.uIcc a b) :=
      ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn).pow 2
    have h2 : ContinuousOn (fun θ : ℝ => Real.sin (2*θ) ^ (-(2 + Work.Spaces.eta)))
        (Set.uIcc a b) := hsinC.rpow_const (fun θ hθ => Or.inl (hsinne θ hθ))
    exact h1.mul h2
  have hIBc : IntervalIntegrable (fun θ : ℝ => f θ * deriv f θ * cs1 θ) volume a b :=
    ((hcf.mul hcf').mul hcs1C).intervalIntegrable
  have hIC : IntervalIntegrable (fun θ : ℝ => (f θ)^2 * Work.FTS.EllipticEst.thEta θ)
      volume a b := ((hcf.pow 2).mul hσC).intervalIntegrable
  have hID : IntervalIntegrable (fun θ : ℝ => (f θ)^2 * csq θ) volume a b :=
    ((hcf.pow 2).mul hcsqC).intervalIntegrable
  set Q2 : ℝ → ℝ := fun θ : ℝ => f θ * deriv f θ * cs1 θ
      - (f θ)^2 * Work.FTS.EllipticEst.thEta θ
      - (1 + Work.Spaces.eta) * ((f θ)^2 * csq θ) with hQ2def
  set P2 : ℝ → ℝ := fun θ : ℝ => (1/2) * (f θ)^2 * cs1 θ with hP2def
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt P2 (Q2 x) x := by
    intro x hx
    rw [hP2def, hQ2def]
    exact hasDerivAt_prim2 hf (hmem x hx)
  have hB2 : IntervalIntegrable
      (fun θ : ℝ => f θ * deriv f θ * cs1 θ - (f θ)^2 * Work.FTS.EllipticEst.thEta θ)
      volume a b := hIBc.sub hIC
  have h1e : IntervalIntegrable
      (fun θ : ℝ => (1 + Work.Spaces.eta) * ((f θ)^2 * csq θ)) volume a b :=
    hID.const_mul _
  have hQ2int : IntervalIntegrable Q2 volume a b := by
    rw [hQ2def]; exact hB2.sub h1e
  have hFTC : (∫ θ in a..b, Q2 θ) = P2 b - P2 a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hQ2int
  have hPb : P2 b = (1/2) * (f b)^2 * cs1 b := rfl
  have hPa : P2 a = (1/2) * (f a)^2 * cs1 a := rfl
  rw [hPb, hPa] at hFTC
  have hQ2val : (∫ θ in a..b, Q2 θ)
      = (∫ θ in a..b, f θ * deriv f θ * cs1 θ)
        - (∫ θ in a..b, (f θ)^2 * Work.FTS.EllipticEst.thEta θ)
        - (1 + Work.Spaces.eta) * (∫ θ in a..b, (f θ)^2 * csq θ) := by
    rw [hQ2def]
    rw [intervalIntegral.integral_sub hB2 h1e, intervalIntegral.integral_sub hIBc hIC,
      intervalIntegral.integral_const_mul]
  linarith [hFTC, hQ2val]

/-! ## §6. The truncating sequences -/

/-- The left truncation point `a_n = 1/(n+2)`. -/
private def za (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)

/-- The right truncation point `b_n = π/2 - 1/(n+2)`. -/
private def zb (n : ℕ) : ℝ := Real.pi / 2 - 1 / ((n : ℝ) + 2)

private theorem za_pos (n : ℕ) : 0 < za n := by
  rw [za]; positivity

private theorem za_le_half (n : ℕ) : za n ≤ 1/2 := by
  rw [za, div_le_iff₀ (by positivity)]
  have h : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  linarith

private theorem za_lt_pi4 (n : ℕ) : za n < Real.pi / 4 := by
  rw [za, div_lt_iff₀ (by positivity)]
  have h : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  nlinarith [Real.pi_gt_three]

private theorem zb_lt_pi2 (n : ℕ) : zb n < Real.pi / 2 := by
  have h : 0 < (1:ℝ) / ((n:ℝ) + 2) := za_pos n
  rw [zb]
  linarith

private theorem zb_ge_pi4 (n : ℕ) : Real.pi / 4 ≤ zb n := by
  have h : (1:ℝ) / ((n:ℝ) + 2) < Real.pi/4 := za_lt_pi4 n
  rw [zb]
  linarith

private theorem za_lt_zb (n : ℕ) : za n < zb n := by
  have h1 : za n < Real.pi/4 := za_lt_pi4 n
  have h2 : Real.pi/4 ≤ zb n := zb_ge_pi4 n
  linarith

private theorem za_mem (n : ℕ) : za n ∈ Set.Ioo (0:ℝ) (Real.pi/2) :=
  ⟨za_pos n, lt_trans (za_lt_pi4 n) (by linarith [Real.pi_pos])⟩

private theorem zb_mem (n : ℕ) : zb n ∈ Set.Ioo (0:ℝ) (Real.pi/2) :=
  ⟨lt_of_lt_of_le (by linarith [Real.pi_pos]) (zb_ge_pi4 n), zb_lt_pi2 n⟩

private theorem za_antitone : Antitone za := by
  intro m n hmn
  rw [za, za]
  refine one_div_le_one_div_of_le (by positivity) ?_
  have : (m:ℝ) ≤ (n:ℝ) := by exact_mod_cast hmn
  linarith

private theorem zb_monotone : Monotone zb := by
  intro m n hmn
  rw [zb, zb]
  have h : (1:ℝ) / ((n:ℝ) + 2) ≤ 1 / ((m:ℝ) + 2) := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    have : (m:ℝ) ≤ (n:ℝ) := by exact_mod_cast hmn
    linarith
  linarith

private theorem tendsto_za : Tendsto za atTop (nhds 0) := by
  have h : Tendsto (fun n : ℕ => ((n:ℝ) + 2)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have h2 : Tendsto (fun n : ℕ => (1:ℝ) / ((n:ℝ) + 2)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop h
  exact h2

private theorem tendsto_zb : Tendsto zb atTop (nhds (Real.pi/2)) := by
  have h : Tendsto (fun n : ℕ => Real.pi/2 - 1 / ((n:ℝ) + 2)) atTop (nhds (Real.pi/2 - 0)) :=
    tendsto_const_nhds.sub tendsto_za
  rw [sub_zero] at h
  exact h

private theorem tendsto_za_nhdsWithin : Tendsto za atTop (nhdsWithin (0:ℝ) (Set.Ioi 0)) := by
  rw [tendsto_nhdsWithin_iff]
  exact ⟨tendsto_za, Eventually.of_forall fun n => za_pos n⟩

/-- The elementary power limits at the two endpoints. -/
private theorem tendsto_rpow_pos_nhdsGT_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun θ : ℝ => θ ^ a) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
  have h := (tendsto_rpow_neg_nhdsGT_zero (show -a < 0 by linarith)).inv_tendsto_atTop
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  show (θ ^ (-a))⁻¹ = θ ^ a
  rw [Real.rpow_neg (le_of_lt hθ), inv_inv]

private theorem tendsto_rpow_za {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => (za n) ^ a) atTop (nhds 0) :=
  (tendsto_rpow_pos_nhdsGT_zero ha).comp tendsto_za_nhdsWithin

/-- `√(c θ^{1+η}) = √c · θ^{(1+η)/2}`. -/
private theorem sqrt_mul_rpow_half {c θ : ℝ} (hc : 0 ≤ c) (hθ : 0 ≤ θ) :
    Real.sqrt (c * θ ^ (1 + Work.Spaces.eta)) = Real.sqrt c * θ ^ ((1 + Work.Spaces.eta)/2) := by
  have h1 : Real.sqrt (θ ^ (1 + Work.Spaces.eta)) = θ ^ ((1 + Work.Spaces.eta)/2) := by
    have hsq : θ ^ ((1 + Work.Spaces.eta)/2) * θ ^ ((1 + Work.Spaces.eta)/2)
        = θ ^ (1 + Work.Spaces.eta) := by
      rw [← Real.rpow_add' hθ (by linarith [Work.Spaces.eta_pos]),
        show (1 + Work.Spaces.eta)/2 + (1 + Work.Spaces.eta)/2 = 1 + Work.Spaces.eta by ring]
    rw [← hsq, Real.sqrt_mul (Real.rpow_nonneg hθ _), ← pow_two,
      Real.sq_sqrt (Real.rpow_nonneg hθ _)]
  rw [Real.sqrt_mul hc, h1]

/-- `cs1` is nonnegative on `(0, π/4]`. -/
private theorem cs1_nonneg_left {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ Real.pi/4) : 0 ≤ cs1 θ := by
  have h2θ : 2*θ ≤ Real.pi/2 := by linarith [hθ1, Real.pi_pos]
  have hc : 0 ≤ Real.cos (2*θ) := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Real.pi_pos], h2θ⟩
  rw [cs1]
  refine mul_nonneg hc ?_
  exact Real.rpow_nonneg (le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))) _

/-! ## §7. The tails of an integrable function -/

/-- The integral of an integrable function over the shrinking left intervals tends to `0`. -/
private theorem tail_left (g : ℝ → ℝ) (hg : IntegrableOn g (Set.Ioo (0:ℝ) (Real.pi/2))) :
    Tendsto (fun n : ℕ => ∫ t in Set.Ioo (0:ℝ) (za n), g t) atTop (nhds 0) := by
  have hmeas : ∀ n : ℕ, MeasurableSet (Set.Ioo (0:ℝ) (za n)) := fun n => measurableSet_Ioo
  have hanti : Antitone (fun n : ℕ => Set.Ioo (0:ℝ) (za n)) := by
    intro m n hmn x hx
    exact ⟨hx.1, lt_of_lt_of_le hx.2 (za_antitone hmn)⟩
  have hint : IntegrableOn g (Set.Ioo (0:ℝ) (za 0)) :=
    hg.mono_set (fun x hx => ⟨hx.1, lt_of_lt_of_le hx.2 (le_of_lt (za_mem 0).2)⟩)
  have h := Antitone.tendsto_setIntegral hmeas hanti hint
  have hInter : (⋂ n : ℕ, Set.Ioo (0:ℝ) (za n)) = ∅ := by
    ext x
    constructor
    · intro hx
      have hx0 : (0:ℝ) < x := (Set.mem_iInter.mp hx 0).1
      obtain ⟨k, hk⟩ := exists_nat_gt (1/x)
      have hkx : (1:ℝ) / ((k:ℝ) + 2) < x := by
        rw [div_lt_iff₀ (by positivity)]
        have h2 : (1:ℝ)/x < (k:ℝ) + 2 := by
          have : (k:ℝ) < (k:ℝ) + 2 := by linarith
          linarith [hk]
        rw [div_lt_iff₀ hx0] at h2
        linarith [h2]
      exact absurd (Set.mem_iInter.mp hx k).2 (not_lt.mpr hkx.le)
    · intro hx; exact absurd hx (Set.notMem_empty x)
  rw [hInter, MeasureTheory.setIntegral_empty] at h
  simpa using h

/-- The integral of an integrable function over the shrinking right intervals tends to `0`. -/
private theorem tail_right (g : ℝ → ℝ) (hg : IntegrableOn g (Set.Ioo (0:ℝ) (Real.pi/2))) :
    Tendsto (fun n : ℕ => ∫ t in Set.Ioo (zb n) (Real.pi/2), g t) atTop (nhds 0) := by
  have hmeas : ∀ n : ℕ, MeasurableSet (Set.Ioo (zb n) (Real.pi/2)) := fun n => measurableSet_Ioo
  have hanti : Antitone (fun n : ℕ => Set.Ioo (zb n) (Real.pi/2)) := by
    intro m n hmn x hx
    exact ⟨lt_of_le_of_lt (zb_monotone hmn) hx.1, hx.2⟩
  have hint : IntegrableOn g (Set.Ioo (zb 0) (Real.pi/2)) :=
    hg.mono_set (fun x hx => ⟨lt_of_lt_of_le (zb_mem 0).1 (le_of_lt hx.1), hx.2⟩)
  have h := Antitone.tendsto_setIntegral hmeas hanti hint
  have hInter : (⋂ n : ℕ, Set.Ioo (zb n) (Real.pi/2)) = ∅ := by
    ext x
    constructor
    · intro hx
      have hxlt : x < Real.pi/2 := (Set.mem_iInter.mp hx 0).2
      have hposd : 0 < Real.pi/2 - x := by linarith
      obtain ⟨k, hk⟩ := exists_nat_gt (1/(Real.pi/2 - x))
      have h1 : x < zb k := by
        rw [zb]
        have h3 : (1:ℝ) / ((k:ℝ) + 2) < Real.pi/2 - x := by
          rw [div_lt_iff₀ (by positivity)]
          have h4 : (1:ℝ)/(Real.pi/2 - x) < (k:ℝ) + 2 := by
            have : (k:ℝ) < (k:ℝ) + 2 := by linarith
            linarith [hk]
          rw [div_lt_iff₀ hposd] at h4
          linarith [h4]
        linarith
      exact absurd (Set.mem_iInter.mp hx k).1 (not_lt.mpr h1.le)
    · intro hx; exact absurd hx (Set.notMem_empty x)
  rw [hInter, MeasureTheory.setIntegral_empty] at h
  simpa using h

/-! ## §8. Monotone convergence of the truncated integrals -/

/-- The truncated integrals increase to the full integral over `Iθ`. -/
private theorem expandingIntegral (g : ℝ → ℝ) (hg : IntegrableOn g Work.Spaces.Iθ)
    (hgn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ g θ) :
    Tendsto (fun n : ℕ => ∫ x in (za n)..(zb n), g x) atTop (nhds (∫ x in Work.Spaces.Iθ, g x)) := by
  have hIθ : Work.Spaces.Iθ = Set.Icc (0:ℝ) (Real.pi/2) := rfl
  have hsub : ∀ n : ℕ, Set.Icc (za n) (zb n) ⊆ Work.Spaces.Iθ := by
    intro n x hx
    rw [Set.mem_Icc] at hx
    exact ⟨le_of_lt (lt_of_lt_of_le (za_pos n) hx.1),
      le_of_lt (lt_of_le_of_lt hx.2 (zb_lt_pi2 n))⟩
  have hIθmeas : MeasurableSet Work.Spaces.Iθ := by rw [hIθ]; exact measurableSet_Icc
  have hmeas : ∀ n : ℕ, MeasurableSet (Work.Spaces.Iθ \ Set.Icc (za n) (zb n)) :=
    fun n => hIθmeas.diff measurableSet_Icc
  have hanti : Antitone (fun n : ℕ => Work.Spaces.Iθ \ Set.Icc (za n) (zb n)) := by
    intro m n hmn x hx
    exact ⟨hx.1, fun hxin => hx.2 (Set.Icc_subset_Icc (za_antitone hmn) (zb_monotone hmn) hxin)⟩
  have hint : IntegrableOn g (Work.Spaces.Iθ \ Set.Icc (za 0) (zb 0)) :=
    hg.mono_set Set.sdiff_subset
  have hlim := Antitone.tendsto_setIntegral hmeas hanti hint
  have hInter : (⋂ n : ℕ, (Work.Spaces.Iθ \ Set.Icc (za n) (zb n))) = {0, Real.pi/2} := by
    ext x
    constructor
    · intro hx
      have hxI : x ∈ Work.Spaces.Iθ := (Set.mem_iInter.mp hx 0).1
      rw [hIθ, Set.mem_Icc] at hxI
      rw [Set.mem_insert_iff, Set.mem_singleton_iff]
      by_contra hcon
      push_neg at hcon
      obtain ⟨hx0, hxpi⟩ := hcon
      have hxpos : 0 < x := lt_of_le_of_ne hxI.1 (Ne.symm hx0)
      have hxlt : x < Real.pi/2 := lt_of_le_of_ne hxI.2 hxpi
      obtain ⟨k, hk⟩ := exists_nat_gt (1/x)
      have hza : za k < x := by
        rw [za, div_lt_iff₀ (by positivity)]
        have h4 : (1:ℝ)/x < (k:ℝ) + 2 := by
          have h5 : (k:ℝ) < (k:ℝ) + 2 := by linarith
          linarith [hk]
        rw [div_lt_iff₀ hxpos] at h4
        linarith [h4]
      have hposd : 0 < Real.pi/2 - x := by linarith
      obtain ⟨l, hl⟩ := exists_nat_gt (1/(Real.pi/2 - x))
      have hzb : x < zb l := by
        rw [zb]
        have h5 : (1:ℝ)/((l:ℝ) + 2) < Real.pi/2 - x := by
          rw [div_lt_iff₀ (by positivity)]
          have h6 : (1:ℝ)/(Real.pi/2 - x) < (l:ℝ) + 2 := by
            have h7 : (l:ℝ) < (l:ℝ) + 2 := by linarith
            linarith [hl]
          rw [div_lt_iff₀ hposd] at h6
          linarith [h6]
        linarith
      have hmem : x ∈ Set.Icc (za (max k l)) (zb (max k l)) :=
        ⟨le_of_lt (lt_of_le_of_lt (za_antitone (le_max_left k l)) hza),
          le_of_lt (lt_of_lt_of_le hzb (zb_monotone (le_max_right k l)))⟩
      exact (Set.mem_iInter.mp hx (max k l)).2 hmem
    · intro hx
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rw [Set.mem_iInter]
      intro n
      constructor
      · rw [hIθ, Set.mem_Icc]
        rcases hx with h | h
        · rw [h]; exact ⟨le_refl 0, by linarith [Real.pi_pos]⟩
        · rw [h]; exact ⟨by linarith [Real.pi_pos], le_refl _⟩
      · intro hmem
        rw [Set.mem_Icc] at hmem
        rcases hx with h | h
        · rw [h] at hmem; exact absurd hmem.1 (not_le.mpr (za_pos n))
        · rw [h] at hmem; exact absurd hmem.2 (not_le.mpr (zb_lt_pi2 n))
  rw [hInter] at hlim
  have hzero : (∫ x in ({0, Real.pi/2} : Set ℝ), g x) = 0 :=
    MeasureTheory.setIntegral_measure_zero _ (Set.Finite.measure_zero (by simp) MeasureTheory.volume)
  rw [hzero] at hlim
  have hdisj : ∀ n : ℕ, Disjoint (Work.Spaces.Iθ \ Set.Icc (za n) (zb n))
      (Set.Icc (za n) (zb n)) := by
    intro n
    rw [Set.disjoint_iff]
    intro x hx1
    exact hx1.1.2 hx1.2
  have hunion : ∀ n : ℕ, (Work.Spaces.Iθ \ Set.Icc (za n) (zb n)) ∪ Set.Icc (za n) (zb n)
      = Work.Spaces.Iθ := by
    intro n
    ext x
    constructor
    · rintro (⟨h1, -⟩ | h2)
      · exact h1
      · exact hsub n h2
    · intro hx
      by_cases h : x ∈ Set.Icc (za n) (zb n)
      · exact Or.inr h
      · exact Or.inl ⟨hx, h⟩
  have hadd : ∀ n : ℕ, (∫ x in Work.Spaces.Iθ \ Set.Icc (za n) (zb n), g x)
      + (∫ x in Set.Icc (za n) (zb n), g x) = (∫ x in Work.Spaces.Iθ, g x) := by
    intro n
    rw [← MeasureTheory.setIntegral_union (hdisj n) measurableSet_Icc
      (hg.mono_set Set.sdiff_subset) (hg.mono_set (hsub n)), hunion n]
  have hpoint : ∀ n : ℕ, (∫ x in Set.Icc (za n) (zb n), g x)
      = (∫ x in Work.Spaces.Iθ, g x)
        - (∫ x in Work.Spaces.Iθ \ Set.Icc (za n) (zb n), g x) := fun n => by linarith [hadd n]
  have hlim2 : Tendsto (fun n : ℕ => ∫ x in Set.Icc (za n) (zb n), g x) atTop
      (nhds (∫ x in Work.Spaces.Iθ, g x)) := by
    have h' : Tendsto (fun n : ℕ => (∫ x in Work.Spaces.Iθ, g x)
        - (∫ x in Work.Spaces.Iθ \ Set.Icc (za n) (zb n), g x)) atTop
        (nhds ((∫ x in Work.Spaces.Iθ, g x) - 0)) := tendsto_const_nhds.sub hlim
    rw [sub_zero] at h'
    refine h'.congr' ?_
    filter_upwards with n
    exact (hpoint n).symm
  refine hlim2.congr' ?_
  filter_upwards with n
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (le_of_lt (za_lt_zb n))]

/-! ## §9. The endpoint analysis and the Cauchy–Schwarz bound -/

/-- The interval-integrability of the five integrands on an interior sub-interval. -/
private theorem intervalIntegrable_pieces {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ioo (0:ℝ) (Real.pi/2)))
    {a b : ℝ} (ha : 0 < a) (hb : b < Real.pi/2) (hab : a ≤ b) :
    IntervalIntegrable (fun θ : ℝ => (deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ) volume a b
    ∧ IntervalIntegrable (fun θ : ℝ => f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ)
        volume a b
    ∧ IntervalIntegrable (fun θ : ℝ => (f θ)^2 * Work.FTS.EllipticEst.thEta θ) volume a b
    ∧ IntervalIntegrable (fun θ : ℝ => (f θ)^2 * csq θ) volume a b
    ∧ IntervalIntegrable (fun θ : ℝ => f θ * deriv f θ * cs1 θ) volume a b
    ∧ IntervalIntegrable (fun θ : ℝ => (deriv (deriv f) θ)^2 * Work.FTS.EllipticEst.thEta θ)
        volume a b := by
  have hmem : ∀ x ∈ Set.uIcc a b, x ∈ Set.Ioo (0:ℝ) (Real.pi/2) := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩
  have hIoo : IsOpen (Set.Ioo (0:ℝ) (Real.pi/2)) := isOpen_Ioo
  have hcf : ContinuousOn f (Set.uIcc a b) := hf.continuousOn.mono hmem
  have hcf' : ContinuousOn (deriv f) (Set.uIcc a b) :=
    (hf.continuousOn_deriv_of_isOpen hIoo (by norm_num)).mono hmem
  have hcf'' : ContinuousOn (deriv (deriv f)) (Set.uIcc a b) := by
    have h1 : ContDiffOn ℝ 1 (deriv f) (Set.Ioo (0:ℝ) (Real.pi/2)) :=
      hf.deriv_of_isOpen hIoo (by norm_num)
    exact (contDiffOn_zero.1 (h1.deriv_of_isOpen hIoo (by norm_num))).mono hmem
  have hsinC : ContinuousOn (fun θ : ℝ => Real.sin (2*θ)) (Set.uIcc a b) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hsinne : ∀ θ ∈ Set.uIcc a b, Real.sin (2*θ) ≠ 0 := fun θ hθ =>
    (sin_two_pos_of_mem (hmem θ hθ)).ne'
  have hσC : ContinuousOn Work.FTS.EllipticEst.thEta (Set.uIcc a b) :=
    hsinC.rpow_const (fun θ hθ => Or.inl (hsinne θ hθ))
  have hcs1C : ContinuousOn cs1 (Set.uIcc a b) := by
    have h1 : ContinuousOn (fun θ : ℝ => Real.cos (2*θ)) (Set.uIcc a b) :=
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
    have h2 : ContinuousOn (fun θ : ℝ => Real.sin (2*θ) ^ (-(1 + Work.Spaces.eta)))
        (Set.uIcc a b) := hsinC.rpow_const (fun θ hθ => Or.inl (hsinne θ hθ))
    exact h1.mul h2
  have hcsqC : ContinuousOn csq (Set.uIcc a b) := by
    have h1 : ContinuousOn (fun θ : ℝ => (Real.cos (2*θ))^2) (Set.uIcc a b) :=
      ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn).pow 2
    have h2 : ContinuousOn (fun θ : ℝ => Real.sin (2*θ) ^ (-(2 + Work.Spaces.eta)))
        (Set.uIcc a b) := hsinC.rpow_const (fun θ hθ => Or.inl (hsinne θ hθ))
    exact h1.mul h2
  exact ⟨((hcf'.pow 2).mul hσC).intervalIntegrable, ((hcf.mul hcf'').mul hσC).intervalIntegrable,
    ((hcf.pow 2).mul hσC).intervalIntegrable, ((hcf.pow 2).mul hcsqC).intervalIntegrable,
    ((hcf.mul hcf').mul hcs1C).intervalIntegrable, ((hcf''.pow 2).mul hσC).intervalIntegrable⟩

/-- The pointwise expansion of the completed square. -/
private theorem sq_expand_pointwise {f : ℝ → ℝ} {θ : ℝ} (hsin : 0 < Real.sin (2*θ)) :
    (deriv f θ - (1 + Work.Spaces.eta) * f θ * (Real.cos (2*θ)/Real.sin (2*θ)))^2
        * Work.FTS.EllipticEst.thEta θ
      = (deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ
        - 2*(1 + Work.Spaces.eta) * (f θ * deriv f θ * cs1 θ)
        + (1 + Work.Spaces.eta)^2 * ((f θ)^2 * csq θ) := by
  have k1 : Real.cos (2*θ)/Real.sin (2*θ) * Work.FTS.EllipticEst.thEta θ = cs1 θ :=
    cossin_mul_thEta hsin
  have k2 : (Real.cos (2*θ)/Real.sin (2*θ))^2 * Work.FTS.EllipticEst.thEta θ = csq θ :=
    cossin_sq_mul_thEta hsin
  calc (deriv f θ - (1 + Work.Spaces.eta) * f θ * (Real.cos (2*θ)/Real.sin (2*θ)))^2
        * Work.FTS.EllipticEst.thEta θ
      = ((deriv f θ)^2
          - 2*(1 + Work.Spaces.eta)*(deriv f θ * f θ * (Real.cos (2*θ)/Real.sin (2*θ)))
          + (1 + Work.Spaces.eta)^2 * ((f θ)^2 * (Real.cos (2*θ)/Real.sin (2*θ))^2))
        * Work.FTS.EllipticEst.thEta θ := by ring
    _ = (deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ
          - 2*(1 + Work.Spaces.eta) * ((deriv f θ * f θ)
              * ((Real.cos (2*θ)/Real.sin (2*θ)) * Work.FTS.EllipticEst.thEta θ))
          + (1 + Work.Spaces.eta)^2 * ((f θ)^2
              * ((Real.cos (2*θ)/Real.sin (2*θ))^2 * Work.FTS.EllipticEst.thEta θ)) := by ring
    _ = (deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ
          - 2*(1 + Work.Spaces.eta) * ((deriv f θ * f θ) * cs1 θ)
          + (1 + Work.Spaces.eta)^2 * ((f θ)^2 * csq θ) := by rw [k1, k2]
    _ = (deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ
          - 2*(1 + Work.Spaces.eta) * (f θ * deriv f θ * cs1 θ)
          + (1 + Work.Spaces.eta)^2 * ((f θ)^2 * csq θ) := by ring

/-- The two endpoint weights `f f' σ` and `f² cs1` vanish along the truncating sequence. -/
private theorem traceBoundarySeq {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ioo (0:ℝ) (Real.pi/2)))
    (h0 : Tendsto f (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0))
    (h1 : Tendsto f (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds 0))
    (hA : IntegrableOn (fun θ : ℝ => (deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo 0 (Real.pi/2)))
    (hE : IntegrableOn (fun θ : ℝ => (deriv (deriv f) θ)^2 * Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo 0 (Real.pi/2))) :
    (Tendsto (fun n : ℕ => f (za n) * deriv f (za n) * Work.FTS.EllipticEst.thEta (za n))
        atTop (nhds 0))
    ∧ (Tendsto (fun n : ℕ => (f (za n))^2 * cs1 (za n)) atTop (nhds 0))
    ∧ (Tendsto (fun n : ℕ => f (zb n) * deriv f (zb n) * Work.FTS.EllipticEst.thEta (zb n))
        atTop (nhds 0))
    ∧ (Tendsto (fun n : ℕ => (f (zb n))^2 * cs1 (zb n)) atTop (nhds 0)) := by
  obtain ⟨K, hKpos, hmain⟩ := Work.EllipticEst.Core.sliceBoundaryLimit
  have hd1 : ContDiffOn ℝ 1 (deriv f) (Set.Ioo (0:ℝ) (Real.pi/2)) :=
    hf.deriv_of_isOpen isOpen_Ioo (by norm_num)
  obtain ⟨c1, hc1tend, hc1bnd⟩ := (hmain f (hf.of_le (by norm_num)) hA).1
  have hc1z : c1 = 0 := tendsto_nhds_unique hc1tend h0
  obtain ⟨c2, hc2tend, hc2bnd⟩ := (hmain (deriv f) hd1 hE).1
  obtain ⟨d1, hd1tend, hd1bnd⟩ := (hmain f (hf.of_le (by norm_num)) hA).2
  have hd1z : d1 = 0 := tendsto_nhds_unique hd1tend h1
  obtain ⟨d2, hd2tend, hd2bnd⟩ := (hmain (deriv f) hd1 hE).2
  set Aoo : ℝ := ∫ t in Set.Ioo (0:ℝ) (Real.pi/2), (deriv f t)^2 * Work.FTS.EllipticEst.thEta t
    with hAoo
  set Eoo : ℝ := ∫ t in Set.Ioo (0:ℝ) (Real.pi/2),
    (deriv (deriv f) t)^2 * Work.FTS.EllipticEst.thEta t with hEoo
  have hAoonn : 0 ≤ Aoo := by
    rw [hAoo]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun t ht => mul_nonneg (sq_nonneg _)
      (le_of_lt (thEta_pos_of_mem ht)))
  have hEoonn : 0 ≤ Eoo := by
    rw [hEoo]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun t ht => mul_nonneg (sq_nonneg _)
      (le_of_lt (thEta_pos_of_mem ht)))
  -- the two Agmon bounds at the left endpoint
  have hbndfL : ∀ n : ℕ, (f (za n))^2 ≤ K * (za n)^(1 + Work.Spaces.eta)
      * (∫ t in Set.Ioo (0:ℝ) (za n), (deriv f t)^2 * Work.FTS.EllipticEst.thEta t) := by
    intro n
    have h := hc1bnd (za n) (za_mem n)
    rw [hc1z, sub_zero] at h
    exact h
  have hbndgL : ∀ n : ℕ, (deriv f (za n) - c2)^2 ≤ K * (za n)^(1 + Work.Spaces.eta)
      * (∫ t in Set.Ioo (0:ℝ) (za n), (deriv (deriv f) t)^2 * Work.FTS.EllipticEst.thEta t) :=
    fun n => hc2bnd (za n) (za_mem n)
  -- the two Agmon bounds at the right endpoint
  have hbndfR : ∀ n : ℕ, (f (zb n))^2 ≤ K * (Real.pi/2 - zb n)^(1 + Work.Spaces.eta)
      * (∫ t in Set.Ioo (zb n) (Real.pi/2), (deriv f t)^2 * Work.FTS.EllipticEst.thEta t) := by
    intro n
    have h := hd1bnd (zb n) (zb_mem n)
    rw [hd1z, sub_zero] at h
    exact h
  have hbndgR : ∀ n : ℕ, (deriv f (zb n) - d2)^2 ≤ K * (Real.pi/2 - zb n)^(1 + Work.Spaces.eta)
      * (∫ t in Set.Ioo (zb n) (Real.pi/2), (deriv (deriv f) t)^2 * Work.FTS.EllipticEst.thEta t) :=
    fun n => hd2bnd (zb n) (zb_mem n)
  have hδn : ∀ n : ℕ, Real.pi/2 - zb n = za n := by
    intro n
    rw [zb, za]; ring
  have htailAL : ∀ n : ℕ, (∫ t in Set.Ioo (0:ℝ) (za n),
      (deriv f t)^2 * Work.FTS.EllipticEst.thEta t) ≤ Aoo := by
    intro n
    rw [hAoo]
    refine MeasureTheory.setIntegral_mono_set hA ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      exact mul_nonneg (sq_nonneg _) (le_of_lt (thEta_pos_of_mem ht))
    · filter_upwards with t ht
      exact ⟨ht.1, lt_of_lt_of_le ht.2 (le_of_lt (za_mem n).2)⟩
  have htailEL : ∀ n : ℕ, (∫ t in Set.Ioo (0:ℝ) (za n),
      (deriv (deriv f) t)^2 * Work.FTS.EllipticEst.thEta t) ≤ Eoo := by
    intro n
    rw [hEoo]
    refine MeasureTheory.setIntegral_mono_set hE ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      exact mul_nonneg (sq_nonneg _) (le_of_lt (thEta_pos_of_mem ht))
    · filter_upwards with t ht
      exact ⟨ht.1, lt_of_lt_of_le ht.2 (le_of_lt (za_mem n).2)⟩
  have htailAR : ∀ n : ℕ, (∫ t in Set.Ioo (zb n) (Real.pi/2),
      (deriv f t)^2 * Work.FTS.EllipticEst.thEta t) ≤ Aoo := by
    intro n
    rw [hAoo]
    refine MeasureTheory.setIntegral_mono_set hA ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      exact mul_nonneg (sq_nonneg _) (le_of_lt (thEta_pos_of_mem ht))
    · filter_upwards with t ht
      exact ⟨lt_trans (zb_mem n).1 ht.1, ht.2⟩
  have htailER : ∀ n : ℕ, (∫ t in Set.Ioo (zb n) (Real.pi/2),
      (deriv (deriv f) t)^2 * Work.FTS.EllipticEst.thEta t) ≤ Eoo := by
    intro n
    rw [hEoo]
    refine MeasureTheory.setIntegral_mono_set hE ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      exact mul_nonneg (sq_nonneg _) (le_of_lt (thEta_pos_of_mem ht))
    · filter_upwards with t ht
      exact ⟨lt_trans (zb_mem n).1 ht.1, ht.2⟩
  -- the bounds on the factors
  have hfbL : ∀ n : ℕ, |f (za n)| ≤ Real.sqrt (K * Aoo) * (za n)^((1 + Work.Spaces.eta)/2) := by
    intro n
    have h1 : (f (za n))^2 ≤ K * Aoo * (za n)^(1 + Work.Spaces.eta) := by
      have h2 := hbndfL n
      have h3 := htailAL n
      calc (f (za n))^2 ≤ K * (za n)^(1 + Work.Spaces.eta)
            * (∫ t in Set.Ioo (0:ℝ) (za n), (deriv f t)^2 * Work.FTS.EllipticEst.thEta t) := h2
        _ ≤ K * (za n)^(1 + Work.Spaces.eta) * Aoo :=
            mul_le_mul_of_nonneg_left h3 (mul_nonneg hKpos.le
              (Real.rpow_nonneg (le_of_lt (za_pos n)) _))
        _ = K * Aoo * (za n)^(1 + Work.Spaces.eta) := by ring
    have h2 : Real.sqrt ((f (za n))^2) ≤ Real.sqrt (K * Aoo * (za n)^(1 + Work.Spaces.eta)) :=
      Real.sqrt_le_sqrt h1
    rw [Real.sqrt_sq_eq_abs] at h2
    rw [sqrt_mul_rpow_half (mul_nonneg hKpos.le hAoonn) (le_of_lt (za_pos n))] at h2
    exact h2
  have hfdL : ∀ n : ℕ, |deriv f (za n)| ≤ |c2| + Real.sqrt (K * Eoo) := by
    intro n
    have h1 : (deriv f (za n) - c2)^2 ≤ K * Eoo := by
      have h2 := hbndgL n
      have h3 := htailEL n
      calc (deriv f (za n) - c2)^2 ≤ K * (za n)^(1 + Work.Spaces.eta)
            * (∫ t in Set.Ioo (0:ℝ) (za n),
                (deriv (deriv f) t)^2 * Work.FTS.EllipticEst.thEta t) := h2
        _ ≤ K * (za n)^(1 + Work.Spaces.eta) * Eoo :=
            mul_le_mul_of_nonneg_left h3 (mul_nonneg hKpos.le
              (Real.rpow_nonneg (le_of_lt (za_pos n)) _))
        _ ≤ K * 1 * Eoo := by
            refine mul_le_mul_of_nonneg_right ?_ hEoonn
            refine mul_le_mul_of_nonneg_left ?_ hKpos.le
            refine le_of_le_of_eq (Real.rpow_le_rpow_of_exponent_ge (za_pos n)
              (by linarith [za_le_half n]) (by have := Work.Spaces.eta_pos; linarith))
              (Real.rpow_zero _)
        _ = K * Eoo := by ring
    have h2 : |deriv f (za n) - c2| ≤ Real.sqrt (K * Eoo) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt h1
    have h3 : |deriv f (za n)| = |(deriv f (za n) - c2) + c2| := by ring_nf
    rw [h3]
    linarith [h2, abs_add_le (deriv f (za n) - c2) c2]
  have hfbR : ∀ n : ℕ, |f (zb n)| ≤ Real.sqrt (K * Aoo) * (Real.pi/2 - zb n)^((1 + Work.Spaces.eta)/2) := by
    intro n
    have h1 : (f (zb n))^2 ≤ K * Aoo * (Real.pi/2 - zb n)^(1 + Work.Spaces.eta) := by
      have h2 := hbndfR n
      have h3 := htailAR n
      calc (f (zb n))^2 ≤ K * (Real.pi/2 - zb n)^(1 + Work.Spaces.eta)
            * (∫ t in Set.Ioo (zb n) (Real.pi/2), (deriv f t)^2 * Work.FTS.EllipticEst.thEta t) := h2
        _ ≤ K * (Real.pi/2 - zb n)^(1 + Work.Spaces.eta) * Aoo :=
            mul_le_mul_of_nonneg_left h3 (mul_nonneg hKpos.le
              (Real.rpow_nonneg (by linarith [zb_lt_pi2 n]) _))
        _ = K * Aoo * (Real.pi/2 - zb n)^(1 + Work.Spaces.eta) := by ring
    have h2 : Real.sqrt ((f (zb n))^2) ≤
        Real.sqrt (K * Aoo * (Real.pi/2 - zb n)^(1 + Work.Spaces.eta)) := Real.sqrt_le_sqrt h1
    rw [Real.sqrt_sq_eq_abs] at h2
    rw [sqrt_mul_rpow_half (mul_nonneg hKpos.le hAoonn) (by linarith [zb_lt_pi2 n])] at h2
    exact h2
  have hfdR : ∀ n : ℕ, |deriv f (zb n)| ≤ |d2| + Real.sqrt (K * Eoo) := by
    intro n
    have h1 : (deriv f (zb n) - d2)^2 ≤ K * Eoo := by
      have h2 := hbndgR n
      have h3 := htailER n
      calc (deriv f (zb n) - d2)^2 ≤ K * (Real.pi/2 - zb n)^(1 + Work.Spaces.eta)
            * (∫ t in Set.Ioo (zb n) (Real.pi/2),
                (deriv (deriv f) t)^2 * Work.FTS.EllipticEst.thEta t) := h2
        _ ≤ K * (Real.pi/2 - zb n)^(1 + Work.Spaces.eta) * Eoo :=
            mul_le_mul_of_nonneg_left h3 (mul_nonneg hKpos.le
              (Real.rpow_nonneg (by linarith [zb_lt_pi2 n]) _))
        _ ≤ K * 1 * Eoo := by
            refine mul_le_mul_of_nonneg_right ?_ hEoonn
            refine mul_le_mul_of_nonneg_left ?_ hKpos.le
            have h4 : Real.pi/2 - zb n ≤ 1 := by rw [hδn n]; linarith [za_le_half n]
            refine le_of_le_of_eq (Real.rpow_le_rpow_of_exponent_ge
              (by linarith [zb_lt_pi2 n]) h4 (by have := Work.Spaces.eta_pos; linarith))
              (Real.rpow_zero _)
        _ = K * Eoo := by ring
    have h2 : |deriv f (zb n) - d2| ≤ Real.sqrt (K * Eoo) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt h1
    have h3 : |deriv f (zb n)| = |(deriv f (zb n) - d2) + d2| := by ring_nf
    rw [h3]
    linarith [h2, abs_add_le (deriv f (zb n) - d2) d2]
  -- the weight bounds
  have hσL : ∀ n : ℕ, Work.FTS.EllipticEst.thEta (za n)
      ≤ (4/Real.pi)^(-(Work.Spaces.eta)) * (za n)^(-(Work.Spaces.eta)) := by
    intro n
    calc Work.FTS.EllipticEst.thEta (za n) ≤ ((4/Real.pi) * (za n))^(-(Work.Spaces.eta)) :=
          thEta_le_left (za_pos n) (le_of_lt (za_lt_pi4 n))
      _ = (4/Real.pi)^(-(Work.Spaces.eta)) * (za n)^(-(Work.Spaces.eta)) :=
          Real.mul_rpow (by positivity : (0:ℝ) ≤ 4/Real.pi) (le_of_lt (za_pos n))
  have hσR : ∀ n : ℕ, Work.FTS.EllipticEst.thEta (zb n)
      ≤ (4/Real.pi)^(-(Work.Spaces.eta)) * (Real.pi/2 - zb n)^(-(Work.Spaces.eta)) := by
    intro n
    calc Work.FTS.EllipticEst.thEta (zb n)
          ≤ ((4/Real.pi) * (Real.pi/2 - zb n))^(-(Work.Spaces.eta)) :=
          thEta_le_right (zb_ge_pi4 n) (zb_lt_pi2 n)
      _ = (4/Real.pi)^(-(Work.Spaces.eta)) * (Real.pi/2 - zb n)^(-(Work.Spaces.eta)) :=
          Real.mul_rpow (by positivity : (0:ℝ) ≤ 4/Real.pi) (by linarith [zb_lt_pi2 n])
  have hcsL : ∀ n : ℕ, cs1 (za n)
      ≤ (4/Real.pi)^(-(1 + Work.Spaces.eta)) * (za n)^(-(1 + Work.Spaces.eta)) := by
    intro n
    calc cs1 (za n) ≤ ((4/Real.pi) * (za n))^(-(1 + Work.Spaces.eta)) :=
          cs1_le_left (za_pos n) (le_of_lt (za_lt_pi4 n))
      _ = (4/Real.pi)^(-(1 + Work.Spaces.eta)) * (za n)^(-(1 + Work.Spaces.eta)) :=
          Real.mul_rpow (by positivity : (0:ℝ) ≤ 4/Real.pi) (le_of_lt (za_pos n))
  have hcsR : ∀ n : ℕ, |cs1 (zb n)|
      ≤ (4/Real.pi)^(-(1 + Work.Spaces.eta)) * (Real.pi/2 - zb n)^(-(1 + Work.Spaces.eta)) := by
    intro n
    have hδ0 : 0 < Real.pi/2 - zb n := by linarith [zb_lt_pi2 n]
    have hδ1 : Real.pi/2 - zb n ≤ Real.pi/4 := by rw [hδn n]; exact le_of_lt (za_lt_pi4 n)
    have hneg : cs1 (zb n) = - cs1 (Real.pi/2 - zb n) := by
      rw [cs1, cs1]
      have hsin : Real.sin (2*zb n) = Real.sin (2*(Real.pi/2 - zb n)) := by
        rw [show 2*zb n = Real.pi - 2*(Real.pi/2 - zb n) by ring, Real.sin_pi_sub]
      have hcos : Real.cos (2*zb n) = -Real.cos (2*(Real.pi/2 - zb n)) := by
        rw [show 2*zb n = Real.pi - 2*(Real.pi/2 - zb n) by ring, Real.cos_pi_sub]
      rw [hsin, hcos]; ring
    rw [hneg, abs_neg, abs_of_nonneg (cs1_nonneg_left hδ0 hδ1)]
    calc cs1 (Real.pi/2 - zb n) ≤ ((4/Real.pi) * (Real.pi/2 - zb n))^(-(1 + Work.Spaces.eta)) :=
          cs1_le_left hδ0 hδ1
      _ = (4/Real.pi)^(-(1 + Work.Spaces.eta))
            * (Real.pi/2 - zb n)^(-(1 + Work.Spaces.eta)) :=
          Real.mul_rpow (by positivity : (0:ℝ) ≤ 4/Real.pi) (le_of_lt hδ0)
  -- the majorant constants
  set Mx : ℝ := (|c2| + Real.sqrt (K * Eoo)) * Real.sqrt (K * Aoo)
    * (4/Real.pi)^(-(Work.Spaces.eta)) with hMx
  set Md : ℝ := (|d2| + Real.sqrt (K * Eoo)) * Real.sqrt (K * Aoo)
    * (4/Real.pi)^(-(Work.Spaces.eta)) with hMd
  set Mq : ℝ := K * (4/Real.pi)^(-(1 + Work.Spaces.eta)) with hMq
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (f := fun n : ℕ => ‖f (za n) * deriv f (za n)
        * Work.FTS.EllipticEst.thEta (za n)‖)
      (g := fun n : ℕ => Mx * (za n)^((1 - Work.Spaces.eta)/2))
      (Eventually.of_forall fun n => norm_nonneg _) ?_ ?_
    · refine Eventually.of_forall fun n => ?_
      rw [Real.norm_eq_abs]
      have hσnn : 0 ≤ Work.FTS.EllipticEst.thEta (za n) :=
        le_of_lt (thEta_pos_of_mem (za_mem n))
      calc |f (za n) * deriv f (za n) * Work.FTS.EllipticEst.thEta (za n)|
          = |f (za n)| * |deriv f (za n)| * Work.FTS.EllipticEst.thEta (za n) := by
            rw [abs_mul, abs_mul, abs_of_nonneg hσnn]
        _ ≤ (Real.sqrt (K * Aoo) * (za n)^((1 + Work.Spaces.eta)/2))
              * (|c2| + Real.sqrt (K * Eoo))
              * ((4/Real.pi)^(-(Work.Spaces.eta)) * (za n)^(-(Work.Spaces.eta))) := by
            refine mul_le_mul (mul_le_mul (hfbL n) (hfdL n) (abs_nonneg _)
              (mul_nonneg (Real.sqrt_nonneg (K * Aoo))
                (Real.rpow_nonneg (le_of_lt (za_pos n)) _)))
              (hσL n) hσnn ?_
            exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg (K * Aoo))
              (Real.rpow_nonneg (le_of_lt (za_pos n)) _))
              (add_nonneg (abs_nonneg _) (Real.sqrt_nonneg (K * Eoo)))
        _ = Mx * ((za n)^((1 + Work.Spaces.eta)/2) * (za n)^(-(Work.Spaces.eta))) := by
            rw [hMx]; ring
        _ = Mx * (za n)^((1 - Work.Spaces.eta)/2) := by
            rw [← Real.rpow_add (za_pos n)]
            congr 1
            ring
    · have hpow := tendsto_rpow_za (a := (1 - Work.Spaces.eta)/2)
        (by linarith [Work.Spaces.eta_lt_one])
      simpa using hpow.const_mul Mx
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (f := fun n : ℕ => ‖(f (za n))^2 * cs1 (za n)‖)
      (g := fun n : ℕ => Mq * (∫ t in Set.Ioo (0:ℝ) (za n),
        (deriv f t)^2 * Work.FTS.EllipticEst.thEta t))
      (Eventually.of_forall fun n => norm_nonneg _) ?_ ?_
    · refine Eventually.of_forall fun n => ?_
      rw [Real.norm_eq_abs]
      have hcs1nn : 0 ≤ cs1 (za n) := cs1_nonneg_left (za_pos n) (le_of_lt (za_lt_pi4 n))
      have htailnn : 0 ≤ ∫ t in Set.Ioo (0:ℝ) (za n),
          (deriv f t)^2 * Work.FTS.EllipticEst.thEta t :=
        MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun t ht => mul_nonneg (sq_nonneg _)
          (le_of_lt (thEta_pos_of_mem ⟨ht.1, lt_of_lt_of_le ht.2 (le_of_lt (za_mem n).2)⟩)))
      rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hcs1nn)]
      have h6 : (za n)^(1 + Work.Spaces.eta) * (za n)^(-(1 + Work.Spaces.eta)) = 1 := by
        rw [← Real.rpow_add (za_pos n),
          show (1 + Work.Spaces.eta) + (-(1 + Work.Spaces.eta)) = 0 by ring, Real.rpow_zero]
      calc (f (za n))^2 * cs1 (za n)
          ≤ (K * (za n)^(1 + Work.Spaces.eta)
              * (∫ t in Set.Ioo (0:ℝ) (za n), (deriv f t)^2 * Work.FTS.EllipticEst.thEta t))
              * ((4/Real.pi)^(-(1 + Work.Spaces.eta)) * (za n)^(-(1 + Work.Spaces.eta))) := by
            refine mul_le_mul (hbndfL n) (hcsL n) hcs1nn ?_
            exact mul_nonneg (mul_nonneg hKpos.le
              (Real.rpow_nonneg (le_of_lt (za_pos n)) _)) htailnn
        _ = Mq * ((∫ t in Set.Ioo (0:ℝ) (za n),
              (deriv f t)^2 * Work.FTS.EllipticEst.thEta t)
              * ((za n)^(1 + Work.Spaces.eta) * (za n)^(-(1 + Work.Spaces.eta)))) := by
            rw [hMq]; ring
        _ = Mq * (∫ t in Set.Ioo (0:ℝ) (za n),
              (deriv f t)^2 * Work.FTS.EllipticEst.thEta t) := by
            rw [h6]; ring
    · have htailA := tail_left (fun t : ℝ => (deriv f t)^2 * Work.FTS.EllipticEst.thEta t) hA
      simpa using htailA.const_mul Mq
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (f := fun n : ℕ => ‖f (zb n) * deriv f (zb n)
        * Work.FTS.EllipticEst.thEta (zb n)‖)
      (g := fun n : ℕ => Md * (Real.pi/2 - zb n)^((1 - Work.Spaces.eta)/2))
      (Eventually.of_forall fun n => norm_nonneg _) ?_ ?_
    · refine Eventually.of_forall fun n => ?_
      rw [Real.norm_eq_abs]
      have hσnn : 0 ≤ Work.FTS.EllipticEst.thEta (zb n) :=
        le_of_lt (thEta_pos_of_mem (zb_mem n))
      calc |f (zb n) * deriv f (zb n) * Work.FTS.EllipticEst.thEta (zb n)|
          = |f (zb n)| * |deriv f (zb n)| * Work.FTS.EllipticEst.thEta (zb n) := by
            rw [abs_mul, abs_mul, abs_of_nonneg hσnn]
        _ ≤ (Real.sqrt (K * Aoo) * (Real.pi/2 - zb n)^((1 + Work.Spaces.eta)/2))
              * (|d2| + Real.sqrt (K * Eoo))
              * ((4/Real.pi)^(-(Work.Spaces.eta)) * (Real.pi/2 - zb n)^(-(Work.Spaces.eta))) := by
            refine mul_le_mul (mul_le_mul (hfbR n) (hfdR n) (abs_nonneg _)
              (mul_nonneg (Real.sqrt_nonneg (K * Aoo))
                (Real.rpow_nonneg (by linarith [zb_lt_pi2 n]) _)))
              (hσR n) hσnn ?_
            exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg (K * Aoo))
              (Real.rpow_nonneg (by linarith [zb_lt_pi2 n]) _))
              (add_nonneg (abs_nonneg _) (Real.sqrt_nonneg (K * Eoo)))
        _ = Md * ((Real.pi/2 - zb n)^((1 + Work.Spaces.eta)/2)
              * (Real.pi/2 - zb n)^(-(Work.Spaces.eta))) := by
            rw [hMd]; ring
        _ = Md * (Real.pi/2 - zb n)^((1 - Work.Spaces.eta)/2) := by
            rw [← Real.rpow_add (by linarith [zb_lt_pi2 n])]
            congr 1
            ring
    · have hpow : Tendsto (fun n : ℕ => (Real.pi/2 - zb n)^((1 - Work.Spaces.eta)/2))
          atTop (nhds 0) := by
        refine (tendsto_rpow_za (a := (1 - Work.Spaces.eta)/2)
          (by linarith [Work.Spaces.eta_lt_one])).congr' ?_
        filter_upwards with n
        rw [hδn n]
      simpa using hpow.const_mul Md
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (f := fun n : ℕ => ‖(f (zb n))^2 * cs1 (zb n)‖)
      (g := fun n : ℕ => Mq * (∫ t in Set.Ioo (zb n) (Real.pi/2),
        (deriv f t)^2 * Work.FTS.EllipticEst.thEta t))
      (Eventually.of_forall fun n => norm_nonneg _) ?_ ?_
    · refine Eventually.of_forall fun n => ?_
      rw [Real.norm_eq_abs]
      have htailnn : 0 ≤ ∫ t in Set.Ioo (zb n) (Real.pi/2),
          (deriv f t)^2 * Work.FTS.EllipticEst.thEta t :=
        MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun t ht => mul_nonneg (sq_nonneg _)
          (le_of_lt (thEta_pos_of_mem ⟨lt_trans (zb_mem n).1 ht.1, ht.2⟩)))
      have h6 : (Real.pi/2 - zb n)^(1 + Work.Spaces.eta)
          * (Real.pi/2 - zb n)^(-(1 + Work.Spaces.eta)) = 1 := by
        rw [← Real.rpow_add (by linarith [zb_lt_pi2 n]),
          show (1 + Work.Spaces.eta) + (-(1 + Work.Spaces.eta)) = 0 by ring, Real.rpow_zero]
      calc |(f (zb n))^2 * cs1 (zb n)|
          = (f (zb n))^2 * |cs1 (zb n)| := by
            rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
        _ ≤ (K * (Real.pi/2 - zb n)^(1 + Work.Spaces.eta)
              * (∫ t in Set.Ioo (zb n) (Real.pi/2), (deriv f t)^2 * Work.FTS.EllipticEst.thEta t))
              * ((4/Real.pi)^(-(1 + Work.Spaces.eta))
                * (Real.pi/2 - zb n)^(-(1 + Work.Spaces.eta))) := by
            refine mul_le_mul (hbndfR n) (hcsR n) (abs_nonneg _) ?_
            exact mul_nonneg (mul_nonneg hKpos.le
              (Real.rpow_nonneg (by linarith [zb_lt_pi2 n]) _)) htailnn
        _ = Mq * ((∫ t in Set.Ioo (zb n) (Real.pi/2),
              (deriv f t)^2 * Work.FTS.EllipticEst.thEta t)
              * ((Real.pi/2 - zb n)^(1 + Work.Spaces.eta)
                  * (Real.pi/2 - zb n)^(-(1 + Work.Spaces.eta)))) := by
            rw [hMq]; ring
        _ = Mq * (∫ t in Set.Ioo (zb n) (Real.pi/2),
              (deriv f t)^2 * Work.FTS.EllipticEst.thEta t) := by
            rw [h6]; ring
    · have htailA := tail_right (fun t : ℝ => (deriv f t)^2 * Work.FTS.EllipticEst.thEta t) hA
      simpa using htailA.const_mul Mq


/-- Two a.e.-equal forms of the angular interval. -/
private theorem Icc_ae_eq_Ioo_aux (a b : ℝ) : Set.Icc a b =ᵐ[MeasureTheory.volume] Set.Ioo a b := by
  have hpair : MeasureTheory.volume ({a, b} : Set ℝ) = 0 :=
    Set.Finite.measure_zero (by simp) MeasureTheory.volume
  have hpairab : ∀ᵐ x : ℝ, x ∉ ({a, b} : Set ℝ) := by
    rw [MeasureTheory.ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hpair
  filter_upwards [hpairab] with x hx
  refine propext ⟨?_, ?_⟩
  · intro h
    rw [Set.mem_Icc] at h
    rw [Set.mem_Ioo]
    exact ⟨lt_of_le_of_ne h.1 (fun hc => hx (Or.inl hc.symm)),
      lt_of_le_of_ne h.2 (fun hc => hx (Or.inr hc))⟩
  · intro h
    rw [Set.mem_Ioo] at h
    rw [Set.mem_Icc]
    exact ⟨le_of_lt h.1, le_of_lt h.2⟩

/-- Integrability transfers from the closed to the open angular interval. -/
private theorem integrableOn_Ioo_of_Iθ {g : ℝ → ℝ} (hg : IntegrableOn g Work.Spaces.Iθ) :
    IntegrableOn g (Set.Ioo (0:ℝ) (Real.pi/2)) := by
  rw [MeasureTheory.IntegrableOn] at hg ⊢
  exact MeasureTheory.Measure.restrict_congr_set (Icc_ae_eq_Ioo_aux 0 (Real.pi/2)) ▸ hg

theorem traceVanishingInterp : ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ,
    ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
    Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
    Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      ≤ C * ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          + Real.sqrt ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
              * (∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))) := by
  refine ⟨199, by norm_num, ?_⟩
  intro f hf h0 h1 hPint hAint hEint
  have hAintoo := integrableOn_Ioo_of_Iθ hAint
  have hEintoo := integrableOn_Ioo_of_Iθ hEint
  set P : ℝ := ∫ θ in Work.Spaces.Iθ, (f θ)^2 * Work.FTS.EllipticEst.thEta θ with hPdef
  set A : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ with hAdef
  set E : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ)^2 * Work.FTS.EllipticEst.thEta θ with hEdef
  have hIθmeas : MeasurableSet Work.Spaces.Iθ := by
    rw [show Work.Spaces.Iθ = Set.Icc (0:ℝ) (Real.pi/2) from rfl]
    exact measurableSet_Icc
  have hPnn : 0 ≤ P := by
    rw [hPdef]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => mul_nonneg (sq_nonneg _)
      (Work.FTS.EllipticEst.thEta_nonneg hθ))
  have hEnn : 0 ≤ E := by
    rw [hEdef]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => mul_nonneg (sq_nonneg _)
      (Work.FTS.EllipticEst.thEta_nonneg hθ))
  obtain ⟨hb1, hb2, hb3, hb4⟩ := traceBoundarySeq hf h0 h1 hAintoo hEintoo
  -- ## Cauchy–Schwarz on the full interval
  have hCS : ∀ n : ℕ, |∫ θ in (za n)..(zb n),
      f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ| ≤ Real.sqrt (P * E) := by
    intro n
    have ha := za_pos n
    have hb := zb_lt_pi2 n
    have hab := le_of_lt (za_lt_zb n)
    obtain ⟨hIA, hIB, hIC, hID, hIJ, hIE⟩ := intervalIntegrable_pieces hf ha hb hab
    have hmem : ∀ x ∈ Set.uIcc (za n) (zb n), x ∈ Set.Ioo (0:ℝ) (Real.pi/2) := by
      intro x hx
      rw [Set.uIcc_of_le hab] at hx
      exact ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩
    have hCcont : ContinuousOn (fun θ : ℝ => f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ)
        (Set.uIcc (za n) (zb n)) := by
      have hIoo : IsOpen (Set.Ioo (0:ℝ) (Real.pi/2)) := isOpen_Ioo
      have hcf : ContinuousOn f (Set.uIcc (za n) (zb n)) := hf.continuousOn.mono hmem
      have hcf'' : ContinuousOn (deriv (deriv f)) (Set.uIcc (za n) (zb n)) := by
        have h1 : ContDiffOn ℝ 1 (deriv f) (Set.Ioo (0:ℝ) (Real.pi/2)) :=
          hf.deriv_of_isOpen hIoo (by norm_num)
        exact (contDiffOn_zero.1 (h1.deriv_of_isOpen hIoo (by norm_num))).mono hmem
      have hsinC : ContinuousOn (fun θ : ℝ => Real.sin (2*θ)) (Set.uIcc (za n) (zb n)) :=
        (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
      have hσC : ContinuousOn Work.FTS.EllipticEst.thEta (Set.uIcc (za n) (zb n)) :=
        hsinC.rpow_const (fun θ hθ => Or.inl (sin_two_pos_of_mem (hmem θ hθ)).ne')
      exact (hcf.mul hcf'').mul hσC
    have hCs : IntegrableOn (fun θ : ℝ => f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ)
        (Set.Ioc (za n) (zb n)) := hCcont.intervalIntegrable.1
    have hcs := Work.FTS.EllipticEst.AngSecond.abs_setIntegral_le_sqrt_mul_sqrt
      (s := Set.Ioc (za n) (zb n))
      (A := fun θ : ℝ => (f θ)^2 * Work.FTS.EllipticEst.thEta θ)
      (B := fun θ : ℝ => (deriv (deriv f) θ)^2 * Work.FTS.EllipticEst.thEta θ)
      (C := fun θ : ℝ => f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ)
      hIC.1 hIE.1 hCs
      (fun z hz => mul_nonneg (sq_nonneg _) (le_of_lt (thEta_pos_of_mem
        ⟨lt_trans ha hz.1, lt_of_le_of_lt hz.2 hb⟩)))
      (fun z hz => mul_nonneg (sq_nonneg _) (le_of_lt (thEta_pos_of_mem
        ⟨lt_trans ha hz.1, lt_of_le_of_lt hz.2 hb⟩)))
      (fun z hz => by
        have hz' : z ∈ Set.Ioo (0:ℝ) (Real.pi/2) :=
          ⟨lt_trans ha hz.1, lt_of_le_of_lt hz.2 hb⟩
        have hσnn : 0 ≤ Work.FTS.EllipticEst.thEta z := le_of_lt (thEta_pos_of_mem hz')
        have hsq : Real.sqrt (Work.FTS.EllipticEst.thEta z)
            * Real.sqrt (Work.FTS.EllipticEst.thEta z) = Work.FTS.EllipticEst.thEta z := by
          rw [show Real.sqrt (Work.FTS.EllipticEst.thEta z)
                * Real.sqrt (Work.FTS.EllipticEst.thEta z)
              = (Real.sqrt (Work.FTS.EllipticEst.thEta z))^2 by rw [pow_two],
            Real.sq_sqrt hσnn]
        rw [abs_mul, abs_mul, abs_of_nonneg hσnn,
          Real.sqrt_mul (sq_nonneg (f z)), Real.sqrt_mul (sq_nonneg (deriv (deriv f) z)),
          Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs,
          show (|f z| * Real.sqrt (Work.FTS.EllipticEst.thEta z))
                * (|deriv (deriv f) z| * Real.sqrt (Work.FTS.EllipticEst.thEta z))
              = |f z| * |deriv (deriv f) z|
                * (Real.sqrt (Work.FTS.EllipticEst.thEta z)
                    * Real.sqrt (Work.FTS.EllipticEst.thEta z))
              by ring,
          hsq])
    have hAle : (∫ z in Set.Ioc (za n) (zb n), (f z)^2 * Work.FTS.EllipticEst.thEta z) ≤ P := by
      rw [hPdef]
      refine MeasureTheory.setIntegral_mono_set hPint ?_ ?_
      · filter_upwards [MeasureTheory.ae_restrict_mem hIθmeas] with z hz
        exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hz)
      · filter_upwards with z hz
        exact ⟨le_of_lt (lt_trans ha hz.1), le_of_lt (lt_of_le_of_lt hz.2 hb)⟩
    have hEle : (∫ z in Set.Ioc (za n) (zb n),
        (deriv (deriv f) z)^2 * Work.FTS.EllipticEst.thEta z) ≤ E := by
      rw [hEdef]
      refine MeasureTheory.setIntegral_mono_set hEint ?_ ?_
      · filter_upwards [MeasureTheory.ae_restrict_mem hIθmeas] with z hz
        exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hz)
      · filter_upwards with z hz
        exact ⟨le_of_lt (lt_trans ha hz.1), le_of_lt (lt_of_le_of_lt hz.2 hb)⟩
    have hsqrt : Real.sqrt (∫ z in Set.Ioc (za n) (zb n), (f z)^2 * Work.FTS.EllipticEst.thEta z)
        * Real.sqrt (∫ z in Set.Ioc (za n) (zb n),
            (deriv (deriv f) z)^2 * Work.FTS.EllipticEst.thEta z)
        ≤ Real.sqrt P * Real.sqrt E :=
      mul_le_mul (Real.sqrt_le_sqrt hAle) (Real.sqrt_le_sqrt hEle)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    calc |∫ θ in (za n)..(zb n), f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ|
        = |∫ z in Set.Ioc (za n) (zb n),
            f z * deriv (deriv f) z * Work.FTS.EllipticEst.thEta z| := by
          rw [intervalIntegral.integral_of_le hab]
      _ ≤ Real.sqrt (∫ z in Set.Ioc (za n) (zb n), (f z)^2 * Work.FTS.EllipticEst.thEta z)
            * Real.sqrt (∫ z in Set.Ioc (za n) (zb n),
                (deriv (deriv f) z)^2 * Work.FTS.EllipticEst.thEta z) := hcs
      _ ≤ Real.sqrt P * Real.sqrt E := hsqrt
      _ = Real.sqrt (P * E) := (Real.sqrt_mul hPnn E).symm
  -- ## the key estimate on each truncated interval
  set Hf : ℕ → ℝ := fun n => (f (zb n) * deriv f (zb n) * Work.FTS.EllipticEst.thEta (zb n)
        - Work.Spaces.eta * (f (zb n))^2 * cs1 (zb n))
      - (f (za n) * deriv f (za n) * Work.FTS.EllipticEst.thEta (za n)
        - Work.Spaces.eta * (f (za n))^2 * cs1 (za n)) with hHf
  have hkey : ∀ n : ℕ, (∫ θ in (za n)..(zb n), (deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ)
      ≤ 199 * (Hf n + Real.sqrt (P * E)) := by
    intro n
    have ha := za_pos n
    have hb := zb_lt_pi2 n
    have hab := le_of_lt (za_lt_zb n)
    have hmem : ∀ x ∈ Set.uIcc (za n) (zb n), x ∈ Set.Ioo (0:ℝ) (Real.pi/2) := by
      intro x hx
      rw [Set.uIcc_of_le hab] at hx
      exact ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩
    obtain ⟨hIA, hIB, hIC, hID, hIJ, hIE⟩ := intervalIntegrable_pieces hf ha hb hab
    set An : ℝ := ∫ θ in (za n)..(zb n), (deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ with hAn
    set Bn : ℝ := ∫ θ in (za n)..(zb n),
      f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ with hBn
    set Cn : ℝ := ∫ θ in (za n)..(zb n), (f θ)^2 * Work.FTS.EllipticEst.thEta θ with hCn
    set Dn : ℝ := ∫ θ in (za n)..(zb n), (f θ)^2 * csq θ with hDn
    set Jn : ℝ := ∫ θ in (za n)..(zb n), f θ * deriv f θ * cs1 θ with hJn
    have hI2J : IntervalIntegrable (fun θ : ℝ => (2*(1 + Work.Spaces.eta))
        * (f θ * deriv f θ * cs1 θ)) volume (za n) (zb n) := hIJ.const_mul _
    have hI2D : IntervalIntegrable (fun θ : ℝ => (1 + Work.Spaces.eta)^2 * ((f θ)^2 * csq θ))
        volume (za n) (zb n) := hID.const_mul _
    have hsub1 : IntervalIntegrable (fun θ : ℝ => (deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ
        - (2*(1 + Work.Spaces.eta)) * (f θ * deriv f θ * cs1 θ)) volume (za n) (zb n) :=
      hIA.sub hI2J
    have hS1 : An = (f (zb n) * deriv f (zb n) * Work.FTS.EllipticEst.thEta (zb n)
            + Work.Spaces.eta * (f (zb n))^2 * cs1 (zb n))
        - (f (za n) * deriv f (za n) * Work.FTS.EllipticEst.thEta (za n)
            + Work.Spaces.eta * (f (za n))^2 * cs1 (za n))
        - Bn + 2 * Work.Spaces.eta * Cn
        + 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * Dn := by
      rw [hAn, hBn, hCn, hDn]
      exact ibp_main hf ha hb hab
    have hS2 : Jn = Cn + (1 + Work.Spaces.eta) * Dn
        + (1/2) * ((f (zb n))^2 * cs1 (zb n) - (f (za n))^2 * cs1 (za n)) := by
      rw [hJn, hCn, hDn]
      exact ibp_cot hf ha hb hab
    have hQnn : 0 ≤ An - 2*(1 + Work.Spaces.eta)*Jn + (1 + Work.Spaces.eta)^2*Dn := by
      have hcongr : (∫ θ in (za n)..(zb n), (deriv f θ - (1 + Work.Spaces.eta) * f θ
            * (Real.cos (2*θ)/Real.sin (2*θ)))^2 * Work.FTS.EllipticEst.thEta θ)
          = ∫ θ in (za n)..(zb n), ((deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ
              - 2*(1 + Work.Spaces.eta) * (f θ * deriv f θ * cs1 θ)
              + (1 + Work.Spaces.eta)^2 * ((f θ)^2 * csq θ)) :=
        intervalIntegral.integral_congr
          (fun θ hθ => sq_expand_pointwise (sin_two_pos_of_mem (hmem θ hθ)))
      have hnonneg : 0 ≤ ∫ θ in (za n)..(zb n), (deriv f θ - (1 + Work.Spaces.eta) * f θ
          * (Real.cos (2*θ)/Real.sin (2*θ)))^2 * Work.FTS.EllipticEst.thEta θ := by
        rw [intervalIntegral.integral_of_le hab]
        exact MeasureTheory.setIntegral_nonneg measurableSet_Ioc (fun θ hθ => mul_nonneg (sq_nonneg _)
          (le_of_lt (thEta_pos_of_mem ⟨lt_trans ha hθ.1, lt_of_le_of_lt hθ.2 hb⟩)))
      have hlin : (∫ θ in (za n)..(zb n), ((deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ
              - 2*(1 + Work.Spaces.eta) * (f θ * deriv f θ * cs1 θ)
              + (1 + Work.Spaces.eta)^2 * ((f θ)^2 * csq θ)))
          = An - 2*(1 + Work.Spaces.eta)*Jn + (1 + Work.Spaces.eta)^2*Dn := by
        rw [hAn, hJn, hDn]
        rw [intervalIntegral.integral_add hsub1 hI2D, intervalIntegral.integral_sub hIA hI2J,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      linarith [hcongr, hnonneg, hlin]
    have hDle : (1 + Work.Spaces.eta)^2 * Dn ≤ An - 2*(1 + Work.Spaces.eta)*Cn
        - (1 + Work.Spaces.eta) * ((f (zb n))^2 * cs1 (zb n) - (f (za n))^2 * cs1 (za n)) := by
      have h1 : 2*(1 + Work.Spaces.eta)*Jn = 2*(1 + Work.Spaces.eta)*Cn
          + 2*(1 + Work.Spaces.eta)^2*Dn
          + (1 + Work.Spaces.eta)*((f (zb n))^2 * cs1 (zb n) - (f (za n))^2 * cs1 (za n)) := by
        rw [hS2]; ring
      nlinarith [hQnn, h1]
    have hCn0 : 0 ≤ Cn := by
      rw [hCn, intervalIntegral.integral_of_le hab]
      exact MeasureTheory.setIntegral_nonneg measurableSet_Ioc (fun θ hθ => mul_nonneg (sq_nonneg _)
        (le_of_lt (thEta_pos_of_mem ⟨lt_trans ha hθ.1, lt_of_le_of_lt hθ.2 hb⟩)))
    have hstep : An * (1 - Work.Spaces.eta) ≤ (1 + Work.Spaces.eta) * (Hf n + |Bn|) := by
      rw [hHf]
      have heta : Work.Spaces.eta = 99/100 := rfl
      rw [heta] at hS1 hDle ⊢
      nlinarith [hS1, hDle, hCn0, neg_le_abs Bn]
    have hstep2 : An ≤ 199 * (Hf n + Real.sqrt (P * E)) := by
      have hbn : |Bn| ≤ Real.sqrt (P * E) := hCS n
      have hXn : Hf n + |Bn| ≤ Hf n + Real.sqrt (P * E) := by linarith [hbn]
      have h2 : (1 + Work.Spaces.eta) * (Hf n + |Bn|)
          ≤ (1 + Work.Spaces.eta) * (Hf n + Real.sqrt (P * E)) :=
        mul_le_mul_of_nonneg_left hXn (by have := Work.Spaces.eta_pos; linarith)
      rw [hHf] at hstep h2 ⊢
      have heta : Work.Spaces.eta = 99/100 := rfl
      rw [heta] at hstep h2 ⊢
      nlinarith [hstep, h2]
    exact hstep2
  -- ## the limit
  have hlimH : Tendsto (fun n : ℕ => 199 * (Hf n + Real.sqrt (P * E))) atTop
      (nhds (199 * Real.sqrt (P * E))) := by
    have hL : Tendsto (fun n : ℕ => f (za n) * deriv f (za n) * Work.FTS.EllipticEst.thEta (za n)
        - Work.Spaces.eta * (f (za n))^2 * cs1 (za n)) atTop (nhds 0) := by
      have h := hb1.sub (hb2.const_mul Work.Spaces.eta)
      simpa using (h.congr' (Eventually.of_forall fun n => by ring))
    have hR : Tendsto (fun n : ℕ => f (zb n) * deriv f (zb n) * Work.FTS.EllipticEst.thEta (zb n)
        - Work.Spaces.eta * (f (zb n))^2 * cs1 (zb n)) atTop (nhds 0) := by
      have h := hb3.sub (hb4.const_mul Work.Spaces.eta)
      simpa using (h.congr' (Eventually.of_forall fun n => by ring))
    have h3 : Tendsto (fun n : ℕ => Hf n + Real.sqrt (P * E)) atTop
        (nhds (0 + Real.sqrt (P * E))) := by
      rw [hHf]
      have h4 := (hR.sub hL).add (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => Real.sqrt (P * E)) atTop (nhds (Real.sqrt (P * E))))
      simpa using h4
    simpa using h3.const_mul 199
  have hlimA : Tendsto (fun n : ℕ => ∫ θ in (za n)..(zb n),
      (deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ) atTop (nhds A) := by
    have h0 : Tendsto (fun n : ℕ => ∫ θ in (za n)..(zb n),
        (deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ) atTop
        (nhds (∫ θ in Work.Spaces.Iθ, (deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ)) :=
      expandingIntegral (fun θ : ℝ => (deriv f θ)^2 * Work.FTS.EllipticEst.thEta θ) hAint
        (fun θ hθ => mul_nonneg (sq_nonneg (deriv f θ)) (Work.FTS.EllipticEst.thEta_nonneg hθ))
    exact h0
  have hlim : A ≤ 199 * Real.sqrt (P * E) :=
    le_of_tendsto_of_tendsto' hlimA hlimH hkey
  have hgoal : A ≤ 199 * (P + Real.sqrt (P * E)) := by
    have h2 : Real.sqrt (P * E) ≤ P + Real.sqrt (P * E) := le_add_of_nonneg_left hPnn
    nlinarith [hlim, h2]
  rw [hAdef, hPdef, hEdef] at hgoal
  exact hgoal

end

end Work.EllipticEst.Core.i0Aux
