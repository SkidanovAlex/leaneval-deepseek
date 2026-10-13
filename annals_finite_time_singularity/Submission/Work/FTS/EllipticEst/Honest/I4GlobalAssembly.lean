import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.Honest.SliceHyp
import Submission.Work.FTS.EllipticEst.Honest.hksq_eq_w2_sliceIntegral
import Submission.Work.FTS.EllipticEst.AngSecond.abs_setIntegral_le_sqrt_mul_sqrt
import Submission.Work.FTS.EllipticEst.AngSecond.slice_sq_integral_mul_le
import Submission.Work.FTS.EllipticEst.AngSecond.setIntegral_w_mul_sqrt_le
import Submission.Work.FTS.EllipticEst.integral_le_integral_of_ae_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option maxHeartbeats 1600000

/-! ## The two auxiliary steps of the assembly -/

theorem I4IntegrableOnOfConstMul {f : ℝ → ℝ} {s : Set ℝ} {c : ℝ}
    (h : MeasureTheory.IntegrableOn (fun θ => c * f θ) s) (hc : c ≠ 0)
    (hs : MeasurableSet s) :
    MeasureTheory.IntegrableOn f s := by
  have h2 := h.mul_const c⁻¹
  refine MeasureTheory.IntegrableOn.congr_fun h2 (fun θ hθ => ?_) hs
  show (c * f θ) * c⁻¹ = f θ
  calc (c * f θ) * c⁻¹ = f θ * (c * c⁻¹) := by ring
    _ = f θ * 1 := by rw [mul_inv_cancel₀ hc]
    _ = f θ := by ring

theorem I4SliceStep (hS : SliceIneq) {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Hon α F Ψ)
    (hQ : Work.Spaces.HkMem α 0 (fun z θ => Ψ z θ / Real.cos θ))
    {z : ℝ} (hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ
          * Work.Spaces.pthIter 2 Ψ z θ * Work.FTS.EllipticEst.AngSecond.sig θ)
      ≤ 50 * (∫ θ in Work.Spaces.Iθ,
            (Ψ z θ / Real.cos θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
        + Real.sqrt (∫ θ in Work.Spaces.Iθ,
              (Ψ z θ / Real.cos θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) := by
  -- (1) the slice is `C²` on the open interval
  have hsm : ContDiffOn ℝ 2 (fun θ : ℝ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) := by
    have h2 := h.sm 2
    have hg : ContDiffOn ℝ 2 (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2)) := by
      fun_prop
    have hcomp := h2.comp hg (fun θ hθ => ⟨hz, hθ⟩)
    simpa [Function.comp_def] using hcomp
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hw2ne : AngSecond.w2 z ≠ 0 := by
    have hwpos := AngSecond.w_pos hz
    simp only [AngSecond.w2]
    positivity
  -- (2) integrability of the two weighted squares, from `HkMem α 0 (Ψ/cos)` and `Hon.memB`
  have hptQ : Set.EqOn
      (fun θ => Work.Spaces.HkIntegrand α 0 (fun z θ => Ψ z θ / Real.cos θ) z θ)
      (fun θ => AngSecond.w2 z * ((Ψ z θ / Real.cos θ) ^ 2 * AngSecond.sig θ))
      Work.Spaces.Iθ := by
    intro θ hθ
    beta_reduce
    rw [HkIntegrand_zero_eq,
      sq_profile_eq (fun z θ => Ψ z θ / Real.cos θ) z θ (sin_two_nonneg_of_mem_Iθ hθ),
      AngSecond.w2, AngSecond.sig]
    ring
  have hQz : MeasureTheory.IntegrableOn
      (fun θ => (Ψ z θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
      (Set.Icc 0 (Real.pi / 2)) := by
    have h0 := MeasureTheory.IntegrableOn.congr_fun (hQ.1 z hzI) hptQ measurableSet_Icc
    have h1 := I4IntegrableOnOfConstMul h0 hw2ne measurableSet_Icc
    refine MeasureTheory.IntegrableOn.congr_fun h1 (fun θ hθ => ?_) measurableSet_Icc
    show (Ψ z θ / Real.cos θ) ^ 2 * AngSecond.sig θ
      = (Ψ z θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))
    rfl
  have hptB : Set.EqOn
      (fun θ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ)
      (fun θ => AngSecond.w2 z * ((Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * AngSecond.sig θ))
      Work.Spaces.Iθ := by
    intro θ hθ
    beta_reduce
    rw [HkIntegrand_zero_eq,
      sq_profile_eq (Work.Spaces.pthIter 2 Ψ) z θ (sin_two_nonneg_of_mem_Iθ hθ),
      AngSecond.w2, AngSecond.sig]
    ring
  have hBz : MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv (fun θ' => Ψ z θ')) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))) (Set.Icc 0 (Real.pi / 2)) := by
    have h0 := MeasureTheory.IntegrableOn.congr_fun (h.memB.1 z hzI) hptB measurableSet_Icc
    have h1 := I4IntegrableOnOfConstMul h0 hw2ne measurableSet_Icc
    refine MeasureTheory.IntegrableOn.congr_fun h1 (fun θ hθ => ?_) measurableSet_Icc
    show (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * AngSecond.sig θ
      = (deriv (deriv (fun θ' => Ψ z θ')) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))
    rw [AngSecond.sig]
    rfl
  -- (3) instantiate the assumed slice inequality
  have hsl := hS (fun θ : ℝ => Ψ z θ) hsm hQz hBz
  refine le_trans hsl ?_
  exact le_of_eq rfl

/-- **Reduction of the requested `I₄` upper bound to the single-slice inequality.**

Assume the slice inequality: for every `Φ : ℝ → ℝ` of class `C²` on `(0, π/2)` whose weighted
squares `∫_θ (Φ/cos θ)²σ` and `∫_θ (Φ'')²σ` are integrable (`σ = sin(2θ)^{-η}`, `η = 99/100`),

`∫_θ ∂_θ(tan θ·Φ)·Φ''·σ ≤ 50∫_θ (Φ/cos θ)²σ + √(∫_θ(Φ/cos θ)²σ)·√(∫_θ(Φ'')²σ)`.

Then the requested estimate holds:
`IP (∂_θ(tan θ·Ψ)) (∂_θθΨ) ≤ C(‖Ψ/cos θ‖² + ‖Ψ/cos θ‖·‖∂_θθΨ‖ + ‖F‖²)`
for the honest class `Hon α F Ψ` with `HkMem α 0 Ψ` and `HkMem α 0 (Ψ/cos θ)`.

Route: for each `z ∈ (0,∞)` apply the slice inequality to `Φ := Ψ z` (the slice `Φ` is `C²` and
the two integrability hypotheses come from `HkMem α 0 (Ψ/cos θ)` and `Hon.memB`, dividing by
`w z² ≠ 0`); multiply by `w z²` and integrate in `z`; the cross term
`∫_z w²·√(∫_θ(Ψ/cos)²σ)·√(∫_θ(∂_θθΨ)²σ)` is bounded by Cauchy–Schwarz in `z`
(`Work.FTS.EllipticEst.AngSecond.abs_setIntegral_le_sqrt_mul_sqrt`, with the pointwise bound
`|∫_θ u·b·σ| ≤ √(∫_θ(cψ)²σ)·√(∫_θb²σ)` from
`Work.FTS.EllipticEst.AngSecond.slice_sq_integral_mul_le`), giving
`50·HkSq α 0 (Ψ/cos) + √(HkSq α 0 (Ψ/cos))·√(HkSq α 0 (∂_θθΨ))`; the remaining slack
`HkSq α 0 F ≥ 0` allows the constant `C = 51`.  Note `IP f g = ∫_z∫_θ f g w²σ` and
`HkSq α 0 g = ∫_z∫_θ g²w²σ` (`HkSq_zero_eq`), and `IPMem`/`HkMem` provide the integrability
needed for both Cauchy–Schwarz steps; `z = 0` is null since `w 0 = 0`. -/
theorem I4GlobalAssembly
    (hslice : ∀ (Φ : ℝ → ℝ), ContDiffOn ℝ 2 Φ (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn
        (fun θ => (Φ θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
        (Set.Icc 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn
        (fun θ => (deriv (deriv Φ) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
        (Set.Icc 0 (Real.pi / 2)) →
      (∫ θ in Set.Icc 0 (Real.pi / 2),
          deriv (fun θ' => Real.tan θ' * Φ θ') θ * deriv (deriv Φ) θ
            * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
        ≤ 50 * (∫ θ in Set.Icc 0 (Real.pi / 2),
              (Φ θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
          + Real.sqrt (∫ θ in Set.Icc 0 (Real.pi / 2),
              (Φ θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
            * Real.sqrt (∫ θ in Set.Icc 0 (Real.pi / 2),
              (deriv (deriv Φ) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.Honest.Hon α F Ψ →
        Work.Spaces.HkMem α 0 Ψ →
        Work.Spaces.HkMem α 0 (fun z θ => Ψ z θ / Real.cos θ) →
        Work.FTS.EllipticEst.AngSecond.IP
            (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
            (Work.Spaces.pthIter 2 Ψ)
          ≤ C * (Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => Ψ z θ / Real.cos θ)) ^ 2
              + Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => Ψ z θ / Real.cos θ))
                * Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ))
              + (Real.sqrt (Work.Spaces.HkSq α 0 F)) ^ 2) := by
  have hS : SliceIneq := hslice
  refine ⟨51, by norm_num, ?_⟩
  intro α F Ψ hHon hΨ hQmem
  set Q : ℝ → ℝ → ℝ := fun z θ => Ψ z θ / Real.cos θ with hQdef
  set B : ℝ → ℝ → ℝ := Work.Spaces.pthIter 2 Ψ with hBdef
  set u : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ
    with hudef
  set A : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, (Q z θ) ^ 2 * AngSecond.sig θ with hAdef
  set Bz : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, (B z θ) ^ 2 * AngSecond.sig θ with hBzdef
  set Fz : ℝ → ℝ := fun z =>
    ∫ θ in Work.Spaces.Iθ, u z θ * B z θ * AngSecond.w2 z * AngSecond.sig θ with hFzdef
  set Gz : ℝ → ℝ := fun z =>
    AngSecond.w2 z * (50 * A z + Real.sqrt (A z) * Real.sqrt (Bz z)) with hGzdef
  -- `HkSq α 0 g` is the iterated integral of `w z² ∫_θ g² σ`
  have hBmem' : Work.Spaces.HkMem α 0 B := hHon.memB
  have hA := hksq_eq_w2_sliceIntegral (α := α) (g := Q) hQmem
  have hBz := hksq_eq_w2_sliceIntegral (α := α) (g := B) hBmem'
  have hAint : MeasureTheory.IntegrableOn (fun z => AngSecond.w2 z * A z) Work.Spaces.Iz :=
    hA.1
  have hBzint : MeasureTheory.IntegrableOn (fun z => AngSecond.w2 z * Bz z) Work.Spaces.Iz :=
    hBz.1
  have hAval : ∫ z in Work.Spaces.Iz, AngSecond.w2 z * A z = Work.Spaces.HkSq α 0 Q := hA.2
  have hBzval : ∫ z in Work.Spaces.Iz, AngSecond.w2 z * Bz z = Work.Spaces.HkSq α 0 B := hBz.2
  -- the two angular slice integrals are nonnegative
  have hA0 : ∀ z, 0 ≤ A z := fun z =>
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (AngSecond.sig_nonneg hθ))
  have hBz0 : ∀ z, 0 ≤ Bz z := fun z =>
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (AngSecond.sig_nonneg hθ))
  -- the radial Cauchy–Schwarz for the cross term
  have hcross := AngSecond.setIntegral_w_mul_sqrt_le (s := Work.Spaces.Iz)
    (m := AngSecond.w2) (A := A) (B := Bz) AngSecond.w2_nonneg hA0 hBz0 hAint hBzint
  have hcrossB : (∫ z in Work.Spaces.Iz,
        AngSecond.w2 z * Real.sqrt (A z) * Real.sqrt (Bz z))
      ≤ Real.sqrt (Work.Spaces.HkSq α 0 Q) * Real.sqrt (Work.Spaces.HkSq α 0 B) := by
    refine le_trans hcross.2 ?_
    rw [hAval, hBzval]
  -- integrability and value of `∫_z Gz`
  have hGsum : (fun z => AngSecond.w2 z * (50 * A z + Real.sqrt (A z) * Real.sqrt (Bz z)))
      = fun z => 50 * (AngSecond.w2 z * A z)
          + AngSecond.w2 z * Real.sqrt (A z) * Real.sqrt (Bz z) :=
    funext fun z => by ring
  have hGint : MeasureTheory.IntegrableOn Gz Work.Spaces.Iz := by
    rw [hGzdef, hGsum]
    exact (hAint.const_mul 50).add hcross.1
  have hGval : ∫ z in Work.Spaces.Iz, Gz z
      = 50 * (Work.Spaces.HkSq α 0 Q)
        + ∫ z in Work.Spaces.Iz, AngSecond.w2 z * Real.sqrt (A z) * Real.sqrt (Bz z) := by
    rw [hGzdef, hGsum]
    rw [MeasureTheory.integral_add (hAint.const_mul 50) hcross.1,
      MeasureTheory.integral_const_mul, hAval]
  -- the pointwise domination `Fz ≤ Gz` on `Iz`
  have hpoint : ∀ z ∈ Work.Spaces.Iz, Fz z ≤ Gz z := by
    intro z hz
    rcases eq_or_ne z 0 with hz0 | hz0
    · -- at `z = 0` both sides vanish because `w 0 = 0`
      subst hz0
      have hw0 : AngSecond.w2 0 = 0 := by
        rw [AngSecond.w2, Work.Spaces.w]
        norm_num
      have hFz0 : Fz 0 = 0 := by
        rw [hFzdef]
        beta_reduce
        simp only [hw0, mul_zero]
        simp
      have hGz0 : Gz 0 = 0 := by
        rw [hGzdef]
        beta_reduce
        rw [hw0]; ring
      rw [hFz0, hGz0]
    · -- at `z > 0` use the slice inequality
      have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
      have hsl := I4SliceStep hS hHon hQmem hzpos
      have hslice' : (∫ θ in Work.Spaces.Iθ, u z θ * B z θ * AngSecond.sig θ)
          ≤ 50 * A z + Real.sqrt (A z) * Real.sqrt (Bz z) := hsl
      have hconst : Fz z = AngSecond.w2 z
          * (∫ θ in Work.Spaces.Iθ, u z θ * B z θ * AngSecond.sig θ) := by
        rw [hFzdef]
        beta_reduce
        rw [show (fun θ => u z θ * B z θ * AngSecond.w2 z * AngSecond.sig θ)
            = (fun θ => AngSecond.w2 z * (u z θ * B z θ * AngSecond.sig θ)) from
          funext fun θ => by ring]
        exact MeasureTheory.integral_const_mul _ _
      have hGz : Gz z = AngSecond.w2 z
          * (50 * A z + Real.sqrt (A z) * Real.sqrt (Bz z)) := by
        rw [hGzdef]
      rw [hconst, hGz]
      exact mul_le_mul_of_nonneg_left hslice' (AngSecond.w2_nonneg z)
  have hFG : Fz ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz] Gz :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ici).mpr
      (Filter.Eventually.of_forall fun z hz => hpoint z hz)
  have hGz0 : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz] Gz :=
    Filter.Eventually.of_forall fun z => by
      rw [hGzdef]
      exact mul_nonneg (AngSecond.w2_nonneg z)
        (add_nonneg (mul_nonneg (by norm_num) (hA0 z))
          (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
  -- the iterated integral is the pairing, and the assembly
  have hIP : AngSecond.IP u B = ∫ z in Work.Spaces.Iz, Fz z := by
    rw [hFzdef]
    rfl
  have hfinal : AngSecond.IP u B
      ≤ 50 * (Work.Spaces.HkSq α 0 Q)
        + Real.sqrt (Work.Spaces.HkSq α 0 Q) * Real.sqrt (Work.Spaces.HkSq α 0 B) := by
    calc AngSecond.IP u B = ∫ z in Work.Spaces.Iz, Fz z := hIP
      _ ≤ ∫ z in Work.Spaces.Iz, Gz z :=
          Work.FTS.EllipticEst.integral_le_integral_of_ae_le hFG hGint hGz0
      _ = 50 * (Work.Spaces.HkSq α 0 Q)
            + ∫ z in Work.Spaces.Iz,
                AngSecond.w2 z * Real.sqrt (A z) * Real.sqrt (Bz z) := hGval
      _ ≤ 50 * (Work.Spaces.HkSq α 0 Q)
            + Real.sqrt (Work.Spaces.HkSq α 0 Q) * Real.sqrt (Work.Spaces.HkSq α 0 B) :=
          add_le_add le_rfl hcrossB
  rw [hksq_sqrt_sq α Q, hksq_sqrt_sq α F]
  nlinarith [HkSq_zero_nonneg α Q, HkSq_zero_nonneg α F,
    Real.sqrt_nonneg (Work.Spaces.HkSq α 0 Q), Real.sqrt_nonneg (Work.Spaces.HkSq α 0 B)]

end Work.FTS.EllipticEst.Honest
