/-
Copyright: work module for the Elgindi finite-time singularity project.

# The slice bound from the `I4` identity (`Work.FTS.EllipticEst.Mine.slice_ident_bound_fts`)

Self-contained proof of the slice estimate: for `u` of class `C^2` on a neighbourhood of
`[0, pi/2]` with `u 0 = u (pi/2) = 0`, the weighted angular integral of `((u/cos t)')^2`
against `qEta t = sin(2t)^{-eta}` (`eta = 99/100`) is bounded by
`4/(1-eta)^2 * int (u'')^2 qEta + 2 * int (u/cos t)^2 qEta`; numerically the constant is `40000`.

Route.  The `I4` identity `Work.FTS.EllipticEst.TanTheta.slice_ident` (with `eta = Work.Spaces.eta`)
reads

  `int Acoef * ((u/cos)')^2 qEta = -int sin t * (u/cos)' * u'' qEta + ((1-eta)/2) int cos 2t (u/cos)^2 qEta`,

with `Acoef t = ((1-eta)/2) cos 2t + 2 sin^2 t >= (1-eta)/2 = 1/200`.  The left side dominates
`(1/200) int ((u/cos)')^2 qEta`; the first term on the right is at most
`(1/400) int ((u/cos)')^2 qEta + 100 int (u'')^2 qEta` by AM-GM, and the second is at most
`(1/200) int (u/cos)^2 qEta` since `|cos 2t| <= 1`.  Hence
`(1/400) int ((u/cos)')^2 qEta <= 100 int (u'')^2 qEta + (1/200) int (u/cos)^2 qEta`,
i.e. the stated bound with constants `40000` and `2`.

The file is self-contained (it does **not** import `...EllipticEst.tanTheta_bound`, which declares
the colliding `HkIntegrand_zero_eq` and has an unfilled proof of its main theorem); the
conditional step `slice_ident_bound_of_ident_fts` and the two algebraic helpers are local copies
of the corresponding proved declarations of that module.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TanTheta.Defs
import Submission.Work.FTS.EllipticEst.TanTheta.slice_ident

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Mine

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- Multiplication of a nonnegative `L¹` angular slice by a bounded function. -/
theorem integrableOn_mul_bdd_fts {g h : ℝ → ℝ} {C : ℝ}
    (hg : MeasureTheory.IntegrableOn g (Set.Ioo 0 (Real.pi / 2)))
    (hg0 : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2), 0 ≤ g θ)
    (hh : MeasureTheory.AEStronglyMeasurable h
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))))
    (hbd : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2), |h θ| ≤ C) :
    MeasureTheory.IntegrableOn (fun θ => h θ * g θ) (Set.Ioo 0 (Real.pi / 2)) := by
  refine MeasureTheory.Integrable.mono' (hg.const_mul C) (hh.mul hg.aestronglyMeasurable) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hg0 θ hθ)]
  exact mul_le_mul_of_nonneg_right (hbd θ hθ) (hg0 θ hθ)

/-- The pointwise AM-GM bound used in the `I₄` slice estimate: for `κ > 0` and `q ≥ 0`,
`|x||y|q ≤ (κ/2)(x²q) + (1/(2κ))(y²q)`. -/
theorem amgm_pointwise_fts {κ x y q : ℝ} (hκ : 0 < κ) (hq : 0 ≤ q) :
    |x| * |y| * q ≤ κ / 2 * (x ^ 2 * q) + 1 / (2 * κ) * (y ^ 2 * q) := by
  have hkey : 2 * κ * |x| * |y| * q ≤ κ ^ 2 * x ^ 2 * q + y ^ 2 * q := by
    have h := mul_nonneg hq (sq_nonneg (κ * |x| - |y|))
    have hexp : q * (κ * |x| - |y|) ^ 2
        = κ ^ 2 * (x ^ 2 * q) - 2 * κ * |x| * |y| * q + y ^ 2 * q := by
      rw [show (κ * |x| - |y|) ^ 2
        = (κ * |x|) ^ 2 - 2 * (κ * |x|) * |y| + |y| ^ 2 by ring]
      rw [mul_pow, sq_abs x, sq_abs y]
      ring
    linarith [h, hexp]
  have hgoal : (|x| * |y| * q) * (2 * κ)
      ≤ (κ / 2 * (x ^ 2 * q) + 1 / (2 * κ) * (y ^ 2 * q)) * (2 * κ) := by
    have he : (κ / 2 * (x ^ 2 * q) + 1 / (2 * κ) * (y ^ 2 * q)) * (2 * κ)
        = κ ^ 2 * x ^ 2 * q + y ^ 2 * q := by
      field_simp
    rw [he]
    linarith [hkey]
  exact le_of_mul_le_mul_right hgoal (by linarith : (0:ℝ) < 2 * κ)

/-- **The slice bound of the `I₄` identity, conditional on the identity itself.**  Given the
identity instance for this `u` (as provided by `slice_ident`), the three integrability
hypotheses of the terms of its right-hand side (plus the integrability of `(u/cos θ)'²·qEta`)
give

  `∫_θ ((u/cos θ)')²·qEta ≤ 4/(1-η)²·∫_θ (u'')²·qEta + 2·∫_θ (u/cos θ)²·qEta`.

Route: the left side of the identity dominates `((1-η)/2)∫((u/cos)')²qEta` (as
`Acoef θ = (1-η)/2 + (1+η)sin²θ`); the last term of the right side is at most
`((1-η)/2)∫(u/cos)²qEta` in absolute value; the middle term is handled by the pointwise
inequality `|a||b| ≤ (κ/2)a² + (1/(2κ))b²` with `κ = (1-η)/2 = 1/200` applied to
`a = |(u/cos)'|√qEta`, `b = |u''|√qEta` and `sin θ ≤ 1`. -/
theorem slice_ident_bound_of_ident_fts (u : ℝ → ℝ)
    (hident : (∫ θ in Set.Ioo 0 (Real.pi / 2),
          Acoef θ * (deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 * qEta θ)
        = - (∫ θ in Set.Ioo 0 (Real.pi / 2),
              (Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ) * (deriv (deriv u) θ)
                * qEta θ)
          + ((1 - Work.Spaces.eta) / 2)
            * (∫ θ in Set.Ioo 0 (Real.pi / 2),
                Real.cos (2 * θ) * (u θ / Real.cos θ) ^ 2 * qEta θ))
    (hi2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv u) θ) ^ 2 * qEta θ) (Set.Ioo 0 (Real.pi / 2)))
    (hi3 : MeasureTheory.IntegrableOn
      (fun θ => (u θ / Real.cos θ) ^ 2 * qEta θ) (Set.Ioo 0 (Real.pi / 2)))
    (hi4 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 * qEta θ)
      (Set.Ioo 0 (Real.pi / 2))) :
    (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 * qEta θ)
      ≤ 4 / (1 - Work.Spaces.eta) ^ 2
          * (∫ θ in Set.Ioo 0 (Real.pi / 2), (deriv (deriv u) θ) ^ 2 * qEta θ)
        + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (u θ / Real.cos θ) ^ 2 * qEta θ) := by
  have heta : (1 - Work.Spaces.eta) / 2 = 1 / 200 := by
    rw [Work.Spaces.eta]; norm_num
  have heta2 : 1 - Work.Spaces.eta = 1 / 100 := by rw [Work.Spaces.eta]; norm_num
  set L : ℝ → ℝ := fun θ => (deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 * qEta θ with hL
  set W : ℝ → ℝ := fun θ => (deriv (deriv u) θ) ^ 2 * qEta θ with hW
  set B : ℝ → ℝ := fun θ => (u θ / Real.cos θ) ^ 2 * qEta θ with hB
  set Sf : ℝ → ℝ := fun θ => Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ
      * (deriv (deriv u) θ) * qEta θ with hSf
  have hL4 : MeasureTheory.IntegrableOn L (Set.Ioo 0 (Real.pi / 2)) := by rw [hL]; exact hi4
  have hW2 : MeasureTheory.IntegrableOn W (Set.Ioo 0 (Real.pi / 2)) := by rw [hW]; exact hi2
  have hB3 : MeasureTheory.IntegrableOn B (Set.Ioo 0 (Real.pi / 2)) := by rw [hB]; exact hi3
  have hL0 : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2), 0 ≤ L θ := by
    intro θ hθ; rw [hL]
    exact mul_nonneg (sq_nonneg _) (qEta_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  have hident' : (∫ θ in Set.Ioo 0 (Real.pi / 2),
        Acoef θ * ((deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 * qEta θ))
      = - (∫ θ in Set.Ioo 0 (Real.pi / 2),
            (Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ) * (deriv (deriv u) θ)
              * qEta θ)
        + (1 / 200)
          * (∫ θ in Set.Ioo 0 (Real.pi / 2),
              Real.cos (2 * θ) * (u θ / Real.cos θ) ^ 2 * qEta θ) := by
    simpa only [mul_assoc, heta, hSf] using hident
  have hid : (∫ θ in Set.Ioo 0 (Real.pi / 2), Acoef θ * L θ)
      = - (∫ θ in Set.Ioo 0 (Real.pi / 2), Sf θ)
        + (1 / 200)
          * (∫ θ in Set.Ioo 0 (Real.pi / 2),
              Real.cos (2 * θ) * (u θ / Real.cos θ) ^ 2 * qEta θ) := by
    rw [hident']
  -- `Acoef · L` is integrable
  have hAl : MeasureTheory.IntegrableOn (fun θ => Acoef θ * L θ) (Set.Ioo 0 (Real.pi / 2)) :=
    integrableOn_mul_bdd_fts hL4 hL0
      ((by unfold Acoef; fun_prop : Continuous Acoef).measurable.aestronglyMeasurable)
      (fun θ _ => by rw [abs_of_nonneg (Acoef_nonneg θ)]; exact Acoef_le_two θ)
  -- (A) `(1/200) ∫L ≤ ∫Acoef·L`
  have hA : (1 / 200) * (∫ θ in Set.Ioo 0 (Real.pi / 2), L θ)
      ≤ ∫ θ in Set.Ioo 0 (Real.pi / 2), Acoef θ * L θ := by
    have hpt : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))),
        (1 / 200) * L θ ≤ Acoef θ * L θ := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      have h := sub_eta_half_le_Acoef θ
      rw [heta] at h
      exact mul_le_mul_of_nonneg_right h (hL0 θ hθ)
    have h0 : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))]
        (fun θ => (1 / 200) * L θ) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      exact mul_nonneg (by norm_num) (hL0 θ hθ)
    have hstep := MeasureTheory.integral_mono_of_nonneg h0 hAl hpt
    rwa [MeasureTheory.integral_const_mul] at hstep
  -- (B) `∫Sf ≤ (1/400)∫L + 100∫W`
  have hB1 : |∫ θ in Set.Ioo 0 (Real.pi / 2), Sf θ|
      ≤ 1 / 400 * (∫ θ in Set.Ioo 0 (Real.pi / 2), L θ)
        + 100 * (∫ θ in Set.Ioo 0 (Real.pi / 2), W θ) := by
    have hmaj : MeasureTheory.IntegrableOn
        (fun θ => 1 / 400 * L θ + 100 * W θ) (Set.Ioo 0 (Real.pi / 2)) :=
      (hL4.const_mul (1 / 400)).add (hW2.const_mul 100)
    have hpt : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))),
        |Sf θ| ≤ 1 / 400 * L θ + 100 * W θ := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      have hq0 : 0 ≤ qEta θ := qEta_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have hs0 : 0 ≤ Real.sin θ :=
        Real.sin_nonneg_of_nonneg_of_le_pi (le_of_lt hθ.1) (by linarith [hθ.2, Real.pi_pos])
      have hs1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
      have hLv : L θ = (deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 * qEta θ := by rw [hL]
      have hWv : W θ = (deriv (deriv u) θ) ^ 2 * qEta θ := by rw [hW]
      have h1 : |deriv (fun θ' => u θ' / Real.cos θ') θ| * |deriv (deriv u) θ| * qEta θ
          ≤ 1 / 400 * L θ + 100 * W θ := by
        have h := amgm_pointwise_fts (κ := (1:ℝ) / 200)
          (x := deriv (fun θ' => u θ' / Real.cos θ') θ) (y := deriv (deriv u) θ)
          (by norm_num) hq0
        have h200 : ((1:ℝ) / 200) / 2 = 1 / 400 := by norm_num
        have h200' : 1 / (2 * ((1:ℝ) / 200)) = 100 := by norm_num
        rw [hLv, hWv]
        linarith [h, h200, h200']
      have h2 : |Sf θ| = Real.sin θ * (|deriv (fun θ' => u θ' / Real.cos θ') θ|
          * |deriv (deriv u) θ| * qEta θ) := by
        rw [hSf, abs_mul, abs_mul, abs_mul, abs_of_nonneg hs0, abs_of_nonneg hq0]
        ring
      rw [h2]
      calc Real.sin θ * (|deriv (fun θ' => u θ' / Real.cos θ') θ|
              * |deriv (deriv u) θ| * qEta θ)
          ≤ 1 * (|deriv (fun θ' => u θ' / Real.cos θ') θ|
              * |deriv (deriv u) θ| * qEta θ) :=
            mul_le_mul_of_nonneg_right hs1 (by positivity)
        _ = |deriv (fun θ' => u θ' / Real.cos θ') θ| * |deriv (deriv u) θ| * qEta θ := by ring
        _ ≤ 1 / 400 * L θ + 100 * W θ := h1
    have hstep := MeasureTheory.integral_mono_of_nonneg (g := fun θ => 1 / 400 * L θ + 100 * W θ)
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
        exact abs_nonneg _) hmaj hpt
    have h2 := abs_integral_le_integral_abs
      (μ := MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) (f := fun θ => Sf θ)
    rw [MeasureTheory.integral_add (hL4.const_mul (1 / 400)) (hW2.const_mul 100),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hstep
    linarith [h2, hstep]
  -- (C) `(1/200)∫cos2θ·B ≤ (1/200)∫B`
  have hC : (1 / 200)
      * (∫ θ in Set.Ioo 0 (Real.pi / 2), Real.cos (2 * θ) * (u θ / Real.cos θ) ^ 2 * qEta θ)
      ≤ (1 / 200) * (∫ θ in Set.Ioo 0 (Real.pi / 2), B θ) := by
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    have hpt : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))),
        |Real.cos (2 * θ) * (u θ / Real.cos θ) ^ 2 * qEta θ| ≤ B θ := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      have hq0 : 0 ≤ qEta θ := qEta_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have hc1 := Real.abs_cos_le_one (2 * θ)
      rw [hB]
      have h1 : |Real.cos (2 * θ) * (u θ / Real.cos θ) ^ 2 * qEta θ|
          = |Real.cos (2 * θ)| * ((u θ / Real.cos θ) ^ 2 * qEta θ) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hq0,
          abs_of_nonneg (sq_nonneg (u θ / Real.cos θ))]
        ring
      rw [h1]
      exact mul_le_of_le_one_left (mul_nonneg (sq_nonneg _) hq0) hc1
    have hstep := MeasureTheory.integral_mono_of_nonneg (g := B)
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
        exact abs_nonneg _) hB3 hpt
    have h2 := abs_integral_le_integral_abs
      (μ := MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)))
      (f := fun θ => Real.cos (2 * θ) * (u θ / Real.cos θ) ^ 2 * qEta θ)
    linarith [h2, hstep, le_abs_self (∫ θ in Set.Ioo 0 (Real.pi / 2),
      Real.cos (2 * θ) * (u θ / Real.cos θ) ^ 2 * qEta θ)]
  -- assemble
  have hmain : (1 / 200) * (∫ θ in Set.Ioo 0 (Real.pi / 2), L θ)
      ≤ 1 / 400 * (∫ θ in Set.Ioo 0 (Real.pi / 2), L θ)
        + 100 * (∫ θ in Set.Ioo 0 (Real.pi / 2), W θ)
        + (1 / 200) * (∫ θ in Set.Ioo 0 (Real.pi / 2), B θ) := by
    have haux : - (∫ θ in Set.Ioo 0 (Real.pi / 2), Sf θ)
        ≤ 1 / 400 * (∫ θ in Set.Ioo 0 (Real.pi / 2), L θ)
          + 100 * (∫ θ in Set.Ioo 0 (Real.pi / 2), W θ) := by
      linarith [hB1, neg_le_abs (∫ θ in Set.Ioo 0 (Real.pi / 2), Sf θ)]
    have hmid : (∫ θ in Set.Ioo 0 (Real.pi / 2), Acoef θ * L θ)
        ≤ 1 / 400 * (∫ θ in Set.Ioo 0 (Real.pi / 2), L θ)
          + 100 * (∫ θ in Set.Ioo 0 (Real.pi / 2), W θ)
          + (1 / 200) * (∫ θ in Set.Ioo 0 (Real.pi / 2), B θ) := by
      linarith [hid, haux, hC]
    linarith [hA, hmid]
  have hmain2 : (∫ θ in Set.Ioo 0 (Real.pi / 2), L θ)
      ≤ 4 / (1 - Work.Spaces.eta) ^ 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), W θ)
        + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), B θ) := by
    have h1 : 4 / (1 - Work.Spaces.eta) ^ 2 = 40000 := by rw [heta2]; norm_num
    rw [h1]
    linarith [hmain]
  rw [hL, hW, hB]
  exact hmain2

theorem slice_ident_bound_fts (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo (-1) (Real.pi / 2 + 1)))
    (hu0 : u 0 = 0) (hu1 : u (Real.pi / 2) = 0)
    (hi1 : MeasureTheory.IntegrableOn
      (fun θ => (deriv u θ) ^ 2 * Work.FTS.EllipticEst.qEta θ) (Set.Ioo 0 (Real.pi / 2)))
    (hi2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.qEta θ)
      (Set.Ioo 0 (Real.pi / 2)))
    (hi3 : MeasureTheory.IntegrableOn
      (fun θ => (u θ / Real.cos θ) ^ 2 * Work.FTS.EllipticEst.qEta θ)
      (Set.Ioo 0 (Real.pi / 2)))
    (hi4 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 * Work.FTS.EllipticEst.qEta θ)
      (Set.Ioo 0 (Real.pi / 2))) :
    (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 * Work.FTS.EllipticEst.qEta θ)
      ≤ 4 / (1 - Work.Spaces.eta) ^ 2
          * (∫ θ in Set.Ioo 0 (Real.pi / 2),
              (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.qEta θ)
        + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
            (u θ / Real.cos θ) ^ 2 * Work.FTS.EllipticEst.qEta θ) :=
  slice_ident_bound_of_ident_fts u
    (Work.FTS.EllipticEst.TanTheta.slice_ident Work.Spaces.eta
      (le_of_lt Work.Spaces.eta_pos) Work.Spaces.eta_lt_one u hu hu0 hu1 hi1 hi2 hi3)
    hi2 hi3 hi4

end Work.FTS.EllipticEst.Mine
