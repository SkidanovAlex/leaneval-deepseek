import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.radialIBPOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false

/-- The T-adjoint coefficient `b z = (z-3)/(1+z)`. -/
def bcoefR (z : ℝ) : ℝ := (z - 3) / (1 + z)

@[simp] theorem bcoefR_apply (z : ℝ) : bcoefR z = (z - 3) / (1 + z) := rfl

/-- The squared radial weight `(w z)²` written out. -/
@[simp] theorem w_sq_unfold (z : ℝ) :
    (Work.Spaces.w z) ^ 2 = ((1 + z) ^ 2 / z ^ 2) ^ 2 := rfl




end Work.FTS.EllipticEst.TT
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.shift_pair_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

/-! **`shift_pair_bound`** — Cauchy–Schwarz for the two-sided shift pairing.

With `Δ y := G₂ (y+p) − G₂ (y−p)`, the difference of the two pairings is `∫ Q G₁ Δ`
(`integral_sub`, using `hJp`/`hJm`), which is bounded by `√(∫ Q G₁²) √(∫ Q Δ²)`:
`abs_integral_le_integral_abs`, `Q y = √(Q y)²`, then
`Work...JepsTransfer.Pieces.integral_mul_le_sqrt_mul_sqrt` (or
`...JepsTransfer.Pieces.abs_integral_mul_le_sqrt_mul_sqrt` in
`...JepsTransfer.Pieces2.weight_diff_integral_le`) applied to `√Q |G₁|` and `√Q |Δ|`. -/
theorem shift_pair_bound {Q G₁ G₂ : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hQ0 : ∀ y : ℝ × ℝ, 0 ≤ Q y) (hQm : Measurable Q) (hG1m : Measurable G₁)
    (hG2m : Measurable G₂)
    (hI1 : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G₁ y ^ 2))
    (hInt : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2))
    (hJp : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G₁ y * G₂ (y + p)))
    (hJm : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G₁ y * G₂ (y - p))) :
    |(∫ y : ℝ × ℝ, Q y * G₁ y * G₂ (y + p)) - (∫ y : ℝ × ℝ, Q y * G₁ y * G₂ (y - p))|
      ≤ Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
          * Real.sqrt (∫ y : ℝ × ℝ, Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2) := by
  -- The difference of the two pairings is the pairing of `Q G₁` with `Δ = G₂(·+p) − G₂(·−p)`.
  have hdiff : (∫ y : ℝ × ℝ, Q y * G₁ y * (G₂ (y + p) - G₂ (y - p)))
      = (∫ y : ℝ × ℝ, Q y * G₁ y * G₂ (y + p))
        - (∫ y : ℝ × ℝ, Q y * G₁ y * G₂ (y - p)) := by
    rw [← MeasureTheory.integral_sub hJp hJm]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => by ring))
  -- `Q y = √(Q y)²`, so the integrand is a product of two square-roots-of-`Q` factors.
  have hpt : ∀ y : ℝ × ℝ, |Q y * G₁ y * (G₂ (y + p) - G₂ (y - p))|
      = |Real.sqrt (Q y) * G₁ y| * |Real.sqrt (Q y) * (G₂ (y + p) - G₂ (y - p))| := by
    intro y
    have h1 : (Real.sqrt (Q y) * G₁ y) * (Real.sqrt (Q y) * (G₂ (y + p) - G₂ (y - p)))
        = Real.sqrt (Q y) ^ 2 * (G₁ y * (G₂ (y + p) - G₂ (y - p))) := by ring
    calc |Q y * G₁ y * (G₂ (y + p) - G₂ (y - p))|
        = |(Real.sqrt (Q y) * G₁ y) * (Real.sqrt (Q y) * (G₂ (y + p) - G₂ (y - p)))| := by
          rw [h1, Real.sq_sqrt (hQ0 y)]
          congr 1
          ring
      _ = |Real.sqrt (Q y) * G₁ y| * |Real.sqrt (Q y) * (G₂ (y + p) - G₂ (y - p))| :=
          abs_mul _ _
  -- The two square-integrable factors.
  have hA2 : MeasureTheory.Integrable (fun y : ℝ × ℝ => (Real.sqrt (Q y) * G₁ y) ^ 2) := by
    refine hI1.congr (Filter.Eventually.of_forall (fun y => ?_))
    show Q y * G₁ y ^ 2 = (Real.sqrt (Q y) * G₁ y) ^ 2
    rw [mul_pow, Real.sq_sqrt (hQ0 y)]
  have hB2 : MeasureTheory.Integrable
      (fun y : ℝ × ℝ => (Real.sqrt (Q y) * (G₂ (y + p) - G₂ (y - p))) ^ 2) := by
    refine hInt.congr (Filter.Eventually.of_forall (fun y => ?_))
    show Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2
        = (Real.sqrt (Q y) * (G₂ (y + p) - G₂ (y - p))) ^ 2
    rw [mul_pow, Real.sq_sqrt (hQ0 y)]
  have eA : (∫ y : ℝ × ℝ, (Real.sqrt (Q y) * G₁ y) ^ 2) = ∫ y : ℝ × ℝ, Q y * G₁ y ^ 2 :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => by
      show (Real.sqrt (Q y) * G₁ y) ^ 2 = Q y * G₁ y ^ 2
      rw [mul_pow, Real.sq_sqrt (hQ0 y)]))
  have eB : (∫ y : ℝ × ℝ, (Real.sqrt (Q y) * (G₂ (y + p) - G₂ (y - p))) ^ 2)
      = ∫ y : ℝ × ℝ, Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2 :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => by
      show (Real.sqrt (Q y) * (G₂ (y + p) - G₂ (y - p))) ^ 2
          = Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2
      rw [mul_pow, Real.sq_sqrt (hQ0 y)]))
  have hAm : Measurable (fun y : ℝ × ℝ => Real.sqrt (Q y) * G₁ y) := hQm.sqrt.mul hG1m
  have hBm : Measurable (fun y : ℝ × ℝ =>
      Real.sqrt (Q y) * (G₂ (y + p) - G₂ (y - p))) :=
    hQm.sqrt.mul ((hG2m.comp (measurable_id.add measurable_const)).sub
      (hG2m.comp (measurable_id.sub measurable_const)))
  -- Cauchy–Schwarz for the two `√Q`-weighted factors.
  have hCS := Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces2.abs_integral_mul_le_sqrt_mul_sqrt
    (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) hAm hBm hA2 hB2
  calc |(∫ y : ℝ × ℝ, Q y * G₁ y * G₂ (y + p)) - (∫ y : ℝ × ℝ, Q y * G₁ y * G₂ (y - p))|
      = |∫ y : ℝ × ℝ, Q y * G₁ y * (G₂ (y + p) - G₂ (y - p))| := by rw [hdiff]
    _ ≤ ∫ y : ℝ × ℝ, |Q y * G₁ y * (G₂ (y + p) - G₂ (y - p))| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ = ∫ y : ℝ × ℝ, |Real.sqrt (Q y) * G₁ y| * |Real.sqrt (Q y) * (G₂ (y + p) - G₂ (y - p))| :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ ≤ Real.sqrt (∫ y : ℝ × ℝ, (Real.sqrt (Q y) * G₁ y) ^ 2)
        * Real.sqrt (∫ y : ℝ × ℝ, (Real.sqrt (Q y) * (G₂ (y + p) - G₂ (y - p))) ^ 2) := hCS
    _ = Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
        * Real.sqrt (∫ y : ℝ × ℝ, Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2) := by rw [eA, eB]

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.shift_sq_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

/-- `ENNReal.ofReal` of a real integral is at most the lintegral of `ENNReal.ofReal`
(no integrability hypothesis is needed: either the lintegral is `∞`, or the function is
integrable and the two sides agree). -/
lemma ofReal_integral_le_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hfm : AEStronglyMeasurable f μ) (hf : 0 ≤ᵐ[μ] f) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases h : ∫⁻ x, ENNReal.ofReal (f x) ∂μ = ⊤
  · rw [h]; exact le_top
  · have h' : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≠ ⊤ := h
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      ((MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hfm hf).mp h') hf]

/-! **`shift_sq_bound`** — the second moment of the two-sided shift difference of a `C¹` profile.

For a nonnegative weight comparable to its translates forward and a `C¹` profile `G₂` with
weighted gradient in `L²`, `∫ Q y (G₂ (y+p) − G₂ (y−p))² ≤ 4‖p‖² e^{Cw(|p.1|+|p.2|)} ∫ Q y ‖fderiv ℝ G₂ y‖²`,
and the left integrand is integrable.

Suggested proof (feel free to restructure, and to delegate sub-steps):
* for fixed `y`, `φ t = G₂ (y + t • p)` has derivative `(fderiv ℝ G₂ (y + t•p)) p` at `t`
  (`ContDiff.continuous_fderiv`, `ContDiffAt.differentiableAt` → `DifferentiableAt.hasFDerivAt`,
  `HasFDerivAt.comp_hasDerivAt` with the affine parametrisation), so
  `intervalIntegral.integral_eq_sub_of_hasDerivAt` gives
  `G₂ (y+p) − G₂ (y−p) = ∫ t in (-1)..1, (fderiv ℝ G₂ (y + t•p)) p`;
* Cauchy–Schwarz in `t` (`ContinuousLinearMap.le_opNorm` then
  `MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg` with `p = q = 2` on the restricted
  measure, or `(∫ g)² ≤ (∫ 1²)(∫ g²)`) gives pointwise
  `(G₂ (y+p) − G₂ (y−p))² ≤ 2‖p‖² ∫ t in (-1)..1, ‖fderiv ℝ G₂ (y + t•p)‖²`;
* multiply by `Q y ≥ 0`, use `Q y ≤ e^{Cw|t||p|₁} Q (y + t•p) ≤ e^{Cw|p|₁} Q (y + t•p)` for
  `|t| ≤ 1` (`hQsh'` with shift `t • p`), and integrate in `y`, swapping the `y`- and
  `t`-integrals (Tonelli: `MeasureTheory.lintegral_lintegral_swap`,
  `MeasureTheory.ofReal_integral_eq_lintegral_ofReal`, translation invariance
  `MeasureTheory.lintegral_add_right_eq_self`), using `∫_{(-1)..1} 1 = 2`;
* integrability of the difference moment follows from finiteness of its lintegral
  (`MeasureTheory.hasFiniteIntegral_iff_ofReal`). -/
theorem shift_sq_bound {Q G₂ : ℝ × ℝ → ℝ} {Cw : ℝ} (hCw : 0 ≤ Cw)
    (hQ0 : ∀ y : ℝ × ℝ, 0 ≤ Q y) (hQm : Measurable Q)
    (hQsh' : ∀ y p : ℝ × ℝ, Q y ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Q (y + p))
    (hG2d : ContDiff ℝ 1 G₂)
    (hI2 : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * ‖fderiv ℝ G₂ y‖ ^ 2))
    (p : ℝ × ℝ) :
    MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2)
      ∧ ∫ y : ℝ × ℝ, Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2
        ≤ 4 * ‖p‖ ^ 2 * Real.exp (Cw * (|p.1| + |p.2|))
            * ∫ y : ℝ × ℝ, Q y * ‖fderiv ℝ G₂ y‖ ^ 2 := by
  set K : ℝ := Cw * (|p.1| + |p.2|) with hK
  set J : ℝ := ∫ y : ℝ × ℝ, Q y * ‖fderiv ℝ G₂ y‖ ^ 2 with hJ
  set F : ℝ × ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal (Q u * ‖fderiv ℝ G₂ u‖ ^ 2) with hF
  set s : Set ℝ := Set.Ioc (-1 : ℝ) 1 with hs
  set H : (ℝ × ℝ) × ℝ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (2 * ‖p‖ ^ 2 * Real.exp K
      * (Q (z.1 + z.2 • p) * ‖fderiv ℝ G₂ (z.1 + z.2 • p)‖ ^ 2)) with hH
  have hexpK : 0 ≤ Real.exp K := (Real.exp_pos K).le
  have hJ0 : 0 ≤ J := by
    rw [hJ]
    exact integral_nonneg (fun y => mul_nonneg (hQ0 y) (sq_nonneg _))
  have hcfd : Continuous (fun u : ℝ × ℝ => fderiv ℝ G₂ u) := hG2d.continuous_fderiv (by norm_num)
  have hG2c : Continuous G₂ := hG2d.continuous
  -- ### the weight comparison
  have hweight : ∀ (y : ℝ × ℝ) (t : ℝ), |t| ≤ 1 → Q y ≤ Real.exp K * Q (y + t • p) := by
    intro y t ht
    have hexp_eq : |(t • p).1| + |(t • p).2| = |t| * (|p.1| + |p.2|) := by
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, abs_mul]
      ring
    have h := hQsh' y (t • p)
    rw [hexp_eq] at h
    have hKle : Cw * (|t| * (|p.1| + |p.2|)) ≤ K := by
      rw [hK]
      have h2 : |t| * (|p.1| + |p.2|) ≤ |p.1| + |p.2| := by
        calc |t| * (|p.1| + |p.2|) ≤ 1 * (|p.1| + |p.2|) :=
              mul_le_mul_of_nonneg_right ht (by positivity)
          _ = |p.1| + |p.2| := by ring
      exact mul_le_mul_of_nonneg_left h2 hCw
    calc Q y ≤ Real.exp (Cw * (|t| * (|p.1| + |p.2|))) * Q (y + t • p) := h
      _ ≤ Real.exp K * Q (y + t • p) :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hKle) (hQ0 _)
  -- ### the pointwise bound in real numbers: FTC + Cauchy--Schwarz + weight comparison
  have hpt : ∀ y : ℝ × ℝ, Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2
      ≤ 2 * ‖p‖ ^ 2 * ∫ t in (-1 : ℝ)..1, Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2 := by
    intro y
    have hcont1 : Continuous (fun t : ℝ => y + t • p) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hca : Continuous (fun t : ℝ => (fderiv ℝ G₂ (y + t • p)) p) :=
      (hcfd.comp hcont1).clm_apply continuous_const
    have hcs := sq_intervalIntegral_le (f := fun t : ℝ => (fderiv ℝ G₂ (y + t • p)) p)
      (a := -1) (b := 1) (by norm_num) (hca.intervalIntegrable (-1) 1)
      ((hca.pow 2).intervalIntegrable (-1) 1)
    have hbnd : ∀ t : ℝ,
        ((fderiv ℝ G₂ (y + t • p)) p) ^ 2 ≤ ‖p‖ ^ 2 * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2 := by
      intro t
      have hop := ContinuousLinearMap.le_opNorm (fderiv ℝ G₂ (y + t • p)) p
      rw [Real.norm_eq_abs] at hop
      calc ((fderiv ℝ G₂ (y + t • p)) p) ^ 2
          = |(fderiv ℝ G₂ (y + t • p)) p| ^ 2 := by rw [sq_abs]
        _ ≤ (‖fderiv ℝ G₂ (y + t • p)‖ * ‖p‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hop 2
        _ = ‖p‖ ^ 2 * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2 := by ring
    have hstep : (∫ t in (-1 : ℝ)..1, (fderiv ℝ G₂ (y + t • p)) p) ^ 2
        ≤ 2 * ‖p‖ ^ 2 * ∫ t in (-1 : ℝ)..1, ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2 := by
      have hmono : ∫ t in (-1 : ℝ)..1, (fderiv ℝ G₂ (y + t • p)) p ^ 2
          ≤ ∫ t in (-1 : ℝ)..1, ‖p‖ ^ 2 * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2 :=
        intervalIntegral.integral_mono (μ := volume) (by norm_num)
          ((hca.pow 2).intervalIntegrable (-1) 1)
          ((continuous_const.mul ((hcfd.comp hcont1).norm.pow 2)).intervalIntegrable (-1) 1) hbnd
      have hcs' : (∫ t in (-1 : ℝ)..1, (fderiv ℝ G₂ (y + t • p)) p) ^ 2
          ≤ 2 * ∫ t in (-1 : ℝ)..1, (fderiv ℝ G₂ (y + t • p)) p ^ 2 := by
        simpa only [show (1 : ℝ) - (-1) = 2 from by norm_num] using hcs
      calc (∫ t in (-1 : ℝ)..1, (fderiv ℝ G₂ (y + t • p)) p) ^ 2
          ≤ 2 * ∫ t in (-1 : ℝ)..1, (fderiv ℝ G₂ (y + t • p)) p ^ 2 := hcs'
        _ ≤ 2 * ∫ t in (-1 : ℝ)..1, ‖p‖ ^ 2 * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2 :=
              mul_le_mul_of_nonneg_left hmono (by norm_num)
        _ = 2 * ‖p‖ ^ 2 * ∫ t in (-1 : ℝ)..1, ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2 := by
              rw [intervalIntegral.integral_const_mul]; ring
    rw [shift_diff_ftc hG2d y p]
    calc Q y * (∫ t in (-1 : ℝ)..1, (fderiv ℝ G₂ (y + t • p)) p) ^ 2
        ≤ Q y * (2 * ‖p‖ ^ 2 * ∫ t in (-1 : ℝ)..1, ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hstep (hQ0 y)
      _ = 2 * ‖p‖ ^ 2 * ∫ t in (-1 : ℝ)..1, Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2 := by
          rw [intervalIntegral.integral_const_mul]; ring
  -- ### the same bound, upgraded to `ℝ≥0∞` so that Tonelli applies
  have hpt2 : ∀ y : ℝ × ℝ,
      ENNReal.ofReal (Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2)
        ≤ ∫⁻ t in s, H (y, t) := by
    intro y
    have hmeas_t : AEStronglyMeasurable
        (fun t : ℝ => Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2) (volume.restrict s) := by
      apply Measurable.aestronglyMeasurable
      have hc : Continuous (fun t : ℝ => y + t • p) :=
        continuous_const.add (continuous_id.smul continuous_const)
      exact measurable_const.mul (((hcfd.comp hc).norm).pow 2).measurable
    have hmt : Measurable
        (fun t : ℝ => ENNReal.ofReal (Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2)) := by
      have hc : Continuous (fun t : ℝ => y + t • p) :=
        continuous_const.add (continuous_id.smul continuous_const)
      exact ENNReal.measurable_ofReal.comp
        (measurable_const.mul (((hcfd.comp hc).norm).pow 2).measurable)
    have hstep1 : ENNReal.ofReal (Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2)
        ≤ ENNReal.ofReal (2 * ‖p‖ ^ 2)
          * ENNReal.ofReal (∫ t in (-1 : ℝ)..1, Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2) := by
      calc ENNReal.ofReal (Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2)
          ≤ ENNReal.ofReal (2 * ‖p‖ ^ 2
              * ∫ t in (-1 : ℝ)..1, Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2) :=
            ENNReal.ofReal_le_ofReal (hpt y)
        _ = ENNReal.ofReal (2 * ‖p‖ ^ 2)
              * ENNReal.ofReal (∫ t in (-1 : ℝ)..1, Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2) :=
            ENNReal.ofReal_mul (by positivity)
    have hstep2 : ENNReal.ofReal (∫ t in (-1 : ℝ)..1, Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2)
        ≤ ∫⁻ t in s, ENNReal.ofReal (Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2) := by
      have h1 : (∫ t in (-1 : ℝ)..1, Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2)
          = ∫ t, Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2 ∂(volume.restrict s) := by
        rw [hs, intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      rw [h1]
      exact ofReal_integral_le_lintegral hmeas_t
        (Eventually.of_forall (fun t => mul_nonneg (hQ0 y) (sq_nonneg _)))
    have hstep3 : ENNReal.ofReal (2 * ‖p‖ ^ 2)
          * ENNReal.ofReal (∫ t in (-1 : ℝ)..1, Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2)
        ≤ ENNReal.ofReal (2 * ‖p‖ ^ 2)
          * ∫⁻ t in s, ENNReal.ofReal (Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2) :=
      mul_le_mul_right hstep2 _
    have hstep4 : ENNReal.ofReal (2 * ‖p‖ ^ 2)
          * ∫⁻ t in s, ENNReal.ofReal (Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2)
        = ∫⁻ t in s, ENNReal.ofReal (2 * ‖p‖ ^ 2)
          * ENNReal.ofReal (Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2) :=
      (MeasureTheory.lintegral_const_mul (ENNReal.ofReal (2 * ‖p‖ ^ 2)) hmt).symm
    have hstep5 : ∫⁻ t in s, ENNReal.ofReal (2 * ‖p‖ ^ 2)
          * ENNReal.ofReal (Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2)
        ≤ ∫⁻ t in s, H (y, t) := by
      rw [hH]
      refine MeasureTheory.lintegral_mono_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
      have htabs : |t| ≤ 1 := by
        rcases ht with ⟨h1, h2⟩
        rw [abs_le]
        exact ⟨by linarith, by linarith⟩
      have hw := hweight y t htabs
      have hreal : 2 * ‖p‖ ^ 2 * (Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2)
          ≤ 2 * ‖p‖ ^ 2 * Real.exp K
            * (Q (y + t • p) * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2) := by
        have h1 : Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2
            ≤ Real.exp K * Q (y + t • p) * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hw (sq_nonneg _)
        have h2 := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 2 * ‖p‖ ^ 2 by positivity)
        calc 2 * ‖p‖ ^ 2 * (Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2)
            ≤ 2 * ‖p‖ ^ 2
              * (Real.exp K * Q (y + t • p) * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2) := h2
          _ = 2 * ‖p‖ ^ 2 * Real.exp K
              * (Q (y + t • p) * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2) := by ring
      calc ENNReal.ofReal (2 * ‖p‖ ^ 2)
            * ENNReal.ofReal (Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2)
          = ENNReal.ofReal (2 * ‖p‖ ^ 2 * (Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2)) :=
            (ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 * ‖p‖ ^ 2 by positivity)).symm
        _ ≤ ENNReal.ofReal (2 * ‖p‖ ^ 2 * Real.exp K
              * (Q (y + t • p) * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2)) :=
            ENNReal.ofReal_le_ofReal hreal
    calc ENNReal.ofReal (Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2)
        ≤ ENNReal.ofReal (2 * ‖p‖ ^ 2)
          * ENNReal.ofReal (∫ t in (-1 : ℝ)..1, Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2) := hstep1
      _ ≤ ENNReal.ofReal (2 * ‖p‖ ^ 2)
          * ∫⁻ t in s, ENNReal.ofReal (Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2) := hstep3
      _ = ∫⁻ t in s, ENNReal.ofReal (2 * ‖p‖ ^ 2)
          * ENNReal.ofReal (Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2) := hstep4
      _ ≤ ∫⁻ t in s, H (y, t) := hstep5
  -- ### Tonelli: swap the `y`- and `t`-integrals, then use translation invariance
  have hHmeas : AEMeasurable H (volume.prod (volume.restrict s)) := by
    rw [hH]
    apply Measurable.aemeasurable
    have hc : Continuous (fun z : (ℝ × ℝ) × ℝ => z.1 + z.2 • p) :=
      continuous_fst.add (continuous_snd.smul continuous_const)
    exact ENNReal.measurable_ofReal.comp
      (measurable_const.mul ((hQm.comp hc.measurable).mul
        (((hcfd.comp hc).norm).pow 2).measurable))
  have hlin1 : ∫⁻ y : ℝ × ℝ, ENNReal.ofReal (Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2)
      ≤ ∫⁻ y : ℝ × ℝ, ∫⁻ t in s, H (y, t) :=
    MeasureTheory.lintegral_mono hpt2
  have hswap : ∫⁻ y : ℝ × ℝ, ∫⁻ t in s, H (y, t)
      = ∫⁻ t in s, ∫⁻ y : ℝ × ℝ, H (y, t) := by
    have h1 : ∫⁻ y : ℝ × ℝ, ∫⁻ t in s, H (y, t)
        = ∫⁻ z : (ℝ × ℝ) × ℝ, H z ∂(volume.prod (volume.restrict s)) :=
      (MeasureTheory.lintegral_prod (μ := volume) (ν := volume.restrict s) H hHmeas).symm
    have h2 : ∫⁻ t in s, ∫⁻ y : ℝ × ℝ, H (y, t)
        = ∫⁻ z : (ℝ × ℝ) × ℝ, H z ∂(volume.prod (volume.restrict s)) :=
      (MeasureTheory.lintegral_prod_symm (μ := volume) (ν := volume.restrict s) H hHmeas).symm
    rw [h1, h2]
  have hinner : ∀ t : ℝ, ∫⁻ y : ℝ × ℝ, H (y, t)
      = ENNReal.ofReal (2 * ‖p‖ ^ 2 * Real.exp K) * ∫⁻ y : ℝ × ℝ, F y := by
    intro t
    have h1 : ∀ y : ℝ × ℝ, H (y, t)
        = ENNReal.ofReal (2 * ‖p‖ ^ 2 * Real.exp K) * F (y + t • p) := by
      intro y
      rw [hH, hF]
      exact ENNReal.ofReal_mul (by positivity)
    have hmt : Measurable (fun y : ℝ × ℝ => F (y + t • p)) := by
      rw [hF]
      have hc : Continuous (fun y : ℝ × ℝ => y + t • p) := continuous_id.add continuous_const
      exact ENNReal.measurable_ofReal.comp
        ((hQm.comp hc.measurable).mul (((hcfd.comp hc).norm).pow 2).measurable)
    rw [MeasureTheory.lintegral_congr h1, MeasureTheory.lintegral_const_mul _ hmt,
      MeasureTheory.lintegral_add_right_eq_self F (t • p)]
  have hvol : (volume.restrict s) Set.univ = ENNReal.ofReal 2 := by
    rw [hs, Measure.restrict_apply_univ, Real.volume_Ioc]
    norm_num
  have hconst : ∫⁻ t in s, (ENNReal.ofReal (2 * ‖p‖ ^ 2 * Real.exp K) * ∫⁻ y : ℝ × ℝ, F y)
      = ENNReal.ofReal (2 * ‖p‖ ^ 2 * Real.exp K) * (∫⁻ y : ℝ × ℝ, F y)
        * ENNReal.ofReal 2 := by
    rw [MeasureTheory.lintegral_const, hvol]
  have hcF : ∫⁻ y : ℝ × ℝ, F y = ENNReal.ofReal J := by
    rw [hJ, hF]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hI2
      (Eventually.of_forall (fun y => mul_nonneg (hQ0 y) (sq_nonneg _)))).symm
  have hArit : ENNReal.ofReal (2 * ‖p‖ ^ 2 * Real.exp K) * ENNReal.ofReal J * ENNReal.ofReal 2
      = ENNReal.ofReal (4 * ‖p‖ ^ 2 * Real.exp K * J) := by
    calc ENNReal.ofReal (2 * ‖p‖ ^ 2 * Real.exp K) * ENNReal.ofReal J * ENNReal.ofReal 2
        = ENNReal.ofReal (2 * ‖p‖ ^ 2 * Real.exp K)
          * (ENNReal.ofReal J * ENNReal.ofReal 2) := by rw [mul_assoc]
      _ = ENNReal.ofReal (2 * ‖p‖ ^ 2 * Real.exp K) * ENNReal.ofReal (J * 2) := by
            rw [ENNReal.ofReal_mul hJ0]
      _ = ENNReal.ofReal (2 * ‖p‖ ^ 2 * Real.exp K * (J * 2)) := by
            rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 * ‖p‖ ^ 2 * Real.exp K by positivity)]
      _ = ENNReal.ofReal (4 * ‖p‖ ^ 2 * Real.exp K * J) := by
            congr 1; ring
  have hlin : ∫⁻ y : ℝ × ℝ, ENNReal.ofReal (Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2)
      ≤ ENNReal.ofReal (4 * ‖p‖ ^ 2 * Real.exp K * J) := by
    calc ∫⁻ y : ℝ × ℝ, ENNReal.ofReal (Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2)
        ≤ ∫⁻ y : ℝ × ℝ, ∫⁻ t in s, H (y, t) := hlin1
      _ = ∫⁻ t in s, ∫⁻ y : ℝ × ℝ, H (y, t) := hswap
      _ = ∫⁻ t in s, (ENNReal.ofReal (2 * ‖p‖ ^ 2 * Real.exp K) * ∫⁻ y : ℝ × ℝ, F y) :=
            MeasureTheory.lintegral_congr hinner
      _ = ENNReal.ofReal (2 * ‖p‖ ^ 2 * Real.exp K) * (∫⁻ y : ℝ × ℝ, F y)
            * ENNReal.ofReal 2 := hconst
      _ = ENNReal.ofReal (2 * ‖p‖ ^ 2 * Real.exp K) * ENNReal.ofReal J
            * ENNReal.ofReal 2 := by rw [hcF]
      _ = ENNReal.ofReal (4 * ‖p‖ ^ 2 * Real.exp K * J) := hArit
  -- ### back to the real statement
  have hnonneg : 0 ≤ᵐ[volume]
      (fun y : ℝ × ℝ => Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2) :=
    Eventually.of_forall (fun y => mul_nonneg (hQ0 y) (sq_nonneg _))
  have hmeasJ : AEStronglyMeasurable
      (fun y : ℝ × ℝ => Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2) volume := by
    apply Measurable.aestronglyMeasurable
    have hc : Continuous (fun y : ℝ × ℝ => G₂ (y + p) - G₂ (y - p)) :=
      (hG2c.comp (continuous_id.add continuous_const)).sub
        (hG2c.comp (continuous_id.sub continuous_const))
    exact hQm.mul (hc.pow 2).measurable
  have hne : ∫⁻ y : ℝ × ℝ, ENNReal.ofReal (Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2) ≠ ⊤ := by
    intro htop
    rw [htop] at hlin
    exact absurd hlin
      (not_le.mpr (ENNReal.ofReal_lt_top (r := 4 * ‖p‖ ^ 2 * Real.exp K * J)))
  have hInt : MeasureTheory.Integrable
      (fun y : ℝ × ℝ => Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2) :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hmeasJ hnonneg).mp hne
  have hval : ENNReal.ofReal (∫ y : ℝ × ℝ, Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2)
      = ∫⁻ y : ℝ × ℝ, ENNReal.ofReal (Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2) :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hnonneg
  have hle : (∫ y : ℝ × ℝ, Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2)
      ≤ 4 * ‖p‖ ^ 2 * Real.exp K * J := by
    have hq : (0 : ℝ) ≤ 4 * ‖p‖ ^ 2 * Real.exp K * J := mul_nonneg (by positivity) hJ0
    exact (ENNReal.ofReal_le_ofReal_iff hq).mp (by rw [hval]; exact hlin)
  exact ⟨hInt, hle⟩

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.L12Sub4.ConvDiffBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.L12Sub4

open MeasureTheory

/-- **Pointwise-in-`ζ` size of the mollifier error.**  Same hypotheses as `KernelWeightSub`, but the
conclusion is stated directly for the integral of the *difference* integrand
`p ↦ k p * (G (ζ + p.2) - G ζ)`: no rewrite of that integral as a difference of integrals (which
would need the integrability of `p ↦ k p * G (ζ + p.2)`) is required. -/
private lemma conv_diff_inner {k : ℝ × ℝ → ℝ} {G : ℝ → ℝ} {ε B : ℝ}
    (hknn : ∀ p, 0 ≤ k p) (hki : MeasureTheory.Integrable k) (hk1 : ∫ p : ℝ × ℝ, k p = 1)
    (hksupp : ∀ p, k p ≠ 0 → |p.2| ≤ ε)
    (hB : 0 ≤ B)
    (hGdiff : ∀ ζ q : ℝ, |q| ≤ 1 → |G (ζ + q) - G ζ| ≤ B * |q| * G ζ)
    (hε1 : ε ≤ 1) :
    ∀ ζ : ℝ, |∫ p : ℝ × ℝ, k p * (G (ζ + p.2) - G ζ)| ≤ B * ε * G ζ := by
  intro ζ
  by_cases hB0 : B = 0
  · -- `B = 0`: `G` is constant on `[ζ-1, ζ+1]`, hence the integrand vanishes identically.
    have hzero : ∀ p : ℝ × ℝ, k p * (G (ζ + p.2) - G ζ) = 0 := by
      intro p
      by_cases hp : k p = 0
      · rw [hp, zero_mul]
      · have hp2 : |p.2| ≤ 1 := le_trans (hksupp p hp) hε1
        have h2 : |G (ζ + p.2) - G ζ| ≤ 0 := by simpa [hB0] using hGdiff ζ p.2 hp2
        have h3 : G (ζ + p.2) - G ζ = 0 :=
          abs_eq_zero.mp (le_antisymm h2 (abs_nonneg _))
        rw [h3, mul_zero]
    have hI : (∫ p : ℝ × ℝ, k p * (G (ζ + p.2) - G ζ)) = 0 := by
      rw [show (fun p : ℝ × ℝ => k p * (G (ζ + p.2) - G ζ)) = (fun _ => (0 : ℝ)) from
        funext hzero, integral_zero]
    rw [hI]
    simp [hB0]
  · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
    -- The oscillation hypothesis forces `G ζ ≥ 0` (evaluate at `q = 1/2`).
    have hGζ : 0 ≤ G ζ := by
      have h := hGdiff ζ (1 / 2) (by norm_num)
      have h1 : |(1 : ℝ) / 2| = (1 : ℝ) / 2 := by norm_num
      rw [h1] at h
      exact nonneg_of_mul_nonneg_right (le_trans (abs_nonneg _) h)
        (mul_pos hBpos (by norm_num))
    -- Pointwise domination of the difference integrand on the support of `k`.
    have hpt : ∀ p : ℝ × ℝ, k p * |G (ζ + p.2) - G ζ| ≤ (B * ε * G ζ) * k p := by
      intro p
      by_cases hp : k p = 0
      · rw [hp, zero_mul, mul_zero]
      · have hp2 : |p.2| ≤ ε := hksupp p hp
        have hp2' : |p.2| ≤ 1 := le_trans hp2 hε1
        have h1 : |G (ζ + p.2) - G ζ| ≤ B * |p.2| * G ζ := hGdiff ζ p.2 hp2'
        have h2 : B * |p.2| * G ζ ≤ B * ε * G ζ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp2 hB) hGζ
        have h3 : |G (ζ + p.2) - G ζ| ≤ B * ε * G ζ := le_trans h1 h2
        calc k p * |G (ζ + p.2) - G ζ| ≤ k p * (B * ε * G ζ) :=
              mul_le_mul_of_nonneg_left h3 (hknn p)
          _ = (B * ε * G ζ) * k p := by ring
    have hInt : MeasureTheory.Integrable (fun p : ℝ × ℝ => (B * ε * G ζ) * k p) :=
      hki.const_mul _
    calc |∫ p : ℝ × ℝ, k p * (G (ζ + p.2) - G ζ)|
        ≤ ∫ p : ℝ × ℝ, |k p * (G (ζ + p.2) - G ζ)| := abs_integral_le_integral_abs
      _ = ∫ p : ℝ × ℝ, k p * |G (ζ + p.2) - G ζ| := by
            refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
            change |k p * (G (ζ + p.2) - G ζ)| = k p * |G (ζ + p.2) - G ζ|
            rw [abs_mul, abs_of_nonneg (hknn p)]
      _ ≤ ∫ p : ℝ × ℝ, (B * ε * G ζ) * k p := by
            refine MeasureTheory.integral_mono_of_nonneg
              (Filter.Eventually.of_forall fun p => mul_nonneg (hknn p) (abs_nonneg _)) hInt
              (Filter.Eventually.of_forall hpt)
      _ = B * ε * G ζ := by rw [MeasureTheory.integral_const_mul, hk1, mul_one]

/-- **The outer integral step.**  If a plane function `A` is pointwise dominated by `B ε G(·.2)` and
`x ↦ G x.2 * |F x.1 x.2|` is integrable, then
`|∫_x A x · F x.1 x.2| ≤ B ε ∫_x G x.2 · |F x.1 x.2|`. -/
private lemma plane_le_of_pointwise {A : ℝ × ℝ → ℝ} {G : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {ε B : ℝ}
    (hA : ∀ x : ℝ × ℝ, |A x| ≤ B * ε * G x.2)
    (hFint : MeasureTheory.Integrable (fun x : ℝ × ℝ => G x.2 * |F x.1 x.2|)) :
    |∫ x : ℝ × ℝ, A x * F x.1 x.2| ≤ B * ε * (∫ x : ℝ × ℝ, G x.2 * |F x.1 x.2|) := by
  have h1 : |∫ x : ℝ × ℝ, A x * F x.1 x.2| ≤ ∫ x : ℝ × ℝ, |A x * F x.1 x.2| :=
    abs_integral_le_integral_abs
  have h2 : ∫ x : ℝ × ℝ, |A x * F x.1 x.2|
      ≤ ∫ x : ℝ × ℝ, (B * ε) * (G x.2 * |F x.1 x.2|) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun x => abs_nonneg _) (hFint.const_mul (B * ε))
      (Filter.Eventually.of_forall fun x => ?_)
    change |A x * F x.1 x.2| ≤ (B * ε) * (G x.2 * |F x.1 x.2|)
    rw [abs_mul]
    calc |A x| * |F x.1 x.2| ≤ (B * ε * G x.2) * |F x.1 x.2| :=
          mul_le_mul_of_nonneg_right (hA x) (abs_nonneg _)
      _ = (B * ε) * (G x.2 * |F x.1 x.2|) := by ring
  have h3 : ∫ x : ℝ × ℝ, (B * ε) * (G x.2 * |F x.1 x.2|)
      = B * ε * ∫ x : ℝ × ℝ, G x.2 * |F x.1 x.2| := by
    rw [MeasureTheory.integral_const_mul]
  exact le_trans h1 (le_trans h2 (le_of_eq h3))

/-- **The `ε`-size of the mollifier error in the weight-adjoint form** (generic).  Under the
hypotheses of `KernelWeightSub` (nonnegative integrable kernel `k` of mass `1` supported in the strip
`|p₂| ≤ ε ≤ 1`, continuous weight `G` with `|G (ζ+q) - G ζ| ≤ B|q| G ζ` for `|q| ≤ 1`) and with
`x ↦ G x.2 · |F x.1 x.2|` integrable,

  `|∫_x (∫_p k p · (G (x.2+p.2) - G x.2)) · F x.1 x.2| ≤ B ε ∫_x G x.2 · |F x.1 x.2|`

(integrals over the plane).

Hints: the pointwise-in-`ζ` bound `|∫ p, k p * (G (ζ+p.2) - G ζ)| ≤ B ε G ζ` is
`KernelWeightSub` (`FTS/StrongEps/L12Sub4/KernelWeightSub`, already proved, importable) after the
rewrite `∫ p, k p (G(ζ+p.2) - Gζ) = (∫ p, k p G(ζ+p.2)) - Gζ` (`MeasureTheory.integral_sub` +
`MeasureTheory.integral_mul_const` + `hk1`); alternatively prove it directly with
`MeasureTheory.norm_integral_le_integral_norm`, `MeasureTheory.integral_mono_of_nonneg` and
`∫ p, k p * |p.2| ≤ ε`.  Then specialise at `ζ = x.2`, use
`MeasureTheory.norm_integral_le_integral_norm` for the outer integral, and
`MeasureTheory.integral_mono_of_nonneg` against the integrable majorant
`B ε (G x.2 * |F x.1 x.2|)` (`hFint.const_mul`), finishing with
`MeasureTheory.integral_const_mul`.  No measurability of the parametric integral
`x ↦ ∫ p, k p (G (x.2+p.2) - G x.2)` is needed for these steps. -/
theorem ConvDiffBound (k : ℝ × ℝ → ℝ) (G : ℝ → ℝ) (F : ℝ → ℝ → ℝ) {ε B : ℝ}
    (hknn : ∀ p, 0 ≤ k p) (hki : MeasureTheory.Integrable k) (hk1 : ∫ p : ℝ × ℝ, k p = 1)
    (hksupp : ∀ p, k p ≠ 0 → |p.2| ≤ ε)
    (hGcont : Continuous G) (hB : 0 ≤ B)
    (hGdiff : ∀ ζ q : ℝ, |q| ≤ 1 → |G (ζ + q) - G ζ| ≤ B * |q| * G ζ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hFint : MeasureTheory.Integrable (fun x : ℝ × ℝ => G x.2 * |F x.1 x.2|)) :
    |∫ x : ℝ × ℝ, (∫ p : ℝ × ℝ, k p * (G (x.2 + p.2) - G x.2)) * F x.1 x.2|
      ≤ B * ε * (∫ x : ℝ × ℝ, G x.2 * |F x.1 x.2|) := by
  have hA : ∀ x : ℝ × ℝ, |(∫ p : ℝ × ℝ, k p * (G (x.2 + p.2) - G x.2))| ≤ B * ε * G x.2 :=
    fun x => conv_diff_inner hknn hki hk1 hksupp hB hGdiff hε1 x.2
  exact plane_le_of_pointwise
    (A := fun x : ℝ × ℝ => ∫ p : ℝ × ℝ, k p * (G (x.2 + p.2) - G x.2)) hA hFint

end Work.FTS.StrongEps.L12Sub4
end
