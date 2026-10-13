import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.SourceBound

open scoped Real Topology
open MeasureTheory Set Filter

/-- **Angular slices of `F` and of `pzIter 2 Ψ` are honest.**

For a datum of the weak hypothesis class `EllWeakPos α k F Ψ` (any `k`, in particular `k ≥ 2`),
and every `z > 0`, the angular slices `θ ↦ F z θ * sinCos2 θ` and
`θ ↦ pzIter 2 Ψ z θ * sinCos2 θ` are integrable on `Iθ = [0, π/2]`.

Proof sketch.  `HkMem α k F` gives, for every `z ∈ Iz`, integrability on `Iθ` of
`HkIntegrand α k F z ·`; the useful helpers are `Work.Spaces.sq_le_HkIntegrand_z` (which bounds
the `i = 0` summand by the whole integrand) and
`Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted` (which gives `|a * sinCos2 θ| ≤ (a * W)^2 + 1`
with `W = w z / sin(2θ)^(η/2)` for `z > 0`), so `|F z θ * sinCos2 θ| ≤ HkIntegrand α k F z θ + 1`
and `IntegrableOn` follows from `hmem.1`.  AE-strong-measurability comes from `F = bslOp α Ψ` on
the open quadrant together with the smoothness of `bslOp α Ψ` (the same route as in
`remov/pairingIdentityEq.lean`).
The second claim is the same argument for `g = fun z θ => z^2 * pzIter 2 Ψ z θ` (from
`HkMem α k (fun z θ => z^2 * pzIter 2 Ψ z θ)`), followed by the rescaling by `z^2 > 0`.
A ready-made reference for both is `remov/hkMemSliceAbsIntegrable.lean`. -/
theorem weakSliceIntegrable {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    (∀ z, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => F z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ) ∧
    (∀ z, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ) := by
  have hS : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  -- the angular profile `sin θ cos²θ`, as a function of the pair `(z,θ)`
  have hsin_c : Continuous (fun p : ℝ × ℝ => Work.Elliptic.sinCos2 p.2) := by
    simp only [Work.Elliptic.sinCos2]
    exact (Real.continuous_sin.comp continuous_snd).mul
      ((Real.continuous_cos.comp continuous_snd).pow 2)
  have hvol : (volume : Measure ℝ) Work.Spaces.Iθ ≠ ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  constructor
  · -- ## The source slice `θ ↦ F z θ * sin〈θ〉cos²〈θ〉`
    intro z hz
    have hzIz : z ∈ Work.Spaces.Iz := by rw [Work.Spaces.Iz]; exact le_of_lt hz
    have hmem : Integrable (fun θ => Work.Spaces.HkIntegrand α k F z θ)
        (volume.restrict Work.Spaces.Iθ) := h.memF.1 z hzIz
    -- a.e. strong measurability: on the open quadrant `F` is the smooth function `bslOp α Ψ`
    have haesm : AEStronglyMeasurable (fun θ => F z θ * Work.Elliptic.sinCos2 θ)
        (volume.restrict Work.Spaces.Iθ) := by
      have hcont : ContinuousOn (fun p : ℝ × ℝ =>
          Work.Elliptic.bslOp α Ψ p.1 p.2 * Work.Elliptic.sinCos2 p.2)
          Work.FTS.EllipticEst.Q0 :=
        ((Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hS).continuousOn).mul
          hsin_c.continuousOn
      have h1 : AEStronglyMeasurable
          (fun θ => Work.Elliptic.bslOp α Ψ z θ * Work.Elliptic.sinCos2 θ)
          (volume.restrict Work.Spaces.Iθ) :=
        Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hz
      refine h1.congr ?_
      show ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        Work.Elliptic.bslOp α Ψ z θ * Work.Elliptic.sinCos2 θ
          = F z θ * Work.Elliptic.sinCos2 θ
      refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
      rw [h.eq z hz θ hθ.1 hθ.2]
    refine (hmem.add (MeasureTheory.integrableOn_const (C := (1 : ℝ)) hvol)).mono' haesm ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    rw [Real.norm_eq_abs]
    have hb := Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted
      (f := fun θ => F z θ) hz hθ
    have hq := Work.Spaces.sq_le_HkIntegrand_z α k F z θ 0 (Nat.zero_le k)
    rw [Work.Spaces.DzIter_zero] at hq
    exact le_trans hb (add_le_add_left hq 1)
  · -- ## The slice `θ ↦ pzIter 2 Ψ z θ * sin〈θ〉cos²〈θ〉`
    intro z hz
    have hzIz : z ∈ Work.Spaces.Iz := by rw [Work.Spaces.Iz]; exact le_of_lt hz
    have hmem : Integrable (fun θ => Work.Spaces.HkIntegrand α k
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ)
        (volume.restrict Work.Spaces.Iθ) := h.memA.1 z hzIz
    have haesm : AEStronglyMeasurable
        (fun θ => Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ)
        (volume.restrict Work.Spaces.Iθ) := by
      have hcont : ContinuousOn (fun p : ℝ × ℝ =>
          Work.Spaces.pzIter 2 Ψ p.1 p.2 * Work.Elliptic.sinCos2 p.2)
          Work.FTS.EllipticEst.Q0 :=
        (hS.pzIter 2).continuousOn.mul hsin_c.continuousOn
      exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hz
    have hz4ne : z ^ 4 ≠ 0 := pow_ne_zero 4 (ne_of_gt hz)
    refine ((hmem.const_mul ((z ^ 4)⁻¹)).add
      (MeasureTheory.integrableOn_const (C := (1 : ℝ)) hvol)).mono' haesm ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    rw [Real.norm_eq_abs]
    have hb := Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted
      (f := fun θ => Work.Spaces.pzIter 2 Ψ z θ) hz hθ
    have hq := Work.Spaces.sq_le_HkIntegrand_z α k
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ 0 (Nat.zero_le k)
    rw [Work.Spaces.DzIter_zero] at hq
    have hEq : (Work.Spaces.pzIter 2 Ψ z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = (z ^ 4)⁻¹ * (((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
      have h1 : ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          = z ^ 4 * (Work.Spaces.pzIter 2 Ψ z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        ring
      rw [h1, inv_mul_cancel_left₀ hz4ne]
    calc |Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ|
        ≤ (Work.Spaces.pzIter 2 Ψ z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1 := hb
      _ = (z ^ 4)⁻¹ * (((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) + 1 := by
          rw [hEq]
      _ ≤ (z ^ 4)⁻¹ * Work.Spaces.HkIntegrand α k
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ + 1 :=
          add_le_add_left (mul_le_mul_of_nonneg_left hq (by positivity)) 1

end Work.FTS.EllipticEst.remov.SourceBound
