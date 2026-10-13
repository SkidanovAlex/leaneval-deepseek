/-
Change of variables `(σ,θ) ↦ (e^{ασ},θ)` for the transported unknown of the interior-regularity
reduction in the `(σ,θ)`-coordinates of `Q0.RRDefs`.

The hypothesis `LocallyIntegrableOn (Function.uncurry Ψ) Q0` constrains `Ψ` only on the *open*
quadrant `(0,∞)×(0,π/2)`.  For a compact `K` contained in the half-strip
`stripRR = ℝ × (0,π/2)` the image `Φ '' K` under `Φ (σ,θ) = (e^{ασ},θ)` is a compact subset of
the open quadrant (since `e^{ασ} > 0`), so `Ψ` is integrable there; transporting back along the
diffeomorphism `Φ` (Jacobian `|α| e^{ασ}`, and `α ≠ 0`, so `Φ` is injective) gives the
integrability of the pull-back.  The weight `wtRR α σ θ = α e^{5σ} cos θ` differs from the
Jacobian weight by the bounded factor `e^{(5-α)σ} cos θ = ± e^{(5-α)σ} cos θ`, whence the result.

Structure:

* `integrableOn_pullback_absJac` — the change-of-variables statement with the absolute Jacobian
  `e^{ασ} |α|` (the general Mathlib theorem
  `MeasureTheory.integrableOn_image_iff_integrableOn_abs_det_fderiv_smul` applied to `K`);
* `integrableOn_pullback_wtRR` — the target, by writing the weight as the product of the
  Jacobian weight and the continuous factor `(α/|α|) e^{(5-α)σ} cos θ` (split into the two signs
  of `α`, so that no division occurs).
-/
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.RingTheory.TotallySplit
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.EllipticEst.InteriorRegularity.Q0.RRDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.InteriorRegularity.Q0

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-- The determinant of `(c • 1).prodMap 1` acting on `ℝ × ℝ` is `c`. -/
private theorem det_toSpanSingleton_prodMap_one_rr (c : ℝ) :
    ((ContinuousLinearMap.toSpanSingleton ℝ c).prodMap (1 : ℝ →L[ℝ] ℝ)).det = c := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_prodMap, LinearMap.det_prodMap,
    LinearMap.det_ring]
  simp

/-- **Change of variables `(σ,θ) ↦ (e^{ασ},θ)` with the absolute Jacobian `e^{ασ}|α|`.**
For `α ≠ 0`, `Ψ` locally integrable on the open quadrant `Q0`, and `K` a compact subset of the
half-strip `ℝ × (0,π/2)`, the function
`e^{ασ}|α| · Ψ(e^{ασ},θ)` is integrable on `K`. -/
theorem integrableOn_pullback_absJac {α : ℝ} (hα : α ≠ 0) {Ψ : ℝ → ℝ → ℝ}
    (hΨ : MeasureTheory.LocallyIntegrableOn (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKs : K ⊆ Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ =>
        ((Real.exp (α * p.1) * |α| : ℝ) : ℂ) *
          ((Ψ (Real.exp (α * p.1)) p.2 : ℝ) : ℂ)) K := by
  set Φ : ℝ × ℝ → ℝ × ℝ := fun p => (Real.exp (α * p.1), p.2) with hΦ
  set Φ' : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ × ℝ) := fun p =>
    (ContinuousLinearMap.toSpanSingleton ℝ (Real.exp (α * p.1) * α)).prodMap
      (1 : ℝ →L[ℝ] ℝ) with hΦ'
  have hcont : Continuous Φ := by
    rw [hΦ]
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_fst)).prodMk continuous_snd
  -- the image is a compact subset of the open quadrant
  have hsub : Φ '' K ⊆ Work.FTS.EllipticEst.Q0 := by
    rintro y ⟨p, hp, rfl⟩
    exact ⟨Real.exp_pos _, (hKs hp).2.1, (hKs hp).2.2⟩
  have hcomp : IsCompact (Φ '' K) := hK.image hcont
  have hIntΨ : IntegrableOn (Function.uncurry Ψ) (Φ '' K) :=
    hΨ.integrableOn_compact_subset hsub hcomp
  have hIntC : IntegrableOn (fun y : ℝ × ℝ => ((Function.uncurry Ψ y : ℝ) : ℂ)) (Φ '' K) :=
    Complex.ofRealCLM.integrableOn_comp hIntΨ
  -- the derivative of `Φ` and its injectivity on `K`
  have hderiv : ∀ p ∈ K, HasFDerivWithinAt Φ (Φ' p) K p := by
    intro p _
    have h : HasDerivAt (fun z : ℝ => α * z) α p.1 := by
      simpa using (hasDerivAt_id (p.1 : ℝ)).const_mul α
    have hd : HasDerivAt (fun z : ℝ => Real.exp (α * z)) (Real.exp (α * p.1) * α) p.1 :=
      (Real.hasDerivAt_exp (α * p.1)).comp (p.1) h
    have h1 : HasFDerivAt (fun z : ℝ => Real.exp (α * z))
        (ContinuousLinearMap.toSpanSingleton ℝ (Real.exp (α * p.1) * α)) p.1 :=
      hd.hasFDerivAt
    have h2 : HasFDerivAt (id : ℝ → ℝ) (1 : ℝ →L[ℝ] ℝ) p.2 := hasFDerivAt_id p.2
    have h3 := HasFDerivAt.prodMap p h1 h2
    rw [hΦ, hΦ']
    exact h3.hasFDerivWithinAt
  have hinj : InjOn Φ K := by
    rintro ⟨a1, a2⟩ _ ⟨b1, b2⟩ _ h
    rw [hΦ] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have h1' : a1 = b1 := by
      have : α * a1 = α * b1 := Real.exp_injective h1
      exact mul_left_cancel₀ hα this
    rw [h1', h2]
  -- the general change of variables formula for integrability
  have key := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
    (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) hK.measurableSet hderiv hinj
    (fun y : ℝ × ℝ => ((Function.uncurry Ψ y : ℝ) : ℂ))).mp hIntC
  refine IntegrableOn.congr_fun key (fun p _ => ?_) hK.measurableSet
  have hdet : (Φ' p).det = Real.exp (α * p.1) * α := by
    rw [hΦ']
    exact det_toSpanSingleton_prodMap_one_rr _
  rw [hdet, abs_mul, abs_of_pos (Real.exp_pos (α * p.1)), Complex.real_smul, hΦ]
  simp only [Function.uncurry]

/-- **Change of variables for the substitution `(σ,θ) ↦ (e^{ασ},θ)`, with the weight of `Vf`.**
For `α ≠ 0`, `Ψ` locally integrable on the open quadrant `Q0`, and `K` a compact subset of the
half-strip `stripRR`, the function `α e^{5σ} cos θ · Ψ (e^{ασ}, θ)` is integrable on `K`. -/
theorem integrableOn_pullback_wtRR {α : ℝ} (hα : α ≠ 0) {Ψ : ℝ → ℝ → ℝ}
    (hΨ : MeasureTheory.LocallyIntegrableOn (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKs : K ⊆ Work.EllipticEst.InteriorRegularity.Q0.stripRR) :
    MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => ((Work.EllipticEst.InteriorRegularity.Q0.wtRR α p.1 p.2 *
        Ψ (Real.exp (α * p.1)) p.2 : ℝ) : ℂ)) K := by
  have hKs' : K ⊆ Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2) := hKs
  have hjac := integrableOn_pullback_absJac hα hΨ hK hKs'
  rcases lt_or_gt_of_ne hα with hneg | hpos
  · -- `α < 0`: the factor is `-e^{(5-α)σ} cos θ`
    have habs : |α| = -α := abs_of_neg hneg
    have hc : Continuous fun p : ℝ × ℝ =>
        ((-(Real.exp ((5 - α) * p.1) * Real.cos p.2) : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp
        (((Real.continuous_exp.comp (continuous_const.mul continuous_fst)).mul
          (Real.continuous_cos.comp continuous_snd)).neg)
    refine IntegrableOn.congr_fun (hjac.mul_continuousOn hc.continuousOn hK)
      (fun p _ => ?_) hK.measurableSet
    have he : Real.exp (α * p.1) * Real.exp ((5 - α) * p.1) = Real.exp (5 * p.1) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_inj, wtRR, habs, ← he]
    ring
  · -- `0 < α`: the factor is `e^{(5-α)σ} cos θ`
    have habs : |α| = α := abs_of_pos hpos
    have hc : Continuous fun p : ℝ × ℝ =>
        ((Real.exp ((5 - α) * p.1) * Real.cos p.2 : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp
        ((Real.continuous_exp.comp (continuous_const.mul continuous_fst)).mul
          (Real.continuous_cos.comp continuous_snd))
    refine IntegrableOn.congr_fun (hjac.mul_continuousOn hc.continuousOn hK)
      (fun p _ => ?_) hK.measurableSet
    have he : Real.exp (α * p.1) * Real.exp ((5 - α) * p.1) = Real.exp (5 * p.1) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_inj, wtRR, habs, ← he]
    ring

end Work.EllipticEst.InteriorRegularity.Q0
