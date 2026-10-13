import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.RingTheory.TotallySplit
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.InteriorRegularity.VT

open scoped Real Topology
open MeasureTheory Set

/-- The determinant of `(c • 1).prodMap 1` acting on `ℝ × ℝ` is `c`. -/
private theorem det_toSpanSingleton_prodMap_one (c : ℝ) :
    ((ContinuousLinearMap.toSpanSingleton ℝ c).prodMap (1 : ℝ →L[ℝ] ℝ)).det = c := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_prodMap, LinearMap.det_prodMap,
    LinearMap.det_ring]
  simp

/-- Change of variables for the substitution `(s,θ) ↦ (e^{αs},θ)`: the Jacobian-weighted pull-back of a function locally integrable on the open quadrant `Q0` is integrable on every compact subset of the open strip.

Warning: do NOT import `Submission.Work.EllipticEst.InteriorRegularity.IR.Defs` (it re-declares `stripE` and clashes with `Strip.lean`). A sibling proved the analogous statement with the weight `α e^{α s}` as `IR.memLp_Usub_mul.expPullbackIntegrable_aux` -- use it only as a template. -/
theorem pullbackIntegrable {α : ℝ} (hα : 0 < α) {Ψ : ℝ → ℝ → ℝ}
    (hΨ : MeasureTheory.LocallyIntegrableOn (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKs : K ⊆ Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => ((α * Real.exp ((5 + 2 * α) * p.1) * Real.cos p.2
        * Ψ (Real.exp (α * p.1)) p.2 : ℝ) : ℂ)) K := by
  -- The coordinate substitution `(s,θ) ↦ (e^{αs},θ)` and its differential.
  set Φ : ℝ × ℝ → ℝ × ℝ := fun p => (Real.exp (α * p.1), p.2) with hΦ
  set Φ' : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ × ℝ) := fun p =>
    (ContinuousLinearMap.toSpanSingleton ℝ (Real.exp (α * p.1) * α)).prodMap
      (1 : ℝ →L[ℝ] ℝ) with hΦ'
  have hcont : Continuous Φ := by
    rw [hΦ]
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_fst)).prodMk continuous_snd
  -- The image of the compact set is a compact subset of the open quadrant.
  have hsub : Φ '' K ⊆ Work.FTS.EllipticEst.Q0 := by
    rintro y ⟨p, hp, rfl⟩
    exact ⟨Real.exp_pos _, (hKs hp).2.1, (hKs hp).2.2⟩
  have hcomp : IsCompact (Φ '' K) := hK.image hcont
  have hIntΨ : MeasureTheory.IntegrableOn (Function.uncurry Ψ) (Φ '' K) :=
    hΨ.integrableOn_compact_subset hsub hcomp
  -- `Φ` is a `C¹` diffeomorphism onto its image, of Jacobian determinant `α e^{αs}`.
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
      exact mul_left_cancel₀ hα.ne' this
    rw [h1', h2]
  -- The change of variables, with the bare Jacobian weight.
  have hkey : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => |(Φ' p).det| • (Function.uncurry Ψ) (Φ p)) K :=
    (MeasureTheory.integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
      (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) hK.measurableSet hderiv hinj
      (Function.uncurry Ψ)).mp hIntΨ
  -- The remaining factor `e^{(5+α)s} cos θ` is continuous, hence bounded on the compact `K`.
  have hb : ContinuousOn (fun p : ℝ × ℝ => Real.exp ((5 + α) * p.1) * Real.cos p.2) K :=
    (((Real.continuous_exp.comp (continuous_const.mul continuous_fst)).mul
      (Real.continuous_cos.comp continuous_snd)).continuousOn)
  have hkey2 : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => (|(Φ' p).det| • (Function.uncurry Ψ) (Φ p))
        * (Real.exp ((5 + α) * p.1) * Real.cos p.2)) K :=
    hkey.mul_continuousOn hb hK
  have hkey3 : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => (((|(Φ' p).det| • (Function.uncurry Ψ) (Φ p))
        * (Real.exp ((5 + α) * p.1) * Real.cos p.2) : ℝ) : ℂ)) K :=
    Complex.ofRealCLM.integrableOn_comp hkey2
  refine hkey3.congr_fun (fun p _ => ?_) hK.measurableSet
  beta_reduce
  have hdet : (Φ' p).det = Real.exp (α * p.1) * α := by
    simp only [hΦ']
    exact det_toSpanSingleton_prodMap_one _
  rw [hdet, abs_of_pos (mul_pos (Real.exp_pos _) hα), hΦ]
  simp only [Function.uncurry, smul_eq_mul]
  rw [show (5 + 2 * α) * p.1 = α * p.1 + (5 + α) * p.1 by ring, Real.exp_add]
  push_cast
  ring

end Work.EllipticEst.InteriorRegularity.VT
