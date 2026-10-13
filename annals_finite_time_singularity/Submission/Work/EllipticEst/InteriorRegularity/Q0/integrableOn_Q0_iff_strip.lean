/-
Integrability on the open quadrant `Q0 = (0,∞) × (0,π/2)` versus integrability on the half-strip
`ℝ × (0,π/2)` under the change of variables `z = exp (α σ)` (Jacobian `α exp (α σ)`).

This is the integrability form of `Work.EllipticEst.InteriorRegularity.IR.integralQ0eqStrip`; it is
the change of variables formula for the diffeomorphism `(σ,θ) ↦ (exp (ασ), θ)` of
`ℝ × (0,π/2)` onto `(0,∞) × (0,π/2)`, stated for a function with values in an arbitrary real
normed space (no integrability hypothesis is needed: the general Mathlib theorem
`MeasureTheory.integrableOn_image_iff_integrableOn_abs_det_fderiv_smul` gives the equivalence of
the two integrability statements directly).
-/
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.RingTheory.TotallySplit
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

/-- The determinant of `(c • 1).prodMap 1` acting on `ℝ × ℝ` is `c`. -/
private theorem det_toSpanSingleton_prodMap_one (c : ℝ) :
    ((ContinuousLinearMap.toSpanSingleton ℝ c).prodMap (1 : ℝ →L[ℝ] ℝ)).det = c := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_prodMap, LinearMap.det_prodMap,
    LinearMap.det_ring]
  simp

theorem integrableOn_Q0_iff_strip {α : ℝ} (hα : 0 < α) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (X : ℝ × ℝ → E) :
    MeasureTheory.IntegrableOn X Work.FTS.EllipticEst.Q0 ↔
      MeasureTheory.IntegrableOn (fun q : ℝ × ℝ =>
          (α * Real.exp (α * q.1)) • X (Real.exp (α * q.1), q.2))
        (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  -- the substitution `(σ,θ) ↦ (exp (ασ), θ)` and its derivative
  set Φ : ℝ × ℝ → ℝ × ℝ := fun p => (Real.exp (α * p.1), p.2) with hΦ
  set f' : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := fun p =>
    (ContinuousLinearMap.toSpanSingleton ℝ (Real.exp (α * p.1) * α)).prodMap
      (1 : ℝ →L[ℝ] ℝ) with hf'
  set s : Set (ℝ × ℝ) := Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2) with hs'
  -- the half-strip is measurable
  have hs : MeasurableSet s := by rw [hs']; exact MeasurableSet.univ.prod measurableSet_Ioo
  -- the range of `σ ↦ exp (α σ)` is `(0,∞)`
  have hrange : Set.range (fun z : ℝ => Real.exp (α * z)) = Set.Ioi (0 : ℝ) := by
    have h1 : Set.range (fun z : ℝ => α * z) = Set.univ := by
      rw [Set.eq_univ_iff_forall]
      intro y
      exact ⟨y / α, by field_simp⟩
    calc Set.range (fun z : ℝ => Real.exp (α * z))
        = Set.range (Real.exp ∘ fun z : ℝ => α * z) := rfl
      _ = Real.exp '' Set.range (fun z : ℝ => α * z) := Set.range_comp _ _
      _ = Real.exp '' Set.univ := by rw [h1]
      _ = Set.range Real.exp := Set.image_univ
      _ = Set.Ioi 0 := Real.range_exp
  -- the substitution maps the half-strip onto the open quadrant
  have himg : Φ '' s = Work.FTS.EllipticEst.Q0 := by
    rw [hΦ, hs', Work.FTS.EllipticEst.Q0]
    change (Prod.map (fun z : ℝ => Real.exp (α * z)) id) ''
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2))
        = Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)
    rw [Set.prodMap_image_prod, Set.image_univ, hrange, Set.image_id]
  -- and it is injective there
  have hinj : Set.InjOn Φ s := by
    rw [hΦ]
    rintro ⟨a1, a2⟩ _ ⟨b1, b2⟩ _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have h1' : a1 = b1 := by
      have : α * a1 = α * b1 := Real.exp_injective h1
      exact mul_left_cancel₀ hα.ne' this
    rw [h1', h2]
  -- its derivative on the half-strip
  have hderiv : ∀ p ∈ s, HasFDerivWithinAt Φ (f' p) s p := by
    intro p hp
    have h : HasDerivAt (fun z : ℝ => α * z) α p.1 := by
      simpa using (hasDerivAt_id (p.1 : ℝ)).const_mul α
    have hd : HasDerivAt (fun z : ℝ => Real.exp (α * z)) (Real.exp (α * p.1) * α) p.1 :=
      (Real.hasDerivAt_exp (α * p.1)).comp (p.1) h
    have h1 : HasFDerivAt (fun z : ℝ => Real.exp (α * z))
        (ContinuousLinearMap.toSpanSingleton ℝ (Real.exp (α * p.1) * α)) p.1 :=
      hd.hasFDerivAt
    have h2 : HasFDerivAt (id : ℝ → ℝ) (1 : ℝ →L[ℝ] ℝ) p.2 := hasFDerivAt_id p.2
    have h3 := HasFDerivAt.prodMap p h1 h2
    rw [hΦ, hf']
    exact h3.hasFDerivWithinAt
  -- the general change of variables formula for integrability
  have key := MeasureTheory.integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
    (μ := (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))) (s := s) (f := Φ)
    (f' := f') hs hderiv hinj X
  rw [himg] at key
  rw [key]
  -- identify the Jacobian `|det| = α exp (α σ)`
  have hfun : (fun q : ℝ × ℝ => |(f' q).det| • X (Φ q))
      = fun q : ℝ × ℝ => (α * Real.exp (α * q.1)) • X (Real.exp (α * q.1), q.2) := by
    funext q
    simp only [hΦ, hf']
    rw [det_toSpanSingleton_prodMap_one,
      abs_of_pos (by positivity : (0 : ℝ) < Real.exp (α * q.1) * α),
      mul_comm (Real.exp (α * q.1)) α]
  rw [hfun]

end Work.EllipticEst.InteriorRegularity.Q0
