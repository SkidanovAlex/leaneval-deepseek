import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.RingTheory.TotallySplit

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

set_option linter.unusedVariables false

namespace Work.EllipticEst.InteriorRegularity.IR

/-- The determinant of `(c • 1).prodMap 1` acting on `ℝ × ℝ` is `c`. -/
private theorem det_toSpanSingleton_prodMap_one (c : ℝ) :
    ((ContinuousLinearMap.toSpanSingleton ℝ c).prodMap (1 : ℝ →L[ℝ] ℝ)).det = c := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_prodMap, LinearMap.det_prodMap,
    LinearMap.det_ring]
  simp

/-- Substitution `z = exp (α σ)` in the integral of a complex-valued function over the open
quadrant `(0,∞) × (0,π/2)`: the integral becomes the integral over the half-strip
`ℝ × (0,π/2)` of `X (exp (ασ), θ) · α exp (ασ)`.

This is the one-dimensional change of variables formula `∫_{f '' s} g = ∫_s |f'| • (g ∘ f)`
applied to the diffeomorphism `(σ,θ) ↦ (exp (ασ), θ)` of `ℝ × (0,π/2)` onto
`(0,∞) × (0,π/2)`; its Jacobian determinant is `α exp (ασ)`. -/
theorem integralQ0eqStrip {α : ℝ} (hα : 0 < α) {X : ℝ × ℝ → ℂ}
    (hX : MeasureTheory.IntegrableOn X (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    (∫ p in Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2), X p)
      = ∫ q in (Set.univ ×ˢ Set.Ioo 0 (π / 2) : Set (ℝ × ℝ)),
          X (Real.exp (α * q.1), q.2) * (α * Real.exp (α * q.1)) := by
  set t : Set ℝ := Set.Ioo 0 (π / 2) with ht
  set Φ : ℝ × ℝ → ℝ × ℝ := fun p => (Real.exp (α * p.1), p.2) with hΦ
  -- the parameter domain and the substitution are measurable
  have htm : MeasurableSet t := by rw [ht]; exact measurableSet_Ioo
  have hmeas : MeasurableSet ((Set.univ : Set ℝ) ×ˢ t) := MeasurableSet.univ.prod htm
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
  have himg : Φ '' (Set.univ ×ˢ t) = Set.Ioi 0 ×ˢ t := by
    rw [hΦ]
    change (Prod.map (fun z : ℝ => Real.exp (α * z)) id) '' (Set.univ ×ˢ t) = Set.Ioi 0 ×ˢ t
    rw [Set.prodMap_image_prod, Set.image_univ, hrange, Set.image_id]
  -- and it is injective there
  have hinj : Set.InjOn Φ (Set.univ ×ˢ t) := by
    rw [hΦ]
    rintro ⟨a1, a2⟩ _ ⟨b1, b2⟩ _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have h1' : a1 = b1 := by
      have : α * a1 = α * b1 := Real.exp_injective h1
      exact mul_left_cancel₀ hα.ne' this
    rw [h1', h2]
  -- the derivative of the substitution, with its Jacobian determinant `α exp (α σ)`
  have hderiv : ∀ p ∈ ((Set.univ : Set ℝ) ×ˢ t),
      HasFDerivWithinAt Φ
        ((ContinuousLinearMap.toSpanSingleton ℝ (Real.exp (α * p.1) * α)).prodMap
          (1 : ℝ →L[ℝ] ℝ)) ((Set.univ : Set ℝ) ×ˢ t) p := by
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
    rw [hΦ]
    exact h3.hasFDerivWithinAt
  -- the one-dimensional change of variables formula in `ℝ × ℝ`
  have key := MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
    (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) (s := (Set.univ : Set ℝ) ×ˢ t) (f := Φ)
    (f' := fun p => (ContinuousLinearMap.toSpanSingleton ℝ (Real.exp (α * p.1) * α)).prodMap
      (1 : ℝ →L[ℝ] ℝ)) hmeas hderiv hinj X
  rw [himg] at key
  rw [key]
  -- identify the Jacobian factor `|α exp (α σ)| = α exp (α σ)` with the requested one
  refine MeasureTheory.setIntegral_congr_fun hmeas ?_
  intro p hp
  simp only [hΦ]
  have hdet : ((ContinuousLinearMap.toSpanSingleton ℝ (Real.exp (α * p.1) * α)).prodMap
      (1 : ℝ →L[ℝ] ℝ)).det = Real.exp (α * p.1) * α := det_toSpanSingleton_prodMap_one _
  rw [hdet, abs_of_pos (by positivity), Complex.real_smul, Complex.ofReal_mul]
  ring

end Work.EllipticEst.InteriorRegularity.IR
