/-
Auxiliary lemmas for `Work.FTS.EllipticEst.ThetaU.interpol_mixed_weighted_open`.

Contents (all proved here, to be consumed by the main file and by the delegated
`compact_interpol`):

* `bcoef` and its bound: `b z = (z-3)/(1+z)` is the logarithmic derivative of `z * (w z)^2`;
* `radial_ibp_eta`: integration by parts in the radial variable against the weight `w²`,
  for functions supported in `[δ,R] ⊆ (0,∞)` (no boundary terms at either end).
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.weight_algebra_fts
import Submission.Work.FTS.EllipticEst.integrableOn_Ioi_of_tail_zero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.ThetaU

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The coefficient `b` -/

/-- `b z = (z-3)/(1+z)`, the logarithmic derivative of `z * (w z)^2`: `(z w²)' = b · w²`. -/
def bcoef (z : ℝ) : ℝ := (z - 3) / (1 + z)

theorem bcoef_abs_le {z : ℝ} (hz : 0 ≤ z) : |bcoef z| ≤ 3 := by
  rw [bcoef, abs_div, abs_of_pos (by linarith : (0 : ℝ) < 1 + z)]
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 + z)]
  rcases le_or_gt z 3 with h | h
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

/-- The derivative of `z ↦ z * (w z)^2`, in terms of `bcoef`. -/
theorem deriv_mul_w_sq {z : ℝ} (hz : 0 < z) :
    deriv (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) z
      = bcoef z * (Work.Spaces.w z) ^ 2 := by
  obtain ⟨_, _, _, hG, _, _, _, _, _, _, _⟩ := Work.FTS.EllipticEst.weight_algebra_fts
  rw [hG z (ne_of_gt hz), bcoef, Work.Spaces.w]
  field_simp

/-- `z ↦ z * (w z)^2` is differentiable at every `z > 0`, with derivative `b z · w z ²`. -/
theorem hasDerivAt_mul_w_sq (z : ℝ) (hz : 0 < z) :
    HasDerivAt (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) (bcoef z * (Work.Spaces.w z) ^ 2) z := by
  have hd : DifferentiableAt ℝ (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) z := by
    have heq : (fun y : ℝ => y * (Work.Spaces.w y) ^ 2)
        =ᶠ[𝓝 z] (fun y : ℝ => (1 + y) ^ 4 / y ^ 3) := by
      filter_upwards [isOpen_ne.mem_nhds (ne_of_gt hz)] with y hy
      rw [Work.Spaces.w]
      field_simp
    rw [heq.differentiableAt_iff]
    exact DifferentiableAt.div (by fun_prop) (by fun_prop) (pow_ne_zero 3 (ne_of_gt hz))
  rw [← deriv_mul_w_sq hz]
  exact hd.hasDerivAt

/-- `b · w²` as a rational function. -/
theorem bcoef_mul_w_sq (z : ℝ) (hz : z ≠ 0) :
    bcoef z * (Work.Spaces.w z) ^ 2 = (z - 3) * (1 + z) ^ 3 / z ^ 4 := by
  rw [bcoef, Work.Spaces.w]
  field_simp

/-- `w² · z` as a rational function. -/
theorem w_sq_mul_self (z : ℝ) (hz : z ≠ 0) :
    (Work.Spaces.w z) ^ 2 * z = (1 + z) ^ 4 / z ^ 3 := by
  rw [Work.Spaces.w]
  field_simp

/-! ## Radial integration by parts against `w² dz` -/

/-- **Radial integration by parts for the weight `w²`**, for functions vanishing off `[δ,R]`
with `0 < δ < R`:
`∫_{Iz} w² φ (z ∂_z ψ) = ∫_{Iz} w² (-(z ∂_z φ) - b φ) ψ`, `b z = (z-3)/(1+z)`.

The boundary terms vanish: `φ ψ` is supported in `[δ,R]`. -/
theorem radial_ibp_eta {δ R : ℝ} (hδ : 0 < δ) (hδR : δ < R) {φ ψ : ℝ → ℝ}
    (hφ : ContDiffOn ℝ 1 φ (Set.Ioi 0)) (hψ : ContDiffOn ℝ 1 ψ (Set.Ioi 0))
    (hsφ : ∀ z, (0 < z ∧ z < δ) ∨ R < z → φ z = 0)
    (hsψ : ∀ z, (0 < z ∧ z < δ) ∨ R < z → ψ z = 0) :
    (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * φ z * (z * deriv ψ z))
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (-(z * deriv φ z) - (z - 3) / (1 + z) * φ z) * ψ z := by
  set u : ℝ → ℝ := fun y => (Work.Spaces.w y) ^ 2 * y * φ y with hu
  set u' : ℝ → ℝ := fun y => bcoef y * (Work.Spaces.w y) ^ 2 * φ y
      + (Work.Spaces.w y) ^ 2 * y * deriv φ y with hu'
  -- first derivatives of the two factors
  have hderiv_φ : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt φ (deriv φ z) z := by
    intro z hz
    have hd : DifferentiableAt ℝ φ z :=
      (hφ.differentiableOn_one).differentiableAt (isOpen_Ioi.mem_nhds hz)
    exact DifferentiableAt.hasDerivAt hd
  have hderiv_ψ : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt ψ (deriv ψ z) z := by
    intro z hz
    have hd : DifferentiableAt ℝ ψ z :=
      (hψ.differentiableOn_one).differentiableAt (isOpen_Ioi.mem_nhds hz)
    exact DifferentiableAt.hasDerivAt hd
  have hderiv_u : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt u (u' z) z := by
    intro z hz
    have hz0 : 0 < z := hz
    have h1 : HasDerivAt (fun y : ℝ => (Work.Spaces.w y) ^ 2 * y)
        (bcoef z * (Work.Spaces.w z) ^ 2) z := by
      have heq : (fun y : ℝ => (Work.Spaces.w y) ^ 2 * y)
          =ᶠ[𝓝 z] (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) := by
        filter_upwards with y
        ring
      rw [heq.hasDerivAt_iff]
      exact hasDerivAt_mul_w_sq z hz0
    exact h1.mul (hderiv_φ z hz)
  -- continuity of the pieces on the compact interval
  have hcont_w : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2 * z) (Set.Icc δ R) := by
    have hrat : ContinuousOn (fun z : ℝ => (1 + z) ^ 4 / z ^ 3) (Set.Icc δ R) := by
      refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
      intro z hz
      have hz0 : 0 < z := lt_of_lt_of_le hδ hz.1
      positivity
    refine hrat.congr (fun z hz => ?_)
    exact w_sq_mul_self z (ne_of_gt (lt_of_lt_of_le hδ hz.1))
  have hcont_bw : ContinuousOn (fun z : ℝ => bcoef z * (Work.Spaces.w z) ^ 2) (Set.Icc δ R) := by
    have hrat : ContinuousOn (fun z : ℝ => (z - 3) * (1 + z) ^ 3 / z ^ 4) (Set.Icc δ R) := by
      refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
      intro z hz
      have hz0 : 0 < z := lt_of_lt_of_le hδ hz.1
      positivity
    refine hrat.congr (fun z hz => ?_)
    exact bcoef_mul_w_sq z (ne_of_gt (lt_of_lt_of_le hδ hz.1))
  have hcont_φ : ContinuousOn φ (Set.Icc δ R) :=
    hφ.continuousOn.mono (fun z hz => lt_of_lt_of_le hδ hz.1)
  have hcont_ψ : ContinuousOn ψ (Set.Icc δ R) :=
    hψ.continuousOn.mono (fun z hz => lt_of_lt_of_le hδ hz.1)
  have hcont_ψ' : ContinuousOn (deriv ψ) (Set.Icc δ R) :=
    (hψ.continuousOn_deriv_of_isOpen isOpen_Ioi (le_refl 1)).mono
      (fun z hz => lt_of_lt_of_le hδ hz.1)
  have hcont_φ' : ContinuousOn (deriv φ) (Set.Icc δ R) :=
    (hφ.continuousOn_deriv_of_isOpen isOpen_Ioi (le_refl 1)).mono
      (fun z hz => lt_of_lt_of_le hδ hz.1)
  -- integrability of `u * ψ'` on `(0,∞)`
  have hIntF : IntegrableOn (fun z => u z * deriv ψ z) (Set.Ioi 0) := by
    have h1 : IntegrableOn (fun z => u z * deriv ψ z) (Set.Ioo 0 δ) := by
      refine MeasureTheory.integrableOn_zero.congr_fun (fun z hz => ?_) measurableSet_Ioo
      rw [show u z = (Work.Spaces.w z) ^ 2 * z * φ z from rfl, hsφ z (Or.inl hz)]
      ring
    have h2 : IntegrableOn (fun z => u z * deriv ψ z) (Set.Icc δ R) := by
      refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
      rw [show (fun z => u z * deriv ψ z)
          = fun z => ((Work.Spaces.w z) ^ 2 * z) * (φ z * deriv ψ z) from by
        funext z; simp only [u]; ring]
      exact hcont_w.mul (hcont_φ.mul hcont_ψ')
    have h3 : IntegrableOn (fun z => u z * deriv ψ z) (Set.Ioi R) := by
      refine MeasureTheory.integrableOn_zero.congr_fun (fun z hz => ?_) measurableSet_Ioi
      rw [show u z = (Work.Spaces.w z) ^ 2 * z * φ z from rfl, hsφ z (Or.inr hz)]
      ring
    have h4 := h1.union (h2.union h3)
    rwa [show Set.Ioo (0 : ℝ) δ ∪ (Set.Icc δ R ∪ Set.Ioi R) = Set.Ioi 0 from ?_] at h4
    ext z
    simp only [Set.mem_union, Set.mem_Ioo, Set.mem_Icc, Set.mem_Ioi]
    constructor
    · rintro (⟨h1, -⟩ | ⟨h2, -⟩ | h3) <;> linarith
    · intro hz
      rcases lt_or_ge z δ with h | h
      · exact Or.inl ⟨hz, h⟩
      · rcases le_or_gt z R with h' | h'
        · exact Or.inr (Or.inl ⟨h, h'⟩)
        · exact Or.inr (Or.inr h')
  -- integrability of `u' * ψ` on `(0,∞)`
  have hIntG : IntegrableOn (fun z => u' z * ψ z) (Set.Ioi 0) := by
    have h1 : IntegrableOn (fun z => u' z * ψ z) (Set.Ioo 0 δ) := by
      refine MeasureTheory.integrableOn_zero.congr_fun (fun z hz => ?_) measurableSet_Ioo
      rw [show u' z = bcoef z * (Work.Spaces.w z) ^ 2 * φ z
          + (Work.Spaces.w z) ^ 2 * z * deriv φ z from rfl,
        hsφ z (Or.inl hz), hsψ z (Or.inl hz)]
      ring
    have h2 : IntegrableOn (fun z => u' z * ψ z) (Set.Icc δ R) := by
      refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
      rw [show (fun z => u' z * ψ z)
          = fun z => (bcoef z * (Work.Spaces.w z) ^ 2) * (φ z * ψ z)
              + ((Work.Spaces.w z) ^ 2 * z) * (deriv φ z * ψ z) from by
        funext z; simp only [u']; ring]
      exact (hcont_bw.mul (hcont_φ.mul hcont_ψ)).add (hcont_w.mul (hcont_φ'.mul hcont_ψ))
    have h3 : IntegrableOn (fun z => u' z * ψ z) (Set.Ioi R) := by
      refine MeasureTheory.integrableOn_zero.congr_fun (fun z hz => ?_) measurableSet_Ioi
      rw [show u' z = bcoef z * (Work.Spaces.w z) ^ 2 * φ z
          + (Work.Spaces.w z) ^ 2 * z * deriv φ z from rfl,
        hsφ z (Or.inr hz), hsψ z (Or.inr hz)]
      ring
    have h4 := h1.union (h2.union h3)
    rwa [show Set.Ioo (0 : ℝ) δ ∪ (Set.Icc δ R ∪ Set.Ioi R) = Set.Ioi 0 from ?_] at h4
    ext z
    simp only [Set.mem_union, Set.mem_Ioo, Set.mem_Icc, Set.mem_Ioi]
    constructor
    · rintro (⟨h1, -⟩ | ⟨h2, -⟩ | h3) <;> linarith
    · intro hz
      rcases lt_or_ge z δ with h | h
      · exact Or.inl ⟨hz, h⟩
      · rcases le_or_gt z R with h' | h'
        · exact Or.inr (Or.inl ⟨h, h'⟩)
        · exact Or.inr (Or.inr h')
  -- the two boundary limits
  have hzero : Tendsto (fun z => u z * ψ z) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hev : (fun z => u z * ψ z) =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => (0 : ℝ)) := by
      filter_upwards [Ioo_mem_nhdsGT hδ] with z hz
      have hz0 : 0 < z := hz.1
      rw [show u z = (Work.Spaces.w z) ^ 2 * z * φ z from rfl, hsφ z (Or.inl ⟨hz0, hz.2⟩)]
      ring
    exact tendsto_const_nhds.congr' hev.symm
  have hinfty : Tendsto (fun z => u z * ψ z) atTop (𝓝 0) := by
    have hev : (fun z => u z * ψ z) =ᶠ[atTop] (fun _ => (0 : ℝ)) := by
      filter_upwards [eventually_gt_atTop R] with z hz
      rw [show u z = (Work.Spaces.w z) ^ 2 * z * φ z from rfl, hsφ z (Or.inr hz),
        hsψ z (Or.inr hz)]
      ring
    exact tendsto_const_nhds.congr' hev.symm
  -- integration by parts on `(0,∞)`
  have hIBP : (∫ z in Set.Ioi (0 : ℝ), u z * deriv ψ z)
      = - ∫ z in Set.Ioi (0 : ℝ), u' z * ψ z := by
    have h := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul (a := (0 : ℝ)) (a' := 0) (b' := 0)
      (u := u) (u' := u') (v := ψ) (v' := deriv ψ) hderiv_u hderiv_ψ hIntF hIntG hzero hinfty
    simpa using h
  -- back to set integrals over `Iz`
  have hIz : Work.Spaces.Iz = Set.Ici (0 : ℝ) := rfl
  rw [hIz, MeasureTheory.integral_Ici_eq_integral_Ioi,
    MeasureTheory.integral_Ici_eq_integral_Ioi]
  have hleft : (∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * φ z * (z * deriv ψ z))
      = ∫ z in Set.Ioi (0 : ℝ), u z * deriv ψ z := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
    simp only [u]
    ring
  have hright : (∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2
        * (-(z * deriv φ z) - (z - 3) / (1 + z) * φ z) * ψ z)
      = - ∫ z in Set.Ioi (0 : ℝ), u' z * ψ z := by
    rw [← MeasureTheory.integral_neg]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
    simp only [u', bcoef]
    ring
  rw [hleft, hright, hIBP]

end Work.FTS.EllipticEst.ThetaU
