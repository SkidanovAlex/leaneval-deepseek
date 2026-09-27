import Mathlib

/-!
# The Cayley transform: the unit disc is homeomorphic to the upper half plane

`cayley w = i (1 + w) / (1 - w)` maps the open unit disc onto the upper half plane, with inverse
`cayleyInv z = (z - i) / (z + i)`. This is used to transport Fatou's theorem (stated for bounded
holomorphic functions on the unit disc) to functions on the upper half plane, in the equichordal
point problem.
-/

noncomputable section

open Complex Metric Filter _root_.Topology

namespace Work.EQ

/-- The Cayley transform, as a function on `ℂ`. -/
def cayley (w : ℂ) : ℂ := Complex.I * (1 + w) / (1 - w)

/-- The inverse of the Cayley transform, as a function on `ℂ`. -/
def cayleyInv (z : ℂ) : ℂ := (z - Complex.I) / (z + Complex.I)

theorem one_sub_ne_zero {w : ℂ} (hw : ‖w‖ < 1) : (1 : ℂ) - w ≠ 0 := by
  intro h
  have hw' : w = 1 := (sub_eq_zero.mp h).symm
  rw [hw'] at hw
  simp at hw

theorem add_I_ne_zero {z : ℂ} (hz : 0 < z.im) : z + Complex.I ≠ 0 := by
  intro h
  have hz' : z = -Complex.I := add_eq_zero_iff_eq_neg.mp h
  rw [hz'] at hz
  simp at hz
  exact absurd hz (by norm_num)

/-- The Cayley transform maps the open unit disc into the upper half plane. -/
theorem cayley_im_pos {w : ℂ} (hw : ‖w‖ < 1) : 0 < (cayley w).im := by
  have h1 : (1 : ℂ) - w ≠ 0 := one_sub_ne_zero hw
  have hden : (0 : ℝ) < Complex.normSq (1 - w) := by
    rw [Complex.normSq_pos]; exact h1
  have hpos : (0 : ℝ) < 1 - Complex.normSq w := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg w, hw]
  have him : (cayley w).im = (1 - Complex.normSq w) / Complex.normSq (1 - w) := by
    rw [cayley, Complex.div_im, div_sub_div_same]
    congr 1
    simp only [Complex.I_mul, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
      Complex.sub_re, Complex.sub_im, Complex.normSq_apply]
    ring
  rw [him]
  exact div_pos hpos hden

/-- The forward formula is a left inverse of the backward one. -/
theorem cayleyInv_cayley {w : ℂ} (hw : (1 : ℂ) - w ≠ 0) : cayleyInv (cayley w) = w := by
  rw [cayleyInv, cayley, div_eq_iff (by
    rw [show Complex.I * (1 + w) / (1 - w) + Complex.I = 2 * Complex.I / (1 - w) by
      field_simp
      ring]
    exact div_ne_zero (by simp) hw)]
  field_simp
  ring

/-- The backward formula is a left inverse of the forward one. -/
theorem cayley_cayleyInv {z : ℂ} (hz : z + Complex.I ≠ 0) : cayley (cayleyInv z) = z := by
  rw [cayley, cayleyInv, div_eq_iff (by
    rw [show (1 : ℂ) - (z - Complex.I) / (z + Complex.I) = 2 * Complex.I / (z + Complex.I) by
      field_simp
      ring]
    exact div_ne_zero (by simp) hz)]
  field_simp
  ring

/-- `cayleyInv` maps the upper half plane into the open unit disc. -/
theorem norm_cayleyInv_lt_one {z : ℂ} (hz : 0 < z.im) : ‖cayleyInv z‖ < 1 := by
  have h1 : z + Complex.I ≠ 0 := add_I_ne_zero hz
  have hb : 0 < ‖z + Complex.I‖ := norm_pos_iff.mpr h1
  have hsq : Complex.normSq (z - Complex.I) < Complex.normSq (z + Complex.I) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.I_re, Complex.I_im]
    nlinarith [hz]
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hsq
  have hlt : ‖z - Complex.I‖ < ‖z + Complex.I‖ := by
    nlinarith [norm_nonneg (z - Complex.I), norm_nonneg (z + Complex.I),
      sq_nonneg (‖z - Complex.I‖ - ‖z + Complex.I‖)]
  rw [cayleyInv, norm_div, div_lt_one hb]
  exact hlt

theorem continuousOn_cayley : ContinuousOn cayley (Metric.ball (0 : ℂ) 1) := by
  show ContinuousOn (fun w : ℂ => Complex.I * (1 + w) / (1 - w)) _
  refine ContinuousOn.div ?_ ?_ ?_
  · exact continuousOn_const.mul (continuousOn_const.add continuousOn_id)
  · exact continuousOn_const.sub continuousOn_id
  · intro w hw
    exact one_sub_ne_zero (by simpa [Metric.mem_ball, dist_eq_norm] using hw)

theorem continuousOn_cayleyInv : ContinuousOn cayleyInv {z : ℂ | 0 < z.im} := by
  show ContinuousOn (fun z : ℂ => (z - Complex.I) / (z + Complex.I)) _
  refine ContinuousOn.div ?_ ?_ ?_
  · exact continuousOn_id.sub continuousOn_const
  · exact continuousOn_id.add continuousOn_const
  · intro z hz
    exact add_I_ne_zero hz

/-- **The Cayley transform as a homeomorphism** from the open unit disc onto the upper half
plane, with the two explicit formulas. -/
theorem cayley_homeomorph_uhp :
    ∃ e : ↥(Metric.ball (0 : ℂ) 1) ≃ₜ UpperHalfPlane,
      (∀ w : ↥(Metric.ball (0 : ℂ) 1), (e w : ℂ) = Complex.I * (1 + (w : ℂ)) / (1 - (w : ℂ))) ∧
      (∀ z : UpperHalfPlane, (e.symm z : ℂ) = ((z : ℂ) - Complex.I) / ((z : ℂ) + Complex.I)) := by
  have hball : ∀ w : ↥(Metric.ball (0 : ℂ) 1), ‖(w : ℂ)‖ < 1 := fun w => by
    have h := w.2
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at h
    exact h
  let f : ↥(Metric.ball (0 : ℂ) 1) → UpperHalfPlane :=
    fun w => ⟨cayley w, cayley_im_pos (hball w)⟩
  let g : UpperHalfPlane → ↥(Metric.ball (0 : ℂ) 1) :=
    fun z => ⟨cayleyInv z, by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]
      exact norm_cayleyInv_lt_one z.2⟩
  have hfg : Function.LeftInverse g f := fun w =>
    Subtype.ext (cayleyInv_cayley (one_sub_ne_zero (hball w)))
  have hgf : Function.RightInverse g f := fun z =>
    UpperHalfPlane.coe_injective (cayley_cayleyInv (add_I_ne_zero z.2))
  have hfc : Continuous f := by
    rw [UpperHalfPlane.isEmbedding_coe.continuous_iff]
    exact continuousOn_cayley.comp_continuous continuous_subtype_val (fun w => w.2)
  have hgc : Continuous g := by
    refine Continuous.subtype_mk ?_ _
    exact continuousOn_cayleyInv.comp_continuous UpperHalfPlane.continuous_coe (fun z => z.2)
  let e : ↥(Metric.ball (0 : ℂ) 1) ≃ UpperHalfPlane :=
    { toFun := f, invFun := g, left_inv := hfg, right_inv := hgf }
  refine ⟨Homeomorph.mk e hfc hgc, ?_, ?_⟩
  · intro w
    rfl
  · intro z
    rfl

end Work.EQ
