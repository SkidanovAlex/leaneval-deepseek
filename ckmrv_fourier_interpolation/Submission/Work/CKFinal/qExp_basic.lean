import Mathlib
import Submission.Work.CKFinal.EngineDefs

namespace Work.CKFinal

open UpperHalfPlane

/-- The extension `pext g` of a `1`-periodic function on `ℍ` is again `1`-periodic. -/
lemma pext_periodic (g : UpperHalfPlane → ℂ)
    (hper : ∀ τ : UpperHalfPlane, g ((1 : ℝ) +ᵥ τ) = g τ) :
    Function.Periodic (pext g) 1 := by
  intro z
  by_cases hz : 0 < z.im
  · have hz1 : 0 < (z + 1).im := by simpa using hz
    rw [pext, pext, dif_pos hz1, dif_pos hz]
    have hpt : (⟨z + 1, hz1⟩ : UpperHalfPlane) = (1 : ℝ) +ᵥ (⟨z, hz⟩ : UpperHalfPlane) := by
      ext
      simp [UpperHalfPlane.coe_vadd]
      ring
    rw [hpt, hper]
  · have hz1 : ¬ (0 < (z + 1).im) := by simpa using hz
    rw [pext, pext, dif_neg hz1, dif_neg hz]

/-- On the upper half plane the extension `pext g` is holomorphic whenever `g` is. -/
lemma pext_differentiableAt (g : UpperHalfPlane → ℂ)
    (hhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) g) :
    ∀ (z : ℂ) (_hz : 0 < z.im), DifferentiableAt ℂ (pext g) z := by
  intro z hz
  have hg : DifferentiableAt ℂ (g ∘ UpperHalfPlane.ofComplex) z :=
    UpperHalfPlane.mdifferentiableAt_iff.mp (hhol ⟨z, hz⟩)
  refine hg.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz] with w hw
  rw [pext, dif_pos hw, UpperHalfPlane.comp_ofComplex_of_im_pos]

/-- For `q` in the punctured open unit disc, `invQParam 1 q` lies in the upper half plane. -/
lemma invQParam_one_im_pos (q : ℂ) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    0 < (Function.Periodic.invQParam 1 q).im := by
  rw [Function.Periodic.im_invQParam]
  have hlog : Real.log ‖q‖ < 0 := Real.log_neg hq0 hq1
  have hpi : (0 : ℝ) < 1 / (2 * Real.pi) := by positivity
  have h1 : (1 : ℝ) / (2 * Real.pi) * Real.log ‖q‖ < 0 := mul_neg_of_pos_of_neg hpi hlog
  have h2 : (-1 : ℝ) / (2 * Real.pi) = -(1 / (2 * Real.pi)) := by ring
  rw [h2]
  linarith

theorem qExp_basic (g : UpperHalfPlane → ℂ)
    (hper : ∀ τ : UpperHalfPlane, g ((1 : ℝ) +ᵥ τ) = g τ)
    (hhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) g) :
    Function.Periodic (Work.CKFinal.pext g) 1 ∧
    (∀ (z : ℂ) (hz : 0 < z.im), Work.CKFinal.pext g z = g ⟨z, hz⟩) ∧
    (∀ (z : ℂ) (hz : 0 < z.im), DifferentiableAt ℂ (Work.CKFinal.pext g) z) ∧
    (∀ τ : UpperHalfPlane, Work.CKFinal.qExp g (Function.Periodic.qParam 1 (τ : ℂ)) = g τ) ∧
    (∀ q : ℂ, 0 < ‖q‖ → ‖q‖ < 1 → DifferentiableAt ℂ (Work.CKFinal.qExp g) q) := by
  have hpext_per : Function.Periodic (pext g) 1 := pext_periodic g hper
  have hpext_apply : ∀ (z : ℂ) (hz : 0 < z.im), pext g z = g ⟨z, hz⟩ := by
    intro z hz
    rw [pext, dif_pos hz]
  have hpext_diff : ∀ (z : ℂ) (hz : 0 < z.im), DifferentiableAt ℂ (pext g) z :=
    pext_differentiableAt g hhol
  have hqexp_val : ∀ τ : UpperHalfPlane, qExp g (Function.Periodic.qParam 1 (τ : ℂ)) = g τ := by
    intro τ
    have h := Function.Periodic.eq_cuspFunction (h := 1) one_ne_zero hpext_per (τ : ℂ)
    rw [pext, dif_pos τ.2] at h
    rw [UpperHalfPlane.mk_coe τ] at h
    simpa [qExp] using h
  have hqexp_diff : ∀ q : ℂ, 0 < ‖q‖ → ‖q‖ < 1 → DifferentiableAt ℂ (qExp g) q := by
    intro q hq0 hq1
    have hqne : q ≠ 0 := by
      intro hq
      rw [hq, norm_zero] at hq0
      exact lt_irrefl 0 hq0
    have hz : 0 < (Function.Periodic.invQParam 1 q).im := invQParam_one_im_pos q hq0 hq1
    have hd : DifferentiableAt ℂ (Function.Periodic.cuspFunction 1 (pext g))
        (Function.Periodic.qParam 1 (Function.Periodic.invQParam 1 q)) :=
      Function.Periodic.differentiableAt_cuspFunction (h := 1) (f := pext g) one_ne_zero
        hpext_per (hpext_diff _ hz)
    rw [Function.Periodic.qParam_right_inv (h := 1) one_ne_zero hqne] at hd
    simpa [qExp] using hd
  exact ⟨hpext_per, hpext_apply, hpext_diff, hqexp_val, hqexp_diff⟩

end Work.CKFinal
