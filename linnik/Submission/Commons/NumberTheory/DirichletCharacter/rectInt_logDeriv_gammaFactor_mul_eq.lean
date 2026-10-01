import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.chebyshevPsiChi_explicit_formula_mult

open Complex MeasureTheory intervalIntegral Filter
open scoped Real Topology BigOperators

namespace Commons.NumberTheory.DirichletCharacter

theorem rectInt_logDeriv_gammaFactor_mul_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    {z w : ℂ} (hzre : z.re < w.re) (hzim : z.im < w.im) (hz1 : -(1 : ℝ) < z.re)
    (h0in : z.re < 0 ∧ 0 < w.re ∧ z.im < 0 ∧ 0 < w.im) (hE : χ.Even) :
    Commons.NumberTheory.DirichletCharacter.rectInt z w
        (fun s => logDeriv (DirichletCharacter.gammaFactor χ) s * G s) =
      -(2 * (Real.pi : ℂ) * Complex.I) * G 0 := by
  set A : ℂ → ℂ := fun s => -(Complex.log (Real.pi : ℂ)) / 2 +
    Complex.digamma ((s + 2) / 2) / 2 with hAdef
  have hre_ge : ∀ s ∈ rectSet z w, -(1 : ℝ) < s.re := by
    intro s hs
    obtain ⟨hre, -⟩ := Complex.mem_reProdIm.mp hs
    rw [Set.uIcc_of_le (le_of_lt hzre)] at hre
    linarith [hre.1, hz1]
  have hgf : DirichletCharacter.gammaFactor χ = Complex.Gammaℝ := by
    funext s; exact hE.gammaFactor_def s
  rw [hgf]
  have hdig : DifferentiableOn ℂ (fun s : ℂ => Complex.digamma ((s + 2) / 2)) (rectSet z w) :=
    differentiableOn_digamma_shift (c := 2) (fun s hs => digamma_re_shift_two (hre_ge s hs))
  have hA : DifferentiableOn ℂ A (rectSet z w) := by
    rw [hAdef]
    exact DifferentiableOn.add (differentiableOn_const _) (hdig.div_const 2)
  have hGon : DifferentiableOn ℂ G (rectSet z w) := fun s _ => (hG s).differentiableWithinAt
  have hAG : DifferentiableOn ℂ (fun s : ℂ => A s * G s) (rectSet z w) := hA.mul hGon
  have hpoint : ∀ s ∈ rectBoundary z w,
      logDeriv Complex.Gammaℝ s * G s = A s * G s + (-1) * (G s / s) := by
    intro s hs
    have hsne : s ≠ 0 := ne_zero_of_mem_rectBoundary h0in.1 h0in.2.1 h0in.2.2.1 h0in.2.2.2 hs
    have hsre : -(1 : ℝ) < s.re := hre_ge s (rectBoundary_subset_rectSet hzre hzim hs)
    have h := logDeriv_Gammaℝ_add_inv hsne hsre
    rw [show s / 2 + 1 = (s + 2) / 2 by ring] at h
    have h' : logDeriv Complex.Gammaℝ s = A s - 1 / s := by
      rw [hAdef]; exact eq_sub_iff_add_eq.mpr h
    rw [h', div_eq_mul_inv, div_eq_mul_inv]
    ring
  have hcont_g : ContinuousOn (fun s : ℂ => (-1) * (G s / s)) {s : ℂ | s ≠ 0} :=
    continuousOn_const.mul
      (hG.continuous.continuousOn.div continuousOn_id (fun s hs => hs))
  obtain ⟨af1, af2, af3, af4⟩ := edgeIntegrable_of_continuousOn hAG.continuousOn
  obtain ⟨ag1, ag2, ag3, ag4⟩ :=
    edgeIntegrable_of_continuousOn_ne (u := 0) (by simpa using h0in) hcont_g
  have hcongr : rectInt z w (fun s => logDeriv Complex.Gammaℝ s * G s) =
      rectInt z w (fun s => A s * G s + (-1) * (G s / s)) := by
    apply rectInt_congr_boundary'
    intro s hs
    exact hpoint s hs
  rw [hcongr, rectInt_add'' af1 ag1 af2 ag2 af3 ag3 af4 ag4,
    rectInt_eq_zero_of_differentiableOn hAG,
    rectInt_const_mul' (-1) (fun s : ℂ => G s / s),
    rectInt_analytic_div_self hzre hzim h0in hGon]
  ring

end Commons.NumberTheory.DirichletCharacter
