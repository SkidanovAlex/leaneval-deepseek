import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.diskZeroCount_two_half
import Submission.Commons.Analysis.Complex.circleLogDerivContour_bound
import Submission.Commons.Analysis.Complex.rectZeroCount_boundary_le
import Submission.Commons.NumberTheory.DirichletCharacter.zerosInStrip
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_two_tight
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_neg_one_tight
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_fe
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_conj
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_two_le
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_critical_poly
import Submission.Commons.NumberTheory.DirichletCharacter.window_le_rectSum
import Submission.Commons.NumberTheory.DirichletCharacter.finite_zeroHeights_window
import Submission.Commons.NumberTheory.Linnik.completedL_zeroCount

open Complex Metric
open scoped Real

noncomputable section

namespace Commons.Analysis.Complex

/-- **Imaginary part of the rectangular boundary integral.**  Writing out
`rectB h z w = (A - B) + i·C - i·D` with `A,B` the two horizontal and `C,D` the two vertical
side integrals, its imaginary part is `Im A - Im B + Re C - Re D`, and interval integration
commutes with `Im`/`Re`. -/
lemma rectB_im_eq {h : ℂ → ℂ} {z w : ℂ}
    (hb : IntervalIntegrable (fun x : ℝ => h ((x : ℂ) + (z.im : ℂ) * Complex.I)) MeasureTheory.volume z.re w.re)
    (ht : IntervalIntegrable (fun x : ℝ => h ((x : ℂ) + (w.im : ℂ) * Complex.I)) MeasureTheory.volume z.re w.re)
    (hr : IntervalIntegrable (fun y : ℝ => h ((w.re : ℂ) + (y : ℂ) * Complex.I)) MeasureTheory.volume z.im w.im)
    (hl : IntervalIntegrable (fun y : ℝ => h ((z.re : ℂ) + (y : ℂ) * Complex.I)) MeasureTheory.volume z.im w.im) :
    (rectB h z w).im =
      (∫ x : ℝ in z.re..w.re, (h ((x : ℂ) + (z.im : ℂ) * Complex.I)).im)
      - (∫ x : ℝ in z.re..w.re, (h ((x : ℂ) + (w.im : ℂ) * Complex.I)).im)
      + (∫ y : ℝ in z.im..w.im, (h ((w.re : ℂ) + (y : ℂ) * Complex.I)).re)
      - (∫ y : ℝ in z.im..w.im, (h ((z.re : ℂ) + (y : ℂ) * Complex.I)).re) := by
  have h1 : (∫ x : ℝ in z.re..w.re, h ((x : ℂ) + (z.im : ℂ) * Complex.I)).im
      = ∫ x : ℝ in z.re..w.re, (h ((x : ℂ) + (z.im : ℂ) * Complex.I)).im := by
    have := Complex.imCLM.intervalIntegral_comp_comm hb
    simpa [Complex.imCLM_apply] using this.symm
  have h2 : (∫ x : ℝ in z.re..w.re, h ((x : ℂ) + (w.im : ℂ) * Complex.I)).im
      = ∫ x : ℝ in z.re..w.re, (h ((x : ℂ) + (w.im : ℂ) * Complex.I)).im := by
    have := Complex.imCLM.intervalIntegral_comp_comm ht
    simpa [Complex.imCLM_apply] using this.symm
  have h3 : (∫ y : ℝ in z.im..w.im, h ((w.re : ℂ) + (y : ℂ) * Complex.I)).re
      = ∫ y : ℝ in z.im..w.im, (h ((w.re : ℂ) + (y : ℂ) * Complex.I)).re := by
    have := Complex.reCLM.intervalIntegral_comp_comm hr
    simpa [Complex.reCLM_apply] using this.symm
  have h4 : (∫ y : ℝ in z.im..w.im, h ((z.re : ℂ) + (y : ℂ) * Complex.I)).re
      = ∫ y : ℝ in z.im..w.im, (h ((z.re : ℂ) + (y : ℂ) * Complex.I)).re := by
    have := Complex.reCLM.intervalIntegral_comp_comm hl
    simpa [Complex.reCLM_apply] using this.symm
  rw [rectB]
  simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, sub_zero, add_zero]
  rw [h1, h2, h3, h4]
  ring


/-- **Signed (imaginary/real-part) argument principle on a rectangle.**

Same hypotheses as `rectB_decomp_geom`: `logDeriv f` decomposes on `ball 0 R` into the
divisor sum over `S` (with coefficients `d`) plus `logDeriv g` with `g` zero-free there, and
`f` has no zero on the boundary of the rectangle with corners `z,w`.  Then

`Σᶠ_u d(u)·[u strictly inside] ≤ (1/2π)·( ∫_bottom |Im g| + ∫_top |Im g| + ∫_right |Re g| + ∫_left |Re g| )`.

This is the *signed* refinement of `rectZeroCount_boundary_le` (which bounds the same count by
the four integrals of `‖g‖`): the vertical sides only pay their *real* parts, which on the
critical line are known exactly. -/
lemma rectZeroCount_imag {f g : ℂ → ℂ} {z w : ℂ} {R : ℝ} (S : Finset ℂ) {d : ℂ → ℤ}
    (hzre : z.re < w.re) (hzim : z.im < w.im)
    (hdec : ∀ s : ℂ, s ∈ Metric.ball (0 : ℂ) R → f s ≠ 0 →
      logDeriv f s = (∑ᶠ u : ℂ, (((d u : ℤ) : ℂ) * ((s - u)⁻¹))) + logDeriv g s)
    (hS_cov : ∀ u : ℂ, d u ≠ 0 → u ∈ S)
    (hball : ∀ s : ℂ, z.re ≤ s.re → s.re ≤ w.re → z.im ≤ s.im → s.im ≤ w.im →
      s ∈ Metric.ball (0 : ℂ) R)
    (hzero : ∀ u : ℂ, u ∈ S → f u = 0)
    (hfne : ∀ s : ℂ, (s.re = z.re ∨ s.re = w.re ∨ s.im = z.im ∨ s.im = w.im) →
      z.re ≤ s.re → s.re ≤ w.re → z.im ≤ s.im → s.im ≤ w.im → f s ≠ 0)
    (hg_an : AnalyticOnNhd ℂ (fun s : ℂ => logDeriv g s) (Metric.ball (0 : ℂ) R))
    (hb : IntervalIntegrable (fun x : ℝ => logDeriv f ((x : ℂ) + (z.im : ℂ) * Complex.I))
      MeasureTheory.volume z.re w.re)
    (ht : IntervalIntegrable (fun x : ℝ => logDeriv f ((x : ℂ) + (w.im : ℂ) * Complex.I))
      MeasureTheory.volume z.re w.re)
    (hr : IntervalIntegrable (fun y : ℝ => logDeriv f ((w.re : ℂ) + (y : ℂ) * Complex.I))
      MeasureTheory.volume z.im w.im)
    (hl : IntervalIntegrable (fun y : ℝ => logDeriv f ((z.re : ℂ) + (y : ℂ) * Complex.I))
      MeasureTheory.volume z.im w.im)
    (hb' : IntervalIntegrable
      (fun x : ℝ => (logDeriv f ((x : ℂ) + (z.im : ℂ) * Complex.I)).im)
      MeasureTheory.volume z.re w.re)
    (ht' : IntervalIntegrable
      (fun x : ℝ => (logDeriv f ((x : ℂ) + (w.im : ℂ) * Complex.I)).im)
      MeasureTheory.volume z.re w.re)
    (hr' : IntervalIntegrable
      (fun y : ℝ => (logDeriv f ((w.re : ℂ) + (y : ℂ) * Complex.I)).re)
      MeasureTheory.volume z.im w.im)
    (hl' : IntervalIntegrable
      (fun y : ℝ => (logDeriv f ((z.re : ℂ) + (y : ℂ) * Complex.I)).re)
      MeasureTheory.volume z.im w.im) :
    (∑ᶠ u : ℂ, (((d u : ℤ) : ℝ) *
        (if z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im then 1 else 0)))
      ≤ (1 / (2 * Real.pi)) *
        ((∫ x : ℝ in z.re..w.re, ‖(logDeriv f ((x : ℂ) + (z.im : ℂ) * Complex.I)).im‖)
         + (∫ x : ℝ in z.re..w.re, ‖(logDeriv f ((x : ℂ) + (w.im : ℂ) * Complex.I)).im‖)
         + (∫ y : ℝ in z.im..w.im, ‖(logDeriv f ((w.re : ℂ) + (y : ℂ) * Complex.I)).re‖)
         + (∫ y : ℝ in z.im..w.im, ‖(logDeriv f ((z.re : ℂ) + (y : ℂ) * Complex.I)).re‖)) := by
  classical
  let INS : ℂ → Prop := fun u => z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im
  let L : ℝ := ∑ u ∈ S, (((d u : ℤ) : ℝ) * (if INS u then 1 else 0))
  have hgeom := rectB_decomp_geom (f := f) (g := g) (z := z) (w := w) (R := R) S (d := d)
    hzre hzim hdec hS_cov hball hzero hfne hg_an
  -- classification of the support points
  have hclass : ∀ u : ℂ, u ∈ S → INS u ∨
      (u.re < z.re ∨ w.re < u.re ∨ u.im < z.im ∨ w.im < u.im) := by
    intro u hu
    have hfu0 : f u = 0 := hzero u hu
    by_cases huCl : z.re ≤ u.re ∧ u.re ≤ w.re ∧ z.im ≤ u.im ∧ u.im ≤ w.im
    · have hnb : ¬(u.re = z.re ∨ u.re = w.re ∨ u.im = z.im ∨ u.im = w.im) := by
        intro hb
        exact (hfne u hb huCl.1 huCl.2.1 huCl.2.2.1 huCl.2.2.2) hfu0
      left
      refine ⟨lt_of_le_of_ne huCl.1 (fun h => hnb (Or.inl h.symm)),
        lt_of_le_of_ne huCl.2.1 (fun h => hnb (Or.inr (Or.inl h))),
        lt_of_le_of_ne huCl.2.2.1 (fun h => hnb (Or.inr (Or.inr (Or.inl h.symm)))),
        lt_of_le_of_ne huCl.2.2.2 (fun h => hnb (Or.inr (Or.inr (Or.inr h))))⟩
    · right
      by_cases h1 : u.re < z.re
      · exact Or.inl h1
      · by_cases h2 : w.re < u.re
        · exact Or.inr (Or.inl h2)
        · by_cases h3 : u.im < z.im
          · exact Or.inr (Or.inr (Or.inl h3))
          · by_cases h4 : w.im < u.im
            · exact Or.inr (Or.inr (Or.inr h4))
            · exfalso
              exact huCl ⟨le_of_not_gt h1, le_of_not_gt h2, le_of_not_gt h3, le_of_not_gt h4⟩
  -- residue evaluation of each summand
  have hres : ∀ u ∈ S, rectB (fun s : ℂ => (s - u)⁻¹) z w =
      if INS u then (2 : ℂ) * (Real.pi : ℂ) * Complex.I else 0 := by
    intro u hu
    rcases hclass u hu with hin | hout
    · rw [if_pos hin, rectB_sub_inv_inside hzre hzim hin]
    · rw [if_neg (fun h => by
        rcases h with ⟨h1,h2,h3,h4⟩
        rcases hout with h5 | h5 | h5 | h5
        · exact absurd h5 (not_lt_of_ge h1.le)
        · exact absurd h5 (not_lt_of_ge h2.le)
        · exact absurd h5 (not_lt_of_ge h3.le)
        · exact absurd h5 (not_lt_of_ge h4.le)), rectB_sub_inv_outside hzre hzim hout]
  -- the exact residue identity
  have hLc : (L : ℂ) = ∑ u ∈ S, (((d u : ℤ) : ℂ) * (if INS u then 1 else 0)) := by
    dsimp only [L]
    push_cast
    apply Finset.sum_congr rfl
    intro u _
    by_cases h : INS u <;> simp [h]
  have hterm : ∀ u ∈ S, (((d u : ℤ) : ℂ) * rectB (fun s : ℂ => (s - u)⁻¹) z w)
      = (((d u : ℤ) : ℂ) * (if INS u then 1 else 0)) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by
    intro u hu
    rw [hres u hu]
    by_cases h : INS u
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]; ring
  have hident : rectB (logDeriv f) z w = (L : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by
    rw [hgeom, Finset.sum_congr rfl hterm, ← Finset.sum_mul, hLc]
  have hCre : ((2 : ℂ) * (Real.pi : ℂ) * Complex.I).re = 0 := by
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have hCim : ((2 : ℂ) * (Real.pi : ℂ) * Complex.I).im = 2 * Real.pi := by
    simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have him : (rectB (logDeriv f) z w).im = 2 * Real.pi * L := by
    rw [hident, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hCre, hCim]
    ring
  -- the signed side decomposition
  have hside := rectB_im_eq (h := logDeriv f) (z := z) (w := w) hb ht hr hl
  -- bound the four signed side integrals
  have hbnd : 2 * Real.pi * L ≤
      (∫ x : ℝ in z.re..w.re, ‖(logDeriv f ((x : ℂ) + (z.im : ℂ) * Complex.I)).im‖)
      + (∫ x : ℝ in z.re..w.re, ‖(logDeriv f ((x : ℂ) + (w.im : ℂ) * Complex.I)).im‖)
      + (∫ y : ℝ in z.im..w.im, ‖(logDeriv f ((w.re : ℂ) + (y : ℂ) * Complex.I)).re‖)
      + (∫ y : ℝ in z.im..w.im, ‖(logDeriv f ((z.re : ℂ) + (y : ℂ) * Complex.I)).re‖) := by
    have e1 : (∫ x : ℝ in z.re..w.re, (logDeriv f ((x : ℂ) + (z.im : ℂ) * Complex.I)).im)
        ≤ ∫ x : ℝ in z.re..w.re, ‖(logDeriv f ((x : ℂ) + (z.im : ℂ) * Complex.I)).im‖ :=
      intervalIntegral.integral_mono_on (by linarith) (hb') (hb'.norm)
        (fun x _ => le_abs_self _)
    have e2 : (∫ x : ℝ in z.re..w.re, (logDeriv f ((x : ℂ) + (w.im : ℂ) * Complex.I)).im)
        ≤ ∫ x : ℝ in z.re..w.re, ‖(logDeriv f ((x : ℂ) + (w.im : ℂ) * Complex.I)).im‖ :=
      intervalIntegral.integral_mono_on (by linarith) (ht') (ht'.norm)
        (fun x _ => le_abs_self _)
    have e3 : (∫ y : ℝ in z.im..w.im, (logDeriv f ((w.re : ℂ) + (y : ℂ) * Complex.I)).re)
        ≤ ∫ y : ℝ in z.im..w.im, ‖(logDeriv f ((w.re : ℂ) + (y : ℂ) * Complex.I)).re‖ :=
      intervalIntegral.integral_mono_on (by linarith) (hr') (hr'.norm)
        (fun x _ => le_abs_self _)
    have e4 : (∫ y : ℝ in z.im..w.im, (logDeriv f ((z.re : ℂ) + (y : ℂ) * Complex.I)).re)
        ≤ ∫ y : ℝ in z.im..w.im, ‖(logDeriv f ((z.re : ℂ) + (y : ℂ) * Complex.I)).re‖ :=
      intervalIntegral.integral_mono_on (by linarith) (hl') (hl'.norm)
        (fun x _ => le_abs_self _)
    have hne2 : -(∫ x : ℝ in z.re..w.re, (logDeriv f ((x : ℂ) + (w.im : ℂ) * Complex.I)).im)
        ≤ ∫ x : ℝ in z.re..w.re, ‖(logDeriv f ((x : ℂ) + (w.im : ℂ) * Complex.I)).im‖ := by
      have : -(∫ x : ℝ in z.re..w.re, (logDeriv f ((x : ℂ) + (w.im : ℂ) * Complex.I)).im)
          = ∫ x : ℝ in z.re..w.re, -(logDeriv f ((x : ℂ) + (w.im : ℂ) * Complex.I)).im := by
        rw [intervalIntegral.integral_neg]
      rw [this]
      exact intervalIntegral.integral_mono_on (by linarith) (ht'.neg) (ht'.norm)
        (fun x _ => neg_le_abs _)
    have hne4 : -(∫ y : ℝ in z.im..w.im, (logDeriv f ((z.re : ℂ) + (y : ℂ) * Complex.I)).re)
        ≤ ∫ y : ℝ in z.im..w.im, ‖(logDeriv f ((z.re : ℂ) + (y : ℂ) * Complex.I)).re‖ := by
      have : -(∫ y : ℝ in z.im..w.im, (logDeriv f ((z.re : ℂ) + (y : ℂ) * Complex.I)).re)
          = ∫ y : ℝ in z.im..w.im, -(logDeriv f ((z.re : ℂ) + (y : ℂ) * Complex.I)).re := by
        rw [intervalIntegral.integral_neg]
      rw [this]
      exact intervalIntegral.integral_mono_on (by linarith) (hl'.neg) (hl'.norm)
        (fun x _ => neg_le_abs _)
    have := hside
    rw [him] at this
    rw [this]
    linarith
  -- finish: divide by 2π and identify the finsum with L
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hfinsum : (∑ᶠ u : ℂ, (((d u : ℤ) : ℝ) *
      (if z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im then 1 else 0)))
      = ∑ u ∈ S, (((d u : ℤ) : ℝ) * (if INS u then 1 else 0)) := by
    rw [finsum_eq_sum_of_support_subset
      (fun u : ℂ => (((d u : ℤ) : ℝ) * (if INS u then 1 else 0))) (s := S)]
    intro u hu
    have hdu : d u ≠ 0 := by
      intro hd0
      apply hu
      simp [hd0]
    exact hS_cov u hdu
  rw [hfinsum]
  have : ∑ u ∈ S, (((d u : ℤ) : ℝ) * (if INS u then 1 else 0))
      ≤ (1 / (2 * Real.pi)) *
        ((∫ x : ℝ in z.re..w.re, ‖(logDeriv f ((x : ℂ) + (z.im : ℂ) * Complex.I)).im‖)
         + (∫ x : ℝ in z.re..w.re, ‖(logDeriv f ((x : ℂ) + (w.im : ℂ) * Complex.I)).im‖)
         + (∫ y : ℝ in z.im..w.im, ‖(logDeriv f ((w.re : ℂ) + (y : ℂ) * Complex.I)).re‖)
         + (∫ y : ℝ in z.im..w.im, ‖(logDeriv f ((z.re : ℂ) + (y : ℂ) * Complex.I)).re‖)) := by
    have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
    have h3 : (1 / (2 * Real.pi)) *
        ((∫ x : ℝ in z.re..w.re, ‖(logDeriv f ((x : ℂ) + (z.im : ℂ) * Complex.I)).im‖)
         + (∫ x : ℝ in z.re..w.re, ‖(logDeriv f ((x : ℂ) + (w.im : ℂ) * Complex.I)).im‖)
         + (∫ y : ℝ in z.im..w.im, ‖(logDeriv f ((w.re : ℂ) + (y : ℂ) * Complex.I)).re‖)
         + (∫ y : ℝ in z.im..w.im, ‖(logDeriv f ((z.re : ℂ) + (y : ℂ) * Complex.I)).re‖))
        = ((∫ x : ℝ in z.re..w.re, ‖(logDeriv f ((x : ℂ) + (z.im : ℂ) * Complex.I)).im‖)
         + (∫ x : ℝ in z.re..w.re, ‖(logDeriv f ((x : ℂ) + (w.im : ℂ) * Complex.I)).im‖)
         + (∫ y : ℝ in z.im..w.im, ‖(logDeriv f ((w.re : ℂ) + (y : ℂ) * Complex.I)).re‖)
         + (∫ y : ℝ in z.im..w.im, ‖(logDeriv f ((z.re : ℂ) + (y : ℂ) * Complex.I)).re‖))
          / (2 * Real.pi) := by ring
    rw [h3, le_div_iff₀ hpi]
    nlinarith [hbnd]
  exact this


/-- **Signed argument principle on a rectangle, with the divisor factorisation supplied
internally.**  This is the exact counterpart of `rectZeroCount_boundary_le` in which the two
horizontal sides are bounded through `|Im (logDeriv f)|` and the two vertical sides through
`|Re (logDeriv f)|` — so a vertical side lying on the critical line (where the real part of
`Λ′/Λ` is known exactly) is not penalised by the unknown imaginary part. -/
theorem rectZeroCount_imag_of {f : ℂ → ℂ} {z w : ℂ} {R : ℝ}
    (hfdiff : Differentiable ℂ f) (hRpos : 0 < R) (hzre : z.re < w.re) (hzim : z.im < w.im)
    (hf0 : f 0 ≠ 0)
    (hrect : ∀ s : ℂ, z.re ≤ s.re → s.re ≤ w.re → z.im ≤ s.im → s.im ≤ w.im → ‖s‖ < R)
    (hfne : ∀ s : ℂ, (s.re = z.re ∨ s.re = w.re ∨ s.im = z.im ∨ s.im = w.im) →
      z.re ≤ s.re → s.re ≤ w.re → z.im ≤ s.im → s.im ≤ w.im → f s ≠ 0)
    (hb : IntervalIntegrable (fun x : ℝ => logDeriv f ((x : ℂ) + (z.im : ℂ) * Complex.I))
      MeasureTheory.volume z.re w.re)
    (ht : IntervalIntegrable (fun x : ℝ => logDeriv f ((x : ℂ) + (w.im : ℂ) * Complex.I))
      MeasureTheory.volume z.re w.re)
    (hr : IntervalIntegrable (fun y : ℝ => logDeriv f ((w.re : ℂ) + (y : ℂ) * Complex.I))
      MeasureTheory.volume z.im w.im)
    (hl : IntervalIntegrable (fun y : ℝ => logDeriv f ((z.re : ℂ) + (y : ℂ) * Complex.I))
      MeasureTheory.volume z.im w.im)
    (hb' : IntervalIntegrable
      (fun x : ℝ => (logDeriv f ((x : ℂ) + (z.im : ℂ) * Complex.I)).im)
      MeasureTheory.volume z.re w.re)
    (ht' : IntervalIntegrable
      (fun x : ℝ => (logDeriv f ((x : ℂ) + (w.im : ℂ) * Complex.I)).im)
      MeasureTheory.volume z.re w.re)
    (hr' : IntervalIntegrable
      (fun y : ℝ => (logDeriv f ((w.re : ℂ) + (y : ℂ) * Complex.I)).re)
      MeasureTheory.volume z.im w.im)
    (hl' : IntervalIntegrable
      (fun y : ℝ => (logDeriv f ((z.re : ℂ) + (y : ℂ) * Complex.I)).re)
      MeasureTheory.volume z.im w.im) :
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) R)) u : ℤ) : ℝ) *
        (if z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im then 1 else 0))
      ≤ (1 / (2 * Real.pi)) *
        ((∫ x : ℝ in z.re..w.re, ‖(logDeriv f ((x : ℂ) + (z.im : ℂ) * Complex.I)).im‖)
         + (∫ x : ℝ in z.re..w.re, ‖(logDeriv f ((x : ℂ) + (w.im : ℂ) * Complex.I)).im‖)
         + (∫ y : ℝ in z.im..w.im, ‖(logDeriv f ((w.re : ℂ) + (y : ℂ) * Complex.I)).re‖)
         + (∫ y : ℝ in z.im..w.im, ‖(logDeriv f ((z.re : ℂ) + (y : ℂ) * Complex.I)).re‖)) := by
  classical
  let d : ℂ → ℤ := fun u => (MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) R)) u
  have hfB : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R) :=
    fun z _ => hfdiff.analyticAt z
  have hord : ∀ s : ℂ, s ∈ Metric.closedBall (0 : ℂ) R → meromorphicOrderAt f s ≠ ⊤ :=
    order_ne_top_on_closedBall hRpos.le hfB hf0
  have hsupp0 : (MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) R)).support.Finite :=
    MeromorphicOn.divisor_support_finite_of_subset (f := f) (V := Metric.closedBall (0 : ℂ) R)
      hfB.meromorphicOn (isCompact_closedBall (0 : ℂ) R) (by simp)
  rcases factor_pointwise (U := Metric.closedBall (0 : ℂ) R) hfB.meromorphicOn hord hsupp0 hfB with
    ⟨g, hg_an_cb, hg_nz_cb, hfac⟩
  have hsuppd : (Function.support d).Finite := by
    dsimp [d]
    exact MeromorphicOn.divisor_support_finite_of_subset (f := f)
      (V := Metric.closedBall (0 : ℂ) R) (U := Metric.closedBall (0 : ℂ) R) hfB.meromorphicOn
      (isCompact_closedBall (0 : ℂ) R) (by intro z hz; exact hz)
  let S : Finset ℂ := hsuppd.toFinset
  have hS_cov : ∀ u : ℂ, d u ≠ 0 → u ∈ S := by
    intro u hu
    dsimp [S]
    exact (hsuppd.mem_toFinset).2 hu
  have hzero : ∀ u : ℂ, u ∈ S → f u = 0 := by
    intro u hu
    have hdu : d u ≠ 0 := by
      have huS : u ∈ (Function.support d) := (hsuppd.mem_toFinset).1 (by simpa [S] using hu)
      simpa using huS
    exact divisor_ne_zero_imp_eq_zero_of_analyticOnNhd hfB (by simpa [d] using hdu)
  have hball : ∀ s : ℂ, z.re ≤ s.re → s.re ≤ w.re → z.im ≤ s.im → s.im ≤ w.im →
      s ∈ Metric.ball (0 : ℂ) R := by
    intro s h1 h2 h3 h4
    simpa [Metric.mem_ball, dist_eq_norm] using hrect s h1 h2 h3 h4
  have hg_an_ball : AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) R) :=
    fun s hs => hg_an_cb s (Metric.ball_subset_closedBall hs)
  have hg_nz_ball : ∀ s ∈ Metric.ball (0 : ℂ) R, g s ≠ 0 :=
    fun s hs => hg_nz_cb s (Metric.ball_subset_closedBall hs)
  have hlogg_an : AnalyticOnNhd ℂ (fun s : ℂ => logDeriv g s) (Metric.ball (0 : ℂ) R) :=
    analyticOnNhd_logDeriv_of hg_an_ball hg_nz_ball
  have hdec : ∀ s : ℂ, s ∈ Metric.ball (0 : ℂ) R → f s ≠ 0 →
      logDeriv f s = (∑ᶠ u : ℂ, (((d u : ℤ) : ℂ) * ((s - u)⁻¹))) + logDeriv g s := by
    intro s hs hfs
    have h := logDeriv_decompose_cb (f := f) (g := g) (R := R) hfdiff hfac hs hfs
      (hg_an_cb s (Metric.ball_subset_closedBall hs)).differentiableAt
      (hg_nz_cb s (Metric.ball_subset_closedBall hs))
    simpa [d, one_div] using h
  exact rectZeroCount_imag (f := f) (g := g) (z := z) (w := w) (R := R) S (d := d)
    hzre hzim hdec hS_cov hball hzero hfne hlogg_an hb ht hr hl hb' ht' hr' hl'


/-- **Signed argument-principle identity on a rectangle (hypothesis form).**

The exact counterpart of `rectZeroCount_imag` as an *identity* rather than an inequality:

   2π·Σᶠ_u d(u)·[u strictly inside]
     =  ∫_bottom Im g − ∫_top Im g + ∫_right Re g − ∫_left Re g ,      g = logDeriv f.

This is what lets the vertical sides be bounded by *one-sided* estimates: on the right side no
absolute value is taken, and on the left side the functional-equation rewrite
`∫_left Re g = −(w.re − z.re)·log N − ∫_right Re (g ∘ reflection)` can be substituted before
bounding.  (`rectZeroCount_imag` bounds the same four terms by their absolute values, which is
lossy on the two vertical sides.) -/
theorem rectZeroCount_imag_eq {f g : ℂ → ℂ} {z w : ℂ} {R : ℝ} (S : Finset ℂ) {d : ℂ → ℤ}
    (hzre : z.re < w.re) (hzim : z.im < w.im)
    (hdec : ∀ s : ℂ, s ∈ Metric.ball (0 : ℂ) R → f s ≠ 0 →
      logDeriv f s = (∑ᶠ u : ℂ, (((d u : ℤ) : ℂ) * ((s - u)⁻¹))) + logDeriv g s)
    (hS_cov : ∀ u : ℂ, d u ≠ 0 → u ∈ S)
    (hball : ∀ s : ℂ, z.re ≤ s.re → s.re ≤ w.re → z.im ≤ s.im → s.im ≤ w.im →
      s ∈ Metric.ball (0 : ℂ) R)
    (hzero : ∀ u : ℂ, u ∈ S → f u = 0)
    (hfne : ∀ s : ℂ, (s.re = z.re ∨ s.re = w.re ∨ s.im = z.im ∨ s.im = w.im) →
      z.re ≤ s.re → s.re ≤ w.re → z.im ≤ s.im → s.im ≤ w.im → f s ≠ 0)
    (hg_an : AnalyticOnNhd ℂ (fun s : ℂ => logDeriv g s) (Metric.ball (0 : ℂ) R))
    (hb : IntervalIntegrable (fun x : ℝ => logDeriv f ((x : ℂ) + (z.im : ℂ) * Complex.I))
      MeasureTheory.volume z.re w.re)
    (ht : IntervalIntegrable (fun x : ℝ => logDeriv f ((x : ℂ) + (w.im : ℂ) * Complex.I))
      MeasureTheory.volume z.re w.re)
    (hr : IntervalIntegrable (fun y : ℝ => logDeriv f ((w.re : ℂ) + (y : ℂ) * Complex.I))
      MeasureTheory.volume z.im w.im)
    (hl : IntervalIntegrable (fun y : ℝ => logDeriv f ((z.re : ℂ) + (y : ℂ) * Complex.I))
      MeasureTheory.volume z.im w.im) :
    2 * Real.pi * (∑ u ∈ S, (((d u : ℤ) : ℝ) *
        (if z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im then 1 else 0)))
      = (∫ x : ℝ in z.re..w.re, (logDeriv f ((x : ℂ) + (z.im : ℂ) * Complex.I)).im)
        - (∫ x : ℝ in z.re..w.re, (logDeriv f ((x : ℂ) + (w.im : ℂ) * Complex.I)).im)
        + (∫ y : ℝ in z.im..w.im, (logDeriv f ((w.re : ℂ) + (y : ℂ) * Complex.I)).re)
        - (∫ y : ℝ in z.im..w.im, (logDeriv f ((z.re : ℂ) + (y : ℂ) * Complex.I)).re) := by
  classical
  let INS : ℂ → Prop := fun u => z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im
  have hgeom := rectB_decomp_geom (f := f) (g := g) (z := z) (w := w) (R := R) S (d := d)
    hzre hzim hdec hS_cov hball hzero hfne hg_an
  have hclass : ∀ u : ℂ, u ∈ S → INS u ∨
      (u.re < z.re ∨ w.re < u.re ∨ u.im < z.im ∨ w.im < u.im) := by
    intro u hu
    have hfu0 : f u = 0 := hzero u hu
    by_cases huCl : z.re ≤ u.re ∧ u.re ≤ w.re ∧ z.im ≤ u.im ∧ u.im ≤ w.im
    · have hnb : ¬(u.re = z.re ∨ u.re = w.re ∨ u.im = z.im ∨ u.im = w.im) := by
        intro hb
        exact (hfne u hb huCl.1 huCl.2.1 huCl.2.2.1 huCl.2.2.2) hfu0
      left
      exact ⟨lt_of_le_of_ne huCl.1 (fun h => hnb (Or.inl h.symm)),
        lt_of_le_of_ne huCl.2.1 (fun h => hnb (Or.inr (Or.inl h))),
        lt_of_le_of_ne huCl.2.2.1 (fun h => hnb (Or.inr (Or.inr (Or.inl h.symm)))),
        lt_of_le_of_ne huCl.2.2.2 (fun h => hnb (Or.inr (Or.inr (Or.inr h))))⟩
    · right
      by_cases h1 : u.re < z.re
      · exact Or.inl h1
      · by_cases h2 : w.re < u.re
        · exact Or.inr (Or.inl h2)
        · by_cases h3 : u.im < z.im
          · exact Or.inr (Or.inr (Or.inl h3))
          · by_cases h4 : w.im < u.im
            · exact Or.inr (Or.inr (Or.inr h4))
            · exact absurd ⟨le_of_not_gt h1, le_of_not_gt h2, le_of_not_gt h3,
                le_of_not_gt h4⟩ huCl
  have hres : ∀ u ∈ S, rectB (fun s : ℂ => (s - u)⁻¹) z w =
      if INS u then (2 : ℂ) * (Real.pi : ℂ) * Complex.I else 0 := by
    intro u hu
    rcases hclass u hu with hin | hout
    · rw [if_pos hin, rectB_sub_inv_inside hzre hzim hin]
    · rw [if_neg (fun h => by
        rcases h with ⟨h1,h2,h3,h4⟩
        rcases hout with h5 | h5 | h5 | h5
        · exact absurd h5 (not_lt_of_ge h1.le)
        · exact absurd h5 (not_lt_of_ge h2.le)
        · exact absurd h5 (not_lt_of_ge h3.le)
        · exact absurd h5 (not_lt_of_ge h4.le)), rectB_sub_inv_outside hzre hzim hout]
  have hterm : ∀ u ∈ S, (((d u : ℤ) : ℂ) * rectB (fun s : ℂ => (s - u)⁻¹) z w)
      = (((d u : ℤ) : ℂ) * (if INS u then 1 else 0)) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by
    intro u hu
    rw [hres u hu]
    by_cases h : INS u
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]; ring
  have hLc : ((∑ u ∈ S, (((d u : ℤ) : ℝ) * (if INS u then 1 else 0)) : ℝ) : ℂ)
      = ∑ u ∈ S, (((d u : ℤ) : ℂ) * (if INS u then 1 else 0)) := by
    push_cast
    apply Finset.sum_congr rfl
    intro u _
    by_cases h : INS u <;> simp [h]
  have hident : rectB (logDeriv f) z w
      = ((∑ u ∈ S, (((d u : ℤ) : ℝ) * (if INS u then 1 else 0)) : ℝ) : ℂ)
        * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by
    rw [hgeom, Finset.sum_congr rfl hterm, ← Finset.sum_mul, hLc]
  have hCre : ((2 : ℂ) * (Real.pi : ℂ) * Complex.I).re = 0 := by
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have hCim : ((2 : ℂ) * (Real.pi : ℂ) * Complex.I).im = 2 * Real.pi := by
    simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have him : (rectB (logDeriv f) z w).im
      = 2 * Real.pi * (∑ u ∈ S, (((d u : ℤ) : ℝ) * (if INS u then 1 else 0))) := by
    rw [hident, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hCre, hCim]
    ring
  have hside := rectB_im_eq (h := logDeriv f) (z := z) (w := w) hb ht hr hl
  rw [← him, hside]



/-- **Signed argument-principle identity on a rectangle, with the divisor factorisation supplied
internally.**  Applied companion of `rectZeroCount_imag_eq`, stated hypothesis-for-hypothesis
against `rectZeroCount_boundary_le` (like `rectZeroCount_imag_of`), but as the exact *identity*
— so the caller may bound the right side by one-sided estimates on the verticals. -/
theorem rectZeroCount_imag_eq_of {f : ℂ → ℂ} {z w : ℂ} {R : ℝ}
    (hfdiff : Differentiable ℂ f) (hRpos : 0 < R) (hzre : z.re < w.re) (hzim : z.im < w.im)
    (hf0 : f 0 ≠ 0)
    (hrect : ∀ s : ℂ, z.re ≤ s.re → s.re ≤ w.re → z.im ≤ s.im → s.im ≤ w.im → ‖s‖ < R)
    (hfne : ∀ s : ℂ, (s.re = z.re ∨ s.re = w.re ∨ s.im = z.im ∨ s.im = w.im) →
      z.re ≤ s.re → s.re ≤ w.re → z.im ≤ s.im → s.im ≤ w.im → f s ≠ 0)
    (hb : IntervalIntegrable (fun x : ℝ => logDeriv f ((x : ℂ) + (z.im : ℂ) * Complex.I))
      MeasureTheory.volume z.re w.re)
    (ht : IntervalIntegrable (fun x : ℝ => logDeriv f ((x : ℂ) + (w.im : ℂ) * Complex.I))
      MeasureTheory.volume z.re w.re)
    (hr : IntervalIntegrable (fun y : ℝ => logDeriv f ((w.re : ℂ) + (y : ℂ) * Complex.I))
      MeasureTheory.volume z.im w.im)
    (hl : IntervalIntegrable (fun y : ℝ => logDeriv f ((z.re : ℂ) + (y : ℂ) * Complex.I))
      MeasureTheory.volume z.im w.im) :
    2 * Real.pi * (∑ᶠ u : ℂ, (((MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) R)) u : ℤ) : ℝ) *
        (if z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im then 1 else 0))
      = (∫ x : ℝ in z.re..w.re, (logDeriv f ((x : ℂ) + (z.im : ℂ) * Complex.I)).im)
        - (∫ x : ℝ in z.re..w.re, (logDeriv f ((x : ℂ) + (w.im : ℂ) * Complex.I)).im)
        + (∫ y : ℝ in z.im..w.im, (logDeriv f ((w.re : ℂ) + (y : ℂ) * Complex.I)).re)
        - (∫ y : ℝ in z.im..w.im, (logDeriv f ((z.re : ℂ) + (y : ℂ) * Complex.I)).re) := by
  classical
  let d : ℂ → ℤ := fun u => (MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) R)) u
  have hfB : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R) :=
    fun z _ => hfdiff.analyticAt z
  have hord : ∀ s : ℂ, s ∈ Metric.closedBall (0 : ℂ) R → meromorphicOrderAt f s ≠ ⊤ :=
    order_ne_top_on_closedBall hRpos.le hfB hf0
  have hsupp0 : (MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) R)).support.Finite :=
    MeromorphicOn.divisor_support_finite_of_subset (f := f) (V := Metric.closedBall (0 : ℂ) R)
      hfB.meromorphicOn (isCompact_closedBall (0 : ℂ) R) (by simp)
  rcases factor_pointwise (U := Metric.closedBall (0 : ℂ) R) hfB.meromorphicOn hord hsupp0 hfB with
    ⟨g, hg_an_cb, hg_nz_cb, hfac⟩
  have hsuppd : (Function.support d).Finite := by
    dsimp [d]
    exact MeromorphicOn.divisor_support_finite_of_subset (f := f)
      (V := Metric.closedBall (0 : ℂ) R) (U := Metric.closedBall (0 : ℂ) R) hfB.meromorphicOn
      (isCompact_closedBall (0 : ℂ) R) (by intro z hz; exact hz)
  let S : Finset ℂ := hsuppd.toFinset
  have hS_cov : ∀ u : ℂ, d u ≠ 0 → u ∈ S := by
    intro u hu
    dsimp [S]
    exact (hsuppd.mem_toFinset).2 hu
  have hzero : ∀ u : ℂ, u ∈ S → f u = 0 := by
    intro u hu
    have hdu : d u ≠ 0 := by
      have huS : u ∈ (Function.support d) := (hsuppd.mem_toFinset).1 (by simpa [S] using hu)
      simpa using huS
    exact divisor_ne_zero_imp_eq_zero_of_analyticOnNhd hfB (by simpa [d] using hdu)
  have hball : ∀ s : ℂ, z.re ≤ s.re → s.re ≤ w.re → z.im ≤ s.im → s.im ≤ w.im →
      s ∈ Metric.ball (0 : ℂ) R := by
    intro s h1 h2 h3 h4
    simpa [Metric.mem_ball, dist_eq_norm] using hrect s h1 h2 h3 h4
  have hg_an_ball : AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) R) :=
    fun s hs => hg_an_cb s (Metric.ball_subset_closedBall hs)
  have hg_nz_ball : ∀ s ∈ Metric.ball (0 : ℂ) R, g s ≠ 0 :=
    fun s hs => hg_nz_cb s (Metric.ball_subset_closedBall hs)
  have hlogg_an : AnalyticOnNhd ℂ (fun s : ℂ => logDeriv g s) (Metric.ball (0 : ℂ) R) :=
    analyticOnNhd_logDeriv_of hg_an_ball hg_nz_ball
  have hdec : ∀ s : ℂ, s ∈ Metric.ball (0 : ℂ) R → f s ≠ 0 →
      logDeriv f s = (∑ᶠ u : ℂ, (((d u : ℤ) : ℂ) * ((s - u)⁻¹))) + logDeriv g s := by
    intro s hs hfs
    have h := logDeriv_decompose_cb (f := f) (g := g) (R := R) hfdiff hfac hs hfs
      (hg_an_cb s (Metric.ball_subset_closedBall hs)).differentiableAt
      (hg_nz_cb s (Metric.ball_subset_closedBall hs))
    simpa [d, one_div] using h
  have hid := rectZeroCount_imag_eq (f := f) (g := g) (z := z) (w := w) (R := R) S (d := d)
    hzre hzim hdec hS_cov hball hzero hfne hlogg_an hb ht hr hl
  have hfinsum : (∑ᶠ u : ℂ, (((d u : ℤ) : ℝ) *
      (if z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im then 1 else 0)))
      = ∑ u ∈ S, (((d u : ℤ) : ℝ) *
          (if z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im then 1 else 0)) := by
    rw [finsum_eq_sum_of_support_subset
      (fun u : ℂ => (((d u : ℤ) : ℝ) *
        (if z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im then 1 else 0))) (s := S)]
    intro u hu
    have hdu : d u ≠ 0 := by
      intro hd0
      apply hu
      simp [hd0]
    exact hS_cov u hdu
  rw [hfinsum]
  exact hid


end Commons.Analysis.Complex

open Complex DirichletCharacter
open scoped Real Topology

/-! ---------------------------------------------------------------------------------------
**STATUS: PROVED (final session).**  The target

    ∀ T₀,  Σᶠ_u (divisor Λ (closedBall (2+iT₀) (5/2))) u ≤ (3/2)(log N + log(4+|T₀|)) + 6

is proved below by invoking the shared-commons theorem
`Commons.NumberTheory.DirichletCharacter.diskZeroCount_two_half`
(`Submission/Commons/NumberTheory/DirichletCharacter/diskZeroCount_two_half.lean`), which was
proved by a teammate in the shared repository via the disk-Jensen route (circle of radius `5`
about `2+iT₀`, pointwise `L`-bounds `LFunction_log_le_circUB`, the reduction
`circleExcess_le_L_excess`, and the arithmetic `integral_circUB_le`).

This file additionally contains the *Jensen step* of the same route in a reusable form:

  `completedL_disk_divisor_le_circleAverage` :
    `log(6/(5/2)) · Σᶠ_u (divisor Λ (closedBall c (5/2))) u
       ≤ circleAverage (log‖Λ·‖) c 6 - log‖Λ c‖`

i.e. Jensen's formula on the circle of radius `6` about `c = 2 + iT₀` together with the
weight comparison `log(6/‖c-u‖) ≥ log(12/5)` for the zeros in the ball of radius `5/2`
(and nonnegativity of the remaining weights).  Everything below the status note is the
historical analysis/reduction record of the earlier sessions (mostly superseded).

The pointwise-bound material requested for the radius-`6` variant of the circle bound (which
was the plan of this session) is in the commons: `gammaR_upper_stirling_shift`,
`gammaR_upper_low_strip`, `gammaR_lower_two_sharp`, `gammaR_lower_three_sharp`,
`LFunction_strip_convexity_abs`, `LFunction_norm_le_two_of_two_le_re`,
`LFunction_two_lower_euler`.
--------------------------------------------------------------------------------------- -/
/-!
# `completedL_diskZeroCount_explicit` : analysis and reduction (historical record)

Target (fixed statement, see below):

    ∀ T₀ : ℝ,
      (∑ᶠ u : ℂ, (((divisor (completedLFunction χ) (closedBall (2 + I*T₀) (5/2))) u : ℤ) : ℝ))
        ≤ (3/2) * (log N + log (2 + |T₀| + 2)) + 6

for a primitive non-trivial `χ mod N`.  [NOTE: `2 + |T₀| + 2 = 4 + |T₀|`.]

## Status after the second session (this file)

The statement is TRUE (Riemann–von Mangoldt: the true count is `≈ 0.73·log(N(2+|T₀|)) + O(1)`
with `o(log)` fluctuations, so the target's `1.5·log + 6` has room).  It is NOT proved here;
what follows is a complete reduction with exact constant requirements, plus a full account of
two candidate proof routes and their (small!) remaining gaps, so that the work can be
continued without redoing the analysis.

Pieces already proved in the shared commons (use them):
* `completedLogDeriv_two_tight`             : `‖Λ'/Λ(2+it)‖ ≤ (1/2)log(2+|t|) + 3`.
* `completedLogDeriv_neg_one_tight` (NEW)   :
  `‖Λ'/Λ(-1+it)‖ ≤ log N + (1/2)log(2+|t|) + 3`   (FE + the previous line).
* `zerosInStrip`                            : every zero of `Λ` has `0 < Re < 1`.
* `completedLFunction_eq`                   : `Λ(s,χ) = N^(1/2-s)·ε(χ)·Λ(1-s,χ⁻¹)`.
* `completedLogDeriv_fe`                    : `logDeriv Λ(χ) s = -log N - logDeriv Λ(χ⁻¹) (1-s)`
                                              (requires both completed values ≠ 0).
* `LFunction_conj`                          : `conj(L(χ,s)) = L(χ⁻¹, conj s)`; and
  `gammaFactor χ = Gammaℝ` (even χ) or `Gammaℝ(·+1)` (odd χ) is **N-free**, so with
  `Λ = gammaFactor · L` one gets `conj(Λ(s,χ)) = Λ(conj s, χ⁻¹)` and hence
      `conj(logDeriv Λ(χ) (conj s)) = logDeriv Λ(χ⁻¹) s`                       (**)
* `rectZeroCount_boundary_le`               : argument principle on a rectangle (weight 1).

## PROVED IN THIS FILE (session 2; helper lemmas above the target)

* `completedL_zero_im_close` : every zero `u` of `Λ(χ,·)` with
  `‖u - (2+iT₀)‖ ≤ 5/2` satisfies `|Im u - T₀| < √21/2` (containment, Step 1).
* `GammaR_star` : `conj(Γℝ z) = Γℝ (conj z)`.
* `logDeriv_starComp` : `logDeriv (starComp f) z = conj (logDeriv f (conj z))` for `f` entire.
* `starComp_completedLFunction_eq` : `conj(Λ(s,χ)) = Λ(conj s, χ⁻¹)` for `χ ≠ 1`
  (identity theorem from the half plane `Re > 1`, using `LFunction_conj` and
  `PL.AfeAssembly.gammaFactor_inv_eq`).
* `re_completedLogDeriv_critical_line` : **for primitive `χ ≠ 1` and `Λ(1/2+iT) ≠ 0`,
  `Re (logDeriv Λ(χ)) (1/2+iT) = -(log N)/2`.**  This is the key identity for the
  "eyebrow" route of Step 4 below: on the critical line the logarithmic derivative has a
  *known* real part, so the conductor costs only `(log N)/2` there (with no additive error).
  (Requests to publish these in the shared commons were refused because the fleet was busy;
  they live here for now and will be published when the target is finished.)

## Step 1 — containment (proved above as `completedL_zero_im_close`)

A zero `u` of `Λ` in `closedBall (2+iT₀) (5/2)` satisfies `0 < Re u < 1` (`zerosInStrip`),
hence `(Re u - 2)² + (Im u - T₀)² ≤ 25/4` with `1 < (Re u - 2)² ≤ 4`, so

    |Im u - T₀| < √(25/4 - 1) = √21/2 = 2.2913...,     (strict!)

i.e. the disk count is at most the number of zeros in the *lens*
`L := {σ ∈ (0,1), (σ-2)² + (γ-T₀)² ≤ 6.25}` (the disk intersected with the critical strip).
Moreover the zero set is invariant under `ρ ↦ 1 - ρ̄` (from the FE and `LFunction_conj`).

## Step 2 — why the obvious routes fail

1. *Jensen on a circle around `2+iT₀`.*  The circular mean of `log|Λ|` satisfies
   `M(σ) := (1/2π)∫ log|Λ(σ+iθ)| dθ = -(3/2)log N + M(-1,...)`, and on the left part of the
   circle `Λ` grows like `N^{3R/2}`; consequently `count ≤ 0.66·R·log N / log(R/(5/2)) ≥ 5 log N`
   (minimum at `R ≈ 5`).  Hopeless — Jensen is ~3.5× too lossy.  (Jensen–Carleman is equally bad.)
2. *Window cover by `completedL_local_zeroCount` / `completedL_ballZeroCount`*: the constant is
   `≈ 4·cw·(1+log 3/2)·(ρ+1) ≈ 25·cw + 4` with `cw ≳ 0.7`; 50× too lossy.
3. *Horizontal integrals `∫_{-1}^{2}‖Λ'/Λ(σ+iT)‖dσ` at a "good height T"* (the team's route
   L144 → L149 → ... ): the pointwise bound needs `Σ_j log(1/δ_j)` over the zeros near `T`,
   and the only available (pole-sum) bounds lose a factor ≈ 3.  Concretely the team's
   `logDeriv_horizontal_good_height` gives `40 + 8(log N + log(2+c+3))`, whereas the rectangle
   route (step 3 below) *requires* `(12/5)(log N + log(2+c+3)) + O(1)`: factor ≈ 3.3 too lossy.
   Also, the registry shows that chain is DOWNSTREAM of this lemma (`pfPole_pointwise` needs
   this disk count), so it cannot be used here.

## Step 3 — the viable route: weighted argument principle + an entire test function

`rectZeroCount_weighted` (REQUESTED; generic, in `Analysis/Complex/`):
for `f`, `G` entire, the rectangle with corners `z,w` inside `ball 0 R` and `f ≠ 0` on its
boundary,

    rectB (fun s => logDeriv f s * G s) z w
      = 2πi · ∑ᶠ u, (divisor f (closedBall 0 R) u : ℂ) · (if u strictly inside then G u else 0).

Proof sketch (all ingredients are already in the commons): factor
`f = ∏ᶠ_u (·-u)^{d u} · g` with `g` analytic and non-vanishing on the rectangle
(`logDeriv_decompose_cb`, `factor_pointwise`), so `logDeriv f = Σ d u (s-u)⁻¹ + logDeriv g`;
`rectB` is linear, `rectB` of a holomorphic function vanishes
(`rectB_logDeriv_eq_zero` generalised), and for each `u` write
`G(s) = G(u) + (s-u)·dslope G u s` with `dslope G u` entire (Mathlib `dslope`), so
`rectB (fun s => G s * (s-u)⁻¹) = G u · rectB (fun s => (s-u)⁻¹)`, and the latter is
`2πi` inside / `0` outside by `rectIntegral_sub_inv_inside` / `rectIntegral_sub_inv_outside`.

Application ("two-line" form): for the rectangle `[-1,2] × [T₋,T₊]` containing the disk and
`G` entire with `G ≈ c > 0` on the lens and decaying in `|Im s|`,

    (#zeros in the lens)·c ≤ (1/2π)·[ ∫ w₂(t)|G(2+it)| dt + ∫ w₋₁(t)|G(-1+it)| dt ] + (tiny)

where `w₂(t) = (1/2)log(2+|t|) + B`, `w₋₁(t) = log N + (1/2)log(2+|t|) + B` and
`B ≈ 1.6` is the provable constant in `‖Λ'/Λ(2+it)‖ ≤ (1/2)log(2+|t|) + B` (the commons has
`B = 3`; the sharp value from `logDeriv Γℝ = -log π/2 + ψ(·)/2` is `B ≈ 1.6`).
The horizontal sides are damped by `|G| ≈ e^{-μH²}` and the far zeros contribute `≥ -tiny`
(Gaussian-type `G` satisfies `Re G(ρ) ≥ 0` for every zero, since `|arg G(ρ)| ≤ μ|γ-T₀|`
and `|G(ρ)| = e^{-μ(γ-T₀)²}`).

**Exact constants required** (worst cases `T₀ = 0`, `N = 3`, log N = 1.0986) with
`M₂ := ∫|G(2+it)|dt`, `M₋₁ := ∫|G(-1+it)|dt`:

    (a)  M₋₁/c ≤ 9.42            (log N coefficient)
    (b)  (M₂+M₋₁)/c ≤ 18.85      (log(4+|T₀|) coefficient)
    (c)  2.40·(M₂+M₋₁)/c + 1.10·M₋₁/c ≤ 61.1   (additive constant 6)

The ideal test function (sharp in `Im`, flat over the lens) gives `M₂ = M₋₁ ≈ 4.58c`
(9.16c total) and would satisfy everything comfortably.  Numerically (this session) the best
smooth families give:

    G = (1+a z²+b z⁴)e^{μz²},  z = s - (x₀+iT₀):   M₂/c = 10.7, M₋₁/c = 9.2, sum = 19.9  [need ≤ 18.85]
    G = e^{μz²} (plain Gaussian, optimal x₀ ≈ 0): M₂/c = 12.1, M₋₁/c = 9.6, sum = 21.6
    (a) and (c) are satisfied; only (b) is violated, by ~5–12%.
    The log-convexity of `σ ↦ ∫|G(σ+it)|dt` gives only the weak bound `M₂ ≥ 3.2c`.

**Conclusion for this route**: everything closes except a ~5% shortfall in constraint (b);
it needs a better entire test function than the Gaussian/`poly·Gaussian` families (or a
slightly better constant `B`, or a sharper lens).  Candidates for the next session:
`(1+a z² + b z⁴ + c z⁶)e^{μz²}` optimised numerically, sums/differences of Gaussians with
complex parameters, or (see Step 4) replacing the right-hand line by an arc.

## Step 4 — better route: use the critical line (the "eyebrow" contour)

**Key identity (provable from (*) and `completedLogDeriv_fe`, requested as
`Commons.NumberTheory.DirichletCharacter.re_completedLogDeriv_critical_line`):**

    Re (logDeriv Λ(χ)) (1/2 + iT) = -(log N)/2      (whenever Λ(1/2+iT) ≠ 0).

Proof: `conj(g(s)) = -log N - g(s)` at `s = 1/2+iT` (FE + (*)), take real parts.

This halves the log N cost.  Consider the region
`Ω = {|s-(2+iT₀)| ≤ R, Re s ≥ 1/2}` (half-disk) and `Ω' = {|s-(-1+iT₀)| ≤ R, Re s ≥ 1/2}`
(a cap).  Using the reflection `ρ ↦ 1-ρ̄`:

    count(disk(2+iT₀,R)) = #{zeros in Ω} + #{zeros in Ω'}      (exactly, if no zero lies on Re = 1/2)

and each term is bounded by the argument principle on that region.  The contour is
"the arc of the disk with `Re ≥ 1/2`" plus "the diameter `{Re = 1/2}`", and:
* on the diameter `Re g(1/2+it) = -(log N)/2` **exactly**, so the diameter's contribution to
  the bound has log N coefficient `1/2` and *no* additive constant;
* the arc of `disk(2)` has `Re ≥ 2` where `‖Λ'/Λ‖ ≤ (1/2)log(2+|t|) + O(1)` with
  **no log N** (the conductor is absent: `|L'/L(σ+it)| ≤ ΣΛ(n)n^{-2} ≈ 0.57` for `σ ≥ 2`);
* the arc of the cap has `Re ∈ [1/2,3/2]`, contributing log N only on its short `Re ≤ 1` part.
With `G = e^{μ(s-(2+iT₀))²}`, `μ ≈ 0.05`, crudely computed constants are
`(log N) ≈ 1.41 ≤ 1.5`, `(log T₀) ≈ 1.27 ≤ 1.5`, `(additive) ≈ 3.9 ≤ 6` — i.e. this route
seems to FIT, but two technical obstructions must be handled:
1. the diameter `{Re = 1/2, |Im - T₀| ≤ 2}` must be free of zeros (the log-derivative has
   poles there).  The ordinates of zeros on the critical line are a *discrete* set, but a
   length-4 window generally contains some.  Standard fix: shift the centre `T₀ → T₀'` (the
   count for `closedBall(2+iT₀,5/2)` is recovered as the `T₀' → T₀`, `R ↓ 5/2` limit) or push
   the diameter to `Re = 1/2 ± ε` and bound the loss with a *derivative* bound
   `‖g'‖ ≤ C log²(q(|t|+2))` (needs `logDeriv_estimate`-style machinery plus clearance);
2. the weight on the cap's arc near `Re = 1` blows up like `1/(σ-1)` (the pole of `ζ'/ζ`);
   the *true* `L'/L(σ+it,χ)` is bounded there (`χ ≠ 1`), but an effective bound needs a
   quantitative lower bound `|L(1+it,χ)| ≫ 1/log(q(|t|+2))`.

## STATUS after session 3 (the accurate accounting)

The file builds (`lake build Submission.Work...completedL_diskZeroCount_explicit`, rc=0) with
TWO unproved statements (the `logDeriv_im_good_height` crux, since deleted, and one other), both isolated in *stated* lemmas that the assembly consumed:

* `logDeriv_im_good_height`  : the crux (two good heights `T₁ < T₀-√21/2 < T₀+√21/2 < T₂`
  with `T₂-T₁ ≤ √21+2` and the strip bound `∫_{1/2}^{2}‖Im(Λ′/Λ)‖ ≤ (7/10)(log N+log(2+|T₀|+4))+9`).
  Requested from the fleet (fleet reported busy three times) but not yet proved.
* `re_completedLogDeriv_two_tight` : the sharp *one-sided* bound
  `Re(Λ′/Λ)(2+iT) ≤ (1/2)log(2+|T|)+3/4` (reduces the additive constant of the vertical sides
  from `H·6` to `H·(3/2)`; the loose commons versions give `H·6`, which already saturates the
  additive budget `6` when `H = √21+2`).

Proved in this file (no unproved steps):

* `exists_good_height` : every interval contains a height with no zero of `Λ(χ,·)` on it
  (from `finite_zeroHeights_window` + infinity of an open interval).  This is the *only*
  geometric ingredient of the good-height step that is independent of the constants.

### NEW (session 3, second half): the signed argument principle is PROVED

`Submission/Work/Analysis/Complex/rectZeroCount_imag.lean` (module
`Submission.Work.Analysis.Complex.rectZeroCount_imag`, elaborates with **no unproved steps**) contains
the two lemmas the assembly needs instead of the norm version `rectZeroCount_boundary_le`:

* `rectB_im_eq` — the imaginary part of `rectB` as the signed combination of the four side
  integrals (pure unfolding + `Complex.imCLM.intervalIntegral_comp_comm`);
* `rectZeroCount_imag` — the **signed argument principle**:

      Σᶠ_u d(u)·[u strictly inside]
        ≤ (1/2π)·( ∫_bottom |Im g| + ∫_top |Im g| + ∫_right |Re g| + ∫_left |Re g| ),   g = logDeriv f

  proved from `rectB_decomp_geom` + `rectB_sub_inv_inside`/`rectB_sub_inv_outside` +
  `rectB_im_eq` + the monotone integral inequality.  Its hypotheses are the *same* as
  `rectB_decomp_geom`'s (the divisor factorisation is supplied by the caller, exactly as
  `rectZeroCount_boundary_le` does internally), plus the interval-integrability of `logDeriv f`
  and of its real/imaginary parts along the four sides.

A fourth lemma, `rectZeroCount_imag_eq`, is also **proved** there — the *exact identity*

    2π·Σᶠ_u d(u)·[u inside] = ∫_bottom Im g − ∫_top Im g + ∫_right Re g − ∫_left Re g

(no absolute values).  This is the sharp form the assembly wants: only the identity lets the two
vertical sides be bounded by *one-sided* estimates.  Indeed with the functional equation,
`∫_left Re g = −(w.re−z.re)·log N − ∫_right Re (g^{χ⁻¹}∘reflection)`, so the two vertical
contributions combine to `H·log N + ∫_right Re g + ∫_right Re g^{χ⁻¹}` and are bounded by
`H(log N + log(4+|T₀|) + 2·(3/4))` using only `re_completedLogDeriv_two_tight` for `χ` and `χ⁻¹`
— *not* by `|Re|` on each side separately, which would need a two-sided bound and cost an extra
additive `≈ 2H` (≈ 2.5 after dividing by `2π`).  With that, the budget leaves coefficient `≈ 7/10`
and additive `≈ 6` for the crux, as recorded below.

A third lemma, `rectZeroCount_imag_of`, is also **proved** in that file: it is the *drop-in*
counterpart of `rectZeroCount_boundary_le` with the factorisation supplied internally
(`factor_pointwise` -> `g`, `hsuppd` -> `S`, `logDeriv_decompose_cb` -> `hdec`,
`order_ne_top_on_closedBall`, `analyticOnNhd_logDeriv_of`, `divisor_ne_zero_imp_eq_zero_of_analyticOnNhd`),
so the hypothesis list is *identical* to `rectZeroCount_boundary_le`'s (plus the interval
integrability of `logDeriv f` and of its real/imaginary parts on the four sides, which follow from
continuity of `logDeriv Λ` off the boundary).

`request_lemma` for all three (`Analysis/Complex/rectZeroCount_imag`, `Analysis/Complex/rectB_im_eq`,
`Analysis/Complex/rectZeroCount_imag_of`) was attempted repeatedly and every time reported the team
busy, so they are **not yet in the commons**; a colleague can commit them directly from the Work
file above once the queue drains.

### What remains (mechanical)

1. Apply `rectZeroCount_imag_of` with `f := Λ(χ,·)`, `z := -1+iT₁`, `w := 2+iT₂`,
   `R` large enough, `hf0 := completedLFunction_zero_ne_zero`, `hfne` from the good heights
   (`hg₁`/`hg₂`), and the eight interval-integrability hypotheses from continuity of
   `logDeriv Λ` and of `Im`/`Re (logDeriv Λ)` off the horizontal lines.
2. Bound the four signed sides: `∫ Re(Λ′/Λ)(2+it) dt` by `re_completedLogDeriv_two_tight`,
   `-∫ Re(Λ′/Λ)(-1+it) dt = ∫(log N + Re(Λ′/Λ)(χ⁻¹)(2-it)) dt` by the same bound for `χ⁻¹`,
   and the two horizontal sides by `∫_{-1}^{2}|Im(Λ′/Λ)| = 2∫_{1/2}^{2}|Im(Λ′/Λ)|` together with
   the crux `logDeriv_im_good_height`.
3. Close with the algebra recorded above (the target is `(3/2)(log N + log(4+|T₀|)) + 6`).


### Horizontal block: `im_logDeriv_reflect` is PROVED

`im_logDeriv_reflect` (proved, no unproved steps) states

    Im (Λ′/Λ)(σ+iT) = Im (Λ′/Λ)(1−σ+iT)      for σ ≤ 1/2, any zero-free height T,

via the functional equation `logDeriv Λ(χ) s = -log N - logDeriv Λ(χ⁻¹)(1−s)` together with
`logDeriv Λ(χ⁻¹) z = conj (logDeriv Λ(χ) (conj z))`.  Two points worth recording:

* the `-log N` term **drops out** on taking imaginary parts (`((Real.log N : ℝ) : ℂ)` is real);
* the two minus signs — one from the functional equation, one from conjugation — **cancel**, so
  the reflection contributes a factor `+1`.

Consequence (the next, purely integral-theoretic step): by the substitution `σ ↦ 1−σ`,

    ∫_{-1}^{1/2} Im g(σ+iT) dσ = ∫_{1/2}^{2} Im g(σ+iT) dσ   ⟹   ∫_{-1}^{2} Im g(σ+iT) dσ = 2∫_{1/2}^{2} Im g(σ+iT) dσ,

so each horizontal side of `completedL_boxZeroCount_eq` is at most `2 ∫_{1/2}^{2} |Im g|` —
i.e. the crux `logDeriv_im_good_height`.  What remains for the horizontals is therefore only the
interval substitution (a.e. congruence plus `intervalIntegral.integral_comp_sub_left`-style
change of variable), not any further analysis of `Λ`.

### ADDITIVE-CONSTANT GAP found (session 3, end) — must be fixed before the final step

`completedL_boxZeroCount_final` gives

    N_box ≤ (1/2π) · ( H·(log N + log(2+|T₀|+2) + c_v) + 4·((7/10)(log N + log(2+|T₀|+4)) + c_h) )

with `H = T₂−T₁ ≤ √21 + 2 = 6.583`, currently `c_v = 4` (proved inside
`completedL_boxVertical_le`; the proof actually establishes `15/4`, and `13/4` after replacing the
`+5/2` slack in `hpt2` by `+2`) and `c_h = 6`.  Pushing this through
`(3/2)(log N + log(2+|T₀|+2)) + 6` needs (using `log(2+|T₀|+4) ≤ log(2+|T₀|+2) + log(3/2)`)

    √21+2 + 4·(7/10) ≤ 2π·(3/2)          ⟺  9.383 ≤ 9.425   ✓ (coefficient: fine)
    6.583·c_v + 4·c_h + 1.13 ≤ 2π·6 = 37.7  ⟺  6.583·c_v + 4·c_h ≤ 36.6   (additive)

and `6.583·4 + 4·6 = 50.3 > 36.6`: **the additive constants as stated do NOT close** (the earlier
`3/2` figure in the note above assumed `c_v = 3/2`, which the vertical proof does not deliver).
Feasible pairs: `(c_v, c_h) = (13/4, 3)` gives `21.4 + 12 = 33.4` ✓ with slack; `(5/2, 5)` gives
`36.5` — at the limit.  So either `completedL_boxVertical_le`'s constant must be tightened to
`≤ 13/4` (replace `+5/2` by `+2` in `hpt2`/`hI2`) **and** the crux `logDeriv_im_good_height`
restated with additive `3` instead of `6`, or `H` must be reduced (windows of half-width `1/2`
around `T₀ ∓ √21/2` would give `H ≤ √21+1` and `2π·6` is then comfortably enough).

### Corrected constant accounting (this is the exact algebra the assembly must satisfy)

Write `F(T) := ∫_{1/2}^{2}‖Im(Λ′/Λ)(σ+iT)‖dσ`.  With the **signed** argument principle on
`[-1,2] × [T₁,T₂]` (needed: the unsigned norm version pays an extra `3 log N` from the
functional-equation step `∫_{-1}^{1/2}‖Λ′/Λ‖ ≤ (3/2)log N + ∫_{1/2}^{2}‖Λ′/Λ‖`, which
*by itself* exceeds the `1.5 log N` budget once `H = √21+2`):

   2π·count ≤ H·(log N + log(4+|T₀|) + 3/2)   [vertical sides; sharp one-sided bounds]
            + 4·F(T)                            [two horizontal sides, |∫_{-1}^{2}Im Λ′/Λ| ≤ 2F]

and the target `(3/2)(log N+log(4+|T₀|))+6` is met **iff**  `F(T) ≤ (7/10)(log N+log(4+|T₀|+2)) + 9`
(as stated; the coefficient `7/10` comes out of `1.5 - H/2π = 1.5 - 1.047 = 0.453` divided by
`4/2π = 0.6366`).  The additive constant `6` leaves room once the vertical additive is `H·(3/2) ≈ 9.9`
(i.e. `≈ 1.57` after dividing by `2π`).

If instead the sharp one-sided vertical bound is unavailable and only `‖Λ′/Λ(2+it)‖ ≤
(1/2)log(2+|t|)+3` is used, the additive budget forces `H ≤ 5.5`, i.e. the two good heights must
lie in windows of total length `≤ 5.5-√21 = 0.917` around `T₀ ∓ √21/2`; the crux must then be
stated with *half-windows* `(c, c+1/2)` (or narrow windows) and the corresponding average.

### Why the crux cannot be avoided

`Im(Λ′/Λ)(σ+iT) = -∂_T log|Λ(σ+iT)|`, so `∫_{-1}^{2}Im(Λ′/Λ)(σ+iT)dσ` is (minus) the
`T`-derivative of the slice integral `∫_{-1}^{2}log|Λ(σ+iT)|dσ`; by the functional equation
`Λ(χ,s) = N^{1/2-s}ε(χ)Λ(χ⁻¹,1-s)` this equals `-2∫_{1/2}^{2}Im(Λ′/Λ)(σ+iT)dσ`.  On the strip
`1/2 ≤ σ ≤ 1` the functional equation maps `σ` to `1-σ ∈ [1/2,1]` — the *same* strip — so it
gives no bound there.  A pointwise bound is also impossible (a zero may lie arbitrarily close
to the line `Im = T`), so the correct input is the *integral* form `F` above; classically this
is the `S(T)`-bound obtained from the local Riemann–von Mangoldt count of the zeros near the
segment (Hadamard partial fraction / explicit formula).  The commons `partialFraction_eq`,
`logDeriv_estimate`, `marginLogDeriv_estimate`, `pfPole_pointwise` and the local zero count
`completedL_local_zeroCount`/`windowZeroCountC` are the tools for it; the last two currently
carry constants (`≈25`) far too large, and the far-zero part of the partial fraction converges
only conditionally (`Σ_ρ|1/(s-ρ)+1/ρ| = ∞`), so the shell/annulus argument via the
2-dimensional zero density (each zero contributes `≤ π` to `F`, and the shells
`|γ-T| ∈ [2^j,2^{j+1}]` contribute `≪ log(qT)` in total) is the form the proof must take.

## What to do next (concrete)

1. Prove `rectZeroCount_weighted` (requested; adapt `rectZeroCount_boundary_le`, using
   Mathlib's `dslope` for the difference-quotient factor).
2. Prove `re_completedLogDeriv_critical_line` (short: from `completedLogDeriv_fe` and (*),
   which needs `conj(Λ(s,χ)) = Λ(conj s,χ⁻¹)` from `LFunction_conj` + the N-freeness of
   `gammaFactor`).
3. Push the test-function optimisation (route of Step 3) and/or implement Step 4 with the
   convergence/perturbation argument.
4. Only then assemble: containment (Step 1) + weighted argument principle + test function
   + the two tight vertical bounds + the algebra, and `declare_proven`.
-/


/-! ## SESSION 4: the viable route is JENSEN on the disk (Mathlib), not the argument principle

### The exact constant accounting (refined) — route (3) fits with room

* The circle-mean of the conductor coefficient `κ̄` (with `κ(σ) = max 0 (1/2-σ)`, which equals the
  conductor coefficient of `Λ` at every `σ`) equals
  `E[max 0 (-3/2 - 6 cos θ)] = (6·√(1-1/16) - (3/2)·arccos(1/4))/π = 1.2199...`;  using only
  `arccos(1/4) ≥ 1.3` (provable from `Real.sin_gt_sub_cube` and `π > 3.14`) gives `κ̄ ≤ 1.2285`.
* The circle-mean of the `log|t|` coefficient `λ(σ) = max 0 ((σ-1)/2) (-σ/2)` equals `1.7265...`;
  it splits as `(1/2)·E[max 0 (1+6cos θ)] + (1/2)·E[max 0 (-2-6cos θ)]`, with
  `E[max 0 (1+6cos θ)] = (α + 6 sin α)/π`, `α = arccos(-1/6) ≥ 1.73`, `≤ 1.74` (from
  `Real.sin_gt_sub_cube`), and `E[max 0 (-2-6cos θ)] = (6√(1-1/9) - 2·arccos(1/3))/π`.
  Bound: `λ̄ ≤ 1.727`.
* Hence both log-coefficients are `κ̄/log(12/5) = 1.4032` and `(λ̄-1/2)/log(12/5) = 1.4013`, both
  `≤ 3/2`, with slack `≈ 0.10` per logarithm.
* The constant terms are small **provided** one does not use the crude bounds:
  `log ‖L(σ+it)‖ ≤ log ζ(σ)` for `σ ≥ 2` (i.e. `≤ log 2`), the log-log bound
  `log ‖L(σ+it)‖ ≤ log(log N + log(2+|t|) + 6)` only on `1 ≤ σ ≤ 2` and (via the functional
  equation) on `-1 ≤ σ ≤ 0`, the convexity bound with the log-log factor only on the strip
  `0 ≤ σ ≤ 1` (together the arcs of `σ ∈ [-1,2]` are only `16.7%` of the circle), the sharp
  Stirling bounds `log ‖Γℝ(σ+it)‖ ≤ ((σ-1)/2)log(2+|t|) + 0.35 - (π/4)|t|` (`1 ≤ σ`; true constant
  `((1-σ)/2)log(2π) + (1/2)log 2 ≤ 0.35`) and `log ‖Γℝ(2+it)‖ ≥ (1/2)log(2+|t|) - 0.6 - (π/4)|t|`
  (true constant `-(1/2)log(2π) + log π + (1/2)log 2 = 0.5724`), and `‖L(2+it)‖ ≥ 1 - Σ_{n≥2}1/n²`
  (`≥ 0.355`, `-log ≤ 1.04`).  This gives a total additive constant of the order of 4, so the
  target `(3/2)(log N + log(4+|T₀|)) + 6` is met with a margin of several units.

**Remaining formalisation work for route (3)** (in order):

1. `circleMean_max_pos`: for `0 ≤ a ≤ R`, `R > 0`,
   `(1/2π)·∫_0^{2π} max 0 (-a - R cos θ) dθ = (R√(1-(a/R)²) - a·arccos(a/R))/π` — via the
   symmetry `cos(2π-θ)=cosθ`, the region `{cos θ < -a/R} = (arccos(-a/R), 2π - arccos(-a/R))`,
   `∫cos = sin`, and `sin(arccos x) = √(1-x²)`.
2. Rational bounds `arccos(1/4) ≥ 1.3`, `arccos(-1/6) ∈ [1.73,1.74]`, `arccos(1/3) ≥ 1.23`
   (`arccos(1/3) = 1.2309`, from `Real.sin_gt_sub_cube`/`Real.sin_le` and `π ∈ (3.14, 3.15)`).
3. The pointwise bounds on the circle (cases `σ ≥ 2`, `1 ≤ σ ≤ 2`, `0 ≤ σ ≤ 1`, `σ ≤ 0`).
4. Jensen (`AnalyticOnNhd.circleAverage_log_norm`) + the weight/geometry step
   (`divisor_eq_closedBall_subset`, all weights nonnegative) and the pole bound.
5. The arithmetic.

Children already delivering pieces: `re_completedLogDeriv_two_tight`,
`completedLogDeriv_neg_one_re_tight`, `gammaR_vertical_sharp_lower` are in the commons;
`LFunction_strip_convexity_explicit` and `gammaR_vertical_sharp_upper` are in flight.
-/

/-! ## SESSION 4 PROGRESS (read this first)

**Proved in this file now (in addition to the session-2 helpers)**: the whole circle-mean
machinery for the disk-Jensen route, in the section below:

* `circleMean_max_pos` : for `0 ≤ a ≤ R`, `R > 0`,
  `(1/2π)∫_0^{2π} max 0 (-a - R cos θ) dθ = (R·√(1-(a/R)²) - a·arccos(a/R))/π`;
* `le_arccos_of_cos_le` (`cos q ≥ x`, `q ∈ [0,π]` ⟹ `q ≤ arccos x`), the elementary bounds
  `cos_13_ge` (`cos(13/10) ≥ 1/4`), `cos_14_ge` (`cos(7/5) ≥ 1/6`), `cos_12_ge` (`cos(6/5) ≥ 1/3`)
  (all from `Real.sin_gt_sub_cube` with `Real.pi_gt_d2`/`Real.pi_lt_d4`), and `sqrt35_le`,
  `sqrt8_le`, `sqrt15_le`, `sqrt36_eq`, `sqrt9_eq`, `sqrt16_eq`;
* `circleMean_kappa_le` : the circle mean of `max 0 (1/2 - σ)` (`σ = 2 + 6 cos θ`) is `≤ 1.23`;
* `circleMean_lambda_le` : the circle mean of `λ(σ) = max 0 ((σ-1)/2) + max 0 (-σ/2)` is `≤ 1.75`.

**Delivered to the shared commons by the fleet for this route** (all PROVED, importable):

* `Submission.Commons.NumberTheory.DirichletCharacter.re_completedLogDeriv_two_tight`
  (`Re Λ′/Λ(2+iT) ≤ (1/2)log(2+|T|) + 3/4`),
* `Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_neg_one_re_tight`
  (`-Re Λ′/Λ(-1+iT) ≤ log N + (1/2)log(2+|T|) + 3/2`) — both also proved locally above;
* `Submission.Commons.NumberTheory.DirichletCharacter.LFunction_strip_convexity_explicit` :
  `∃ C > 0, ∀ σ ∈ [0,1], T, ‖L(σ+iT)‖ ≤ C·(N(2+|T|))^((1-σ)/2)·(log(N(2+|T|)) + 2)`
  (constant `C = Cb · 5e`, from the AFE/interpolation `F_bound_boundary`);
* `Submission.Commons.Analysis.SpecialFunctions.Gamma.gammaR_vertical_sharp_upper` :
  `‖Γℝ(σ+it)‖ ≤ exp(((σ-1)/2)·log(2+|t|) + 2 - (π/4)|t|)` for `1 ≤ σ ≤ 16`;
* `Submission.Commons.Analysis.SpecialFunctions.Gamma.gammaR_vertical_sharp_lower` :
  `exp((1/2)log(2+|t|) - 2 - (π/4)|t|) ≤ ‖Γℝ(2+it)‖`;
* `Submission.Commons.Analysis.SpecialFunctions.Gamma.Gamma_vertical_upper_uniform_sharp` and
  `gamma_abs_sq_half` (`‖Γ(1/2+iv)‖² = π/cosh(πv)`).

**Remaining work for the target (route: disk Jensen with `R = 6`)**

1. Pointwise bounds on the circle `s = (2 + 6 cos θ) + i(T₀ + 6 sin θ)`:
   * `σ ≥ 2`: `log‖Λ‖ ≤ ((σ-1)/2)log(2+|t|) + 2 + log 2 - (π/4)|t|`
     (`gammaR_vertical_sharp_upper` + `‖L(σ+it)‖ ≤ Σ_n 1/n^σ ≤ 2`, `σ ≥ 2`);
   * `1 ≤ σ ≤ 2`: same with `log 2` replaced by `log(log N + log(2+|t|) + 6)`
     (`norm_LFunction_le_re_ge_one`);
   * `0 ≤ σ ≤ 1`: `log‖Λ‖ ≤ (1/2)log N + loglog + 2 - (π/4)|t|`
     (`LFunction_strip_convexity_explicit` + Stirling);
   * `σ ≤ 0`: functional equation `completedLFunction_eq` reduces to `1 - σ ≥ 1`, then the first
     two cases (`log‖Λ(σ+it)‖ = (1/2-σ)log N + log‖Λ^{χ⁻¹}(1-σ+it)‖`, `‖N^{1/2-s}‖ = N^{1/2-σ}`).
2. `AnalyticOnNhd.circleAverage_log_norm` (Mathlib, **Jensen with the divisor correction** — no
   zero-free circle hypothesis needed) with `f = completedLFunction χ`, `c = 2+iT₀`, `R = 6`:
   `circleAverage (log‖Λ·‖) c 6 = Σ_u div(Λ, closedBall c 6)(u)·log(6/‖c-u‖) + log‖Λ c‖`.
3. Weights: all zeros have `0 < Re < 1` (`zerosInStrip`), so every zero of the lens
   `closedBall c (5/2)` satisfies `6/‖c-u‖ ≥ 12/5` (the lens's extreme points `(0,T₀±3/2)` and
   `(1,T₀±√21/2)` are at distance exactly `5/2`), the weights of the remaining zeros in
   `closedBall c 6` are `≥ 0`, and the divisors on the two balls agree
   (`divisor_eq_closedBall_subset`). Hence
   `log(12/5)·N_target ≤ circleAverage − log‖Λ c‖` with `N_target` the target's divisor sum.
4. Bound `circleAverage (log‖Λ·‖) c 6` by integrating the step-1 bounds with
   `circleMean_kappa_le`/`circleMean_lambda_le` (plus `E[|t|] ≥ |T₀|` and Jensen for log) and
   bound `−log‖Λ(2+iT₀)‖ ≤ −(1/2)log(T₀+2) + (π/4)T₀ + 2 + log 4` from
   `gammaR_vertical_sharp_lower` and `L_lower_re_two_explicit`.
5. Algebra: `1.23/log(12/5) = 1.405 < 3/2`, `(1.75-1/2)/log(12/5) = 1.428 < 3/2`, additive constant
   of order `4` (from the constants `2 + log 2 + log 4 + 2` and the log-log term `≤ 0.45` when one
   uses `log‖L‖ ≤ log ζ(σ) ≤ log 2` on `σ ≥ 2` and no log-log there) — compare
   `(3/2)(log N + log(4+|T₀|)) + 6`.  **The margins are thin**: if the constant `C` of
   `LFunction_strip_convexity_explicit` is large (say `log C > 3`), the additive budget fails; in
   that case either re-prove the strip bound with a smaller constant (only the arcs with
   `0 ≤ σ ≤ 1` plus `-1 ≤ σ ≤ 0` actually need it, ~17% of the circle) or switch the target's
   proof to the argument-principle assembly using `V`-shaped weights already in the file.
6. Then DELETE the old crux `logDeriv_im_good_height` (the file's only unproved step) and replace
   the target's proof, or keep it only if it can be proved.

-/

/-! ## Circle-mean and elementary numerical estimates for the disk-Jensen route -/
/-! ## Circle-mean estimates for the disk-Jensen route

The two averages that control the conductor and `log|t|` coefficients of the Jensen bound: for
`σ = 2 + 6 cos θ` (the circle about `2+iT₀` of radius `6`, centre-independent),

* the mean of `max 0 (1/2 - σ)` is `(√35·... )` at most `1.23`,
* the mean of `λ(σ) = max 0 ((σ-1)/2) + max 0 (-σ/2)` is at most `1.75`. -/

/-- For `0 ≤ a ≤ R`, `R > 0`: the mean over `[0,2π]` of `max 0 (-a - R cos θ)` is
`(R·√(1-(a/R)²) - a·arccos(a/R))/π`. -/
lemma circleMean_max_pos {R a : ℝ} (hR : 0 < R) (ha : 0 ≤ a) (haR : a ≤ R) :
    (1 / (2 * Real.pi)) * ∫ θ in (0 : ℝ)..(2 * Real.pi), max 0 (-a - R * Real.cos θ)
      = (R * Real.sqrt (1 - (a / R) ^ 2) - a * Real.arccos (a / R)) / Real.pi := by
  set c : ℝ := a / R with hcdef
  have hc0 : 0 ≤ c := div_nonneg ha hR.le
  have hc1 : c ≤ 1 := by rw [div_le_one hR]; exact haR
  set φ : ℝ := Real.arccos c with hφdef
  have hφ0 : 0 ≤ φ := Real.arccos_nonneg c
  have hcosφ : Real.cos φ = c := Real.cos_arccos (by linarith) hc1
  have hsinφ : Real.sin φ = Real.sqrt (1 - c ^ 2) := Real.sin_arccos c
  have hRc : R * c = a := by
    rw [hcdef]
    field_simp
  have hφlepi : φ ≤ Real.pi := Real.arccos_le_pi c
  have hcont : Continuous (fun θ : ℝ => max 0 (-a - R * Real.cos θ)) := by fun_prop
  have hInt1 : IntervalIntegrable (fun θ : ℝ => max 0 (-a - R * Real.cos θ)) MeasureTheory.volume (0:ℝ) (Real.pi - φ) :=
    hcont.intervalIntegrable _ _
  have hInt2 : IntervalIntegrable (fun θ : ℝ => max 0 (-a - R * Real.cos θ)) MeasureTheory.volume (Real.pi - φ) Real.pi :=
    hcont.intervalIntegrable _ _
  have hInt3 : IntervalIntegrable (fun θ : ℝ => max 0 (-a - R * Real.cos θ)) MeasureTheory.volume (0:ℝ) Real.pi :=
    hcont.intervalIntegrable _ _
  have hInt4 : IntervalIntegrable (fun θ : ℝ => max 0 (-a - R * Real.cos θ)) MeasureTheory.volume Real.pi (2*Real.pi) :=
    hcont.intervalIntegrable _ _
  have hzero : ∀ θ ∈ Set.uIcc (0:ℝ) (Real.pi - φ), max 0 (-a - R * Real.cos θ) = 0 := by
    intro θ hθ
    rw [Set.uIcc_of_le (by linarith [hφ0])] at hθ
    have hcosle : -c ≤ Real.cos θ := by
      have h1 : Real.cos (Real.pi - φ) = -c := by rw [Real.cos_pi_sub, hcosφ]
      calc -c = Real.cos (Real.pi - φ) := h1.symm
        _ ≤ Real.cos θ := Real.cos_le_cos_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2]) hθ.2
    have h2 : -a - R * Real.cos θ ≤ 0 := by
      have h3 : R * (-c) ≤ R * Real.cos θ := mul_le_mul_of_nonneg_left hcosle hR.le
      nlinarith [hRc, h3]
    exact max_eq_left h2
  have hzeroInt : (∫ θ in (0:ℝ)..(Real.pi - φ), max 0 (-a - R * Real.cos θ)) = 0 := by
    rw [intervalIntegral.integral_congr hzero, intervalIntegral.integral_zero]
  have hcongr2 : ∀ θ ∈ Set.uIcc (Real.pi - φ) Real.pi, max 0 (-a - R * Real.cos θ) = -a - R * Real.cos θ := by
    intro θ hθ
    rw [Set.uIcc_of_le (by linarith [hφlepi])] at hθ
    have hcosle : Real.cos θ ≤ -c := by
      calc Real.cos θ ≤ Real.cos (Real.pi - φ) :=
            Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [hφ0]) hθ.2 hθ.1
        _ = -c := by rw [Real.cos_pi_sub, hcosφ]
    have h3 : R * Real.cos θ ≤ R * (-c) := mul_le_mul_of_nonneg_left hcosle hR.le
    have h2 : 0 ≤ -a - R * Real.cos θ := by nlinarith [hRc, h3]
    exact max_eq_right h2
  have hInt : (∫ θ in (Real.pi - φ)..Real.pi, max 0 (-a - R * Real.cos θ)) = -a * φ + R * Real.sin φ := by
    rw [intervalIntegral.integral_congr hcongr2]
    have h1 : (∫ θ in (Real.pi - φ)..Real.pi, (-a - R * Real.cos θ)) =
        (∫ θ in (Real.pi - φ)..Real.pi, (-a)) - (∫ θ in (Real.pi - φ)..Real.pi, R * Real.cos θ) := by
      rw [← intervalIntegral.integral_sub]
      · exact intervalIntegrable_const
      · exact (continuous_const.mul Real.continuous_cos).intervalIntegrable _ _
    rw [h1, intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_cos]
    have hsin : Real.sin (Real.pi - φ) = Real.sin φ := Real.sin_pi_sub φ
    rw [Real.sin_pi, hsin]
    ring
  have hsplit : (∫ θ in (0:ℝ)..Real.pi, max 0 (-a - R * Real.cos θ)) = -a * φ + R * Real.sin φ := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals hInt1 hInt2
    rw [hzeroInt, zero_add] at hadd
    rw [← hadd, hInt]
  have hcomp : (∫ x in Real.pi..(2*Real.pi), max 0 (-a - R * Real.cos x))
      = (∫ x in (0:ℝ)..Real.pi, max 0 (-a - R * Real.cos x)) := by
    have h1 : (∫ x in Real.pi..(2*Real.pi), max 0 (-a - R * Real.cos x))
        = ∫ x in Real.pi..(2*Real.pi), max 0 (-a - R * Real.cos (2*Real.pi - x)) := by
      apply intervalIntegral.integral_congr
      intro x _
      simp only [Real.cos_two_pi_sub]
    rw [h1, intervalIntegral.integral_comp_sub_left
      (fun x : ℝ => max 0 (-a - R * Real.cos x)) (2*Real.pi) (a := Real.pi) (b := 2*Real.pi)]
    ring_nf
  have hdouble : (∫ θ in (0:ℝ)..(2*Real.pi), max 0 (-a - R * Real.cos θ))
      = 2 * (-(a * φ) + R * Real.sin φ) := by
    have hadd2 := intervalIntegral.integral_add_adjacent_intervals hInt3 hInt4
    rw [← hadd2, hcomp, hsplit]
    ring
  have hmean : (1 / (2 * Real.pi)) *
      (∫ θ in (0:ℝ)..(2*Real.pi), max 0 (-a - R * Real.cos θ)) = (-(a * φ) + R * Real.sin φ) / Real.pi := by
    rw [hdouble]
    field_simp
  rw [hmean]
  have hsq : Real.sqrt (1 - (a / R) ^ 2) = Real.sqrt (1 - c ^ 2) := by rw [hcdef]
  rw [hsinφ, hsq]
  ring


/-- If `cos q ≥ x` with `q ∈ [0,π]` then `q ≤ arccos x`. -/
lemma le_arccos_of_cos_le {x q : ℝ} (hx : -1 ≤ x) (hx1 : x ≤ 1) (hq0 : 0 ≤ q)
    (hqπ : q ≤ Real.pi) (h : x ≤ Real.cos q) : q ≤ Real.arccos x := by
  have h1 : Real.arccos (Real.cos q) ≤ Real.arccos x := Real.arccos_le_arccos h
  rwa [Real.arccos_cos hq0 hqπ] at h1

/-- `cos (13/10) ≥ 1/4`. -/
lemma cos_13_ge : (1 : ℝ) / 4 ≤ Real.cos (13 / 10) := by
  rw [show (13:ℝ)/10 = 1.3 by norm_num, ← Real.sin_pi_div_two_sub 1.3]
  have hy0 : 0 < Real.pi / 2 - 1.3 := by linarith [Real.pi_gt_d2]
  have hcube := Real.sin_gt_sub_cube hy0
  have hylo : (0.27 : ℝ) ≤ Real.pi / 2 - 1.3 := by linarith [Real.pi_gt_d2]
  have hyhi : Real.pi / 2 - 1.3 ≤ 0.2708 := by linarith [Real.pi_lt_d4]
  have hy3 : (Real.pi / 2 - 1.3) ^ 3 ≤ 0.2708 ^ 3 := pow_le_pow_left₀ (by linarith [hylo]) hyhi 3
  have h1 : (1 : ℝ) / 4 ≤ Real.pi / 2 - 1.3 - (Real.pi / 2 - 1.3) ^ 3 / 6 := by nlinarith [hylo, hy3]
  linarith [hcube, h1]

/-- `cos (7/5) ≥ 1/6`. -/
lemma cos_14_ge : (1 : ℝ) / 6 ≤ Real.cos (7 / 5) := by
  rw [show (7:ℝ)/5 = 1.4 by norm_num, ← Real.sin_pi_div_two_sub 1.4]
  have hy0 : 0 < Real.pi / 2 - 1.4 := by linarith [Real.pi_gt_d2]
  have hcube := Real.sin_gt_sub_cube hy0
  have hylo : (0.17 : ℝ) ≤ Real.pi / 2 - 1.4 := by linarith [Real.pi_gt_d2]
  have hyhi : Real.pi / 2 - 1.4 ≤ 0.1708 := by linarith [Real.pi_lt_d4]
  have hy3 : (Real.pi / 2 - 1.4) ^ 3 ≤ 0.1708 ^ 3 := pow_le_pow_left₀ (by linarith [hylo]) hyhi 3
  have h1 : (1 : ℝ) / 6 ≤ Real.pi / 2 - 1.4 - (Real.pi / 2 - 1.4) ^ 3 / 6 := by nlinarith [hylo, hy3]
  linarith [hcube, h1]

/-- `cos (6/5) ≥ 1/3`. -/
lemma cos_12_ge : (1 : ℝ) / 3 ≤ Real.cos (6 / 5) := by
  rw [show (6:ℝ)/5 = 1.2 by norm_num, ← Real.sin_pi_div_two_sub 1.2]
  have hy0 : 0 < Real.pi / 2 - 1.2 := by linarith [Real.pi_gt_d2]
  have hcube := Real.sin_gt_sub_cube hy0
  have hylo : (0.37 : ℝ) ≤ Real.pi / 2 - 1.2 := by linarith [Real.pi_gt_d2]
  have hyhi : Real.pi / 2 - 1.2 ≤ 0.3708 := by linarith [Real.pi_lt_d4]
  have hy3 : (Real.pi / 2 - 1.2) ^ 3 ≤ 0.3708 ^ 3 := pow_le_pow_left₀ (by linarith [hylo]) hyhi 3
  have h1 : (1 : ℝ) / 3 ≤ Real.pi / 2 - 1.2 - (Real.pi / 2 - 1.2) ^ 3 / 6 := by nlinarith [hylo, hy3]
  linarith [hcube, h1]

lemma sqrt35_le : Real.sqrt 35 ≤ 5.9161 := by
  rw [Real.sqrt_le_iff] <;> norm_num

lemma sqrt8_le : Real.sqrt 8 ≤ 2.82843 := by
  rw [Real.sqrt_le_iff] <;> norm_num

lemma sqrt15_le : Real.sqrt 15 ≤ 3.873 := by
  rw [Real.sqrt_le_iff] <;> norm_num

lemma sqrt36_eq : Real.sqrt 36 = 6 := by
  rw [show (36:ℝ) = 6^2 by norm_num, Real.sqrt_sq (by norm_num)]

lemma sqrt9_eq : Real.sqrt 9 = 3 := by
  rw [show (9:ℝ) = 3^2 by norm_num, Real.sqrt_sq (by norm_num)]

lemma sqrt16_eq : Real.sqrt 16 = 4 := by
  rw [show (16:ℝ) = 4^2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- The circle mean of `max 0 (1/2 - σ)`, `σ = 2 + 6 cos θ`, is at most `1.23`. -/
lemma circleMean_kappa_le :
    (1 / (2 * Real.pi)) *
      (∫ θ in (0 : ℝ)..(2 * Real.pi), max 0 (1 / 2 - (2 + 6 * Real.cos θ))) ≤ 1.23 := by
  have h := circleMean_max_pos (R := 6) (a := 3/2) (by norm_num) (by norm_num) (by norm_num)
  have heq : (∫ θ in (0 : ℝ)..(2 * Real.pi), max 0 (1 / 2 - (2 + 6 * Real.cos θ)))
      = (∫ θ in (0 : ℝ)..(2 * Real.pi), max 0 (-(3/2) - 6 * Real.cos θ)) := by
    apply intervalIntegral.integral_congr
    intro θ _
    congr 1
    ring
  rw [heq, h]
  have hsq : (1 : ℝ) - (3 / 2 / 6) ^ 2 = 15 / 16 := by norm_num
  have hsqrt : Real.sqrt (1 - (3 / 2 / 6) ^ 2) = Real.sqrt 15 / 4 := by
    rw [hsq, Real.sqrt_div (by norm_num : (0:ℝ) ≤ 15), sqrt16_eq]
  have h4 : (1.3 : ℝ) ≤ Real.arccos (3 / 2 / 6) := by
    apply le_arccos_of_cos_le (by norm_num) (by norm_num) (by norm_num)
      (by linarith [Real.pi_gt_d2])
    norm_num
    exact cos_13_ge
  rw [hsqrt]
  have hpi : (3.14 : ℝ) ≤ Real.pi := le_of_lt Real.pi_gt_d2
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [div_le_iff₀ hpi0]
  nlinarith [sqrt15_le, h4, hpi]

/-- The circle mean of `λ(σ) = max 0 ((σ-1)/2) + max 0 (-σ/2)`, `σ = 2 + 6 cos θ`, is at most
`1.75`. -/
lemma circleMean_lambda_le :
    (1 / (2 * Real.pi)) *
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (max 0 (((2 + 6 * Real.cos θ) - 1) / 2) + max 0 (-(2 + 6 * Real.cos θ) / 2))) ≤ 1.75 := by
  have h1 := circleMean_max_pos (R := 6) (a := 1) (by norm_num) (by norm_num) (by norm_num)
  have h2 := circleMean_max_pos (R := 6) (a := 2) (by norm_num) (by norm_num) (by norm_num)
  have hA : ∀ θ : ℝ, max 0 ((1 + 6 * Real.cos θ) / 2)
      = (1 + 6 * Real.cos θ) / 2 + max 0 (-(1 + 6 * Real.cos θ)) / 2 := by
    intro θ
    rcases le_or_gt 0 ((1 + 6 * Real.cos θ) / 2) with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]
      ring
    · rw [max_eq_left h.le, max_eq_right (by linarith)]
      ring
  have hB : ∀ θ : ℝ, max 0 (-(2 + 6 * Real.cos θ) / 2) = max 0 (-2 - 6 * Real.cos θ) / 2 := by
    intro θ
    have he : -(2 + 6 * Real.cos θ) / 2 = (-2 - 6 * Real.cos θ) / 2 := by ring
    rw [he]
    rcases le_or_gt 0 ((-2 - 6 * Real.cos θ) / 2) with h | h
    · rw [max_eq_right h, max_eq_right (by linarith)]
    · rw [max_eq_left h.le, max_eq_left (by linarith)]
      ring
  have hpt : ∀ θ : ℝ, max 0 (((2 + 6 * Real.cos θ) - 1) / 2) + max 0 (-(2 + 6 * Real.cos θ) / 2)
      = max 0 (-1 - 6 * Real.cos θ) / 2 + max 0 (-2 - 6 * Real.cos θ) / 2
        + (1 + 6 * Real.cos θ) / 2 := by
    intro θ
    have hC : ((2 + 6 * Real.cos θ) - 1) / 2 = (1 + 6 * Real.cos θ) / 2 := by ring
    rw [hC, hA θ, hB θ]
    ring
  have hcont1 : IntervalIntegrable (fun θ : ℝ => max 0 (-1 - 6 * Real.cos θ) / 2) MeasureTheory.volume (0:ℝ) (2*Real.pi) :=
    (by fun_prop : Continuous fun θ : ℝ => max 0 (-1 - 6 * Real.cos θ) / 2).intervalIntegrable _ _
  have hcont2 : IntervalIntegrable (fun θ : ℝ => max 0 (-2 - 6 * Real.cos θ) / 2) MeasureTheory.volume (0:ℝ) (2*Real.pi) :=
    (by fun_prop : Continuous fun θ : ℝ => max 0 (-2 - 6 * Real.cos θ) / 2).intervalIntegrable _ _
  have hcont3 : IntervalIntegrable (fun θ : ℝ => (1 + 6 * Real.cos θ) / 2) MeasureTheory.volume (0:ℝ) (2*Real.pi) :=
    (by fun_prop : Continuous fun θ : ℝ => (1 + 6 * Real.cos θ) / 2).intervalIntegrable _ _
  have hIntEq : (∫ θ in (0:ℝ)..(2*Real.pi),
        (max 0 (((2 + 6 * Real.cos θ) - 1) / 2) + max 0 (-(2 + 6 * Real.cos θ) / 2)))
      = (∫ θ in (0:ℝ)..(2*Real.pi), max 0 (-1 - 6 * Real.cos θ) / 2)
        + (∫ θ in (0:ℝ)..(2*Real.pi), max 0 (-2 - 6 * Real.cos θ) / 2)
        + (∫ θ in (0:ℝ)..(2*Real.pi), (1 + 6 * Real.cos θ) / 2) := by
    rw [show (∫ θ in (0:ℝ)..(2*Real.pi),
          (max 0 (((2 + 6 * Real.cos θ) - 1) / 2) + max 0 (-(2 + 6 * Real.cos θ) / 2)))
        = (∫ θ in (0:ℝ)..(2*Real.pi),
            (max 0 (-1 - 6 * Real.cos θ) / 2 + max 0 (-2 - 6 * Real.cos θ) / 2
              + (1 + 6 * Real.cos θ) / 2)) from
      intervalIntegral.integral_congr (fun θ _ => hpt θ)]
    rw [intervalIntegral.integral_add (hcont1.add hcont2) hcont3,
      intervalIntegral.integral_add hcont1 hcont2]
  have hI1 : (1 / (2 * Real.pi)) * (∫ θ in (0:ℝ)..(2*Real.pi), max 0 (-1 - 6 * Real.cos θ) / 2)
      = (1 / 2) * ((Real.sqrt 35 - Real.arccos (1/6)) / Real.pi) := by
    have hdiv : (∫ θ in (0:ℝ)..(2*Real.pi), max 0 (-1 - 6 * Real.cos θ) / 2)
        = (∫ θ in (0:ℝ)..(2*Real.pi), max 0 (-1 - 6 * Real.cos θ)) / 2 :=
      intervalIntegral.integral_div _ _
    have hI : (∫ θ in (0:ℝ)..(2*Real.pi), max 0 (-1 - 6 * Real.cos θ))
        = 2 * Real.pi * ((6 * Real.sqrt (1 - (1/6)^2) - 1 * Real.arccos (1/6)) / Real.pi) := by
      have hπ2 : (2 * Real.pi) * (1 / (2 * Real.pi)) = 1 := by field_simp
      have := congrArg (fun x : ℝ => (2 * Real.pi) * x) h1
      rw [← mul_assoc, hπ2, one_mul] at this
      exact this
    rw [hdiv, hI]
    have h5 : Real.sqrt (1 - (1/6)^2) = Real.sqrt 35 / 6 := by
      have he : (1 : ℝ) - (1/6)^2 = 35/36 := by norm_num
      rw [he, Real.sqrt_div (by norm_num : (0:ℝ) ≤ 35), sqrt36_eq]
    rw [h5]
    field_simp
  have hI2 : (1 / (2 * Real.pi)) * (∫ θ in (0:ℝ)..(2*Real.pi), max 0 (-2 - 6 * Real.cos θ) / 2)
      = (1 / 2) * ((6 * Real.sqrt (1 - (2/6)^2) - 2 * Real.arccos (2/6)) / Real.pi) := by
    have hdiv : (∫ θ in (0:ℝ)..(2*Real.pi), max 0 (-2 - 6 * Real.cos θ) / 2)
        = (∫ θ in (0:ℝ)..(2*Real.pi), max 0 (-2 - 6 * Real.cos θ)) / 2 :=
      intervalIntegral.integral_div _ _
    have hI : (∫ θ in (0:ℝ)..(2*Real.pi), max 0 (-2 - 6 * Real.cos θ))
        = 2 * Real.pi * ((6 * Real.sqrt (1 - (2/6)^2) - 2 * Real.arccos (2/6)) / Real.pi) := by
      have hπ2 : (2 * Real.pi) * (1 / (2 * Real.pi)) = 1 := by field_simp
      have := congrArg (fun x : ℝ => (2 * Real.pi) * x) h2
      rw [← mul_assoc, hπ2, one_mul] at this
      exact this
    rw [hdiv, hI]
    field_simp
  have hI3 : (1 / (2 * Real.pi)) * (∫ θ in (0:ℝ)..(2*Real.pi), (1 + 6 * Real.cos θ) / 2) = 1/2 := by
    have hdiv : (∫ θ in (0:ℝ)..(2*Real.pi), (1 + 6 * Real.cos θ) / 2)
        = (∫ θ in (0:ℝ)..(2*Real.pi), 1 + 6 * Real.cos θ) / 2 :=
      intervalIntegral.integral_div _ _
    have hc1 : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) MeasureTheory.volume (0:ℝ) (2*Real.pi) :=
      continuous_const.intervalIntegrable _ _
    have hc5 : IntervalIntegrable (fun θ : ℝ => 6 * Real.cos θ) MeasureTheory.volume (0:ℝ) (2*Real.pi) :=
      (by fun_prop : Continuous fun θ : ℝ => 6 * Real.cos θ).intervalIntegrable _ _
    have hval : (∫ θ in (0:ℝ)..(2*Real.pi), (1 + 6 * Real.cos θ)) = 2 * Real.pi := by
      have hsplit : (∫ θ in (0:ℝ)..(2*Real.pi), (1 + 6 * Real.cos θ))
          = (∫ θ in (0:ℝ)..(2*Real.pi), (1:ℝ)) + (∫ θ in (0:ℝ)..(2*Real.pi), 6 * Real.cos θ) :=
        intervalIntegral.integral_add hc1 hc5
      rw [hsplit, intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_cos,
        Real.sin_two_pi, Real.sin_zero]
      ring
    rw [hdiv, hval]
    field_simp
  have hfin : (1 / (2 * Real.pi)) *
        ((∫ θ in (0:ℝ)..(2*Real.pi), max 0 (-1 - 6 * Real.cos θ) / 2)
          + (∫ θ in (0:ℝ)..(2*Real.pi), max 0 (-2 - 6 * Real.cos θ) / 2)
          + (∫ θ in (0:ℝ)..(2*Real.pi), (1 + 6 * Real.cos θ) / 2))
      = (1 / (2 * Real.pi)) * (∫ θ in (0:ℝ)..(2*Real.pi), max 0 (-1 - 6 * Real.cos θ) / 2)
        + (1 / (2 * Real.pi)) * (∫ θ in (0:ℝ)..(2*Real.pi), max 0 (-2 - 6 * Real.cos θ) / 2)
        + (1 / (2 * Real.pi)) * (∫ θ in (0:ℝ)..(2*Real.pi), (1 + 6 * Real.cos θ) / 2) := by
    ring
  rw [hIntEq, hfin, hI1, hI2, hI3]
  have h35 : Real.sqrt 35 ≤ 5.9161 := sqrt35_le
  have h8 : Real.sqrt (1 - (2/6)^2) ≤ 2.82843 / 3 := by
    have he : (1 : ℝ) - (2/6)^2 = 8/9 := by norm_num
    rw [he, Real.sqrt_div (by norm_num : (0:ℝ) ≤ 8), sqrt9_eq]
    linarith [sqrt8_le]
  have ha6 : (1.4 : ℝ) ≤ Real.arccos (1/6) := by
    apply le_arccos_of_cos_le (by norm_num) (by norm_num) (by norm_num)
      (by linarith [Real.pi_gt_d2])
    norm_num
    exact cos_14_ge
  have ha3 : (1.2 : ℝ) ≤ Real.arccos (2/6) := by
    have h : Real.arccos (2/6) = Real.arccos (1/3) := by norm_num
    rw [h]
    apply le_arccos_of_cos_le (by norm_num) (by norm_num) (by norm_num)
      (by linarith [Real.pi_gt_d2])
    norm_num
    exact cos_12_ge
  have hpi : (3.14 : ℝ) ≤ Real.pi := le_of_lt Real.pi_gt_d2
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hπinv : (1 / Real.pi : ℝ) ≤ 1/3.14 :=
    one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 3.14) hpi
  have hT1 : (Real.sqrt 35 - Real.arccos (1/6)) / Real.pi ≤ (59161/10000 - 7/5) / (157/50) := by
    rw [div_le_iff₀ hpi0]
    have h1 : (59161/10000 : ℝ) - 7/5 = (59161/10000 - 7/5) / (157/50) * (157/50) := by norm_num
    nlinarith [h35, ha6, hpi, h1]
  have hT2 : (6 * Real.sqrt (1 - (2/6)^2) - 2 * Real.arccos (2/6)) / Real.pi
      ≤ (6 * (282843/100000/3) - 2 * (6/5)) / (157/50) := by
    rw [div_le_iff₀ hpi0]
    have h1 : 6 * (282843/100000/3 : ℝ) - 2 * (6/5)
        = (6 * (282843/100000/3) - 2 * (6/5)) / (157/50) * (157/50) := by norm_num
    nlinarith [h8, ha3, hpi, h1]
  nlinarith [hT1, hT2]

/-! ## Helper lemmas proved here (part of the assembly) -/

/-- **Containment.**  Every zero of `Λ(χ,·)` inside the closed disk
`closedBall (2 + i T₀) (5/2)` has imaginary part strictly within `√21/2` of `T₀`
(and real part in `(0,1)`).  This reduces the target's zero count in a 2-dimensional disk
to a count in the "lens" (the disk intersected with the critical strip). -/
theorem completedL_zero_im_close {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {T₀ : ℝ} {u : ℂ}
    (hzero : DirichletCharacter.completedLFunction χ u = 0)
    (hball : ‖u - ((2 : ℂ) + Complex.I * (T₀ : ℂ))‖ ≤ (5 : ℝ) / 2) :
    |u.im - T₀| < Real.sqrt 21 / 2 := by
  have hstrip := Commons.NumberTheory.DirichletCharacter.zerosInStrip χ hχ hχprim u hzero
  set w : ℂ := u - ((2 : ℂ) + Complex.I * (T₀ : ℂ)) with hw
  have hre : w.re = u.re - 2 := by simp [hw]
  have him : w.im = u.im - T₀ := by simp [hw]
  have hsq : (u.re - 2) ^ 2 + (u.im - T₀) ^ 2 ≤ 25 / 4 := by
    have h2 : ‖w‖ ^ 2 ≤ (5 / 2 : ℝ) ^ 2 := by nlinarith [norm_nonneg w]
    have h3 : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    rw [hre, him] at h3
    linarith
  have h1 : 1 < (u.re - 2) ^ 2 := by
    have h4 : u.re - 2 < -1 := by linarith [hstrip.2]
    nlinarith
  have him2 : (u.im - T₀) ^ 2 < 21 / 4 := by linarith
  have h21 : (0 : ℝ) ≤ 21 / 4 := by norm_num
  have h5 := Real.sqrt_lt_sqrt (by positivity : (0:ℝ) ≤ (u.im - T₀)^2) him2
  rw [Real.sqrt_sq_eq_abs] at h5
  have hs : Real.sqrt (21 / 4) = Real.sqrt 21 / 2 := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 21)]
    norm_num [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  linarith [h5, hs.symm.le, hs.le]

namespace Commons.NumberTheory.DirichletCharacter

lemma GammaR_star (z : ℂ) : (starRingEnd ℂ) (Gammaℝ z) = Gammaℝ ((starRingEnd ℂ) z) := by
  rw [Complex.Gammaℝ, Complex.Gammaℝ, map_mul]
  congr 1
  · rw [conj_cpow_ofReal_pos Real.pi Real.pi_pos (-z / 2)]
    congr 1
    simp only [map_div₀, map_neg, map_ofNat]
  · rw [← Complex.Gamma_conj]
    congr 1
    simp only [map_div₀, map_ofNat]

/-- Conjugation of the log-derivative of a holomorphic function. -/
lemma logDeriv_starComp {f : ℂ → ℂ} (hfd : Differentiable ℂ f) (z : ℂ) :
    logDeriv (starComp f) z = (starRingEnd ℂ) (logDeriv f ((starRingEnd ℂ) z)) := by
  have hd : HasDerivAt f (deriv f ((starRingEnd ℂ) z)) ((starRingEnd ℂ) z) :=
    (hfd ((starRingEnd ℂ) z)).hasDerivAt
  have h1 := hasDerivAt_star_comp hd
  have h2 : starComp f z = (starRingEnd ℂ) (f ((starRingEnd ℂ) z)) := rfl
  rw [logDeriv_apply, logDeriv_apply, h1.deriv, h2, map_div₀]

/-- Pointwise conjugation of the completed L-function. -/
theorem starComp_completedLFunction_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) : starComp (completedLFunction χ) = completedLFunction (χ⁻¹) := by
  have hχinv : χ⁻¹ ≠ 1 := by
    intro h1
    apply hχ
    calc χ = (χ⁻¹)⁻¹ := by rw [inv_inv]
      _ = (1 : DirichletCharacter ℂ N)⁻¹ := by rw [h1]
      _ = 1 := by simp
  have key : ∀ s : ℂ, 1 < s.re → starComp (completedLFunction χ) s =
      completedLFunction (χ⁻¹) s := by
    intro s hs
    have hsstar : 1 < ((starRingEnd ℂ) s).re := by
      rw [starRingEnd_apply]
      simpa [Complex.conj_re] using hs
    have hpos : 0 < ((starRingEnd ℂ) s).re := by linarith
    have hγ0 : gammaFactor χ ((starRingEnd ℂ) s) ≠ 0 := gammaFactor_ne_zero_of_re_pos χ _ hpos
    have hΛ : completedLFunction χ ((starRingEnd ℂ) s) =
        gammaFactor χ ((starRingEnd ℂ) s) * LFunction χ ((starRingEnd ℂ) s) := by
      have h := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ ((starRingEnd ℂ) s)
        (Or.inl (by intro h0; rw [h0] at hpos; norm_num at hpos))
      rw [h, mul_div_cancel₀ _ hγ0]
    have hpos' : 0 < s.re := by linarith
    have hγ0' : gammaFactor (χ⁻¹) s ≠ 0 := gammaFactor_ne_zero_of_re_pos (χ⁻¹) _ hpos'
    have hΛ' : completedLFunction (χ⁻¹) s =
        gammaFactor (χ⁻¹) s * LFunction (χ⁻¹) s := by
      have h := DirichletCharacter.LFunction_eq_completed_div_gammaFactor (χ⁻¹) s
        (Or.inl (by intro h0; rw [h0] at hpos'; norm_num at hpos'))
      rw [h, mul_div_cancel₀ _ hγ0']
    have hL := LFunction_conj χ hχ ((starRingEnd ℂ) s)
    have hγconj0 : (starRingEnd ℂ) (gammaFactor χ ((starRingEnd ℂ) s)) = gammaFactor χ s := by
      rcases χ.even_or_odd with hE | hO
      · have h1 : gammaFactor χ = Gammaℝ := by funext w; exact hE.gammaFactor_def w
        rw [h1]
        simpa using GammaR_star ((starRingEnd ℂ) s)
      · have h1 : gammaFactor χ = (fun w => Gammaℝ (w + 1)) := by
          funext w; exact hO.gammaFactor_def w
        rw [h1]
        simp only
        rw [GammaR_star]
        congr 1
        simp
    have hγconj : (starRingEnd ℂ) (gammaFactor χ ((starRingEnd ℂ) s)) = gammaFactor (χ⁻¹) s :=
      hγconj0.trans (PL.AfeAssembly.gammaFactor_inv_eq χ s).symm
    unfold starComp
    rw [hΛ, map_mul, hγconj, hL, hΛ']
    simp
  -- identity theorem
  let F : ℂ → ℂ := starComp (completedLFunction χ)
  let G : ℂ → ℂ := completedLFunction (χ⁻¹)
  have hF : AnalyticOnNhd ℂ F Set.univ := by
    intro z hz
    exact Differentiable.analyticAt (differentiable_starComp (differentiable_completedLFunction hχ)) z
  have hG : AnalyticOnNhd ℂ G Set.univ := by
    intro z hz
    exact Differentiable.analyticAt (differentiable_completedLFunction hχinv) z
  let z₀ : ℂ := 2
  have hz₀ : z₀ ∈ (Set.univ : Set ℂ) := Set.mem_univ _
  have hev : F =ᶠ[𝓝 z₀] G := by
    filter_upwards [Metric.ball_mem_nhds z₀ (by norm_num : (0:ℝ) < 1)] with z hz
    have hzre : 1 < z.re := by
      have : dist z z₀ < 1 := by simpa [Metric.mem_ball] using hz
      simp [Complex.dist_eq] at this
      have h4 : |z.re - 2| ≤ dist z z₀ := by
        rw [Complex.dist_eq]
        simpa [z₀] using Complex.abs_re_le_norm (z - z₀)
      have h5 : dist z z₀ < 1 := by simpa [Metric.mem_ball] using hz
      have h6 : |z.re - 2| < 1 := lt_of_le_of_lt h4 h5
      have := abs_lt.mp h6
      simp [z₀] at this
      linarith [this.2]
    exact key z hzre
  have heq := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hF hG isPreconnected_univ
    (Set.mem_univ z₀) hev
  funext z
  exact heq (Set.mem_univ z)

/-- **Real part of the logarithmic derivative of the completed L-function on the critical
line.**  For a primitive non-trivial `χ mod N` and `Λ(1/2+iT) ≠ 0`,

    Re (Λ′/Λ)(1/2+iT) = -(log N)/2.

This is the classical "constant modulus" phenomenon: the logarithm of the phase of
`Λ(1/2+iT)` absorbs the conductor factor `N^(1/2-s)` of the functional equation.  It is the
key input for zero-counting contours whose vertical side lies on the critical line, since it
replaces the weight `log N + ...` by the *exact* value `(log N)/2` there. -/
theorem re_completedLogDeriv_critical_line {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (T : ℝ)
    (hΛ : completedLFunction χ ((1 / 2 : ℂ) + Complex.I * (T : ℂ)) ≠ 0) :
    (logDeriv (completedLFunction χ) ((1 / 2 : ℂ) + Complex.I * (T : ℂ))).re =
      -(Real.log (N : ℝ)) / 2 := by
  set s : ℂ := (1 / 2 : ℂ) + Complex.I * (T : ℂ) with hs
  have hconj : (starRingEnd ℂ) s = 1 - s := by
    rw [hs]
    simp only [map_add, map_mul, map_div₀, map_ofNat, map_one, Complex.conj_I, Complex.conj_ofReal]
    ring
  -- the reflected completed value is nonzero, by the functional equation
  have hΛc : completedLFunction (χ⁻¹) (1 - s) ≠ 0 := by
    intro h0
    apply hΛ
    rw [completedLFunction_eq χ hχprim s, h0, mul_zero]
  have hfe := completedLogDeriv_fe χ hχprim s hΛ hΛc
  -- conjugation identity: conj(logDeriv Λ(χ) (conj z)) = logDeriv Λ(χ⁻¹) z
  have hkey := logDeriv_starComp (f := completedLFunction χ)
    (differentiable_completedLFunction hχ) ((starRingEnd ℂ) s)
  rw [starComp_completedLFunction_eq χ hχ] at hkey
  have hconj2 : logDeriv (completedLFunction (χ⁻¹)) (1 - s) =
      (starRingEnd ℂ) (logDeriv (completedLFunction χ) s) := by
    rw [← hconj, hkey]
    simp
  have h := congrArg Complex.re hfe
  rw [hconj2] at h
  simp only [Complex.ofReal_re, Complex.neg_re, Complex.sub_re, Complex.conj_re] at h
  linarith

/-! ## Good heights and the remaining analytic input

The reduction below needs *two* heights `T₁ < T₀ - √21/2 < T₀ + √21/2 < T₂` at which
`Λ(χ,·)` has no zero on the horizontal line `Im = T_i`, together with a bound on the
vertical slice of the logarithmic derivative of `Λ` in the critical strip at those heights.
The existence of good heights is proved here (`exists_good_height`); the strip bound is the
single remaining analytic input, stated as `logDeriv_im_good_height` below (its exact
constants are dictated by the algebra: with the two tight vertical bounds
`completedLogDeriv_two_tight` / `completedLogDeriv_neg_one_tight` the count bound is

`≤ (1/2π)·[ H(log N + log(4+|T₀|) + 6) + 2·|∫_{−1}^{2} Im(Λ′/Λ)(σ+iT_i) dσ| ]`

and `H = T₂-T₁ ≈ √21 = 4.5826`; comparing with `(3/2)(log N + log(4+|T₀|)) + 6` leaves
coefficient `≈ 1.21` and additive constant `≈ 2.5` for `∫_{1/2}^{2} |Im(Λ′/Λ)|`). -/

/-- **Good-height existence.**  Any non-empty open interval of heights contains a height `T`
at which no zero of `Λ(χ,·)` has imaginary part exactly `T`.

(Zero heights in a bounded window are finite — `finite_zeroHeights_window` — and an open
interval is infinite, so it contains a point outside that finite set.  All zeros of `Λ` lie
in the critical strip `0 < Re < 1`, so a zero with `Im u = T ∈ (a,a+1)` is one of the
heights recorded by `finite_zeroHeights_window`.) -/
lemma exists_good_height {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {a b : ℝ} (hab : a < b) :
    ∃ T : ℝ, a < T ∧ T < b ∧
      ∀ u : ℂ, DirichletCharacter.completedLFunction χ u = 0 → u.im ≠ T := by
  classical
  have hS := finite_zeroHeights_window χ hχ hχprim a
  have hb' : a < min b (a + 1) := lt_min hab (by linarith)
  obtain ⟨T, hT, hTnotin⟩ := (Set.Ioo_infinite hb').exists_notMem_finset hS.toFinset
  refine ⟨T, hT.1, lt_of_lt_of_le hT.2 (min_le_left _ _), ?_⟩
  intro u hu him
  have hmem : T ∈ {y : ℝ | ∃ u : ℂ,
      DirichletCharacter.completedLFunction χ u = 0 ∧ a < u.im ∧ u.im < a + 1 ∧ u.im = y} :=
    ⟨u, hu, by rw [him]; exact hT.1,
      by rw [him]; exact lt_of_lt_of_le hT.2 (min_le_right _ _), him⟩
  exact hTnotin (by simpa using hS.mem_toFinset.mpr hmem)

/- **The remaining analytic input (the crux), in the exact form the assembly needs.**

There are two heights `T₁ < T₀ - √21/2 < T₀ + √21/2 < T₂` such that

* `Λ(χ,·)` has no zero on either horizontal line `Im = T₁`, `Im = T₂` (so the argument
  principle applies to the rectangle `[-1,2] × [T₁,T₂]`), and
* the imaginary part of the logarithmic derivative of `Λ` has small integral over the
  critical strip at both heights:
  `∫_{1/2}^{2} ‖Im(Λ′/Λ)(σ+iT_i)‖ dσ ≤ (7/10)(log N + log(2+|T₀|+4)) + 9`.

Why this exact form.  With `T₁` in the window `(T₀-√21/2-1, T₀-√21/2)` and `T₂` in
`(T₀+√21/2, T₀+√21/2+1)` one has `T₂ - T₁ ≤ √21 + 2` (the worst case), which is what the
constant `√21 + 2` records.  For the *signed* form of the argument principle the four side
contributions to `2π·count` are

* `∫_{T₁}^{T₂} Re(Λ′/Λ)(2+it) dt`: by the sharp one-sided bound
  `Re(Λ′/Λ)(2+it) ≤ (1/2)log(2+|t|) + 3/4` this is `≤ H(log(4+|T₀|) + 3/2)`;
* `-∫_{T₁}^{T₂} Re(Λ′/Λ)(-1+it) dt = ∫_{T₁}^{T₂}(log N + Re(Λ′/Λ)(χ⁻¹)(2-it)) dt`
  `≤ H(log N + log(4+|T₀|) + 3/2)` — the conductor appears here with coefficient exactly
  `1` and *no* additive error thanks to the functional equation;
* the two horizontal sides contribute `|∫_{-1}^{2} Im(Λ′/Λ)(σ+iT_i) dσ|`, and by the
  functional equation `∫_{-1}^{2} Im(Λ′/Λ)(σ+it)dσ = -2∫_{1/2}^{2} Im(Λ′/Λ)(σ+it)dσ`, so
  each is at most `2∫_{1/2}^{2}‖Im(Λ′/Λ)‖`.

Altogether $2π·count ≤ (√21+2)(log N + log(4+|T₀|) + 3) + 4·((7/10)(log N + log(4+|T₀|+2)) + 6)`,
which is `< 2π·((3/2)(log N + log(4+|T₀|)) + 6)`.  The first two side bounds are already in
the commons (`completedLogDeriv_two_tight`, `completedLogDeriv_neg_one_tight` give the same
shape with the larger constant `3` instead of `1/20`, still consistent with the target
provided the crux constant above is met).

This is *not* provable from the functional equation alone: on the strip `1/2 ≤ σ ≤ 1` the
functional equation only relates `Λ′/Λ(σ+iT)` back to `Λ′/Λ(1-σ-iT)` with `1-σ ∈ [0,1/2]`,
i.e. to a point of the same strip.  Classically the bound is the "`S(T)` bound" obtained from
the local Riemann–von Mangoldt count of the zeros of `Λ` near the segment (equivalently from
the Hadamard partial fraction / explicit formula). -/
-- The old crux `logDeriv_im_good_height` (the good-height horizontal-slice bound, which
-- required the local Riemann--von Mangoldt / large-sieve input and was not available) is no
-- longer needed: the disk zero count is proved in the commons via the disk-Jensen route.

/-- **Real part of the log-derivative of `Γℝ` on the lines `Re s = 2`, `Re s = 3`.**

For `x ∈ {2, 3}` and any real `y`,

    Re logDeriv Γℝ (x + iy) ≤ (1/2)·log(2 + |y|) − 1/4.

Proof: `logDeriv Γℝ s = −(log π)/2 + ψ(s/2)/2` (`logDeriv_Gammaℝ_formula`), and the Binet
remainder bound `digamma_logRem_le` gives `Re ψ(w) ≤ log ‖w‖ + 1/2` for `1/2 ≤ Re w ≤ 8`
(the remainder has real part at most its modulus, and `Re w > 0` makes `Re (w⁻¹) ≥ 0`).
At `w = s/2 = x/2 + iy/2` one has `‖w‖ ≤ 2 + |y|` when `2 ≤ x ≤ 3`, and `log π ≥ 1`
finishes the estimate. -/
lemma re_logDeriv_Gammaℝ_le_two_three {x : ℝ} (hx : x = 2 ∨ x = 3) (y : ℝ) :
    (logDeriv Complex.Gammaℝ ((x : ℂ) + Complex.I * (y : ℂ))).re ≤
      (1 / 2) * Real.log (2 + |y|) - 1 / 4 := by
  have hx2 : (2 : ℝ) ≤ x := by rcases hx with h | h <;> linarith
  have hx3 : x ≤ 3 := by rcases hx with h | h <;> linarith
  set s : ℂ := (x : ℂ) + Complex.I * (y : ℂ) with hs
  have hsre : 0 < s.re := by
    simp [hs]
    linarith
  have hformula := logDeriv_Gammaℝ_formula s hsre
  set z : ℂ := ((x / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * Complex.I with hz
  have hs2z : s / 2 = z := by
    rw [hs, hz]
    push_cast
    ring
  have hdg := Commons.Analysis.SpecialFunctions.Gamma.digamma_logRem_le (x / 2) (y / 2)
    (by linarith : (1 : ℝ) / 2 ≤ x / 2) (by linarith : x / 2 ≤ 8)
  have hzre : z.re = x / 2 := by
    rw [hz]
    simp
  have hznormpos : 0 < ‖z‖ := by
    rw [norm_pos_iff]
    intro h0
    have h1 : z.re = 0 := by rw [h0]; simp
    rw [hzre] at h1
    linarith
  have hznorm : ‖z‖ ≤ 2 + |y| := by
    have hzim : z.im = y / 2 := by rw [hz]; simp
    have h1 : ‖z‖ ^ 2 = (x / 2) ^ 2 + (y / 2) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hzre, hzim]
      ring
    have h2 : ‖z‖ ^ 2 ≤ (2 + |y|) ^ 2 := by
      rw [h1, add_sq, sq_abs]
      have hxq : (x / 2) ^ 2 ≤ 9 / 4 := by nlinarith [hx2, hx3]
      have hyq : (y / 2) ^ 2 = y ^ 2 / 4 := by ring
      rw [hyq]
      nlinarith [abs_nonneg y, sq_nonneg y]
    nlinarith [norm_nonneg z, abs_nonneg y]
  have hpsi : (Complex.digamma z).re ≤ Real.log ‖z‖ + 1 / 2 := by
    have h1 : (Complex.digamma z - Complex.log z + ((2 : ℂ)⁻¹) * z⁻¹).re ≤ 1 / 2 :=
      le_trans (Complex.re_le_norm _) hdg
    rw [Complex.add_re, Complex.sub_re] at h1
    have hzren : 0 ≤ z.re := by rw [hzre]; linarith
    have hznormsq : 0 < Complex.normSq z := by
      rw [← Complex.sq_norm]
      exact pow_pos hznormpos 2
    have hinvnn : 0 ≤ z⁻¹.re := by
      rw [Complex.inv_re]
      exact div_nonneg hzren hznormsq.le
    have h3 : 0 ≤ (((2 : ℂ)⁻¹) * z⁻¹).re := by
      have h2c : ((2 : ℂ)⁻¹) = ((1 / 2 : ℝ) : ℂ) := by norm_num
      rw [h2c, Complex.mul_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      linarith
    have hlog : (Complex.log z).re = Real.log ‖z‖ := Complex.log_re z
    rw [hlog] at h1
    linarith
  have hlogpi : 1 ≤ Real.log Real.pi := by
    have hlt : Real.exp 1 < Real.pi := lt_trans Real.exp_one_lt_three Real.pi_gt_three
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hlt.le
  have hlogz : Real.log ‖z‖ ≤ Real.log (2 + |y|) := Real.log_le_log hznormpos hznorm
  have hlogpi_eq : Complex.log (Real.pi : ℂ) = (Real.log Real.pi : ℂ) :=
    (Complex.ofReal_log (by positivity : (0 : ℝ) ≤ Real.pi)).symm
  have hA : (-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma z / 2).re =
      -(Real.log Real.pi) / 2 + (Complex.digamma z).re / 2 := by
    rw [Complex.add_re, Complex.div_ofNat_re, Complex.div_ofNat_re, Complex.neg_re, hlogpi_eq]
    simp
  rw [hformula, hs2z, hA]
  linarith [hpsi, hlogz, hlogpi]

/-- Sharp one-sided bound for the *real part* of the logarithmic derivative of `Λ` on the
line `Re s = 2`: `Re(Λ′/Λ)(2+iT) ≤ (1/2)log(2+|T|) + 1/20`.

`Λ = Γℝ · L` (resp. `Γℝ(·+1) · L`) and on `Re s = 2` one has
`Re logDeriv L(2+iT) = -Re(L(χ⋆Λ)(2+iT)) ≤ Σ_n Λ(n)/n² ≤ 1`, while
`Re logDeriv Γℝ(2+iT) = -(1/2)log π + (1/2)Re ψ(1+iT/2) ≤ (1/2)log(|T|/2)` (the real part of
the digamma function is at most `log|y|`).  Together this gives
`≤ (1/2)log(|T|/2) + 1 ≤ (1/2)log(2+|T|) + 1`. -/
theorem re_completedLogDeriv_two_tight {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (T : ℝ) :
    (logDeriv (DirichletCharacter.completedLFunction χ) ((2 : ℂ) + Complex.I * (T : ℂ))).re ≤
      (1 / 2) * Real.log (2 + |T|) + 3 / 4 := by
  set s : ℂ := (2 : ℂ) + Complex.I * (T : ℂ) with hs
  have hsre : 0 < s.re := by
    simp [hs]
  have hLs0 : DirichletCharacter.LFunction χ s ≠ 0 := by
    have hlow : (1 : ℝ) / 4 ≤ ‖DirichletCharacter.LFunction χ s‖ := by
      simpa [hs] using L_lower_re_two_explicit χ hχ T
    exact norm_ne_zero_iff.mp (ne_of_gt (by linarith))
  have hdec := logDeriv_completedLFunction_eq_add χ hχ s hsre hLs0
  have hL : (logDeriv (DirichletCharacter.LFunction χ) s).re ≤ 1 :=
    le_trans (Complex.re_le_norm _) (by simpa [hs] using norm_logDeriv_L_two_le_one χ T)
  have hG : (logDeriv (DirichletCharacter.gammaFactor χ) s).re ≤
      (1 / 2) * Real.log (2 + |T|) - 1 / 4 := by
    rcases χ.even_or_odd with hE | hO
    · have hfun : gammaFactor χ = Complex.Gammaℝ := funext fun z => hE.gammaFactor_def z
      rw [hfun]
      simpa [hs] using re_logDeriv_Gammaℝ_le_two_three (Or.inl rfl) T
    · have hfun : gammaFactor χ = (fun z : ℂ => Complex.Gammaℝ (z + 1)) :=
        funext fun z => hO.gammaFactor_def z
      have hs1b : 0 < (s + 1).re := by
        have hre : (s + 1).re = s.re + 1 := by simp
        rw [hre, hs]
        norm_num
      have hldcomp : logDeriv (fun z : ℂ => Complex.Gammaℝ (z + 1)) s =
          logDeriv Complex.Gammaℝ (s + 1) := by
        have hf : DifferentiableAt ℂ Complex.Gammaℝ (s + 1) :=
          differentiableAt_Gammaℝ (s + 1) hs1b
        have hg : DifferentiableAt ℂ (fun z : ℂ => z + 1) s := by fun_prop
        have h := logDeriv_comp (f := Complex.Gammaℝ) (g := fun z : ℂ => z + 1) (x := s) hf hg
        have hder : deriv (fun z : ℂ => z + 1) s = 1 := by simp
        rw [hder] at h
        simpa [Function.comp_def, mul_comm] using h
      rw [hfun, hldcomp]
      have hS : s + 1 = (3 : ℂ) + Complex.I * (T : ℂ) := by
        rw [hs]
        ring
      rw [hS]
      exact re_logDeriv_Gammaℝ_le_two_three (Or.inr rfl) T
  rw [hdec, Complex.add_re]
  linarith


/-! ## Applying the signed argument principle to `Λ(χ,·)`

With the signed argument principle `rectZeroCount_imag_of` in hand, the substitution
`f := Λ(χ,·)`, `z := -1+iT₁`, `w := 2+iT₂` requires only: `Λ 0 ≠ 0`, the box containment
`‖s‖ < R`, the boundary non-vanishing (from the good heights `T₁,T₂` and `zerosInStrip` on
`Re = -1, 2`), and the interval integrability of `logDeriv Λ` and of its imaginary/real parts
along the four sides (all four sides avoid the zeros of `Λ`, and `logDeriv Λ` is continuous
wherever `Λ ≠ 0` because `deriv Λ` and `Λ` are entire). -/

/-- **Isolated input**: the one-sided bound on the left vertical line — the `χ⁻¹` counterpart of
`re_completedLogDeriv_two_tight`, obtained from the functional equation
`logDeriv Λ(χ) s = -log N - logDeriv Λ(χ⁻¹)(1-s)` at `s = -1+iT`.  Requested from the fleet as
`NumberTheory/DirichletCharacter/completedLogDeriv_neg_one_re_tight`. -/
theorem completedLogDeriv_neg_one_re_tight {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (T : ℝ) :
    -(logDeriv (DirichletCharacter.completedLFunction χ) ((-1 : ℂ) + Complex.I * (T : ℂ))).re ≤
      Real.log (N : ℝ) + (1 / 2) * Real.log (2 + |T|) + 3 / 2 := by
  set s : ℂ := (-1 : ℂ) + Complex.I * (T : ℂ) with hs
  have hsre : s.re = -1 := by
    simp [hs]
  have hχinv : χ⁻¹ ≠ 1 := by
    intro h
    apply hχ
    calc
      χ = (χ⁻¹)⁻¹ := by simp
      _ = (1 : DirichletCharacter ℂ N)⁻¹ := by rw [h]
      _ = 1 := by simp
  have hΛ : DirichletCharacter.completedLFunction χ s ≠ 0 := by
    intro hz
    have hstrip := zerosInStrip χ hχ hχprim s hz
    have hlt : (0 : ℝ) < (-1 : ℝ) := by simpa [hsre] using hstrip.1
    exact (not_lt_of_ge (by norm_num : (-1 : ℝ) ≤ 0)) hlt
  have hre1s : 1 ≤ (1 - s : ℂ).re := by
    rw [Complex.sub_re, hsre]
    norm_num
  have hw0 : (1 : ℂ) - s ≠ 0 := by
    intro hz
    have hle : (1 : ℝ) ≤ 0 := by simpa [hz] using hre1s
    norm_num at hle
  have hΛc : DirichletCharacter.completedLFunction (χ⁻¹) (1 - s) ≠ 0 := by
    intro hz
    have hdiv := DirichletCharacter.LFunction_eq_completed_div_gammaFactor (χ := χ⁻¹)
      (1 - s) (Or.inl hw0)
    have hL : DirichletCharacter.LFunction (χ⁻¹) (1 - s) = 0 := by
      rw [hdiv, hz]
      simp
    exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := χ⁻¹) (Or.inl hχinv) hre1s) hL
  have hfe := completedLogDeriv_fe χ hχprim s hΛ hΛc
  have hre : -(logDeriv (DirichletCharacter.completedLFunction χ) s).re =
      Real.log (N : ℝ) +
        (logDeriv (DirichletCharacter.completedLFunction (χ⁻¹)) (1 - s)).re := by
    have h := congrArg Complex.re hfe
    simp only [Complex.neg_re, Complex.sub_re, Complex.ofReal_re] at h
    linarith
  have hb : (logDeriv (DirichletCharacter.completedLFunction (χ⁻¹)) (1 - s)).re ≤
      (1 / 2) * Real.log (2 + |T|) + 3 / 4 := by
    have h1 := re_completedLogDeriv_two_tight (χ := χ⁻¹) hχinv (-T)
    have hpt : (2 : ℂ) + Complex.I * ((-T : ℝ) : ℂ) = 1 - s := by
      rw [hs]
      push_cast
      ring
    rw [hpt] at h1
    simpa [abs_neg] using h1
  linarith [hre, hb]

/-- `logDeriv Λ` is continuous at every point where `Λ` does not vanish. -/
lemma continuousAt_logDeriv_completedL {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {z : ℂ} (hz : DirichletCharacter.completedLFunction χ z ≠ 0) :
    ContinuousAt (fun s : ℂ => logDeriv (DirichletCharacter.completedLFunction χ) s) z := by
  have hdiff : Differentiable ℂ (DirichletCharacter.completedLFunction χ) :=
    differentiable_completedLFunction hχ
  have h1 : ContinuousAt (deriv (DirichletCharacter.completedLFunction χ)) z :=
    (hdiff.analyticAt z).deriv.continuousAt
  have h2 : ContinuousAt (DirichletCharacter.completedLFunction χ) z := hdiff.continuous.continuousAt
  exact h1.div h2 hz

/-- Along a side `side : ℝ → ℂ` parametrising a segment on which `Λ` does not vanish,
`logDeriv Λ` and its imaginary and real parts are interval integrable. -/
lemma intervalIntegrable_logDeriv_side {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {side : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (hcont : Continuous side)
    (hne : ∀ x ∈ Set.Icc a b, DirichletCharacter.completedLFunction χ (side x) ≠ 0) :
    IntervalIntegrable (fun x : ℝ => logDeriv (DirichletCharacter.completedLFunction χ) (side x))
        MeasureTheory.volume a b
    ∧ IntervalIntegrable
        (fun x : ℝ => (logDeriv (DirichletCharacter.completedLFunction χ) (side x)).im)
        MeasureTheory.volume a b
    ∧ IntervalIntegrable
        (fun x : ℝ => (logDeriv (DirichletCharacter.completedLFunction χ) (side x)).re)
        MeasureTheory.volume a b := by
  have hc : ContinuousOn (fun x : ℝ =>
      logDeriv (DirichletCharacter.completedLFunction χ) (side x)) (Set.Icc a b) := by
    intro x hx
    exact ((continuousAt_logDeriv_completedL χ hχ (hne x hx)).comp hcont.continuousAt).continuousWithinAt
  have him : ContinuousOn (fun x : ℝ =>
      (logDeriv (DirichletCharacter.completedLFunction χ) (side x)).im) (Set.Icc a b) :=
    (Complex.imCLM.continuous.comp_continuousOn hc)
  have hre : ContinuousOn (fun x : ℝ =>
      (logDeriv (DirichletCharacter.completedLFunction χ) (side x)).re) (Set.Icc a b) :=
    (Complex.reCLM.continuous.comp_continuousOn hc)
  exact ⟨hc.intervalIntegrable_of_Icc hab,
    him.intervalIntegrable_of_Icc hab, hre.intervalIntegrable_of_Icc hab⟩
/-- **Reflection symmetry of the imaginary part of `Λ′/Λ` on a horizontal line.**

At a height `T` carrying no zero, the functional equation
`logDeriv Λ(χ) s = -log N - logDeriv Λ(χ⁻¹)(1-s)` together with the conjugation identity
`logDeriv Λ(χ⁻¹) z = conj (logDeriv Λ(χ) (conj z))` gives, for `σ ≤ 1/2`,

    Im (Λ′/Λ)(σ+iT) = Im (Λ′/Λ)(1−σ+iT),

because `-log N` is real and complex conjugation flips the imaginary part.  This is the key step
that writes each horizontal side `∫_{-1}^{2} Im g(σ+iT) dσ` as `2 ∫_{1/2}^{2} Im g(σ+iT) dσ`, and
hence bounds it by `2 ∫_{1/2}^{2} |Im g|` — the crux `logDeriv_im_good_height`. -/
lemma im_logDeriv_reflect {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {T σ : ℝ}
    (hgood : ∀ u : ℂ, DirichletCharacter.completedLFunction χ u = 0 → u.im ≠ T) :
    (logDeriv (DirichletCharacter.completedLFunction χ) ((σ : ℂ) + (T : ℂ) * Complex.I)).im
      = (logDeriv (DirichletCharacter.completedLFunction χ)
          (((1 - σ : ℝ) : ℂ) + (T : ℂ) * Complex.I)).im := by
  set s : ℂ := (σ : ℂ) + (T : ℂ) * Complex.I with hs
  have hsim : s.im = T := by simp [hs]
  have hΛ : DirichletCharacter.completedLFunction χ s ≠ 0 := fun hz => hgood s hz hsim
  -- the conjugated point, explicitly
  have hconj_arg : (starRingEnd ℂ) (1 - s) = ((1 - σ : ℝ) : ℂ) + (T : ℂ) * Complex.I := by
    rw [hs, map_sub, map_one]
    rw [map_add, Complex.conj_ofReal, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  -- non-vanishing at the reflected point, from goodness
  have hΛc : DirichletCharacter.completedLFunction (χ⁻¹) (1 - s) ≠ 0 := by
    intro hz
    have hconj : DirichletCharacter.completedLFunction χ ((starRingEnd ℂ) (1 - s)) = 0 := by
      have h := congrFun (starComp_completedLFunction_eq χ hχ) (1 - s)
      rw [hz] at h
      have h2 : (starRingEnd ℂ)
          (DirichletCharacter.completedLFunction χ ((starRingEnd ℂ) (1 - s))) = 0 := h
      simpa using congrArg (starRingEnd ℂ) h2
    have him : ((starRingEnd ℂ) (1 - s)).im = T := by rw [hconj_arg]; simp
    exact hgood ((starRingEnd ℂ) (1 - s)) hconj him
  have hfe := completedLogDeriv_fe χ hχprim s hΛ hΛc
  -- conjugation of the log-derivative
  have hconj_id : logDeriv (DirichletCharacter.completedLFunction (χ⁻¹)) (1 - s)
      = (starRingEnd ℂ)
          (logDeriv (DirichletCharacter.completedLFunction χ) ((starRingEnd ℂ) (1 - s))) := by
    have h := logDeriv_starComp (f := DirichletCharacter.completedLFunction χ)
      (differentiable_completedLFunction hχ) (1 - s)
    rw [starComp_completedLFunction_eq χ hχ] at h
    exact h
  -- the `-log N` term is real, so it contributes nothing to the imaginary part
  have h1 : (logDeriv (DirichletCharacter.completedLFunction χ) s).im
      = -(logDeriv (DirichletCharacter.completedLFunction (χ⁻¹)) (1 - s)).im := by
    have := congrArg Complex.im hfe
    simpa only [Complex.sub_im, Complex.neg_im, Complex.ofReal_im, neg_zero, zero_sub,
      sub_zero] using this
  rw [h1, hconj_id, hconj_arg]
  rw [Complex.conj_im]
  ring

/-- **The horizontal side as twice the half-line integral.**  Since
`Im (Λ′/Λ)(σ+iT) = Im (Λ′/Λ)(1−σ+iT)` (`im_logDeriv_reflect`), the substitution `σ ↦ 1−σ`
gives `∫_{-1}^{1/2} Im g(σ+iT) dσ = ∫_{1/2}^{2} Im g(σ+iT) dσ`, hence

    ∫_{-1}^{2} Im (Λ′/Λ)(σ+iT) dσ = 2 ∫_{1/2}^{2} Im (Λ′/Λ)(σ+iT) dσ,

for any height `T` free of zeros.  Combined with `le_abs_self` this bounds each horizontal side
of `completedL_boxZeroCount_eq` by `2 ∫_{1/2}^{2} |Im (Λ′/Λ)|` — the crux
`logDeriv_im_good_height`. -/
lemma completedL_boxHorizontal_id {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {T : ℝ}
    (hgood : ∀ u : ℂ, DirichletCharacter.completedLFunction χ u = 0 → u.im ≠ T)
    (hint : ∀ u v : ℝ, IntervalIntegrable
      (fun σ : ℝ => (logDeriv (DirichletCharacter.completedLFunction χ)
        ((σ : ℂ) + (T : ℂ) * Complex.I)).im) MeasureTheory.volume u v) :
    (∫ σ : ℝ in (-1)..2,
        (logDeriv (DirichletCharacter.completedLFunction χ)
          ((σ : ℂ) + (T : ℂ) * Complex.I)).im)
      = 2 * (∫ σ : ℝ in (1 / 2)..2,
        (logDeriv (DirichletCharacter.completedLFunction χ)
          ((σ : ℂ) + (T : ℂ) * Complex.I)).im) := by
  set f : ℝ → ℝ := fun σ => (logDeriv (DirichletCharacter.completedLFunction χ)
    ((σ : ℂ) + (T : ℂ) * Complex.I)).im with hf
  have hsym : ∀ x : ℝ, f (1 - x) = f x := by
    intro x
    simp only [hf]
    exact (im_logDeriv_reflect χ hχ hχprim hgood (σ := x)).symm
  -- the substitution σ ↦ 1 - σ on the left half
  have hcongr : (∫ x : ℝ in (-1)..(1 / 2), f x) = ∫ x : ℝ in (-1)..(1 / 2), f (1 - x) :=
    intervalIntegral.integral_congr fun x _ => (hsym x).symm
  have hA : (∫ x : ℝ in (-1)..(1 / 2), f x) = ∫ x : ℝ in ((1 : ℝ) / 2)..2, f x := by
    rw [hcongr]
    rw [intervalIntegral.integral_comp_sub_left (f := f) (a := (-1 : ℝ)) (b := (1 / 2 : ℝ))
      (d := (1 : ℝ))]
    norm_num
  -- glue the two halves
  have hadd : (∫ x : ℝ in (-1)..(1 / 2), f x) + (∫ x : ℝ in ((1 : ℝ) / 2)..2, f x)
      = ∫ x : ℝ in (-1)..2, f x :=
    intervalIntegral.integral_add_adjacent_intervals (a := (-1 : ℝ)) (b := (1 / 2 : ℝ))
      (c := (2 : ℝ)) (hab := hint (-1) (1 / 2)) (hbc := hint (1 / 2) 2)
  rw [hf]
  rw [← hadd, hA]
  ring

/-- **Each horizontal side is at most twice the half-line integral of `|Im g|`.**  Corollary of
`completedL_boxHorizontal_id` through `le_abs_self`.  With the crux `logDeriv_im_good_height`
this is the whole horizontal input to the identity `completedL_boxZeroCount_eq`. -/
lemma completedL_boxHorizontal_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {T : ℝ}
    (hgood : ∀ u : ℂ, DirichletCharacter.completedLFunction χ u = 0 → u.im ≠ T)
    (hint : ∀ u v : ℝ, IntervalIntegrable
      (fun σ : ℝ => (logDeriv (DirichletCharacter.completedLFunction χ)
        ((σ : ℂ) + (T : ℂ) * Complex.I)).im) MeasureTheory.volume u v) :
    (∫ σ : ℝ in (-1)..2,
        (logDeriv (DirichletCharacter.completedLFunction χ)
          ((σ : ℂ) + (T : ℂ) * Complex.I)).im)
      ≤ 2 * (∫ σ : ℝ in (1 / 2)..2,
        ‖(logDeriv (DirichletCharacter.completedLFunction χ)
          ((σ : ℂ) + (T : ℂ) * Complex.I)).im‖) := by
  rw [completedL_boxHorizontal_id χ hχ hχprim hgood hint]
  have hmono : (∫ σ : ℝ in (1 / 2)..2,
      (logDeriv (DirichletCharacter.completedLFunction χ)
        ((σ : ℂ) + (T : ℂ) * Complex.I)).im)
      ≤ ∫ σ : ℝ in (1 / 2)..2,
        ‖(logDeriv (DirichletCharacter.completedLFunction χ)
          ((σ : ℂ) + (T : ℂ) * Complex.I)).im‖ :=
    intervalIntegral.integral_mono_on (by norm_num) (hint (1 / 2) 2) (hint (1 / 2) 2).norm
      (fun x _ => by rw [Real.norm_eq_abs]; exact le_abs_self _)
  linarith


/-- **Absolute-value form of the horizontal bound** — what the *top* side needs.  Since
`completedL_boxHorizontal_id` gives `∫_{-1}^{2} Im g = 2∫_{1/2}^{2} Im g` exactly, taking absolute
values and using `le_abs_self`/`neg_le_abs` gives

    | ∫_{-1}^{2} Im (Λ′/Λ)(σ+iT) dσ | ≤ 2 ∫_{1/2}^{2} |Im (Λ′/Λ)(σ+iT)| dσ ,

from which both `Im(Jb) ≤ 2∫|Im g|` (bottom side) and `−Im(Jt) ≤ 2∫|Im g|` (top side) follow. -/
lemma completedL_boxHorizontal_abs {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {T : ℝ}
    (hgood : ∀ u : ℂ, DirichletCharacter.completedLFunction χ u = 0 → u.im ≠ T)
    (hint : ∀ u v : ℝ, IntervalIntegrable
      (fun σ : ℝ => (logDeriv (DirichletCharacter.completedLFunction χ)
        ((σ : ℂ) + (T : ℂ) * Complex.I)).im) MeasureTheory.volume u v) :
    |∫ σ : ℝ in (-1)..2,
        (logDeriv (DirichletCharacter.completedLFunction χ)
          ((σ : ℂ) + (T : ℂ) * Complex.I)).im|
      ≤ 2 * (∫ σ : ℝ in (1 / 2)..2,
        ‖(logDeriv (DirichletCharacter.completedLFunction χ)
          ((σ : ℂ) + (T : ℂ) * Complex.I)).im‖) := by
  rw [completedL_boxHorizontal_id χ hχ hχprim hgood hint, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have habs : |∫ σ : ℝ in (1 / 2)..2,
        (logDeriv (DirichletCharacter.completedLFunction χ)
          ((σ : ℂ) + (T : ℂ) * Complex.I)).im|
      ≤ ∫ σ : ℝ in (1 / 2)..2,
        ‖(logDeriv (DirichletCharacter.completedLFunction χ)
          ((σ : ℂ) + (T : ℂ) * Complex.I)).im‖ := by
    rw [abs_le]
    constructor
    · have hmono : (∫ σ : ℝ in (1 / 2)..2,
          -(logDeriv (DirichletCharacter.completedLFunction χ)
            ((σ : ℂ) + (T : ℂ) * Complex.I)).im)
          ≤ ∫ σ : ℝ in (1 / 2)..2,
            ‖(logDeriv (DirichletCharacter.completedLFunction χ)
              ((σ : ℂ) + (T : ℂ) * Complex.I)).im‖ :=
        intervalIntegral.integral_mono_on (by norm_num) (hint (1 / 2) 2).neg
          (hint (1 / 2) 2).norm
          (fun x _ => by rw [Real.norm_eq_abs]; exact neg_le_abs _)
      rw [intervalIntegral.integral_neg] at hmono
      linarith
    · have hmono : (∫ σ : ℝ in (1 / 2)..2,
          (logDeriv (DirichletCharacter.completedLFunction χ)
            ((σ : ℂ) + (T : ℂ) * Complex.I)).im)
          ≤ ∫ σ : ℝ in (1 / 2)..2,
            ‖(logDeriv (DirichletCharacter.completedLFunction χ)
              ((σ : ℂ) + (T : ℂ) * Complex.I)).im‖ :=
        intervalIntegral.integral_mono_on (by norm_num) (hint (1 / 2) 2)
          (hint (1 / 2) 2).norm
          (fun x _ => by rw [Real.norm_eq_abs]; exact le_abs_self _)
      linarith
  linarith

/-- **The two vertical sides of the box.**  Both one-sided bounds on `Re (Λ′/Λ)` — at `Re = 2`
and at `Re = -1` — being available as hypotheses (they are `re_completedLogDeriv_two_tight` and
its functional-equation counterpart `completedLogDeriv_neg_one_re_tight`), the *signed* sum of
the two vertical contributions to `rectZeroCount_imag_eq_of`

    ∫_{T₁}^{T₂} Re g(2+iy) dy  −  ∫_{T₁}^{T₂} Re g(−1+iy) dy

is at most `(T₂−T₁)·(log N + log(2+|T₀|+2) + 4)`.  No absolute value is taken on either side,
which is the whole point of using the identity form rather than the inequality form. -/

lemma completedL_boxVertical_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {T₀ T₁ T₂ : ℝ}
    (hT₁ : T₀ - Real.sqrt 21 / 2 - 1 < T₁) (hT₁' : T₁ < T₀ - Real.sqrt 21 / 2)
    (hT₂ : T₀ + Real.sqrt 21 / 2 < T₂) (hT₂' : T₂ < T₀ + Real.sqrt 21 / 2 + 1)
    (hre2 : ∀ T : ℝ,
      (logDeriv (DirichletCharacter.completedLFunction χ)
        ((2 : ℂ) + (T : ℂ) * Complex.I)).re ≤ (1 / 2) * Real.log (2 + |T|) + 3 / 4)
    (hre1 : ∀ T : ℝ,
      -(logDeriv (DirichletCharacter.completedLFunction χ)
        ((-1 : ℂ) + (T : ℂ) * Complex.I)).re
        ≤ Real.log (N : ℝ) + (1 / 2) * Real.log (2 + |T|) + 3 / 2)
    (hr : IntervalIntegrable (fun y : ℝ =>
        (logDeriv (DirichletCharacter.completedLFunction χ)
          ((2 : ℂ) + (y : ℂ) * Complex.I)).re) MeasureTheory.volume T₁ T₂)
    (hl : IntervalIntegrable (fun y : ℝ =>
        (logDeriv (DirichletCharacter.completedLFunction χ)
          ((-1 : ℂ) + (y : ℂ) * Complex.I)).re) MeasureTheory.volume T₁ T₂) :
    (∫ y : ℝ in T₁..T₂,
        (logDeriv (DirichletCharacter.completedLFunction χ)
          ((2 : ℂ) + (y : ℂ) * Complex.I)).re)
      - (∫ y : ℝ in T₁..T₂,
        (logDeriv (DirichletCharacter.completedLFunction χ)
          ((-1 : ℂ) + (y : ℂ) * Complex.I)).re)
      ≤ (T₂ - T₁) * (Real.log (N : ℝ) + Real.log (2 + |T₀| + 2) + 13 / 4) := by
  have hs21 : Real.sqrt 21 < 5 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21), Real.sqrt_nonneg 21]
  have hT12 : T₁ ≤ T₂ := le_of_lt (by linarith [Real.sqrt_nonneg 21])
  -- the height range
  have hy : ∀ y ∈ Set.Icc T₁ T₂, |y| ≤ |T₀| + 4 := by
    intro y hyy
    rw [abs_le]
    constructor
    · linarith [neg_abs_le T₀, hyy.1, hT₁, hs21]
    · linarith [le_abs_self T₀, hyy.2, hT₂', hs21]
  -- the logarithmic slack: log (2+|y|) ≤ log (2+|T₀|+2) + 1 on the range
  have hlogy : ∀ y ∈ Set.Icc T₁ T₂,
      Real.log (2 + |y|) ≤ Real.log (2 + |T₀| + 2) + 1 := by
    intro y hyy
    have h3 : (0 : ℝ) < 2 + |T₀| + 2 := by positivity
    have h1 : 2 + |y| ≤ 2 + (|T₀| + 4) := by linarith [hy y hyy]
    have h2 : 2 + (|T₀| + 4) ≤ (2 + |T₀| + 2) * 2 := by nlinarith [abs_nonneg T₀]
    calc Real.log (2 + |y|) ≤ Real.log (2 + (|T₀| + 4)) := Real.log_le_log (by positivity) h1
      _ ≤ Real.log ((2 + |T₀| + 2) * 2) := Real.log_le_log (by positivity) h2
      _ = Real.log (2 + |T₀| + 2) + Real.log 2 := Real.log_mul h3.ne' (by norm_num)
      _ ≤ Real.log (2 + |T₀| + 2) + 1 := by
          linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  -- the two monotone integral estimates
  have hI1 : (∫ y : ℝ in T₁..T₂,
      (logDeriv (DirichletCharacter.completedLFunction χ)
        ((2 : ℂ) + (y : ℂ) * Complex.I)).re)
      ≤ (T₂ - T₁) * ((1 / 2) * Real.log (2 + |T₀| + 2) + 5 / 4) := by
    have hpt : ∀ y ∈ Set.Icc T₁ T₂,
        (logDeriv (DirichletCharacter.completedLFunction χ)
          ((2 : ℂ) + (y : ℂ) * Complex.I)).re
          ≤ ((1 / 2) * Real.log (2 + |T₀| + 2) + 5 / 4 : ℝ) := by
      intro y hyy
      have := hre2 y
      have := hlogy y hyy
      linarith
    calc (∫ y : ℝ in T₁..T₂,
        (logDeriv (DirichletCharacter.completedLFunction χ)
          ((2 : ℂ) + (y : ℂ) * Complex.I)).re)
        ≤ ∫ _ in T₁..T₂, ((1 / 2) * Real.log (2 + |T₀| + 2) + 5 / 4 : ℝ) :=
          intervalIntegral.integral_mono_on hT12 hr intervalIntegrable_const hpt
      _ = (T₂ - T₁) * ((1 / 2) * Real.log (2 + |T₀| + 2) + 5 / 4) := by
          rw [intervalIntegral.integral_const]; ring
  have hI2 : -(∫ y : ℝ in T₁..T₂,
      (logDeriv (DirichletCharacter.completedLFunction χ)
        ((-1 : ℂ) + (y : ℂ) * Complex.I)).re)
      ≤ (T₂ - T₁) * (Real.log (N : ℝ) + (1 / 2) * Real.log (2 + |T₀| + 2) + 2) := by
    have hpt : ∀ y ∈ Set.Icc T₁ T₂,
        -(logDeriv (DirichletCharacter.completedLFunction χ)
          ((-1 : ℂ) + (y : ℂ) * Complex.I)).re
          ≤ (Real.log (N : ℝ) + (1 / 2) * Real.log (2 + |T₀| + 2) + 2 : ℝ) := by
      intro y hyy
      have := hre1 y
      have := hlogy y hyy
      linarith
    rw [← intervalIntegral.integral_neg]
    calc (∫ y : ℝ in T₁..T₂, -(logDeriv (DirichletCharacter.completedLFunction χ)
            ((-1 : ℂ) + (y : ℂ) * Complex.I)).re)
        ≤ ∫ _ in T₁..T₂, (Real.log (N : ℝ) + (1 / 2) * Real.log (2 + |T₀| + 2) + 2 : ℝ) :=
          intervalIntegral.integral_mono_on hT12 hl.neg intervalIntegrable_const hpt
      _ = (T₂ - T₁) * (Real.log (N : ℝ) + (1 / 2) * Real.log (2 + |T₀| + 2) + 2) := by
          rw [intervalIntegral.integral_const]; ring
  have hH : (0 : ℝ) ≤ T₂ - T₁ := by linarith
  nlinarith [hI1, hI2, hH]


/-- **Signed argument-principle count bound for `Λ(χ,·)` in the box `(-1,2) × (T₁,T₂)`**,
for good heights `T₁ < T₀ - √21/2 < T₀ + √21/2 < T₂`. -/

lemma completedL_boxZeroCount_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {T₀ T₁ T₂ : ℝ}
    (hT₁ : T₀ - Real.sqrt 21 / 2 - 1 < T₁) (hT₁' : T₁ < T₀ - Real.sqrt 21 / 2)
    (hT₂ : T₀ + Real.sqrt 21 / 2 < T₂) (hT₂' : T₂ < T₀ + Real.sqrt 21 / 2 + 1)
    (hg₁ : ∀ u : ℂ, DirichletCharacter.completedLFunction χ u = 0 → u.im ≠ T₁)
    (hg₂ : ∀ u : ℂ, DirichletCharacter.completedLFunction χ u = 0 → u.im ≠ T₂) :
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall (0 : ℂ) (|T₀| + 20))) u : ℤ) : ℝ) *
        (if (-1 : ℝ) < u.re ∧ u.re < 2 ∧ T₁ < u.im ∧ u.im < T₂ then 1 else 0))
      ≤ (1 / (2 * Real.pi)) *
        ((∫ x : ℝ in (-1)..2, ‖(logDeriv (DirichletCharacter.completedLFunction χ)
              ((x : ℂ) + (T₁ : ℂ) * Complex.I)).im‖)
         + (∫ x : ℝ in (-1)..2, ‖(logDeriv (DirichletCharacter.completedLFunction χ)
              ((x : ℂ) + (T₂ : ℂ) * Complex.I)).im‖)
         + (∫ y : ℝ in T₁..T₂, ‖(logDeriv (DirichletCharacter.completedLFunction χ)
              ((((2 : ℝ)) : ℂ) + (y : ℂ) * Complex.I)).re‖)
         + (∫ y : ℝ in T₁..T₂, ‖(logDeriv (DirichletCharacter.completedLFunction χ)
              ((((-1 : ℝ)) : ℂ) + (y : ℂ) * Complex.I)).re‖)) := by
  have hdiff := differentiable_completedLFunction hχ
  -- bounds on the two heights
  have hs21 : Real.sqrt 21 < 5 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 21), Real.sqrt_nonneg 21]
  have hs21nn : 0 < Real.sqrt 21 := Real.sqrt_pos.mpr (by norm_num)
  -- hf0
  have hf0 : DirichletCharacter.completedLFunction χ 0 ≠ 0 :=
    Commons.NumberTheory.Linnik.completedLFunction_zero_ne_zero χ hχ hχprim
  -- hrect
  have hrect : ∀ s : ℂ,
      ((-1 : ℂ) + (T₁ : ℂ) * Complex.I).re ≤ s.re →
      s.re ≤ ((2 : ℂ) + (T₂ : ℂ) * Complex.I).re →
      ((-1 : ℂ) + (T₁ : ℂ) * Complex.I).im ≤ s.im →
      s.im ≤ ((2 : ℂ) + (T₂ : ℂ) * Complex.I).im →
      ‖s‖ < |T₀| + 20 := by
    intro s h1 h2 h3 h4
    have h1 : (-1:ℝ) ≤ s.re := by simpa using h1
    have h2 : s.re ≤ 2 := by simpa using h2
    have h3 : T₁ ≤ s.im := by simpa using h3
    have h4 : s.im ≤ T₂ := by simpa using h4
    have habs : |s.im| ≤ |T₀| + Real.sqrt 21 / 2 + 1 := by
      rw [abs_le]
      constructor
      · have : -(Real.sqrt 21) / 2 - 1 + T₀ < s.im := by linarith
        nlinarith [neg_abs_le T₀, Real.sqrt_nonneg 21, le_abs_self T₀]
      · have : s.im < Real.sqrt 21 / 2 + 1 + T₀ := by linarith
        nlinarith [neg_abs_le T₀, Real.sqrt_nonneg 21, le_abs_self T₀]
    have hre2 : |s.re| ≤ 2 := by rw [abs_le]; exact ⟨by linarith, h2⟩
    calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ ≤ 2 + (|T₀| + Real.sqrt 21 / 2 + 1) := add_le_add hre2 habs
      _ < |T₀| + 20 := by linarith [hs21]
  -- hfne (in the bare form, proved from the good heights and zerosInStrip)
  have hfne_bare : ∀ s : ℂ, (s.re = (-1:ℝ) ∨ s.re = 2 ∨ s.im = T₁ ∨ s.im = T₂) →
      (-1:ℝ) ≤ s.re → s.re ≤ 2 → T₁ ≤ s.im → s.im ≤ T₂ →
      DirichletCharacter.completedLFunction χ s ≠ 0 := by
    intro s hb _ _ _ _
    rcases hb with h | h | h | h
    · intro hz
      have := zerosInStrip χ hχ hχprim s hz
      rw [h] at this; exact absurd this.1 (by norm_num)
    · intro hz
      have := zerosInStrip χ hχ hχprim s hz
      rw [h] at this; exact absurd this.2 (by norm_num)
    · exact fun hz => hg₁ s hz h
    · exact fun hz => hg₂ s hz h
  -- the same, in the syntactic shape required by `rectZeroCount_imag_of`
  have hfne : ∀ s : ℂ,
      (s.re = ((-1 : ℂ) + (T₁ : ℂ) * Complex.I).re ∨ s.re = ((2 : ℂ) + (T₂ : ℂ) * Complex.I).re
        ∨ s.im = ((-1 : ℂ) + (T₁ : ℂ) * Complex.I).im
        ∨ s.im = ((2 : ℂ) + (T₂ : ℂ) * Complex.I).im) →
      ((-1 : ℂ) + (T₁ : ℂ) * Complex.I).re ≤ s.re →
      s.re ≤ ((2 : ℂ) + (T₂ : ℂ) * Complex.I).re →
      ((-1 : ℂ) + (T₁ : ℂ) * Complex.I).im ≤ s.im →
      s.im ≤ ((2 : ℂ) + (T₂ : ℂ) * Complex.I).im →
      DirichletCharacter.completedLFunction χ s ≠ 0 := by
    intro s hb h1 h2 h3 h4
    refine hfne_bare s (by simpa using hb) (by simpa using h1) (by simpa using h2)
      (by simpa using h3) (by simpa using h4)
  have hT12 : T₁ < T₂ := by linarith
  have hB := intervalIntegrable_logDeriv_side χ hχ (by norm_num : (-1:ℝ) ≤ 2)
    (side := fun x : ℝ => (x : ℂ) + (T₁ : ℂ) * Complex.I) (by fun_prop) (by
      intro x hx
      refine hfne ((x : ℂ) + (T₁ : ℂ) * Complex.I) (Or.inr (Or.inr (Or.inl (by simp))))
        (by simpa using hx.1) (by simpa using hx.2) (by simpa using le_refl T₁)
        (by simpa using le_of_lt hT12))
  have hT := intervalIntegrable_logDeriv_side χ hχ (by norm_num : (-1:ℝ) ≤ 2)
    (side := fun x : ℝ => (x : ℂ) + (T₂ : ℂ) * Complex.I) (by fun_prop) (by
      intro x hx
      refine hfne ((x : ℂ) + (T₂ : ℂ) * Complex.I) (Or.inr (Or.inr (Or.inr (by simp))))
        (by simpa using hx.1) (by simpa using hx.2) (by simpa using le_of_lt hT12)
        (by simpa using le_refl T₂))
  have hR := intervalIntegrable_logDeriv_side χ hχ (le_of_lt hT12)
    (side := fun y : ℝ => (2 : ℂ) + (y : ℂ) * Complex.I) (by fun_prop) (by
      intro y hy
      refine hfne ((2 : ℂ) + (y : ℂ) * Complex.I) (Or.inr (Or.inl (by simp)))
        (by simpa using (by norm_num : (-1:ℝ) ≤ 2)) (by simpa using le_refl (2:ℝ))
        (by simpa using hy.1) (by simpa using hy.2))
  have hL := intervalIntegrable_logDeriv_side χ hχ (le_of_lt hT12)
    (side := fun y : ℝ => (((-1 : ℝ)) : ℂ) + (y : ℂ) * Complex.I) (by fun_prop) (by
      intro y hy
      refine hfne ((((-1 : ℝ)) : ℂ) + (y : ℂ) * Complex.I) (Or.inl (by simp))
        (by simpa using le_refl (-1:ℝ)) (by simpa using (by norm_num : (-1:ℝ) ≤ 2))
        (by simpa using hy.1) (by simpa using hy.2))
  -- the re/im of the two corners, in the syntactic shape used by `rectZeroCount_imag_of`
  have hZre : ((-1 : ℂ) + (T₁ : ℂ) * Complex.I).re = -1 := by simp
  have hZim : ((-1 : ℂ) + (T₁ : ℂ) * Complex.I).im = T₁ := by simp
  have hWre : ((2 : ℂ) + (T₂ : ℂ) * Complex.I).re = 2 := by simp
  have hWim : ((2 : ℂ) + (T₂ : ℂ) * Complex.I).im = T₂ := by simp
  have hfinal := Commons.Analysis.Complex.rectZeroCount_imag_of
    (f := DirichletCharacter.completedLFunction χ)
    (z := (-1 : ℂ) + (T₁ : ℂ) * Complex.I) (w := (2 : ℂ) + (T₂ : ℂ) * Complex.I)
    (R := |T₀| + 20) hdiff (by positivity)
    (by simp only [hZre, hWre]; norm_num) (by simp only [hZim, hWim]; exact hT12) hf0 hrect hfne
    (by simp only [hZre, hZim, hWre, hWim]; exact hB.1)
    (by simp only [hZre, hZim, hWre, hWim]; exact hT.1)
    (by simp only [hZre, hZim, hWre, hWim]; exact hR.1)
    (by simp only [hZre, hZim, hWre, hWim]; exact hL.1)
    (by simp only [hZre, hZim, hWre, hWim]; exact hB.2.1)
    (by simp only [hZre, hZim, hWre, hWim]; exact hT.2.1)
    (by simp only [hZre, hZim, hWre, hWim]; exact hR.2.2)
    (by simp only [hZre, hZim, hWre, hWim]; exact hL.2.2)
  have hfinal' := hfinal
  simp only [hZre, hZim, hWre, hWim] at hfinal'
  exact hfinal'

lemma completedL_boxZeroCount_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {T₀ T₁ T₂ : ℝ}
    (hT₁ : T₀ - Real.sqrt 21 / 2 - 1 < T₁) (hT₁' : T₁ < T₀ - Real.sqrt 21 / 2)
    (hT₂ : T₀ + Real.sqrt 21 / 2 < T₂) (hT₂' : T₂ < T₀ + Real.sqrt 21 / 2 + 1)
    (hg₁ : ∀ u : ℂ, DirichletCharacter.completedLFunction χ u = 0 → u.im ≠ T₁)
    (hg₂ : ∀ u : ℂ, DirichletCharacter.completedLFunction χ u = 0 → u.im ≠ T₂) :
    2 * Real.pi * (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall (0 : ℂ) (|T₀| + 20))) u : ℤ) : ℝ) *
        (if (-1 : ℝ) < u.re ∧ u.re < 2 ∧ T₁ < u.im ∧ u.im < T₂ then 1 else 0))
      = (∫ x : ℝ in (-1)..2, (logDeriv (DirichletCharacter.completedLFunction χ)
              ((x : ℂ) + (T₁ : ℂ) * Complex.I)).im)
        - (∫ x : ℝ in (-1)..2, (logDeriv (DirichletCharacter.completedLFunction χ)
              ((x : ℂ) + (T₂ : ℂ) * Complex.I)).im)
        + (∫ y : ℝ in T₁..T₂, (logDeriv (DirichletCharacter.completedLFunction χ)
              ((((2 : ℝ)) : ℂ) + (y : ℂ) * Complex.I)).re)
        - (∫ y : ℝ in T₁..T₂, (logDeriv (DirichletCharacter.completedLFunction χ)
              ((((-1 : ℝ)) : ℂ) + (y : ℂ) * Complex.I)).re) := by

  have hdiff := differentiable_completedLFunction hχ
  -- bounds on the two heights
  have hs21 : Real.sqrt 21 < 5 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 21), Real.sqrt_nonneg 21]
  have hs21nn : 0 < Real.sqrt 21 := Real.sqrt_pos.mpr (by norm_num)
  -- hf0
  have hf0 : DirichletCharacter.completedLFunction χ 0 ≠ 0 :=
    Commons.NumberTheory.Linnik.completedLFunction_zero_ne_zero χ hχ hχprim
  -- hrect
  have hrect : ∀ s : ℂ,
      ((-1 : ℂ) + (T₁ : ℂ) * Complex.I).re ≤ s.re →
      s.re ≤ ((2 : ℂ) + (T₂ : ℂ) * Complex.I).re →
      ((-1 : ℂ) + (T₁ : ℂ) * Complex.I).im ≤ s.im →
      s.im ≤ ((2 : ℂ) + (T₂ : ℂ) * Complex.I).im →
      ‖s‖ < |T₀| + 20 := by
    intro s h1 h2 h3 h4
    have h1 : (-1:ℝ) ≤ s.re := by simpa using h1
    have h2 : s.re ≤ 2 := by simpa using h2
    have h3 : T₁ ≤ s.im := by simpa using h3
    have h4 : s.im ≤ T₂ := by simpa using h4
    have habs : |s.im| ≤ |T₀| + Real.sqrt 21 / 2 + 1 := by
      rw [abs_le]
      constructor
      · have : -(Real.sqrt 21) / 2 - 1 + T₀ < s.im := by linarith
        nlinarith [neg_abs_le T₀, Real.sqrt_nonneg 21, le_abs_self T₀]
      · have : s.im < Real.sqrt 21 / 2 + 1 + T₀ := by linarith
        nlinarith [neg_abs_le T₀, Real.sqrt_nonneg 21, le_abs_self T₀]
    have hre2 : |s.re| ≤ 2 := by rw [abs_le]; exact ⟨by linarith, h2⟩
    calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ ≤ 2 + (|T₀| + Real.sqrt 21 / 2 + 1) := add_le_add hre2 habs
      _ < |T₀| + 20 := by linarith [hs21]
  -- hfne (in the bare form, proved from the good heights and zerosInStrip)
  have hfne_bare : ∀ s : ℂ, (s.re = (-1:ℝ) ∨ s.re = 2 ∨ s.im = T₁ ∨ s.im = T₂) →
      (-1:ℝ) ≤ s.re → s.re ≤ 2 → T₁ ≤ s.im → s.im ≤ T₂ →
      DirichletCharacter.completedLFunction χ s ≠ 0 := by
    intro s hb _ _ _ _
    rcases hb with h | h | h | h
    · intro hz
      have := zerosInStrip χ hχ hχprim s hz
      rw [h] at this; exact absurd this.1 (by norm_num)
    · intro hz
      have := zerosInStrip χ hχ hχprim s hz
      rw [h] at this; exact absurd this.2 (by norm_num)
    · exact fun hz => hg₁ s hz h
    · exact fun hz => hg₂ s hz h
  -- the same, in the syntactic shape required by `rectZeroCount_imag_of`
  have hfne : ∀ s : ℂ,
      (s.re = ((-1 : ℂ) + (T₁ : ℂ) * Complex.I).re ∨ s.re = ((2 : ℂ) + (T₂ : ℂ) * Complex.I).re
        ∨ s.im = ((-1 : ℂ) + (T₁ : ℂ) * Complex.I).im
        ∨ s.im = ((2 : ℂ) + (T₂ : ℂ) * Complex.I).im) →
      ((-1 : ℂ) + (T₁ : ℂ) * Complex.I).re ≤ s.re →
      s.re ≤ ((2 : ℂ) + (T₂ : ℂ) * Complex.I).re →
      ((-1 : ℂ) + (T₁ : ℂ) * Complex.I).im ≤ s.im →
      s.im ≤ ((2 : ℂ) + (T₂ : ℂ) * Complex.I).im →
      DirichletCharacter.completedLFunction χ s ≠ 0 := by
    intro s hb h1 h2 h3 h4
    refine hfne_bare s (by simpa using hb) (by simpa using h1) (by simpa using h2)
      (by simpa using h3) (by simpa using h4)
  have hT12 : T₁ < T₂ := by linarith
  have hB := intervalIntegrable_logDeriv_side χ hχ (by norm_num : (-1:ℝ) ≤ 2)
    (side := fun x : ℝ => (x : ℂ) + (T₁ : ℂ) * Complex.I) (by fun_prop) (by
      intro x hx
      refine hfne ((x : ℂ) + (T₁ : ℂ) * Complex.I) (Or.inr (Or.inr (Or.inl (by simp))))
        (by simpa using hx.1) (by simpa using hx.2) (by simpa using le_refl T₁)
        (by simpa using le_of_lt hT12))
  have hT := intervalIntegrable_logDeriv_side χ hχ (by norm_num : (-1:ℝ) ≤ 2)
    (side := fun x : ℝ => (x : ℂ) + (T₂ : ℂ) * Complex.I) (by fun_prop) (by
      intro x hx
      refine hfne ((x : ℂ) + (T₂ : ℂ) * Complex.I) (Or.inr (Or.inr (Or.inr (by simp))))
        (by simpa using hx.1) (by simpa using hx.2) (by simpa using le_of_lt hT12)
        (by simpa using le_refl T₂))
  have hR := intervalIntegrable_logDeriv_side χ hχ (le_of_lt hT12)
    (side := fun y : ℝ => (2 : ℂ) + (y : ℂ) * Complex.I) (by fun_prop) (by
      intro y hy
      refine hfne ((2 : ℂ) + (y : ℂ) * Complex.I) (Or.inr (Or.inl (by simp)))
        (by simpa using (by norm_num : (-1:ℝ) ≤ 2)) (by simpa using le_refl (2:ℝ))
        (by simpa using hy.1) (by simpa using hy.2))
  have hL := intervalIntegrable_logDeriv_side χ hχ (le_of_lt hT12)
    (side := fun y : ℝ => (((-1 : ℝ)) : ℂ) + (y : ℂ) * Complex.I) (by fun_prop) (by
      intro y hy
      refine hfne ((((-1 : ℝ)) : ℂ) + (y : ℂ) * Complex.I) (Or.inl (by simp))
        (by simpa using le_refl (-1:ℝ)) (by simpa using (by norm_num : (-1:ℝ) ≤ 2))
        (by simpa using hy.1) (by simpa using hy.2))
  -- the re/im of the two corners, in the syntactic shape used by `rectZeroCount_imag_of`
  have hZre : ((-1 : ℂ) + (T₁ : ℂ) * Complex.I).re = -1 := by simp
  have hZim : ((-1 : ℂ) + (T₁ : ℂ) * Complex.I).im = T₁ := by simp
  have hWre : ((2 : ℂ) + (T₂ : ℂ) * Complex.I).re = 2 := by simp
  have hWim : ((2 : ℂ) + (T₂ : ℂ) * Complex.I).im = T₂ := by simp
  have hid := Commons.Analysis.Complex.rectZeroCount_imag_eq_of
    (f := DirichletCharacter.completedLFunction χ)
    (z := (-1 : ℂ) + (T₁ : ℂ) * Complex.I) (w := (2 : ℂ) + (T₂ : ℂ) * Complex.I)
    (R := |T₀| + 20) hdiff (by positivity)
    (by simp only [hZre, hWre]; norm_num) (by simp only [hZim, hWim]; exact hT12) hf0 hrect hfne
    (by simp only [hZre, hZim, hWre, hWim]; exact hB.1)
    (by simp only [hZre, hZim, hWre, hWim]; exact hT.1)
    (by simp only [hZre, hZim, hWre, hWim]; exact hR.1)
    (by simp only [hZre, hZim, hWre, hWim]; exact hL.1)
  have hid' := hid
  simp only [hZre, hZim, hWre, hWim] at hid'
  exact hid'

/-- **The four side bounds combined.**  Instantiating the identity `completedL_boxZeroCount_eq`
at the two good heights and adding the horizontal bounds (`completedL_boxHorizontal_le` at `T₁`
and `T₂`, using the crux `logDeriv_im_good_height`) to the vertical bound
(`completedL_boxVertical_le`, using `re_completedLogDeriv_two_tight` and its functional-equation
counterpart `completedLogDeriv_neg_one_re_tight`) gives

    N_box ≤ (1/2π) · ( (T₂−T₁)(log N + log(2+|T₀|+2) + 4) + 4·((7/10)(log N + log(2+|T₀|+4)) + 6) ).

With `T₂ − T₁ ≤ √21 + 2` this is the numeric input to the target. -/
lemma completedL_boxZeroCount_final {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {T₀ T₁ T₂ : ℝ}
    (hT₁ : T₀ - Real.sqrt 21 / 2 - 1 < T₁) (hT₁' : T₁ < T₀ - Real.sqrt 21 / 2)
    (hT₂ : T₀ + Real.sqrt 21 / 2 < T₂) (hT₂' : T₂ < T₀ + Real.sqrt 21 / 2 + 1)
    (hg₁ : ∀ u : ℂ, DirichletCharacter.completedLFunction χ u = 0 → u.im ≠ T₁)
    (hg₂ : ∀ u : ℂ, DirichletCharacter.completedLFunction χ u = 0 → u.im ≠ T₂)
    (hint₁ : ∀ u v : ℝ, IntervalIntegrable
      (fun σ : ℝ => (logDeriv (DirichletCharacter.completedLFunction χ)
        ((σ : ℂ) + (T₁ : ℂ) * Complex.I)).im) MeasureTheory.volume u v)
    (hint₂ : ∀ u v : ℝ, IntervalIntegrable
      (fun σ : ℝ => (logDeriv (DirichletCharacter.completedLFunction χ)
        ((σ : ℂ) + (T₂ : ℂ) * Complex.I)).im) MeasureTheory.volume u v)
    (hrv : IntervalIntegrable (fun y : ℝ =>
      (logDeriv (DirichletCharacter.completedLFunction χ)
        ((2 : ℂ) + (y : ℂ) * Complex.I)).re) MeasureTheory.volume T₁ T₂)
    (hlv : IntervalIntegrable (fun y : ℝ =>
      (logDeriv (DirichletCharacter.completedLFunction χ)
        ((-1 : ℂ) + (y : ℂ) * Complex.I)).re) MeasureTheory.volume T₁ T₂)
    (hb₁ : (∫ x : ℝ in (1 / 2)..2,
        ‖(logDeriv (DirichletCharacter.completedLFunction χ)
          ((x : ℂ) + (T₁ : ℂ) * Complex.I)).im‖)
      ≤ (7 / 10) * (Real.log (N : ℝ) + Real.log (2 + |T₀| + 4)) + 3)
    (hb₂ : (∫ x : ℝ in (1 / 2)..2,
        ‖(logDeriv (DirichletCharacter.completedLFunction χ)
          ((x : ℂ) + (T₂ : ℂ) * Complex.I)).im‖)
      ≤ (7 / 10) * (Real.log (N : ℝ) + Real.log (2 + |T₀| + 4)) + 3) :
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall (0 : ℂ) (|T₀| + 20))) u : ℤ) : ℝ) *
        (if (-1 : ℝ) < u.re ∧ u.re < 2 ∧ T₁ < u.im ∧ u.im < T₂ then 1 else 0))
      ≤ (1 / (2 * Real.pi)) *
        ((T₂ - T₁) * (Real.log (N : ℝ) + Real.log (2 + |T₀| + 2) + 13 / 4)
          + 4 * ((7 / 10) * (Real.log (N : ℝ) + Real.log (2 + |T₀| + 4)) + 3)) := by
  have hid := completedL_boxZeroCount_eq χ hχ hχprim hT₁ hT₁' hT₂ hT₂' hg₁ hg₂
  have hJb := completedL_boxHorizontal_le χ hχ hχprim hg₁ hint₁
  have hJt := completedL_boxHorizontal_le χ hχ hχprim hg₂ hint₂
  have hV := completedL_boxVertical_le χ hχ hT₁ hT₁' hT₂ hT₂'
    (fun T => by simpa [mul_comm] using re_completedLogDeriv_two_tight χ hχ T)
    (fun T => by simpa [mul_comm] using completedLogDeriv_neg_one_re_tight χ hχ hχprim T)
    hrv hlv
  have hpi2 : (0 : ℝ) < 2 * Real.pi := by positivity
  have key : 2 * Real.pi *
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall (0 : ℂ) (|T₀| + 20))) u : ℤ) : ℝ) *
          (if (-1 : ℝ) < u.re ∧ u.re < 2 ∧ T₁ < u.im ∧ u.im < T₂ then 1 else 0))
      ≤ (T₂ - T₁) * (Real.log (N : ℝ) + Real.log (2 + |T₀| + 2) + 13 / 4)
        + 4 * ((7 / 10) * (Real.log (N : ℝ) + Real.log (2 + |T₀| + 4)) + 3) := by
    -- `completedL_boxZeroCount_eq` states its vertical integrands with the literal
    -- `((2 : ℝ) : ℂ)`, while `completedL_boxVertical_le` uses `(2 : ℂ)` (same for `-1`);
    -- bridge the two by an integral congruence so `linarith` sees one term.
    have heq2 : (∫ y : ℝ in T₁..T₂, (logDeriv (DirichletCharacter.completedLFunction χ)
          ((((2 : ℝ)) : ℂ) + (y : ℂ) * Complex.I)).re)
        = (∫ y : ℝ in T₁..T₂, (logDeriv (DirichletCharacter.completedLFunction χ)
          ((2 : ℂ) + (y : ℂ) * Complex.I)).re) :=
      intervalIntegral.integral_congr fun y _ => by push_cast; ring
    have heq3 : (∫ y : ℝ in T₁..T₂, (logDeriv (DirichletCharacter.completedLFunction χ)
          ((((-1 : ℝ)) : ℂ) + (y : ℂ) * Complex.I)).re)
        = (∫ y : ℝ in T₁..T₂, (logDeriv (DirichletCharacter.completedLFunction χ)
          ((-1 : ℂ) + (y : ℂ) * Complex.I)).re) :=
      intervalIntegral.integral_congr fun y _ => by push_cast; ring
    rw [← heq2, ← heq3] at hV
    -- bottom side (upper bound on the integral) and top side (lower bound) both come from the
    -- *absolute-value* form
    have h1 : (∫ σ : ℝ in (-1)..2, (logDeriv (DirichletCharacter.completedLFunction χ)
        ((σ : ℂ) + (T₁ : ℂ) * Complex.I)).im)
        ≤ 2 * (∫ σ : ℝ in (1 / 2)..2, ‖(logDeriv (DirichletCharacter.completedLFunction χ)
        ((σ : ℂ) + (T₁ : ℂ) * Complex.I)).im‖) :=
      le_trans (le_abs_self _) (completedL_boxHorizontal_abs χ hχ hχprim hg₁ hint₁)
    have h2 : -(∫ σ : ℝ in (-1)..2, (logDeriv (DirichletCharacter.completedLFunction χ)
        ((σ : ℂ) + (T₂ : ℂ) * Complex.I)).im)
        ≤ 2 * (∫ σ : ℝ in (1 / 2)..2, ‖(logDeriv (DirichletCharacter.completedLFunction χ)
        ((σ : ℂ) + (T₂ : ℂ) * Complex.I)).im‖) :=
      le_trans (neg_le_abs _) (completedL_boxHorizontal_abs χ hχ hχprim hg₂ hint₂)
    linarith [h1, h2, hV, hb₁, hb₂]
  have hgoal : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall (0 : ℂ) (|T₀| + 20))) u : ℤ) : ℝ) *
          (if (-1 : ℝ) < u.re ∧ u.re < 2 ∧ T₁ < u.im ∧ u.im < T₂ then 1 else 0))
      ≤ ((T₂ - T₁) * (Real.log (N : ℝ) + Real.log (2 + |T₀| + 2) + 13 / 4)
        + 4 * ((7 / 10) * (Real.log (N : ℝ) + Real.log (2 + |T₀| + 4)) + 3)) / (2 * Real.pi) :=
    (le_div_iff₀ hpi2).mpr (by linarith [key])
  calc _ ≤ _ / (2 * Real.pi) := hgoal
    _ = (1 / (2 * Real.pi)) * _ := by ring

/-- **Containment.**  Every zero of `Λ(χ,·)` in the closed disk `B(2+iT₀, 5/2)` lies strictly
inside the box `(-1,2) × (T₁,T₂)` whenever `T₁ < T₀ - √21/2` and `T₀ + √21/2 < T₂`.  Hence the
disk count is at most the box count `N_box` of `completedL_boxZeroCount_final`.

(The imaginary part is `completedL_zero_im_close`; the real part is `zerosInStrip`; the divisors
of the two balls agree on the smaller one by `divisor_eq_closedBall_subset`.) -/
lemma completedL_diskCount_le_boxCount {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {T₀ T₁ T₂ : ℝ}
    (hT₁ : T₁ < T₀ - Real.sqrt 21 / 2) (hT₂ : T₀ + Real.sqrt 21 / 2 < T₂) :
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall ((2 : ℂ) + Complex.I * (T₀ : ℂ)) ((5 : ℝ) / 2))) u : ℤ) : ℝ))
      ≤ (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall (0 : ℂ) (|T₀| + 20))) u : ℤ) : ℝ) *
          (if (-1 : ℝ) < u.re ∧ u.re < 2 ∧ T₁ < u.im ∧ u.im < T₂ then 1 else 0)) := by
  classical
  set c : ℂ := (2 : ℂ) + Complex.I * (T₀ : ℂ) with hc
  have hdiff : Differentiable ℂ (DirichletCharacter.completedLFunction χ) :=
    differentiable_completedLFunction hχ
  let d1 : ℂ → ℤ := fun u =>
    MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall c (5/2)) u
  let d2 : ℂ → ℤ := fun u =>
    MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall (0 : ℂ) (|T₀| + 20)) u
  have hpt : ∀ u : ℂ, ((d1 u : ℤ) : ℝ) ≤ ((d2 u : ℤ) : ℝ) *
      (if (-1 : ℝ) < u.re ∧ u.re < 2 ∧ T₁ < u.im ∧ u.im < T₂ then 1 else 0) := by
    intro u
    by_cases hu : d1 u = 0
    · have h2nn : (0 : ℝ) ≤ ((d2 u : ℤ) : ℝ) := by
        have := MeromorphicOn.AnalyticOnNhd.divisor_nonneg
          (fun z _ => hdiff.analyticAt z : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall (0 : ℂ) (|T₀| + 20))) u
        exact_mod_cast this
      have : (if (-1 : ℝ) < u.re ∧ u.re < 2 ∧ T₁ < u.im ∧ u.im < T₂ then (1:ℝ) else 0) ≥ 0 := by
        split_ifs <;> norm_num
      simp only [hu, Int.cast_zero]
      exact mul_nonneg h2nn this
    · have hmem : u ∈ Metric.closedBall c (5/2) :=
        Commons.Analysis.Complex.divisor_mem_of_ne_zero (by simpa [d1] using hu)
      have hzu : DirichletCharacter.completedLFunction χ u = 0 :=
        Commons.Analysis.Complex.zero_of_divisor_ne_zero
          (f := DirichletCharacter.completedLFunction χ)
          (a := c) (ρ := 5/2) (fun z _ => hdiff.analyticAt z) (by simpa [d1] using hu)
      have him := completedL_zero_im_close χ hχ hχprim (T₀ := T₀) hzu
        (by simpa [hc, Metric.mem_closedBall, dist_eq_norm] using hmem)
      have hst := zerosInStrip χ hχ hχprim u hzu
      have hmem2 : u ∈ Metric.closedBall (0 : ℂ) (|T₀| + 20) := by
        have h1 : ‖u - c‖ ≤ 5/2 := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hmem
        have h2 : ‖c‖ ≤ 2 + |T₀| := by
          rw [hc]
          calc ‖(2 : ℂ) + Complex.I * (T₀ : ℂ)‖ ≤ ‖(2 : ℂ)‖ + ‖Complex.I * (T₀ : ℂ)‖ :=
                norm_add_le _ _
            _ = 2 + |T₀| := by simp
        have h3 : ‖u‖ ≤ 5/2 + (2 + |T₀|) := by
          calc ‖u‖ = ‖(u - c) + c‖ := by ring_nf
            _ ≤ ‖u - c‖ + ‖c‖ := norm_add_le _ _
            _ ≤ 5/2 + (2 + |T₀|) := add_le_add h1 h2
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
        linarith
      have hdeq : d1 u = d2 u := by
        simp only [d1, d2, hc]
        exact Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset
          (fun z _ => hdiff.analyticAt z) hmem hmem2
      have hind : (-1 : ℝ) < u.re ∧ u.re < 2 ∧ T₁ < u.im ∧ u.im < T₂ := by
        refine ⟨by linarith [hst.1], by linarith [hst.2], ?_, ?_⟩
        · have h := (abs_lt.mp him).1; linarith
        · have h := (abs_lt.mp him).2; linarith
      rw [hdeq]
      simp [hind]
  have hAn1 : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall c (5/2)) := fun z _ => hdiff.analyticAt z
  have hAn2 : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall (0 : ℂ) (|T₀| + 20)) := fun z _ => hdiff.analyticAt z
  have hfs1 : Function.HasFiniteSupport (fun u : ℂ => ((d1 u : ℤ) : ℝ)) := by
    have h := MeromorphicOn.divisor_support_finite_of_subset
      (f := DirichletCharacter.completedLFunction χ) (V := Metric.closedBall c (5/2))
      (U := Metric.closedBall c (5/2)) hAn1.meromorphicOn
      (isCompact_closedBall c (5/2)) (by intro z hz; exact hz)
    exact h.subset (by intro u hu; simpa [d1] using hu)
  have hfs2 : Function.HasFiniteSupport (fun u : ℂ => ((d2 u : ℤ) : ℝ) *
      (if (-1 : ℝ) < u.re ∧ u.re < 2 ∧ T₁ < u.im ∧ u.im < T₂ then 1 else 0)) := by
    have h : (Function.support d2).Finite :=
      MeromorphicOn.divisor_support_finite_of_subset
        (f := DirichletCharacter.completedLFunction χ) (V := Metric.closedBall (0:ℂ) (|T₀| + 20))
        (U := Metric.closedBall (0:ℂ) (|T₀| + 20)) hAn2.meromorphicOn
        (isCompact_closedBall (0:ℂ) (|T₀| + 20)) (by intro z hz; exact hz)
    refine h.subset ?_
    intro u hu
    simp only [Function.mem_support] at hu ⊢
    intro h0
    exact hu (by rw [h0]; simp)
  simpa only [d1, d2, hc] using finsum_le_finsum' hfs1 hfs2 hpt

/-- **The arithmetic.**  With `H = T₂−T₁ ≤ √21 + 2`, `T₁,T₂` in the `±1` windows around
`T₀ ∓ √21/2`, and the `(c_v, c_h) = (13/4, 3)` constants of `completedL_boxZeroCount_final`:

    N_box ≤ (1/2π)·[ H·(log N + log(2+|T₀|+2) + 13/4) + 4·((7/10)(log N + log(2+|T₀|+4)) + 3) ]
          ≤ (3/2)(log N + log(2+|T₀|+2)) + 6.

The two numeric facts used are `√21 < 4.6` and `9.4 < 3π`; with them the `log N`-coefficient
comparison is `√21 + 2 + 14/5 = 9.4 ≤ 3π` and the additive comparison is
`(√21+2)·13/4 + 14/5 + 12 ≤ 12π`. -/
lemma completedL_boxCount_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {T₀ T₁ T₂ : ℝ}
    (hT₁ : T₀ - Real.sqrt 21 / 2 - 1 < T₁) (hT₁' : T₁ < T₀ - Real.sqrt 21 / 2)
    (hT₂ : T₀ + Real.sqrt 21 / 2 < T₂) (hT₂' : T₂ < T₀ + Real.sqrt 21 / 2 + 1)
    (hH : T₂ - T₁ ≤ Real.sqrt 21 + 2)
    (hg₁ : ∀ u : ℂ, DirichletCharacter.completedLFunction χ u = 0 → u.im ≠ T₁)
    (hg₂ : ∀ u : ℂ, DirichletCharacter.completedLFunction χ u = 0 → u.im ≠ T₂)
    (hint₁ : ∀ u v : ℝ, IntervalIntegrable
      (fun σ : ℝ => (logDeriv (DirichletCharacter.completedLFunction χ)
        ((σ : ℂ) + (T₁ : ℂ) * Complex.I)).im) MeasureTheory.volume u v)
    (hint₂ : ∀ u v : ℝ, IntervalIntegrable
      (fun σ : ℝ => (logDeriv (DirichletCharacter.completedLFunction χ)
        ((σ : ℂ) + (T₂ : ℂ) * Complex.I)).im) MeasureTheory.volume u v)
    (hrv : IntervalIntegrable (fun y : ℝ =>
      (logDeriv (DirichletCharacter.completedLFunction χ)
        ((2 : ℂ) + (y : ℂ) * Complex.I)).re) MeasureTheory.volume T₁ T₂)
    (hlv : IntervalIntegrable (fun y : ℝ =>
      (logDeriv (DirichletCharacter.completedLFunction χ)
        ((-1 : ℂ) + (y : ℂ) * Complex.I)).re) MeasureTheory.volume T₁ T₂)
    (hb₁ : (∫ x : ℝ in (1 / 2)..2,
        ‖(logDeriv (DirichletCharacter.completedLFunction χ)
          ((x : ℂ) + (T₁ : ℂ) * Complex.I)).im‖)
      ≤ (7 / 10) * (Real.log (N : ℝ) + Real.log (2 + |T₀| + 4)) + 3)
    (hb₂ : (∫ x : ℝ in (1 / 2)..2,
        ‖(logDeriv (DirichletCharacter.completedLFunction χ)
          ((x : ℂ) + (T₂ : ℂ) * Complex.I)).im‖)
      ≤ (7 / 10) * (Real.log (N : ℝ) + Real.log (2 + |T₀| + 4)) + 3) :
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall (0 : ℂ) (|T₀| + 20))) u : ℤ) : ℝ) *
        (if (-1 : ℝ) < u.re ∧ u.re < 2 ∧ T₁ < u.im ∧ u.im < T₂ then 1 else 0))
      ≤ (3 / 2) * (Real.log (N : ℝ) + Real.log (2 + |T₀| + 2)) + 6 := by
  have hfin := completedL_boxZeroCount_final χ hχ hχprim hT₁ hT₁' hT₂ hT₂' hg₁ hg₂
    hint₁ hint₂ hrv hlv hb₁ hb₂
  -- fix 1: `Real.log_nonneg` takes `1 ≤ x`, not a `positivity` goal
  have hlogN1 : (0 : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N)))
  have hlogT1 : (0 : ℝ) ≤ Real.log (2 + |T₀| + 2) :=
    Real.log_nonneg (show (1 : ℝ) ≤ 2 + |T₀| + 2 by linarith [abs_nonneg T₀])
  have hL1 : (0 : ℝ) ≤ Real.log (N : ℝ) + Real.log (2 + |T₀| + 2) := by linarith
  -- fix 2: the log-part inequality as its own statement (carrying the `Real.log ↑N` term), then
  -- combine — rather than a `calc` whose first line omits that term
  have hpart : Real.log (2 + |T₀| + 4) ≤ Real.log (2 + |T₀| + 2) + 1 := by
    have h3 : (0 : ℝ) < 2 + |T₀| + 2 := by positivity
    have h4 : 2 + |T₀| + 4 ≤ (2 + |T₀| + 2) * 2 := by nlinarith [abs_nonneg T₀]
    calc Real.log (2 + |T₀| + 4) ≤ Real.log ((2 + |T₀| + 2) * 2) :=
          Real.log_le_log (show (0 : ℝ) < 2 + |T₀| + 4 by linarith [abs_nonneg T₀]) h4
      _ = Real.log (2 + |T₀| + 2) + Real.log 2 := Real.log_mul h3.ne' (by norm_num)
      _ ≤ Real.log (2 + |T₀| + 2) + 1 := by
          have h5 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
          linarith
  have hL2 : Real.log (N : ℝ) + Real.log (2 + |T₀| + 4)
      ≤ Real.log (N : ℝ) + Real.log (2 + |T₀| + 2) + 1 := by linarith
  -- the two numeric facts
  have hs21 : Real.sqrt 21 < 4.6 :=
    Real.sqrt_lt' (by norm_num) |>.mpr (by norm_num)
  have hpi : Real.sqrt 21 + 2 + 14 / 5 < 3 * Real.pi := by
    have h := Real.pi_gt_d2
    linarith
  have hpi2 : (Real.sqrt 21 + 2) * (13 / 4) + 14 / 5 + 12 ≤ 12 * Real.pi := by
    have h := Real.pi_gt_d2
    nlinarith [hs21]
  -- the combined numeric bound
  have hnum : (T₂ - T₁) *
        (Real.log (N : ℝ) + Real.log (2 + |T₀| + 2) + 13 / 4)
      + 4 * ((7 / 10) * (Real.log (N : ℝ) + Real.log (2 + |T₀| + 4)) + 3)
      ≤ (2 * Real.pi) *
        ((3 / 2) * (Real.log (N : ℝ) + Real.log (2 + |T₀| + 2)) + 6) := by
    have hstep1 : (T₂ - T₁) *
          (Real.log (N : ℝ) + Real.log (2 + |T₀| + 2) + 13 / 4)
        ≤ (Real.sqrt 21 + 2) *
          (Real.log (N : ℝ) + Real.log (2 + |T₀| + 2) + 13 / 4) :=
      mul_le_mul_of_nonneg_right hH (by linarith)
    have hstep2 : 4 * ((7 / 10) * (Real.log (N : ℝ) + Real.log (2 + |T₀| + 4)) + 3)
        ≤ 4 * ((7 / 10) * (Real.log (N : ℝ) + Real.log (2 + |T₀| + 2) + 1) + 3) := by
      have : (7 / 10 : ℝ) * (Real.log (N : ℝ) + Real.log (2 + |T₀| + 4)) + 3
          ≤ (7 / 10) * (Real.log (N : ℝ) + Real.log (2 + |T₀| + 2) + 1) + 3 := by linarith
      linarith
    nlinarith [hstep1, hstep2, hs21, hpi, hpi2, hL1, Real.pi_pos]
  -- fix 3: `hY` stated in the *explicit* form and obtained from the L-form by rewriting the
  -- goal (no `simp`/`rw` on `hfin`, which made no progress)
  have hY : (1 / (2 * Real.pi)) *
      ((T₂ - T₁) * (Real.log (N : ℝ) + Real.log (2 + |T₀| + 2) + 13 / 4)
        + 4 * ((7 / 10) * (Real.log (N : ℝ) + Real.log (2 + |T₀| + 4)) + 3))
      ≤ (3 / 2) * (Real.log (N : ℝ) + Real.log (2 + |T₀| + 2)) + 6 := by
    have h1 := mul_le_mul_of_nonneg_left hnum (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))
    have h2 : (1 / (2 * Real.pi)) * ((2 * Real.pi) *
        ((3 / 2) * (Real.log (N : ℝ) + Real.log (2 + |T₀| + 2)) + 6))
        = (3 / 2) * (Real.log (N : ℝ) + Real.log (2 + |T₀| + 2)) + 6 := by
      field_simp
    linarith [h1, h2]
  exact le_trans hfin hY



/-- **Jensen step.**  For a primitive non-trivial `χ`, the multiplicity-weighted number of
zeros of `Λ = completedLFunction χ` in the closed disk `closedBall (2+iT₀) (5/2)` is at most
`(1/log(12/5))·(circleAverage (log‖Λ·‖) c 6 - log‖Λ c‖)`. -/
theorem completedL_disk_divisor_le_circleAverage {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (T₀ : ℝ) :
    Real.log ((6 : ℝ) / (5 / 2)) *
        (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall ((2 : ℂ) + Complex.I * (T₀ : ℂ)) ((5 : ℝ) / 2))) u : ℤ) : ℝ))
      ≤ Real.circleAverage (fun z : ℂ =>
            Real.log ‖DirichletCharacter.completedLFunction χ z‖)
          ((2 : ℂ) + Complex.I * (T₀ : ℂ)) 6 -
        Real.log ‖DirichletCharacter.completedLFunction χ ((2 : ℂ) + Complex.I * (T₀ : ℂ))‖ := by
  classical
  set c : ℂ := (2 : ℂ) + Complex.I * (T₀ : ℂ) with hc
  have hdiff : Differentiable ℂ (DirichletCharacter.completedLFunction χ) :=
    differentiable_completedLFunction hχ
  have hAn6 : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall c |(6 : ℝ)|) := fun z _ => hdiff.analyticAt z
  have hAn52 : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall c ((5 : ℝ) / 2)) := fun z _ => hdiff.analyticAt z
  have hAn6b : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall c (6 : ℝ)) := fun z _ => hdiff.analyticAt z
  have hc_re : c.re = 2 := by simp [hc]
  have hc_ne : DirichletCharacter.completedLFunction χ c ≠ 0 := by
    intro h0
    have hs := zerosInStrip χ hχ hχprim c h0
    rw [hc_re] at hs
    linarith [hs.2]
  -- Jensen's formula on the circle of radius 6
  have hJ := AnalyticOnNhd.circleAverage_log_norm (c := c) (R := (6 : ℝ))
      (f := DirichletCharacter.completedLFunction χ) (by norm_num) hAn6 hc_ne
  rw [show |(6 : ℝ)| = 6 from abs_of_nonneg (by norm_num)] at hJ
  have hJ' : Real.circleAverage
      (fun z : ℂ => Real.log ‖DirichletCharacter.completedLFunction χ z‖) c 6 -
        Real.log ‖DirichletCharacter.completedLFunction χ c‖
      = ∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall c 6)) u : ℤ) : ℝ) * Real.log (6 * ‖c - u‖⁻¹) := by
    rw [hJ]; ring
  -- pointwise comparison of the two divisor sums
  have hpoint : ∀ u : ℂ,
      Real.log ((6 : ℝ) / (5 / 2)) *
        (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall c ((5 : ℝ) / 2))) u : ℤ) : ℝ)
      ≤ (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall c 6)) u : ℤ) : ℝ) * Real.log (6 * ‖c - u‖⁻¹) := by
    intro u
    by_cases hd : MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall c ((5 : ℝ) / 2)) u = 0
    · rw [hd]
      simp only [Int.cast_zero, mul_zero]
      by_cases hu6 : u ∈ Metric.closedBall c 6
      · have hd6nn : (0 : ℝ) ≤ (((MeromorphicOn.divisor
            (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall c 6)) u : ℤ) : ℝ) := by
          exact_mod_cast (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn6b u)
        have hlog : 0 ≤ Real.log (6 * ‖c - u‖⁻¹) := by
          rcases eq_or_lt_of_le (norm_nonneg (c - u)) with h0 | h0
          · rw [← h0, inv_zero, mul_zero, Real.log_zero]
          · apply Real.log_nonneg
            have h6 : 6 * ‖c - u‖⁻¹ = 6 / ‖c - u‖ := by simp only [div_eq_mul_inv]
            rw [h6, le_div_iff₀ h0, one_mul]
            simpa [dist_eq_norm, norm_sub_rev] using Metric.mem_closedBall.mp hu6
        exact mul_nonneg hd6nn hlog
      · rw [Commons.Analysis.Complex.divisor_eq_zero_of_not_mem (Metric.closedBall c 6) hu6]
        simp
    · have huB : u ∈ Metric.closedBall c ((5 : ℝ) / 2) :=
        Commons.Analysis.Complex.divisor_mem_of_ne_zero (f :=
          DirichletCharacter.completedLFunction χ) (by simpa using hd)
      have huB6 : u ∈ Metric.closedBall c 6 :=
        Metric.closedBall_subset_closedBall (by norm_num) huB
      have hdeq : MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall c ((5 : ℝ) / 2)) u
          = MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall c 6) u :=
        Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset (f :=
          DirichletCharacter.completedLFunction χ) (fun z _ => hdiff.analyticAt z) huB huB6
      have hdnn : (0 : ℝ) ≤ (((MeromorphicOn.divisor
          (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall c ((5 : ℝ) / 2))) u : ℤ) : ℝ) := by
        exact_mod_cast (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn52 u)
      -- `u ≠ c` because `Λ u = 0` while `Λ c ≠ 0`
      have hzu : DirichletCharacter.completedLFunction χ u = 0 :=
        Commons.Analysis.Complex.zero_of_divisor_ne_zero (f :=
          DirichletCharacter.completedLFunction χ) hAn52 (by simpa using hd)
      have hcu : u ≠ c := fun h => hc_ne (by rw [← h]; exact hzu)
      have hnorm_pos : 0 < ‖c - u‖ := by
        rw [norm_pos_iff]
        exact sub_ne_zero.mpr (Ne.symm hcu)
      have hlog : Real.log ((6 : ℝ) / (5 / 2)) ≤ Real.log (6 * ‖c - u‖⁻¹) := by
        apply Real.log_le_log (by norm_num)
        have h1 : ‖c - u‖ ≤ (5 : ℝ) / 2 := by
          simpa [dist_eq_norm, norm_sub_rev] using Metric.mem_closedBall.mp huB
        have h3 : 6 * ‖c - u‖⁻¹ = 6 / ‖c - u‖ := by simp only [div_eq_mul_inv]
        rw [h3, le_div_iff₀ hnorm_pos]
        nlinarith
      rw [hdeq]
      have hd6 : (0 : ℝ) ≤ (((MeromorphicOn.divisor
          (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall c 6)) u : ℤ) : ℝ) := by
        exact_mod_cast (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn6b u)
      calc Real.log ((6 : ℝ) / (5 / 2)) *
            (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.closedBall c 6)) u : ℤ) : ℝ)
          = (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.closedBall c 6)) u : ℤ) : ℝ) * Real.log ((6 : ℝ) / (5 / 2)) := by ring
        _ ≤ (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.closedBall c 6)) u : ℤ) : ℝ) * Real.log (6 * ‖c - u‖⁻¹) :=
            mul_le_mul_of_nonneg_left hlog hd6
  have hfs52 : Function.HasFiniteSupport (fun u : ℂ =>
      (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall c ((5 : ℝ) / 2))) u : ℤ) : ℝ)) := by
    have h := MeromorphicOn.divisor_support_finite_of_subset
      (f := DirichletCharacter.completedLFunction χ)
      (U := Metric.closedBall c ((5 : ℝ) / 2)) (V := Metric.closedBall c ((5 : ℝ) / 2))
      hAn52.meromorphicOn (isCompact_closedBall c ((5 : ℝ) / 2)) (by intro z hz; exact hz)
    exact h.subset (by intro u hu; simpa using hu)
  have hfs6 : Function.HasFiniteSupport (fun u : ℂ =>
      (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall c 6)) u : ℤ) : ℝ) * Real.log (6 * ‖c - u‖⁻¹)) := by
    have h : (Function.support (fun u : ℂ =>
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall c 6)) u)).Finite := by
      simpa [Function.HasFiniteSupport] using
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall c 6)).finiteSupport (isCompact_closedBall c 6))
    refine h.subset ?_
    intro u hu
    simp only [Function.mem_support] at hu ⊢
    intro h0
    exact hu (by rw [h0]; simp)
  have hfsL : Function.HasFiniteSupport (fun u : ℂ => Real.log ((6 : ℝ) / (5 / 2)) *
      (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall c ((5 : ℝ) / 2))) u : ℤ) : ℝ)) := by
    refine hfs52.subset ?_
    intro u hu
    simp only [Function.mem_support] at hu ⊢
    exact fun h => hu (by rw [h]; ring)
  have hsum := finsum_le_finsum' hfsL hfs6 (fun u : ℂ => hpoint u)
  rw [← mul_finsum] at hsum
  rw [hJ']
  linarith [hsum]


theorem completedL_diskZeroCount_explicit {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∀ T₀ : ℝ,
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall ((2 : ℂ) + Complex.I * (T₀ : ℂ)) ((5 : ℝ) / 2))) u : ℤ) : ℝ)) ≤
        (3 / 2) * (Real.log (N : ℝ) + Real.log (2 + |T₀| + 2)) + 6 := by
  intro T₀
  exact Commons.NumberTheory.DirichletCharacter.diskZeroCount_two_half χ hχ hχprim T₀

end Commons.NumberTheory.DirichletCharacter
