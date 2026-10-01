import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.chebyshevPsiChi_explicit_formula_mult
import Submission.Commons.NumberTheory.DirichletCharacter.rectInt_logDeriv_gammaFactor_mul_eq

open Complex MeasureTheory intervalIntegral Filter
open scoped Real Topology BigOperators

set_option maxHeartbeats 1600000

namespace Commons.NumberTheory.DirichletCharacter

/-- Additivity of `rectInt` for functions continuous at every boundary point. -/
lemma rectInt_add_of_boundary_cts_aux {z w : ℂ} {f g : ℂ → ℂ}
    (hf : ∀ s ∈ rectBoundary z w, ContinuousAt f s)
    (hg : ∀ s ∈ rectBoundary z w, ContinuousAt g s) :
    rectInt z w (fun s => f s + g s) = rectInt z w f + rectInt z w g := by
  obtain ⟨a1, a2, a3, a4⟩ := intervalIntegrable_of_boundary_continuousAt hf
  obtain ⟨b1, b2, b3, b4⟩ := intervalIntegrable_of_boundary_continuousAt hg
  exact rectInt_add'' a1 b1 a2 b2 a3 b3 a4 b4

/-- Residue of `f(s)/(s-u)`: for `f` differentiable on the closed rectangle and `u` strictly
inside, the contour integral is `2πi f(u)`. -/
lemma rectInt_analytic_div_sub_inside_aux {z w u : ℂ} {f : ℂ → ℂ}
    (hzre : z.re < w.re) (hzim : z.im < w.im)
    (huin : z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im)
    (hf : DifferentiableOn ℂ f (rectSet z w)) :
    rectInt z w (fun s => f s / (s - u)) = f u * (2 * (Real.pi : ℂ) * Complex.I) := by
  have hn : rectSet z w ∈ 𝓝 u := rectSet_mem_nhds huin.1 huin.2.1 huin.2.2.1 huin.2.2.2
  have hds : DifferentiableOn ℂ (dslope f u) (rectSet z w) :=
    differentiableOn_dslope_of_differentiableOn hn hf
  have hcongr : rectInt z w (fun s => f s / (s - u)) =
      rectInt z w (fun s => dslope f u s + f u / (s - u)) := by
    apply rectInt_congr_boundary'
    intro s hs
    have hsne : s ≠ u := ne_of_mem_rectBoundary_of_inside huin hs
    rw [dslope_of_ne f hsne, slope_def_module, smul_eq_mul]
    field_simp
    ring
  obtain ⟨d1, d2, d3, d4⟩ := edgeIntegrable_of_continuousOn hds.continuousOn
  have hcont : ContinuousOn (fun s : ℂ => f u / (s - u)) {s : ℂ | s ≠ u} :=
    continuousOn_const.div (continuousOn_id.sub continuousOn_const)
      (fun s hs => sub_ne_zero.mpr hs)
  obtain ⟨e1, e2, e3, e4⟩ := edgeIntegrable_of_continuousOn_ne huin hcont
  rw [hcongr, rectInt_add'' d1 e1 d2 e2 d3 e3 d4 e4,
    rectInt_eq_zero_of_differentiableOn hds, rectInt_const_div_sub_inside (f u) hzre hzim huin,
    zero_add]

/-- The contour integral of `r/(s(s-s₀))` vanishes: the residues at `0` and at `s₀` cancel. -/
lemma rectInt_div_mul_sub_eq_zero_aux {z w s₀ : ℂ} (r : ℂ)
    (hzre : z.re < w.re) (hzim : z.im < w.im)
    (h0in : z.re < 0 ∧ 0 < w.re ∧ z.im < 0 ∧ 0 < w.im)
    (hs0in : z.re < s₀.re ∧ s₀.re < w.re ∧ z.im < s₀.im ∧ s₀.im < w.im)
    (hs0ne : s₀ ≠ 0) :
    rectInt z w (fun s => r / (s * (s - s₀))) = 0 := by
  have hcongr : rectInt z w (fun s => r / (s * (s - s₀))) =
      rectInt z w (fun s => (r / s₀) / (s - s₀) + (-(r / s₀)) * (1 / s)) := by
    apply rectInt_congr_boundary'
    intro s hs
    have hs0 : s ≠ 0 := ne_zero_of_mem_rectBoundary h0in.1 h0in.2.1 h0in.2.2.1 h0in.2.2.2 hs
    have hss0 : s ≠ s₀ := ne_of_mem_rectBoundary_of_inside hs0in hs
    field_simp
    ring
  have hc1 : ∀ s ∈ rectBoundary z w, ContinuousAt (fun s : ℂ => (r / s₀) / (s - s₀)) s := by
    intro s hs
    exact ContinuousAt.div continuousAt_const (continuousAt_id.sub continuousAt_const)
      (sub_ne_zero.mpr (ne_of_mem_rectBoundary_of_inside hs0in hs))
  have hc2 : ∀ s ∈ rectBoundary z w, ContinuousAt (fun s : ℂ => (-(r / s₀)) * (1 / s)) s := by
    intro s hs
    exact ContinuousAt.mul continuousAt_const
      (ContinuousAt.div continuousAt_const continuousAt_id
        (ne_zero_of_mem_rectBoundary h0in.1 h0in.2.1 h0in.2.2.1 h0in.2.2.2 hs))
  rw [hcongr, rectInt_add_of_boundary_cts_aux hc1 hc2,
    rectInt_const_div_sub_inside (r / s₀) hzre hzim hs0in,
    rectInt_const_mul' (-(r / s₀)) (fun s : ℂ => 1 / s),
    rectInt_one_div_self hzre hzim h0in]
  ring

/-- The contour integral of `logDeriv γ · G` for entire `G`: only the possible pole of `γ'/γ`
at `0` (present exactly for even characters) contributes. -/
lemma rectInt_logDeriv_gammaFactor_mul_entire_aux {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) [Decidable χ.Even] {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    {z w : ℂ} (hzre : z.re < w.re) (hzim : z.im < w.im) (hz1 : -(1 : ℝ) < z.re)
    (h0in : z.re < 0 ∧ 0 < w.re ∧ z.im < 0 ∧ 0 < w.im) :
    rectInt z w (fun s => logDeriv (DirichletCharacter.gammaFactor χ) s * G s) =
      -(2 * (Real.pi : ℂ) * Complex.I) * (if χ.Even then G 0 else 0) := by
  rcases χ.even_or_odd with hE | hO
  · rw [if_pos hE]
    exact rectInt_logDeriv_gammaFactor_mul_eq χ hG hzre hzim hz1 h0in hE
  · rw [if_neg hO.not_even, mul_zero]
    have hre_ge : ∀ s ∈ rectSet z w, -(1 : ℝ) < s.re := by
      intro s hs
      obtain ⟨hre, -⟩ := Complex.mem_reProdIm.mp hs
      rw [Set.uIcc_of_le (le_of_lt hzre)] at hre
      linarith [hre.1, hz1]
    have hgf : DirichletCharacter.gammaFactor χ = fun s => Complex.Gammaℝ (s + 1) :=
      funext hO.gammaFactor_def
    rw [hgf]
    have hdig : DifferentiableOn ℂ (fun s : ℂ => Complex.digamma ((s + 1) / 2)) (rectSet z w) :=
      differentiableOn_digamma_shift (c := 1) (fun s hs => digamma_re_shift_one (hre_ge s hs))
    have hGd : DifferentiableOn ℂ (fun s : ℂ =>
        (-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma ((s + 1) / 2) / 2) * G s)
        (rectSet z w) :=
      (DifferentiableOn.add (differentiableOn_const _) (hdig.div_const 2)).mul hG.differentiableOn
    rw [rectInt_congr_boundary'
      (f := fun s => logDeriv (fun s : ℂ => Complex.Gammaℝ (s + 1)) s * G s)
      (g := fun s => (-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma ((s + 1) / 2) / 2) * G s)
      ?_]
    · exact rectInt_eq_zero_of_differentiableOn hGd
    · intro s hs
      have hsre : -(1 : ℝ) < s.re := hre_ge s (rectBoundary_subset_rectSet hzre hzim hs)
      have h1 : 0 < (s + 1).re := by
        have h2 : (s + 1).re = s.re + 1 := by simp
        rw [h2]; linarith
      have hcomp : logDeriv (fun s : ℂ => Complex.Gammaℝ (s + 1)) s =
          logDeriv Complex.Gammaℝ (s + 1) := by
        have h := logDeriv_comp (f := Complex.Gammaℝ) (g := fun s : ℂ => s + 1) (x := s)
          (differentiableAt_Gammaℝ (s + 1) h1) (by fun_prop)
        simpa [Function.comp_def] using h
      rw [hcomp, logDeriv_Gammaℝ_formula (s + 1) h1]

/-- The contour integral of `logDeriv γ · r/(s-s₀)` for `s₀` strictly inside the rectangle:
the residue at `s₀` together with the residue of `γ'/γ` at `0` (even characters only). -/
lemma rectInt_logDeriv_gammaFactor_mul_div_sub_aux {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) [Decidable χ.Even]
    {s₀ r : ℂ} {z w : ℂ}
    (hγne : DirichletCharacter.gammaFactor χ s₀ ≠ 0)
    (hzre : z.re < w.re) (hzim : z.im < w.im) (hz1 : -(1 : ℝ) < z.re)
    (h0in : z.re < 0 ∧ 0 < w.re ∧ z.im < 0 ∧ 0 < w.im)
    (hs0in : z.re < s₀.re ∧ s₀.re < w.re ∧ z.im < s₀.im ∧ s₀.im < w.im) :
    rectInt z w (fun s => logDeriv (DirichletCharacter.gammaFactor χ) s * (r / (s - s₀))) =
      2 * (Real.pi : ℂ) * Complex.I * (logDeriv (DirichletCharacter.gammaFactor χ) s₀) * r
        + (if χ.Even then 2 * (Real.pi : ℂ) * Complex.I * (r / s₀) else 0) := by
  have hre_ge : ∀ s ∈ rectSet z w, -(1 : ℝ) < s.re := by
    intro s hs
    obtain ⟨hre, -⟩ := Complex.mem_reProdIm.mp hs
    rw [Set.uIcc_of_le (le_of_lt hzre)] at hre
    linarith [hre.1, hz1]
  rcases χ.even_or_odd with hE | hO
  · rw [if_pos hE]
    have hgf : DirichletCharacter.gammaFactor χ = Complex.Gammaℝ := funext hE.gammaFactor_def
    set A : ℂ → ℂ := fun s => -(Complex.log (Real.pi : ℂ)) / 2 +
      Complex.digamma ((s + 2) / 2) / 2 with hAdef
    have hs0re : -(1 : ℝ) < s₀.re := by linarith [hs0in.1, hz1]
    have hs0ne : s₀ ≠ 0 := by
      intro h
      have h0 : DirichletCharacter.gammaFactor χ 0 = 0 := by
        rw [hgf, Complex.Gammaℝ_eq_zero_iff]
        exact ⟨0, by simp⟩
      exact hγne (by rw [h]; exact h0)
    have hdig : DifferentiableOn ℂ (fun s : ℂ => Complex.digamma ((s + 2) / 2)) (rectSet z w) :=
      differentiableOn_digamma_shift (c := 2) (fun s hs => digamma_re_shift_two (hre_ge s hs))
    have hA : DifferentiableOn ℂ A (rectSet z w) := by
      rw [hAdef]
      exact DifferentiableOn.add (differentiableOn_const _) (hdig.div_const 2)
    have hAs0 : A s₀ = logDeriv Complex.Gammaℝ s₀ + 1 / s₀ := by
      rw [hAdef]
      have h := logDeriv_Gammaℝ_add_inv (s := s₀) hs0ne hs0re
      rw [show s₀ / 2 + 1 = (s₀ + 2) / 2 by ring] at h
      exact h.symm
    have hpt : ∀ s ∈ rectBoundary z w,
        logDeriv (DirichletCharacter.gammaFactor χ) s * (r / (s - s₀)) =
          A s * (r / (s - s₀)) + (-1) * (r / (s * (s - s₀))) := by
      intro s hs
      have hsne : s ≠ 0 :=
        ne_zero_of_mem_rectBoundary h0in.1 h0in.2.1 h0in.2.2.1 h0in.2.2.2 hs
      have hsre : -(1 : ℝ) < s.re := hre_ge s (rectBoundary_subset_rectSet hzre hzim hs)
      have h := logDeriv_Gammaℝ_add_inv (s := s) hsne hsre
      rw [show s / 2 + 1 = (s + 2) / 2 by ring] at h
      have h' : logDeriv Complex.Gammaℝ s = A s - 1 / s := by
        rw [hAdef]
        exact eq_sub_iff_add_eq.mpr h
      rw [hgf, h']
      field_simp
      ring
    have hc1 : ∀ s ∈ rectBoundary z w,
        ContinuousAt (fun s : ℂ => A s * (r / (s - s₀))) s := by
      intro s hs
      have hsre : -(1 : ℝ) < s.re := hre_ge s (rectBoundary_subset_rectSet hzre hzim hs)
      have hAc : ContinuousAt A s := by
        rw [hAdef]
        exact ContinuousAt.const_add
          ((differentiableAt_digamma_shift (s := s) (c := 2)
            (digamma_re_shift_two hsre)).continuousAt.div_const 2)
          (-(Complex.log (Real.pi : ℂ)) / 2)
      exact hAc.mul (ContinuousAt.div continuousAt_const
        (continuousAt_id.sub continuousAt_const)
        (sub_ne_zero.mpr (ne_of_mem_rectBoundary_of_inside hs0in hs)))
    have hc2 : ∀ s ∈ rectBoundary z w,
        ContinuousAt (fun s : ℂ => (-1) * (r / (s * (s - s₀)))) s := by
      intro s hs
      have hsne : s ≠ 0 :=
        ne_zero_of_mem_rectBoundary h0in.1 h0in.2.1 h0in.2.2.1 h0in.2.2.2 hs
      have hss0 : s ≠ s₀ := ne_of_mem_rectBoundary_of_inside hs0in hs
      exact ContinuousAt.mul continuousAt_const (ContinuousAt.div continuousAt_const
        (continuousAt_id.mul (continuousAt_id.sub continuousAt_const))
        (mul_ne_zero hsne (sub_ne_zero.mpr hss0)))
    rw [rectInt_congr_boundary' hpt, rectInt_add_of_boundary_cts_aux hc1 hc2]
    have hA1 : rectInt z w (fun s => A s * (r / (s - s₀))) =
        (A s₀ * r) * (2 * (Real.pi : ℂ) * Complex.I) := by
      have hcongr2 : rectInt z w (fun s => A s * (r / (s - s₀))) =
          rectInt z w (fun s => (A s * r) / (s - s₀)) := by
        apply rectInt_congr_boundary'
        intro s hs
        ring
      rw [hcongr2]
      exact rectInt_analytic_div_sub_inside_aux hzre hzim hs0in (hA.mul_const r)
    have hA2 : rectInt z w (fun s => (-1) * (r / (s * (s - s₀)))) = 0 := by
      rw [rectInt_const_mul' (-1) (fun s => r / (s * (s - s₀))),
        rectInt_div_mul_sub_eq_zero_aux r hzre hzim h0in hs0in hs0ne]
      ring
    rw [hA1, hA2, add_zero, hAs0, hgf]
    ring
  · rw [if_neg hO.not_even, add_zero]
    have hgf : DirichletCharacter.gammaFactor χ = fun s => Complex.Gammaℝ (s + 1) :=
      funext hO.gammaFactor_def
    set A : ℂ → ℂ := fun s => -(Complex.log (Real.pi : ℂ)) / 2 +
      Complex.digamma ((s + 1) / 2) / 2 with hAdef
    have hdig : DifferentiableOn ℂ (fun s : ℂ => Complex.digamma ((s + 1) / 2)) (rectSet z w) :=
      differentiableOn_digamma_shift (c := 1) (fun s hs => digamma_re_shift_one (hre_ge s hs))
    have hA : DifferentiableOn ℂ A (rectSet z w) := by
      rw [hAdef]
      exact DifferentiableOn.add (differentiableOn_const _) (hdig.div_const 2)
    have hAs0 : A s₀ = logDeriv (DirichletCharacter.gammaFactor χ) s₀ := by
      rw [hgf]
      have h1 : 0 < (s₀ + 1).re := by
        have h2 : (s₀ + 1).re = s₀.re + 1 := by simp
        rw [h2]
        linarith [hs0in.1, hz1]
      have hcomp : logDeriv (fun s : ℂ => Complex.Gammaℝ (s + 1)) s₀ =
          logDeriv Complex.Gammaℝ (s₀ + 1) := by
        have h := logDeriv_comp (f := Complex.Gammaℝ) (g := fun s : ℂ => s + 1) (x := s₀)
          (differentiableAt_Gammaℝ (s₀ + 1) h1) (by fun_prop)
        simpa [Function.comp_def] using h
      rw [hAdef, hcomp, logDeriv_Gammaℝ_formula (s₀ + 1) h1]
    have hpt : ∀ s ∈ rectBoundary z w,
        logDeriv (DirichletCharacter.gammaFactor χ) s * (r / (s - s₀)) =
          A s * (r / (s - s₀)) := by
      intro s hs
      have hsre : -(1 : ℝ) < s.re := hre_ge s (rectBoundary_subset_rectSet hzre hzim hs)
      have h1 : 0 < (s + 1).re := by
        have h2 : (s + 1).re = s.re + 1 := by simp
        rw [h2]
        linarith
      have hcomp : logDeriv (fun s : ℂ => Complex.Gammaℝ (s + 1)) s =
          logDeriv Complex.Gammaℝ (s + 1) := by
        have h := logDeriv_comp (f := Complex.Gammaℝ) (g := fun s : ℂ => s + 1) (x := s)
          (differentiableAt_Gammaℝ (s + 1) h1) (by fun_prop)
        simpa [Function.comp_def] using h
      rw [hgf, hcomp, logDeriv_Gammaℝ_formula (s + 1) h1]
    rw [rectInt_congr_boundary' hpt]
    have hcongr2 : rectInt z w (fun s => A s * (r / (s - s₀))) =
        rectInt z w (fun s => (A s * r) / (s - s₀)) := by
      apply rectInt_congr_boundary'
      intro s hs
      ring
    rw [hcongr2, rectInt_analytic_div_sub_inside_aux hzre hzim hs0in (hA.mul_const r), hAs0]
    ring

theorem rectInt_logDeriv_gammaFactor_mul_simplePole {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) [Decidable χ.Even]
    {G : ℂ → ℂ} {s₀ : ℂ} {r : ℂ}
    (hG : Differentiable ℂ (fun u => G u - r / (u - s₀)))
    (hγan : AnalyticAt ℂ (DirichletCharacter.gammaFactor χ) s₀)
    (hγne : DirichletCharacter.gammaFactor χ s₀ ≠ 0)
    {z w : ℂ} (hzre : z.re < w.re) (hzim : z.im < w.im) (hz1 : -(1 : ℝ) < z.re)
    (h0in : z.re < 0 ∧ 0 < w.re ∧ z.im < 0 ∧ 0 < w.im)
    (hs0in : z.re < s₀.re ∧ s₀.re < w.re ∧ z.im < s₀.im ∧ s₀.im < w.im)
    {M : ℝ} (hMb : ∀ s ∈ Commons.NumberTheory.DirichletCharacter.rectSet z w,
      ‖G s - r / (s - s₀)‖ ≤ M) :
    Commons.NumberTheory.DirichletCharacter.rectInt z w
        (fun s => logDeriv (DirichletCharacter.gammaFactor χ) s * G s) =
      -(2 * (Real.pi : ℂ) * Complex.I) * (if χ.Even then G 0 else 0)
        + (2 * (Real.pi : ℂ) * Complex.I) *
            (logDeriv (DirichletCharacter.gammaFactor χ) s₀) * r := by
  let H : ℂ → ℂ := fun u => G u - r / (u - s₀)
  have hH : Differentiable ℂ H := hG
  have hre_ge : ∀ s ∈ rectSet z w, -(1 : ℝ) < s.re := by
    intro s hs
    obtain ⟨hre, -⟩ := Complex.mem_reProdIm.mp hs
    rw [Set.uIcc_of_le (le_of_lt hzre)] at hre
    linarith [hre.1, hz1]
  have hclog : ∀ s ∈ rectBoundary z w,
      ContinuousAt (fun u : ℂ => logDeriv (DirichletCharacter.gammaFactor χ) u) s := by
    intro s hs
    have hsre : -(1 : ℝ) < s.re := hre_ge s (rectBoundary_subset_rectSet hzre hzim hs)
    have hs0 : s ≠ 0 :=
      ne_zero_of_mem_rectBoundary h0in.1 h0in.2.1 h0in.2.2.1 h0in.2.2.2 hs
    exact continuousAt_logDeriv_gammaFactor χ hsre hs0
  have hf1 : ∀ s ∈ rectBoundary z w,
      ContinuousAt (fun s : ℂ => logDeriv (DirichletCharacter.gammaFactor χ) s * H s) s :=
    fun s hs => (hclog s hs).mul hH.continuous.continuousAt
  have hf2 : ∀ s ∈ rectBoundary z w,
      ContinuousAt (fun s : ℂ => logDeriv (DirichletCharacter.gammaFactor χ) s *
        (r / (s - s₀))) s := by
    intro s hs
    exact (hclog s hs).mul (ContinuousAt.div continuousAt_const
      (continuousAt_id.sub continuousAt_const)
      (sub_ne_zero.mpr (ne_of_mem_rectBoundary_of_inside hs0in hs)))
  have hcongr : rectInt z w (fun s => logDeriv (DirichletCharacter.gammaFactor χ) s * G s) =
      rectInt z w (fun s => logDeriv (DirichletCharacter.gammaFactor χ) s * H s +
        logDeriv (DirichletCharacter.gammaFactor χ) s * (r / (s - s₀))) := by
    apply rectInt_congr_boundary'
    intro s hs
    have hGs : G s = H s + r / (s - s₀) := by
      simp only [H]
      ring
    rw [hGs]
    ring
  rw [hcongr, rectInt_add_of_boundary_cts_aux hf1 hf2,
    rectInt_logDeriv_gammaFactor_mul_entire_aux χ hH hzre hzim hz1 h0in,
    rectInt_logDeriv_gammaFactor_mul_div_sub_aux χ hγne hzre hzim hz1 h0in hs0in]
  by_cases hE : χ.Even
  · rw [if_pos hE, if_pos hE, if_pos hE]
    have hG0 : G 0 = H 0 + r / ((0 : ℂ) - s₀) := by
      simp only [H]
      ring
    rw [hG0]
    ring
  · rw [if_neg hE, if_neg hE, if_neg hE]
    ring

end Commons.NumberTheory.DirichletCharacter
