import Mathlib
import Submission.Work.LinnikAreas.LoneLowerDefs
import Submission.Work.LinnikAreas.triPerronDefs
import Submission.Work.LinnikAreas.triFun_residue_decomp
import Submission.Work.LinnikAreas.triPerron_dslope_diff
import Submission.Commons.NumberTheory.DirichletCharacter.chebyshevPsiChi_explicit_formula_mult
import Submission.Commons.NumberTheory.DirichletCharacter.completedL_shift_identity_gen

/-!
# The Perron contour shift for the triangle kernel (`triPerron_shift`)

`triFun ψ β x s = ζ(s+β)L(s+β,ψ) x^s/(s(s+1))` is the Perron integrand with the triangle
("second order") kernel.  When `ψ` is non-principal and `L(β,ψ) = 0`, the integrand has a single
simple pole inside the rectangle `[(5/8-β) - iT, 1 + iT]`, at `s = 1-β`, with residue
`Res = L(1,ψ)x^{1-β}/((1-β)(2-β))` (the zero at `s = 0` coming from `L(s+β,ψ)` removes the
apparent pole of the kernel `1/(s(s+1))` there).  Cauchy's theorem on the rectangle therefore
gives the contour shift
`(1/2π)∫_{-T}^{T} F(1+it) dt = Res + (1/2π)∫_{-T}^{T} F(5/8-β+it) dt + (1/2πi)(∫ F(u+iT) - ∫ F(u-iT))`.
-/

namespace Work.LinnikAreas

open DirichletCharacter Complex MeasureTheory intervalIntegral
open scoped Real Topology BigOperators

noncomputable section

open Commons.NumberTheory.DirichletCharacter

/-- The rectangle integral of `F` over `[(5/8-β) - iT, 1 + iT]`, expanded into its four sides,
in exactly the shape used by `triPerron_shift`. -/
lemma rectInt_triPerron_expand (β T : ℝ) (F : ℂ → ℂ) :
    rectInt (triPerronZ β T) (triPerronW T) F =
      (∫ u in ((5 / 8 - β : ℝ))..1, F ((u : ℂ) - T * Complex.I))
      - (∫ u in ((5 / 8 - β : ℝ))..1, F ((u : ℂ) + T * Complex.I))
      + Complex.I * (∫ y in (-T)..T, F (1 + (y : ℂ) * Complex.I))
      - Complex.I * (∫ y in (-T)..T, F ((((5 / 8 - β : ℝ)) : ℂ) + (y : ℂ) * Complex.I)) := by
  simpa [triPerronZ, triPerronW, Complex.ofReal_one] using
    (rectInt_strip_expand (5 / 8 - β) 1 T F)


theorem triPerron_shift {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (hψ : ψ ≠ 1)
    {β x T : ℝ} (hβlo : 3 / 4 ≤ β) (hβ1 : β < 1) (hx : 0 < x) (hT : 0 < T)
    (hL0 : DirichletCharacter.LFunction ψ (β : ℂ) = 0) :
    (1 / (2 * Real.pi)) *
        (∫ y in (-T)..T, Work.LinnikAreas.triFun ψ β x (1 + (y : ℂ) * Complex.I))
      = DirichletCharacter.LFunction ψ 1 * (x : ℂ) ^ (((1 - β : ℝ)) : ℂ)
            / ((((1 - β : ℝ)) : ℂ) * (((2 - β : ℝ)) : ℂ))
        + (1 / (2 * Real.pi)) *
            (∫ y in (-T)..T,
              Work.LinnikAreas.triFun ψ β x (((5 / 8 - β : ℝ)) + (y : ℂ) * Complex.I))
        + (1 / (2 * Real.pi * Complex.I)) *
            ((∫ u in ((5 / 8 - β : ℝ))..1,
                Work.LinnikAreas.triFun ψ β x ((u : ℂ) + T * Complex.I))
              - (∫ u in ((5 / 8 - β : ℝ))..1,
                Work.LinnikAreas.triFun ψ β x ((u : ℂ) - T * Complex.I))) := by
  have hc1 : 5 / 8 - β < 1 := by linarith
  have hTm : -T < T := by linarith
  have hzre : (triPerronZ β T).re < (triPerronW T).re := by
    rw [triPerronZ_re, triPerronW_re]; linarith
  have hzim : (triPerronZ β T).im < (triPerronW T).im := by
    rw [triPerronZ_im, triPerronW_im]; linarith
  have huin : (triPerronZ β T).re < (triPerronU β).re ∧ (triPerronU β).re < (triPerronW T).re ∧
      (triPerronZ β T).im < (triPerronU β).im ∧ (triPerronU β).im < (triPerronW T).im := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [triPerronZ_re, triPerronW_re, triPerronU_re, triPerronZ_im, triPerronW_im,
        triPerronU_im] <;> linarith
  -- differentiability of the regularised integrand on the rectangle
  have hGdiff : DifferentiableOn ℂ (dslope (triPerronM ψ β x) (triPerronU β))
      (rectSet (triPerronZ β T) (triPerronW T)) := by
    have h := triPerron_dslope_diff ψ hψ hβ1 hx hT
    simpa [rectSet, triPerronZ_re, triPerronZ_im, triPerronW_re, triPerronW_im,
      Set.uIcc_of_le hc1.le, Set.uIcc_of_le hTm.le] using h
  -- pointwise residue decomposition on the boundary
  have hbd : ∀ s ∈ rectBoundary (triPerronZ β T) (triPerronW T),
      triFun ψ β x s = triPerronRes ψ β x / (s - triPerronU β)
        + dslope (triPerronM ψ β x) (triPerronU β) s := by
    intro s hs
    have hs0 : s ≠ 0 :=
      ne_zero_of_mem_rectBoundary (by rw [triPerronZ_re]; linarith)
        (by rw [triPerronW_re]; norm_num) (by rw [triPerronZ_im]; linarith)
        (by rw [triPerronW_im]; linarith) hs
    have hsu : s ≠ triPerronU β := ne_of_mem_rectBoundary_of_inside huin hs
    have hsm1 : s + 1 ≠ 0 := by
      intro h
      have hsV := rectBoundary_subset_rectSet hzre hzim hs
      have hre : s.re ∈ Set.uIcc (triPerronZ β T).re (triPerronW T).re :=
        (Complex.mem_reProdIm.mp hsV).1
      rw [triPerronZ_re, triPerronW_re, Set.uIcc_of_le hc1.le] at hre
      have h1 : s.re = -1 := by
        have := congrArg Complex.re h
        simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at this
        linarith
      linarith [hre.1]
    exact triFun_residue_decomp ψ hψ hβ1 hx hL0 hs0 hsu hsm1
  -- the rectangle integral of the integrand picks up the residue
  have hrect : rectInt (triPerronZ β T) (triPerronW T) (triFun ψ β x)
      = triPerronRes ψ β x * (2 * (Real.pi : ℂ) * Complex.I) := by
    have hcontf : ContinuousOn (fun s : ℂ => triPerronRes ψ β x / (s - triPerronU β))
        {s : ℂ | s ≠ triPerronU β} :=
      continuousOn_const.div (by fun_prop) (fun s hs => sub_ne_zero.mpr hs)
    obtain ⟨a1, a2, a3, a4⟩ := edgeIntegrable_of_continuousOn_ne huin hcontf
    obtain ⟨b1, b2, b3, b4⟩ := edgeIntegrable_of_continuousOn hGdiff.continuousOn
    rw [rectInt_congr_boundary' hbd,
      rectInt_add'' a1 b1 a2 b2 a3 b3 a4 b4,
      rectInt_const_div_sub_inside (triPerronRes ψ β x) hzre hzim huin,
      rectInt_eq_zero_of_differentiableOn hGdiff, add_zero]
  -- the four sides of the rectangle, in the shapes used by the statement
  set P : ℂ := ∫ u in ((5 / 8 - β : ℝ))..1, triFun ψ β x ((u : ℂ) - T * Complex.I) with hP
  set Q : ℂ := ∫ u in ((5 / 8 - β : ℝ))..1, triFun ψ β x ((u : ℂ) + T * Complex.I) with hQ
  set R : ℂ := ∫ y in (-T)..T, triFun ψ β x (1 + (y : ℂ) * Complex.I) with hR
  set S : ℂ := ∫ y in (-T)..T,
    triFun ψ β x ((((5 / 8 - β : ℝ)) : ℂ) + (y : ℂ) * Complex.I) with hS
  have hrel' : P - Q + Complex.I * R - Complex.I * S
      = triPerronRes ψ β x * (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [hP, hQ, hR, hS, ← rectInt_triPerron_expand β T (triFun ψ β x)]
    exact hrect
  have hrel : P - Q + Complex.I * (R - S)
      = triPerronRes ψ β x * (2 * (Real.pi : ℂ) * Complex.I) := by
    linear_combination hrel'
  -- elementary algebra: solve the rectangle identity for the top edge integral
  have hgoal : (1 / (2 * (Real.pi : ℂ))) * R
      = triPerronRes ψ β x + (1 / (2 * (Real.pi : ℂ))) * S
        + (1 / (2 * (Real.pi : ℂ) * Complex.I)) * (Q - P) := by
    have hπ : ((Real.pi : ℂ)) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hI : ((Complex.I : ℂ)) ≠ 0 := Complex.I_ne_zero
    have hneg : (-Complex.I) * Complex.I = 1 := by rw [neg_mul, Complex.I_mul_I]; ring
    have hy : (-Complex.I) * (2 * (Real.pi : ℂ) * Complex.I * triPerronRes ψ β x)
        = 2 * (Real.pi : ℂ) * triPerronRes ψ β x := by
      rw [show (-Complex.I) * (2 * (Real.pi : ℂ) * Complex.I * triPerronRes ψ β x)
          = ((-Complex.I) * Complex.I) * (2 * (Real.pi : ℂ) * triPerronRes ψ β x) by ring,
        hneg, one_mul]
    have h3 : (-Complex.I) * (P - Q + Complex.I * (R - S))
        = (-Complex.I) * (2 * (Real.pi : ℂ) * Complex.I * triPerronRes ψ β x) := by
      rw [hrel]; ring
    rw [mul_add, ← mul_assoc, hneg, one_mul, hy, neg_mul] at h3
    have key : R = 2 * (Real.pi : ℂ) * triPerronRes ψ β x + S + Complex.I * (P - Q) := by
      linear_combination h3
    field_simp
    rw [key, add_mul, add_mul]
    rw [show Complex.I * (P - Q) * Complex.I = (Q - P) by
      rw [show Complex.I * (P - Q) * Complex.I = (Complex.I * Complex.I) * (P - Q) by ring,
        Complex.I_mul_I]; ring]
  simpa [hP, hQ, hR, hS, triPerronRes] using hgoal

end

end Work.LinnikAreas
