import Mathlib
import Submission.Work.LinnikAreas.triPerronDefs
import Submission.Work.LinnikAreas.triFun_residue_decomp
import Submission.Work.LinnikAreas.triPerron_dslope_diff
import Submission.Work.Sieve.perronShift_topEdge_solve
import Submission.Commons.NumberTheory.DirichletCharacter.chebyshevPsiChi_explicit_formula_mult

/-!
# The Perron contour shift for the triangle kernel with a general left edge

`Work.LinnikAreas.triPerron_shift` proves the contour shift for the rectangle
`[5/8 - β, 1] × [-T, T]`.  Here the left edge is moved to `σ₀ - β` for an arbitrary
`1/2 < σ₀ < 1`: the exceptional zero `β` of `L(·, ψ)` still produces exactly one simple
pole inside the rectangle (at `s = 1 - β`), the residue is the same, and the regularised
integrand stays holomorphic on the (possibly wider) rectangle.  Hence the identity holds
with `5/8` replaced by `σ₀`.

Two points differ from the `5/8` case.

* The holomorphy of the regularised integrand `dslope (triPerronM ψ β x) (1-β)` on the
  rectangle, now possibly wider than `[5/8-β, 1] × [-T, T]`, is
  `differentiableOn_dslope_triPerronM_gen`.
* The pointwise residue decomposition `triFun ψ β x s = Res/(s-(1-β)) + dslope M (1-β) s`
  requires `s ≠ 0`, and when `σ₀ = β` the left edge passes through `s = 0`, where Lean's
  totalised division makes `triFun` vanish rather than take its limiting value
  `triPerronM ψ β x 0 / (0 - (1-β))`.  Interval integrals do not see single points, so the
  rectangle integral is unaffected: `rectInt_congr_boundary_off_zero`.
-/

namespace Work.LinnikAreas

open Complex DirichletCharacter

noncomputable section

/-- `dslope (triPerronM ψ β x) (triPerronU β)` is complex differentiable on the closed
rectangle `[A-β, 1] × [-T, T]` for every `A > 1/2` (and `β < 1`, so the rectangle stays
inside the half-plane where `triPerronM` is holomorphic, and stays away from the pole
`s = -1`).  This is `triPerron_dslope_diff` with `5/8` replaced by `A`. -/
lemma differentiableOn_dslope_triPerronM_gen {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N)
    (hψ : ψ ≠ 1) {β x T A : ℝ} (hA : 1 / 2 < A) (hβ1 : β < 1) (hx : 0 < x) (hT : 0 < T) :
    DifferentiableOn ℂ (dslope (triPerronM ψ β x) (triPerronU β))
      (Complex.reProdIm (Set.Icc (A - β) 1) (Set.Icc (-T) T)) := by
  set R : Set ℂ := Complex.reProdIm (Set.Icc (A - β) 1) (Set.Icc (-T) T) with hRdef
  set V : Set ℂ := Complex.reProdIm (Set.Ioo (1 / 2 - β) (2 - β)) (Set.Ioo (-T - 1) (T + 1))
    with hVdef
  have hRV : R ⊆ V := by
    intro s hs
    rw [hRdef] at hs
    rw [hVdef]
    obtain ⟨hre, him⟩ := Complex.mem_reProdIm.mp hs
    exact Complex.mem_reProdIm.mpr
      ⟨⟨by linarith [hre.1], by linarith [hre.2, hβ1]⟩,
       ⟨by linarith [him.1], by linarith [him.2]⟩⟩
  have hVopen : IsOpen V := by
    rw [hVdef]; exact isOpen_Ioo.reProdIm isOpen_Ioo
  have hcV : triPerronU β ∈ V := by
    rw [hVdef]
    exact Complex.mem_reProdIm.mpr
      ⟨⟨by rw [triPerronU_re]; linarith, by rw [triPerronU_re]; linarith⟩,
       ⟨by rw [triPerronU_im]; linarith, by rw [triPerronU_im]; linarith⟩⟩
  have hfV : DifferentiableOn ℂ (triPerronM ψ β x) V := by
    rw [hVdef]
    exact differentiableOn_triPerronM ψ hψ hβ1 hx
  exact differentiableOn_dslope_of_isOpen_mem hVopen hRV hcV hfV

end

end Work.LinnikAreas

namespace Work.Sieve

open DirichletCharacter Complex MeasureTheory intervalIntegral
open scoped Real Topology BigOperators
open Commons.NumberTheory.DirichletCharacter
open Work.LinnikAreas

noncomputable section

/-- The set `{0} ⊆ ℝ` is null. -/
lemma ae_ne_zero_volume : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by
  rw [MeasureTheory.ae_iff]
  simp

/-- Interval integrals do not see the single parameter value `0`. -/
lemma intervalIntegral_congr_ae_off_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} {f g : ℝ → E} (h : ∀ x ∈ Set.uIcc a b, x ≠ 0 → f x = g x) :
    (∫ x in a..b, f x) = ∫ x in a..b, g x := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [ae_ne_zero_volume] with x hx hmem
  exact h x (Set.uIoc_subset_uIcc hmem) hx

/-- `rectInt` is unchanged if two integrands agree on the boundary of the rectangle except
possibly at `s = 0`.  On each of the four sides the side parameter is a real part or an
imaginary part of the boundary point, so the set of parameters where the two integrands can
disagree is contained in `{0}`, which is null. -/
lemma rectInt_congr_boundary_off_zero {z w : ℂ} {f g : ℂ → ℂ}
    (h : ∀ s ∈ rectBoundary z w, s ≠ 0 → f s = g s) :
    rectInt z w f = rectInt z w g := by
  have h1 : (∫ x : ℝ in z.re..w.re, f (x + z.im * Complex.I))
      = (∫ x : ℝ in z.re..w.re, g (x + z.im * Complex.I)) := by
    apply intervalIntegral_congr_ae_off_zero
    intro x hx hx0
    refine h _ (Or.inl ⟨by simpa using hx, Or.inl (by simp)⟩) ?_
    intro h0
    exact hx0 (by simpa using congrArg Complex.re h0)
  have h2 : (∫ x : ℝ in z.re..w.re, f (x + w.im * Complex.I))
      = (∫ x : ℝ in z.re..w.re, g (x + w.im * Complex.I)) := by
    apply intervalIntegral_congr_ae_off_zero
    intro x hx hx0
    refine h _ (Or.inl ⟨by simpa using hx, Or.inr (by simp)⟩) ?_
    intro h0
    exact hx0 (by simpa using congrArg Complex.re h0)
  have h3 : (∫ y : ℝ in z.im..w.im, f (w.re + y * Complex.I))
      = (∫ y : ℝ in z.im..w.im, g (w.re + y * Complex.I)) := by
    apply intervalIntegral_congr_ae_off_zero
    intro y hy hy0
    refine h _ (Or.inr ⟨by simpa using hy, Or.inr (by simp)⟩) ?_
    intro h0
    exact hy0 (by simpa using congrArg Complex.im h0)
  have h4 : (∫ y : ℝ in z.im..w.im, f (z.re + y * Complex.I))
      = (∫ y : ℝ in z.im..w.im, g (z.re + y * Complex.I)) := by
    apply intervalIntegral_congr_ae_off_zero
    intro y hy hy0
    refine h _ (Or.inr ⟨by simpa using hy, Or.inl (by simp)⟩) ?_
    intro h0
    exact hy0 (by simpa using congrArg Complex.im h0)
  rw [rectInt_eq_def, rectInt_eq_def, h1, h2, h3, h4]

/-- Expansion of the rectangle integral over `[σ₀-β-iT, 1+iT]` into its four sides, in the
shape used by `triPerron_shift_gen`. -/
lemma rectInt_expand_gen (z w : ℂ) {σ₀ β T : ℝ} (hzre : z.re = σ₀ - β) (hzim : z.im = -T)
    (hwre : w.re = 1) (hwim : w.im = T) (F : ℂ → ℂ) :
    rectInt z w F =
      (∫ u in ((σ₀ - β : ℝ))..1, F ((u : ℂ) - T * Complex.I))
      - (∫ u in ((σ₀ - β : ℝ))..1, F ((u : ℂ) + T * Complex.I))
      + Complex.I * (∫ y in (-T)..T, F (1 + (y : ℂ) * Complex.I))
      - Complex.I * (∫ y in (-T)..T, F ((((σ₀ - β : ℝ)) : ℂ) + (y : ℂ) * Complex.I)) := by
  rw [rectInt_eq_def, hzre, hwre, hzim, hwim]
  simp only [Complex.ofReal_neg, neg_mul]
  congr 2

theorem triPerron_shift_gen {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (hψ : ψ ≠ 1)
    {β x T σ₀ : ℝ} (hβ0 : 1/2 < β) (hβ1 : β < 1) (hσ0 : 1/2 < σ₀) (hσ1 : σ₀ < 1)
    (hx : 0 < x) (hT : 0 < T) (hL0 : DirichletCharacter.LFunction ψ (β : ℂ) = 0) :
    (1 / (2 * Real.pi)) *
        (∫ y in (-T)..T, Work.LinnikAreas.triFun ψ β x (1 + (y : ℂ) * Complex.I))
      = Work.LinnikAreas.triPerronRes ψ β x
        + (1 / (2 * Real.pi)) *
            (∫ y in (-T)..T, Work.LinnikAreas.triFun ψ β x ((σ₀ - β : ℝ) + (y : ℂ) * Complex.I))
        + (1 / (2 * Real.pi * Complex.I)) *
            ((∫ u in ((σ₀ - β : ℝ))..1, Work.LinnikAreas.triFun ψ β x ((u : ℂ) + T * Complex.I))
              - (∫ u in ((σ₀ - β : ℝ))..1, Work.LinnikAreas.triFun ψ β x ((u : ℂ) - T * Complex.I))) := by
  have hβpos : 0 < β := by linarith
  -- the rectangle `z = (σ₀-β) - iT`, `w = 1 + iT`
  set z : ℂ := (((σ₀ - β : ℝ)) : ℂ) - (T : ℂ) * Complex.I with hzdef
  set w : ℂ := (1 : ℂ) + (T : ℂ) * Complex.I with hwdef
  have hzre : z.re = σ₀ - β := by rw [hzdef]; simp
  have hzim : z.im = -T := by rw [hzdef]; simp
  have hwre : w.re = 1 := by rw [hwdef]; simp
  have hwim : w.im = T := by rw [hwdef]; simp
  have hc1 : σ₀ - β < 1 := by linarith
  have hTm : -T < T := by linarith
  have hzre' : z.re < w.re := by rw [hzre, hwre]; linarith
  have hzim' : z.im < w.im := by rw [hzim, hwim]; linarith
  have huin : z.re < (triPerronU β).re ∧ (triPerronU β).re < w.re ∧
      z.im < (triPerronU β).im ∧ (triPerronU β).im < w.im := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [hzre, hwre, hzim, hwim, triPerronU_re, triPerronU_im] <;> linarith
  -- holomorphy of the regularised integrand on the closed rectangle
  have hGdiff : DifferentiableOn ℂ (dslope (triPerronM ψ β x) (triPerronU β))
      (rectSet z w) := by
    have h := differentiableOn_dslope_triPerronM_gen (N := N) ψ hψ (β := β) (x := x) (T := T)
      (A := σ₀) hσ0 hβ1 hx hT
    simpa [rectSet, hzre, hwre, hzim, hwim, Set.uIcc_of_le hc1.le, Set.uIcc_of_le hTm.le] using h
  -- pointwise residue decomposition off `s = 0`
  have hbd : ∀ s ∈ rectBoundary z w, s ≠ 0 →
      triFun ψ β x s = triPerronRes ψ β x / (s - triPerronU β)
        + dslope (triPerronM ψ β x) (triPerronU β) s := by
    intro s hs hs0
    have hsu : s ≠ triPerronU β := ne_of_mem_rectBoundary_of_inside huin hs
    have hsm1 : s + 1 ≠ 0 := by
      intro h
      have hsV := rectBoundary_subset_rectSet hzre' hzim' hs
      have hre : s.re ∈ Set.uIcc z.re w.re := (Complex.mem_reProdIm.mp hsV).1
      rw [hzre, hwre, Set.uIcc_of_le hc1.le] at hre
      have h1 : s.re = -1 := by
        have := congrArg Complex.re h
        simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at this
        linarith
      linarith [hre.1]
    exact triFun_residue_decomp ψ hψ hβ1 hx hL0 hs0 hsu hsm1
  -- the rectangle integral of `triFun` picks up exactly the residue at `1-β`
  have hrect : rectInt z w (triFun ψ β x)
      = triPerronRes ψ β x * (2 * (Real.pi : ℂ) * Complex.I) := by
    have hcontf : ContinuousOn (fun s : ℂ => triPerronRes ψ β x / (s - triPerronU β))
        {s : ℂ | s ≠ triPerronU β} :=
      continuousOn_const.div (by fun_prop) (fun s hs => sub_ne_zero.mpr hs)
    obtain ⟨a1, a2, a3, a4⟩ := edgeIntegrable_of_continuousOn_ne huin hcontf
    obtain ⟨b1, b2, b3, b4⟩ := edgeIntegrable_of_continuousOn hGdiff.continuousOn
    rw [rectInt_congr_boundary_off_zero hbd,
      rectInt_add'' a1 b1 a2 b2 a3 b3 a4 b4,
      rectInt_const_div_sub_inside (triPerronRes ψ β x) hzre' hzim' huin,
      rectInt_eq_zero_of_differentiableOn hGdiff, add_zero]
  -- the four sides, in the shapes used by the statement
  set P : ℂ := ∫ u in ((σ₀ - β : ℝ))..1, triFun ψ β x ((u : ℂ) - T * Complex.I) with hP
  set Q : ℂ := ∫ u in ((σ₀ - β : ℝ))..1, triFun ψ β x ((u : ℂ) + T * Complex.I) with hQ
  set R : ℂ := ∫ y in (-T)..T, triFun ψ β x (1 + (y : ℂ) * Complex.I) with hR
  set S : ℂ := ∫ y in (-T)..T, triFun ψ β x ((((σ₀ - β : ℝ)) : ℂ) + (y : ℂ) * Complex.I) with hS
  have hrel' : P - Q + Complex.I * R - Complex.I * S
      = triPerronRes ψ β x * (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [hP, hQ, hR, hS, ← rectInt_expand_gen z w (σ₀ := σ₀) (β := β) (T := T)
      hzre hzim hwre hwim (triFun ψ β x)]
    exact hrect
  have hrel : P - Q + Complex.I * (R - S)
      = triPerronRes ψ β x * (2 * (Real.pi : ℂ) * Complex.I) := by
    linear_combination hrel'
  -- elementary algebra (delegated as `perronShift_topEdge_solve`): solve the rectangle
  -- identity for the top edge integral
  have hgoal : (1 / (2 * (Real.pi : ℂ))) * R
      = triPerronRes ψ β x + (1 / (2 * (Real.pi : ℂ))) * S
        + (1 / (2 * (Real.pi : ℂ) * Complex.I)) * (Q - P) :=
    perronShift_topEdge_solve hrel
  simpa [hP, hQ, hR, hS] using hgoal

end

end Work.Sieve
