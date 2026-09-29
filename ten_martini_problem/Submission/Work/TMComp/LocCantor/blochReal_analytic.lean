import Mathlib
import Submission.Work.TMComp.LocCantor.Bloch

/-!
# C17 (`P_LocCantor`) — real-analyticity and 1-periodicity of the real Bloch matrix

The real Bloch matrix `A = blochReal α θ u` (see `Defs.blochReal`) has entries
`A i j` built from the real and imaginary parts of the two components
`W 0 = U(x) e^{2πiθ}` and `W 1 = U(x-α)` of the Bloch vector, where `U = fourier u`
is the Fourier transform of the sequence `u`.

The two structural facts recorded here are exactly what the localisation argument of
AJ §5 needs about `A` *before* it can be used: `A` is entrywise real-analytic (so that
its determinant, its zero set, etc. are analytic objects), and `A` is 1-periodic
(because `U` is), so that `A` is a function on the circle and the relation
`A(x+α) = S_{λ⁻¹,E/λ}(x) A(x) R_θ` of `Bloch.lean` can be iterated.

The only input is that `U` is analytic (`hA`) and 1-periodic (`hper`) — in practice
supplied by `fourier_analytic` for exponentially decaying `u`.
-/

open Set

namespace Work.TMComp.LocCantor

/-- The real part of a real-analytic complex-valued function is real-analytic. -/
theorem analyticOnNhd_re_comp {f : ℝ → ℂ} (hf : AnalyticOnNhd ℝ f univ) :
    AnalyticOnNhd ℝ (fun x => (f x).re) univ := fun x _ =>
  (Complex.reCLM.analyticAt (f x)).comp (hf x trivial)

/-- The imaginary part of a real-analytic complex-valued function is real-analytic. -/
theorem analyticOnNhd_im_comp {f : ℝ → ℂ} (hf : AnalyticOnNhd ℝ f univ) :
    AnalyticOnNhd ℝ (fun x => (f x).im) univ := fun x _ =>
  (Complex.imCLM.analyticAt (f x)).comp (hf x trivial)

/-- Multiplication by a constant preserves real-analyticity of complex-valued functions. -/
theorem analyticOnNhd_mul_const {f : ℝ → ℂ} (hf : AnalyticOnNhd ℝ f univ) (c : ℂ) :
    AnalyticOnNhd ℝ (fun x => f x * c) univ := fun x _ =>
  (hf x trivial).mul analyticAt_const

/-- Precomposition with the translation `x ↦ x - a` preserves real-analyticity. -/
theorem analyticOnNhd_comp_sub_const {f : ℝ → ℂ} (hf : AnalyticOnNhd ℝ f univ) (a : ℝ) :
    AnalyticOnNhd ℝ (fun x => f (x - a)) univ := fun x _ =>
  AnalyticAt.comp (g := f) (f := fun y : ℝ => y - a) (hf (x - a) trivial)
    (analyticAt_id.sub analyticAt_const)

/-- The Bloch vector is 1-periodic as soon as `U` is. -/
theorem blochVec_add_one {α θ : ℝ} {u : ℤ → ℂ}
    (hper : ∀ x, Work.TMComp.fourier u (x + 1) = Work.TMComp.fourier u x) :
    ∀ x, Work.TMComp.blochVec α θ u (x + 1) = Work.TMComp.blochVec α θ u x := by
  intro x
  have hb0 : Work.TMComp.blochVec α θ u (x + 1) 0 = Work.TMComp.blochVec α θ u x 0 := by
    simp only [Work.TMComp.blochVec, Matrix.cons_val_zero]
    rw [hper x]
  have hb1 : Work.TMComp.blochVec α θ u (x + 1) 1 = Work.TMComp.blochVec α θ u x 1 := by
    simp only [Work.TMComp.blochVec, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [show (x + 1) - α = (x - α) + 1 by ring, hper]
  funext i
  fin_cases i
  · exact hb0
  · exact hb1

/-- **Real-analyticity and 1-periodicity of the real Bloch matrix.**  If the Fourier
transform `U = fourier u` is real-analytic and 1-periodic, then so is every entry of
`blochReal α θ u`, and `blochReal α θ u` itself is 1-periodic. -/
theorem blochReal_analytic {α θ : ℝ} {u : ℤ → ℂ}
    (hA : AnalyticOnNhd ℝ (Work.TMComp.fourier u) Set.univ)
    (hper : ∀ x, Work.TMComp.fourier u (x + 1) = Work.TMComp.fourier u x) :
    (∀ i j, AnalyticOnNhd ℝ (fun x => Work.TMComp.blochReal α θ u x i j) Set.univ) ∧
      (∀ x, Work.TMComp.blochReal α θ u (x + 1) = Work.TMComp.blochReal α θ u x) := by
  have h0 : AnalyticOnNhd ℝ
      (fun x => (Work.TMComp.fourier u x * Complex.exp (2 * Real.pi * θ * Complex.I)).re) univ :=
    analyticOnNhd_re_comp
      (analyticOnNhd_mul_const hA (Complex.exp (2 * Real.pi * θ * Complex.I)))
  have h1 : AnalyticOnNhd ℝ
      (fun x => (Work.TMComp.fourier u x * Complex.exp (2 * Real.pi * θ * Complex.I)).im) univ :=
    analyticOnNhd_im_comp
      (analyticOnNhd_mul_const hA (Complex.exp (2 * Real.pi * θ * Complex.I)))
  have h2 : AnalyticOnNhd ℝ (fun x => (Work.TMComp.fourier u (x - α)).re) univ :=
    analyticOnNhd_re_comp (analyticOnNhd_comp_sub_const hA α)
  have h3 : AnalyticOnNhd ℝ (fun x => (Work.TMComp.fourier u (x - α)).im) univ :=
    analyticOnNhd_im_comp (analyticOnNhd_comp_sub_const hA α)
  refine ⟨fun i j => ?_, fun x => ?_⟩
  · fin_cases i <;> fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  · have hbv : Work.TMComp.blochVec α θ u (x + 1) = Work.TMComp.blochVec α θ u x :=
      blochVec_add_one hper x
    exact congrArg (fun v : Fin 2 → ℂ => !![(v 0).re, (v 0).im; (v 1).re, (v 1).im]) hbv

end Work.TMComp.LocCantor
