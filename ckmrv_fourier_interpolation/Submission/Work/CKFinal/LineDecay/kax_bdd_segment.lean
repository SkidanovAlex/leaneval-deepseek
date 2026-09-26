import Mathlib
import Submission.Work.CKFinal.LineDecay.Defs
import Submission.Work.CKFinal.LineDecay.j_eq_tau_of_lines
import Submission.Work.Residues.KernelPoleLocation

namespace Work.CKFinal.LineDecay

open UpperHalfPlane

/-- The imaginary part of a horizontal translate `a +ᵥ z` of `z ∈ ℍ`. -/
private lemma im_vadd_real (a : ℝ) (z : ℍ) : (a +ᵥ z).im = z.im := by
  rw [← UpperHalfPlane.coe_im, UpperHalfPlane.coe_vadd]
  simp [Complex.add_im]

/-- The real part of a horizontal translate `a +ᵥ z` of `z ∈ ℍ`. -/
private lemma re_vadd_real (a : ℝ) (z : ℍ) : (a +ᵥ z).re = z.re + a := by
  rw [← UpperHalfPlane.coe_re, UpperHalfPlane.coe_vadd]
  simp [Complex.add_re]
  ring

/-- The imaginary part of the point `i t ∈ ℍ`. -/
private lemma im_imagAxis (t : ℝ) (h : 0 < t) : (Work.Kernels.imagAxis t h).im = t := by
  rw [← UpperHalfPlane.coe_im, Work.Kernels.imagAxis]
  simp

/-- The real part of the point `i t ∈ ℍ`. -/
private lemma re_imagAxis (t : ℝ) (h : 0 < t) : (Work.Kernels.imagAxis t h).re = 0 := by
  rw [← UpperHalfPlane.coe_re, Work.Kernels.imagAxis]
  simp

/-- The horizontal segment `x ↦ x + i·1` is a continuous curve in `ℍ`. -/
private lemma continuous_segment (w₀ : ℍ) : Continuous (fun x : ℝ => x +ᵥ w₀) := by
  rw [UpperHalfPlane.isEmbedding_coe.continuous_iff]
  show Continuous (fun x : ℝ => ((x +ᵥ w₀ : ℍ) : ℂ))
  simp only [UpperHalfPlane.coe_vadd]
  fun_prop

/-- **Boundedness of the kernel on the horizontal segment `[-1+i, 1+i]` for `τ` on the lines.**

For `τ` with `Re τ = ±1/2` and `Im τ ≥ 12`, the function `x ↦ K^{(d)}(τ, x+i)` (`x ∈ [-1,1]`) is
bounded: no point of the segment lies on the `SL(2,ℤ)`-orbit of `τ`, since an orbit point with
`-1 ≤ Re ≤ 1` and `Im ≥ 1` is one of `τ, τ-1, τ+1` (`j_eq_tau_of_lines`), whose imaginary parts are
`≥ 12 > 1`; and `ζ ↦ K^{(d)}(τ,ζ)` is holomorphic off the orbit
(`Work.Residues.mdifferentiableAt_Kfun_snd`), hence continuous on the compact segment. -/
theorem kax_bdd_segment (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (hτ : τ.re = 1 / 2 ∨ τ.re = - 1 / 2) (hy : 12 ≤ τ.im) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      ‖Work.CKFinal.Kax (Work.Kernels.Kfun ℓ d) τ x 1‖ ≤ B := by
  have h1pos : (0:ℝ) < 1 := by norm_num
  -- the point `i` of the segment
  set w₀ : ℍ := Work.Kernels.imagAxis 1 h1pos with hw₀
  -- the segment map `x ↦ x + i` is continuous
  have hcontvadd : Continuous (fun x : ℝ => x +ᵥ w₀) := continuous_segment w₀
  -- no point of the segment lies on the orbit of `τ`
  have hne : ∀ x ∈ Set.Icc (-1:ℝ) 1,
      Work.Kernels.jInvariantFun (x +ᵥ w₀) ≠ Work.Kernels.jInvariantFun τ := by
    intro x hx hjeq
    have him3 : (3:ℝ) ≤ τ.im := by linarith
    have hwre : (x +ᵥ w₀).re = x := by rw [hw₀, re_vadd_real, re_imagAxis]; ring
    have hwim : (x +ᵥ w₀).im = 1 := by rw [hw₀, im_vadd_real, im_imagAxis]
    rcases Work.CKFinal.LineDecay.j_eq_tau_of_lines τ (x +ᵥ w₀) hτ him3
        (by rw [hwre]; exact hx.1) (by rw [hwre]; exact hx.2) (by rw [hwim])
        hjeq with h | h | h
    · rw [h] at hwim; linarith
    · rw [h, im_vadd_real] at hwim; linarith
    · rw [h, im_vadd_real] at hwim; linarith
  -- `ζ ↦ K(τ,ζ)` is continuous at every point off the orbit
  have hcontat : ∀ ζ : ℍ, Work.Kernels.jInvariantFun ζ ≠ Work.Kernels.jInvariantFun τ →
      ContinuousAt (fun ζ : ℍ => Work.Kernels.Kfun ℓ d τ ζ) ζ :=
    fun ζ hζ => (Work.Residues.mdifferentiableAt_Kfun_snd ℓ d hd τ ζ hζ).continuousAt
  -- hence the composite is continuous on the compact segment
  have hcontOn : ContinuousOn (fun x : ℝ => Work.Kernels.Kfun ℓ d τ (x +ᵥ w₀))
      (Set.Icc (-1:ℝ) 1) := by
    intro x hx
    have h1 : ContinuousAt (fun x : ℝ => Work.Kernels.Kfun ℓ d τ (x +ᵥ w₀)) x :=
      ContinuousAt.comp (x := x) (f := fun t : ℝ => t +ᵥ w₀)
        (g := fun ζ : ℍ => Work.Kernels.Kfun ℓ d τ ζ)
        (hcontat (x +ᵥ w₀) (hne x hx)) (hcontvadd.continuousAt)
    exact h1.continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcontOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx
  rw [Work.CKFinal.Kax, dif_pos h1pos]
  exact le_trans (hC x hx) (le_max_left _ _)

end Work.CKFinal.LineDecay
