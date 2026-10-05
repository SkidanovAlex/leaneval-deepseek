import Mathlib
import Submission.Work.RPV.Defs

/-!
# `Work.RPV.hasDerivAt_levelPt_snd`

The partial derivative in the second parameter `t` of the family of level-curve points

`s ↦ levelPt (Γ σ s) σ (A σ s)  =  (((e^{-i A(σ,s)} Γ σ s).im, A σ s),
                                    ((e^{-i A(σ,s)} Γ σ s).re, ‖Γ σ s‖²/2 - σ - 1))`.

Writing `e = exp (-(A σ t) i)`, `z = Γ σ t`, the derivative is

`(((e (Γt - A_t i z)).im, A_t), ((e (Γt - A_t i z)).re, Re(z̄ Γt)))`.

The proof is a straight computation: differentiate the phase factor `exp (-(A σ ·) i)` with the
chain rule, multiply by `Γ σ ·`, take real/imaginary parts (a continuous linear map, so the
derivative is the same map applied to the derivative), and separate
`‖Γ σ s‖² / 2 = normSq (Γ σ s) / 2` into squares of the coordinate functions `re` and `im`.  The
four real coordinates are then reassembled with `HasDerivAt.prodMk`.
-/

set_option autoImplicit false

noncomputable section

namespace Work.RPV

theorem hasDerivAt_levelPt_snd (Γ : ℝ → ℝ → ℂ) (A : ℝ → ℝ → ℝ) (σ t : ℝ) (Γt : ℂ) (At : ℝ)
    (hΓt : HasDerivAt (fun s => Γ σ s) Γt t) (hAt : HasDerivAt (fun s => A σ s) At t) :
    HasDerivAt (fun s => Work.RPV.levelPt (Γ σ s) σ (A σ s))
      (((Complex.exp (-(A σ t : ℂ) * Complex.I) * (Γt - (At : ℂ) * Complex.I * Γ σ t)).im, At),
       ((Complex.exp (-(A σ t : ℂ) * Complex.I) * (Γt - (At : ℂ) * Complex.I * Γ σ t)).re,
        ((starRingEnd ℂ) (Γ σ t) * Γt).re)) t := by
  -- derivative of the phase factor `s ↦ exp (-(A σ s) i)`
  have hexp : HasDerivAt (fun s : ℝ => Complex.exp (-(A σ s : ℂ) * Complex.I))
      (Complex.exp (-(A σ t : ℂ) * Complex.I) * (-(At : ℂ) * Complex.I)) t := by
    have h1 : HasDerivAt (fun s : ℝ => -(A σ s : ℂ) * Complex.I) (-(At : ℂ) * Complex.I) t := by
      simpa using ((hAt.ofReal_comp).neg).mul_const Complex.I
    exact h1.cexp
  -- derivative of `v s = exp (-(A σ s) i) * Γ σ s`
  have hv : HasDerivAt (fun s : ℝ => Complex.exp (-(A σ s : ℂ) * Complex.I) * Γ σ s)
      (Complex.exp (-(A σ t : ℂ) * Complex.I) * (Γt - (At : ℂ) * Complex.I * Γ σ t)) t := by
    have := hexp.mul hΓt
    convert this using 1
    ring
  have hre : HasDerivAt (fun s : ℝ => (Complex.exp (-(A σ s : ℂ) * Complex.I) * Γ σ s).re)
      (Complex.exp (-(A σ t : ℂ) * Complex.I) * (Γt - (At : ℂ) * Complex.I * Γ σ t)).re t := by
    have h' := (Complex.reCLM.hasFDerivAt.comp t hv.hasFDerivAt).hasDerivAt
    simp only [ContinuousLinearMap.comp_apply] at h'
    convert h' using 1
    · ext y; rfl
    · simp
  have him : HasDerivAt (fun s : ℝ => (Complex.exp (-(A σ s : ℂ) * Complex.I) * Γ σ s).im)
      (Complex.exp (-(A σ t : ℂ) * Complex.I) * (Γt - (At : ℂ) * Complex.I * Γ σ t)).im t := by
    have h' := (Complex.imCLM.hasFDerivAt.comp t hv.hasFDerivAt).hasDerivAt
    simp only [ContinuousLinearMap.comp_apply] at h'
    convert h' using 1
    · ext y; rfl
    · simp
  -- derivatives of the real and imaginary parts of `Γ σ ·`
  have hr : HasDerivAt (fun s : ℝ => (Γ σ s).re) Γt.re t := by
    have h' := (Complex.reCLM.hasFDerivAt.comp t hΓt.hasFDerivAt).hasDerivAt
    simp only [ContinuousLinearMap.comp_apply] at h'
    convert h' using 1
    · ext y; rfl
    · simp
  have hi : HasDerivAt (fun s : ℝ => (Γ σ s).im) Γt.im t := by
    have h' := (Complex.imCLM.hasFDerivAt.comp t hΓt.hasFDerivAt).hasDerivAt
    simp only [ContinuousLinearMap.comp_apply] at h'
    convert h' using 1
    · ext y; rfl
    · simp
  -- derivative of `normSq (Γ σ ·) = ‖Γ σ ·‖ ^ 2`
  have hn : HasDerivAt (fun s : ℝ => Complex.normSq (Γ σ s))
      (2 * ((starRingEnd ℂ) (Γ σ t) * Γt).re) t := by
    have hs := (hr.pow 2).add (hi.pow 2)
    convert hs using 1
    · ext s; simp only [Pi.pow_apply, Pi.add_apply, Complex.normSq_apply]; ring
    · rw [Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring
  -- derivative of the `p₂`-coordinate `‖Γ σ s‖ ^ 2 / 2 - σ - 1`
  have hp2 : HasDerivAt (fun s : ℝ => ‖Γ σ s‖ ^ 2 / 2 - σ - 1)
      (((starRingEnd ℂ) (Γ σ t) * Γt).re) t := by
    have hs : HasDerivAt (fun s : ℝ => ‖Γ σ s‖ ^ 2 / 2)
        (((starRingEnd ℂ) (Γ σ t) * Γt).re) t := by
      have := hn.div_const 2
      convert this using 1
      · ext s; simp [Complex.sq_norm]
      · ring
    have := hs.sub_const (σ + 1)
    simpa using this
  -- assemble the four coordinates
  have hF : HasDerivAt (fun s : ℝ => ((Complex.exp (-(A σ s : ℂ) * Complex.I) * Γ σ s).im,
        A σ s))
      ((Complex.exp (-(A σ t : ℂ) * Complex.I) * (Γt - (At : ℂ) * Complex.I * Γ σ t)).im,
        At) t :=
    him.prodMk hAt
  have hG : HasDerivAt (fun s : ℝ => ((Complex.exp (-(A σ s : ℂ) * Complex.I) * Γ σ s).re,
        ‖Γ σ s‖ ^ 2 / 2 - σ - 1))
      ((Complex.exp (-(A σ t : ℂ) * Complex.I) * (Γt - (At : ℂ) * Complex.I * Γ σ t)).re,
        ((starRingEnd ℂ) (Γ σ t) * Γt).re) t :=
    hre.prodMk hp2
  have := hF.prodMk hG
  convert this using 1
  ext <;> simp [levelPt]

end Work.RPV
