import Mathlib
import Submission.Work.RPB.B2.hasDerivAt_div_norm

/-!
# B1: one-dimensional argument lift

The one-variable heart of `Work.RPB.B1.argument_lift`: if `g : ℝ → ℂ` is `C¹` and nowhere
vanishing and `g 0 = ‖g 0‖ · exp (θ · I)`, then for every `s`

  `g s = ‖g s‖ · exp ((θ + ∫_0^s Im (g'/g)) · I)`.

The proof is the standard one.  Put `A s = θ + ∫_0^s Im (g'/g)` and
`Q s = exp (-(A s) · I) · (g s / ‖g s‖)`.  By the fundamental theorem of calculus
`A' = Im (g'/g)`, and the rule for the derivative of the unit vector field
(`Work.RPB.B2.hasDerivAt_div_norm`) shows `Q' = 0`.  Hence `Q` is constant, and `Q 0 = 1`
by the initial condition, which gives `g s / ‖g s‖ = exp (A s · I)`.
-/

open scoped ContDiff
open MeasureTheory

namespace Work.RPB.B1

noncomputable section

/-- `(z / w).im = ωC w z / ‖w‖ ^ 2`: the imaginary part of a quotient is the symplectic form of
`Work.RPV.Defs` divided by the squared norm.  Valid for all `w` (both sides are `0` at `w = 0`). -/
lemma im_div_eq_omegaC_div_normSq (z w : ℂ) :
    (z / w).im = Work.RPV.ωC w z / ‖w‖ ^ 2 := by
  rw [Complex.div_im, Complex.normSq_eq_norm_sq, Work.RPV.ωC]
  simp only [Complex.conj_re, Complex.conj_im, Complex.mul_im]
  ring

/-- The first partial derivative `(s,t) ↦ ∂₁F(s,t) = deriv (fun σ => F σ t) s` of a jointly smooth
`F` is again jointly smooth (it is the composition of `fderiv ℝ F` with the constant direction
`(1,0)`, using `ContDiff.fderiv_apply`). -/
theorem fderiv_slice_contDiff' (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => F q.1 q.2)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => deriv (fun σ : ℝ => F σ q.2) q.1) := by
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry (fun x : ℝ × ℝ => fun y : ℝ => F y x.2)) := by
    have hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : (ℝ × ℝ) × ℝ => (p.2, p.1.2)) := by fun_prop
    have h := hF.comp hψ
    convert h using 1
    ext p
    rfl
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × ℝ => x.1) := by fun_prop
  have hk : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : ℝ × ℝ => (1 : ℝ)) := contDiff_const
  have h := ContDiff.fderiv_apply (𝕜 := ℝ) hf hg hk
    (le_rfl : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
  exact h

/-- The one-dimensional argument lift. -/
theorem argument_lift_oneDim {g : ℝ → ℂ} {θ : ℝ}
    (hg : ContDiff ℝ 1 g) (hne : ∀ s, g s ≠ 0)
    (h0 : g 0 = (‖g 0‖ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) :
    ∀ s, g s = (‖g s‖ : ℂ) * Complex.exp
      (((θ + ∫ τ in (0 : ℝ)..s, (deriv g τ / g τ).im) : ℂ) * Complex.I) := by
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hgc : Continuous g := hg.continuous
  have hderiv_cont : Continuous (deriv g) := hg.continuous_deriv le_rfl
  set q : ℝ → ℝ := fun τ => (deriv g τ / g τ).im with hq_def
  have hq_cont : Continuous q := by
    rw [hq_def]
    exact Complex.continuous_im.comp (hderiv_cont.div hgc hne)
  set A : ℝ → ℝ := fun s => θ + ∫ τ in (0 : ℝ)..s, q τ with hA_def
  have hA_deriv : ∀ s, HasDerivAt A (q s) s := by
    intro s
    have hint : HasDerivAt (fun u : ℝ => ∫ τ in (0 : ℝ)..u, q τ) (q s) s :=
      intervalIntegral.integral_hasDerivAt_right
        (hq_cont.intervalIntegrable 0 s)
        (hq_cont.stronglyMeasurableAtFilter volume (nhds s))
        hq_cont.continuousAt
    rw [hA_def]
    exact hint.const_add θ
  -- derivative of `s ↦ exp (-(A s) * I)`
  have hexp_deriv : ∀ s, HasDerivAt (fun u : ℝ => Complex.exp (-(A u : ℂ) * Complex.I))
      (Complex.exp (-(A s : ℂ) * Complex.I) * (-(q s : ℂ) * Complex.I)) s := by
    intro s
    have hAc : HasDerivAt (fun u : ℝ => (A u : ℂ)) ((q s : ℂ)) s := (hA_deriv s).ofReal_comp
    have h1 : HasDerivAt (fun u : ℝ => -(A u : ℂ) * Complex.I) (-(q s : ℂ) * Complex.I) s := by
      have h2 := hAc.neg.mul_const Complex.I
      exact h2
    exact h1.cexp
  -- derivative of the unit vector `s ↦ g s / ‖g s‖`
  have hratio_deriv : ∀ s, HasDerivAt (fun u : ℝ => g u / ‖g u‖)
      (Complex.I * (g s / ‖g s‖) *
        ((Work.RPV.ωC (g s) (deriv g s) / ‖g s‖ ^ 2 : ℝ) : ℂ)) s := fun s =>
    Work.RPB.B2.hasDerivAt_div_norm g (deriv g s) s ((hgd s).hasDerivAt) (hne s)
  -- the product has derivative zero everywhere
  have hQ_deriv : ∀ s, HasDerivAt
      (fun u : ℝ => Complex.exp (-(A u : ℂ) * Complex.I) * (g u / ‖g u‖)) 0 s := by
    intro s
    refine ((hexp_deriv s).mul (hratio_deriv s)).congr_deriv ?_
    have hw : ((Work.RPV.ωC (g s) (deriv g s) / ‖g s‖ ^ 2 : ℝ) : ℂ) = (q s : ℂ) := by
      have hqs : q s = (deriv g s / g s).im := by rw [hq_def]
      simp only [hqs, im_div_eq_omegaC_div_normSq]
    rw [hw]
    ring
  -- hence it is constant, and its value at `0` is `1`
  have hQ_const : ∀ s, Complex.exp (-(A s : ℂ) * Complex.I) * (g s / ‖g s‖)
      = Complex.exp (-(A 0 : ℂ) * Complex.I) * (g 0 / ‖g 0‖) := fun s =>
    is_const_of_deriv_eq_zero (fun x => (hQ_deriv x).differentiableAt)
      (fun x => (hQ_deriv x).deriv) s 0
  have hA0 : A 0 = θ := by
    rw [hA_def]
    simp
  have hQ0 : Complex.exp (-(A 0 : ℂ) * Complex.I) * (g 0 / ‖g 0‖) = 1 := by
    rw [hA0]
    have hnorm_ne : (‖g 0‖ : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]
      exact norm_ne_zero_iff.mpr (hne 0)
    have hratio : g 0 / ‖g 0‖ = Complex.exp ((θ : ℂ) * Complex.I) := by
      rw [div_eq_iff hnorm_ne]
      exact h0.trans (mul_comm _ _)
    rw [hratio, ← Complex.exp_add]
    have hz : -(θ : ℂ) * Complex.I + (θ : ℂ) * Complex.I = 0 := by ring
    rw [hz, Complex.exp_zero]
  -- conclude
  intro s
  have hQs1 : Complex.exp (-(A s : ℂ) * Complex.I) * (g s / ‖g s‖) = 1 := by
    rw [hQ_const s, hQ0]
  have hE : Complex.exp ((A s : ℂ) * Complex.I) * Complex.exp (-(A s : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add]
    have hz : (A s : ℂ) * Complex.I + -(A s : ℂ) * Complex.I = 0 := by ring
    rw [hz, Complex.exp_zero]
  have hratio : g s / ‖g s‖ = Complex.exp ((A s : ℂ) * Complex.I) := by
    have h2 := congrArg (fun z => Complex.exp ((A s : ℂ) * Complex.I) * z) hQs1
    rw [mul_one] at h2
    rw [← mul_assoc, hE, one_mul] at h2
    exact h2
  have hnormC : ((‖g s‖ : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact norm_ne_zero_iff.mpr (hne s)
  have h4 : g s = Complex.exp ((A s : ℂ) * Complex.I) * (‖g s‖ : ℂ) := by
    have h := congrArg (fun z => z * (‖g s‖ : ℂ)) hratio
    rw [div_mul_cancel₀ _ hnormC] at h
    exact h
  refine h4.trans ?_
  have hAs : (A s : ℂ) = ↑θ + ↑(∫ τ in (0 : ℝ)..s, (deriv g τ / g τ).im) := by
    rw [hA_def, hq_def]
    push_cast
    rfl
  rw [hAs, mul_comm]

end

end Work.RPB.B1
