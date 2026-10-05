import Mathlib
import Submission.Work.RPB.B3.EvenTaylorDefs
import Submission.Work.RPB.B3.stepOpApply

/-!
# Steps of the even Taylor splitting

Helper lemmas about the Hadamard quotient `stepOp` and the even quotient `evenStep` of
`Work.RPB.B3.EvenTaylor`, used to prove `Work.RPB.B3.evenTaylorSplit`.
-/

open scoped ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Work.RPB.B3.EvenTaylor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Any finite order is below the smooth (`∞`) order. -/
theorem le_sm (n : ℕ) : (n : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top

/-- An even function has vanishing derivative at the origin. -/
theorem deriv_zero_of_even (g : ℝ → E) (hg : ∀ r, g (-r) = g r) : deriv g 0 = 0 := by
  have h2 : fderiv ℝ (fun r : ℝ => g (-r)) 0 = fderiv ℝ g 0 := by
    rw [show (fun r : ℝ => g (-r)) = g from funext hg]
  have h1 : fderiv ℝ (fun r : ℝ => g (-r)) 0 = - fderiv ℝ g 0 := by
    rw [← fderivWithin_univ (f := fun r : ℝ => g (-r)), fderivWithin_comp_neg]
    simp
  rw [h1] at h2
  have h3 : fderiv ℝ g 0 = 0 := by
    apply ContinuousLinearMap.ext_ring
    have hh := congrArg (fun M : ℝ →L[ℝ] E => M 1) h2
    simp only [neg_apply, zero_apply] at hh ⊢
    have hv : (2 : ℝ) • ((fderiv ℝ g 0) 1) = 0 := by
      have hvv : (fderiv ℝ g 0) 1 + (fderiv ℝ g 0) 1 = 0 := by
        have hc := neg_add_cancel ((fderiv ℝ g 0) 1)
        rwa [hh] at hc
      rwa [two_smul ℝ ((fderiv ℝ g 0) 1)]
    have hnorm : (2 : ℝ) * ‖(fderiv ℝ g 0) 1‖ = 0 := by
      have hc := congrArg norm hv
      simpa [norm_smul] using hc
    have : ‖(fderiv ℝ g 0) 1‖ = 0 := by linarith [norm_nonneg ((fderiv ℝ g 0) 1)]
    exact norm_eq_zero.mp this
  rw [show deriv g 0 = (fderiv ℝ g 0) 1 from rfl, h3]
  simp

/-- Smoothness of `Hsub`. -/
theorem Hsub_contDiff (h : (ℝ × ℝ) × ℝ → E) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (Hsub h) := by
  unfold Hsub
  fun_prop

/-- `0` is a fixed point of the value of `Hsub`. -/
theorem Hsub_zero (h : (ℝ × ℝ) × ℝ → E) (p : ℝ × ℝ) : Hsub h (p, 0) = 0 := by
  simp [Hsub]

/-- `Hsub` preserves evenness in the last variable. -/
theorem Hsub_even (h : (ℝ × ℝ) × ℝ → E) (he : ∀ p r, h (p, -r) = h (p, r)) :
    ∀ p r, Hsub h (p, -r) = Hsub h (p, r) := by
  intro p r
  simp only [Hsub]
  rw [he p r]

/-- The `fderiv` of a function `2π`-periodic in the middle variable is `2π`-periodic. -/
theorem fderiv_per (h : (ℝ × ℝ) × ℝ → E) (hp : Per h) :
    ∀ τ t r, fderiv ℝ h ((τ, t + 2 * Real.pi), r) = fderiv ℝ h ((τ, t), r) := by
  intro τ t r
  set a : (ℝ × ℝ) × ℝ := ((0, 2 * Real.pi), 0) with ha
  have hshift : (fun z : (ℝ × ℝ) × ℝ => h (z + a)) = h := by
    funext z
    obtain ⟨⟨τ', t'⟩, r'⟩ := z
    show h (((τ', t') + (0, 2 * Real.pi)), r' + 0) = h ((τ', t'), r')
    rw [add_zero]
    simp only [Prod.mk_add_mk, add_zero]
    exact hp τ' t' r'
  have key := fderiv_comp_add_right (𝕜 := ℝ) (f := h) (a := a) (x := ((τ, t), r))
  rw [hshift] at key
  have hw : ((τ, t), r) + a = ((τ, t + 2 * Real.pi), r) := by
    rw [ha]
    simp [Prod.mk_add_mk]
  rw [← hw]
  exact key.symm

/-- `pdR` preserves `2π`-periodicity in the middle variable. -/
theorem per_pdR (h : (ℝ × ℝ) × ℝ → E) (hp : Per h) : Per (pdR h) := by
  intro τ t r
  simp only [pdR]
  rw [fderiv_per h hp τ t r]

/-- `Hsub` preserves `2π`-periodicity in the middle variable. -/
theorem per_Hsub (h : (ℝ × ℝ) × ℝ → E) (hp : Per h) : Per (Hsub h) := by
  intro τ t r
  simp only [Hsub]
  rw [hp τ t r, hp τ t 0]

/-- `stepOp` preserves `2π`-periodicity in the middle variable. -/
theorem per_stepOp (h : (ℝ × ℝ) × ℝ → E) (hp : Per (pdR h)) : Per (stepOp h) := by
  intro τ t r
  simp only [stepOp]
  refine intervalIntegral.integral_congr (fun u _ => hp τ t (r * u))

/-! ### Smoothness of the Hadamard quotient -/

/-- The Hadamard quotient identity. -/
theorem stepOp_sub (h : (ℝ × ℝ) × ℝ → E) (hh : ContDiff ℝ 1 h) (z : (ℝ × ℝ) × ℝ) :
    h (z.1, z.2) - h (z.1, 0) = z.2 • stepOp h z :=
  Work.RPB.B3.stepOpApply h hh z

/-- The Hadamard quotient identity for functions vanishing on `r = 0`. -/
theorem stepOp_apply_zero (h : (ℝ × ℝ) × ℝ → E) (hh : ContDiff ℝ 1 h)
    (h0 : ∀ p, h (p, 0) = 0) (z : (ℝ × ℝ) × ℝ) :
    h z = z.2 • stepOp h z := by
  have h' := stepOp_sub h hh z
  rw [h0 z.1, sub_zero] at h'
  simpa using h'

/-- `stepOp` of an even function vanishes at `r = 0`. -/
theorem stepOp_zero_of_even (h : (ℝ × ℝ) × ℝ → E) (hh : ContDiff ℝ 1 h)
    (he : ∀ p r, h (p, -r) = h (p, r)) (p : ℝ × ℝ) :
    stepOp h (p, 0) = 0 := by
  rw [stepOp_zero]
  rw [pdR_eq_deriv h p 0 hh.differentiable_one.differentiableAt]
  exact deriv_zero_of_even (fun s : ℝ => h (p, s)) (fun s => he p s)

/-! ### The even-quotient identity -/

/-! ### The iterated even quotient -/

theorem chi_succ (f : (ℝ × ℝ) × ℝ → E) (n : ℕ) : chi f (n + 1) = evenStep (chi f n) := by
  rw [chi, chi, Function.iterate_succ_apply']

/-! ### Periodicity of the iterated even quotient -/

theorem per_evenStep (h : (ℝ × ℝ) × ℝ → E) (hp : Per h) : Per (evenStep h) := by
  have hH : Per (Hsub h) := per_Hsub h hp
  have h2 : Per (stepOp (stepOp (Hsub h))) :=
    per_stepOp (stepOp (Hsub h)) (per_pdR (stepOp (Hsub h)) (per_stepOp (Hsub h) (per_pdR (Hsub h) hH)))
  simpa [evenStep] using h2

theorem per_chi (f : (ℝ × ℝ) × ℝ → E) (hf : Per f) (n : ℕ) : Per (chi f n) := by
  induction n with
  | zero => simpa [chi] using hf
  | succ n ih => rw [chi_succ]; exact per_evenStep (chi f n) ih

end Work.RPB.B3.EvenTaylor
