import Mathlib
import Submission.Work.BMF.mr_core.bumpFnScaledAux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Integration by parts for the rescaled bump function

The main term of the smoothed `Λ`-sum is obtained by integrating

`t ↦ φ(t/A) · t^{iδ} = φ(t/A) · (t^{1+iδ}/(1+iδ))'`

by parts, the antiderivative of `t^{iδ}` being `t^{1+iδ}/(1+iδ)`.  Since `φ(t/A)` and `φ'(t/A)`
vanish at both ends of `[0, ⌈4A⌉]` (the bump is supported on `[1/4, 4]`), the boundary terms drop
out and one gets

`∫_0^{⌈4A⌉} (φ'(t/A)/A) · t^{1+iδ}/(1+iδ) dt = -∫_0^{⌈4A⌉} φ(t/A) · t^{iδ} dt`.

The statement is proved for an arbitrary upper limit `b ≥ 4A` (`bumpFnDerivMainTerm_aux`); the
target theorem is the special case `b = ⌈4A⌉₊`.

Because the integrands vanish on a neighbourhood of `0`, where `t^{1+iδ}` is not differentiable,
both integrals are first pushed to `[A/8, b]` (`intervalIntegral_eq_of_eqOn_left`), and integration
by parts is performed there.
-/

namespace Work.BMF.mr_core

open MeasureTheory

noncomputable section

/-- If a continuous-on-`[0,a]`-vanishing function `f` vanishes on `[0, a]` (with `0 ≤ a ≤ b`), then
the integral of `f` over `[0, b]` equals its integral over `[a, b]`. -/
lemma intervalIntegral_eq_of_eqOn_left {f : ℝ → ℂ} {a b : ℝ} (h0a : 0 ≤ a) (hab : a ≤ b)
    (hf : ∀ x ∈ Set.Icc (0 : ℝ) a, f x = 0) :
    ∫ x in (0 : ℝ)..b, f x = ∫ x in a..b, f x := by
  have h0b : (0 : ℝ) ≤ b := le_trans h0a hab
  rw [intervalIntegral.integral_of_le h0b, intervalIntegral.integral_of_le hab]
  apply MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc
  · intro x hx
    rw [Set.mem_Ioc] at hx ⊢
    exact ⟨lt_of_le_of_lt h0a hx.1, hx.2⟩
  · intro x hx
    rw [Set.mem_sdiff, Set.mem_Ioc] at hx
    obtain ⟨⟨hx0, hxb⟩, hxnot⟩ := hx
    have hxle : x ≤ a := by
      by_contra h
      rw [not_le] at h
      exact hxnot ⟨h, hxb⟩
    exact hf x ⟨le_of_lt hx0, hxle⟩

/-- Integration by parts for the rescaled bump: for any `b ≥ 4A`,
`∫_0^b (φ'(t/A)/A) t^{1+iδ}/(1+iδ) dt = -∫_0^b φ(t/A) t^{iδ} dt`. -/
lemma bumpFnDerivMainTerm_aux (A δ b : ℝ) (hA0 : 0 < A) (hb : 4 * A ≤ b) :
    ∫ t in (0 : ℝ)..b,
        (((deriv Work.BMF.bumpFn (t / A)) : ℝ) : ℂ) / (A : ℂ) *
          ((t : ℂ) ^ (1 + Complex.I * (δ : ℂ)) / (1 + Complex.I * (δ : ℂ)))
      = - ∫ t in (0 : ℝ)..b,
          ((Work.BMF.bumpFn (t / A)) : ℂ) * ((t : ℂ) ^ (Complex.I * (δ : ℂ))) := by
  have hA8pos : 0 < A / 8 := by linarith
  have hA8le : A / 8 ≤ b := by linarith
  have hquot : (A / 8) / A = 1 / 8 := by field_simp
  -- the `φ'` integrand vanishes on `[0, A/8]`: push the integral to `[A/8, b]`
  have hred1 : (∫ t in (0 : ℝ)..b,
        (((deriv Work.BMF.bumpFn (t / A)) : ℝ) : ℂ) / (A : ℂ) *
          ((t : ℂ) ^ (1 + Complex.I * (δ : ℂ)) / (1 + Complex.I * (δ : ℂ))))
      = ∫ t in A / 8..b,
        (((deriv Work.BMF.bumpFn (t / A)) : ℝ) : ℂ) / (A : ℂ) *
          ((t : ℂ) ^ (1 + Complex.I * (δ : ℂ)) / (1 + Complex.I * (δ : ℂ))) := by
    apply intervalIntegral_eq_of_eqOn_left (le_of_lt hA8pos) hA8le
    intro x hx
    rw [Set.mem_Icc] at hx
    have hxA : x / A < 1 / 4 := by
      have h1 : x / A ≤ (A / 8) / A := div_le_div_of_nonneg_right hx.2 (le_of_lt hA0)
      rw [hquot] at h1
      linarith
    rw [Work.BMF.deriv_bumpFn_eq_zero_of_lt hxA]
    simp
  -- the `φ` integrand vanishes on `[0, A/8]` as well
  have hred2 : (∫ t in (0 : ℝ)..b,
        ((Work.BMF.bumpFn (t / A)) : ℂ) * ((t : ℂ) ^ (Complex.I * (δ : ℂ))))
      = ∫ t in A / 8..b,
        ((Work.BMF.bumpFn (t / A)) : ℂ) * ((t : ℂ) ^ (Complex.I * (δ : ℂ))) := by
    apply intervalIntegral_eq_of_eqOn_left (le_of_lt hA8pos) hA8le
    intro x hx
    rw [Set.mem_Icc] at hx
    have hxA : x ≤ A / 4 := by
      have h1 : x ≤ A / 8 := hx.2
      linarith
    rw [bumpFn_div_eq_zero_of_le hA0 hxA]
    simp
  -- integration by parts data
  have hu : ∀ x ∈ Set.uIcc (A / 8) b,
      HasDerivAt (fun t : ℝ => (t : ℂ) ^ (1 + Complex.I * (δ : ℂ)) / (1 + Complex.I * (δ : ℂ)))
        ((x : ℂ) ^ (Complex.I * (δ : ℂ))) x := by
    intro x hx
    rw [Set.uIcc_of_le hA8le, Set.mem_Icc] at hx
    have hxpos : 0 < x := lt_of_lt_of_le hA8pos hx.1
    have h := Work.BMF.hasDerivAt_cpow_F δ hxpos
    rw [show Complex.I * (δ : ℂ) + 1 = 1 + Complex.I * (δ : ℂ) from by ring] at h
    exact h
  have hv : ∀ x ∈ Set.uIcc (A / 8) b,
      HasDerivAt (fun t : ℝ => ((Work.BMF.bumpFn (t / A) : ℝ) : ℂ))
        ((((deriv Work.BMF.bumpFn (x / A)) : ℝ) : ℂ) / (A : ℂ)) x :=
    fun x _ => hasDerivAt_bumpFn_div A x
  have hu' : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (Complex.I * (δ : ℂ)))
      volume (A / 8) b := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le hA8le, Set.mem_Icc] at hx
    exact (Work.BMF.continuousAt_ofReal_cpow δ (lt_of_lt_of_le hA8pos hx.1)).continuousWithinAt
  have hv' : IntervalIntegrable
      (fun x : ℝ => (((deriv Work.BMF.bumpFn (x / A)) : ℝ) : ℂ) / (A : ℂ)) volume (A / 8) b :=
    (continuous_deriv_bumpFn_div A).intervalIntegrable _ _
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  -- both boundary terms vanish
  have hvb : ((Work.BMF.bumpFn (b / A) : ℝ) : ℂ) = 0 := by
    have hbA : (4 : ℝ) ≤ b / A := (le_div_iff₀ hA0).mpr (by linarith)
    rw [Work.BMF.bumpFn_eq_zero (b / A) (Or.inr hbA), Complex.ofReal_zero]
  have hva : ((Work.BMF.bumpFn ((A / 8) / A) : ℝ) : ℂ) = 0 := by
    rw [hquot, Work.BMF.bumpFn_eighth, Complex.ofReal_zero]
  have key : (∫ t in A / 8..b,
        (((deriv Work.BMF.bumpFn (t / A)) : ℝ) : ℂ) / (A : ℂ) *
          ((t : ℂ) ^ (1 + Complex.I * (δ : ℂ)) / (1 + Complex.I * (δ : ℂ))))
      = - ∫ t in A / 8..b,
          ((Work.BMF.bumpFn (t / A)) : ℂ) * ((t : ℂ) ^ (Complex.I * (δ : ℂ))) := by
    have e1 : (∫ t in A / 8..b,
          (((deriv Work.BMF.bumpFn (t / A)) : ℝ) : ℂ) / (A : ℂ) *
            ((t : ℂ) ^ (1 + Complex.I * (δ : ℂ)) / (1 + Complex.I * (δ : ℂ))))
        = ∫ t in A / 8..b,
            ((t : ℂ) ^ (1 + Complex.I * (δ : ℂ)) / (1 + Complex.I * (δ : ℂ))) *
              ((((deriv Work.BMF.bumpFn (t / A)) : ℝ) : ℂ) / (A : ℂ)) :=
      intervalIntegral.integral_congr (fun t _ => mul_comm _ _)
    have e2 : (∫ t in A / 8..b,
          ((Work.BMF.bumpFn (t / A)) : ℂ) * ((t : ℂ) ^ (Complex.I * (δ : ℂ))))
        = ∫ t in A / 8..b,
            ((t : ℂ) ^ (Complex.I * (δ : ℂ))) * ((Work.BMF.bumpFn (t / A)) : ℂ) :=
      intervalIntegral.integral_congr (fun t _ => mul_comm _ _)
    rw [e1, e2]
    rw [hIBP, hvb, hva]
    ring
  rw [hred1, hred2]
  exact key

theorem bumpFnDerivMainTerm (A δ : ℝ) (hA0 : 0 < A) :
    ∫ t in (0 : ℝ)..(((⌈4 * A⌉₊ : ℕ) : ℝ)),
        (((deriv Work.BMF.bumpFn (t / A)) : ℝ) : ℂ) / (A : ℂ) *
          ((t : ℂ) ^ (1 + Complex.I * (δ : ℂ)) / (1 + Complex.I * (δ : ℂ)))
      = - ∫ t in (0 : ℝ)..(((⌈4 * A⌉₊ : ℕ) : ℝ)),
          ((Work.BMF.bumpFn (t / A)) : ℂ) * ((t : ℂ) ^ (Complex.I * (δ : ℂ))) := by
  exact bumpFnDerivMainTerm_aux A δ (((⌈4 * A⌉₊ : ℕ) : ℝ)) hA0 (four_mul_le_ceil A)

end

end Work.BMF.mr_core
