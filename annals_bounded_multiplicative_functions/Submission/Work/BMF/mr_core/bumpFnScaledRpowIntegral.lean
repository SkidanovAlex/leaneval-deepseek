import Mathlib
import Submission.Work.BMF.mr_core.bumpFnScaledAux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The rescaled Mellin integral of the bump function

For `A > 0` and any `δ : ℝ`, the substitution `t = A y` turns the integral of
`t ↦ φ(t/A) · t^{iδ}` over `[0, ⌈4A⌉₊]` into a multiple of the Mellin-type integral
`∫_{1/4}^{4} y^{iδ} φ(y) dy`:

`∫_0^{⌈4A⌉₊} φ(t/A) t^{iδ} dt = A^{1+iδ} ∫_{1/4}^{4} y^{iδ} φ(y) dy`.

The only point to be careful about is the range of integration: `φ` vanishes outside `[1/4, 4]`,
so both integrals may be replaced by the integral of the same integrand over *all of* `ℝ`; this
is what `intervalIntegral.integral_eq_integral_of_support_subset` exploits.
-/

namespace Work.BMF.mr_core

open MeasureTheory intervalIntegral

noncomputable section

theorem bumpFnScaledRpowIntegral (A δ : ℝ) (hA0 : 0 < A) :
    ∫ t in (0 : ℝ)..(((⌈4 * A⌉₊ : ℕ) : ℝ)),
        ((Work.BMF.bumpFn (t / A)) : ℂ) * ((t : ℂ) ^ (Complex.I * (δ : ℂ)))
      = (A : ℂ) ^ (1 + Complex.I * (δ : ℂ)) *
          (∫ y in (1 / 4 : ℝ)..4, (y : ℂ) ^ (Complex.I * (δ : ℂ)) * ((Work.BMF.bumpFn y) : ℂ)) := by
  set s : ℂ := Complex.I * (δ : ℂ) with hs
  set g : ℝ → ℂ := fun t => ((Work.BMF.bumpFn (t / A) : ℝ) : ℂ) * (t : ℂ) ^ s with hg
  set G : ℝ → ℂ := fun y => (y : ℂ) ^ s * ((Work.BMF.bumpFn y : ℝ) : ℂ) with hG
  have hceil : 4 * A ≤ (((⌈4 * A⌉₊ : ℕ) : ℝ)) := Work.BMF.mr_core.four_mul_le_ceil A
  -- `φ` is supported in `(1/4, 4)`, hence in `(A/4, 4A)` and in `(0, ⌈4A⌉₊)`.
  have hφ_ne : ∀ y : ℝ, Work.BMF.bumpFn y ≠ 0 → (1 / 4 : ℝ) < y ∧ y < 4 := by
    intro y hy
    constructor
    · by_contra h
      exact hy (Work.BMF.bumpFn_eq_zero y (Or.inl (le_of_not_gt h)))
    · by_contra h
      exact hy (Work.BMF.bumpFn_eq_zero y (Or.inr (le_of_not_gt h)))
  have hsup1 : Function.support g ⊆ Set.Ioc (A / 4) (4 * A) := by
    intro t ht
    have hφ : Work.BMF.bumpFn (t / A) ≠ 0 := by
      intro h0
      exact ht (by rw [hg]; simp [h0])
    obtain ⟨h1, h2⟩ := hφ_ne (t / A) hφ
    exact ⟨by have := (lt_div_iff₀ hA0).mp h1; linarith,
           by have := (div_lt_iff₀ hA0).mp h2; linarith⟩
  have hsup0 : Function.support g ⊆ Set.Ioc (0 : ℝ) (((⌈4 * A⌉₊ : ℕ) : ℝ)) := by
    intro t ht
    obtain ⟨h1, h2⟩ := hsup1 ht
    exact ⟨by linarith [show (0 : ℝ) < A / 4 by linarith], by linarith [hceil]⟩
  -- Both intervals have the same integral as `∫ g` over all of `ℝ`.
  have h1 : ∫ t in (0 : ℝ)..(((⌈4 * A⌉₊ : ℕ) : ℝ)), g t
      = ∫ t in A / 4..4 * A, g t := by
    rw [intervalIntegral.integral_eq_integral_of_support_subset (f := g) (a := 0)
          (b := ((⌈4 * A⌉₊ : ℕ) : ℝ)) hsup0,
        ← intervalIntegral.integral_eq_integral_of_support_subset (f := g) (a := A / 4)
          (b := 4 * A) hsup1]
  -- Change of variables `t = A y` on `[1/4, 4]`.
  have hsub := intervalIntegral.smul_integral_comp_mul_left (a := (1 / 4 : ℝ)) (b := 4) g A
  rw [show A * (1 / 4) = A / 4 by ring, show A * 4 = 4 * A by ring] at hsub
  -- On `[1/4, 4]` one has `φ(y) (Ay)^{iδ} = A^{iδ} (y^{iδ} φ(y))`.
  have hpt : Set.EqOn (fun y => g (A * y)) (fun y => (A : ℂ) ^ s * G y)
      (Set.uIcc (1 / 4 : ℝ) 4) := by
    intro y hy
    have hy' : y ∈ Set.Icc (1 / 4 : ℝ) 4 := by
      rwa [Set.uIcc_of_le (by norm_num : (1 / 4 : ℝ) ≤ 4)] at hy
    obtain ⟨hy1, hy4⟩ := hy'
    have hypos : (0 : ℝ) < y := by linarith
    rw [hg, hG]
    dsimp only
    have hAy : (A * y) / A = y := by
      rw [mul_comm A y, mul_div_cancel_right₀ y hA0.ne']
    rw [hAy, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hA0.le hypos.le s]
    ring
  have hInt : ∫ y in (1 / 4 : ℝ)..4, g (A * y)
      = (A : ℂ) ^ s * ∫ y in (1 / 4 : ℝ)..4, G y := by
    rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_const_mul]
  rw [h1, ← hsub, hInt, Complex.real_smul,
      Complex.cpow_add (1 : ℂ) s (Complex.ofReal_ne_zero.mpr hA0.ne'), Complex.cpow_one]
  ring

end

end Work.BMF.mr_core
