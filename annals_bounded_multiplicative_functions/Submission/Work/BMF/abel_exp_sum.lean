import Mathlib
import Submission.Work.BMF.kdr_defs
import Submission.Work.BMF.abel_identity
import Submission.Work.BMF.norm_eC_comp_sub_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF
open Finset
open scoped BigOperators

/-- The additive character `eC` has unit modulus. -/
lemma norm_eC_one' (t : ℝ) : ‖eC t‖ = 1 := by
  rw [eC, Complex.norm_exp]
  simp

/-- **Discrete Abel summation against an exponential weight.**
For a sequence `a : ℕ → ℂ` and `β : ℝ → ℝ` differentiable on `[1,L]` with `‖β'‖ ≤ Cβ` there,
the sum `Σ_{h ≤ L} a h · e(β h)` is at most `‖Σ_{h ≤ L} a h‖ + 2π Cβ Σ_{h < L} ‖Σ_{h' ≤ h} a h'‖`.

Suggested route: the Abel identity
`Σ_{h=1}^L a h E(β h) = A(L)E(β L) - Σ_{h=1}^{L-1} A(h)(E(β(h+1)) - E(β h))` with
`A(h) = Σ_{h'=1}^h a h'` and `E = eC`; then bound `‖E(β(h+1)) - E(β h)‖` using that
`E` has derivative `2πi E` of norm `2π`, together with the mean value inequality
`norm_image_sub_le_of_norm_deriv_le_segment'` giving `‖β(h+1)-β(h)‖ ≤ Cβ`. -/
theorem abel_exp_sum (L : ℕ) (a : ℕ → ℂ) (β : ℝ → ℝ) (Cβ : ℝ)
    (hβ : ∀ y ∈ Set.Icc (1:ℝ) L, HasDerivAt β (deriv β y) y)
    (hCβ : ∀ y ∈ Set.Icc (1:ℝ) L, ‖deriv β y‖ ≤ Cβ) :
    ‖∑ h ∈ Finset.Icc 1 L, a h * eC (β h)‖ ≤
      ‖∑ h ∈ Finset.Icc 1 L, a h‖ +
        2 * Real.pi * Cβ * ∑ h ∈ Finset.range L, ‖∑ h' ∈ Finset.Icc 1 h, a h'‖ := by
  rw [abel_identity L a (fun h => eC (β h))]
  calc ‖(∑ h ∈ Finset.Icc 1 L, a h) * eC (β L) -
        ∑ h ∈ Finset.range L, (∑ h' ∈ Finset.Icc 1 h, a h') *
          (eC (β (↑(h + 1))) - eC (β h))‖
    ≤ ‖(∑ h ∈ Finset.Icc 1 L, a h) * eC (β L)‖ +
        ‖∑ h ∈ Finset.range L, (∑ h' ∈ Finset.Icc 1 h, a h') *
          (eC (β (↑(h + 1))) - eC (β h))‖ :=
        norm_sub_le _ _
  _ = ‖∑ h ∈ Finset.Icc 1 L, a h‖ +
        ‖∑ h ∈ Finset.range L, (∑ h' ∈ Finset.Icc 1 h, a h') *
          (eC (β (↑(h + 1))) - eC (β h))‖ := by
        rw [norm_mul, norm_eC_one', mul_one]
  _ ≤ ‖∑ h ∈ Finset.Icc 1 L, a h‖ +
        ∑ h ∈ Finset.range L, ‖(∑ h' ∈ Finset.Icc 1 h, a h') *
          (eC (β (↑(h + 1))) - eC (β h))‖ :=
        add_le_add_right (norm_sum_le _ _) _
  _ ≤ ‖∑ h ∈ Finset.Icc 1 L, a h‖ +
        ∑ h ∈ Finset.range L,
          ‖∑ h' ∈ Finset.Icc 1 h, a h'‖ * (2 * Real.pi * Cβ) := by
        apply add_le_add_right
        apply Finset.sum_le_sum
        intro h hh
        rw [norm_mul]
        by_cases h0 : h = 0
        · subst h0; simp
        · have h1 : 1 ≤ h := Nat.one_le_iff_ne_zero.mpr h0
          have hL : h + 1 ≤ L := by
            have := Finset.mem_range.mp hh
            omega
          exact mul_le_mul_of_nonneg_left
            (by simpa only [Nat.cast_add, Nat.cast_one] using
              norm_eC_comp_sub_le L β Cβ hβ hCβ h1 hL) (norm_nonneg _)
  _ = ‖∑ h ∈ Finset.Icc 1 L, a h‖ +
        2 * Real.pi * Cβ * ∑ h ∈ Finset.range L, ‖∑ h' ∈ Finset.Icc 1 h, a h'‖ := by
        rw [← Finset.sum_mul]
        ring

end Work.BMF
