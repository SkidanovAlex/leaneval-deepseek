import Mathlib
import Submission.Work.OddRadon.Abel

/-!
# `radonInverse` is invariant under `F ↦ F (b * ·)` combined with `u ↦ u / b`

Scaling the data function `F` of the odd-dimensional Radon inversion by `c ↦ b * c` (with
`b > 0`) and rescaling the evaluation point by `u ↦ u / b` leaves `radonInverse n` unchanged.

The two structural inputs are:
* `abelReduceIter` scales by `b ^ (2 * k)` under composition with `b * ·`
  (`radonInverseAux_abelReduceIter_comp_mul_left`), which cancels the `b ^ (2 * n - 2)`
  coming from the weight `c ^ (2 * n - 2)` in the definition of `radonInverse`;
* the classical Abel inversion `abelInvert` is invariant under `Φ ↦ Φ (b * ·)` composed with
  `u ↦ u / b` (`radonInverseAux_abelInvert_comp_mul_left`).
-/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace Pointwise Interval Topology

namespace Work.OddRadon

/-- Pull a constant factor out of `abelReduceIter`. -/
lemma radonInverseAux_abelReduceIter_const_mul (α C : ℝ) (k : ℕ) (F : ℝ → ℝ) :
    abelReduceIter α k (fun c => C * F c) = fun c => C * abelReduceIter α k F c := by
  induction k generalizing α F with
  | zero => rfl
  | succ k ih =>
    rw [abelReduceIter_succ, abelReduce_const_mul]
    exact ih (α - 1) (abelReduce α F)

/-- One exponent-reduction step scales by `b ^ 2` under `c ↦ b * c`. -/
lemma radonInverseAux_abelReduce_comp_mul_left (α : ℝ) {b : ℝ} (hb : b ≠ 0)
    (Φ : ℝ → ℝ) (y : ℝ) :
    abelReduce α (fun t => Φ (b * t)) y = b ^ 2 * abelReduce α Φ (b * y) := by
  rw [abelReduce, abelReduce, deriv_comp_mul_left]
  simp only [smul_eq_mul]
  field_simp

/-- `k` exponent-reduction steps scale by `b ^ (2 * k)` under `c ↦ b * c`. -/
lemma radonInverseAux_abelReduceIter_comp_mul_left (α : ℝ) {b : ℝ} (hb : b ≠ 0) (k : ℕ)
    (Φ : ℝ → ℝ) (y : ℝ) :
    abelReduceIter α k (fun t => Φ (b * t)) y = b ^ (2 * k) * abelReduceIter α k Φ (b * y) := by
  induction k generalizing α Φ with
  | zero => simp
  | succ k ih =>
    have hr : abelReduce α (fun t => Φ (b * t)) = fun c => b ^ 2 * (abelReduce α Φ) (b * c) := by
      funext c; exact radonInverseAux_abelReduce_comp_mul_left α hb Φ c
    rw [abelReduceIter_succ]
    rw [abelReduceIter_succ]
    rw [hr, radonInverseAux_abelReduceIter_const_mul (α - 1) (b ^ 2) k
        (fun c => (abelReduce α Φ) (b * c))]
    simp only []
    rw [ih (α - 1) (abelReduce α Φ)]
    rw [show 2 * (k + 1) = 2 * k + 2 by ring]
    ring

/-- Substitution lemma: the Abel integral scales by the inverse scale factor. -/
lemma radonInverseAux_int_scale (g : ℝ → ℝ) (b : ℝ) (hb : 0 < b) (w : ℝ) :
    (∫ c in (0 : ℝ)..w, g c) = b⁻¹ * ∫ y in (0 : ℝ)..(b * w), g (y / b) := by
  have hbne : b ≠ 0 := ne_of_gt hb
  rw [intervalIntegral.integral_comp_div _ hbne]
  rw [zero_div, mul_div_cancel_left₀ w hbne, smul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hbne, one_mul]

/-- Pointwise form of the substitution for the Abel kernel
`c ↦ c * Φ c / √(c₀ ^ 2 - c ^ 2)`. -/
lemma radonInverseAux_kernel_scale (Φ : ℝ → ℝ) (b : ℝ) (hb : 0 < b) (w y : ℝ) :
    y * Φ y / Real.sqrt ((b * w) ^ 2 - y ^ 2)
      = (fun c : ℝ => c * Φ (b * c) / Real.sqrt (w ^ 2 - c ^ 2)) (y / b) := by
  have hbne : b ≠ 0 := ne_of_gt hb
  simp only []
  have hsq : w ^ 2 - (y / b) ^ 2 = ((b * w) ^ 2 - y ^ 2) / b ^ 2 := by field_simp
  rw [hsq, Real.sqrt_div' _ (sq_nonneg b), Real.sqrt_sq hb.le]
  rw [← mul_div_assoc, mul_div_cancel_left₀ y hbne]
  rw [div_div_eq_mul_div]
  rw [show (y / b * Φ y) * b = y * Φ y by field_simp]

/-- The Abel integral of the kernel of `Φ (b * ·)` at `w` is `b⁻¹` times the Abel integral
of the kernel of `Φ` at `b * w`. -/
lemma radonInverseAux_key (Φ : ℝ → ℝ) (b : ℝ) (hb : 0 < b) (w : ℝ) :
    (∫ c in (0 : ℝ)..w, c * Φ (b * c) / Real.sqrt (w ^ 2 - c ^ 2))
      = b⁻¹ * ∫ c in (0 : ℝ)..(b * w), c * Φ c / Real.sqrt ((b * w) ^ 2 - c ^ 2) := by
  have hB : ∀ y : ℝ, (fun c : ℝ => c * Φ (b * c) / Real.sqrt (w ^ 2 - c ^ 2)) (y / b)
      = y * Φ y / Real.sqrt ((b * w) ^ 2 - y ^ 2) := fun y =>
    (radonInverseAux_kernel_scale Φ b hb w y).symm
  have hint : (∫ c in (0 : ℝ)..(b * w), (fun c : ℝ => c * Φ (b * c) / Real.sqrt (w ^ 2 - c ^ 2)) (c / b))
      = ∫ c in (0 : ℝ)..(b * w), c * Φ c / Real.sqrt ((b * w) ^ 2 - c ^ 2) := by
    apply intervalIntegral.integral_congr
    intro x _
    exact hB x
  rw [radonInverseAux_int_scale (fun c : ℝ => c * Φ (b * c) / Real.sqrt (w ^ 2 - c ^ 2)) b hb w,
    hint]

/-- **The classical Abel inversion is invariant under `Φ ↦ Φ (b * ·)` combined with
`u ↦ u / b`** for `b > 0`. -/
lemma radonInverseAux_abelInvert_comp_mul_left {Φ : ℝ → ℝ} {b u : ℝ} (hb : 0 < b) :
    abelInvert (fun y : ℝ => Φ (b * y)) (u / b) = abelInvert Φ u := by
  have hbne : b ≠ 0 := ne_of_gt hb
  have hfun : (fun w : ℝ => ∫ c in (0 : ℝ)..w, c * Φ (b * c) / Real.sqrt (w ^ 2 - c ^ 2))
      = fun w => b⁻¹ * (∫ c in (0 : ℝ)..(b * w), c * Φ c / Real.sqrt ((b * w) ^ 2 - c ^ 2)) :=
    funext (radonInverseAux_key Φ b hb)
  rw [abelInvert, abelInvert]
  congr 1
  rw [hfun]
  rw [deriv_const_mul_field]
  change b⁻¹ * deriv ((fun v : ℝ => ∫ c in (0 : ℝ)..v, c * Φ c / Real.sqrt (v ^ 2 - c ^ 2)) <| b * ·)
        (u / b)
      = deriv (fun v : ℝ => ∫ c in (0 : ℝ)..v, c * Φ c / Real.sqrt (v ^ 2 - c ^ 2)) u
  set J : ℝ → ℝ := fun v : ℝ => ∫ c in (0 : ℝ)..v, c * Φ c / Real.sqrt (v ^ 2 - c ^ 2) with hJ
  rw [deriv_comp_mul_left]
  simp only [smul_eq_mul]
  rw [← mul_div_assoc, mul_div_cancel_left₀ u hbne]
  rw [← mul_assoc, inv_mul_cancel₀ hbne, one_mul]

theorem radonInverse_comp_mul_left (n : ℕ) {F : ℝ → ℝ} {b u : ℝ} (hb : 0 < b) (hu : 0 < u) :
    radonInverse n (fun c : ℝ => F (b * c)) (u / b) = radonInverse n F u := by
  have hbne : b ≠ 0 := ne_of_gt hb
  have hbe : b ^ (2 * n - 2) ≠ 0 := pow_ne_zero _ hbne
  rw [radonInverse, radonInverse]
  set Ψ : ℝ → ℝ := fun c : ℝ => (2 * sphereArea (2 * n - 2))⁻¹ * c ^ (2 * n - 2) * F c with hΨ
  have hkey : abelReduceIter ((n : ℝ) - 3 / 2) (n - 1)
        (fun c : ℝ => (2 * sphereArea (2 * n - 2))⁻¹ * c ^ (2 * n - 2) * F (b * c))
      = fun c : ℝ => abelReduceIter ((n : ℝ) - 3 / 2) (n - 1) Ψ (b * c) := by
    have h1 : (fun c : ℝ => (2 * sphereArea (2 * n - 2))⁻¹ * c ^ (2 * n - 2) * F (b * c))
        = fun c : ℝ => (b ^ (2 * n - 2))⁻¹ * (fun t : ℝ => Ψ (b * t)) c := by
      funext c
      rw [hΨ]
      simp only [mul_pow]
      field_simp
    funext y
    rw [h1, radonInverseAux_abelReduceIter_const_mul ((n : ℝ) - 3 / 2) ((b ^ (2 * n - 2))⁻¹)
        (n - 1) (fun t : ℝ => Ψ (b * t))]
    simp only []
    rw [radonInverseAux_abelReduceIter_comp_mul_left ((n : ℝ) - 3 / 2) hbne (n - 1) Ψ y]
    have hE : (b ^ (2 * n - 2))⁻¹ * b ^ (2 * (n - 1)) = 1 := by
      have hpow : 2 * (n - 1) = 2 * n - 2 := by omega
      rw [hpow, inv_mul_cancel₀ hbe]
    rw [← mul_assoc, hE, one_mul]
  rw [hkey]
  exact radonInverseAux_abelInvert_comp_mul_left (Φ := abelReduceIter ((n : ℝ) - 3 / 2) (n - 1) Ψ) hb

end Work.OddRadon
