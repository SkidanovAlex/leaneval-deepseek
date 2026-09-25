import Mathlib
import Submission.Work.BourgainPlan.Maximal.annulusSymbolDefs

/-!
# `AnnulusSymbolSmooth` is stable under dyadic dilation of a fixed symbol

Given a `ℂ`-valued function `ψ` on `ℝ` which vanishes off the annulus `2⁻¹ < |ξ| < 2` and whose
`k`-th derivative is bounded on all of `ℝ` by a constant `C_k`, the family

  `b m ξ = ψ (2^m ξ)`

is an `AnnulusSymbolSmooth` annulus symbol: each `b m` is supported in the annulus at scale `2^m`
(the first half of `AnnulusSymbolSmooth`), and its `k`-th derivative obeys the scale bound
`‖(d/dξ)^k b m ξ‖ ≤ C_k · 2^{m k}` (the second half).

The point of the proof is the exact chain rule for the dilation,
`iteratedDeriv k (fun x => f (c * x)) x = c^k * iteratedDeriv k f (c * x)`, which in Mathlib is
available *without* any smoothness or differentiability hypothesis on `f` (the library uses `0` as
the fallback value of the derivative at non-differentiable points, so the identity is true for
every `f` and every `c`), so the only hypotheses needed are the two above.
-/

open scoped BigOperators

namespace Work.BourgainPlan.Maximal

/-- The exact chain rule for iterated derivatives of a dilation, with **no** differentiability
hypothesis: `(d/dx)^k f(c x) = c^k (d/dx)^k f (c x)`.  (Mathlib's `deriv_comp_mul_left` needs no
hypothesis because `deriv` is `0` where the function is not differentiable.) -/
private lemma iteratedDeriv_comp_const_mul_complex (f : ℝ → ℂ) (c : ℝ) (k : ℕ) :
    iteratedDeriv k (fun x => f (c * x)) = fun x => (c : ℂ) ^ k * iteratedDeriv k f (c * x) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih, deriv_const_mul_field']
    funext x
    rw [deriv_comp_mul_left, iteratedDeriv_succ, Complex.real_smul]
    ring

/-- Norm form of the dilation chain rule for `c ≥ 0`. -/
private lemma norm_iteratedDeriv_comp_const_mul (f : ℝ → ℂ) (c : ℝ) (hc : 0 ≤ c) (k : ℕ)
    (x : ℝ) : ‖iteratedDeriv k (fun y => f (c * y)) x‖ = c ^ k * ‖iteratedDeriv k f (c * x)‖ := by
  rw [iteratedDeriv_comp_const_mul_complex, norm_mul, norm_pow, Complex.norm_of_nonneg hc]

/-- The two exponents `2^{mk}` and `(2^m)^k` agree, for `m : ℤ` and `k : ℕ`. -/
private lemma zpow_mul_natCast (m : ℤ) (k : ℕ) :
    ((2 : ℝ) ^ m) ^ k = (2 : ℝ) ^ (m * k) := by
  rw [← zpow_natCast, ← zpow_mul]

theorem annulusSymbolSmooth_of_dilate (ψ : ℝ → ℂ) (hsupp : ∀ ξ : ℝ, ψ ξ ≠ 0 → (2 : ℝ)⁻¹ < |ξ| ∧ |ξ| < 2) (hbdd : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ, ‖iteratedDeriv k ψ ξ‖ ≤ C) : Work.BourgainPlan.Maximal.AnnulusSymbolSmooth (fun m ξ => ψ ((2 : ℝ) ^ m * ξ)) := by
  refine ⟨?_, ?_⟩
  · -- the annulus support is inherited directly from `ψ`
    intro m ξ h
    exact hsupp _ h
  · -- the scale bound comes from the exact dilation chain rule
    intro k
    obtain ⟨C, hC, hbound⟩ := hbdd k
    refine ⟨C, hC, ?_⟩
    intro m ξ
    have hm : (0 : ℝ) ≤ (2 : ℝ) ^ m := zpow_nonneg (by norm_num) m
    rw [norm_iteratedDeriv_comp_const_mul ψ ((2 : ℝ) ^ m) hm k ξ]
    calc ((2 : ℝ) ^ m) ^ k * ‖iteratedDeriv k ψ ((2 : ℝ) ^ m * ξ)‖
        ≤ ((2 : ℝ) ^ m) ^ k * C :=
          mul_le_mul_of_nonneg_left (hbound _) (pow_nonneg hm k)
      _ = C * (2 : ℝ) ^ (m * k) := by rw [zpow_mul_natCast]; ring

end Work.BourgainPlan.Maximal
