/-
# ZeroFreeTables — TrigPolyPos.lean

Two elementary facts about Chebyshev polynomials of the first kind that turn the
non-negativity of a Chebyshev polynomial on `[-1,1]` into the non-negativity of
`∑ₖ cₖ ℜ(wᵏ)` for `w` on the complex unit circle.

They are the "trigonometric" input to `ksum_trigPoly_nonneg`: for `n` coprime to
`q` the quantity `χ(n) n^{-iγ}` is a point of the unit circle, and
`ℜ(wᵏ) = Tₖ(ℜ w)`.
-/
import Mathlib

open Complex
open scoped BigOperators
noncomputable section

namespace Work.ZeroFreeTables

/-- **Chebyshev on the unit circle.**  For `w : ℂ` with `‖w‖ = 1` and `k : ℕ`,
`ℜ(w ^ k)` equals the Chebyshev polynomial `T k` evaluated at `ℜ w`. -/
theorem re_pow_eval_chebyshevT (w : ℂ) (hw : ‖w‖ = 1) (k : ℕ) :
    (w ^ k).re = (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval w.re := by
  have hexp : w = cexp ((w.arg : ℂ) * I) := by
    have h := Complex.norm_mul_exp_arg_mul_I w
    rw [hw] at h
    simpa using h.symm
  have hre : w.re = Real.cos w.arg := by
    have h := congrArg Complex.re hexp
    rwa [Complex.exp_ofReal_mul_I_re] at h
  have hpow : (w ^ k).re = Real.cos ((k : ℝ) * w.arg) := by
    conv_lhs => rw [hexp]
    rw [← Complex.exp_nat_mul]
    have : ((k : ℂ) * ((w.arg : ℂ) * I)) = (((k : ℝ) * w.arg : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [this, Complex.exp_ofReal_mul_I_re]
  rw [hpow, hre, Polynomial.Chebyshev.T_real_cos]
  congr 1

/-- **Positivity transfer.**  If the Chebyshev polynomial
`P(x) = ∑_{k ≤ d} c k · T k(x)` is non-negative on `[-1,1]`, then
`∑_{k ≤ d} c k · ℜ(w ^ k) ≥ 0` for every `w` on the unit circle. -/
theorem trigPoly_eval_nonneg {c : ℕ → ℝ} {d : ℕ}
    (hP : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      0 ≤ ∑ k ∈ Finset.range (d + 1), c k * (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval x)
    {w : ℂ} (hw : ‖w‖ = 1) :
    0 ≤ ∑ k ∈ Finset.range (d + 1), c k * (w ^ k).re := by
  have hsum : ∑ k ∈ Finset.range (d + 1), c k * (w ^ k).re
      = ∑ k ∈ Finset.range (d + 1), c k * (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval w.re :=
    Finset.sum_congr rfl (fun k _ => by rw [re_pow_eval_chebyshevT w hw k])
  rw [hsum]
  refine hP w.re ⟨?_, ?_⟩
  · have h := Complex.abs_re_le_norm w
    rw [hw, abs_le] at h
    exact h.1
  · have h := Complex.abs_re_le_norm w
    rw [hw, abs_le] at h
    exact h.2

/-- **Splitting off the real part.**  Same identity as
`Commons.NumberTheory.Linnik.re_div_cpow_eq`, restated here so that files under
`Submission/Work` can use it without reaching into `Submission/Commons`:
for `n ≥ 1`,
`ℜ(χ(n) / n^(β+w)) = n^{-β} · ℜ(χ(n) · n^{-w})`. -/
theorem re_div_cpow_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {n : ℕ} (hn : 1 ≤ n)
    (β : ℝ) (w : ℂ) :
    (χ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + w)).re =
      (n : ℝ) ^ (-β) * (χ (n : ZMod q) * (n : ℂ) ^ (-w)).re := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnc : (n : ℂ) ≠ 0 := by simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hcn : (((n : ℝ) ^ (-β) : ℝ) : ℂ) = (n : ℂ) ^ (-(β : ℂ)) := by
    have h1 : (n : ℂ) = ((n : ℝ) : ℂ) := by push_cast; ring
    rw [h1, ← Complex.ofReal_neg, ← Complex.ofReal_cpow hnpos.le (-β)]
  have hkey : (n : ℂ) ^ (-((β : ℂ) + w)) =
      (((n : ℝ) ^ (-β) : ℝ) : ℂ) * (n : ℂ) ^ (-w) := by
    have h2 : -((β : ℂ) + w) = (-(β : ℂ)) + (-w) := by ring
    rw [h2, Complex.cpow_add _ _ hnc, hcn]
  have hmain : χ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + w)
      = (((n : ℝ) ^ (-β) : ℝ) : ℂ) * (χ (n : ZMod q) * (n : ℂ) ^ (-w)) := by
    rw [div_eq_mul_inv, ← Complex.cpow_neg, hkey]; ring
  rw [hmain, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

end Work.ZeroFreeTables
