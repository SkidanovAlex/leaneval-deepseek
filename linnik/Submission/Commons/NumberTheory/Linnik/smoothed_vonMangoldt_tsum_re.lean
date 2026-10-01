import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.DirichletCharacter.Basic

namespace Commons.NumberTheory.Linnik

/-- The real part of `(a : ℂ) * z * (b : ℂ)` for real `a`, `b` is `a * z.re * b`. -/
lemma re_ofReal_mul_ofReal (a b : ℝ) (z : ℂ) : ((a : ℂ) * z * (b : ℂ)).re = a * z.re * b := by
  rw [Complex.mul_re]; simp [Complex.ofReal_re, Complex.ofReal_im]

/-- For a smoothing function `f` supported in `t < x₀` (i.e. `f t = 0` for `x₀ ≤ t`),
the smoothed von Mangoldt series twisted by a Dirichlet character is summable, and its
real part equals the series of the real parts of the terms.

The summability is elementary: the support hypothesis kills every term with
`Real.log n / L ≥ x₀`, i.e. `n ≥ exp (x₀ * L)`, so only finitely many terms can be
nonzero. -/
theorem smoothed_vonMangoldt_tsum_re {x₀ : ℝ} (hx₀ : 0 < x₀) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {f : ℝ → ℝ} (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
    {L : ℝ} (hL : 0 < L) (s : ℂ) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod q) : ℂ) / (n : ℂ) ^ s * ((f (Real.log n / L) : ℝ) : ℂ))
      ∧ (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod q) : ℂ) / (n : ℂ) ^ s * ((f (Real.log n / L) : ℝ) : ℂ)).re
          = ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * ((χ (n : ZMod q) / (n : ℂ) ^ s).re) * f (Real.log n / L) := by
  have hxL : 0 < x₀ * L := mul_pos hx₀ hL
  have hsumm : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod q) : ℂ) / (n : ℂ) ^ s * ((f (Real.log n / L) : ℝ) : ℂ)) := by
    refine summable_of_ne_finset_zero (s := Finset.range (Nat.ceil (Real.exp (x₀ * L)))) ?_
    intro n hn
    have hnN : Nat.ceil (Real.exp (x₀ * L)) ≤ n := by
      simpa only [Finset.mem_range, not_lt] using hn
    have hle : Real.exp (x₀ * L) ≤ (n : ℝ) := by
      have h1 : Real.exp (x₀ * L) ≤ (Nat.ceil (Real.exp (x₀ * L)) : ℝ) := Nat.ceil_le.mp le_rfl
      exact h1.trans (by exact_mod_cast hnN)
    have hlog : x₀ * L ≤ Real.log (n : ℝ) := by
      calc x₀ * L = Real.log (Real.exp (x₀ * L)) := (Real.log_exp _).symm
        _ ≤ Real.log (n : ℝ) := Real.log_le_log (Real.exp_pos _) hle
    have harg : x₀ ≤ Real.log (n : ℝ) / L := (le_div_iff₀ hL).mpr hlog
    have hf0 : f (Real.log (n : ℝ) / L) = 0 := hsupp _ harg
    show (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod q) : ℂ) / (n : ℂ) ^ s * ((f (Real.log n / L) : ℝ) : ℂ) = 0
    rw [hf0]
    simp
  refine ⟨hsumm, ?_⟩
  rw [Complex.re_tsum hsumm]
  apply tsum_congr
  intro n
  have hcast : (ArithmeticFunction.vonMangoldt n : ℂ) = ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) := by
    norm_cast
  rw [hcast, mul_div_assoc, re_ofReal_mul_ofReal]

end Commons.NumberTheory.Linnik