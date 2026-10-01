/-
# Area 4 / HB §11 (11.9) — the inverse-Mellin representation of `Ssm`

Namespace `Work.LinnikAreas.Density4`.

This file collects the integrand `SsmTerm` of the inverse-Mellin representation of the
smoothed sum `Ssm = Σ_n Ψ(n)Θ(n)χ(n)·n^{-ρ}·e^{-n/X}` (HB (11.6)–(11.9)), together with the
elementwise measure-theoretic facts about it.  It is used by
`Submission.Work.LinnikAreas.Density4.Ssm_eq_line`, which assembles the identity
`Ssm = (1/(2π)) ∫_ℝ Γ(1+it)·X^{1+it}·Σ_n Ψ(n)Θ(n)χ(n)·n^{-(ρ+1+it)} dt`.
-/
import Mathlib
import Submission.Work.LinnikAreas.Density4.SsmSetup
import Submission.Work.LinnikAreas.Density4.mellin_kernel_exp

open DirichletCharacter Complex MeasureTheory
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas.Density4

/-- The `n`-th summand of the inverse-Mellin representation of `Ssm`:
`Ψ(n)Θ(n)χ(n)·n^{-ρ}·(n/X)^{-(1+it)}·Γ(1+it)`.  Its `(1/(2π))·∫_ℝ dt` is the `n`-th term
`Ψ(n)Θ(n)χ(n)·n^{-ρ}e^{-n/X}` of `Ssm`. -/
def SsmTerm (q : ℕ) [NeZero q] (U V W X : ℝ) (χ : DirichletCharacter ℂ q) (ρ : ℂ)
    (n : ℕ) (t : ℝ) : ℂ :=
  mollCoeff q U V W χ n * (n : ℂ) ^ (-ρ)
    * ((((n : ℝ) / X : ℝ) : ℂ) ^ (-(1 + (t : ℂ) * Complex.I))
        * Complex.Gamma ((1 : ℂ) + (t : ℂ) * Complex.I))

/-- The mollified coefficient vanishes at `n = 0`. -/
lemma mollCoeff_zero (q : ℕ) [NeZero q] (U V W : ℝ) (χ : DirichletCharacter ℂ q) :
    mollCoeff q U V W χ 0 = 0 := by
  simp [mollCoeff, psiS_zero]

/-- The `0`-th summand vanishes, because `Ψ(0) = 0`. -/
lemma SsmTerm_zero (q : ℕ) [NeZero q] (U V W X : ℝ) (χ : DirichletCharacter ℂ q) (ρ : ℂ)
    (t : ℝ) : SsmTerm q U V W X χ ρ 0 t = 0 := by
  simp [SsmTerm, mollCoeff_zero]

/-- `t ↦ ‖Γ(1 + it)‖` is integrable on `ℝ` (Stirling/exponential decay on the vertical line
`Re s = 1`). -/
theorem integrable_norm_gamma_vertical_one :
    Integrable (fun t : ℝ => ‖Complex.Gamma ((1 : ℂ) + (t : ℂ) * Complex.I)‖) := by
  obtain ⟨C, hCpos, hCbd⟩ :=
    Commons.Analysis.SpecialFunctions.Gamma.gamma_vertical_exp_decay 1 one_pos
  have h := gamma_vertical_integrable_of_bound 1 C hCpos (fun t => by
    have ht := hCbd t
    rw [mul_comm Complex.I] at ht
    exact ht)
  exact h.norm

/-- Pointwise norm bound for the summands.  For `n ≥ 1` it is an identity; for `n = 0`
both sides vanish. -/
lemma norm_SsmTerm_le (q : ℕ) [NeZero q] (U V W X : ℝ) (χ : DirichletCharacter ℂ q) (ρ : ℂ)
    (hX : 0 < X) (n : ℕ) (t : ℝ) :
    ‖SsmTerm q U V W X χ ρ n t‖
      ≤ (‖mollCoeff q U V W χ n‖ * (n : ℝ) ^ (-ρ.re) * (X / n))
          * ‖Complex.Gamma ((1 : ℂ) + (t : ℂ) * Complex.I)‖ := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [SsmTerm_zero, mollCoeff_zero]
    simp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hcast : (n : ℂ) = ((n : ℝ) : ℂ) := by push_cast; ring
  rw [SsmTerm, norm_mul, norm_mul, norm_mul, hcast,
    Complex.norm_cpow_eq_rpow_re_of_pos hn0 (-ρ),
    Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hn0 hX) (-(1 + (t : ℂ) * Complex.I))]
  simp only [Complex.neg_re, Complex.add_re, Complex.one_re, Complex.mul_re,
    Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero,
    Complex.ofReal_im]
  rw [show (-(1 : ℝ)) = (-1 : ℝ) by ring, Real.rpow_neg_one, inv_div]
  exact le_of_eq (by ring)

