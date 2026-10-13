/-
# `Work.FTS.PhiStar.Series.Deleg.gCAtOne`

The value of the Gegenbauer polynomial `C^{(3/2)}_k` at `1`:

  `gC k 1 = (k+1)(k+2)/2`.

This is the classical evaluation `C_n^{(λ)}(1) = binom(n + 2λ - 1, n)` (here `λ = 3/2`), and
it is what makes the eigenfunctions `eFam m θ = cos θ · gC (2m+1) (sin θ)` normalisable
(`∫_0^1 (1 - u²) q(u)² du` is evaluated at `u = 1` as the natural boundary of the
Sturm–Liouville problem).

The proof is a two-step induction on `k` from the three-term recurrence `gC_rec`
(`(n+2) C_{n+2} = (2n+5) x C_{n+1} - (n+3) C_n`), evaluated at `x = 1`; the two base cases
are `C_0 = 1` and `C_1 = 3x`.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.FTS.PhiStar.Gegenbauer.gC_ode

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real

namespace Work.FTS.PhiStar.Series.Deleg

open Work.FTS.PhiStar.Gegenbauer (gC gC_rec)

/-- The value of `C^{(3/2)}_k` at `1`: `C^{(3/2)}_k(1) = (k+1)(k+2)/2`. -/
theorem gCAtOne (k : ℕ) :
    Work.FTS.PhiStar.Gegenbauer.gC k 1 = (((k : ℝ) + 1) * ((k : ℝ) + 2)) / 2 := by
  induction k using Nat.twoStepInduction with
  | zero =>
    rw [show gC 0 = (fun _ : ℝ => (1 : ℝ)) from rfl]
    norm_num
  | one =>
    rw [show gC 1 = (fun x : ℝ => 3 * x) from rfl]
    norm_num
  | more n ih1 ih2 =>
    have h2 : ((n : ℝ) + 2) ≠ 0 := by positivity
    have h : ((n : ℝ) + 2) * gC (n + 2) 1
        = ((n : ℝ) + 2) * (((n : ℝ) + 2 + 1) * ((n : ℝ) + 2 + 2) / 2) := by
      rw [gC_rec n 1, ih1, ih2]
      push_cast
      ring
    have hh := mul_left_cancel₀ h2 h
    push_cast
    exact hh

end Work.FTS.PhiStar.Series.Deleg
