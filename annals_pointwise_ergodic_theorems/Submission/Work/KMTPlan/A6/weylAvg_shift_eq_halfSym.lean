import Mathlib
import Submission.Work.KMTPlan.A6.SymIdentityAux

namespace Work.KMTPlan.A6

/-- **The real evaluation of an integer polynomial at an integer point**:
`PevalR P n = P.eval n` for `n : ℤ`. -/
lemma symp_PevalR_intCast (P : Polynomial ℤ) (n : ℤ) :
    Work.KMTAreas.A7.PevalR P (n : ℝ) = ((P.eval n : ℤ) : ℝ) := by
  simp [Work.KMTAreas.A7.PevalR]

/-- **The summand of `weylAvg` at an aliased frequency is the unshifted summand of `halfSym`.**

The two arithmetic characters cancel the two shifts `e (-n · gamR γ₁)` and
`e (-PevalR P n · gamR γ₂)` produced by evaluating the phase at `ξ₁ = x - gamR γ₁ + m₁`,
`ξ₂ = y - gamR γ₂ + m₂`, and the integer residues `m₁ n`, `m₂ P.eval n` contribute `e (·) = 1`. -/
lemma momPhase_shift_eq_halfSym_summand (P : Polynomial ℤ) (N : ℕ)
    (γ₁ γ₂ : Work.Analysis.IonescuWainger.Circle) (x y : ℝ) (m₁ m₂ : ℤ) (n : ℕ) :
    Work.KMTAreas.A7.momPhase P N γ₁ γ₂
        (x - gamR γ₁ + (m₁ : ℝ)) (y - gamR γ₂ + (m₂ : ℝ)) (n : ℤ)
      = eeC ((n : ℝ) * x + ((P.eval (n : ℤ) : ℤ) : ℝ) * y) := by
  rw [Work.KMTAreas.A7.momPhase]
  rw [symp_fourier_eq_eeC, symp_fourier_eq_eeC]
  rw [show (Work.KMTAreas.A7.ee : ℝ → ℂ) = eeC from rfl]
  rw [← symp_eeC_add, ← symp_eeC_add]
  have h : ((n : ℤ) : ℝ) * gamR γ₁ + ((P.eval (n : ℤ) : ℤ) : ℝ) * gamR γ₂
      + ((x - gamR γ₁ + (m₁ : ℝ)) * ((n : ℤ) : ℝ)
          + (y - gamR γ₂ + (m₂ : ℝ)) * Work.KMTAreas.A7.PevalR P ((n : ℤ) : ℝ))
      = (n : ℝ) * x + ((P.eval (n : ℤ) : ℤ) : ℝ) * y
          + ((m₁ * (n : ℤ) + m₂ * P.eval (n : ℤ) : ℤ) : ℝ) := by
    rw [symp_PevalR_intCast]
    push_cast
    ring
  rw [h, symp_eeC_add, symp_eeC_int, mul_one]

/-- **The discrete average is invisible to the aliasing shift.**

`weylAvg P N γ₁ γ₂ ξ₁ ξ₂ = N⁻¹ ∑_{n ∈ Ioc (N/2) N} fourier n γ₁ * fourier (P.eval n) γ₂ *
e(ξ₁ n + ξ₂ PevalR P n)` is the discrete average of §6, and `halfSym N P x y` is the same
trigonometric polynomial at the *unshifted* point with `fourier n 0 = 1`.

The characters `fourier n γ₁ = e (n * gamR γ₁)` and `fourier (P.eval n) γ₂ = e (P.eval n * gamR γ₂)`
cancel exactly against the terms `e (-n gamR γ₁)` and `e (-PevalR P n * gamR γ₂)` produced by
evaluating the phase at `ξ₁ = x - gamR γ₁ + m₁`, `ξ₂ = y - gamR γ₂ + m₂`; the residues are
`e (n m₁)` and `e (PevalR P n * m₂)`, both `= 1` because `n m₁` and `PevalR P n * m₂` are integers
(`PevalR P n` is the cast of the integer `P.eval n`).  Hence the value is independent of `γ₁, γ₂`
and of the representatives `m₁, m₂`, and equals `halfSym N P x y`. -/
theorem weylAvg_shift_eq_halfSym (P : Polynomial ℤ) (N : ℕ)
    (γ₁ γ₂ : Work.Analysis.IonescuWainger.Circle) (x y : ℝ) (m₁ m₂ : ℤ) :
    Work.KMTAreas.A7.weylAvg P N γ₁ γ₂
        (x - Work.KMTPlan.A6.gamR γ₁ + (m₁ : ℝ)) (y - Work.KMTPlan.A6.gamR γ₂ + (m₂ : ℝ))
      = Work.KMTPlan.A6.halfSym N P x y := by
  unfold Work.KMTAreas.A7.weylAvg halfSym
  congr 1
  exact Finset.sum_congr rfl fun n _ =>
    momPhase_shift_eq_halfSym_summand P N γ₁ γ₂ x y m₁ m₂ n

end Work.KMTPlan.A6
