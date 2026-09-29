import Mathlib
import Submission.Work.ALift.bridge

/-!
# Area ALift — the lift `Φ` avoids the singularities of Zagier's operator on the annulus

The operator `P·y'' + Q·y' + R·y = b + c/(1-x)` of Theorem A
(`P(x) = x(1-x)(1-9x)`, `Q(x) = 1 - 20x + 27x²`, `R(x) = -3 + 9x`, inhomogeneity `b + c/(1-x)`)
has its singularities at `x ∈ {0, 1/9, 1}` (the zeros of `P`, and the pole of the inhomogeneity).
For a lift `Φ` of `φ_A` (i.e. `Φ z + Φ(-z) = Φ z · Φ(-z) = phiA (z²)`) we show that on the annulus
`1/31 < ‖z‖ < 1` the values `0, 1, 1/9` are all avoided, so that the pulled-back system is
holomorphic there:

* `Φ z = 0` forces `z = 0` (`LiftData`);
* `Φ z = 1` is incompatible with `Φ z + Φ(-z) = Φ z · Φ(-z)` (`1 + w = w`);
* `Φ z = 1/9` forces `Φ(-z) = -1/8` and hence `phiA (z²) = -1/72`; by the certified numerics
  `ANumerics` (conjunct 3) this needs `‖z²‖ < 1/1000`, i.e. `‖z‖ < 1/√1000 < 1/31`.
-/

namespace Work.ALift

open Submission.CDTPlan Metric

/-- On the annulus `1/31 < ‖z‖ < 1` the lift `Φ` avoids all singularities of Zagier's operator. -/
theorem Phi_avoid (hN : ANumerics) (Φ : ℂ → ℂ) (hL : LiftData phiA Φ) :
    ∀ z : ℂ, 1 / 31 < ‖z‖ → ‖z‖ < 1 → Pd (Φ z) ≠ 0 ∧ (1 - Φ z) ≠ 0 := by
  obtain ⟨hdiff, heq, hzero⟩ := hL
  intro z hzr hz1
  have hzmem : z ∈ ball (0 : ℂ) 1 := by rw [mem_ball, dist_zero_right]; exact hz1
  obtain ⟨hsum, hprod⟩ := heq z hzmem
  have hne1 : Φ z ≠ 1 := by
    intro h1
    rw [h1] at hsum hprod
    rw [one_mul] at hprod
    rw [hprod] at hsum
    exact absurd hsum (by norm_num)
  have hne0 : Φ z ≠ 0 := by
    intro h0
    have hz0 : z = 0 := hzero z hzmem h0
    rw [hz0, norm_zero] at hzr
    norm_num at hzr
  have hne9 : Φ z ≠ 1 / 9 := by
    intro h9
    rw [h9] at hsum hprod
    -- `Φ (-z) = -1/8` and `phiA (z^2) = -1/72`
    have hw : Φ (-z) = -1 / 8 := by
      have h1 : (1 / 9 : ℂ) + Φ (-z) = phiA (z ^ 2) := hsum
      have h2 : (1 / 9 : ℂ) * Φ (-z) = phiA (z ^ 2) := hprod
      linear_combination (9 / 8 : ℂ) * (h1 - h2)
    have hphi : phiA (z ^ 2) = -1 / 72 := by
      rw [← hsum, hw]; norm_num
    have hzsq_le : ‖z ^ 2‖ ≤ 1 := by
      rw [norm_pow]; nlinarith [norm_nonneg z, hz1.le]
    have hlt : ‖z ^ 2‖ < 1 / 1000 := by
      by_contra hcon
      rw [not_lt] at hcon
      exact hN.2.2 (z ^ 2) hcon hzsq_le hphi
    have hsq : ‖z‖ ^ 2 < 1 / 1000 := by rw [norm_pow] at hlt; exact hlt
    have hgt : (1 / 31 : ℝ) ^ 2 < ‖z‖ ^ 2 := by
      have h31 : (0:ℝ) ≤ 1 / 31 := by norm_num
      exact pow_lt_pow_left₀ hzr h31 (by norm_num)
    nlinarith [hsq, hgt]
  refine ⟨?_, ?_⟩
  · intro hPd
    unfold Pd at hPd
    rcases mul_eq_zero.mp hPd with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact hne0 h'
      · exact hne1 (by linear_combination (-1) * h')
    · exact hne9 (by linear_combination (-1/9) * h)
  · intro h
    exact hne1 (by linear_combination (-1) * h)

end Work.ALift
