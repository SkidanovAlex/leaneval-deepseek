/-
# `FIArea2/R6/tau3InnerSelf` — the fibre bound for `τ₃(Δ)²`

For `z₁` primitive with `|z₁|² > N` and in the polar box (5.14), the sum of `τ₃(|Δ(z₁,z₂)|)²`
over the polar box is at most `C(θN + 1)(log N + 2)¹⁶`.

Since `Δ(z₁,·) = Im(z̄₁·)` is injective on the box (`Work.FIArea3.delta_fibre_injective`), each
value of `|Δ|` is attained at most twice (`sum_absDelta_le_two_mul`, the sign of `Δ` being the
only ambiguity), and every value is `< 4πθN` (`Work.FIArea2.absDelta_lt_four_pi`).  The fibre sum
is therefore at most twice the full divisor sum `∑_{n ≤ 4πθN} τ₃(n)² ≤ ∑ τ(n)⁴`
(`sum_tau3_sq_range_le`, using `tau3 ≤ τ²` and the fourth-power bound `sum_tau_pow_le 4`, whose
exponent `16 = 2⁴` is exactly the one appearing here).  Absorbing `< 4πθN` into `(θN+1)` and
`log(4πθN)` into `log N + 2` gives the stated bound.
-/
import Mathlib
import Submission.Work.FIArea2.R6.SixDefs
import Submission.Work.FIArea3.BoxDefs
import Submission.Work.FIArea3.delta_fibre_injective
import Submission.Work.FIArea2.absDelta_lt_four_pi
import Submission.Work.FIArea2.R6.sum_absDelta_le_two_mul
import Submission.Work.FIArea2.R6.sum_tau3_sq_range_le
import Submission.Work.FIArea2.R6.BetaFacts6

set_option maxHeartbeats 1000000

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

theorem tau3InnerSelf :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Pa : Work.FITop.Params) (φ : ℝ) (z1 : GaussianInt),
      (Pa.N : ℝ) < (Work.FIPlan.gnorm z1 : ℝ) →
      Work.FIPlan.IsPrimitive z1 →
      Work.FITop3.InPolarBox Pa φ z1 →
      (∑ z2 ∈ Work.FIArea3.polarBoxFinset Pa φ,
          ((tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ) ^ (2 : ℕ))
        ≤ C * (Pa.θ * Pa.N + 1) * (Real.log Pa.N + 2) ^ (16 : ℕ) := by
  obtain ⟨C2, hC2pos, hC2⟩ := sum_tau3_sq_range_le
  refine ⟨2 * (C2 * (4 * Real.pi + 1) * (8 : ℝ) ^ (16 : ℕ)) + 1, by positivity, ?_⟩
  intro Pa φ z1 hgn hprim hin
  set P : Finset GaussianInt := Work.FIArea3.polarBoxFinset Pa φ with hP
  set X : ℕ := ⌊4 * Real.pi * Pa.θ * Pa.N⌋₊ with hX
  have hθ0 : (0 : ℝ) < Pa.θ := Pa.hθ0
  have hN0 : (0 : ℝ) ≤ (Pa.N : ℝ) := by linarith [Pa.hN1]
  have hNpos : (0 : ℝ) < (Pa.N : ℝ) := by linarith [Pa.hN1]
  have hlogN0 : (0 : ℝ) ≤ Real.log (Pa.N : ℝ) := Real.log_nonneg Pa.hN1
  have hL0 : (0 : ℝ) ≤ Real.log (Pa.N : ℝ) + 2 := by linarith
  -- (1) `Δ(z₁,·)` is injective on the polar box
  have hinj : ∀ z ∈ P, ∀ z' ∈ P, Work.FIPlan.Delta z1 z = Work.FIPlan.Delta z1 z' → z = z' := by
    intro z hz z' hz' heq
    have hz2 : Work.FITop3.InPolarBox Pa φ z := by
      rw [hP, Work.FIArea3.mem_polarBoxFinset] at hz; exact hz.2
    have hz2' : Work.FITop3.InPolarBox Pa φ z' := by
      rw [hP, Work.FIArea3.mem_polarBoxFinset] at hz'; exact hz'.2
    exact Work.FIArea3.delta_fibre_injective hgn hprim hz2 hz2' heq
  -- (2) every `|Δ|` is at most `X`
  have hle : ∀ z ∈ P, Work.FIPlan.absDelta z1 z ≤ X := by
    intro z hz
    have hz2 : Work.FITop3.InPolarBox Pa φ z := by
      rw [hP, Work.FIArea3.mem_polarBoxFinset] at hz; exact hz.2
    have hlt := Work.FIArea2.absDelta_lt_four_pi hin hz2
    rw [hX]
    exact Nat.le_floor (le_of_lt hlt)
  -- (3) the two-piece bound
  have hstep1 : (∑ z ∈ P, (((tau3 (Work.FIPlan.absDelta z1 z) : ℕ)) : ℝ) ^ (2 : ℕ))
      ≤ 2 * ∑ n ∈ Finset.range (X + 1), (((tau3 n : ℕ)) : ℝ) ^ (2 : ℕ) :=
    sum_absDelta_le_two_mul (z1 := z1) (P := P) (X := X)
      (fun n => ((tau3 n : ℕ) : ℝ) ^ (2 : ℕ)) (fun n => pow_nonneg (Nat.cast_nonneg _) _) hinj hle
  have hstep2 : (∑ n ∈ Finset.range (X + 1), (((tau3 n : ℕ)) : ℝ) ^ (2 : ℕ))
      ≤ C2 * ((X : ℝ) + 1) * (Real.log (X : ℝ) + 2) ^ (16 : ℕ) := hC2 X
  -- (4) convert `X` and `log X` into `θN` and `log N`
  have hXle : (X : ℝ) ≤ 4 * Real.pi * Pa.θ * Pa.N := by
    rw [hX]; exact Nat.floor_le (by positivity)
  have hX1 : (X : ℝ) + 1 ≤ (4 * Real.pi + 1) * (Pa.θ * Pa.N + 1) := by
    have hθN0 : (0 : ℝ) ≤ Pa.θ * Pa.N := mul_nonneg hθ0.le hN0
    nlinarith only [hXle, Real.pi_pos, hθN0]
  have hlogX0 : (0 : ℝ) ≤ Real.log (X : ℝ) := by
    rcases Nat.eq_zero_or_pos X with h0 | hpos
    · rw [h0]; simp [Real.log_zero]
    · exact Real.log_nonneg (by exact_mod_cast hpos)
  have hlogX : Real.log (X : ℝ) + 2 ≤ 8 * (Real.log (Pa.N : ℝ) + 2) := by
    have hθ1 : Pa.θ ≤ 1 := theta_le_one6 Pa
    have hXN : (X : ℝ) ≤ 4 * Real.pi * Pa.N := by
      have h : Pa.θ * Pa.N ≤ Pa.N := by nlinarith only [hθ1, hN0]
      have h2 : 4 * Real.pi * Pa.θ * Pa.N ≤ 4 * Real.pi * Pa.N := by
        nlinarith only [Real.pi_pos, h]
      linarith only [hXle, h2]
    rcases Nat.eq_zero_or_pos X with h0 | hpos
    · rw [h0]; simp only [Nat.cast_zero, Real.log_zero]; linarith only [hlogN0]
    · have hlogXle : Real.log (X : ℝ) ≤ Real.log (4 * Real.pi * Pa.N) :=
        Real.log_le_log (by exact_mod_cast hpos) hXN
      have h4π : Real.log (4 * Real.pi * Pa.N) = Real.log (4 * Real.pi) + Real.log Pa.N :=
        Real.log_mul (by positivity) (ne_of_gt hNpos)
      have hlog4 : Real.log (4 : ℝ) ≤ 2 := by
        have h : Real.log (4 : ℝ) = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
          norm_num
        linarith only [h, Real.log_two_lt_d9]
      have hlogπ : Real.log Real.pi ≤ 3 := by
        have h1 : Real.log Real.pi ≤ Real.pi - 1 := Real.log_le_sub_one_of_pos Real.pi_pos
        linarith only [h1, Real.pi_lt_four]
      have hlog4π : Real.log (4 * Real.pi) ≤ 5 := by
        rw [Real.log_mul (by norm_num) (ne_of_gt Real.pi_pos)]
        linarith only [hlog4, hlogπ]
      rw [h4π] at hlogXle
      linarith only [hlogXle, hlog4π, hlogN0]
  have hC20 : (0 : ℝ) ≤ C2 := le_of_lt hC2pos
  have hK0 : (0 : ℝ) ≤ 4 * Real.pi + 1 := by linarith [Real.pi_pos]
  have h816 : (0 : ℝ) ≤ (8 : ℝ) ^ (16 : ℕ) := by positivity
  have hXp0 : (0 : ℝ) ≤ Pa.θ * Pa.N + 1 := by linarith [mul_nonneg hθ0.le hN0]
  have hLp0 : (0 : ℝ) ≤ (Real.log (Pa.N : ℝ) + 2) ^ (16 : ℕ) := pow_nonneg hL0 _
  have h1 : C2 * ((X : ℝ) + 1) * (Real.log (X : ℝ) + 2) ^ (16 : ℕ)
      ≤ C2 * ((4 * Real.pi + 1) * (Pa.θ * Pa.N + 1))
          * ((8 : ℝ) ^ (16 : ℕ) * (Real.log (Pa.N : ℝ) + 2) ^ (16 : ℕ)) := by
    have hlog16 : (Real.log (X : ℝ) + 2) ^ (16 : ℕ)
        ≤ ((8 : ℝ) * (Real.log (Pa.N : ℝ) + 2)) ^ (16 : ℕ) :=
      pow_le_pow_left₀ (by linarith only [hlogX0]) hlogX 16
    have hmul : ((8 : ℝ) * (Real.log (Pa.N : ℝ) + 2)) ^ (16 : ℕ)
        = (8 : ℝ) ^ (16 : ℕ) * (Real.log (Pa.N : ℝ) + 2) ^ (16 : ℕ) := by rw [mul_pow]
    calc C2 * ((X : ℝ) + 1) * (Real.log (X : ℝ) + 2) ^ (16 : ℕ)
        ≤ C2 * ((4 * Real.pi + 1) * (Pa.θ * Pa.N + 1))
            * ((8 : ℝ) * (Real.log (Pa.N : ℝ) + 2)) ^ (16 : ℕ) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hX1 hC20) hlog16
            (pow_nonneg (by linarith only [hlogX0]) _) (mul_nonneg hC20 (mul_nonneg hK0 hXp0))
      _ = C2 * ((4 * Real.pi + 1) * (Pa.θ * Pa.N + 1))
            * ((8 : ℝ) ^ (16 : ℕ) * (Real.log (Pa.N : ℝ) + 2) ^ (16 : ℕ)) := by rw [hmul]
  have h4 : 2 * (C2 * ((4 * Real.pi + 1) * (Pa.θ * Pa.N + 1))
          * ((8 : ℝ) ^ (16 : ℕ) * (Real.log (Pa.N : ℝ) + 2) ^ (16 : ℕ)))
      = (2 * C2 * (4 * Real.pi + 1) * (8 : ℝ) ^ (16 : ℕ))
          * ((Pa.θ * Pa.N + 1) * (Real.log (Pa.N : ℝ) + 2) ^ (16 : ℕ)) := by ring
  have h5 : (2 * C2 * (4 * Real.pi + 1) * (8 : ℝ) ^ (16 : ℕ))
          * ((Pa.θ * Pa.N + 1) * (Real.log (Pa.N : ℝ) + 2) ^ (16 : ℕ))
      ≤ (2 * (C2 * (4 * Real.pi + 1) * (8 : ℝ) ^ (16 : ℕ)) + 1)
          * (Pa.θ * Pa.N + 1) * (Real.log (Pa.N : ℝ) + 2) ^ (16 : ℕ) := by
    have hA0 : (0 : ℝ) ≤ 2 * C2 * (4 * Real.pi + 1) * (8 : ℝ) ^ (16 : ℕ) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC20) hK0) h816
    have hle' : 2 * C2 * (4 * Real.pi + 1) * (8 : ℝ) ^ (16 : ℕ)
        ≤ 2 * (C2 * (4 * Real.pi + 1) * (8 : ℝ) ^ (16 : ℕ)) + 1 := by linarith only [hA0]
    have hstep : (2 * C2 * (4 * Real.pi + 1) * (8 : ℝ) ^ (16 : ℕ))
          * ((Pa.θ * Pa.N + 1) * (Real.log (Pa.N : ℝ) + 2) ^ (16 : ℕ))
        ≤ (2 * (C2 * (4 * Real.pi + 1) * (8 : ℝ) ^ (16 : ℕ)) + 1)
          * ((Pa.θ * Pa.N + 1) * (Real.log (Pa.N : ℝ) + 2) ^ (16 : ℕ)) :=
      mul_le_mul_of_nonneg_right hle' (mul_nonneg hXp0 hLp0)
    have heq : (2 * (C2 * (4 * Real.pi + 1) * (8 : ℝ) ^ (16 : ℕ)) + 1)
          * ((Pa.θ * Pa.N + 1) * (Real.log (Pa.N : ℝ) + 2) ^ (16 : ℕ))
        = (2 * (C2 * (4 * Real.pi + 1) * (8 : ℝ) ^ (16 : ℕ)) + 1)
          * (Pa.θ * Pa.N + 1) * (Real.log (Pa.N : ℝ) + 2) ^ (16 : ℕ) := by ring
    exact le_trans hstep (le_of_eq heq)
  calc (∑ z ∈ P, (((tau3 (Work.FIPlan.absDelta z1 z) : ℕ)) : ℝ) ^ (2 : ℕ))
      ≤ 2 * ∑ n ∈ Finset.range (X + 1), (((tau3 n : ℕ)) : ℝ) ^ (2 : ℕ) := hstep1
    _ ≤ 2 * (C2 * ((X : ℝ) + 1) * (Real.log (X : ℝ) + 2) ^ (16 : ℕ)) := by
        linarith only [hstep2]
    _ ≤ 2 * (C2 * ((4 * Real.pi + 1) * (Pa.θ * Pa.N + 1))
          * ((8 : ℝ) ^ (16 : ℕ) * (Real.log (Pa.N : ℝ) + 2) ^ (16 : ℕ))) :=
        mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ = (2 * C2 * (4 * Real.pi + 1) * (8 : ℝ) ^ (16 : ℕ))
          * ((Pa.θ * Pa.N + 1) * (Real.log (Pa.N : ℝ) + 2) ^ (16 : ℕ)) := h4
    _ ≤ (2 * (C2 * (4 * Real.pi + 1) * (8 : ℝ) ^ (16 : ℕ)) + 1)
          * (Pa.θ * Pa.N + 1) * (Real.log (Pa.N : ℝ) + 2) ^ (16 : ℕ) := h5

end

end Work.FIArea2.R6
