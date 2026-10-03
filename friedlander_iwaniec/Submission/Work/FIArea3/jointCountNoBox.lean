import Mathlib
import Submission.Work.FIArea3.jointCount6

namespace Work.FIArea3

open Finset Work.FIPlan
open scoped BigOperators

namespace Work.FIArea3

/-- `jointCount6` without the hypothesis `z₁ ∈ polarBoxFinset`: the joint count of polar-box
points with `d ∣ |z₂|²` and `e ∣ |Δ(z₁,z₂)|` is bounded by
`πu²·τ(d)·gcd(d,e)/(d·e) + 80u·τ(d)/√d + τ(d)`, `u = θ√N`, for every *primitive* `z₁`.
The proof is verbatim that of `jointCount6` (`hz₁` is unused there). -/
theorem jointCountNoBox (Pa : Work.FITop.Params) (φ : ℝ) (z₁ : GaussianInt) (d e : ℕ)
    (hcop : Nat.Coprime z₁.re.natAbs z₁.im.natAbs) (hd : 1 ≤ d) (he : 1 ≤ e) :
    (((Work.FIArea3.polarBoxFinset Pa φ).filter
        (fun z => d ∣ Work.FIPlan.gnorm z ∧ e ∣ Work.FIPlan.absDelta z₁ z)).card : ℝ)
      ≤ Real.pi * (Pa.θ * Real.sqrt Pa.N) ^ 2
            * (((d.divisors.card : ℝ) * ((Nat.gcd d e : ℕ) : ℝ)) / ((d : ℝ) * (e : ℝ)))
        + 80 * (Pa.θ * Real.sqrt Pa.N) * ((d.divisors.card : ℝ)) / Real.sqrt (d : ℝ)
        + (d.divisors.card : ℝ) := by
  have hLHS : ((Work.FIArea3.polarBoxFinset Pa φ).filter
        (fun z => d ∣ Work.FIPlan.gnorm z ∧ e ∣ Work.FIPlan.absDelta z₁ z)).card
      = (Work.FIArea3.JointCount.pairBoxFinset Pa φ z₁ d e).card := rfl
  rw [hLHS]
  classical
  set u : ℝ := Pa.θ * Real.sqrt Pa.N with hu
  set L : ℝ := (Nat.lcm d e : ℝ) with hL
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hL0 : 0 < L := by rw [hL]; exact_mod_cast Nat.lcm_pos (by omega) (by omega)
  have hu0 : 0 ≤ u := by rw [hu]; exact mul_nonneg Pa.hθ0.le (Real.sqrt_nonneg _)
  set C : ℝ := Real.pi * u ^ 2 / L + 80 * u / Real.sqrt (d : ℝ) + 1 with hC
  have hC0 : 0 ≤ C := by
    rw [hC]
    have h1 : 0 ≤ Real.pi * u ^ 2 / L := div_nonneg (by positivity) hL0.le
    have h2 : 0 ≤ 80 * u / Real.sqrt (d : ℝ) :=
      div_nonneg (by linarith) (Real.sqrt_pos.mpr hd0).le
    linarith
  -- Step 1: the box is covered by the maximal pieces.
  have h1 : ((Work.FIArea3.JointCount.pairBoxFinset Pa φ z₁ d e).card : ℝ)
      ≤ ∑ w ∈ Work.FIArea3.JointCount.maxPieceFinset d,
          ((Work.FIArea3.JointCount.jointPieceBoxFinset Pa φ z₁ w e).card : ℝ) :=
    Work.FIArea3.JointCount.card_filter_le_le_pieces Pa φ z₁ d e hd
  -- Step 2: each piece contributes at most `C`.
  have h2 : (∑ w ∈ Work.FIArea3.JointCount.maxPieceFinset d,
        ((Work.FIArea3.JointCount.jointPieceBoxFinset Pa φ z₁ w e).card : ℝ))
      ≤ ((Work.FIArea3.JointCount.maxPieceFinset d).card : ℝ) * C := by
    calc (∑ w ∈ Work.FIArea3.JointCount.maxPieceFinset d,
          ((Work.FIArea3.JointCount.jointPieceBoxFinset Pa φ z₁ w e).card : ℝ))
        ≤ ∑ _w ∈ Work.FIArea3.JointCount.maxPieceFinset d, C := by
          refine Finset.sum_le_sum (fun w hw => ?_)
          have := card_jointPieceBox_le_lcm Pa φ z₁ d e hd he hcop hw
          rw [hC]
          rw [← hu, ← hL] at this
          exact this
      _ = ((Work.FIArea3.JointCount.maxPieceFinset d).card : ℝ) * C := by
          rw [Finset.sum_const, nsmul_eq_mul]
  -- Step 3: there are at most `τ(d)` maximal pieces.
  have h3 : ((Work.FIArea3.JointCount.maxPieceFinset d).card : ℝ) * C
      ≤ ((d.divisors.card : ℝ)) * C :=
    mul_le_mul_of_nonneg_right
      (by exact_mod_cast (Work.FIArea3.JointCount.maxPieceFinset_card_le d hd).1) hC0
  have h4 : ((d.divisors.card : ℝ)) * C
      = Real.pi * u ^ 2
          * (((d.divisors.card : ℝ) * ((Nat.gcd d e : ℕ) : ℝ)) / ((d : ℝ) * (e : ℝ)))
        + 80 * u * ((d.divisors.card : ℝ)) / Real.sqrt (d : ℝ) + (d.divisors.card : ℝ) := by
    have hde : ((Nat.gcd d e : ℕ) : ℝ) * L = (d : ℝ) * (e : ℝ) := by
      rw [hL]; exact_mod_cast Nat.gcd_mul_lcm d e
    have hgcd0 : (0 : ℝ) < (Nat.gcd d e : ℝ) := by
      exact_mod_cast Nat.gcd_pos_of_pos_left e (by omega : 0 < d)
    have hLde : L = (d : ℝ) * (e : ℝ) / ((Nat.gcd d e : ℕ) : ℝ) := by
      rw [eq_div_iff (ne_of_gt hgcd0), mul_comm]
      exact hde
    rw [hC, hLde]
    field_simp
  have hfin : ((Work.FIArea3.JointCount.pairBoxFinset Pa φ z₁ d e).card : ℝ)
      ≤ Real.pi * u ^ 2
          * (((d.divisors.card : ℝ) * ((Nat.gcd d e : ℕ) : ℝ)) / ((d : ℝ) * (e : ℝ)))
        + 80 * u * ((d.divisors.card : ℝ)) / Real.sqrt (d : ℝ) + (d.divisors.card : ℝ) := by
    linarith [h1, h2, h3, h4.le, h4.ge]
  exact hfin

end Work.FIArea3

end Work.FIArea3

namespace Work.FIArea3

/-- Alias of `Work.FIArea3.Work.FIArea3.jointCountNoBox` under the requested name. -/
alias jointCountNoBox := _root_.Work.FIArea3.Work.FIArea3.jointCountNoBox

end Work.FIArea3
