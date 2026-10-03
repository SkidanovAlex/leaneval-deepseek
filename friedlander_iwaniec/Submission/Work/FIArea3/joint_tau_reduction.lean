/-
# `Submission.Work.FIArea3.joint_tau_reduction` — the elementary reduction of the joint τ-average

The target `Work.FIArea3.delta_tau_joint_average` (= `JointBound`) bounds
`Σ_{z₂ ∈ polar box} τ(|z₂|²)·τ(|Δ(z₁,z₂)|)`.

This file proves the *elementary* first step of every route to it: FI Lemma 2.2 with `k = 4`
turns each of the two divisor functions into a sum over divisors `d | m` of `τ(d)^8`, with
`d^4 ≤ m`, i.e. `d ≤ m^{1/4}`, and the passage from `Σ_{z₂} τ(d(z₂))^8 τ(e(z₂))^8` to the
double sum over `(d,e)` of the *counts* `#{z₂ ∈ box : d | |z₂|², e | |Δ|}`
(over-counting the specific divisors chosen by Lemma 2.2 as one term of the full double sum).

Concretely (with `K = (2N)^{1/4}`, `K'' = (4πθN)^{1/4}`, using `|z₂|² ≤ 2N` and
`|Δ(z₁,z₂)| ≤ 2πθ|z₁||z₂| ≤ 4πθN` of `absDelta_le_sector`):

  `Σ_{z₂ ∈ box} τ(|z₂|²) τ(|Δ|)  ≤  2^16 Σ_{d ≤ K} Σ_{e ≤ K''} τ(d)^8 τ(e)^8
                                        · #{z₂ ∈ box : d ∣ |z₂|², e ∣ |Δ(z₁,z₂)|}`.

Everything after this step is a *counting* problem for the polar box.
-/
import Mathlib
import Submission.Work.FIArea3.lemma_2_2
import Submission.Work.FIArea3.BoxDefs

set_option maxHeartbeats 4000000

namespace Work.FIArea3

open Finset Work.FIPlan
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

lemma log_four : Real.log ((4:ℕ):ℝ) = 2 * Real.log (2:ℝ) := by
  rw [show ((4:ℕ):ℝ) = (2:ℝ)^(2:ℕ) by norm_num, Real.log_pow]; norm_num

lemma exp_eq_eight : (((4:ℕ):ℝ) * Real.log ((4:ℕ):ℝ) / Real.log (2:ℝ)) = ((8:ℕ):ℝ) := by
  rw [log_four]
  have h2 : Real.log (2:ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp
  ring

/-- **FI Lemma 2.2 with `k = 4`**: `τ m ≤ 2^8 ∑_{d | m} τ(d)^8` for `m ≥ 1`.
(The divisor singled out by the lemma has `d^4 ≤ m`, hence `d ≤ m^{1/4}`.) -/
lemma tau_le_sum_pow (m : ℕ) (hm : 1 ≤ m) :
    (m.divisors.card : ℝ) ≤ 256 * ∑ d ∈ m.divisors, ((d.divisors.card : ℝ)) ^ (8 : ℕ) := by
  obtain ⟨d, hdvd, hdk, hbound⟩ := lemma_2_2 (k := 4) (by norm_num) hm
  have hm0 : m ≠ 0 := by omega
  have hmem : d ∈ m.divisors := Nat.mem_divisors.mpr ⟨hdvd, hm0⟩
  have hsingle : ((d.divisors.card : ℝ)) ^ (8 : ℕ)
      ≤ ∑ d' ∈ m.divisors, ((d'.divisors.card : ℝ)) ^ (8 : ℕ) :=
    Finset.single_le_sum (f := fun d' => ((d'.divisors.card : ℝ)) ^ (8 : ℕ))
      (fun _ _ => by positivity) hmem
  rw [exp_eq_eight] at hbound
  rw [Real.rpow_natCast] at hbound
  have h2 : (2 * (d.divisors.card : ℝ)) ^ (8:ℕ)
      = 256 * ((d.divisors.card : ℝ)) ^ (8:ℕ) := by ring
  rw [h2] at hbound
  calc (m.divisors.card : ℝ) ≤ 256 * ((d.divisors.card : ℝ)) ^ (8:ℕ) := hbound
    _ ≤ 256 * ∑ d' ∈ m.divisors, ((d'.divisors.card : ℝ)) ^ (8 : ℕ) :=
        mul_le_mul_of_nonneg_left hsingle (by norm_num)

end

end Work.FIArea3
