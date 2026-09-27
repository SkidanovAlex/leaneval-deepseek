import Mathlib
import Submission.Work.Mostow.orthSmallCommuteDefs

namespace Work.Mostow.osc

open Submission.Mostow

/-- **Buser's estimate for the Engel sequence.**  If `mOf a ≤ 1/4` and `mOf b ≤ 1/4` then the
Engel sequence `B₀ = b`, `B_{i+1} = [a, B_i] = a B_i a⁻¹ B_i⁻¹` shrinks geometrically:
`mOf B_i ≤ (1/2)^i * (1/4)`.

Indeed `mOf B_{i+1} ≤ 2 * mOf a * mOf B_i ≤ (1/2) * mOf B_i`
(`Work.Mostow.mOf_commutator`, with `mOf a ≤ 1/4 ⇒ 2 * mOf a ≤ 1/2`), and `mOf b ≤ 1/4`. -/
lemma engelSeq_mOf_le {m : ℕ} (A : Subgroup (Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m))
    (a b : A)
    (ha : Work.Mostow.mOf (a : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) ≤ 1 / 4)
    (hb : Work.Mostow.mOf (b : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) ≤ 1 / 4)
    (i : ℕ) :
    Work.Mostow.mOf (Work.Mostow.engelSeq A a b i : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)
      ≤ (1 / 2 : ℝ) ^ i * (1 / 4) := by
  induction i with
  | zero => simpa using hb
  | succ n ih =>
    rw [Work.Mostow.engelSeq_succ]
    have h1 : (2 : ℝ) * Work.Mostow.mOf (a : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)
        ≤ 1 / 2 := by linarith
    have h2 : (2 : ℝ) * Work.Mostow.mOf (a : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)
          * Work.Mostow.mOf (Work.Mostow.engelSeq A a b n : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)
        ≤ (1 / 2) * Work.Mostow.mOf (Work.Mostow.engelSeq A a b n : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) :=
      mul_le_mul_of_nonneg_right h1 (Work.Mostow.mOf_nonneg _)
    have h3 : (1 / 2 : ℝ) * Work.Mostow.mOf (Work.Mostow.engelSeq A a b n : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)
        ≤ (1 / 2) * ((1 / 2 : ℝ) ^ n * (1 / 4)) :=
      mul_le_mul_of_nonneg_left ih (by norm_num)
    calc Work.Mostow.mOf ((a : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) * (Work.Mostow.engelSeq A a b n : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) * (a : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)⁻¹ * (Work.Mostow.engelSeq A a b n : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)⁻¹)
        ≤ 2 * Work.Mostow.mOf (a : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) * Work.Mostow.mOf (Work.Mostow.engelSeq A a b n : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) :=
          Work.Mostow.mOf_commutator _ _
      _ ≤ (1 / 2) * Work.Mostow.mOf (Work.Mostow.engelSeq A a b n : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) := h2
      _ ≤ (1 / 2) * ((1 / 2 : ℝ) ^ n * (1 / 4)) := h3
      _ = (1 / 2 : ℝ) ^ (n + 1) * (1 / 4) := by rw [pow_succ]; ring

end Work.Mostow.osc
