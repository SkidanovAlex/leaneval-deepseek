import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.box_iInter_conjBox

/-!
# `EKLC6Core.aDiag_conj_expansion` — the diagonal flow expands a full neighbourhood of `1`

Whereas `aDiag_exp_contraction` controls the action of `aDiag t ^ n` on a *contracted*
horospherical subgroup (entries damped by `e^{-n·gap}`), here we record the elementary
complementary fact used when an *arbitrary* element `w` of the ambient neighbourhood `V ρ`
of the identity (not lying in any special subgroup) is conjugated: there is a single rate
`α ≥ 0`, depending only on `t`, such that

`aDiag t ^ n · w · (aDiag t ^ n)⁻¹ ∈ V (ρ · e^{α n})`  for every `n` and every `ρ > 0`.

`α = 2 ∑ k |t k|` is a crude but uniform bound for the largest exponent gap `t i - t j`, and the
identity `((aDiag t)ⁿ w (aDiag t)⁻ⁿ)ᵢⱼ = e^{n (tᵢ - tⱼ)} wᵢⱼ` (`boxi_conj_pow_apply`) turns the
statement into the entrywise estimate

`|wᵢⱼ| e^{n (tᵢ - tⱼ)} ≤ ρ e^{2 n ∑|t|}`
-/

open Work.EKLContract

namespace Work.EKLC6Core

/-- **Expansion of the full identity neighbourhood under conjugation by the diagonal flow.**
For every exponent vector `t : Fin 3 → ℝ` there is a rate `α ≥ 0` such that conjugating the
`V ρ`-neighbourhood of the identity by `aDiag t ^ n` lands inside `V (ρ · e^{α n})`. -/
theorem aDiag_conj_expansion (t : Fin 3 → ℝ) :
    ∃ α : ℝ, 0 ≤ α ∧ ∀ (n : ℕ) (ρ : ℝ), 0 < ρ → ∀ w : Work.EKLContract.SL3,
      w ∈ Work.EKLContract.V ρ →
        Work.EKLContract.aDiag t ^ n * w * (Work.EKLContract.aDiag t ^ n)⁻¹ ∈
          Work.EKLContract.V (ρ * Real.exp (α * (n : ℝ))) := by
  refine ⟨2 * ∑ k, |t k|, by positivity, ?_⟩
  intro n ρ hρ w hw
  show ∀ i j : Fin 3,
    |(Work.EKLContract.aDiag t ^ n * w * (Work.EKLContract.aDiag t ^ n)⁻¹ : Work.EKLContract.SL3) i j
        - ((1 : Work.EKLContract.SL3) i j)|
      < ρ * Real.exp ((2 * ∑ k, |t k|) * (n : ℝ))
  intro i j
  rw [Work.EKLC6Core.boxi_conj_pow_apply]
  -- the exponent gap `t i - t j` is dominated by `2 ∑ |t k|`
  have hsum_ge : ∀ a : Fin 3, |t a| ≤ ∑ k, |t k| := fun a =>
    Finset.single_le_sum (fun k _ => abs_nonneg (t k)) (Finset.mem_univ a)
  have hdiff : t i - t j ≤ 2 * ∑ k, |t k| := by
    have h1 : t i ≤ |t i| := le_abs_self _
    have h2 : -t j ≤ |t j| := neg_le_abs _
    have h3 := hsum_ge i
    have h4 := hsum_ge j
    linarith
  have hexpmono : Real.exp ((n : ℝ) * (t i - t j))
      ≤ Real.exp ((2 * ∑ k, |t k|) * (n : ℝ)) := by
    rw [Real.exp_le_exp]
    calc (n : ℝ) * (t i - t j) ≤ (n : ℝ) * (2 * ∑ k, |t k|) :=
          mul_le_mul_of_nonneg_left hdiff (Nat.cast_nonneg n)
      _ = (2 * ∑ k, |t k|) * (n : ℝ) := by ring
  rcases eq_or_ne i j with rfl | hij
  · -- diagonal entry: the exponential factor is `1` and `ρ ≤ ρ · e^{α n}`
    rw [show ((1 : Work.EKLContract.SL3) i i) = 1 from by simp]
    rw [sub_self, mul_zero, Real.exp_zero, one_mul]
    have hwii : |(w : Matrix (Fin 3) (Fin 3) ℝ) i i - 1| < ρ := by
      have h := hw i i
      rw [Matrix.one_apply_eq i] at h
      exact h
    have hle : (1 : ℝ) ≤ Real.exp ((2 * ∑ k, |t k|) * (n : ℝ)) := by
      rw [Real.one_le_exp_iff]
      exact mul_nonneg (by positivity) (Nat.cast_nonneg n)
    calc |(w : Matrix (Fin 3) (Fin 3) ℝ) i i - 1| < ρ := hwii
      _ ≤ ρ * Real.exp ((2 * ∑ k, |t k|) * (n : ℝ)) := by nlinarith [hρ.le, hle]
  · -- off-diagonal entry: multiply the `V ρ`-bound on `wᵢⱼ` by the exponential factor
    rw [show ((1 : Work.EKLContract.SL3) i j) = 0 from by simpa using Matrix.one_apply_ne hij,
      sub_zero]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hwij : |(w : Matrix (Fin 3) (Fin 3) ℝ) i j| < ρ := by
      have h := hw i j
      rw [Matrix.one_apply_ne hij, sub_zero] at h
      exact h
    calc Real.exp ((n:ℝ) * (t i - t j)) * |(w : Matrix (Fin 3) (Fin 3) ℝ) i j|
        < Real.exp ((n:ℝ) * (t i - t j)) * ρ :=
          mul_lt_mul_of_pos_left hwij (Real.exp_pos _)
      _ ≤ Real.exp ((2 * ∑ k, |t k|) * (n:ℝ)) * ρ :=
          mul_le_mul_of_nonneg_right hexpmono hρ.le
      _ = ρ * Real.exp ((2 * ∑ k, |t k|) * (n:ℝ)) := by ring

end Work.EKLC6Core
