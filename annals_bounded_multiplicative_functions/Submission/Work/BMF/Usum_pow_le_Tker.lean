import Mathlib
import Submission.Work.BMF.vkford51_defs
import Submission.Work.BMF.Uspt.base
import Submission.Work.BMF.Uspt.Tsum_le_Tker
import Submission.Work.BMF.Uspt.Yfun_pow_eq
import Submission.Work.BMF.Uspt.sum_ncount_sq_eq_J
import Submission.Work.BMF.Uspt.norm_sum_weighted_pow_le
import Submission.Work.BMF.Uspt.exists_eps_phase

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `‖Usum‖^{2rs}` is dominated by the kernel-weighted `2s`-th moment

This is Ford's display (5.3) of the proof of Lemma 5.1 (*Vinogradov's integral and bounds for
the Riemann zeta function*, Proc. LMS 85 (2002)), in the form needed for the extraction
`Work.BMF.vkford_lemma51`.

Writing `U = Σ_{a≤M₁} Σ_{b≤M₂} e(Σ_j γ_j (ab)^{j+1})` and `Y_b = Σ_{a≤M₁} e(Σ_j γ_j (ab)^{j+1})`,
Hölder's inequality gives `‖U‖^r ≤ M₂^{r-1} Σ_b ‖Y_b‖^r`; choosing the phases `ε_b` so that
`ε_b Y_b^r = ‖Y_b‖^r`, expanding the `r`-th powers and grouping the tuples `a : Fin r → [1,M₁]`
by their power-sum vector `psVec` gives

  `Σ_b ε_b Y_b^r = Σ_{c ∈ Cbox} ncount r k M₁ c · Xsum k M₂ γ ε c`,

and two further inequalities (a weighted power mean and Cauchy–Schwarz) bound this by
`(M₁^r)^{2s-2} · J_{r,k}(M₁) · Tsum`, where `Σ_c ncount = M₁^r` and `Σ_c ncount² = J_{r,k}(M₁)`.
Finally `Tsum ≤ Tker` (the kernel `kern` dominates `1` on the box and is nonnegative elsewhere),
which is exactly the right-hand side of the statement.

The five ingredients above are proved in the modules `Uspt/Yfun_pow_eq`, `Uspt/sum_ncount_sq_eq_J`,
`Uspt/norm_sum_weighted_pow_le`, `Uspt/Tsum_le_Tker` and `Uspt/exists_eps_phase`; the elementary
facts about `eZ`, `psVec`, `ncount` and the fiberwise regrouping used here are in `Uspt/base`.
-/

namespace Work.BMF

open Finset
open scoped BigOperators

noncomputable section

lemma Uspt_norm_ofReal_cast (x : ℝ) : ‖(x : ℂ)‖ = |x| := by
  have h : ‖(x : ℂ)‖ ^ 2 = x ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_ofReal, sq]
  rw [← Real.sqrt_sq (norm_nonneg (x : ℂ)), h, Real.sqrt_sq_eq_abs]

lemma Uspt_Usum_eq_sum_Yfun (k M₁ M₂ : ℕ) (γ : Fin k → ℝ) :
    Work.BMF.Usum k M₁ M₂ γ = ∑ b ∈ Finset.Icc 1 M₂, Work.BMF.Yfun k M₁ γ b := by
  unfold Work.BMF.Usum Work.BMF.Yfun
  rw [Finset.sum_comm]


theorem Usum_pow_le_Tker (k r s M₁ M₂ : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂)
    (γ : Fin k → ℝ) :
    ∃ ε : ℕ → ℂ, (∀ b, ‖ε b‖ ≤ 1) ∧
      ‖Usum k M₁ M₂ γ‖ ^ (2 * r * s)
        ≤ (M₂ : ℝ) ^ (2 * r * s - 2 * s) * (M₁ : ℝ) ^ (r * (2 * s - 2))
            * LeanEval.NumberTheory.VinogradovMeanValue.J r k M₁ * Tker r s M₁ M₂ k γ ε := by

  obtain ⟨ε, hε1, hε2⟩ := Uspt.exists_eps_phase k r M₁ M₂ hr γ
  refine ⟨ε, hε1, ?_⟩
  set Sr : ℝ := ∑ b ∈ Finset.Icc 1 M₂, ‖Work.BMF.Yfun k M₁ γ b‖ ^ r with hSr
  set A : ℂ := ∑ c ∈ Work.BMF.Cbox r M₁ k,
      (Work.BMF.ncount r k M₁ c : ℂ) * Work.BMF.Xsum k M₂ γ ε c with hA
  set Jv : ℝ := LeanEval.NumberTheory.VinogradovMeanValue.J r k M₁ with hJv
  set T : ℝ := Work.BMF.Tsum r s M₁ M₂ k γ ε with hT
  set Kk : ℝ := Work.BMF.Tker r s M₁ M₂ k γ ε with hKk
  have hJnn : 0 ≤ Jv := by rw [hJv]; exact Nat.cast_nonneg _
  -- step 1 : `‖U‖^r ≤ M₂^(r-1) · Sr`
  have hU : ‖Work.BMF.Usum k M₁ M₂ γ‖ ^ r ≤ (M₂ : ℝ) ^ (r - 1) * Sr := by
    rw [hSr, Uspt_Usum_eq_sum_Yfun]
    calc ‖∑ b ∈ Finset.Icc 1 M₂, Work.BMF.Yfun k M₁ γ b‖ ^ r
        ≤ (∑ b ∈ Finset.Icc 1 M₂, ‖Work.BMF.Yfun k M₁ γ b‖) ^ r :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) r
      _ ≤ ((Finset.Icc 1 M₂).card : ℝ) ^ (r - 1)
            * ∑ b ∈ Finset.Icc 1 M₂, ‖Work.BMF.Yfun k M₁ γ b‖ ^ r := by
          have h := pow_sum_le_card_mul_sum_pow (s := Finset.Icc 1 M₂)
            (f := fun b => ‖Work.BMF.Yfun k M₁ γ b‖) (fun b _ => norm_nonneg _) (r - 1)
          simpa [Nat.sub_add_cancel hr] using h
      _ = (M₂ : ℝ) ^ (r - 1) * ∑ b ∈ Finset.Icc 1 M₂, ‖Work.BMF.Yfun k M₁ γ b‖ ^ r := by
          have hc : ((Finset.Icc 1 M₂).card : ℝ) = (M₂ : ℝ) := by simp
          rw [hc]
  -- step 2 : the sum `∑_b ε_b Y_b^r` is `A`, and `‖A‖ = Sr`
  have hAeq : (∑ b ∈ Finset.Icc 1 M₂, ε b * (Work.BMF.Yfun k M₁ γ b) ^ r) = A := by
    rw [hA, Uspt.sum_ncount_mul hr hM₁ (fun c => Work.BMF.Xsum k M₂ γ ε c)]
    simp only [Uspt.Yfun_pow_eq k r M₁ hr hM₁ γ, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Work.BMF.Xsum]
  have hcast : (∑ b ∈ Finset.Icc 1 M₂, ε b * (Work.BMF.Yfun k M₁ γ b) ^ r)
      = ((∑ b ∈ Finset.Icc 1 M₂, ‖Work.BMF.Yfun k M₁ γ b‖ ^ r : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun b hb => hε2 b hb)
  have hSrnn : 0 ≤ Sr := by
    rw [hSr]
    exact Finset.sum_nonneg (fun b _ => pow_nonneg (norm_nonneg _) _)
  have hnormA : ‖A‖ = Sr := by
    have hA' : A = ((Sr : ℝ) : ℂ) := by rw [← hAeq, hcast, ← hSr]
    rw [hA', Uspt_norm_ofReal_cast, abs_of_nonneg hSrnn]
  -- step 3 : the analytic inequality on the box
  have h4' : ‖A‖ ^ (2 * s) ≤ ((M₁ : ℝ) ^ r) ^ (2 * s - 2) * Jv * T := by
    rw [hA, hT, hJv]
    have h := Uspt.norm_sum_weighted_pow_le (s := s) hs (t := Work.BMF.Cbox r M₁ k)
      (n := Work.BMF.ncount r k M₁) (y := Work.BMF.Xsum k M₂ γ ε)
    have hs1 : (∑ c ∈ Work.BMF.Cbox r M₁ k, (Work.BMF.ncount r k M₁ c : ℝ)) = (M₁ : ℝ) ^ r := by
      rw [← Nat.cast_sum, Uspt.sum_ncount_eq hr hM₁, Nat.cast_pow]
    have hs2 : (∑ c ∈ Work.BMF.Cbox r M₁ k, ((Work.BMF.ncount r k M₁ c : ℝ)) ^ 2)
        = LeanEval.NumberTheory.VinogradovMeanValue.J r k M₁ := Uspt.sum_ncount_sq_eq_J r k M₁ hr hM₁
    rw [hs1, hs2] at h
    simpa [Work.BMF.Tsum] using h
  -- step 4 : exponent bookkeeping and `Tsum ≤ Tker`
  have hTK : T ≤ Kk := Uspt.Tsum_le_Tker r s M₁ M₂ k hr hs hM₁ hM₂ γ ε
  have hfac : 0 ≤ (M₂ : ℝ) ^ (2 * r * s - 2 * s) * (M₁ : ℝ) ^ (r * (2 * s - 2)) * Jv :=
    mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (Nat.cast_nonneg _) _)) hJnn
  have hexp1 : r * (2 * s) = 2 * r * s := by ring
  have hexp2 : (r - 1) * (2 * s) = 2 * r * s - 2 * s := by
    rw [Nat.sub_mul, one_mul, hexp1]
  have hmain : ‖Work.BMF.Usum k M₁ M₂ γ‖ ^ (2 * r * s)
      ≤ (M₂ : ℝ) ^ (2 * r * s - 2 * s) * (M₁ : ℝ) ^ (r * (2 * s - 2)) * Jv * T := by
    rw [show ‖Work.BMF.Usum k M₁ M₂ γ‖ ^ (2 * r * s)
        = (‖Work.BMF.Usum k M₁ M₂ γ‖ ^ r) ^ (2 * s) by
      rw [← pow_mul]; congr 1; ring]
    calc (‖Work.BMF.Usum k M₁ M₂ γ‖ ^ r) ^ (2 * s)
        ≤ ((M₂ : ℝ) ^ (r - 1) * Sr) ^ (2 * s) :=
          pow_le_pow_left₀ (pow_nonneg (norm_nonneg _) _) hU (2 * s)
      _ = ((M₂ : ℝ) ^ (r - 1)) ^ (2 * s) * Sr ^ (2 * s) := by rw [mul_pow]
      _ = (M₂ : ℝ) ^ ((r - 1) * (2 * s)) * ‖A‖ ^ (2 * s) := by rw [← pow_mul, ← hnormA]
      _ ≤ (M₂ : ℝ) ^ ((r - 1) * (2 * s)) * (((M₁ : ℝ) ^ r) ^ (2 * s - 2) * Jv * T) :=
          mul_le_mul_of_nonneg_left h4' (pow_nonneg (Nat.cast_nonneg _) _)
      _ = (M₂ : ℝ) ^ ((r - 1) * (2 * s)) * (M₁ : ℝ) ^ (r * (2 * s - 2)) * Jv * T := by
          rw [← pow_mul]; ring
      _ = (M₂ : ℝ) ^ (2 * r * s - 2 * s) * (M₁ : ℝ) ^ (r * (2 * s - 2)) * Jv * T := by
          rw [hexp2]
  calc ‖Work.BMF.Usum k M₁ M₂ γ‖ ^ (2 * r * s)
      ≤ (M₂ : ℝ) ^ (2 * r * s - 2 * s) * (M₁ : ℝ) ^ (r * (2 * s - 2)) * Jv * T := hmain
    _ ≤ (M₂ : ℝ) ^ (2 * r * s - 2 * s) * (M₁ : ℝ) ^ (r * (2 * s - 2)) * Jv * Kk :=
        mul_le_mul_of_nonneg_left hTK hfac
    _ = (M₂ : ℝ) ^ (2 * r * s - 2 * s) * (M₁ : ℝ) ^ (r * (2 * s - 2))
          * LeanEval.NumberTheory.VinogradovMeanValue.J r k M₁ * Work.BMF.Tker r s M₁ M₂ k γ ε := by
        rw [hKk, hJv]

end

end Work.BMF
