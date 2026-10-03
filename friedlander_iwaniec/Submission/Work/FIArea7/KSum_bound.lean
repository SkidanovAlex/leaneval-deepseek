/-
# `Submission.Work.FIArea7.KSum_bound` — *FI* Proposition 22.1, the bound for the linear form `K(N)`

The arrow: the box sum `KLinear Rz w k chi = Σ∧_{z ∈ gBox Rz} ψ(z)[wz]` is decomposed into the
fibres `KInner Rz w k chi r` over the real part `r` (`Submission/Work/FIArea7/KSDefs.lean`), each
fibre is estimated by the Pólya–Vinogradov bound for the product of the two Jacobi characters
`(s | |r|)` and `(s - ωr | |w|²)` (`Work.FIArea7.KInner_bound_good`, built on
`Work.FIArea7.twoChar_pv_dilated` and `Work.FIArea7.jacobiSym_dilation`), the few `r` for which the
relevant Jacobi character is trivial are estimated trivially and counted by
`Work.FIArea7.card_bad_r_le`, and the resulting sums over `r` are evaluated by
`Work.FIArea7.sum_sqrt_Icc_le` and `Work.FIArea7.sum_inv_sqrt_Icc_le`.
-/
import Mathlib
import Submission.Work.FIArea7.Prop172
import Submission.Work.FIArea7.pv_weighted_jacobiSym
import Submission.Work.FIArea7.jksym_mul_rule
import Submission.Work.FIArea7.omega_rep
import Submission.Work.FIArea7.KSDefs
import Submission.Work.FIArea7.KInner_bound
import Submission.Work.FIArea7.KInner_bound_good
import Submission.Work.FIArea7.card_bad_r_le
import Submission.Work.FIArea7.sum_sqrt_Icc_le
import Submission.Work.FIArea7.sum_inv_sqrt_Icc_le
import Submission.Work.FIArea7.exists_omega

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `‖z‖ = √|z|²` for a Gaussian integer, read in `ℂ`. -/
lemma norm_toComplex_eq_sqrt (z : GaussianInt) :
    ‖(z : ℂ)‖ = Real.sqrt (((Work.FIPlan.gnorm z : ℕ)) : ℝ) := by
  have h2 : (((Work.FIPlan.gnorm z : ℕ)) : ℝ) = (z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2 := by
    have h3 : (Work.FIPlan.gnorm z : ℤ) = z.re ^ 2 + z.im ^ 2 := Work.FIArea7.norm_eq z
    have h4 : (((Work.FIPlan.gnorm z : ℕ)) : ℤ) = z.re ^ 2 + z.im ^ 2 := by
      rw [← h3]
    exact_mod_cast h4
  have h : ‖(z : ℂ)‖ ^ 2 = (((Work.FIPlan.gnorm z : ℕ)) : ℝ) := by
    rw [Complex.sq_norm, Complex.normSq_apply, h2]
    rw [show ((z : ℂ)).re = (z.re : ℝ) from (GaussianInt.intCast_re z).symm,
      show ((z : ℂ)).im = (z.im : ℝ) from (GaussianInt.intCast_im z).symm]
    ring
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

lemma odd_ne_zero' {r : ℤ} (h : Odd r) : r ≠ 0 := by
  intro h0
  rw [h0] at h
  obtain ⟨k, hk⟩ := h
  omega

/-- A fibre with even (or zero) real part vanishes: the primary condition forces `z.re` odd. -/
lemma KInner_eq_zero_of_not_odd {Rz : ℤ} {w : GaussianInt} {k : ℤ} {chi : GaussianInt → ℂ} {r : ℤ}
    (hr : ¬ Odd r) : KInner Rz w k chi r = 0 := by
  rw [KInner]
  apply Finset.sum_eq_zero
  intro s _
  rw [if_neg]
  intro hz
  exact hr hz.1

/-- The trivial fibre bound: at most one term per `s` in the box. -/
lemma KInner_le_card (Rz : ℤ) (w : GaussianInt) (k : ℤ) (chi : GaussianInt → ℂ) (r : ℤ)
    (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) :
    ‖KInner Rz w k chi r‖ ≤ ((((2 * Rz + 1).toNat : ℕ)) : ℝ) := by
  have h1 : ‖KInner Rz w k chi r‖
      ≤ ∑ s ∈ Finset.Icc (-Rz) Rz, (if Work.FIPlan.IsPrimary (⟨r, s⟩ : GaussianInt) then (1 : ℝ) else 0) := by
    rw [KInner]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun s _ => ?_))
    by_cases hz : Work.FIPlan.IsPrimary (⟨r, s⟩ : GaussianInt)
    · rw [if_pos hz, if_pos hz, norm_mul]
      calc ‖grossenChar chi k (⟨r, s⟩ : GaussianInt)‖ * ‖JKSym (w * (⟨r, s⟩ : GaussianInt))‖
          ≤ 1 * 1 := mul_le_mul (norm_grossenChar_le_one chi k hchi _) (norm_JKSym_le_one _)
              (norm_nonneg _) (by norm_num)
        _ = 1 := by ring
    · rw [if_neg hz, if_neg hz, norm_zero]
  refine h1.trans ?_
  calc ∑ s ∈ Finset.Icc (-Rz) Rz,
        (if Work.FIPlan.IsPrimary (⟨r, s⟩ : GaussianInt) then (1 : ℝ) else 0)
      ≤ ∑ _s ∈ Finset.Icc (-Rz) Rz, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro s _
        by_cases hz : Work.FIPlan.IsPrimary (⟨r, s⟩ : GaussianInt) <;> simp [hz]
    _ = ((Finset.Icc (-Rz) Rz).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = ((((2 * Rz + 1).toNat : ℕ)) : ℝ) := by
        congr 1
        rw [Int.card_Icc]
        congr 1
        ring

end

end Work.FIArea7
