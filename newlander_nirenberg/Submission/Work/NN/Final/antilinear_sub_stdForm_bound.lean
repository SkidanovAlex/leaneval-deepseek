import Mathlib
import Submission.Work.NN.Final.Defs
import Submission.Work.NN.Final.antilinear_defs
import Submission.Work.NN.Final.relations_and_bound

namespace Work.NN.Final

open Work.NN.Core

noncomputable section

variable {n : ℕ}

/-- **The final estimate.**  `L` is `(Jstd + B)`-antilinear with `‖B‖ ≤ ε ≤ 1`; assuming the core
estimate on the coefficients (`hcore`), the defect of `L` from the standard form is bounded by
`12 ε (∑ k, ‖L (e_k)‖) (‖w‖ + 1)`. -/
lemma final_estimate (L : Cn n →L[ℝ] ℂ) (B : Cn n →L[ℝ] Cn n) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hB : ‖B‖ ≤ ε)
    (hc : ∀ w, L (Complex.I • w + B w) = -Complex.I * L w)
    (hcore : (∑ k, ‖avec L B k‖) ≤ 6 * ε * ∑ k, ‖hvec L B k‖) (w : Cn n) :
    ‖L w - ∑ k, L (Pi.single k (1 : ℂ)) * star (w k)‖
      ≤ 12 * ε * (∑ k, ‖L (Pi.single k (1 : ℂ))‖) * (‖w‖ + 1) := by
  have h1 : (∑ k, L (Pi.single k (1 : ℂ)) * star (w k))
      = ∑ k, ((avec L B k + bvec L B k) / 2) * star (w k) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [cvec_eq (L := L) (B := B) hc k]
  have h2 : ‖L w - ∑ k, ((avec L B k + bvec L B k) / 2) * star (w k)‖
      ≤ (∑ k, ‖avec L B k‖) * ‖w‖ := norm_stdForm_sub (L := L) (B := B) hc w
  have h3 : (∑ k, ‖hvec L B k‖) = 2 * ∑ k, ‖L (Pi.single k (1 : ℂ))‖ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show hvec L B k = 2 * L (Pi.single k (1 : ℂ)) from ?_]
    · rw [norm_mul, Complex.norm_ofNat]
    · simp only [hvec, avec, bvec, psiOf, lamOf]
      rw [cvec_eq (L := L) (B := B) hc k]
      ring
  have h4 : (∑ k, ‖avec L B k‖) * ‖w‖ ≤ 12 * ε * (∑ k, ‖L (Pi.single k (1 : ℂ))‖) * (‖w‖ + 1) := by
    have hsum_nn : 0 ≤ ∑ k, ‖L (Pi.single k (1 : ℂ))‖ := Finset.sum_nonneg fun k _ => norm_nonneg _
    have hcore' : (∑ k, ‖avec L B k‖) ≤ 12 * ε * ∑ k, ‖L (Pi.single k (1 : ℂ))‖ := by
      rw [h3] at hcore
      linarith
    calc (∑ k, ‖avec L B k‖) * ‖w‖
        ≤ (12 * ε * ∑ k, ‖L (Pi.single k (1 : ℂ))‖) * ‖w‖ := by
          refine mul_le_mul_of_nonneg_right hcore' (norm_nonneg _)
      _ ≤ (12 * ε * ∑ k, ‖L (Pi.single k (1 : ℂ))‖) * (‖w‖ + 1) := by
          refine mul_le_mul_of_nonneg_left (by linarith [norm_nonneg w]) ?_
          have : (0:ℝ) ≤ 12 * ε := by linarith
          exact mul_nonneg this hsum_nn
  rw [h1]
  exact h2.trans h4

/-- **The requested estimate.**  For every `n` there is a constant `C > 0` such that for every
real-linear perturbation `A` of the standard complex structure with `‖A z‖ ≤ ε ≤ 1` and every
real-linear `(Jstd + A z)`-antilinear form `α z`, the deviation of `α z` from the standard
`(0,1)`-form with the same coefficients on the basis is bounded by
`C ε (∑ m, ‖α z (e_m)‖) (‖w‖ + 1)`. -/
theorem antilinear_sub_stdForm_bound {n : ℕ} : ∃ C : ℝ, 0 < C ∧ ∀ (A : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ)) (ε : ℝ), 0 ≤ ε → ε ≤ 1 → (∀ z, ‖A z‖ ≤ ε) → ∀ (α : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] ℂ) (z : Fin n → ℂ), (∀ w : Fin n → ℂ, α z ((Work.NN.Core.JstdCn n + A) z w) = -Complex.I * α z w) → ∀ w : Fin n → ℂ, ‖α z w - Work.NN.Core.stdForm (fun m _ => α z (Pi.single m 1)) z w‖ ≤ C * ε * (∑ m, ‖α z (Pi.single m 1)‖) * (‖w‖ + 1) := by
  refine ⟨12, by norm_num, ?_⟩
  intro A ε hε0 hε1 hA α z hα w
  have hc : ∀ v : Cn n, α z (Complex.I • v + A z v) = -Complex.I * α z v := by
    intro v
    have h := hα v
    simpa [Pi.add_apply, ContinuousLinearMap.add_apply, Work.NN.Core.JstdCn_apply] using h
  have hcore := relations_and_bound (α z) (A z) ε hε0 hε1 (hA z) hc
  have h := final_estimate (α z) (A z) ε hε0 hε1 (hA z) hc hcore w
  have hstd : Work.NN.Core.stdForm (fun m _ => α z (Pi.single m (1 : ℂ))) z w
      = ∑ k, α z (Pi.single k (1 : ℂ)) * star (w k) := by
    rw [Work.NN.Core.stdForm_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.conjCLE_apply, Complex.star_def]
  rw [hstd]
  exact h

end

end Work.NN.Final
