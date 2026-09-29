import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.classZ_defs
import Submission.Work.A14D.local_A14
import Submission.Work.A14D.Dd_ne_zero
import Submission.Work.C17.order3_class_injective

namespace Work.A14D

open Polynomial
open scoped BigOperators

theorem classZ_injective (p : Fin 4 → Polynomial ℚ)
    (h : (∑ k : Fin 4, (p k).eval₂ (algebraMap ℚ (RatFunc ℚ)) yQs * (clsZ k).1) = 0 ∧
         (∑ k : Fin 4, (p k).eval₂ (algebraMap ℚ (RatFunc ℚ)) yQs * (clsZ k).2) = 0) : p = 0 := by
  let Q : Fin 4 → RatFunc ℚ := fun k => (p k).eval₂ (algebraMap ℚ (RatFunc ℚ)) yQs
  have hQeq : ∀ k, Q k = (p k).eval₂ (algebraMap ℚ (RatFunc ℚ)) yQs := fun k => rfl
  have hsum1 : ∑ k : Fin 4, Q k * (clsZ k).1 = 0 := h.1
  have hsum2 : ∑ k : Fin 4, Q k * (clsZ k).2 = 0 := h.2
  rw [Fin.sum_univ_four] at hsum1 hsum2
  rw [clsZ_zero_fst, clsZ_one_fst, clsZ_two_fst, clsZ_three_fst] at hsum1
  rw [clsZ_zero_snd, clsZ_one_snd, clsZ_two_snd, clsZ_three_snd] at hsum2
  simp only [mul_one, mul_zero, zero_mul, add_zero] at hsum1 hsum2
  have hrne : rhos ≠ 0 := (Work.C17.lead2_rhoQ).to_LeadAt.ne_zero
  have hQ0 : Q 0 = -(Q 2 * u2 + Q 3 * u3) := by linear_combination hsum1
  have hQ1 : Q 1 = -(Q 2 * w2 + Q 3 * w3) := by
    have hv : Q 1 * rhos + Q 2 * v2 + Q 3 * v3 = 0 := by linear_combination hsum2
    rw [v2, v3] at hv
    have hfac : rhos * (Q 1 + Q 2 * w2 + Q 3 * w3) = 0 := by linear_combination hv
    rcases mul_eq_zero.mp hfac with h0 | h0
    · exact absurd h0 hrne
    · linear_combination h0
  have hfix : ∀ k, Work.C17.sigmaQ (Q k) = Q k := fun k => Work.C17.sigmaQ_eval₂ (p k)
  have heq1 : Q 2 * Z2 + Q 3 * Z3 = 0 := by
    have hs : Work.C17.sigmaQ (Q 0) = Work.C17.sigmaQ (-(Q 2 * u2 + Q 3 * u3)) := by rw [hQ0]
    rw [hfix 0, map_neg, map_add, map_mul, map_mul, hfix 2, hfix 3] at hs
    rw [hQ0] at hs
    have hA' : Q 2 * u2 + Q 3 * u3
        = Q 2 * Work.C17.sigmaQ u2 + Q 3 * Work.C17.sigmaQ u3 := neg_inj.mp hs
    rw [Z2, Z3, mul_sub, mul_sub]
    linear_combination hA'
  have heq2 : Q 2 * Y2 + Q 3 * Y3 = 0 := by
    have hs : Work.C17.sigmaQ (Q 1) = Work.C17.sigmaQ (-(Q 2 * w2 + Q 3 * w3)) := by rw [hQ1]
    rw [hfix 1, map_neg, map_add, map_mul, map_mul, hfix 2, hfix 3] at hs
    rw [hQ1] at hs
    have hA' : Q 2 * w2 + Q 3 * w3
        = Q 2 * Work.C17.sigmaQ w2 + Q 3 * Work.C17.sigmaQ w3 := neg_inj.mp hs
    rw [Y2, Y3, mul_sub, mul_sub]
    linear_combination hA'
  have hdet : Dd ≠ 0 :=
    Dd_ne_zero local_A14.1 local_A14.2.1 local_A14.2.2.1 local_A14.2.2.2
  have hQ2 : Q 2 = 0 := by
    have h1' := congrArg (fun x => Y3 * x) heq1
    have h2' := congrArg (fun x => Z3 * x) heq2
    rw [mul_zero] at h1' h2'
    have hcomb : Q 2 * Dd = 0 := by rw [Dd]; linear_combination h1' - h2'
    exact (mul_eq_zero.mp hcomb).resolve_right hdet
  have hQ3 : Q 3 = 0 := by
    have h1' := congrArg (fun x => Y2 * x) heq1
    have h2' := congrArg (fun x => Z2 * x) heq2
    rw [mul_zero] at h1' h2'
    have hcomb : Q 3 * Dd = 0 := by rw [Dd]; linear_combination h2' - h1'
    exact (mul_eq_zero.mp hcomb).resolve_right hdet
  have hQ0z : Q 0 = 0 := by rw [hQ0, hQ2, hQ3, zero_mul, zero_mul, add_zero, neg_zero]
  have hQ1z : Q 1 = 0 := by rw [hQ1, hQ2, hQ3, zero_mul, zero_mul, add_zero, neg_zero]
  funext k
  have hk : Q k = 0 := by fin_cases k <;> assumption
  have hk' : (p k).eval₂ (algebraMap ℚ (RatFunc ℚ)) yQs = 0 := by rw [← hQeq k]; exact hk
  exact Work.C17.eval₂_yQ_eq_zero (P := p k) hk'

end Work.A14D
