import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.StrataFinsetDefs
import Submission.Work.BourgainPlan.IonescuWainger.khintchine_majorArc_real
import Submission.Work.BourgainPlan.IonescuWainger.tsum_sq_pow_le_sunflower

/-!
# Summability of the strata square function's `r`-th power

The strata analogue of `summable_powerset_rpow`: for a band-limited family `f : 𝕋 → ℓ²(ℤ)`, the
`r`-th power of the pointwise square function `Σ_{A ∈ binom(S,≤k)} ‖Σ_{α ∈ Σ_A} f_α(·)‖²` is
summable on `ℤ` (the finite sum of squared norms is `ℓ¹`, hence bounded, so its `r`-th power is
still `ℓ¹`).  This is the finiteness input of the `ENNReal`/`ofReal` bookkeeping in the
Khintchine inequality for the strata.
-/

open Finset MeasureTheory
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

/-- For `r ≥ 1`, the `r`-th power of `Σ_A ‖Σ_{α ∈ Σ_A} f_α‖²` (strata convention) is summable in
`x`. -/
theorem summable_powerset_rpow_strata {S : Finset ℕ} {f : Circle → ℤ → ℂ}
    (hf : ∀ δ, Memℓp (f δ) 2) (k r : ℕ) (hr : 1 ≤ r) :
    Summable fun x : ℤ => (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
      ‖∑ α ∈ sigmaStrataFinset A, f α x‖ ^ 2) ^ r := by
  have hw_mem : ∀ A, Memℓp (fun x => ∑ α ∈ sigmaStrataFinset A, f α x) 2 :=
    fun A => Memℓp.finsetSum (sigmaStrataFinset A) (fun α _ => hf α)
  have hsq : ∀ A, Summable (fun x => ‖∑ α ∈ sigmaStrataFinset A, f α x‖ ^ 2) :=
    fun A => summable_norm_sq_of_memℓp (hw_mem A)
  have hHsum : Summable (fun x => ∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
      ‖∑ α ∈ sigmaStrataFinset A, f α x‖ ^ 2) :=
    summable_sum (L := SummationFilter.unconditional ℤ)
      (f := fun A x => ‖∑ α ∈ sigmaStrataFinset A, f α x‖ ^ 2)
      (s := S.powerset.filter (fun A => A.card ≤ k)) (fun A _ => hsq A)
  set M : ℝ := max 1 (∑' x, ∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
      ‖∑ α ∈ sigmaStrataFinset A, f α x‖ ^ 2) with hM
  refine Summable.of_nonneg_of_le
    (f := fun x : ℤ => M ^ (r - 1) * (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
      ‖∑ α ∈ sigmaStrataFinset A, f α x‖ ^ 2)) (fun x => ?_) (fun x => ?_)
    (hHsum.mul_left (M ^ (r - 1)))
  · exact pow_nonneg (Finset.sum_nonneg (fun A _ => sq_nonneg _)) r
  · have hnn : 0 ≤ ∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
        ‖∑ α ∈ sigmaStrataFinset A, f α x‖ ^ 2 := Finset.sum_nonneg (fun A _ => sq_nonneg _)
    have hle : (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
        ‖∑ α ∈ sigmaStrataFinset A, f α x‖ ^ 2) ≤ M := by
      rw [hM]
      exact le_trans (Summable.le_tsum hHsum x
        (fun j _ => Finset.sum_nonneg (fun A _ => sq_nonneg _))) (le_max_right _ _)
    have hpow : (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
          ‖∑ α ∈ sigmaStrataFinset A, f α x‖ ^ 2) ^ r
        = (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
            ‖∑ α ∈ sigmaStrataFinset A, f α x‖ ^ 2) ^ (r - 1)
          * (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
              ‖∑ α ∈ sigmaStrataFinset A, f α x‖ ^ 2) := by
      conv_lhs => rw [show r = (r - 1) + 1 from (Nat.sub_add_cancel hr).symm]
      rw [pow_succ]
    calc (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
          ‖∑ α ∈ sigmaStrataFinset A, f α x‖ ^ 2) ^ r
        = (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
              ‖∑ α ∈ sigmaStrataFinset A, f α x‖ ^ 2) ^ (r - 1)
            * (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
                ‖∑ α ∈ sigmaStrataFinset A, f α x‖ ^ 2) := hpow
      _ ≤ M ^ (r - 1) * (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
            ‖∑ α ∈ sigmaStrataFinset A, f α x‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hnn hle (r - 1)) hnn

end Work.BourgainPlan.IonescuWainger
