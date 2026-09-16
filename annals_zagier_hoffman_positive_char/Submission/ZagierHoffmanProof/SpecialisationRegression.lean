import Submission.ZagierHoffmanProof.Specialisation
import Submission.ZagierHoffmanProof.LSeriesRegression
import Submission.ZagierHoffmanProof.MZPropertyRegression
import Submission.Commons.FieldTheory.RatFunc.charP_completionAtInfty

/-!
# Regression checks: Step 2 (specialisation) of the paper

Concrete instantiations over `K = F(t)_∞`, `θ = X`, `F = ZMod 2` of `specialise_sum_div`,
`step2_specialisation_period` and `lseriesWeight`.
-/

set_option autoImplicit false
open Polynomial RatFunc
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

attribute [local instance 100] Classical.decEq
attribute [local instance] Commons.FieldTheory.RatFunc.charP_completionAtInfty

noncomputable section

/-- The field `K = F₂(t)_∞`. -/
abbrev K2 := RatFunc.CompletionAtInfty (ZMod 2)
/-- The element `θ = X ∈ K`. -/
abbrev th2 : K2 := thetaOf (ZMod 2)
/-- The small period datum `θ⁻¹Ω̃`. -/
abbrev omg2 : PowerSeries K2 := PowerSeries.C (th2⁻¹) * atOmega 2 th2
/-- The tuple `(1, θ⁻¹)` of `L`-series data. -/
abbrev L1 : List (ℕ × PowerSeries K2) := [(1, PowerSeries.C (th2⁻¹))]

/-- The weight of the tuple `(1,θ⁻¹)` is `1`. -/
example : lseriesWeight L1 = 1 := rfl

/-- `specialise_sum_div` over `F₂`. -/
example (P Q : Polynomial K2) (S : PowerSeries K2) (hS : SuperEntire S) (c : K2)
    (hQ : Q.eval c ≠ 0) (h : (((P * 1 : Polynomial K2)) : PowerSeries K2) * S = 0) :
    (P.eval c / Q.eval c) * evalSeries S c = 0 := by
  have h' := specialise_sum_div (s := (Finset.univ : Finset Unit))
    (P := fun _ => P) (Q := fun _ => Q) (S := fun _ => S) c
    (by intro i _; exact hS) (by intro i _; exact hQ) (by simpa using h)
  simpa using h'

/-- **Step 2 on the empty relation** (a vacuity check of the statement). -/
example : ∑ k ∈ ((∅ : Finset Unit).filter (fun _ => 0 = 0)),
      (0 : K2) = 0 :=
  step2_specialisation_period (μ := 0) 2 th2 1 (by norm_num) (v_thetaOf (ZMod 2)) (by norm_num)
    (by simp : Valued.v (0 : K2) ≤ WithZero.exp (-1)) (∅ : Finset Unit) (fun _ => L1)
    (by intro k hk; exact (Finset.notMem_empty k hk).elim)
    (by intro k hk; exact (Finset.notMem_empty k hk).elim)
    (by intro k hk; exact (Finset.notMem_empty k hk).elim)
    (by intro k hk; exact (Finset.notMem_empty k hk).elim)
    (fun _ => 0) (fun _ => 0) 0 (by intro k hk; exact (Finset.notMem_empty k hk).elim)
    (j := 1) (by norm_num) (by intro k hk; exact (Finset.notMem_empty k hk).elim) (by simp)

end

end ZagierHoffmanPositiveChar
