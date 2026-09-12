import Mathlib.NumberTheory.NumberField.House
import Lake.Toml
import Lake.Util.Message
import Lean
import Submission.Helpers
import Submission.Conjugates
import Submission.Induction
import Submission.Engine

namespace Submission

noncomputable section

open Submission.Conjugates
open Submission.Powers

/-- The analytic engine applied to the fixed field `K`: every element with
irreducible `pow2 (minpoly ℤ β)` satisfies the house bound. -/
private theorem engine (K : Type*) [Field K] [NumberField K] : Submission.Induction.EngineStatement K :=
  fun β hβ h0 hROU h2irr =>
    Submission.Engine.house_bound_of_pow2_irreducible β hβ h0 hROU h2irr

theorem dimitrov {K : Type*} [Field K] [NumberField K]
    (α : K)
    (α_int : IsIntegral ℤ α)
    (α_ne_zero : α ≠ 0)
    (α_not_rootOfUnity : ¬ IsOfFinOrder α) :
    (2 : ℝ) ^ (1 / (4 * (Finset.univ.image fun σ : K →+* ℂ ↦ (σ α).arg).card) : ℝ) ≤
      NumberField.house α := by
  classical
  have hb : Submission.Induction.Bound α :=
    Submission.Induction.dimitrov_of_engine (K := K) (engine (K := K)) α α_int α_ne_zero
      α_not_rootOfUnity
  rw [argSet_card α]
  exact hb

end

end Submission
