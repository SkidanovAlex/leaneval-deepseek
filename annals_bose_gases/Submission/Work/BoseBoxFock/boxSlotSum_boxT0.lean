import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.BoseBoxFock.BombNExcDefs
import Submission.Work.BoseBoxFock.BoxFockDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.boxSlotSum_boxT0` — the first-quantised form of `boxT0 = 1 − |e₀⟩⟨e₀|`

The model's excited number operator is `nExc = dΓ m (boxT0 m)` with
`boxT0 = 1 − |e_vec 0⟩⟨e_vec 0|` (`Work.BoseBoxFock.nExc_eq_dGamma_boxT0`).  Under the model ↔ box
dictionary (`Work.BoseDict.bomb_dGamma_slot`), `dΓ m T` becomes the first-quantised slot sum
`Work.BoseDict.boxSlotSum e T Θ`.  This file evaluates that slot sum at `T = boxT0`:

    `boxSlotSum e boxT0 Θ = boxSlotSum e 1 Θ − Σ_j boxSlotOf e e₀ e₀ j Θ`,

which is the algebraic half of the `nExc = cnPlusC` row.  `boxSlotSum` is linear in its operator
argument and the rank-one operator `|e₀⟩⟨e₀|` is the corpus's already-analysed `proj0`
(`Work.BoseBoxFock.boxSlotSum_proj0`, `Work.BoseBoxFock.boxSlotOf_evec0_eq_uSlot`), so the
identity is pure finite-dimensional bookkeeping.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. Linearity of `boxSlotSum` in the one-particle operator -/

/-- `boxSlotSum` is additive in the one-particle operator: the coefficients of the defining
double sum split and `∑ (fᵢ − gᵢ) = ∑ fᵢ − ∑ gᵢ` (pointwise on `Xn d`). -/
theorem boxSlotSum_sub {m d : ℕ} (e : Fin m → Work.BoseDict.Sp → ℂ)
    (T1 T2 : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (Θ : Work.BoseDict.Xn d → ℂ) :
    Work.BoseDict.boxSlotSum e (T1 - T2) Θ
      = Work.BoseDict.boxSlotSum e T1 Θ - Work.BoseDict.boxSlotSum e T2 Θ := by
  funext x
  simp only [Work.BoseDict.boxSlotSum, Finset.sum_apply, Pi.sub_apply, LinearMap.sub_apply,
    sub_smul, Finset.sum_sub_distrib]

/-! ## 2. The rank-one piece `|e₀⟩⟨e₀| = proj0` -/

/-- The rank-one projection `|e_vec 0⟩⟨e_vec 0|` of the dictionary is the corpus's `proj0`. -/
theorem smulRight_proj_zero_evec_zero_eq_proj0 (m : ℕ) [NeZero m] :
    LinearMap.smulRight (LinearMap.proj (0 : Fin m) : (Fin m → ℝ) →ₗ[ℝ] ℝ)
        (Work.BoseB4.evec m 0)
      = proj0 m := by
  ext v i
  rfl

/-- The slot sum of the rank-one operator `|e₀⟩⟨e₀|` is exactly the sum of the slot projections
onto `etaOf e (evec 0) = e 0`. -/
theorem boxSlotSum_smulRight_proj0 {m d : ℕ} [NeZero m] (e : Fin m → Work.BoseDict.Sp → ℂ)
    (Θ : Work.BoseDict.Xn d → ℂ) :
    Work.BoseDict.boxSlotSum e
        (LinearMap.smulRight (LinearMap.proj (0 : Fin m) : (Fin m → ℝ) →ₗ[ℝ] ℝ)
          (Work.BoseB4.evec m 0)) Θ
      = ∑ j : Fin d,
          Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m 0) (Work.BoseB4.evec m 0) j Θ := by
  rw [smulRight_proj_zero_evec_zero_eq_proj0 m, boxSlotSum_proj0]
  funext x
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact (congrFun (boxSlotOf_evec0_eq_uSlot e j Θ) x).symm

/-! ## 3. The target identity -/

theorem boxSlotSum_boxT0 {m d : ℕ} [NeZero m] {e : Fin m → Work.BoseDict.Sp → ℂ}
    (Θ : Work.BoseDict.Xn d → ℂ) :
    Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ
      = Work.BoseDict.boxSlotSum e (1 : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) Θ
        - ∑ j : Fin d,
            Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m 0) (Work.BoseB4.evec m 0) j Θ := by
  have hT : Work.BoseBoxFock.boxT0 m
      = 1 - LinearMap.smulRight (LinearMap.proj (0 : Fin m) : (Fin m → ℝ) →ₗ[ℝ] ℝ)
            (Work.BoseB4.evec m 0) := rfl
  rw [hT, boxSlotSum_sub, boxSlotSum_smulRight_proj0]

end Work.BoseBoxFock
