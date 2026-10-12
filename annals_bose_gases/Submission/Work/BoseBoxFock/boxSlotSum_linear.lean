import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.BoseDict.Defs3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.boxSlotSum_linear` — linearity of the box slot sum in the one-body operator

`Work.BoseDict.boxSlotSum e T Θ` is defined through the matrix elements `(T (evec l'))_l` of the
one-body operator `T`, hence is **linear in `T`**.  Only the homogeneity `boxSlotSum_smul_real` and
the subtraction `boxSlotSum_sub` were on disk; this module adds the general additivity and the
finite-sum form, which are what the block-III reduction of the FS `Q₂` row needs in order to write

    `Σ_{k : Lab N} boxSlotSum e (rankOne (f k)) Θ = boxSlotSum e (Σ_k rankOne (f k)) Θ`

(the left-hand side is the `(L₀+L₁)∘Σ_k a_k†a_k` row of `potPairRows`, and the operator
`Σ_k rankOne (f k) = S_N` is the one whose matrix bound `Work.BoseBoxFock.frameMat_le` controls).

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

open Work.BoseDict

/-- `boxSlotSum` is additive in the one-body operator. -/
theorem boxSlotSum_op_add {m d : ℕ} (e : Fin m → Sp → ℂ)
    (T T' : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (Θ : Xn d → ℂ) :
    boxSlotSum e (T + T') Θ = boxSlotSum e T Θ + boxSlotSum e T' Θ := by
  funext x
  simp only [boxSlotSum, Finset.sum_apply, Pi.add_apply, LinearMap.add_apply, add_smul,
    Finset.sum_add_distrib]

/-- `boxSlotSum` of a finite sum of one-body operators. -/
theorem boxSlotSum_op_sum {m d : ℕ} {ι : Type*} (e : Fin m → Sp → ℂ) (s : Finset ι)
    (T : ι → (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (Θ : Xn d → ℂ) :
    boxSlotSum e (∑ k ∈ s, T k) Θ = ∑ k ∈ s, boxSlotSum e (T k) Θ := by
  classical
  induction s using Finset.induction with
  | empty => simp [boxSlotSum]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, boxSlotSum_op_add, ih]

end Work.BoseBoxFock
