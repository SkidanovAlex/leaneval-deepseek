/-
Orbit quadruples satisfy the Descartes equation (with positive sum and
coprime coordinates).  This lets us apply the χ₂ machinery to actual packing
quadruples.
-/
import Submission.Apollo.Defs
import Submission.Apollo.Mod24
import Mathlib.Tactic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
set_option autoImplicit false
open scoped Pointwise
open LocalGlobalApollonianCirclePackings

namespace Apollo

/-- The base quadruple satisfies the Descartes equation. -/
lemma q0v_descarates : (∑ i : Fin 4, q0v i) ^ 2 = 2 * ∑ i : Fin 4, (q0v i) ^ 2 := by
  decide

/-- An S-move preserves the Descartes equation. -/
lemma gen_smul_descarates (i : Fin 4) (v : Fin 4 → ℤ)
    (h : (∑ j : Fin 4, v j) ^ 2 = 2 * ∑ j : Fin 4, (v j) ^ 2) :
    (∑ j : Fin 4, (gen i • v) j) ^ 2 = 2 * ∑ j : Fin 4, ((gen i • v) j) ^ 2 := by
  let w : Fin 4 → ℤ := fun j => if j = i then 2 * (∑ k, if k = i then 0 else v k) - v i else v j
  have hw : gen i • v = w := by
    ext j
    rw [gen_smul_apply]
    by_cases hji : j = i <;> simp [w, hji] <;> ring
  rw [hw]
  rw [Fin.sum_univ_four] at h
  simp only [Fin.sum_univ_four] at h
  fin_cases i <;> simp [w, Fin.sum_univ_four] at h ⊢ <;> ring_nf at h ⊢ <;> nlinarith

/-- Every Descartes quadruple in the Apollonian orbit satisfies the Descartes
equation. -/
theorem apOrbit_descarates (v : Fin 4 → ℤ) (hv : v ∈ apOrbit) :
    (∑ i : Fin 4, v i) ^ 2 = 2 * ∑ i : Fin 4, (v i) ^ 2 := by
  refine of_closure_apply (P := fun w => (∑ j : Fin 4, w j) ^ 2 = 2 * ∑ j : Fin 4, (w j) ^ 2) ?hP ?hS v hv
  · exact q0v_descarates
  · intro i w hw
    exact gen_smul_descarates i w hw

end Apollo
