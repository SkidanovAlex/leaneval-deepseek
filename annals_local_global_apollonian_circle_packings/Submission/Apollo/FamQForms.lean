/-
Descartes-equation and quadratic-form facts for the orbit of the family
quadruple famQuad t (the analogues of QForms.qf_discriminant and
Chi2.descartes_fourterm for the family orbit).
-/
import Submission.Apollo.FamOrbit
import Submission.Apollo.QForms
import Submission.Apollo.Chi2
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

/-- the Descartes equation of a family-orbit quadruple, expanded at four
pairwise distinct indices. -/
theorem fam_descarates_fourterm (t : ℕ) (w : Fin 4 → ℤ) (hw : w ∈ orbitOf (famQuad t))
    {i j k l : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    (w i + w j + w k + w l) ^ 2 = 2 * ((w i) ^ 2 + (w j) ^ 2 + (w k) ^ 2 + (w l) ^ 2) := by
  have hD := famOrbit_desc t w hw
  have hcard : ({i, j, k, l} : Finset (Fin 4)).card = Fintype.card (Fin 4) := by
    rw [Fintype.card_fin]
    simp [hij, hik, hil, hjk, hjl, hkl]
  have huniv : ({i, j, k, l} : Finset (Fin 4)) = Finset.univ :=
    Finset.eq_univ_of_card _ hcard
  have hs1 : (∑ x ∈ ({i, j, k, l} : Finset (Fin 4)), w x) =
      w i + w j + w k + w l := by
    simp [hij, hik, hil, hjk, hjl, hkl]
    ring
  have hs2 : (∑ x ∈ ({i, j, k, l} : Finset (Fin 4)), (w x) ^ 2) =
      (w i) ^ 2 + (w j) ^ 2 + (w k) ^ 2 + (w l) ^ 2 := by
    simp [hij, hik, hil, hjk, hjl, hkl]
    ring
  rw [← huniv] at hD
  rw [hs1, hs2] at hD
  ring_nf at hD ⊢
  exact hD

/-- the discriminant of the form attached at (w,i) is -4 (w i)², for w in the
family orbit. -/
theorem fam_qf_discriminant (t : ℕ) (w : Fin 4 → ℤ) (hw : w ∈ orbitOf (famQuad t))
    (i : Fin 4) :
    (qfB w i) ^ 2 - 4 * (qfA w i) * (qfC w i) = -4 * (w i) ^ 2 := by
  let a := w i
  let b := w (i + 1)
  let c := w (i + 2)
  let d := w (i + 3)
  have hD := fam_descarates_fourterm t w hw
    (i := i) (j := i + 1) (k := i + 2) (l := i + 3)
    fin_ne_succ fin_ne_succ2 fin_ne_succ3 fin_succ_ne fin_succ2_ne fin_succ3_ne
  have hD' : (a + b + c + d) ^ 2 = 2 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
    simpa [a, b, c, d, add_assoc, add_comm, add_left_comm] using hD
  dsimp [qfA, qfB, qfC]
  change (a + b + c - d) ^ 2 - 4 * (a + b) * (a + c) = -4 * a ^ 2
  nlinarith [hD']

end Apollo
