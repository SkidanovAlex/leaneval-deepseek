import Mathlib
import Submission.Work.EKLContract.Lemmas.isHoro_Uij
import Submission.Work.EKLContract.Interfaces

/-!
# Distinct root subgroups `U_ij` intersect trivially

`U_ij = {u_ij(s) = 1 + sE_ij}` is the root subgroup of `SL₃(ℝ)` attached to the root
`e_i - e_j`.  Two *distinct* roots give subgroups meeting only in the identity:

`∀ g, g ∈ U_ij → g ∈ U_kl → g = 1` whenever `i ≠ j`, `k ≠ l` and `(i,j) ≠ (k,l)`.

The proof is the elementary computation alluded to everywhere in the EKL development:
via `horoUij_mem_iff`, elements of `U_ij` are `u_ij(s) = 1 + sE_ij` and elements of `U_kl`
are `u_kl(t) = 1 + tE_kl`.  Comparing the single matrix entry `(i,j)` of the two
expressions: the `(i,j)`-entry of `u_ij(s)` is `s`, while the `(i,j)`-entry of `u_kl(t)` is
`0`, because `k = i ∧ l = j` would force `(i,j) = (k,l)`.  Hence `s = 0` and `g = u_ij(0) = 1`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false
set_option warn.classDefReducibility false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLC6Core

namespace UijAux

open Work.EKLContract

/-- The `(i,j)`-entry of `u_ij(s) = 1 + sE_ij` is `s`. -/
theorem uij_entry_self {i j : Fin 3} (hij : i ≠ j) (s : ℝ) :
    toMat (uij hij s) i j = s := by
  rw [Work.EKLContract.Lemmas.horoUij_toMat hij s, Matrix.add_apply, Matrix.single_apply,
    if_pos ⟨rfl, rfl⟩, Matrix.one_apply_ne hij, zero_add]

/-- Any entry of `u_ij(s) = 1 + sE_ij` other than `(i,j)` agrees with the identity matrix. -/
theorem uij_entry_other {i j k l : Fin 3} (hij : i ≠ j) (h : ¬(i = k ∧ j = l)) (s : ℝ) :
    toMat (uij hij s) k l = (1 : Matrix (Fin 3) (Fin 3) ℝ) k l := by
  rw [Work.EKLContract.Lemmas.horoUij_toMat hij s, Matrix.add_apply, Matrix.single_apply,
    if_neg h, add_zero]

end UijAux

open UijAux

theorem disjoint_Uij {i j k l : Fin 3} (hij : i ≠ j) (hkl : k ≠ l)
    (hne : (i, j) ≠ (k, l)) :
    ∀ g : Work.EKLContract.SL3,
      g ∈ Work.EKLContract.Uij hij → g ∈ Work.EKLContract.Uij hkl → g = 1 := by
  intro g hg1 hg2
  obtain ⟨s, hs⟩ := (Work.EKLContract.Lemmas.horoUij_mem_iff hij g).mp hg1
  obtain ⟨t, ht⟩ := (Work.EKLContract.Lemmas.horoUij_mem_iff hkl g).mp hg2
  -- `hs : uij hij s = g`; work with `g` replaced by the explicit matrix.
  subst hs
  -- `(k,l) ≠ (i,j)` as an assumption about the indices.
  have hklne : ¬(k = i ∧ l = j) := by
    rintro ⟨rfl, rfl⟩
    exact hne rfl
  -- Compare the `(i,j)`-entry of the two expressions for `g`.
  have key : Work.EKLContract.toMat (Work.EKLContract.uij hij s) i j
      = Work.EKLContract.toMat (Work.EKLContract.uij hkl t) i j := by rw [ht]
  rw [uij_entry_self hij s, uij_entry_other hkl hklne t, Matrix.one_apply_ne hij] at key
  rw [key]
  exact Work.EKLContract.Lemmas.horoUij_zero hij

end Work.EKLC6Core
