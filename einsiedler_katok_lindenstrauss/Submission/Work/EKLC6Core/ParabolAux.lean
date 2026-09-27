import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.mem_uminus_of_entry_form
import Submission.Work.EKLC6Core.uminus_entry_zero

/-!
# `EKLC6Core.ParabolAux` — auxiliary lemmas for the parabolic decomposition

The target lemma `Work.EKLC6Core.parabol_eq_centralizer_mul_uminus` states that the
*parabolic* `P_t = {v : v_{ij} = 0 whenever t i > t j}` of the diagonal flow `aDiag t`
factorises as

  `P_t = C(aDiag t) · Uminus t`,   `v = c · u`,

where `Uminus t = ⨆_{t i < t j} Uij` is the contracted (stable horospherical) subgroup and
`C(aDiag t)` the centraliser of `aDiag t`.

This module collects the two ingredients that are shared by all the order patterns of `t`:

* `aDiag_comm_of_entry_zero`: an element `c ∈ SL₃(ℝ)` that is *block diagonal* for the
  equality pattern of `t` (`c_{ij} = 0` whenever `t i ≠ t j`) commutes with `aDiag t`.  This
  is the whole content of the centraliser condition, because `aDiag t` is diagonal:
  `(aDiag t · c)_{ij} = e^{t_i - m} c_{ij}` and `(c · aDiag t)_{ij} = c_{ij} e^{t_j - m}`
  differ exactly when `t i ≠ t j`.

* `permSL e`: the transport of the whole problem along a permutation `e` of the three
  coordinates, `(permSL e g)_{ij} = g_{e i, e j}`.  It is a group endomorphism of
  `SL₃(ℝ)` (`permSL_mul`, `permSL_one`), invertible (`permSL_symm_permSL`), and it sends the
  diagonal flow to the diagonal flow of the permuted exponent vector
  (`permSL_aDiag`: `permSL e (aDiag s) = aDiag (s ∘ e)`).  Together with the entry-form
  characterisation of `Uminus` (`Work.EKLC6Core.uminus_entry_zero`,
  `Work.EKLC6Core.mem_uminus_of_entry_form`) this reduces the general case `t` to the case
  `t 0 ≤ t 1 ≤ t 2` obtained by sorting the three values of `t`
  (`Work.EKLC6Core.exists_sorted`).
-/

open Matrix

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-! ## The centraliser condition is entrywise vanishing away from the level sets of `t` -/

/-- An element of `SL₃(ℝ)` whose `(i,j)`-entry vanishes whenever `t i ≠ t j` commutes with
`aDiag t`. -/
theorem aDiag_comm_of_entry_zero {t : Fin 3 → ℝ} {c : SL3}
    (h : ∀ i j : Fin 3, t i ≠ t j → (toMat c) i j = 0) :
    aDiag t * c = c * aDiag t := by
  apply ext_toMat
  simp only [toMat_mul, toMat_aDiag]
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hc : t i = t j
  · rw [hc]; ring
  · rw [h i j hc, mul_zero, zero_mul]

/-! ## Transport along a permutation of the coordinates -/

/-- The permutation transport of `SL₃(ℝ)`: `(permSL e g) i j = g (e i) (e j)`. -/
def permSL (e : Fin 3 ≃ Fin 3) (g : SL3) : SL3 :=
  ⟨(toMat g).submatrix ⇑e ⇑e, by
    rw [Matrix.det_submatrix_equiv_self e (toMat g)]; exact g.property⟩

@[simp] theorem toMat_permSL (e : Fin 3 ≃ Fin 3) (g : SL3) :
    toMat (permSL e g) = (toMat g).submatrix ⇑e ⇑e := rfl

theorem permSL_mul (e : Fin 3 ≃ Fin 3) (g h : SL3) :
    permSL e (g * h) = permSL e g * permSL e h := by
  apply ext_toMat
  rw [toMat_permSL, toMat_mul, toMat_mul, toMat_permSL, toMat_permSL]
  exact (Matrix.submatrix_mul_equiv (toMat g) (toMat h) ⇑e e ⇑e).symm

theorem permSL_one (e : Fin 3 ≃ Fin 3) : permSL e 1 = (1 : SL3) := by
  apply ext_toMat
  rw [toMat_permSL, toMat_one]
  exact Matrix.submatrix_one_equiv e

/-- The transport is inverted by the transport along the inverse permutation. -/
theorem permSL_symm_permSL (e : Fin 3 ≃ Fin 3) (g : SL3) :
    permSL e.symm (permSL e g) = g := by
  apply ext_toMat
  rw [toMat_permSL, toMat_permSL, Matrix.submatrix_submatrix]
  simp

/-- The transport sends the diagonal flow of `s` to the diagonal flow of the permuted
exponent vector `s ∘ e`. -/
theorem permSL_aDiag (e : Fin 3 ≃ Fin 3) (s : Fin 3 → ℝ) :
    permSL e (aDiag s) = aDiag (s ∘ ⇑e) := by
  apply ext_toMat
  simp only [toMat_permSL, toMat_aDiag]
  ext i j
  rw [Matrix.submatrix_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h
    simp [Function.comp_apply, Equiv.sum_comp e s]
  · have he : e i ≠ e j := fun hh => h (e.injective hh)
    simp [h, he]

end Work.EKLC6Core

end
