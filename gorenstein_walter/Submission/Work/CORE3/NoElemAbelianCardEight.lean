import Mathlib

/-!
# CORE3: no elementary abelian subgroup of order `8`

`Work.CORE3.NoElemAbelianCardEight`.

Let `X` be a finite group whose Sylow 2-subgroup `S` has order `8` and is dihedral
(`S ≃* DihedralGroup 4`).  Then `X` contains no subgroup `W` of order `8` all of whose
elements are involutions.

The mathematics: since `|S| = 8` and `S` is a Sylow 2-subgroup, the 2-part of `|X|` equals
`8` (`Sylow.card_eq_multiplicity`).  A subgroup `W` of order `8` is therefore itself a Sylow
2-subgroup (`Sylow.ofCard`).  All Sylow 2-subgroups are conjugate
(`Sylow.isPretransitive_of_finite`), so `W` is a conjugate of `S`, hence `W ≃* S ≃* DihedralGroup 4`.
But `DihedralGroup 4` (the dihedral group of order `8`) contains an element of order `4`, while
`W`, being of exponent two, has no element of order `4` — a contradiction.

The whole argument is short and self-contained, so it is assembled directly here.
-/

open scoped Pointwise

namespace Work.CORE3

theorem NoElemAbelianCardEight {X : Type} [Group X] [Finite X] (S : Sylow 2 X)
    (hS8 : Nat.card (S : Subgroup X) = 8)
    (hdih : Nonempty ((S : Subgroup X) ≃* DihedralGroup 4)) :
    ¬ ∃ W : Subgroup X, Nat.card W = 8 ∧ ∀ x ∈ W, x ^ 2 = 1 := by
  rintro ⟨W, hW8, hWexp⟩
  -- `|S| = 8` is the 2-part of `|X|`, so every subgroup of order `8` is a Sylow 2-subgroup.
  have hfac : Nat.card W = 2 ^ (Nat.card X).factorization 2 := by
    rw [hW8, ← hS8]
    exact Sylow.card_eq_multiplicity S
  let P : Sylow 2 X := Sylow.ofCard W hfac
  have hP : (P : Subgroup X) = W := Sylow.coe_ofCard W hfac
  -- All Sylow 2-subgroups are conjugate, so `W` is a conjugate of `S`.
  obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := X) P S
  have hmap : W.map (MulEquiv.toMonoidHom (MulAut.conj g)) = (S : Subgroup X) := by
    have h := congrArg (fun Q : Sylow 2 X => (Q : Subgroup X)) hg
    simp only [Sylow.coe_subgroup_smul] at h
    rw [hP, Subgroup.pointwise_smul_def] at h
    exact h
  -- Conjugation by `g` gives `W ≃* S`.
  let e1 : W ≃* (S : Subgroup X) :=
    (Subgroup.equivMapOfInjective W (MulEquiv.toMonoidHom (MulAut.conj g))
      (MulEquiv.injective _)).trans (MulEquiv.subgroupCongr hmap)
  obtain ⟨e2⟩ := hdih
  -- Hence `W ≃* DihedralGroup 4`, which carries an element of order `4`.
  let e : W ≃* DihedralGroup 4 := e1.trans e2
  let w : W := e.symm (DihedralGroup.r (1 : ZMod 4))
  have hw4 : orderOf w = 4 := by
    rw [show w = e.symm (DihedralGroup.r (1 : ZMod 4)) from rfl, MulEquiv.orderOf_eq,
      DihedralGroup.orderOf_r]
    decide
  -- But every element of `W` squares to `1`, a contradiction.
  have hw2 : w ^ 2 = 1 := by
    apply Subtype.ext
    simpa using hWexp w.1 w.2
  have hdvd : orderOf w ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hw2
  rw [hw4] at hdvd
  norm_num at hdvd

end Work.CORE3
