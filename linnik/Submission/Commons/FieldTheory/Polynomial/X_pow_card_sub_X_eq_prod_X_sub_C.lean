import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

open Polynomial

namespace Commons.FieldTheory.Polynomial

theorem X_pow_card_sub_X_eq_prod_X_sub_C {F : Type*} [Field F] [Fintype F] :
    (X ^ Fintype.card F - X : F[X]) = ∏ c : F, (X - C c) := by
  classical
  let f : F[X] := X ^ Fintype.card F - X
  change f = ∏ c : F, (X - C c)
  have hfmonic : f.Monic := by
    dsimp [f]
    change (X ^ Fintype.card F - X : F[X]).leadingCoeff = 1
    have hdeg_lt : (X : F[X]).degree < (X ^ Fintype.card F : F[X]).degree := by
      rw [degree_X, degree_X_pow]
      exact_mod_cast (Fintype.one_lt_card : 1 < Fintype.card F)
    rw [leadingCoeff_sub_of_degree_lt hdeg_lt]
    exact leadingCoeff_X_pow (Fintype.card F)
  have hroots : f.roots = (Finset.univ : Finset F).val := by
    dsimp [f]
    simpa using (FiniteField.roots_X_pow_card_sub_X (K := F))
  have hdeg : f.natDegree = Fintype.card F := by
    dsimp [f]
    simpa using (FiniteField.X_pow_card_sub_X_natDegree_eq (K' := F) (p := Fintype.card F)
      (Fintype.one_lt_card : 1 < Fintype.card F))
  have hsplits : f.Splits := by
    rw [splits_iff_card_roots, hroots, hdeg]
    simp
  calc
    f = ((f.roots.map fun x : F => X - C x).prod) := (hsplits.eq_prod_roots_of_monic hfmonic)
    _ = ((Finset.univ : Finset F).val.map (fun x : F => X - C x)).prod := by rw [hroots]
    _ = ∏ c : F, (X - C c) := rfl

end Commons.FieldTheory.Polynomial