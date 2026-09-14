import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.RingTheory.SimpleRing.Principal

open Polynomial
set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Commons.FieldTheory.PolynomialGaloisGroup

/-- The Galois group of a polynomial `p` embeds into the permutations of its (distinct) roots
in its splitting field, so its cardinality is bounded by `p.natDegree!`. -/
theorem card_gal_le_factorial {F : Type*} [Field F] (p : F[X]) :
    Nat.card p.Gal ≤ p.natDegree.factorial := by
  classical
  haveI : Fact ((p.map (algebraMap F p.SplittingField)).Splits) :=
    ⟨Polynomial.SplittingField.splits p⟩
  have hcard_roots : Fintype.card (p.rootSet p.SplittingField) ≤ p.natDegree := by
    rw [Set.fintypeCard_eq_ncard]
    exact Polynomial.ncard_rootSet_le p p.SplittingField
  have hperm_card : Fintype.card (Equiv.Perm (p.rootSet p.SplittingField)) ≤
      p.natDegree.factorial := by
    rw [Fintype.card_perm]
    exact Nat.factorial_le hcard_roots
  have hinj : Function.Injective (Polynomial.Gal.galActionHom p p.SplittingField) :=
    Polynomial.Gal.galActionHom_injective p p.SplittingField
  have hcard : Fintype.card p.Gal ≤
      Fintype.card (Equiv.Perm (p.rootSet p.SplittingField)) :=
    Fintype.card_le_of_injective (Polynomial.Gal.galActionHom p p.SplittingField) hinj
  simpa [Nat.card_eq_fintype_card] using hcard.trans hperm_card

end Commons.FieldTheory.PolynomialGaloisGroup