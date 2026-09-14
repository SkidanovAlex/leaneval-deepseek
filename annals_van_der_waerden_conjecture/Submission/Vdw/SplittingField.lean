import Mathlib
import Submission.Vdw.GaloisAction

open Polynomial
open scoped NumberField

set_option autoImplicit false

/-!
# The splitting field of an irreducible polynomial (step-(c) infrastructure)

Step (c) of the Case-I squarefullness thread (`CaseI.fieldDisc_val_one_has_
isSwap`) works in the splitting field `L := p.SplittingField` of the
polynomial `p = f.map φℚ` whose Galois group `p.Gal = Gal(L/ℚ)` is the full
automorphism group of `L`.  This module supplies the structural facts that
`L` needs for that argument:

* `splNumberField`: `p.SplittingField` is a `NumberField` (Mathlib has the
  finite-dimensional/separable instances, but not the bundled `NumberField`);
* `splRoot`/`splRootVal`/`splRoot_aeval`: an explicit root of `p` inside its
  splitting field (via the `rootFinEquiv` identification of
  `GaloisAction.lean`);
* `kpolyEmb`/`kpolyAlgebra`: the canonical embedding of
  `K_p := ℚ[x]/(p) = AdjoinRoot p` into `L` (universal property of the
  quotient by the minimal polynomial, `AdjoinRoot.lift`), as an algebra
  structure on `L`;
* **step-1 theorems**: `prime_dvd_discr_splittingField_of_dvd` — if a
  rational prime `q` divides the absolute discriminant of `K_p` then it
  divides that of the splitting field (`NumberField.discr_dvd_discr`, the
  tower discriminant formula); and `ramified_in_splittingField_of_ramified`
  — unramifiedness is preserved downward, so ramification in `K_p` forces
  ramification in `L`.

Everything is stated for an arbitrary irreducible `p : ℚ[X]` (`[Fact
(Irreducible p)]`); `CaseI.lean` instantiates it at `p = f.map φℚ` where
`K_p` is definitionally `Kpoly f`.
-/

namespace Submission.Vdw

noncomputable section

open Polynomial

/-- The splitting field of a polynomial over `ℚ` is a number field. -/
instance splNumberField (p : ℚ[X]) : NumberField p.SplittingField where
  to_charZero := inferInstance
  to_finiteDimensional := inferInstance

/-- An explicit root of the irreducible `p` in its splitting field (a point
of `p.rootSet p.SplittingField`). -/
noncomputable def splRoot (p : ℚ[X]) [Fact (Irreducible p)] : p.rootSet p.SplittingField := by
  classical
  have hdeg : 0 < p.natDegree := by
    rw [Polynomial.natDegree_pos_iff_degree_pos]
    exact Polynomial.degree_pos_of_irreducible Fact.out
  exact (rootFinEquiv p (separable_of_irreducible_rat Fact.out)).symm ⟨0, hdeg⟩

/-- The value in `p.SplittingField` of the root `splRoot`. -/
noncomputable def splRootVal (p : ℚ[X]) [Fact (Irreducible p)] : p.SplittingField :=
  (splRoot p).1

/-- The chosen root is indeed a root: `aeval x p = 0`. -/
lemma splRoot_aeval (p : ℚ[X]) [Fact (Irreducible p)] : Polynomial.aeval (splRootVal p) p = 0 := by
  exact (Polynomial.mem_rootSet.mp (splRoot p).2).2

/-- Canonical embedding of `K_p := ℚ[x]/(p)` into its splitting field
(universal property of `AdjoinRoot`, `AdjoinRoot.lift` at the chosen root). -/
noncomputable def kpolyEmb (p : ℚ[X]) [Fact (Irreducible p)] :
    AdjoinRoot p →+* p.SplittingField :=
  AdjoinRoot.lift (i := algebraMap ℚ p.SplittingField) (x := splRootVal p)
    (by simpa [Polynomial.aeval_def] using splRoot_aeval p)

/-- The induced algebra structure of the splitting field over
`K_p = AdjoinRoot p`.  (Keep as a plain definition — used via `letI` — to
avoid a global instance whose parameters typeclass search cannot infer.) -/
noncomputable def kpolyAlgebra (p : ℚ[X]) [Fact (Irreducible p)] :
    Algebra (AdjoinRoot p) p.SplittingField :=
  RingHom.toAlgebra (kpolyEmb p)

/-- **Step-1 divisibility (tower discriminant formula).**  If a rational
prime `q` divides the absolute discriminant of `K_p = ℚ[x]/(p)`, then it
divides the absolute discriminant of the splitting field `p.SplittingField`.
(Mathlib: `NumberField.discr_dvd_discr`, from the tower formula
`|discr L| = ‖different_{L/K}‖ · |discr K|^{[L:K]}`.) -/
theorem prime_dvd_discr_splittingField_of_dvd (p : ℚ[X]) [Fact (Irreducible p)]
    (q : ℕ) (hq : Nat.Prime q)
    (h : (q : ℤ) ∣ NumberField.discr (AdjoinRoot p)) :
    (q : ℤ) ∣ NumberField.discr p.SplittingField := by
  classical
  letI : Algebra (AdjoinRoot p) p.SplittingField := kpolyAlgebra p
  have hd := NumberField.discr_dvd_discr (K := AdjoinRoot p) (L := p.SplittingField)
  exact dvd_trans h hd

/-- **Step 1, ramification form.**  Unramifiedness is inherited downward, so
if `q` is ramified in `K_p = ℚ[x]/(p)` then it is ramified in the splitting
field `p.SplittingField`. -/
theorem ramified_in_splittingField_of_ramified (p : ℚ[X]) [Fact (Irreducible p)]
    (q : ℕ) (hq : Nat.Prime q)
    (hram : ¬ Algebra.IsUnramifiedIn (𝓞 (AdjoinRoot p)) (Ideal.span ({(q : ℤ)} : Set ℤ))) :
    ¬ Algebra.IsUnramifiedIn (𝓞 p.SplittingField) (Ideal.span ({(q : ℤ)} : Set ℤ)) := by
  classical
  -- hram ⟺ (q:ℤ) ∣ discr (AdjoinRoot p)
  have h1 : ¬ ((q : ℤ) ∣ NumberField.discr (AdjoinRoot p)) ↔
      Algebra.IsUnramifiedIn (𝓞 (AdjoinRoot p)) (Ideal.span ({(q : ℤ)} : Set ℤ)) :=
    NumberField.not_dvd_discr_iff_isUnramifiedIn (K := AdjoinRoot p) (𝒪 := 𝓞 (AdjoinRoot p))
      ((Nat.prime_iff_prime_int).1 hq)
  have hdvd : (q : ℤ) ∣ NumberField.discr (AdjoinRoot p) := by
    by_contra hn
    exact hram (h1.mp hn)
  have hdvdL : (q : ℤ) ∣ NumberField.discr p.SplittingField :=
    prime_dvd_discr_splittingField_of_dvd p q hq hdvd
  have h2 : ¬ ((q : ℤ) ∣ NumberField.discr p.SplittingField) ↔
      Algebra.IsUnramifiedIn (𝓞 p.SplittingField) (Ideal.span ({(q : ℤ)} : Set ℤ)) :=
    NumberField.not_dvd_discr_iff_isUnramifiedIn (K := p.SplittingField)
      (𝒪 := 𝓞 p.SplittingField) ((Nat.prime_iff_prime_int).1 hq)
  exact fun hU => (h2.mpr hU) hdvdL

end
end Submission.Vdw
