import Mathlib
import Submission.Vdw.PolyIndex
import Submission.Vdw.IndexFactor
import Submission.Vdw.ResidueIndex
import Submission.Vdw.IndexBaseChange

open Polynomial
open scoped BigOperators

set_option autoImplicit false

/-!
# Residue-side index atoms (discindex step 1c(iii), mod-p pre-stones)

For a monic polynomial over a field, Bhargava's index is
`polyIndex f = natDegree f − natDegree (rad f)`.  In the Kummer–Dedekind step
of the discindex bridge (Lemma 24), the mod-`p` side of the inequality
`Σ_{P|p} f_P (e_P − 1) ≤ index_{F_p}(f̄)` is computed from the factorization of
the reduction into congruence classes `f̄ ≡ (X − c)^e`-shaped pieces; each
such Hensel factor contributes exactly `e − 1` to the index.

This module records the per-factor atoms: a monic linear polynomial
`X − C c` is irreducible (Mathlib `Polynomial.irreducible_X_sub_C`), hence of
index `0` (`polyIndex_irreducible`), and its `e`-th power has index
`(e − 1)·deg(X − C c) = e − 1` (index of a prime power,
`IndexFactor.polyIndex_pow_irreducible`), over any field.
-/

namespace Submission.Vdw

section injective

variable {F : Type*} [CommRing F]

/-- `X − C` is injective (coefficient-of-`X⁰` argument). -/
theorem X_sub_C_injective {a b : F} (h : (X - C a : F[X]) = X - C b) : a = b := by
  have hc : (X - C a : F[X]).coeff 0 = (X - C b : F[X]).coeff 0 := by rw [h]
  have hneg : -a = -b := by simpa using hc
  exact neg_injective hneg

end injective


noncomputable section

variable {F : Type*} [Field F] [DecidableEq F]

open UniqueFactorizationMonoid

/-- A monic linear polynomial has index `0`: `polyIndex (X − C c) = 0`
(irreducible monic polynomials have index `0`). -/
theorem polyIndex_X_sub_C (c : F) : polyIndex (X - C c) = 0 := by
  have hmon : (X - C c : F[X]).Monic := Polynomial.monic_X_sub_C c
  have hirr : Irreducible (X - C c : F[X]) := Polynomial.irreducible_X_sub_C c
  exact polyIndex_irreducible hmon hirr

/-- The `e`-th power of a monic linear polynomial has index `e − 1`
(for `1 ≤ e`): `polyIndex ((X − C c)^e) = e − 1`. -/
theorem polyIndex_X_sub_C_pow (c : F) (e : ℕ) (he : 1 ≤ e) :
    polyIndex ((X - C c : F[X]) ^ e) = e - 1 := by
  have hmon : (X - C c : F[X]).Monic := Polynomial.monic_X_sub_C c
  have hirr : Irreducible (X - C c : F[X]) := Polynomial.irreducible_X_sub_C c
  have hdeg : (X - C c : F[X]).natDegree = 1 := Polynomial.natDegree_X_sub_C c
  calc
    polyIndex ((X - C c : F[X]) ^ e) = (e - 1) * (X - C c : F[X]).natDegree :=
      polyIndex_pow_irreducible_of_monic hmon hirr e he
    _ = e - 1 := by rw [hdeg, mul_one]

/-- **Fully-ramified atom (index-class form)**: if a monic degree-`n`
polynomial equals `(X − C c)^n` (the trail vector is the reduction of a pure
`n`-th power of a linear factor — the totally ramified situation), then its
index is exactly `n − 1`, i.e. the vector lies in index class `(n, n−1)`. -/
theorem indexClass_pow_X_sub_C_full (n : ℕ) (hn : 1 ≤ n) (v : Fin n → F)
    (c : F) (hc : monicOfTrail n v = (X - C c : F[X]) ^ n) :
    indexClass n (n - 1) v := by
  rw [indexClass]
  have hp : polyIndex (monicOfTrail n v) = n - 1 := by
    rw [hc]
    exact polyIndex_X_sub_C_pow c n hn
  rw [hp]

/-- **Splitting-type residue atom**: when the monic trail polynomial factors
over the field as `∏_{i ∈ s} (X − C (r i)) ^ (e i)` with the residues
`r` injective on `s` (all factors linear and distinct), the index is the
Kummer–Dedekind sum `Σ_i (e_i − 1)`.  This is the `F_p`-side equality of the
discindex chain in the totally-split case. -/
theorem polyIndex_X_sub_C_family_pow {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (r : ι → F) (e : ι → ℕ) (he : ∀ i ∈ s, 1 ≤ e i)
    (hrij : ∀ i ∈ s, ∀ j ∈ s, r i = r j → i = j) :
    polyIndex (∏ i ∈ s, (X - C (r i) : F[X]) ^ e i) =
      ∑ i ∈ s, (e i - 1) := by
  classical
  have hirr : ∀ i ∈ s, Irreducible (X - C (r i) : F[X]) := by
    intro i hi
    exact Polynomial.irreducible_X_sub_C (r i)
  have hdeg : ∀ i ∈ s, (X - C (r i) : F[X]).natDegree = 1 := by
    intro i hi
    exact Polynomial.natDegree_X_sub_C (r i)
  have hne : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (X - C (r i) : F[X]) ≠ (X - C (r j) : F[X]) := by
    intro i hi j hj hij hlin
    have hri : r i = r j := X_sub_C_injective hlin
    exact hij (hrij i hi j hj hri)
  have hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      IsCoprime (X - C (r i) : F[X]) (X - C (r j) : F[X]) := by
    intro i hi j hj hij
    exact monic_irreducible_coprime_of_ne (hirr i hi) (hirr j hj)
      (Polynomial.monic_X_sub_C (r i)) (Polynomial.monic_X_sub_C (r j)) (hne i hi j hj hij)
  let h : ι → F[X] := fun i => X - C (r i)
  have hmon2 : ∀ i ∈ s, (h i).Monic := by
    intro i hi
    exact Polynomial.monic_X_sub_C (r i)
  have hmain := polyIndex_splitting_type (F := F) s h e hmon2 hirr hcop he
  -- hmain : polyIndex (∏ i ∈ s, (X - C (r i)) ^ e i) = ∑ i ∈ s, (e i - 1) * (X - C (r i)).natDegree
  rw [hmain]
  refine Finset.sum_congr rfl ?_
  intro i hi
  change (e i - 1) * (X - C (r i) : F[X]).natDegree = e i - 1
  rw [hdeg i hi, mul_one]

end
end Submission.Vdw
