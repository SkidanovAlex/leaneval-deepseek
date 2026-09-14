import Mathlib
import Submission.Commons.FieldTheory.Polynomial.monic_index_ge_card_le

open Polynomial
open scoped BigOperators

set_option autoImplicit false

/-!
# The index of a monic polynomial over a field (Bhargava §1, §5)

For a monic polynomial `f` over a field, let `f = ∏_i P_i^{e_i}` be its
factorisation into distinct monic irreducible factors.  Bhargava's *index* is
`ind(f) = Σ_i (e_i − 1) · deg P_i`; equivalently

    ind(f) = deg f − deg(rad f),    rad f := ∏ (monic irreducible factors, each once).

This module defines `polyIndex` (via the UFD radical, so the shared-commons
API applies) and the product `monicRadical` (the explicit expression used in
the density statements), and records the elementary glue: the radical is monic
and divides `f`, the index is at most the degree, and
`index ≥ k` ⟺ `deg(rad f) ≤ deg f − k`.

**Finite-field density (Case-I, CI-1), from the shared commons** (file
`Commons.FieldTheory.Polynomial.monic_index_ge_card_le`, both PROVED):
- `Commons.FieldTheory.Polynomial.monic_index_ge_card_le {F} [Field F] [Fintype F]
  [DecidableEq F] (n k : ℕ) (hk : k ≤ n) :
  Nat.card {f : F[X] // f.Monic ∧ f.natDegree = n ∧
    k ≤ f.natDegree − (((normalizedFactors f).toFinset.prod id : F[X]).natDegree)}
    ≤ 2^((n+1)^4) · q^(n−k)`   —  #{monic degree n : index ≥ k} = O(q^{n−k});
- `Commons.FieldTheory.Polynomial.raddeg_le_ncard_le {F} (n M) (hMn : M ≤ n) :
  ({f | f.Monic ∧ f.natDegree = n ∧ (rad f).natDegree ≤ M}).ncard ≤
  (n+1)^(n+1) · q^M`  —  #{monic degree n : deg rad ≤ M} = O(q^M).
- commons API: `radical_monic`, `radical_dvd`, `natDegree_radical_le`,
  `radical_eq_toFinset_prod`, `radical_fiber_card`, `factorSet`.
-/

namespace Submission.Vdw

noncomputable section

variable {F : Type*} [Field F] [DecidableEq F]

open UniqueFactorizationMonoid

/-- The radical of a polynomial as an explicit product of its distinct monic
irreducible factors — the expression used in the density statements. -/
def monicRadical (f : F[X]) : F[X] :=
  (normalizedFactors f).toFinset.prod id

/-- Bhargava's index of a polynomial over a field: `deg f − deg(rad f)`
= `Σ (e_i − 1) deg P_i` over the distinct monic irreducible factors. -/
def polyIndex (f : F[X]) : ℕ :=
  f.natDegree - (UniqueFactorizationMonoid.radical f).natDegree

/-- `monicRadical` agrees with the UFD radical. -/
theorem monicRadical_eq_radical (f : F[X]) :
    monicRadical f = UniqueFactorizationMonoid.radical f := by
  dsimp [monicRadical]
  exact (Commons.FieldTheory.Polynomial.radical_eq_toFinset_prod (F := F) f).symm

/-- The radical of a polynomial is monic. -/
theorem monicRadical_monic (f : F[X]) : (monicRadical f).Monic := by
  classical
  by_cases hf0 : f = 0
  · subst f
    simp [monicRadical, normalizedFactors_zero]
  · dsimp [monicRadical]
    apply monic_prod_of_monic
    intro m hm
    exact ((Polynomial.mem_normalizedFactors_iff hf0).mp (Multiset.mem_toFinset.mp hm)).2.1

/-- The index of a polynomial is at most its degree. -/
theorem polyIndex_le_natDegree (f : F[X]) : polyIndex f ≤ f.natDegree := by
  dsimp [polyIndex]
  omega

/-- `index f ≥ k` iff the radical of `f` has degree at most `deg f − k`
(valid for monic `f`, where `deg rad f ≤ deg f`). -/
theorem polyIndex_ge_iff_radical_deg_le (f : F[X]) (hf : f.Monic) (k : ℕ)
    (hk : k ≤ f.natDegree) :
    k ≤ polyIndex f ↔
      (UniqueFactorizationMonoid.radical f).natDegree ≤ f.natDegree - k := by
  classical
  dsimp [polyIndex]
  have hd : (UniqueFactorizationMonoid.radical f).natDegree ≤ f.natDegree :=
    Commons.FieldTheory.Polynomial.natDegree_radical_le f hf.ne_zero
  omega

end
end Submission.Vdw
