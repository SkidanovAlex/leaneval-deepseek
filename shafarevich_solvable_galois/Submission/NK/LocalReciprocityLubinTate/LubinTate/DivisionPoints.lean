import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.Integral
import Submission.NK.LocalReciprocityLubinTate.LubinTate.EisFactor
import Submission.NK.LocalReciprocityLubinTate.LubinTate.card_rootSet_LTpolyIter
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The division points `Λ_n` of the standard Lubin–Tate group

This file develops the elementary theory of the sets

`Λ_n = { x ∈ F̄ | f^{(n)}(x) = 0 }`

of `π^n`-division points of the standard Lubin–Tate group `f(T) = πT + T^q` (Milne, *CFT*, §I.3),
and of the Lubin–Tate level `K_n = F(Λ_n)`.

## Main results

* `NK.LocalReciprocityLubinTate.LTpolyIter_succ_eq_mul` — the factorisation
  `f^{(n+1)} = f^{[n]} · f^{(n)}` (Milne I.3, Remark 3.1);
* `NK.LocalReciprocityLubinTate.ncard_LTdivisionSet` — **`Λ_n` has exactly `q^n` elements**
  (Milne I.3.1, the cardinality half);
* `NK.LocalReciprocityLubinTate.LTdivisionSet_mono` — `Λ_n ⊆ Λ_{n+1}`;
* `NK.LocalReciprocityLubinTate.LTdivisionSet_succ_eq_union` — `Λ_{n+1} = Λ_n ∪ f^{[n]}`-roots;
* `NK.LocalReciprocityLubinTate.ncard_rootSet_LTpolyEis` — the new division points at level `n`
  number `(q-1)q^n`;
* `NK.LocalReciprocityLubinTate.irreducible_LTpolyEis` — `f^{[n]}` is irreducible over `F`.
-/

open Polynomial

set_option maxHeartbeats 800000

namespace NK.LocalReciprocityLubinTate

universe u

/-- **The factorisation of the iterate into the Eisenstein factors**: for `q ≥ 1`
`f^{(n+1)} = f^{[n]} · f^{(n)}`, where `f^{[n]} = LTpolyEis π q n = (f^{(n)})^{q-1} + π`
(Milne, *CFT*, Remark 3.1). -/
theorem LTpolyIter_succ_eq_mul {A : Type u} [CommRing A] (π : A) (q n : ℕ) (hq : 1 ≤ q) :
    LTpolyIter π q (n + 1) = LTpolyEis π q n * LTpolyIter π q n := by
  rw [LTpolyIter_succ'', LTpoly_comp_eq π q hq (LTpolyIter π q n), LTpolyEis, mul_comm]

/-- The iterate `f^{(n+1)}` evaluated at `x` is the `n`-th iterate evaluated at `f(x)`. -/
theorem aeval_LTpolyIter_succ {A : Type u} [CommRing A] (π : A) (q n : ℕ) (x : A) :
    (aeval x) (LTpolyIter π q (n + 1)) = (aeval ((aeval x) (LTpoly π q))) (LTpolyIter π q n) := by
  rw [LTpolyIter_succ, Polynomial.aeval_comp]

/-- The Eisenstein factor `f^{[n]}` is nonzero (for `q ≥ 2`): it is the other factor of the monic
iterate `f^{(n+1)} ≠ 0`. -/
theorem LTpolyEis_ne_zero {A : Type u} [CommRing A] [Nontrivial A] (π : A) (q n : ℕ) (hq : 2 ≤ q) :
    LTpolyEis π q n ≠ 0 := by
  have hq1 : 1 ≤ q := by omega
  intro h
  have h2 : LTpolyIter π q (n + 1) = 0 := by
    rw [LTpolyIter_succ_eq_mul π q n hq1, h, zero_mul]
  exact LTpolyIter_ne_zero π q (n + 1) hq h2

/-- The standard Lubin–Tate polynomial is compatible with ring homomorphisms. -/
theorem map_LTpoly {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (π : A) (q : ℕ) :
    (LTpoly π q).map φ = LTpoly (φ π) q := by
  simp [LTpoly]

/-- The Eisenstein factors are compatible with ring homomorphisms. -/
theorem map_LTpolyEis {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (π : A) (q n : ℕ) :
    (LTpolyEis π q n).map φ = LTpolyEis (φ π) q n := by
  simp only [LTpolyEis, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_C,
    LTpolyIter_map]

/-- `Λ_0 = {0}`: the `π^0`-division points are the roots of `f^{(0)} = X`. -/
theorem LTdivisionSet_zero (F : Type u) [Field F] (π : F) (q : ℕ) :
    LTdivisionSet F π q 0 = {0} := by
  ext x
  rw [LTdivisionSet, LTpolyIter_zero, Polynomial.mem_rootSet_of_ne (Polynomial.X_ne_zero)]
  simp

/-- **The division points are nested**: `Λ_n ⊆ Λ_{n+1}`.  Indeed `f^{(n+1)} = f ∘ f^{(n)}`, so a
root of `f^{(n)}` is a root of `f^{(n+1)}` because `f(0) = 0`. -/
theorem LTdivisionSet_mono (F : Type u) [Field F] (π : F) (q : ℕ) (hq : 2 ≤ q) :
    Monotone (LTdivisionSet F π q) := by
  have hzero : (aeval (0 : AlgebraicClosure F)) (LTpoly π q) = 0 := by
    simp [LTpoly, zero_pow (n := q) (by omega)]
  refine monotone_nat_of_le_succ fun n x hx => ?_
  rw [mem_LTdivisionSet_iff π q n hq] at hx
  rw [mem_LTdivisionSet_iff π q (n + 1) hq, LTpolyIter_succ'', Polynomial.aeval_comp, hx]
  exact hzero

/-- The `π^n`-division points are the roots of the iterate `f^{(n)}`. -/
theorem LTdivisionSet_eq_setOf_isRoot {F : Type u} [Field F] (π : F) (q n : ℕ) (hq : 2 ≤ q) :
    LTdivisionSet F π q n
      = {x : AlgebraicClosure F |
          ((LTpolyIter π q n).map (algebraMap F (AlgebraicClosure F))).IsRoot x} := by
  ext x
  rw [LTdivisionSet, Polynomial.mem_rootSet_of_ne (LTpolyIter_ne_zero π q n hq),
    Set.mem_setOf_eq, Polynomial.IsRoot.def, ← Polynomial.eval₂_eq_eval_map,
    ← Polynomial.aeval_def]

/-- **`Λ_n` has exactly `q^n` elements** (Milne, *CFT*, §I.3: the `π^n`-torsion of the
Lubin–Tate group is a free `𝒪[F]/π^n`-module of rank one, hence has `q^n` elements).

This is the cardinality half of Theorem I.3.1 of Milne; it is proved here from the separability of
the iterates (`NK.LocalReciprocityLubinTate.LubinTate.card_rootSet_LTpolyIter`). -/
theorem ncard_LTdivisionSet (F : Type u) [Field F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (π : (↥(ValuativeRel.valuation F).integer)) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q) :
    (LTdivisionSet F (π : F) q n).ncard = q ^ n := by
  rw [LTdivisionSet_eq_setOf_isRoot (π : F) q n hq]
  exact LubinTate.card_rootSet_LTpolyIter F π hπ q n hq

/-- `Λ_1` has exactly `q` elements: the `π`-torsion of the Lubin–Tate group consists of `0` and
the `q-1` roots of the Eisenstein polynomial `X^{q-1} + π`. -/
theorem ncard_LTdivisionSet_one (F : Type u) [Field F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (π : (↥(ValuativeRel.valuation F).integer)) (hπ : Irreducible π) (q : ℕ) (hq : 2 ≤ q) :
    (LTdivisionSet F (π : F) q 1).ncard = q := by
  rw [ncard_LTdivisionSet F π hπ q 1 hq, pow_one]

/-- **`f^{[n]}` is irreducible over `F`** (Milne, *CFT*, §I.3: it is Eisenstein at `π`).  It is
the minimal polynomial of a *primitive* `π^{n+1}`-division point, and its degree is
`(q-1)q^n`. -/
theorem irreducible_LTpolyEis (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (π : (↥(ValuativeRel.valuation F).integer)) (hπ : Irreducible π)
    (q n : ℕ) (hq : 2 ≤ q) : Irreducible (LTpolyEis (π : F) q n) := by
  have h := irreducible_LTpolyIter_shift (R := ↥(ValuativeRel.valuation F).integer)
    (K := F) π hπ q n hq
  rw [show ((LTpolyIter π q n) ^ (q - 1) + Polynomial.C π).map
        (algebraMap ↥(ValuativeRel.valuation F).integer F)
      = (LTpolyEis π q n).map (algebraMap ↥(ValuativeRel.valuation F).integer F) from rfl,
    map_LTpolyEis] at h
  exact h

/-- **The number of roots of `f^{[n]}` is `(q-1)q^n`**: the `π^{n+1}`-division points that are not
`π^n`-division points number `(q-1)q^n`. -/
theorem ncard_rootSet_LTpolyEis (F : Type u) [Field F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (π : (↥(ValuativeRel.valuation F).integer)) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q) :
    ((LTpolyEis (π : F) q n).rootSet (AlgebraicClosure F)).ncard = (q - 1) * q ^ n := by
  classical
  have hπF : (π : F) ≠ 0 := fun h => hπ.ne_zero (Subtype.coe_injective (by simpa using h))
  obtain ⟨hGmonic, hGnat, -, -⟩ := LubinTate.LTpolyIter_monic_degree (π : F) q n hq
  have hpowmonic : ((LTpolyIter (π : F) q n) ^ (q - 1)).Monic := hGmonic.pow _
  have hpowdeg : ((LTpolyIter (π : F) q n) ^ (q - 1)).natDegree = (q - 1) * q ^ n := by
    rw [natDegree_pow, hGnat]
  have hdegpos : 0 < (q - 1) * q ^ n := Nat.mul_pos (by omega) (pow_pos (by omega) n)
  have hlt : (Polynomial.C (π : F)).degree < ((LTpolyIter (π : F) q n) ^ (q - 1)).degree := by
    rw [Polynomial.degree_C hπF, degree_eq_natDegree hpowmonic.ne_zero, hpowdeg]
    exact_mod_cast hdegpos
  have hnat : (LTpolyEis (π : F) q n).natDegree = (q - 1) * q ^ n := by
    rw [LTpolyEis, natDegree_add_eq_left_of_degree_lt hlt, hpowdeg]
  have hsep : (LTpolyEis (π : F) q n).Separable :=
    (irreducible_LTpolyEis F π hπ q n hq).separable
  have hsplit : ((LTpolyEis (π : F) q n).map (algebraMap F (AlgebraicClosure F))).Splits :=
    IsAlgClosed.splits _
  have hcard : Fintype.card ↑((LTpolyEis (π : F) q n).rootSet (AlgebraicClosure F))
      = (q - 1) * q ^ n := by
    rw [Polynomial.card_rootSet_eq_natDegree hsep hsplit, hnat]
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
  exact hcard

/-- The factorisation of the division points: `Λ_{n+1}` is the union of `Λ_n` with the roots of
the Eisenstein factor `f^{[n]}`. -/
theorem LTdivisionSet_succ_eq_union (F : Type u) [Field F] (π : F) (q n : ℕ) (hq : 2 ≤ q) :
    LTdivisionSet F π q (n + 1) =
      LTdivisionSet F π q n ∪ (LTpolyEis π q n).rootSet (AlgebraicClosure F) := by
  have hq1 : 1 ≤ q := by omega
  ext x
  rw [Set.mem_union, mem_LTdivisionSet_iff π q (n + 1) hq, mem_LTdivisionSet_iff π q n hq,
    Polynomial.mem_rootSet_of_ne (LTpolyEis_ne_zero π q n hq), LTpolyIter_succ_eq_mul π q n hq1,
    Polynomial.aeval_mul, mul_eq_zero]
  tauto

/-- `adjoin K (s ∪ t) = adjoin K s ⊔ adjoin K t`. -/
theorem adjoin_union_eq_sup {K L : Type*} [Field K] [Field L] [Algebra K L] (s t : Set L) :
    IntermediateField.adjoin K (s ∪ t)
      = IntermediateField.adjoin K s ⊔ IntermediateField.adjoin K t := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    rintro x (hx | hx)
    · exact SetLike.coe_subset_coe.mpr le_sup_left (IntermediateField.subset_adjoin K s hx)
    · exact SetLike.coe_subset_coe.mpr le_sup_right (IntermediateField.subset_adjoin K t hx)
  · refine sup_le ?_ ?_
    · rw [IntermediateField.adjoin_le_iff]
      exact fun x hx => IntermediateField.subset_adjoin K (s ∪ t) (Set.mem_union_left t hx)
    · rw [IntermediateField.adjoin_le_iff]
      exact fun x hx => IntermediateField.subset_adjoin K (s ∪ t) (Set.mem_union_right s hx)

/-- **The tower of Lubin–Tate levels**: `K_{n+1} = K_n ⊔ F(roots of f^{[n]})`, i.e. each level is
obtained from the previous one by adjoining the roots of the Eisenstein polynomial
`f^{[n]}(T) = f^{(n)}(T)^{q-1} + π`. -/
theorem LTLevel_succ_eq_sup (F : Type u) [Field F] (π : F) (q n : ℕ) (hq : 2 ≤ q) :
    LTLevel F π q (n + 1) = LTLevel F π q n ⊔
      IntermediateField.adjoin F ((LTpolyEis π q n).rootSet (AlgebraicClosure F)) := by
  rw [LTLevel, LTdivisionSet_succ_eq_union F π q n hq, adjoin_union_eq_sup, LTLevel]

end NK.LocalReciprocityLubinTate
