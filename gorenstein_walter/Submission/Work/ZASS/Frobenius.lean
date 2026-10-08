/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area ZASS: the Frobenius action of the torus `H = G_{∞0}` on the unipotent radical `U`

Step Z3 of the blueprint says that `H = G_{∞0}` acts *fixed-point-freely* by conjugation on
the unipotent radical `U` of the Borel subgroup (`Work.ZASS.FixedPointFreeConj`), i.e. `U ⋊ H`
is a Frobenius group.  This file

* turns the conjugation homomorphism `Work.ZASS.conjAut` into a `MulDistribMulAction ↥H ↥U`,
  so that the Isaacs Chapter 6 / HB V §8 theory of Frobenius complements applies, and
* records the consequences that step Z6 of the blueprint (HB III XI 1.5, 1.8b, 1.11) needs:

  * `Work.ZASS.isFrobeniusAction_conj` — the action is Frobenius (Isaacs p. 177);
  * `Work.ZASS.unique_involution_of_even` — if `|H|` is even then `H` has a unique involution
    (Isaacs Thm 6.3 = HB V 8.18);
  * `Work.ZASS.involution_inverts` — that involution inverts `U` (Isaacs Thm 6.3 = HB V 8.18),
    which is HB 1.8b (`kt = -k`);
  * `Work.ZASS.isCyclic_of_isMulCommutative_of_free` — an abelian Frobenius complement is cyclic
    (Isaacs Cor 6.17), used for the `d` even branch of HB 1.11;
  * `Work.ZASS.isZGroup_of_odd_of_free` — an odd-order Frobenius complement is a Z-group
    (Isaacs Cor 6.18 = HB V 8.7), used for the `d` odd branch of HB 1.5.
-/
import Mathlib
import Submission.Work.ZASS.Defs
import Submission.Work.ZASS.exists_field_coordinates
import Submission.OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusActionBasics
import Submission.OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusGroup
import Submission.OddOrder.Isaacs.Ch06_FrobeniusActions.Main
import Submission.OddOrder.Isaacs.Ch06_FrobeniusActions.OddComplement

namespace Work.ZASS

open Work.Zassenhaus (borel pairStab)

/-- A `MulDistribMulAction` obtained from a monoid homomorphism into the automorphism group. -/
@[reducible] noncomputable def mulDistribMulActionOfMulAutHom {M N : Type*} [Monoid M]
    [Group N] (φ : M →* MulAut N) : MulDistribMulAction M N where
  toMulAction :=
    { smul := fun m n => φ m n
      one_smul := fun n => by change φ 1 n = n; rw [map_one]; rfl
      mul_smul := fun a b n => by change φ (a * b) n = φ a (φ b n); rw [map_mul]; rfl }
  smul_one := fun m => by change φ m 1 = 1; exact map_one (φ m)
  smul_mul := fun m x y => by change φ m (x * y) = φ m x * φ m y; exact map_mul (φ m) x y

section Bridge

variable {G X : Type} [Group G] [MulAction G X] {inf zero : X} {U : Subgroup G}

/-- The conjugation action of `H = G_{∞0}` on the normal subgroup `U` of the Borel subgroup,
as a `MulDistribMulAction`. -/
@[reducible] noncomputable def conjMulDistribMulAction (hUB : U ≤ borel G inf)
    (hN : (U.subgroupOf (borel G inf)).Normal) :
    MulDistribMulAction ↥(pairStab G inf zero) ↥U :=
  mulDistribMulActionOfMulAutHom (conjAut hUB hN)

/-- The underlying function of `conjMulDistribMulAction`. -/
noncomputable def conjSmul (hUB : U ≤ borel G inf)
    (hN : (U.subgroupOf (borel G inf)).Normal) (h : ↥(pairStab G inf zero)) (u : ↥U) : ↥U :=
  conjAut hUB hN h u

theorem conjSmul_coe (hUB : U ≤ borel G inf)
    (hN : (U.subgroupOf (borel G inf)).Normal) (h : ↥(pairStab G inf zero)) (u : ↥U) :
    ((conjSmul hUB hN h u : ↥U) : G) = conjBy (h : G) (u : G) :=
  conjAut_apply hUB hN h u

/-- **Z3 restated in Isaacs' language.**  `FixedPointFreeConj U H` is exactly Isaacs' notion
of a *Frobenius action* of `H` on `U` (Isaacs p. 177), for the conjugation action. -/
theorem isFrobeniusAction_conj (hUB : U ≤ borel G inf)
    (hN : (U.subgroupOf (borel G inf)).Normal)
    (hfree : FixedPointFreeConj U (pairStab G inf zero)) :
    letI := conjMulDistribMulAction (G := G) (inf := inf) (zero := zero) hUB hN
    OddOrder.Isaacs.Ch06.IsFrobeniusAction ↥(pairStab G inf zero) ↥U := by
  letI := conjMulDistribMulAction (G := G) (inf := inf) (zero := zero) hUB hN
  intro h hh u hu huv
  have h2 : conjSmul hUB hN h u = u := huv
  have hval : conjBy (h : G) (u : G) = (u : G) := by
    rw [← conjSmul_coe hUB hN h u, h2]
  refine hu (Subtype.ext ?_)
  exact hfree (h : G) h.2 (fun h1 => hh (Subtype.ext h1)) (u : G) u.2 hval

end Bridge

section Consequences

variable {G X : Type} [Group G] [Finite G] [MulAction G X] {inf zero : X} {U : Subgroup G}
  {p k : ℕ}

/-- **Isaacs Thm 6.3 / HB V 8.18, uniqueness.**  If `H = G_{∞0}` acts fixed-point-freely on `U`
and `|H|` is even, then `H` has a unique involution. -/
theorem unique_involution_of_even [Finite U] (hUB : U ≤ borel G inf)
    (hN : (U.subgroupOf (borel G inf)).Normal)
    (hfree : FixedPointFreeConj U (pairStab G inf zero))
    (heven : 2 ∣ Nat.card (pairStab G inf zero)) (hnt : Nontrivial ↥U) :
    ∃! t : ↥(pairStab G inf zero), t ≠ 1 ∧ t ^ 2 = 1 := by
  letI := conjMulDistribMulAction (G := G) (inf := inf) (zero := zero) hUB hN
  letI : Fintype ↥(pairStab G inf zero) := Fintype.ofFinite _
  letI : Fintype ↥U := Fintype.ofFinite _
  exact OddOrder.Isaacs.Ch06.IsFrobeniusAction.unique_involution
    (A := ↥(pairStab G inf zero)) (N := ↥U)
    (isFrobeniusAction_conj hUB hN hfree) (by simpa [Nat.card_eq_fintype_card] using heven) hnt

/-- **Isaacs Thm 6.3 / HB V 8.18, inversion (HB 1.8b: `kt = -k`).**  Any involution of `H`
inverts `U`. -/
theorem involution_inverts [Finite U] (hUB : U ≤ borel G inf)
    (hN : (U.subgroupOf (borel G inf)).Normal)
    (hfree : FixedPointFreeConj U (pairStab G inf zero))
    (t : ↥(pairStab G inf zero)) (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1) (u : ↥U) :
    conjBy (t : G) (u : G) = (u : G)⁻¹ := by
  letI := conjMulDistribMulAction (G := G) (inf := inf) (zero := zero) hUB hN
  letI : Fintype ↥U := Fintype.ofFinite _
  have h := OddOrder.Isaacs.Ch06.IsFrobeniusAction.involution_smul_eq_inv
    (A := ↥(pairStab G inf zero)) (N := ↥U)
    (isFrobeniusAction_conj hUB hN hfree) ht1 ht2 u
  have h2 : conjSmul hUB hN t u = u⁻¹ := h
  rw [← conjSmul_coe hUB hN t u, h2, Subgroup.coe_inv]

/-- **Isaacs Cor 6.17.**  An abelian Frobenius complement is cyclic. -/
theorem isCyclic_of_isMulCommutative_of_free [Finite U] (hUB : U ≤ borel G inf)
    (hN : (U.subgroupOf (borel G inf)).Normal)
    (hfree : FixedPointFreeConj U (pairStab G inf zero))
    (hcomm : IsMulCommutative ↥(pairStab G inf zero)) (hnt : Nontrivial ↥U) :
    IsCyclic ↥(pairStab G inf zero) := by
  letI := conjMulDistribMulAction (G := G) (inf := inf) (zero := zero) hUB hN
  letI : Fintype ↥(pairStab G inf zero) := Fintype.ofFinite _
  letI : Fintype ↥U := Fintype.ofFinite _
  letI : IsMulCommutative ↥(pairStab G inf zero) := hcomm
  exact OddOrder.Isaacs.Ch06.isCyclic_of_frobeniusAction_of_isMulCommutative
    (A := ↥(pairStab G inf zero)) (U := ↥U) (isFrobeniusAction_conj hUB hN hfree)

/-- **Isaacs Cor 6.18 / HB V 8.7.**  A Frobenius complement of odd order is a Z-group: all its
Sylow subgroups are cyclic. -/
theorem isZGroup_of_odd_of_free [Finite U] (hUB : U ≤ borel G inf)
    (hN : (U.subgroupOf (borel G inf)).Normal)
    (hfree : FixedPointFreeConj U (pairStab G inf zero))
    (hodd : Odd (Nat.card (pairStab G inf zero))) (hnt : Nontrivial ↥U) :
    IsZGroup ↥(pairStab G inf zero) := by
  letI := conjMulDistribMulAction (G := G) (inf := inf) (zero := zero) hUB hN
  letI : Fintype ↥(pairStab G inf zero) := Fintype.ofFinite _
  letI : Fintype ↥U := Fintype.ofFinite _
  exact OddOrder.Isaacs.Ch06.isZGroup_of_isFrobeniusAction_of_odd
    (A := ↥(pairStab G inf zero)) (U := ↥U) (isFrobeniusAction_conj hUB hN hfree)
    (by simpa [Nat.card_eq_fintype_card] using hodd)

end Consequences

end Work.ZASS
