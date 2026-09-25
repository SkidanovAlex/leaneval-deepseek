import Mathlib
import Submission.Work.ShafarevichKoch.WingbergDefs
import Submission.Work.ShafarevichKoch.CountZ
import Submission.Work.ShafarevichKoch.KcArithmetic
import Submission.Work.ShafarevichKoch.card_twoTorsion_dual_eq_card_twoTorsion

/-!
# `Work.ShafarevichKoch.card_twoTorsionH3_le_of_wingbergDuality`

**From Wingberg's duality for `Kc = ℚ(√-30030)`, the `2`-torsion of `H³(G_∅,ℤ)` has at most two
elements.**

Wingberg's duality (`Work.ShafarevichKoch.WingbergDuality`, Neukirch--Schmidt--Wingberg Ch. VIII §8
Thm. 8.8.1 together with Lemma 8.8.4, in the normalisation of Hajir--Maire--Ramakrishna
`arXiv:2103.09508` §1.2) identifies the Pontryagin dual of `H³(G_∅,ℤ)` with the universal-norm
quotient `Ĥ⁰(G_∅,O_{K_∅}^×)` of the units, which is a quotient of `(𝓞 Kc)ˣ = {±1}`:

```
PDual (H³(G_∅,ℤ)) ≅ Additive ((𝓞 Kc)ˣ ⧸ N)        for some N ≤ (𝓞 Kc)ˣ .
```

Since every unit of `𝓞 Kc` is `±1` (`Work.ShafarevichKoch.card_RingUnit_Kc_le_two`, proved from the
norm form `x² + 30030 y²` of `Kc`, `Kc_unit_eq_or_eq_neg`), the quotient has at most two elements,
so its `2`-torsion has at most two elements; by the counting form of double duality for finite
abelian groups, `#A[2] = #(A^∨)[2]`
(`Work.ShafarevichKoch.card_twoTorsion_dual_eq_card_twoTorsion`), the same holds for
`H³(G_∅,ℤ)[2]`.

The proof is the four-step chain

```
#H³(G_∅,ℤ)[2] = #(PDual H³(G_∅,ℤ))[2] = #(Additive ((𝓞 Kc)ˣ ⧸ N))[2]
               ≤ #((𝓞 Kc)ˣ ⧸ N) ≤ #(𝓞 Kc)ˣ ≤ 2 .
```

## Main declarations

* `Work.ShafarevichKoch.card_twoTorsionH3_le_of_wingbergDuality`;
* the bookkeeping lemmas `Work.ShafarevichKoch.card_twoTorsion_additive_le`,
  `Work.ShafarevichKoch.card_quotient_le_of_subgroup` and the general form
  `Work.ShafarevichKoch.card_twoTorsion_of_dual_quotient_le`.

## Note for the caller

`Submission/Work/ShafarevichKoch/WingbergInput.lean` contains an earlier draft of this same
reduction.  It no longer compiles on its own (it redefines `Work.ShafarevichKoch.WingbergDuality`,
which now lives in `WingbergDefs.lean`), and it declares `card_twoTorsionH3_le_of_wingbergDuality`
(and `card_twoTorsion_additive_le`, `card_quotient_le_of_subgroup`) under the same names as this
module.  Do not import the two together; this module is self-contained and proves the reduction.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open scoped Classical
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

open Work.ClassFieldTower
open Work.ConCohomology

/-! ## Bookkeeping of `2`-torsion, additive isomorphisms and quotients -/

/-- The `2`-torsion of the additive group of a finite commutative group `B` has at most as many
elements as `B`: the map `x ↦ Additive.toMul x` is injective. -/
theorem card_twoTorsion_additive_le (B : Type*) [CommGroup B] [Finite B] :
    Nat.card {x : Additive B // (2 : ℕ) • x = 0} ≤ Nat.card B := by
  haveI : Finite (Additive B) :=
    Finite.of_surjective (fun b : B => Additive.ofMul b) (fun y => ⟨Additive.toMul y, rfl⟩)
  calc Nat.card {x : Additive B // (2 : ℕ) • x = 0} ≤ Nat.card (Additive B) :=
        Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    _ = Nat.card B :=
        Nat.card_congr (Equiv.mk Additive.toMul Additive.ofMul (fun _ => rfl) (fun _ => rfl))

/-- A quotient of a finite commutative group is no larger than the group. -/
theorem card_quotient_le_of_subgroup {A : Type*} [CommGroup A] [Finite A] (N : Subgroup A) :
    Nat.card (A ⧸ N) ≤ Nat.card A :=
  Nat.card_le_card_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

/-- **General form of the count.**  If the Pontryagin dual of a finite abelian group `A` is
isomorphic to a quotient `B ⧸ N` of a commutative group `B`, then the `2`-torsion of `A` has at
most as many elements as `B`.

Indeed `A[2]` has the same cardinality as the `2`-torsion of the dual `PDual A`
(`card_twoTorsion_dual_eq_card_twoTorsion`), the additive isomorphism carries the `2`-torsion onto
the `2`-torsion of `B ⧸ N` (`card_twoTorsion_addEquiv`), and the `2`-torsion of a group is no
larger than the group, which in turn is no larger than `B`. -/
theorem card_twoTorsion_of_dual_quotient_le {A : Type*} [AddCommGroup A] [Fintype A]
    {B : Type*} [CommGroup B] [Finite B] (N : Subgroup B)
    (e : PDual A ≃+ Additive (B ⧸ N)) :
    Nat.card {x : A // (2 : ℕ) • x = 0} ≤ Nat.card B := by
  calc Nat.card {x : A // (2 : ℕ) • x = 0}
      = Nat.card {φ : PDual A // (2 : ℕ) • φ = 0} :=
        (card_twoTorsion_dual_eq_card_twoTorsion A).symm
    _ = Nat.card {y : Additive (B ⧸ N) // (2 : ℕ) • y = 0} :=
        card_twoTorsion_addEquiv (A := PDual A) (B := Additive (B ⧸ N)) e
    _ ≤ Nat.card (B ⧸ N) := card_twoTorsion_additive_le (B ⧸ N)
    _ ≤ Nat.card B := card_quotient_le_of_subgroup N

/-! ## The `2`-torsion of `H³(G_∅,ℤ)` -/

/-- Wingberg's duality (`Work.ShafarevichKoch.WingbergDuality`) identifies the Pontryagin dual of
`H³(G_∅,ℤ)` with the universal-norm quotient of the units of `Kc_∅`, which is a quotient of
`(𝓞 Kc)ˣ = {±1}`; hence the `2`-torsion of `H³(G_∅,ℤ)` has at most two elements. -/
theorem card_twoTorsionH3_le_of_wingbergDuality
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Work.ClassFieldTower.Kc 2)
    (h : Work.ShafarevichKoch.WingbergDuality M) :
    Nat.card (Work.ShafarevichKoch.twoTorsionH3 (Work.ClassFieldTower.galoisGroup M)) ≤ 2 := by
  obtain ⟨N, hN⟩ := h.2.2.2
  obtain ⟨e⟩ := hN
  haveI hfin3 : Finite (H3 (Work.ClassFieldTower.galoisGroup M) ℤ) := h.2.1
  haveI : Fintype (H3 (Work.ClassFieldTower.galoisGroup M) ℤ) := Fintype.ofFinite _
  haveI : Finite (RingUnit Work.ClassFieldTower.Kc) := finite_RingUnit_Kc
  exact (card_twoTorsion_of_dual_quotient_le (A := H3 (Work.ClassFieldTower.galoisGroup M) ℤ)
    (B := RingUnit Work.ClassFieldTower.Kc) N e).trans card_RingUnit_Kc_le_two

end Work.ShafarevichKoch
