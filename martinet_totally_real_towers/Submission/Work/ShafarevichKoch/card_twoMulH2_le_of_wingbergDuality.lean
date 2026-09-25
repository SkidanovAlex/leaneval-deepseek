import Mathlib
import Submission.Work.ShafarevichKoch.WingbergDefs
import Submission.Work.ShafarevichKoch.CountZ
import Submission.Work.ShafarevichKoch.KcArithmetic
import Submission.Work.ShafarevichKoch.card_twoTorsion_dual_eq_card_twoTorsion
import Submission.Work.ShafarevichKoch.card_quotient_two_eq_card_twoTorsion

/-!
# `Work.ShafarevichKoch.card_twoMulH2_le_of_wingbergDuality`

Wingberg's duality (`Work.ShafarevichKoch.WingbergDuality`, Neukirch--Schmidt--Wingberg Ch. VIII
§8 Theorem 8.8.1 together with NSW Ch. VIII §8 Lemma 8.8.4) identifies the Pontryagin dual of
`H²(G_∅,ℤ)` with the `2`-primary part `Cl(Kc) ⊗ ℤ₂` of the class group of `Kc = ℚ(√-30030)`.

The `2`-rank of `H²(G_∅,ℤ)` is the cardinality of its `2`-torsion (equivalently of the quotient
by the subgroup `2·H²(G_∅,ℤ)` of doubles, since `H²(G_∅,ℤ)` is finite).  The dual of an abelian
group has the same `2`-torsion count, and the `2`-torsion of `Cl(Kc) ⊗ ℤ₂` is the `2`-torsion of
`Cl(Kc)`, which has `2 ^ 5 = 32` elements.  Hence

`#(H²(G_∅,ℤ) ⧸ 2·H²(G_∅,ℤ)) ≤ 2 ^ 5`.

This is the numerical content of `WingbergDuality` that the Shafarevich--Koch relation count
(`Work.ShafarevichKoch.CountZ`) consumes.

## Main declarations

* `Work.ShafarevichKoch.card_twoMulH2_le_of_wingbergDuality`.

## Note

The (orphaned, not imported by anything) module `Submission.Work.ShafarevichKoch.WingbergInput`
contains an inlined copy of this same declaration (together with
`Work.ShafarevichKoch.card_twoTorsionH3_le_of_wingbergDuality`), so it must **not** be imported
together with this module: the two would clash on the declaration name.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 16000000
set_option synthInstance.maxHeartbeats 2000000

open scoped Classical

noncomputable section

namespace Work.ShafarevichKoch

open Work.ClassFieldTower
open Work.ConCohomology

/-- Wingberg's duality (`Work.ShafarevichKoch.WingbergDuality`) gives that the Pontryagin dual of
`H²(G_∅,ℤ)` is the `2`-primary part of `Cl(Kc)`, so the `2`-rank of `H²(G_∅,ℤ)` — i.e. the
cardinality of its `2`-torsion or, equivalently, of the quotient by `2H²(G_∅,ℤ)` — is at most
`2^5 = #Cl(Kc)[2]`. -/
theorem card_twoMulH2_le_of_wingbergDuality
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Work.ClassFieldTower.Kc 2)
    (h : Work.ShafarevichKoch.WingbergDuality M) :
    Nat.card (Work.ConCohomology.H2 (Work.ClassFieldTower.galoisGroup M) ℤ ⧸
      Work.ShafarevichKoch.twoMulH2 (Work.ClassFieldTower.galoisGroup M)) ≤ 2 ^ 5 := by
  -- finiteness of `H²(G_∅,ℤ)` (part of the classical setting) and the duality isomorphism
  haveI : Finite (H2 (galoisGroup M) ℤ) := h.1
  haveI : Fintype (H2 (galoisGroup M) ℤ) := Fintype.ofFinite _
  obtain ⟨e⟩ := h.2.2.1
  haveI : Fintype (ClassGroup (NumberField.RingOfIntegers Kc)) := Fintype.ofFinite _
  -- the quotient by the doubles has as many elements as the `2`-torsion
  have hquot : Nat.card (H2 (galoisGroup M) ℤ ⧸ twoMulH2 (galoisGroup M)) =
      Nat.card {a : H2 (galoisGroup M) ℤ // (2 : ℕ) • a = 0} :=
    card_quotient_two_eq_card_twoTorsion _
  -- the dual has the same `2`-torsion as the group
  have hdual : Nat.card {a : H2 (galoisGroup M) ℤ // (2 : ℕ) • a = 0} =
      Nat.card {φ : PDual (H2 (galoisGroup M) ℤ) // (2 : ℕ) • φ = 0} :=
    (card_twoTorsion_dual_eq_card_twoTorsion (H2 (galoisGroup M) ℤ)).symm
  -- transport along the duality isomorphism
  have hiso : Nat.card {φ : PDual (H2 (galoisGroup M) ℤ) // (2 : ℕ) • φ = 0} =
      Nat.card {y : Additive Cl2Part // (2 : ℕ) • y = 0} :=
    card_twoTorsion_addEquiv (A := PDual (H2 (galoisGroup M) ℤ)) (B := Additive Cl2Part) e
  -- `2`-torsion of `Cl(Kc) ⊗ ℤ₂` is the `2`-torsion of `Cl(Kc)`
  have hprim : Nat.card {y : Additive Cl2Part // (2 : ℕ) • y = 0} =
      Nat.card {x : Cl2Part // x ^ 2 = 1} :=
    card_twoTorsion_additive Cl2Part
  have hpart : Nat.card {x : Cl2Part // x ^ 2 = 1} =
      Nat.card {x : ClassGroup (NumberField.RingOfIntegers Kc) // x ^ 2 = 1} :=
    card_twoTorsion_twoPrimaryPart (ClassGroup (NumberField.RingOfIntegers Kc))
  have hKc : Nat.card {x : ClassGroup (NumberField.RingOfIntegers Kc) // x ^ 2 = 1} = 32 :=
    card_twoTorsion_classGroup_Kc
  calc Nat.card (H2 (galoisGroup M) ℤ ⧸ twoMulH2 (galoisGroup M))
      = Nat.card {a : H2 (galoisGroup M) ℤ // (2 : ℕ) • a = 0} := hquot
    _ = Nat.card {φ : PDual (H2 (galoisGroup M) ℤ) // (2 : ℕ) • φ = 0} := hdual
    _ = Nat.card {y : Additive Cl2Part // (2 : ℕ) • y = 0} := hiso
    _ = Nat.card {x : Cl2Part // x ^ 2 = 1} := hprim
    _ = Nat.card {x : ClassGroup (NumberField.RingOfIntegers Kc) // x ^ 2 = 1} := hpart
    _ = 32 := hKc
    _ ≤ 2 ^ 5 := by norm_num

end Work.ShafarevichKoch
