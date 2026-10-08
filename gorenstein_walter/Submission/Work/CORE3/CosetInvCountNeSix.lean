import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.Case1bEightNineDefs
import Submission.Work.CORE3.CosetInvCountBasic
import Submission.Work.CORE3.RelIndexHHhat
import Submission.Work.CORE3.CosetInvCountLeSix
import Submission.Work.CORE3.CosetInvCountNeFive
import Submission.Work.CORE3.BenderSeven
import Submission.Work.CORE3.CosetInvCountNeSixOf
import Submission.Work.CORE3.SixInvSetElements
import Submission.Work.CORE3.SixInvSetMulTable
import Submission.Work.CORE3.J4.J4CosetStep

/-!
# Bender 1981 §3, items (6) and (7): a coset of `Ĥ` does not carry exactly six involutions

This module is the leaf `Work.CORE3.CosetInvCountNeSix` of the area's split of Bender's §3b,
i.e. Bender's Theorem 2.6 alternatives: for every involution `y ∉ Ĥ`,
`cosetInvCount Ĥ y ≠ 6`.

The proof uses Bender's pair of steps (6) and (7) of *Finite groups with dihedral Sylow
2-subgroups*, J. Algebra **70** (1981), p. 224.

* **Bender (6)**, in the case `n = 6` needed here, is proved directly: by
  `Work.CORE3.SixInvSetElements` the inverted set `I_Ĥ(y)` contains an element `a` of order `3`
  and distinct involutions `b₁, b₂`; by `Work.CORE3.SixInvSetMulTable` one has
  `b₁ * a * b₁ = a⁻¹` and `(b₁ * b₂)^3 = 1`.  Hence `X := ⟨a⟩` is a nontrivial odd-order
  subgroup of `Ĥ` inverted by `y`, whose normalizer contains the involution `y` (even order) and
  whose centralizer contains the involution `b₁ * y` (even order: `y b₁ y = b₁` makes `b₁ * y` an
  involution, and `b₁ * a * b₁ = a⁻¹` makes it centralize `a`).
  The case `n = 5` is excluded by `Work.CORE3.CosetInvCountNeFive` and `n ≤ 6` by
  `Work.CORE3.cosetInvCount_le_six`, so `5 ≤ cosetInvCount Ĥ y` forces `cosetInvCount Ĥ y = 6`.
* **Bender (7)** (`Work.CORE3.BenderSeven`): for such an `X`, `|U| = 3` and `|Ĥ ⊓ Ĥ^y| = 6`.

These two steps give the result through `Work.CORE3.cosetInvCount_ne_six_of`: the count is a
coset invariant, so `I_Ĥ(z)` has six elements and lies in the six-element group
`D = Ĥ ⊓ Ĥ^z`; hence `D = I_Ĥ(z)`, which is inverted elementwise by `z` and closed under
multiplication, so `D` is abelian; an abelian group of order `6` has an element `x` of order `6`,
and since `x ∈ I_Ĥ(z)` the orders of `x` and of its image in `Ĥ/VU` agree (Bender (5)), so the
quotient of order `6` would be cyclic, contradicting the non-abelian alternative of Theorem 2.6.
-/

namespace Work.CORE3

open Work.GW2
open Subgroup

/-- **Bender (6) for `n = 6`**, with Bender's `N_Ĥ(X)` witness.  If the coset of the involution
`y ∉ Ĥ` carries at least five involutions (hence, by (5) and `n ≠ 5`, exactly six), then some
involution `z = k * y` of that coset inverts a nontrivial odd-order subgroup `X ≤ Ĥ` whose
`G`-centralizer and `G`-normalizer have even order, and `X` is inverted by an involution of `Ĥ`
as well — namely `b₁` of `Work.CORE3.SixInvSetElements`, whose inversion of the generator `a`
of `X` is `hconj1` from `Work.CORE3.SixInvSetMulTable`.  This extra conjunct is Bender's
`N_Ĥ(X)` hypothesis in step (7), needed by `Work.CORE3.D23.J4U3V18s`; the older statement
without it is `Work.CORE3.BenderSixNeSixAux` below. -/
theorem BenderSixNeSixAuxS (G : Type) [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (h : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B)
    (h5 : ∀ z : G, orderOf z = 2 → z ∉ B.Hhat →
      Work.GW2.invSet (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) z = {1}) :
    ∀ y : G, orderOf y = 2 → y ∉ B.Hhat → 5 ≤ Work.GW2.cosetInvCount B.Hhat y →
      ∃ z : G, orderOf z = 2 ∧ (∃ k ∈ B.Hhat, z = k * y) ∧
        ∃ X : Subgroup G, X ≤ B.Hhat ∧ X ≠ ⊥ ∧ Odd (Nat.card ↥X) ∧ Work.GW2.Inverts z X ∧
          Even (Nat.card (Subgroup.centralizer (X : Set G))) ∧
          Even (Nat.card (Subgroup.normalizer (X : Set G))) ∧
          (∃ s ∈ B.Hhat, orderOf s = 2 ∧ Work.GW2.Inverts s X) := by
  intro y hy2 hyH hbig
  have hy : y * y = 1 := ((orderOf_eq_two_iff_mul_self y).mp hy2).1
  have hyne : y ≠ 1 := ((orderOf_eq_two_iff_mul_self y).mp hy2).2
  have hle6 : Work.GW2.cosetInvCount B.Hhat y ≤ 6 :=
    cosetInvCount_le_six G I h B h1 D h5 y hy2 hyH
  have hne5 : Work.GW2.cosetInvCount B.Hhat y ≠ 5 :=
    CosetInvCountNeFive G I h B h1 D h5 y hy2 hyH
  have h6 : Work.GW2.cosetInvCount B.Hhat y = 6 := by omega
  obtain ⟨a, b1, b2, ha, ha3, hb1, hb1o, hb2, hb2o, hb12⟩ :=
    SixInvSetElements G I h B h1 D h5 y hy2 hyH h6
  obtain ⟨hconj1, hcube⟩ :=
    SixInvSetMulTable G I h B h1 D h5 y hy2 hyH h6 a b1 b2 ha ha3 hb1 hb1o hb2 hb2o hb12
  -- `y` inverts `a`, and `y` inverts (hence centralizes) the involution `b₁`
  have hyinv : y⁻¹ = y := inv_eq_of_sq_eq_one hy
  have hb1_sq : b1 * b1 = 1 := ((orderOf_eq_two_iff_mul_self b1).mp hb1o).1
  have hb1_ne : b1 ≠ 1 := ((orderOf_eq_two_iff_mul_self b1).mp hb1o).2
  have hb1inv : b1⁻¹ = b1 := inv_eq_of_sq_eq_one hb1_sq
  have ha_inv : y * a * y⁻¹ = a⁻¹ := by
    rw [hyinv]; exact ha.2
  have hya : y * b1 * y⁻¹ = b1 := by
    rw [hyinv, hb1.2, hb1inv]
  have hya' : y * b1 = b1 * y := by
    have h := congrArg (fun z => z * y) hya
    simpa [mul_assoc] using h
  -- the auxiliary involution `w = b₁ * y`
  have hw2 : (b1 * y) * (b1 * y) = 1 := by
    calc (b1 * y) * (b1 * y) = b1 * (y * b1) * y := by group
      _ = b1 * (b1 * y) * y := by rw [hya']
      _ = (b1 * b1) * (y * y) := by group
      _ = 1 := by rw [hb1_sq, hy, mul_one]
  have hw1 : b1 * y ≠ 1 := by
    intro hcon
    have h : y = b1 := by
      have h2 : b1 * (b1 * y) = b1 := by
        simpa using congrArg (fun z => b1 * z) hcon
      rw [← mul_assoc, hb1_sq, one_mul] at h2
      exact h2
    exact hyH (by rw [h]; exact hb1.1)
  have hwa : (b1 * y) * a * (b1 * y)⁻¹ = a := by
    have h1 : (b1 * y) * a * (b1 * y)⁻¹ = b1 * (y * a * y⁻¹) * b1 := by
      rw [mul_inv_rev, hyinv, hb1inv]
      group
    rw [h1, ha_inv]
    have h2 : b1 * a⁻¹ * b1 = (b1 * a * b1)⁻¹ := by
      rw [mul_inv_rev, mul_inv_rev, hb1inv, mul_assoc]
    rw [h2, hconj1, inv_inv]
  refine ⟨y, hy2, ⟨1, B.Hhat.one_mem, by rw [one_mul]⟩, Subgroup.zpowers a,
    Subgroup.zpowers_le.mpr ha.1, ?_, ?_, Work.CORE3.J4.inverts_zpowers_of ha_inv, ?_, ?_, ?_⟩
  · intro hbot
    have hmem : a ∈ (Subgroup.zpowers a : Subgroup G) := Subgroup.mem_zpowers a
    rw [hbot] at hmem
    have ha1 : a = 1 := by simpa using hmem
    have : orderOf a = 1 := by rw [ha1]; exact orderOf_one
    omega
  · rw [Nat.card_zpowers, ha3]
    decide
  · have hmem : b1 * y ∈ Subgroup.centralizer (Subgroup.zpowers a : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      have hconjm : MulAut.conj (b1 * y) a = a := by
        rw [MulAut.conj_apply]; exact hwa
      have hpow : (b1 * y) * a ^ n * (b1 * y)⁻¹ = a ^ n := by
        have h1 : (b1 * y) * a ^ n * (b1 * y)⁻¹ = (MulAut.conj (b1 * y)) (a ^ n) := by
          rw [MulAut.conj_apply]
        rw [h1, map_zpow, hconjm]
      calc a ^ n * (b1 * y) = ((b1 * y) * a ^ n * (b1 * y)⁻¹) * (b1 * y) := by rw [hpow]
        _ = (b1 * y) * a ^ n := by group
    exact Work.CORE3.J4.even_card_centralizer_of_involution (X := Subgroup.zpowers a)
      (w := b1 * y) hw2 hw1 hmem
  · exact Work.CORE3.J4.even_card_normalizer_of_inverts (X := Subgroup.zpowers a) hy hyne
      (Work.CORE3.J4.inverts_zpowers_of ha_inv)
  · exact ⟨b1, hb1.1, hb1o,
      Work.CORE3.J4.inverts_zpowers_of (by rw [hb1inv]; exact hconj1)⟩

/-- **Bender (6) for `n = 6`**, in the older form without the `N_Ĥ(X)` witness: the projection of
`Work.CORE3.BenderSixNeSixAuxS` forgetting the last conjunct. -/
theorem BenderSixNeSixAux (G : Type) [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (h : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B)
    (h5 : ∀ z : G, orderOf z = 2 → z ∉ B.Hhat →
      Work.GW2.invSet (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) z = {1}) :
    ∀ y : G, orderOf y = 2 → y ∉ B.Hhat → 5 ≤ Work.GW2.cosetInvCount B.Hhat y →
      ∃ z : G, orderOf z = 2 ∧ (∃ k ∈ B.Hhat, z = k * y) ∧
        ∃ X : Subgroup G, X ≤ B.Hhat ∧ X ≠ ⊥ ∧ Odd (Nat.card ↥X) ∧ Work.GW2.Inverts z X ∧
          Even (Nat.card (Subgroup.centralizer (X : Set G))) ∧
          Even (Nat.card (Subgroup.normalizer (X : Set G))) := by
  intro y hy2 hyH hbig
  obtain ⟨z, hz2, hk, X, hXle, hXne, hXodd, hinv, hC, hN, _hs⟩ :=
    BenderSixNeSixAuxS G I h B h1 D h5 y hy2 hyH hbig
  exact ⟨z, hz2, hk, X, hXle, hXne, hXodd, hinv, hC, hN⟩

theorem CosetInvCountNeSix (G : Type) [Group G] [Finite G] (I : Work.CORE3.Case1Inputs) (h : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B) (D : Work.GW2.Case1bData B)
    (h5 : ∀ z : G, orderOf z = 2 → z ∉ B.Hhat →
      Work.GW2.invSet (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) z = {1}) :
    ∀ y : G, orderOf y = 2 → y ∉ B.Hhat → Work.GW2.cosetInvCount B.Hhat y ≠ 6 :=
  cosetInvCount_ne_six_of G I h B h1 D h5
    (fun y hy2 hyH hbig => BenderSixNeSixAuxS G I h B h1 D h5 y hy2 hyH hbig)
    (fun y X hy2 hyH hXle hXne hXodd hinv hC hN s hsH hs2 hsX =>
      BenderSeven G I h B h1 D hy2 hyH X hXle hXne hXodd hinv hC hN (s := s) hsH hs2 hsX)

end Work.CORE3
