/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area ZASS: steps Z2–Z4 assembled

From a Zassenhaus action (`Work.GW2.ZassHyps2`, `q = p^k`, `p` odd, `q ≥ 5`) we obtain, for
any two chosen points `∞ ≠ 0`, a subgroup `U` with all the structure of steps Z2–Z4:

* `U` is the normal Sylow `p`-subgroup of `B = G_∞`, of order `q`, and `B = U ⋊ H` with
  `H = G_{∞0}` (Z2);
* `H` acts fixed-point-freely on `U` and `u ↦ u • 0` is a bijection `U ≃ X ∖ {∞}` (Z3);
* `U` is abelian of exponent `p` (Z4).

Step Z5 (the field coordinates on `U`, needed by Z6) is `Work.ZASS.exists_field_coordinates`,
which additionally assumes the cyclicity of `H` supplied by `Work.GW2.ZassInvertProp`.
-/
import Mathlib
import Submission.Work.ZASS.Defs
import Submission.Work.ZASS.Basic
import Submission.Work.ZASS.Z2Unipotent
import Submission.Work.ZASS.Z3Free
import Submission.Work.ZASS.equiv_unipotent_compl
import Submission.Work.ZASS.isMulCommutative_of_zass
import Submission.Work.ZASS.exponent_dvd_p_of_zass
import Submission.Work.ZASS.exists_field_coordinates

open scoped MatrixGroups

namespace Work.ZASS

open Work.GW2 (ZassHyps2 ZassInvertProp)
open Work.Zassenhaus (borel pairStab fixesOnly fixesSome)

/-- **Z2–Z4 assembled.**  The structure of the point stabilizer `B = G_∞`, its unipotent
radical `U` and its torus `H = G_{∞0}` in the Zassenhaus setting. -/
theorem exists_unipotent_structure {G X : Type} [Group G] [Finite G] [MulAction G X]
    [Finite X] {p k : ℕ} [Fact p.Prime] (hp : Odd p) (hq : 5 ≤ p ^ k)
    (h : ZassHyps2 G X (p ^ k)) {inf zero : X} (hne : inf ≠ zero) :
    ∃ U : Subgroup G, U ≤ borel G inf ∧ Nat.card U = p ^ k ∧
      (U.subgroupOf (borel G inf)).Normal ∧
      IsDirectDecomp (borel G inf) U (pairStab G inf zero) ∧
      FixedPointFreeConj U (pairStab G inf zero) ∧
      (∃ Φ : U ≃ {x : X // x ≠ inf}, ∀ u : U, (Φ u : X) = (u : G) • zero) ∧
      IsMulCommutative U ∧ (∀ u ∈ U, u ^ p = 1) := by
  obtain ⟨U, hUB, hcardU, hN, hdec⟩ := exists_unipotent hp hq h hne
  have hcardH : Nat.card (pairStab G inf zero) = (p ^ k - 1) / 2 := card_pairStab h hne
  have hfree : FixedPointFreeConj U (pairStab G inf zero) :=
    fixedPointFreeConj_pairStab hp h rfl hne hUB hcardU hcardH
  have hequiv := equiv_unipotent_compl (U := U) hne hUB hcardU hcardH hdec.2 h.2.1
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [hk0, pow_zero] at hq; omega
    · exact hkpos
  have hcomm : IsMulCommutative U :=
    isMulCommutative_of_zass hp hk rfl hUB hcardU hcardH hN hfree
  have hexp : ∀ u ∈ U, u ^ p = 1 :=
    exponent_dvd_p_of_zass hp hk rfl hUB hcardU hcardH hN hcomm hfree
  exact ⟨U, hUB, hcardU, hN, hdec, hfree, hequiv, hcomm, hexp⟩

/-- The cyclicity of `H = G_{∞0}` required by Z5, extracted from the leaf proposition
`Work.GW2.ZassInvertProp` (HB III XI 1.5 for `d` odd, 1.11 for `d` even). -/
theorem isCyclic_pairStab_of_zassInvert {G X : Type} [Group G] [Finite G] [MulAction G X]
    [Finite X] (hInv : ZassInvertProp) {q : ℕ} (hqodd : Odd q) (hq : 5 ≤ q)
    (hs : IsSimpleGroup G) (h : ZassHyps2 G X q) {inf zero : X} (hne : inf ≠ zero) :
    IsCyclic (pairStab G inf zero) := by
  have h1 : IsCyclic (MulAction.stabilizer G inf ⊓ MulAction.stabilizer G zero : Subgroup G) :=
    (hInv G X q hqodd hq hs h inf zero hne).1
  have h2 : (MulAction.stabilizer G inf ⊓ MulAction.stabilizer G zero : Subgroup G) =
      pairStab G inf zero := by
    rw [Work.Zassenhaus.pairStab, inf_comm]
  rwa [h2] at h1

end Work.ZASS
