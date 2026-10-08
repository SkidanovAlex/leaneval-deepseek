/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area ZASS: step Z2, the Borel subgroup and its unipotent radical

Assembly of the Z2 lemmas: for a Zassenhaus action (`Work.GW2.ZassHyps2`) with `q = p^k`,
`p` odd, `q ≥ 5`, the Borel subgroup `B = G_∞ = U ⋊ H` where `U` is the Sylow `p`-subgroup
of `B` (of order `q`, normal in `B`, regular on `X ∖ {∞}`) and `H = G_{∞0}` is the two-point
stabilizer.
-/
import Mathlib
import Submission.Work.ZASS.Defs
import Submission.Work.ZASS.Basic
import Submission.Work.ZASS.card_borel
import Submission.Work.ZASS.card_G
import Submission.Work.ZASS.ncard_fixesSome
import Submission.Work.ZASS.ncard_fixesOnly
import Submission.Work.ZASS.card_sylow_borel
import Submission.Work.ZASS.mem_fixesOnly_of_mem_unipotent
import Submission.Work.ZASS.normal_of_card_eq_mem_fixesOnly
import Submission.Work.ZASS.isDirectDecomp_of_card

open scoped MatrixGroups

namespace Work.ZASS

open Work.GW2 (ZassHyps2)
open Work.Zassenhaus (borel pairStab fixesOnly fixesSome)

/-- **Z2.** The Borel subgroup `B = G_∞` of a Zassenhaus action has a normal Sylow
`p`-subgroup `U` of order `q = p^k`, and `B = U ⋊ H` with `H = G_{∞0}`. -/
theorem exists_unipotent {G X : Type} [Group G] [Finite G] [MulAction G X] [Finite X]
    {p k : ℕ} [Fact p.Prime] (hp : Odd p) (hq : 5 ≤ p ^ k)
    (h : ZassHyps2 G X (p ^ k)) {inf zero : X} (hne : inf ≠ zero) :
    ∃ U : Subgroup G, U ≤ borel G inf ∧ Nat.card U = p ^ k ∧
      (U.subgroupOf (borel G inf)).Normal ∧
      IsDirectDecomp (borel G inf) U (pairStab G inf zero) := by
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [hk0, pow_zero] at hq; omega
    · exact hkpos
  have hB : Nat.card (borel G inf) = p ^ k * ((p ^ k - 1) / 2) := card_borel h hne
  have hsome : (fixesSome G inf).ncard = 1 + p ^ k * ((p ^ k - 1) / 2 - 1) :=
    ncard_fixesSome h hne hB
  have hfixOnly : (fixesOnly G inf).ncard = p ^ k - 1 := ncard_fixesOnly h hne hB hsome
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p (borel G inf)))
  set U : Subgroup G := (P : Subgroup (borel G inf)).map (borel G inf).subtype with hUdef
  have hUB : U ≤ borel G inf := hUdef ▸ Subgroup.map_subtype_le _
  have hcardU : Nat.card U = p ^ k := hUdef ▸ card_sylow_borel hp rfl hB P
  have hcardH : ∀ y : X, y ≠ inf → Nat.card (pairStab G inf y) = (p ^ k - 1) / 2 :=
    fun y hy => card_pairStab h (inf := inf) (zero := y) (Ne.symm hy)
  have hN : (U.subgroupOf (borel G inf)).Normal :=
    normal_of_card_eq_mem_fixesOnly hUB hcardU
      (fun u hu hu1 => mem_fixesOnly_of_mem_unipotent (q := p ^ k) hp rfl hUB hcardU hcardH hu hu1)
      hfixOnly
  have hHle : pairStab G inf zero ≤ borel G inf := Work.Zassenhaus.pairStab_le_borel inf zero
  have hdec : IsDirectDecomp (borel G inf) U (pairStab G inf zero) :=
    isDirectDecomp_of_card hUB hHle hcardU (card_pairStab h hne) hB
      (Work.Zassenhaus.zass_coprime_pow_half (Fact.out) hp hk) hN
  exact ⟨U, hUB, hcardU, hN, hdec⟩

end Work.ZASS
