import Mathlib
import Submission.Work.GLUE.Defs
import Submission.Work.BG.ThmABCDefs
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.B_normalizes_K
import Submission.Work.BG.thmCSec3
import Submission.Work.BG.indexEqCardOfNormalSup
import Submission.Work.BG.relIndex_sup_eq_card_of_inf_eq_bot
import Submission.Work.BG.B2_eq_B

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Subgroup

/-- Under the hypotheses `Work.GW2.C16.ThmCHyps D K1 K2` of Bender–Glauberman's Theorem C, the
number `|K₁ ⊓ K₂|` divides `|U : B₂|` (the `t₂`-analogue of `Work.BG.cardKdvdRelIndexUB1`;
`2 * |K₁ ⊓ K₂|` divides `k = k₁ + k₂`, BG p. 211).

Route.  Let `K = K₁ ⊓ K₂`, `B = B₁ ⊓ B₂`, `C = B ⊔ K`.  Exactly as in `cardKdvdRelIndexUB1`
(`B` normalizes `K` by maximality of the `Kᵢ`, so `C = B * K` with `B ⊓ K = ⊥`, and `C ⊓ B₂ = B`
since `t₂ * (b * k) * t₂ = b * k⁻¹` for `b ∈ B`, `k ∈ K` because `B ≤ B₂` and `t₂` inverts
`K ≤ K₂`), one has `|C : B| = |K|` and `C ⊓ B₂ = B`.  Since `B₂ ≤ U` and `C ≤ U` (from
`U = (B₁ ⊓ K₂) ⊔ C`), the tower `|U : B₂| = |U : B₂ ⊔ C| * |B₂ ⊔ C : B₂|` together with
`Subgroup.relIndex_sup_left` (`(B₂ ⊔ C).relIndex B₂ = C.relIndex (B₂ ⊓ C) = C.relIndex B = |K|`)
gives the divisibility. -/
theorem cardKdvdRelIndexUB2 {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G)
    (K1 K2 : Subgroup G) (hHyps : Work.GW2.C16.ThmCHyps D K1 K2) :
    Nat.card (K1 ⊓ K2 : Subgroup G) ∣ D.B2.relIndex D.U := by
  -- Under the Theorem C hypotheses `B₂ = B = B₁ ⊓ B₂` (`Work.BG.B2_eq_B`).
  have hB2eqB : D.B2 = D.B := B2_eq_B D K1 K2 hHyps
  obtain ⟨h1, h2, hdir, hcop, hB', hfr⟩ := hHyps
  set K : Subgroup G := K1 ⊓ K2 with hKdef
  -- Tower `B ≤ B ⊔ K ≤ U`, so `|U : B| = |B ⊔ K : B| * |U : B ⊔ K|`.
  have hB_le_sup : D.B ≤ D.B ⊔ K := le_sup_left
  have hsup_le_U : D.B ⊔ K ≤ D.U :=
    (le_sup_right : D.B ⊔ K ≤ (D.B1 ⊓ K2) ⊔ (D.B ⊔ K)).trans hdir.1.le
  -- `B ⊓ K = ⊥` (`Work.BG.thmCSec3_B_inf_K1`).
  have hBK_inf : D.B ⊓ K = ⊥ := by
    rw [hKdef]
    exact le_bot_iff.mp
      ((inf_le_inf_left D.B inf_le_left).trans (le_of_eq (thmCSec3_B_inf_K1 D K1 h1)))
  -- `K ◁ B ⊔ K` (`Work.BG.B_normalizes_K`), so `|B ⊔ K : B| = |K|`.
  have hnormBK : D.B ⊔ K ≤ Subgroup.normalizer (K : Set G) := by
    refine sup_le ?_ Subgroup.le_normalizer
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    simpa [hKdef] using B_normalizes_K D K1 K2 h1 h2
  have hBrel : D.B.relIndex (D.B ⊔ K) = Nat.card K :=
    relIndex_sup_eq_card_of_inf_eq_bot D.B K hnormBK hBK_inf
  -- Assemble: `|U : B| = |B ⊔ K : B| * |U : B ⊔ K|` and `|B ⊔ K : B| = |K|`.
  rw [hB2eqB]
  have htower : D.B.relIndex (D.B ⊔ K) * (D.B ⊔ K).relIndex D.U = D.B.relIndex D.U :=
    Subgroup.relIndex_mul_relIndex D.B (D.B ⊔ K) D.U hB_le_sup hsup_le_U
  rw [← htower, hBrel]
  exact dvd_mul_right _ _

end Work.BG
