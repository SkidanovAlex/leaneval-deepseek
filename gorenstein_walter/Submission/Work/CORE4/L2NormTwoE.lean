import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2CountAssembly
import Submission.Work.CORE4.Case2EightAllOfCtx
import Submission.Work.CORE4.Counting.EConjLayerIn
import Submission.Work.CORE4.NormTwoTransport.NcardSubgroupOf
import Submission.Work.CORE4.NormTwoTransport.NcardMulEquiv

open scoped MatrixGroups

namespace Work.CORE4

/-- **Bender 1981, §4, p. 227 (`I.l2normTwo`, `L2NormalizesTwoSylowProp`, transported along §4 (9)).**

Let `E := layerIn h.D.M ≅ PSL(2, pF^kF)` (§4 (9)), `q := qOf h = pF^kF`, and let
`Y ≤ E` be a subgroup of odd prime order `r ≠ pF` (equivalently `r ∤ q`).  Then `Y` normalizes at
most two subgroups of `E` of order `q`:

    #{Q ≤ E : |Q| = q, Y ≤ N(Q)} ≤ 2.

Route: `I.l2normTwo` applied to the image `φ Y` under the §4 (9) isomorphism
`φ : E ≃* PSL(2, pF^kF)`; `Subgroup.equivMapOfInjective` is a bijection between the subgroups of
`E` and those of `PSL(2, pF^kF)` preserving cardinality and normalizers, so the `ncard` is
unchanged (cf. `Work.CORE4.ncard_subgroups_eq_of_mulEquiv`,
`Submission/Work/CORE4/Case2CountPieces.lean`).

This is Bender's "because `X` normalizes at most two subgroups of order `q` in `P × E`"; it is the
second of the two `L₂(q)` inputs of §4 (12) (the first being `I.l2torusNorm`). -/
theorem L2NormTwoE (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B) (r : ℕ) (Y : Subgroup G),
        r.Prime → r ≠ 2 → r ≠ Work.CORE4.nineP h → Y ≤ Work.GW2.layerIn h.D.M →
        Nat.card ↥Y = r →
        {Q : Subgroup G | Q ≤ Work.GW2.layerIn h.D.M ∧ Nat.card ↥Q = Work.CORE4.qOf h ∧
          Y ≤ Subgroup.normalizer (Q : Set G)}.ncard ≤ 2 := by
  intro G _ _ hbc B h r Y hr hr2 hrp hYE hYcard
  -- §4 (9): the isomorphism `φ : E(M) ≃* PSL(2, pF^kF)` of the layer onto `L₂(q)`.
  haveI : Fact (Work.CORE4.nineP h).Prime := ⟨Work.CORE4.nineP_prime h⟩
  obtain ⟨φ⟩ := Work.CORE4.nineP_iso h
  have h7 : 7 ≤ Work.CORE4.nineP h ^ Work.CORE4.nineK h := Work.CORE4.nineP_seven h
  have h5 : 5 ≤ Work.CORE4.nineP h ^ Work.CORE4.nineK h := by omega
  -- `Y` transported into `PSL(2, pF^kF)`: still of cardinality `r`.
  have hY0card : Nat.card ↥(Y.subgroupOf (Work.GW2.layerIn h.D.M)) = r := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYE).toEquiv, hYcard]
  have hY0mapcard :
      Nat.card ↥((Y.subgroupOf (Work.GW2.layerIn h.D.M)).map φ.toMonoidHom) = r := by
    rw [Subgroup.card_map_of_injective φ.injective, hY0card]
  -- The count of subgroups `Q ≤ E` of order `q` normalized by `Y` is the same as the count
  -- inside `E` (§4 (9) transport along `E ↪ G`), and the same as the count inside `L₂(q)`
  -- (transport along `φ`).
  have hstep1 := Work.CORE4.NormTwoTransport.NcardSubgroupOf
    (Work.GW2.layerIn h.D.M) Y hYE (Work.CORE4.qOf h)
  have hstep2 := Work.CORE4.NormTwoTransport.NcardMulEquiv φ
    (Y.subgroupOf (Work.GW2.layerIn h.D.M)) (Work.CORE4.qOf h)
  -- Bender's count in `L₂(q)`: a subgroup of order `r ∤ q` normalizes at most two Sylow
  -- `p`-subgroups.
  have hstep3 := I.l2normTwo (Work.CORE4.nineP h) (Work.CORE4.nineK h)
      (Work.CORE4.nineP_odd h) h5 r hr hr2 hrp
      ((Y.subgroupOf (Work.GW2.layerIn h.D.M)).map φ.toMonoidHom) hY0mapcard
  calc {Q : Subgroup G | Q ≤ Work.GW2.layerIn h.D.M ∧ Nat.card ↥Q = Work.CORE4.qOf h ∧
        Y ≤ Subgroup.normalizer (Q : Set G)}.ncard
      = {Q : Subgroup ↥(Work.GW2.layerIn h.D.M) | Nat.card ↥Q = Work.CORE4.qOf h ∧
          (Y.subgroupOf (Work.GW2.layerIn h.D.M)) ≤
            Subgroup.normalizer (Q : Set ↥(Work.GW2.layerIn h.D.M))}.ncard := hstep1
    _ = {Q : Subgroup (PSL(2, GaloisField (Work.CORE4.nineP h) (Work.CORE4.nineK h))) |
          Nat.card ↥Q = Work.CORE4.qOf h ∧
          ((Y.subgroupOf (Work.GW2.layerIn h.D.M)).map φ.toMonoidHom) ≤
            Subgroup.normalizer (Q : Set _)}.ncard := hstep2
    _ ≤ 2 := hstep3

end Work.CORE4
