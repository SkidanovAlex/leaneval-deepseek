import Mathlib
import Submission.Work.SG.SellStabDefs
import Submission.Work.SG.chkJoin_full

namespace Work.SG

/-! # The `ref` case of `SellData.chkJoin`, as a `Prop`

`Work.SG.Data.SellData.chkJoin` (`Submission/Work/SG/Data/SellCheck.lean`): in the
`ref g0 k1 k2` case (with `K = S.subs.getD s 0`) the checker demands `g ∉ K`, `k1, k2 ∈ K`,
`g = (k1 · g0) · k2`, and that the certificate recorded for `g0` at the *same* `s` is a `full`
one with target `t`, whose bitmask `T = S.subs.getD t 0` contains `g`.  The `ref` branch checks
nothing else, so the claim takes the inner `full` certificate's own passing as two extra
hypotheses (`hinner` names it, `h2` says it passes `chkJoin`), and then states both the `ref`
checks and the `full`-case conclusions for the inner certificate (with `g0` in the role of the
joined element, including that the bitmask `T` lies in the union of the `K`-cosets of the
representatives `Work.SG.CZ.joinReps S cos`).  The `full`-case unpacking is imported from
`Submission.Work.SG.chkJoin_full` (lemma `Work.SG.chkJoin_full`). -/

theorem chkJoin_ref {S : Work.SG.Data.SellData} {s g g0 k1 k2 t : ℕ} {cos : List (ℕ × ℕ)}
    (h : S.chkJoin s g (some (Work.SG.Data.JoinCert.ref g0 k1 k2)) = true)
    (hinner : (S.joins.getD s []).getD g0 none = some (Work.SG.Data.JoinCert.full t cos))
    (h2 : S.chkJoin s g0 (some (Work.SG.Data.JoinCert.full t cos)) = true) :
    (S.subs.getD s 0).testBit g = false ∧
    (S.subs.getD s 0).testBit k1 = true ∧
    (S.subs.getD s 0).testBit k2 = true ∧
    g = Work.SG.CZ.gmul S (Work.SG.CZ.gmul S k1 g0) k2 ∧
    (S.subs.getD t 0).testBit g = true ∧
    ((S.subs.getD s 0 ||| (1 <<< g0) ||| S.subs.getD t 0) = S.subs.getD t 0) ∧
    t < S.subs.length ∧
    (∀ p ∈ cos, p.2 = g0 ∨ (S.subs.getD s 0).testBit p.2 = true) ∧
    (∀ q, q < cos.length → (cos.getD q (0, 0)).1 ≤ q) ∧
    (∀ a, (S.subs.getD t 0).testBit a = true →
      ∃ r ∈ Work.SG.CZ.joinReps S cos, ∃ k, k < S.stab.length ∧
        (S.subs.getD s 0).testBit k = true ∧ Work.SG.CZ.gmul S k r = a) := by
  -- Unfold the `ref` branch of the checker.
  have href := h
  simp only [Work.SG.Data.SellData.chkJoin] at href
  simp only [Bool.and_eq_true] at href
  obtain ⟨⟨⟨⟨hng, hk1⟩, hk2⟩, heq⟩, hmatch⟩ := href
  -- the certificate recorded for `g0` is the given `full` one, so the inner match reduces
  simp only [hinner] at hmatch
  -- the `full`-case conclusions for `g0`
  obtain ⟨-, hf2, hf3, hf4, hf5, hf6⟩ := chkJoin_full h2
  exact ⟨by simpa using hng, hk1, hk2,
    by simpa only [Work.SG.CZ.gmul] using beq_iff_eq.mp heq,
    hmatch, hf3, hf2, hf4, hf5, hf6⟩

end Work.SG
