import Mathlib
import Submission.Work.IntLib.SqrtGcd.SqrtDefs

namespace Work.IntLib.SqrtGcd

open Work.IntLib

/-- One step of the restoring square root is correct: starting from `s = r ^ 2 + rem` with
`r = ⌊√s⌋`, appending the two radicand bits `bhi`, `blo` (as the pair `p = 2 bhi + blo`) produces
`s' = 4 s + p` whose integer square root is the second component, with the third component the
corresponding remainder. -/
theorem sqrtStepSpec (s r rem : ℕ) (bhi blo : Bool)
    (hrem : rem = s - r ^ 2) (hlo : r ^ 2 ≤ s) (hhi : s < (r + 1) ^ 2) :
    (let o := Work.IntLib.SG.sqrtStep s r rem bhi blo
     o.1 = 4 * s + (2 * bhi.toNat + blo.toNat) ∧ o.2.1 ^ 2 ≤ o.1 ∧
       o.1 < (o.2.1 + 1) ^ 2 ∧ o.2.2 = o.1 - o.2.1 ^ 2) := by
  have hs : s = r ^ 2 + rem := by omega
  have hb1 : bhi.toNat ≤ 1 := by cases bhi <;> simp
  have hb2 : blo.toNat ≤ 1 := by cases blo <;> simp
  have hp : 2 * bhi.toNat + blo.toNat ≤ 3 := by omega
  have hremle : rem ≤ 2 * r := by
    rw [hs] at hhi
    nlinarith
  unfold Work.IntLib.SG.sqrtStep
  dsimp only
  split_ifs with h
  · dsimp only
    have hsq : (2 * r + 1) ^ 2 = 4 * r ^ 2 + (4 * r + 1) := by ring
    have hs' : 4 * s + (2 * bhi.toNat + blo.toNat)
        = 4 * r ^ 2 + (4 * rem + (2 * bhi.toNat + blo.toNat)) := by rw [hs]; ring
    refine ⟨rfl, ?_, ?_, ?_⟩
    · nlinarith [h, hs]
    · nlinarith [hremle, hp, hs]
    · rw [hs', hsq, Nat.add_sub_add_left]
  · dsimp only
    have h' : 4 * rem + (2 * bhi.toNat + blo.toNat) < 4 * r + 1 := by omega
    have hs' : 4 * s + (2 * bhi.toNat + blo.toNat)
        = 4 * r ^ 2 + (4 * rem + (2 * bhi.toNat + blo.toNat)) := by rw [hs]; ring
    have hsq2 : (2 * r) ^ 2 = 4 * r ^ 2 := by ring
    refine ⟨rfl, ?_, ?_, ?_⟩
    · nlinarith [hs]
    · nlinarith [hs, h']
    · rw [hs', hsq2, Nat.add_sub_cancel_left]

end Work.IntLib.SqrtGcd
