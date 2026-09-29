import Mathlib
import Submission.Work.Layout.Shared
import Submission.Work.Layout.sliceIdx
import Submission.Work.Layout.selfMap_surj

namespace Work.SB

open HvdH
open Work.Layout

theorem keyFacts (A m B : ℕ) (hm : 0 < m) (hB : 0 < B) :
    (∀ i, i < A * m * B → keyIdx1 m B i < A * m * B) ∧
    (∀ i j, i < A * m * B → j < A * m * B → keyIdx1 m B i = keyIdx1 m B j → i = j) := by
  -- `invIdx1` is injective (globally), since `keyIdx1` is a left inverse of it.
  have hinj : ∀ r r' : ℕ, invIdx1 m B r = invIdx1 m B r' → r = r' := by
    intro r r' h
    have h' := congrArg (keyIdx1 m B) h
    rwa [keyIdx1_invIdx1 m B r hm hB, keyIdx1_invIdx1 m B r' hm hB] at h'
  constructor
  · -- `invIdx1` is an injective self-map of `range (A*m*B)`, hence surjective onto it.
    intro i hi
    obtain ⟨r, hr, hri⟩ := selfMap_surj (invIdx1_lt A m B hm hB)
      (fun i _ i' _ h => hinj i i' h) i hi
    calc keyIdx1 m B i = keyIdx1 m B (invIdx1 m B r) := by rw [hri]
      _ = r := keyIdx1_invIdx1 m B r hm hB
      _ < A * m * B := hr
  · intro i j _ _ h
    have h1 := invIdx1_keyIdx1 m B i hm hB
    have h2 := invIdx1_keyIdx1 m B j hm hB
    rw [← h] at h2
    rw [h1] at h2
    exact h2

end Work.SB
