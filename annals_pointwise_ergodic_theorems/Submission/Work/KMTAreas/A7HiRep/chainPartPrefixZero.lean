import Mathlib
import Submission.Work.KMTAreas.A7Hi.LowpassDefs

namespace Work.KMTAreas.A7HiRep

open scoped ENNReal NNReal BigOperators

/-- **Monotone reparametrisation does not increase the chain part.**
If `a = b ∘ g` with `g : ℕ → ℕ` monotone, then every chain of `a` pulls back along `g` to a chain of
`b` with the *same* jump values, so `chainPart r a ≤ chainPart r b`. -/
lemma chainPart_le_comp (r : NNReal) {g : ℕ → ℕ} (hg : Monotone g) (b : ℕ → ℂ) :
    Work.KMTAreas.A7Hi.chainPart r (fun m : ℕ => b (g m))
      ≤ Work.KMTAreas.A7Hi.chainPart r b := by
  unfold Work.KMTAreas.A7Hi.chainPart
  refine iSup_le fun J => iSup_le fun N => iSup_le fun hN => ?_
  have hmono : Monotone fun k : ℕ => g (N k) := fun i j hij => hg (hN hij)
  exact le_iSup_of_le J (le_iSup_of_le (fun k : ℕ => g (N k)) (le_iSup_of_le hmono le_rfl))

/-- **Inserting `J` constant steps at the beginning of a walk does not increase the chain part.**
For `1 ≤ r`, `J : ℕ` and `b : ℕ → ℂ`,

  `chainPart r (m ↦ if m ≤ J then b 0 else b (m - J)) ≤ chainPart r b`.

(The left walk has increments `0, …, 0` (`J` of them) followed by the increments of `b`; a chain of
the left walk therefore relabels to a chain of `b` with the same jump values.) -/
theorem chainPartPrefixZero (r : NNReal) (hr : 1 ≤ r) (J : ℕ)
    (b : ℕ → ℂ) :
    Work.KMTAreas.A7Hi.chainPart r (fun m : ℕ => if m ≤ J then b 0 else b (m - J))
      ≤ Work.KMTAreas.A7Hi.chainPart r b := by
  have hwalk : (fun m : ℕ => if m ≤ J then b 0 else b (m - J))
      = fun m : ℕ => b (m - J) := by
    funext m
    by_cases hm : m ≤ J
    · rw [if_pos hm, Nat.sub_eq_zero_of_le hm]
    · rw [if_neg hm]
  rw [hwalk]
  exact chainPart_le_comp r (fun _ _ hij => Nat.sub_le_sub_right hij J) b

end Work.KMTAreas.A7HiRep
