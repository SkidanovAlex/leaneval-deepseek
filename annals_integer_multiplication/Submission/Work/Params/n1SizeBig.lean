import Mathlib
import Submission.Work.Params.defs

namespace Work.Params

/-- `n₁ = 2^E` with `E = 2^40 · 8 · d`; `E` is obtained from the equation `n1_eq` (never by unfolding `n1`),
so no kernel ever has to *evaluate* the tower `2^(2^40·8·d)`. -/
theorem n1SizeBig (n : ℕ) (hn : Work.Params.n1 ≤ n) : 65755586 ≤ n.size := by
  obtain ⟨E, hE, hEval⟩ : ∃ E : ℕ, Work.Params.n1 = 2 ^ E ∧ E = 2 ^ 40 * 8 * 1729 :=
    ⟨_, Work.Params.n1_eq, by simp only [HvdH.D]⟩
  have hEbig : 65755586 ≤ E + 1 := by
    rw [hEval]; norm_num
  have hn' : 2 ^ E ≤ n := by rw [← hE]; exact hn
  calc 65755586 ≤ E + 1 := hEbig
    _ = (2 ^ E).size := (Nat.size_pow (n := E)).symm
    _ ≤ n.size := Nat.size_le_size hn'

end Work.Params
