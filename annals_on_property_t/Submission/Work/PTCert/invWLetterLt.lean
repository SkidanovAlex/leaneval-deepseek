import Mathlib
import Submission.Work.PTCert.WordModel

namespace Work.PTCert

/-- Flipping the exponent bit of a letter preserves the bound `m`, provided `m` is even:
an even `c < m` becomes `c + 1 ≤ m - 1`, and an odd `c < m` becomes `c - 1 < m`. -/
theorem invWAux_xor_one_lt {m : ℕ} (hm : Even m) {c : ℕ} (hc : c < m) : c ^^^ 1 < m := by
  rcases Nat.even_or_odd c with h | h
  · rw [Nat.xor_one_of_even h]
    obtain ⟨k, rfl⟩ := h
    obtain ⟨l, rfl⟩ := hm
    omega
  · rw [Nat.xor_one_of_odd h]
    omega

theorem invWLetterLt (m : ℕ) (hm : Even m) (w : List ℕ) (hw : ∀ c ∈ w, c < m) :
    ∀ c ∈ Submission.PTCert.invW w, c < m := by
  intro c hc
  simp only [Submission.PTCert.invW, List.mem_reverse, List.mem_map] at hc
  obtain ⟨d, hd, rfl⟩ := hc
  exact invWAux_xor_one_lt hm (hw d hd)

end Work.PTCert
