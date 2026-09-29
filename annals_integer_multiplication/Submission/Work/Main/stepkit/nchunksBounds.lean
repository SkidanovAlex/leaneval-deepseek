import Mathlib
import Submission.Work.Main.defs

namespace Work.Main.stepkit

/-- `⌈n/b⌉ ≤ n` for `1 ≤ b`. -/
theorem nchunks_le_self (n b : ℕ) (hb : 1 ≤ b) : Work.Main.nchunks n b ≤ n := by
  have hbpos : 0 < b := hb
  rw [Work.Main.nchunks, Nat.div_le_iff_le_mul_add_pred hbpos]
  have h1 : n ≤ b * n := Nat.le_mul_of_pos_left n hbpos
  have h2 : n + b - 1 = n + (b - 1) := by omega
  omega

/-- `n ≤ b * ⌈n/b⌉` for `1 ≤ b`. -/
theorem self_le_mul_nchunks (n b : ℕ) (hb : 1 ≤ b) : n ≤ b * Work.Main.nchunks n b := by
  have hbpos : 0 < b := hb
  have hmod : (n + b - 1) % b ≤ b - 1 := Nat.le_pred_of_lt (Nat.mod_lt _ hbpos)
  have hsub : (n + b - 1) - (b - 1) ≤ (n + b - 1) - (n + b - 1) % b :=
    Nat.sub_le_sub_left hmod (n + b - 1)
  have heq : (n + b - 1) - (n + b - 1) % b = b * ((n + b - 1) / b) := by
    have h := Nat.div_add_mod (n + b - 1) b
    omega
  have h3 : n = (n + b - 1) - (b - 1) := by omega
  rw [Work.Main.nchunks]
  omega

theorem nchunksBounds (n b : ℕ) (hb : 1 ≤ b) :
    Work.Main.nchunks n b ≤ n ∧ n ≤ b * Work.Main.nchunks n b :=
  ⟨nchunks_le_self n b hb, self_le_mul_nchunks n b hb⟩

end Work.Main.stepkit
