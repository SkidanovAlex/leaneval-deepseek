import Mathlib
import Submission.Work.BW.est15defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The `j`-th component of an auxiliary index `λ : AuxIdx r h D0 Dj` is a `Fin (Dj j + 1)`,
so `λ_j ≤ D_j`; monotonicity of integer division by `2^J` gives the bound. -/
theorem auxIdx_div_pow_le {r h D0 : ℕ} {Dj : Fin r → ℕ} (lm : AuxIdx r h D0 Dj) (J : ℕ) (j : Fin r) :
    (((lm.2.2 j : ℕ) / 2 ^ J : ℕ) : ℝ) ≤ (Dj j : ℝ) / 2 ^ J := by
  have hle : (lm.2.2 j : ℕ) ≤ Dj j := Nat.lt_succ_iff.mp (lm.2.2 j).isLt
  have hdiv : (lm.2.2 j : ℕ) / 2 ^ J ≤ Dj j / 2 ^ J := Nat.div_le_div_right hle
  calc (((lm.2.2 j : ℕ) / 2 ^ J : ℕ) : ℝ)
      ≤ ((Dj j / 2 ^ J : ℕ) : ℝ) := by exact_mod_cast hdiv
    _ ≤ (Dj j : ℝ) / (2 : ℝ) ^ J := by
        simpa using (Nat.cast_div_le (α := ℝ) (m := Dj j) (n := 2 ^ J))
    _ = (Dj j : ℝ) / 2 ^ J := rfl

end Work.BW
