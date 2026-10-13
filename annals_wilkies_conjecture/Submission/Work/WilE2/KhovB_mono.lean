import Mathlib
import Submission.Work.WilE2.KhovB

namespace Work.WilE2

/-- For `1 ≤ D` the power bound `D ^ n` is monotone in both the base and the exponent. -/
theorem KhovB_base_mono {n n' D D' : ℕ} (hD : 1 ≤ D) (hn : n ≤ n') (hD' : D ≤ D') :
    D ^ n ≤ D' ^ n' :=
  le_trans (Nat.pow_le_pow_left hD' n) (Nat.pow_le_pow_right (by omega) hn)

theorem KhovB_mono {r n n' D D' : ℕ} (hD : 1 ≤ D) (hn : n ≤ n') (hD' : D ≤ D') :
    KhovB r n D ≤ KhovB r n' D' := by
  induction r generalizing n n' D D' with
  | zero =>
    exact KhovB_base_mono hD hn hD'
  | succ r ih =>
    simp only [KhovB]
    exact ih (by omega) (by omega) (by omega)

end Work.WilE2
