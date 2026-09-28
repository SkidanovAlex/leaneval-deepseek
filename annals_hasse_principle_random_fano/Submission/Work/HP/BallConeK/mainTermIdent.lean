import Mathlib

namespace Work.HP.BallConeK

/-- Algebraic identity underlying the "main term" computation for the cone of
hypersurfaces in `BallConeK`.  Writing `T ^ r = T ^ k * T ^ (r - k)` and
`Y ^ r = Y ^ k * Y ^ (r - k)` (which is legitimate because `k ≤ r`), the
expression collapses to `(T ^ (r-k) - Y ^ (r-k)) * (1 + k/(r-k))`. -/
theorem mainTermIdent (r k : ℕ) {Y T : ℝ} (hk : 1 ≤ k) (hkr : k + 1 < r) (hY : 0 < Y)
    (hT : 0 < T) :
    (T ^ r - Y ^ r) / T ^ k + (k : ℝ) * (T ^ (r - k) - Y ^ (r - k)) / ((r - k : ℕ) : ℝ)
        - Y ^ r * (1 / Y ^ k - 1 / T ^ k)
      = ((r : ℝ) / ((r : ℝ) - (k : ℝ))) * (T ^ (r - k) - Y ^ (r - k)) := by
  have hrk : k ≤ r := by omega
  -- Split the top powers using `k + (r - k) = r`.
  have hTr : T ^ r = T ^ k * T ^ (r - k) := by rw [← pow_add, Nat.add_sub_cancel' hrk]
  have hYr : Y ^ r = Y ^ k * Y ^ (r - k) := by rw [← pow_add, Nat.add_sub_cancel' hrk]
  have hcast : ((r - k : ℕ) : ℝ) = (r : ℝ) - (k : ℝ) := Nat.cast_sub hrk
  rw [hTr, hYr, hcast]
  have hTk : T ^ k ≠ 0 := by positivity
  have hYk : Y ^ k ≠ 0 := by positivity
  have hkrR : (k : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : k < r)
  have hrkR : (r : ℝ) - (k : ℝ) ≠ 0 := by linarith
  field_simp
  ring

end Work.HP.BallConeK
