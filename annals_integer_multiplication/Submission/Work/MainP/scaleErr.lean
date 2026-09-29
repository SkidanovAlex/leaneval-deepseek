import Mathlib
import Submission.Work.Kernel.Raw

namespace Work.MainP

/-- Pure real arithmetic core of Prop 5.2's final error bound (`REFS/nlogn.txt` 2160–2176):
for `c ≥ 1`, `t ≥ 1`, `l ≥ 1` and `3a ≤ t` one has
`2c(2a + 8tl) + 3 < 32ctl`. -/
private lemma scaleErr_arith {c a t l : ℝ} (hc : 1 ≤ c) (ht : 1 ≤ t) (hl : 1 ≤ l)
    (ha : 3 * a ≤ t) : 2 * c * (a + 8 * t * l + a) + 3 < c * (32 * t * l) := by
  have h1 : 4 * a + 3 < 16 * t * l := by nlinarith [ha, ht, hl]
  have hpos : (0:ℝ) < c := by linarith
  have h3 : c * (4 * a + 3) < c * (16 * t * l) := mul_lt_mul_of_pos_left h1 hpos
  have hlt : c * (4 * a + 16 * t * l + 3) < c * (32 * t * l) := by nlinarith [h3]
  calc 2 * c * (a + 8 * t * l + a) + 3 = c * (4 * a + 16 * t * l) + 3 := by ring
    _ ≤ c * (4 * a + 16 * t * l) + 3 * c := by nlinarith [hc]
    _ = c * (4 * a + 16 * t * l + 3) := by ring
    _ < c * (32 * t * l) := hlt

/-- Paper Prop 5.2, final error arithmetic (`REFS/nlogn.txt`, lines 2160–2176).

With `γ = 2·D·α²` (the scaling exponent of Theorem 4.1), `T = ts.prod` and `L = log₂ T`
(`Nat.log 2 T`), the paper's chain
`ε(F̃_s) < 2^{γ+1} ε(F̃'_s) + 3 < 2^{γ+1}(2Dp² + 8T log₂T) + 3 < 2^{γ+5} T log₂T`
only uses `2·D·α² ≤ p`, `100 ≤ p`, `1729 ≤ D`, `3·D·p² < T`:
from `3Dp² < T` we get `T > 2` hence `1 ≤ L` and `2Dp² < (2/3)T ≤ (2/3)TL`, so the left side is
at most `2^{γ+1}·(8TL + (2/3)TL) + 3 ≤ 2^{γ+1}·(26/3)TL + 3`, while the right side is
`2^{γ+5}TL = 2^{γ+1}·16TL`, and `3 < 2^{γ+1}·(22/3)TL` since `γ ≥ 0`, `T ≥ 2`, `L ≥ 1`. -/
theorem scaleErr {D p α T L : ℕ} (hD : 1729 ≤ D) (hp : 100 ≤ p) (hα : 2 * D * α ^ 2 ≤ p)
    (hT : 3 * D * p ^ 2 < T) (hL : L = Nat.log 2 T) :
    2 * (2 : ℝ) ^ (2 * D * α ^ 2) * ((D * p ^ 2 : ℝ) + (8 * T * L : ℝ) + (D * p ^ 2 : ℝ)) + 3
      < ((2 ^ (2 * D * α ^ 2 + 5) * T * L : ℕ) : ℝ) := by
  have _ : 2 * D * α ^ 2 ≤ p := hα
  have hT2 : 2 ≤ T := by
    have h3 : 2 ≤ 3 * D * p ^ 2 := by nlinarith [hD, hp]
    omega
  have hL1 : 1 ≤ L := by
    rw [hL]
    exact Nat.log_pos (by norm_num) hT2
  have hc : (1:ℝ) ≤ (2:ℝ) ^ (2 * D * α ^ 2) := one_le_pow₀ (by norm_num)
  have hT1 : (1:ℝ) ≤ (T:ℝ) := by exact_mod_cast (by omega : 1 ≤ T)
  have hl1 : (1:ℝ) ≤ (L:ℝ) := by exact_mod_cast hL1
  have ha : 3 * ((D:ℝ) * (p:ℝ)^2) ≤ (T:ℝ) := by
    have h : ((3 * D * p^2 : ℕ) : ℝ) ≤ (T:ℝ) := by exact_mod_cast hT.le
    push_cast at h
    nlinarith [h]
  have key := scaleErr_arith (c := (2:ℝ)^(2*D*α^2)) (a := (D:ℝ)*(p:ℝ)^2)
    (t := (T:ℝ)) (l := (L:ℝ)) hc hT1 hl1 ha
  rw [show ((2 ^ (2 * D * α ^ 2 + 5) * T * L : ℕ) : ℝ)
        = (2:ℝ) ^ (2*D*α^2) * (32 * (T:ℝ) * (L:ℝ)) from by
      push_cast; rw [pow_add]; norm_num; ring]
  rw [show 2 * (2 : ℝ) ^ (2 * D * α ^ 2)
        * ((D * p ^ 2 : ℝ) + (8 * T * L : ℝ) + (D * p ^ 2 : ℝ)) + 3
      = 2 * (2:ℝ)^(2*D*α^2) * ((D:ℝ)*(p:ℝ)^2 + 8*(T:ℝ)*(L:ℝ) + (D:ℝ)*(p:ℝ)^2) + 3 from by
      ring]
  exact key

end Work.MainP
