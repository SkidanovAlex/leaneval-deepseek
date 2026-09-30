import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.yc_num
import Submission.Work.BW.yc_geom

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The counting inequality at the degenerate (Y-free) descent level `J`: the product of the
number of admissible points `2⌊2S^{(J)}⌋+1` and of the admissible derivative orders
`⌊ξT^{(J)}⌋+1` exceeds the `Y₀`-degree bound `h(D₀+1)`. Here `S^{(J)} = ξ^{-rJ}S`,
`T^{(J)} = ξ^{rJ}T` (so `S^{(J)}T^{(J)} = ST`), `S = 16rdh`, `T = ⌊11.75 r D⌋` and `ξ = 1-0.536/r`. -/
theorem yc_count {K : Type*} [Field K] [NumberField K] {n r : ℕ} (b : Fin n → ℤ) (v : ℕ)
    (σ : Fin r → ℝ) (hr : 2 ≤ r) (hσ : ∀ j, 1 / (dK K : ℝ) ≤ σ j) (J : ℕ) :
    acH K b v * (pD0 r (dK K) σ + 1) <
      (⌊pxi r * TJ K σ J⌋₊ + 1) * (2 * ⌊2 * SJ K r b v J⌋₊ + 1) := by
  have hd : 1 ≤ dK K := by rw [dK]; exact Module.finrank_pos
  rcases Nat.eq_zero_or_pos (acH K b v) with h0 | hpos
  · rw [h0, Nat.zero_mul]
    exact Nat.mul_pos (Nat.succ_pos _) (by omega)
  · have hN := yc_num (r := r) (d := dK K) (h := acH K b v) hr hd hpos σ hσ
    have hG := yc_geom (K := K) b v J σ hr
    apply (Nat.cast_lt (α := ℝ)).mp
    push_cast
    linarith [hN, hG]

end Work.BW
