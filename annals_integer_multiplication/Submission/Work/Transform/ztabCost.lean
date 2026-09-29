import Mathlib

set_option maxHeartbeats 4000000

namespace Work.Transform

/-- **Cost arithmetic for the `ζ`-table word `Work.Transform.ztabWord`.**

The eight stages of the assembly (base `ζ`-table via `r` calls of `cis`; `pick 4`; the list-product
word `ztabProd`; `pick 4`/`swap`/`fdiv` giving `k = T / r`; `drop`; the stretch `ztabStretch`;
`swap`; the conjugation `Work.Transform.conjVecWord`) cost respectively

* `Kcis * (r * (p+1)^Kcis + 1)`,
* `Kpick * 5 * (Cs + 2*(p+2) + V + V' + 1)`,
* `Kprod * (V + T*p^2 + 1)`,
* `Kpick * 5 * ((T+2) + V + Cs + 2*(p+2) + 1) + Kswap * ((T+2) + (p+3) + 1)
    + Kfdiv * (T+2) * (p+3)`,
* `Kdrop * (V + 1)`,
* `Kst * (k * (Cs + 1) + 1)`,
* `Kswap * (k * (Cs + 2) + (p+2) + 1)`,
* `Kconj * (T * p^2) + Kconj`,

where `Cs = cvecSz p r = r*(2p+8) + r + 1` bounds `vsz (cvecVal bs)` for a vector of `r` disc
entries, `V = vsz (intList ts)`, `V' = vsz (intList ts')`, `T = ts.prod`, `k = T / r`, `r ≥ 2`,
`k * r = T`, `p ≥ 100`.  The claim is that the sum is at most
`Kb * (T * p^2 + r * (p+1)^Kb + V' + V + 1) + Kb` for the explicit constant
`Kb = 1000 * (Kcis + Kpick + Kprod + Kdrop + Kst + Kswap + Kfdiv + Kconj + 100) + 1000`.

Bounds used (each a few lines of `nlinarith`): `k*r = T` gives `r ≤ T` and `k ≤ T`;
`Cs = r*(2p+8)+r+1 ≤ T*p^2` for `p ≥ 100`; `k*(Cs+2) = T*(2p+8) + T + 3k ≤ T*p²`;
`k*(Cs+1) ≤ T*p²`; `(T+2)*(p+3) ≤ T*p² + 2*p`; `Kcis*(p+1)^Kcis ≤ Kb*(p+1)^Kb`;
every library constant appears with coefficient `≤ Kb` on its own term. -/
theorem ztabCost (p r T k V V' Cs Kcis Kpick Kprod Kdrop Kst Kswap Kfdiv Kconj Kb : ℕ)
    (hp : 100 ≤ p) (hr : 2 ≤ r) (hk : 1 ≤ k) (hkr : k * r = T)
    (hCs : Cs = r * (2 * p + 8) + r + 1)
    (hKb : Kb = 1000 * (Kcis + Kpick + Kprod + Kdrop + Kst + Kswap + Kfdiv + Kconj + 100) + 1000) :
    Kcis * (r * (p + 1) ^ Kcis + 1)
    + Kpick * 5 * (Cs + 2 * (p + 2) + V + V' + 1)
    + Kprod * (V + T * p ^ 2 + 1)
    + (Kpick * 5 * ((T + 2) + V + Cs + 2 * (p + 2) + 1) + Kswap * ((T + 2) + (p + 3) + 1)
        + Kfdiv * (T + 2) * (p + 3))
    + Kdrop * (V + 1)
    + Kst * (k * (Cs + 1) + 1)
    + Kswap * (k * (Cs + 2) + (p + 2) + 1)
    + (Kconj * (T * p ^ 2) + Kconj)
    ≤ Kb * (T * p ^ 2 + r * (p + 1) ^ Kb + V' + V + 1) + Kb := by
  -- `T = k*r` with `k ≥ 1`, `r ≥ 2` controls everything below.
  have hrT : r ≤ T := by rw [← hkr]; exact Nat.le_mul_of_pos_left r hk
  have hT2 : 2 ≤ T := le_trans hr hrT
  have hkT : k ≤ T := by rw [← hkr]; exact Nat.le_mul_of_pos_right k (by omega)
  -- the shape bound `Cs ≤ T*p^2` and the `k`-times variants
  have hCsT : Cs ≤ T * p ^ 2 := by rw [hCs]; nlinarith [hrT, hT2, hp]
  have hkCs1 : k * (Cs + 1) ≤ T * p ^ 2 := by rw [hCs]; nlinarith [hkr, hkT, hp]
  have hkCs2 : k * (Cs + 2) ≤ T * p ^ 2 := by rw [hCs]; nlinarith [hkr, hkT, hp]
  -- the linear leftovers are all dominated by `T*p^2`
  have hTp32 : (T + 2) * (p + 3) ≤ T * p ^ 2 := by nlinarith [hT2, hp]
  have hTp22 : T + 2 ≤ T * p ^ 2 := by nlinarith [hT2, hp]
  have hpp3 : p + 3 ≤ T * p ^ 2 := by nlinarith [hT2, hp]
  have hp22 : 2 * (p + 2) ≤ T * p ^ 2 := by nlinarith [hT2, hp]
  -- the exchanged exponent is only used monotonically
  have hKcisKb : Kcis ≤ Kb := by omega
  have hPcP : (p + 1) ^ Kcis ≤ (p + 1) ^ Kb := Nat.pow_le_pow_right (by omega) hKcisKb
  -- the common budget `W` of the right hand side
  set W := T * p ^ 2 + r * (p + 1) ^ Kb + V' + V + 1 with hW
  have hVW : V ≤ W := by omega
  have hV'W : V' ≤ W := by omega
  have hW1 : 1 ≤ W := by omega
  have hTp2W : T * p ^ 2 ≤ W := by omega
  have hCsW : Cs ≤ W := le_trans hCsT hTp2W
  have hp22W : 2 * (p + 2) ≤ W := le_trans hp22 hTp2W
  have hTp22W : T + 2 ≤ W := le_trans hTp22 hTp2W
  have hpp3W : p + 3 ≤ W := le_trans hpp3 hTp2W
  have hTp32W : (T + 2) * (p + 3) ≤ W := le_trans hTp32 hTp2W
  have hkCs1W : k * (Cs + 1) ≤ W := le_trans hkCs1 hTp2W
  have hkCs2W : k * (Cs + 2) ≤ W := le_trans hkCs2 hTp2W
  have hrPcW : r * (p + 1) ^ Kcis ≤ W := by
    have h := Nat.mul_le_mul_left r hPcP
    omega
  -- each of the eight stages is bounded by a small coefficient times `W`
  have p1 : Kcis * (r * (p + 1) ^ Kcis + 1) ≤ 2 * Kcis * W := by nlinarith [hrPcW, hW1]
  have p2 : Kpick * 5 * (Cs + 2 * (p + 2) + V + V' + 1) ≤ 25 * Kpick * W := by
    nlinarith [hCsW, hp22W, hVW, hV'W, hW1]
  have p3 : Kprod * (V + T * p ^ 2 + 1) ≤ 3 * Kprod * W := by nlinarith [hVW, hTp2W, hW1]
  have p4 : Kpick * 5 * ((T + 2) + V + Cs + 2 * (p + 2) + 1) + Kswap * ((T + 2) + (p + 3) + 1)
      + Kfdiv * (T + 2) * (p + 3) ≤ (25 * Kpick + 3 * Kswap + Kfdiv) * W := by
    nlinarith [hTp22W, hVW, hCsW, hp22W, hW1, hpp3W, hTp32W]
  have p5 : Kdrop * (V + 1) ≤ 2 * Kdrop * W := by nlinarith [hVW, hW1]
  have p6 : Kst * (k * (Cs + 1) + 1) ≤ 2 * Kst * W := by nlinarith [hkCs1W, hW1]
  have p7 : Kswap * (k * (Cs + 2) + (p + 2) + 1) ≤ 3 * Kswap * W := by
    nlinarith [hkCs2W, hpp3W, hW1]
  have p8 : Kconj * (T * p ^ 2) + Kconj ≤ 2 * Kconj * W := by nlinarith [hTp2W, hW1]
  -- the accumulated coefficient is still below `Kb`
  have hC : 2 * Kcis + 25 * Kpick + 3 * Kprod + (25 * Kpick + 3 * Kswap + Kfdiv) + 2 * Kdrop
      + 2 * Kst + 3 * Kswap + 2 * Kconj ≤ Kb := by omega
  nlinarith [p1, p2, p3, p4, p5, p6, p7, p8, hC]

end Work.Transform
