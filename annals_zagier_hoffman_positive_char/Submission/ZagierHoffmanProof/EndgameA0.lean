import Submission.ZagierHoffmanProof.DenRec
import Submission.ZagierHoffmanProof.DegFrac
import Submission.ZagierHoffmanProof.KuanLin

/-!
# SESSION 360 — the `θ`-degree obstruction on the *integral* level, and the endgame for `(q-1) ∤ w`

`PLAN.md` §«SESSION 360».  The two rows of the two-term datum are

* **(R)** `Q·σ(Z) = σQ·W^w·(Q·A₁·H_w + Z + Y)`,
* **(A)** `Y·(X^q - X) = -A₂·L^q·Q`   (`L := X - C θ`, `W := X - C (θ^q)`, `P := X^q - X`),

with `A₁, A₂ ∈ F_q[X] ∖ {0}`, `Q, Z, Y ∈ K^{perf}[X]`, `Q ≠ 0`, `w = k + (q-1)`, `2 ≤ k ≤ q-1`.

**The mechanism.**  Dividing **(R)** by `Q·σQ` and clearing `Y/Q = -A₂L^q/P` (from **(A)**) turns
**(R)** into the *rational* `σ`-recursion

  `Ξ := P·Z/Q`,   `σ Ξ = W^w·(Ξ + N)`,   `N := A₁P² + (A₁(k-1)P - A₂)·L^q ∈ F_q[X]`.

Because the multiplier is a polynomial and the inhomogeneity is a polynomial, the *denominator* `D` of
`Ξ = num/D` in lowest terms is `σ`-fixed up to a scalar (`DenRec.den_map_scalar_of_recursion`), and the
normalised `num'' `satisfies the *Kuan–Lin* recursion `σ(num'') = W^w·(num'' + N·D'')` with
`Fp := W^w·N·D'' ∈ ambA F 0[X]`.  `KuanLin.coeff_mem_ambA_zero_of_kuanLin` therefore yields

> ★★★★ **`num'' ∈ ambA F 0[X] = F_q[θ][X]`** — the *integral* level, where the `θ`-degree is a
> genuine (non-negative, integer) invariant.

The `θ`-degree of the recursion is then the *exact* identity

  `q·t = w·q + e`,   `t := deg_θ(num'')`,   `e := deg_θ(num'' + N·D'')`,

with `n₂ := deg_θ N ∈ {0, q}` (`n₂ = q ⟺ A₁(k-1)P ≠ A₂`).  Since `num'' + N·D''` is again integral,
`e ≥ 0`, so `t ≥ w`; and `e = max(t, n₂)` whenever `t ≠ n₂`.  The pure arithmetic of
`dvd_pred_of_theta_degree` below then forces

> ★★★★★ **`(q-1) ∣ w`.**

For `w = k + (q-1)` with `2 ≤ k ≤ q-1` this excludes every `k < q-1`, i.e. **the whole endgame at
`(q-1) ∤ w` is discharged by the integral level alone**; only the single remaining weight
`w = 2q-2` (`k = q-1`) survives (Dac §6's explicit computation, `EndgameReads`/`Solve64`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open Polynomial

namespace ZagierHoffmanPositiveChar

/-! ## §1. The arithmetic of the `θ`-degree identity -/

/-- ★★★ **The arithmetic core.**  If `q·t = w·q + e` with `n₂ ∈ {0, q}`, `e ≤ max t n₂` and
`e = max t n₂` whenever `t ≠ n₂`, and `q < w`, then `(q-1) ∣ w`.

In the application `t` is the `θ`-degree of the integral numerator `num''`, `e` that of
`num'' + N·D''` and `n₂ = deg_θ N ∈ {0,q}`; the hypothesis `e = max t n₂` for `t ≠ n₂` is the
"no cancellation at the top `θ`-degree" statement, which holds because the top `θ`-monomial of
`num'' + N·D''` comes from `num''` when `t > n₂` and from `N·D''` when `t < n₂`. -/
theorem dvd_pred_of_theta_degree {q w t e n₂ : ℕ} (hq : 0 < q) (hn₂ : n₂ = 0 ∨ n₂ = q)
    (he : q * t = w * q + e) (hmax : t ≠ n₂ → e = max t n₂)
    (hw : q < w) : (q - 1) ∣ w := by
  have hcop : Nat.Coprime (q - 1) q := by
    have h1 : q - (q - 1) = 1 := by omega
    have h2 : Nat.Coprime (q - (q - 1)) (q - 1) := by rw [h1]; exact Nat.coprime_one_left (q - 1)
    exact ((Nat.coprime_sub_self_left (m := q - 1) (n := q) (by omega)).mp h2).symm
  by_cases h : t = n₂
  · -- the `t = n₂` branch is contradictory: `e ≥ 0 ⟹ t ≥ w > q ≥ n₂ = t`
    have htw : w ≤ t := by
      have h1 : w * q ≤ q * t := by rw [he]; exact Nat.le_add_right _ _
      rw [mul_comm w q] at h1
      exact Nat.le_of_mul_le_mul_left h1 hq
    rcases hn₂ with h0 | hq'
    · omega
    · omega
  · rw [hmax h] at he
    rcases lt_or_ge t n₂ with hlt | hle
    · -- `t < n₂`: `q·t = w·q + n₂`, impossible since `t ≥ w > q ≥ n₂`
      rw [max_eq_right (le_of_lt hlt)] at he
      rcases hn₂ with h0 | hq'
      · rw [h0] at hlt; omega
      · rw [hq'] at he hlt
        have h2 : q * t = q * (w + 1) := by rw [he]; ring
        have h3 : t = w + 1 := Nat.eq_of_mul_eq_mul_left hq h2
        omega
    · -- `t ≥ n₂`: `(q-1)·t = w·q`, so `(q-1) ∣ w` since `(q-1) ⊥ q`
      rw [max_eq_left hle] at he
      have hq1 : q = (q - 1) + 1 := (Nat.succ_pred_eq_of_pos hq).symm
      have h1 : (q - 1) * t = w * q := by
        have h2 : ((q - 1) + 1) * t = w * q + t := by rw [← hq1]; exact he
        rw [Nat.add_mul, one_mul] at h2
        omega
      exact hcop.dvd_of_dvd_mul_left ⟨t, by rw [h1, Nat.mul_comm]⟩

end ZagierHoffmanPositiveChar
