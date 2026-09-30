import Mathlib
import Submission.Work.BW.DefsMult

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Auxiliary closed-form quantities for `Work.BW.rank_drop_numerics` (BW §21 check (30)). -/

namespace Work.BW

/-- `u = 2rd`, the base of the real powers. -/
noncomputable def rdnU (r d : ℕ) : ℝ := 2 * (r : ℝ) * (d : ℝ)

/-- `log u = log(2rd)`. -/
noncomputable def rdnL (r d : ℕ) : ℝ := Real.log (rdnU r d)

/-- The exponent `50·cap(r) = 26.8·r/(r − 0.536)` bounding `−r log ξ`. -/
noncomputable def rdnCap (r : ℕ) : ℝ := 26.8 * (r : ℝ) / ((r : ℝ) - 0.536)

/-- `u^(50 cap)`. -/
noncomputable def rdnPowD (r d : ℕ) : ℝ := (rdnU r d) ^ (rdnCap r)

/-- `u^26.8`, the guaranteed growth of `ξ^{-rI}`. -/
noncomputable def rdnPC (r d : ℕ) : ℝ := (rdnU r d) ^ (26.8 : ℝ)

/-- `δ = 11.75/(8 u^(50cap))`. -/
noncomputable def rdnDel (r d : ℕ) : ℝ := 11.75 / (8 * rdnPowD r d)

/-- `γ = 4/(u · u^(50 log 2)) = 2/(r d u^{50 log 2})`. -/
noncomputable def rdnGam (r d : ℕ) : ℝ := 4 / (rdnU r d * (rdnU r d) ^ (50 * Real.log 2))

/-- `C = 2 r^r (32d)^{r+1} log(2rd)`; `pD r d σ = C · ∏ σ` by definition. -/
noncomputable def rdnC (r d : ℕ) : ℝ :=
  2 * (r : ℝ) ^ r * ((32 : ℝ) * (d : ℝ)) ^ (r + 1) * rdnL r d

theorem rdnU_pos {r d : ℕ} (hr : 1 ≤ r) (hd : 1 ≤ d) : 0 < rdnU r d := by
  unfold rdnU; positivity

theorem rdnU_one_le {r d : ℕ} (hr : 1 ≤ r) (hd : 1 ≤ d) : 1 ≤ rdnU r d := by
  unfold rdnU
  have : (1:ℝ) ≤ r := by exact_mod_cast hr
  have : (1:ℝ) ≤ d := by exact_mod_cast hd
  nlinarith

theorem pD_eq_rdnC {r d : ℕ} (σ : Fin r → ℝ) :
    pD r d σ = rdnC r d * ∏ j, σ j := by
  unfold pD rdnC rdnL rdnU
  push_cast
  ring

end Work.BW
