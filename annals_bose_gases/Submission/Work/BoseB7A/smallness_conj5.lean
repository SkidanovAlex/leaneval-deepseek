import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseB7.FSParamsVals
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7A.smallness_conj5` — the smallness of `(𝓜+1)(K_ℓK_L)³/(μℓ³)`

At FS's parameters (`FSParamsView E`, `X = fsXp t 1`, `t = μa³ ∈ (0,1]`) we have

* `𝓜 = X^{-327/4}` (`bigM_val`), `K_ℓK_L = X^{-12}` (`Kl_val`, `KL_val`), so
  `(K_ℓK_L)³ = X^{-36}`, and `μℓ³ = X^{-166}` (`mue_val`).

Hence, dividing by `X^{-166} = X^{-166}`,

  `(𝓜+1)(K_ℓK_L)³/(μℓ³) = (𝓜+1)·X^{-36}·X^{166} = (𝓜+1)·X^{130} = X^{193/4} + X^{130}`

**exactly**.  Since `X ≤ 1` we have `𝓜 ≥ 1`, so `𝓜+1 ≤ 2𝓜` and the whole thing is
`≤ 2X^{193/4}`; finally `X ≤ τ` and `193/4 > 0` give `X^{193/4} ≤ τ^{193/4}`.

The statement below is that comparison, in the form the callers of
`Submission/Work/BoseB7A/Statements.lean` need (it is the overall size of the
`K_ℓ³K_L³` term relative to the `thm:Control3Q` bracket `e1A`/`e23A`/`e4A`).

The proof only uses the scalar values of `Work.BoseB7.FSParamsVals`
(`Kl_val`, `KL_val`, `bigM_val`, `mue_val`) and `hv.one_le_bigM`, `hv.t_le_one`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7A

/-- **FS's parameter smallness of `(𝓜+1)K_ℓ³K_L³/(μℓ³)`.**  At FS's parameter
point this quantity is `(𝓜+1)X^{130} ≤ 2X^{193/4} ≤ 2τ^{193/4}` with
`X = (μa³)^{1/323}`, as soon as `X ≤ τ`. -/
theorem smallness_conj5 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E) {τ : ℝ}
    (hX : Work.BoseBox.fsXp hv.t 1 ≤ τ) :
    (E.bigM + 1) * (E.Kl * E.KL) ^ 3 / (E.mu * E.ell ^ 3) ≤ 2 * τ ^ (193 / 4 : ℝ) := by
  have ht : 0 < hv.t := hv.t_pos
  have hXpos : 0 < Work.BoseBox.fsXp hv.t 1 := Work.BoseBox.fsXp_pos ht
  have hXnonneg : 0 ≤ Work.BoseBox.fsXp hv.t 1 := hXpos.le
  have hone : (1 : ℝ) ≤ E.bigM := hv.one_le_bigM
  -- `K_ℓK_L = X^{-12}`
  have hKlKL : E.Kl * E.KL = Work.BoseBox.fsXp hv.t (-12) := by
    rw [Work.BoseB7.Kl_val E hv, Work.BoseB7.KL_val E hv, Work.BoseBox.fsXp_mul ht]
    congr 1
    norm_num
  -- `(K_ℓK_L)³ = X^{-36}`
  have hcube : (E.Kl * E.KL) ^ 3 = Work.BoseBox.fsXp hv.t (-36) := by
    rw [hKlKL, ← Real.rpow_natCast, Work.BoseBox.fsXp_rpow ht.le]
    congr 1
    norm_num
  -- `μℓ³ = X^{-166}`
  have hden : E.mu * E.ell ^ 3 = Work.BoseBox.fsXp hv.t (-166) := Work.BoseB7.mue_val E hv
  -- `𝓜 = X^{-327/4}`
  have hbigM : E.bigM = Work.BoseBox.fsXp hv.t (-(327 / 4)) := Work.BoseB7.bigM_val E hv
  -- the exact closed form: `K_ℓ³K_L³/(μℓ³) = X^{130}`
  have h1 : (E.Kl * E.KL) ^ 3 / (E.mu * E.ell ^ 3) = Work.BoseBox.fsXp hv.t 130 := by
    rw [hcube, hden, div_eq_mul_inv, Work.BoseBox.fsXp_inv ht, neg_neg,
      Work.BoseBox.fsXp_mul ht]
    congr 1
    norm_num
  -- and `(𝓜+1)K_ℓ³K_L³/(μℓ³) = (𝓜+1)X^{130}`
  have hform : (E.bigM + 1) * (E.Kl * E.KL) ^ 3 / (E.mu * E.ell ^ 3)
      = (E.bigM + 1) * Work.BoseBox.fsXp hv.t 130 := by
    rw [mul_div_assoc, h1]
  -- `𝓜 + 1 ≤ 2𝓜`
  have hstep1 : (E.bigM + 1) * Work.BoseBox.fsXp hv.t 130
      ≤ 2 * E.bigM * Work.BoseBox.fsXp hv.t 130 :=
    mul_le_mul_of_nonneg_right (by linarith) (Work.BoseBox.fsXp_nonneg ht.le)
  -- `2𝓜 X^{130} = 2X^{193/4}`
  have hstep2 : 2 * E.bigM * Work.BoseBox.fsXp hv.t 130
      = 2 * Work.BoseBox.fsXp hv.t (193 / 4) := by
    rw [hbigM, mul_assoc, Work.BoseBox.fsXp_mul ht]
    congr 2
    norm_num
  -- `X^{193/4} ≤ τ^{193/4}`
  have hXrpow : Work.BoseBox.fsXp hv.t (193 / 4)
      = (Work.BoseBox.fsXp hv.t 1) ^ (193 / 4 : ℝ) := by
    rw [Work.BoseBox.fsXp_rpow ht.le]
    congr 1
    norm_num
  have hstep3 : 2 * Work.BoseBox.fsXp hv.t (193 / 4) ≤ 2 * τ ^ (193 / 4 : ℝ) := by
    rw [hXrpow]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hXnonneg hX (by norm_num)) (by norm_num)
  calc (E.bigM + 1) * (E.Kl * E.KL) ^ 3 / (E.mu * E.ell ^ 3)
      = (E.bigM + 1) * Work.BoseBox.fsXp hv.t 130 := hform
    _ ≤ 2 * E.bigM * Work.BoseBox.fsXp hv.t 130 := hstep1
    _ = 2 * Work.BoseBox.fsXp hv.t (193 / 4) := hstep2
    _ ≤ 2 * τ ^ (193 / 4 : ℝ) := hstep3

end Work.BoseB7A
