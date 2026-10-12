import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseB7.FSParamsVals
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7A.smallness_conj7` — the Landau-ratio smallness `1/(2sℓ) ≤ 1/(8K_Ha)`

At FS's parameter point (`FSParamsView E`), with `X = (μa³)^{1/323} = fsXp hv.t 1`,
the two scalars of the statement are

* `s·ℓ = X · K_ℓ(μa)^{-1/2} = X · X^{-3/2} · a·t^{-1/2} = a·X^{-162}`,
* `K_H·a = X^{-549/4}·a`,

using `(μa)^{-1/2} = a·(μa³)^{-1/2} = a·t^{-1/2} = a·X^{-323/2}` (`mul_rpow_neg_half`,
`ell_val` below) and `K_H = X^{-549/4}` (`Work.BoseB7.KH_val`).  Hence the *ratio* is
the pure monomial

  `s·ℓ/(K_H·a) = X^{-162+549/4} = X^{-99/4} = fsXp hv.t (-(99/4))`,

independently of `a`, and the requested inequality `1/(2sℓ) ≤ 1/(8K_Ha)` is
equivalent to `4 ≤ s·ℓ/(K_H·a) = X^{-99/4}`.  Since `X ≤ 1/4 < 1` and `-99/4 ≤ -1`,
`X^{-99/4} ≥ X^{-1} ≥ 4`; concretely we prove `X^{99/4} ≤ X ≤ 1/4`, invert, and
multiply by `X^{-549/4}`: `4·X^{-549/4} ≤ X^{-99/4}·X^{-549/4} = X^{-162}`.

All scalars are positive: `s = X > 0`, `ℓ > 0` (`Work.BoseB7.ell_pos`),
`K_H ≥ 1 > 0`, `a > 0`.

The two auxiliary lemmas are stated for general `μ, a` resp. for arbitrary
`Q3Env`/`FSParamsView`, so that the other `smallness_*` files of this family
(`smallness_conj5`, `smallness_conj6`, `smallness_ratios`) may reuse them.
-/

noncomputable section

namespace Work.BoseB7A

/-- `(μa)^{-1/2} = a·(μa³)^{-1/2}` for `μ, a > 0`: the factor `a = (a²)^{1/2}` is
pulled out of the square root, using `a²·(μa) = μa³`.  (The bridge from the box
side `ℓ = K_ℓ(μa)^{-1/2}` to a monomial in `μa³`.) -/
theorem mul_rpow_neg_half (μ a : ℝ) (hμ : 0 < μ) (ha : 0 < a) :
    (μ * a) ^ (-(1 / 2 : ℝ)) = a * (μ * a ^ 3) ^ (-(1 / 2 : ℝ)) := by
  have hμa : 0 < μ * a := mul_pos hμ ha
  have h3 : μ * a ^ 3 = a ^ 2 * (μ * a) := by ring
  have h4 : (μ * a ^ 3) ^ (-(1 / 2 : ℝ)) =
      (a ^ 2) ^ (-(1 / 2 : ℝ)) * (μ * a) ^ (-(1 / 2 : ℝ)) := by
    rw [h3, Real.mul_rpow (by positivity) hμa.le]
  have h5 : (a ^ 2) ^ (-(1 / 2 : ℝ)) = a⁻¹ := by
    rw [Real.rpow_neg (by positivity) (1 / 2), ← Real.sqrt_eq_rpow, Real.sqrt_sq ha.le]
  rw [h4, h5]
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt ha), one_mul]

/-- **FS `eq:def_ell` in monomial form.**  At FS's parameter point the box side is
`ℓ = K_ℓ·a·(μa³)^{-1/2} = K_ℓ·a·X^{-323/2}` with `X = (μa³)^{1/323}`;
equivalently `s·ℓ = fsXp hv.t 1 · E.ell`. -/
theorem ell_val {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E) :
    E.ell = E.Kl * E.aScat * Work.BoseBox.fsXp hv.t (-(323 / 2)) := by
  have ht : 0 < hv.t := hv.t_pos
  have hmu : 0 < E.mu := Work.BoseB7.mu_pos E hv
  have ha : 0 < E.aScat := hv.a_pos
  rw [hv.ell_eq, Work.BoseB7.side, hv.Kl_eq, mul_rpow_neg_half E.mu E.aScat hmu ha,
    hv.mu_eq, Work.BoseB7.rpow_eq_fsXp ht.le]
  rw [show (323 : ℝ) * -(1 / 2) = -(323 / 2) by norm_num]
  ring

/-- **FS's parameter smallness (the `s, ℓ, K_H, a` ratio).**  At FS's parameter
point, `1/(2sℓ) ≤ 1/(8K_Ha)`, i.e. `K_Ha/(sℓ) = X^{99/4} ≤ 1/4` with
`X = (μa³)^{1/323} ≤ 1/4`; equivalently `4K_Ha ≤ sℓ`. -/
theorem smallness_conj7 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E)
    (hX : Work.BoseBox.fsXp hv.t 1 ≤ 1 / 4) :
    1 / (2 * E.s * E.ell) ≤ 1 / (8 * E.KH * E.aScat) := by
  have ht : 0 < hv.t := hv.t_pos
  have ha : 0 < E.aScat := hv.a_pos
  have hXpos : 0 < Work.BoseBox.fsXp hv.t 1 := Work.BoseBox.fsXp_pos ht
  have hX1 : Work.BoseBox.fsXp hv.t 1 ≤ 1 := le_trans hX (by norm_num)
  -- ### (A) `4 ≤ fsXp hv.t (-(99/4))` from `fsXp hv.t 1 ≤ 1/4`
  have hX99 : (Work.BoseBox.fsXp hv.t 1) ^ (99 / 4 : ℝ) ≤ 1 / 4 := by
    calc (Work.BoseBox.fsXp hv.t 1) ^ (99 / 4 : ℝ)
        ≤ (Work.BoseBox.fsXp hv.t 1) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hXpos hX1 (by norm_num)
      _ = Work.BoseBox.fsXp hv.t 1 := Real.rpow_one _
      _ ≤ 1 / 4 := hX
  have h4 : (4 : ℝ) ≤ Work.BoseBox.fsXp hv.t (-(99 / 4)) := by
    have hpos : 0 < (Work.BoseBox.fsXp hv.t 1) ^ (99 / 4 : ℝ) :=
      Real.rpow_pos_of_pos hXpos _
    have h := one_div_le_one_div_of_le hpos hX99
    rw [one_div, one_div] at h
    norm_num at h
    have hneg : ((Work.BoseBox.fsXp hv.t 1) ^ (99 / 4 : ℝ))⁻¹
        = Work.BoseBox.fsXp hv.t (-(99 / 4)) := by
      rw [← Real.rpow_neg hXpos.le, Work.BoseBox.fsXp_rpow ht.le]
      norm_num
    rwa [hneg] at h
  -- ### (B) `4·X^{-549/4} ≤ X^{-162}`
  have hprod : Work.BoseBox.fsXp hv.t (-(99 / 4)) * Work.BoseBox.fsXp hv.t (-(549 / 4))
      = Work.BoseBox.fsXp hv.t (-162) := by
    rw [Work.BoseBox.fsXp_mul ht]
    norm_num
  have hA : 4 * Work.BoseBox.fsXp hv.t (-(549 / 4)) ≤ Work.BoseBox.fsXp hv.t (-162) := by
    calc 4 * Work.BoseBox.fsXp hv.t (-(549 / 4))
        ≤ Work.BoseBox.fsXp hv.t (-(99 / 4)) * Work.BoseBox.fsXp hv.t (-(549 / 4)) :=
          mul_le_mul_of_nonneg_right h4 (Work.BoseBox.fsXp_nonneg ht.le)
      _ = Work.BoseBox.fsXp hv.t (-162) := hprod
  -- ### (C) the scalars as monomials
  have hS : E.s * E.ell = E.aScat * Work.BoseBox.fsXp hv.t (-162) := by
    rw [hv.s_eq, ell_val E hv, hv.Kl_eq]
    have key : Work.BoseBox.fsXp hv.t 1 * Work.BoseBox.fsXp hv.t (-(3 / 2))
          * Work.BoseBox.fsXp hv.t (-(323 / 2))
        = Work.BoseBox.fsXp hv.t (-162) := by
      rw [Work.BoseBox.fsXp_mul ht, Work.BoseBox.fsXp_mul ht]
      norm_num
    rw [← key]
    ring
  have hKH : E.KH * E.aScat = E.aScat * Work.BoseBox.fsXp hv.t (-(549 / 4)) := by
    rw [Work.BoseB7.KH_val E hv]
    ring
  -- ### (D) assembly
  have hmain : 8 * E.KH * E.aScat ≤ 2 * E.s * E.ell := by
    rw [show (8 : ℝ) * E.KH * E.aScat = 8 * (E.KH * E.aScat) by ring,
        show (2 : ℝ) * E.s * E.ell = 2 * (E.s * E.ell) by ring]
    rw [hKH, hS]
    have hB := mul_le_mul_of_nonneg_left hA (show (0 : ℝ) ≤ 2 * E.aScat by linarith)
    linarith [hB]
  have hpos8 : 0 < 8 * E.KH * E.aScat := by
    have hK : 0 < E.KH := lt_of_lt_of_le zero_lt_one hv.one_le_KH
    positivity
  exact one_div_le_one_div_of_le hpos8 hmain

end Work.BoseB7A
