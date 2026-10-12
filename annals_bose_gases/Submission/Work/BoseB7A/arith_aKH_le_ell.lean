import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseB7A.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7A.arith_aKH_le_ell` — `a·K_H ≤ ℓ` at FS's parameter point

At FS's parameter point (`Work.BoseB7.FSParamsView E`) every scalar of the
`Q3Env` is a monomial `fsXp t c = (μa³)^{c/323}` in the diluteness `t = μa³`
(`Work.BoseB7.FSParamsVals`), the box side is the healing length
`ℓ = K_ℓ(μa)^{-1/2}` (FS `eq:def_ell`), `K_ℓ = X^{-3/2}` and `K_H = X^{-549/4}`.
The quotient is

  `a·K_H/ℓ = (√t·K_H)/K_ℓ = X^{323/2-549/4+3/2} = X^{103/4} ≤ 1`  (`X ≤ 1`),

so `a·K_H ≤ ℓ`.  (FS `sec:params`: the small-box estimates dominate exactly this
quotient by `τ^{103/4}`; cf. `Work.BoseB7A.smallness_conj6`.)

The proof is self-contained: it uses only the scalar values of
`Work.BoseB7.FSParamsVals` (`Kl_val`, `KH_val`, `mu_pos`, `a_pos`) and the two
elementary identities
* `a·√(μa) = √(μa³) = √t` (the chemical potential cancels), hence `a = √t·(μa)^{-1/2}`,
* `K_H·√t = X^{323/2-549/4} = X^{97/4} ≤ X^{-3/2} = K_ℓ`.
-/

noncomputable section

namespace Work.BoseB7A

open Work.BoseB7 Work.BoseBox

theorem arith_aKH_le_ell {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E) :
    E.aScat * E.KH ≤ E.ell := by
  have ht : 0 < hv.t := hv.t_pos
  have ha : 0 < E.aScat := hv.a_pos
  have hmu : 0 < E.mu := mu_pos E hv
  have hμa : 0 < E.mu * E.aScat := mul_pos hmu ha
  have hKl : 0 < E.Kl := lt_of_lt_of_le zero_lt_one hv.one_le_Kl
  -- FS `eq:def_ell`: `ℓ = K_ℓ(μa)^{-1/2}`
  have hell : E.ell = E.Kl * (E.mu * E.aScat) ^ (-(1 / 2 : ℝ)) := by
    rw [hv.ell_eq, side]
  -- `√t = X^{323/2}`
  have hsqrt_eq : Real.sqrt hv.t = fsXp hv.t (323 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    simp only [fsXp]
    congr 1
    norm_num
  -- `K_H·√t = X^{-549/4+323/2} = X^{97/4} ≤ X^{-3/2} = K_ℓ`
  have hKH : E.KH * Real.sqrt hv.t ≤ E.Kl := by
    have hprod : E.KH * Real.sqrt hv.t = fsXp hv.t (97 / 4) := by
      rw [KH_val E hv, hsqrt_eq, fsXp_mul ht]
      congr 1
      norm_num
    rw [hprod, Kl_val E hv]
    exact fsXp_le_fsXp ht hv.t_le_one (by norm_num)
  -- `a·√(μa) = √(μa³) = √t`
  have hsqrt : Real.sqrt (E.mu * E.aScat) * E.aScat = Real.sqrt hv.t := by
    calc Real.sqrt (E.mu * E.aScat) * E.aScat
        = Real.sqrt (E.mu * E.aScat) * Real.sqrt (E.aScat ^ 2) := by rw [Real.sqrt_sq ha.le]
      _ = Real.sqrt ((E.mu * E.aScat) * E.aScat ^ 2) := by rw [Real.sqrt_mul hμa.le]
      _ = Real.sqrt (E.mu * E.aScat ^ 3) := by congr 1; ring
      _ = Real.sqrt hv.t := by rw [hv.mu_eq]
  -- `(μa)^{-1/2} = (√(μa))⁻¹`
  have hpow : (E.mu * E.aScat) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (E.mu * E.aScat))⁻¹ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hμa.le]
  -- hence `a = √t·(μa)^{-1/2}`
  have ha_eq : E.aScat = Real.sqrt hv.t * (E.mu * E.aScat) ^ (-(1 / 2 : ℝ)) := by
    have key : E.aScat / (E.mu * E.aScat) ^ (-(1 / 2 : ℝ)) = Real.sqrt hv.t := by
      rw [hpow, div_inv_eq_mul, mul_comm, hsqrt]
    have hd : (E.mu * E.aScat) ^ (-(1 / 2 : ℝ)) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos hμa _)
    rw [← key, div_mul_cancel₀ _ hd]
  -- `a·K_H = (K_H√t/K_ℓ)·ℓ ≤ ℓ`
  have hstep : E.aScat * E.KH
      = (E.KH * Real.sqrt hv.t / E.Kl) * (E.Kl * (E.mu * E.aScat) ^ (-(1 / 2 : ℝ))) := by
    nth_rewrite 1 [ha_eq]
    field_simp
  calc E.aScat * E.KH
      = (E.KH * Real.sqrt hv.t / E.Kl) * (E.Kl * (E.mu * E.aScat) ^ (-(1 / 2 : ℝ))) := hstep
    _ = (E.KH * Real.sqrt hv.t / E.Kl) * E.ell := by rw [hell]
    _ ≤ 1 * E.ell := by
        refine mul_le_mul_of_nonneg_right ?_ (ell_pos E hv).le
        rw [div_le_one hKl]
        exact hKH
    _ = E.ell := one_mul _

end Work.BoseB7A
