import ChallengeDeps
import Submission.Work.BoseFixR.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/dil_rpow_half.lean` — the diluteness is now in the small regime

`dil v μ = μ (a v)³ = t` is FS's diluteness (`BoseFixR/Defs.lean`).  On the admissible set
`Adm v ε₀ μ` one has `t ≤ ε₀` by definition, and the chapter's whole `§11` arithmetic runs at
thresholds of the form `ε₀ = (1/2)^{323/3}` (`K_ℓ^{-2} = t^{3/323}`): this lemma records the
consequence that *inside* the window the `3/323`-power of the diluteness is already `≤ 1/2`,

  `(dil v μ) ^ (3/323) ≤ 1/2`   whenever   `ε₀ ≤ (1/2)^{323/3}`,

i.e. with `δ := t^{3/323}` one has `δ ≤ 1/2`, the regime in which `(1+δ)^{5/2} ≤ 1 + 5δ^{2/3}`
and friends are used (cf. `CloseBoundRLeKappa.lean`).

## The one genuine step: `Adm` forces `t ≥ 0`

`Adm` carries `ParamsOK (fsParams t) t` but only the *upper* bound `t ≤ ε₀`, so `t ≥ 0` has to
come from the parameter conditions.  It does, through `con:KellKLd` (the field `KellKLd`):
`d^{2𝓜-2} ≪ (μa³)^{1/2}`.  Mathlib's real power at a negative base is
`x ^ y = exp (log x · y) · cos (π y)` (`Real.rpow_def_of_neg`), so for `t < 0` the right-hand
side `t^{1/2} = exp (log t / 2)·cos (π/2) = 0` while `d^{2𝓜-2} = (t^{6/323})^{94} > 0`
(`cos (6π/323) > 0`), a contradiction.  (This is the same argument as
`Work.BoseFixB3.Arith.not_paramsOK_of_neg`, reproduced here so that this file depends only on
Mathlib and `BoseFixR/Defs.lean`.)  Note that `t = 0` is *allowed* — and harmless, since
`0^{3/323} = 0 ≤ 1/2` — so `¬ (t < 0)` is all that is needed.

The rest is monotonicity of `x ↦ x^{3/323}` on `[0,∞)` (`Real.rpow_le_rpow`) together with
`((1/2)^{323/3})^{3/323} = (1/2)^{(323/3)(3/323)} = 1/2` (`Real.rpow_mul`).
-/

namespace Work.BoseFixR

open Work.BoseBox Work.BoseBoxFix

set_option autoImplicit false
set_option linter.unusedVariables false

theorem dil_rpow_half {v : EuclideanSpace ℝ (Fin 3) → ℝ} {ε₀ μ : ℝ}
    (hAdm : Work.BoseBoxFix.Adm v ε₀ μ)
    (hε : ε₀ ≤ (1 / 2 : ℝ) ^ (323 / 3 : ℝ)) :
    (Work.BoseFixR.dil v μ) ^ (3 / 323 : ℝ) ≤ 1 / 2 := by
  -- `Adm` forces the diluteness to be nonnegative: `con:KellKLd` fails for `t < 0`.
  have ht_nonneg : 0 ≤ dil v μ := by
    by_contra hcon
    have ht : dil v μ < 0 := lt_of_not_ge hcon
    have hpar : ParamsOK (fsParams (dil v μ)) (dil v μ) := by
      simpa only [dil, paramsAt] using hAdm.2.2
    rcases hpar.KellKLd with ⟨e, he0, heslack, hineq⟩
    -- `t ^ (1/2) = 0` at a negative base
    have hz : (dil v μ) ^ (1 / 2 : ℝ) = 0 := by
      rw [Real.rpow_def_of_neg ht]
      have h2 : ((1 : ℝ) / 2) * Real.pi = Real.pi / 2 := by ring
      rw [h2, Real.cos_pi_div_two, mul_zero]
    rw [hz, zero_mul] at hineq
    -- while `d ^ (2𝓜-2) = (t^{6/323})^{94} > 0`
    have hpos : 0 < (fsParams (dil v μ)).d ^ (2 * ((fsParams (dil v μ)).M : ℝ) - 2) := by
      have hd : (fsParams (dil v μ)).d = (dil v μ) ^ (6 / 323 : ℝ) := rfl
      have hM : (2 * ((fsParams (dil v μ)).M : ℝ) - 2 : ℝ) = 94 := by
        show (2 * ((48 : ℕ) : ℝ) - 2) = 94
        norm_num
      rw [hd, hM]
      apply Real.rpow_pos_of_pos
      rw [Real.rpow_def_of_neg ht]
      have h1 : 0 < Real.cos ((6 : ℝ) / 323 * Real.pi) := by
        apply Real.cos_pos_of_mem_Ioo
        constructor <;> nlinarith [Real.pi_pos]
      positivity
    linarith
  have hle : dil v μ ≤ ε₀ := hAdm.2.1
  -- monotonicity of `x ↦ x^{3/323}` on `[0,∞)`, then `((1/2)^{323/3})^{3/323} = 1/2`
  have h1 : (dil v μ) ^ (3 / 323 : ℝ) ≤ ((1 / 2 : ℝ) ^ (323 / 3 : ℝ)) ^ (3 / 323 : ℝ) :=
    Real.rpow_le_rpow ht_nonneg (le_trans hle hε) (by norm_num)
  have h2 : ((1 / 2 : ℝ) ^ (323 / 3 : ℝ)) ^ (3 / 323 : ℝ) = 1 / 2 := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
      show (323 / 3 : ℝ) * (3 / 323) = 1 by norm_num, Real.rpow_one]
  linarith

end Work.BoseFixR
