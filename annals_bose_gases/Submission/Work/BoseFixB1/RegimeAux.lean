import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseFixB1.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.RegimeAux` — the closed forms of FS's parameter regime

Toolkit for `Work.BoseFixB1.fsRegimeAt`: FS's parameters at the diluteness
`t = μ A³` are the monomials of `fsXp t c = t^{c/323}`, and the box side is
`ℓ = sideAt μ A = A t^{-163/323}`.  Everything needed to verify the elementary
inequalities of the FS regime (`ℓ ≥ μ^{-1/3}`, `μ(dℓ)³ ≥ 1`, `K_B³(μa³)^{1/2} ≤ 1`,
…) is a comparison of such monomials, and the lemmas below record the closed
forms once and for all.

Written by the `fsRegimeAt` lead; used by the per-conjunct lemma requests.
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseFixB1

open Work.BoseBox

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. `fsXp` bookkeeping -/

/-- `fsXp t 323 = t`: the normalisation of the exponent scale. -/
lemma fsXp_323 (t : ℝ) : fsXp t 323 = t := by
  rw [fsXp, show (323 : ℝ) / 323 = 1 by norm_num, Real.rpow_one]

/-- `t^{1/2} = fsXp t (323/2)`. -/
lemma half_eq_fsXp (t : ℝ) : t ^ (1 / 2 : ℝ) = fsXp t (323 / 2) := by
  rw [fsXp]; norm_num

/-- `t^{-1/3} = fsXp t (-(323/3))`. -/
lemma inv_third_eq_fsXp (t : ℝ) : t ^ (-(1 / 3) : ℝ) = fsXp t (-(323 / 3)) := by
  rw [fsXp]; norm_num

/-- `t^{(M)/3} = fsXp t (M·323/3)` at FS's `M = mValue`. -/
lemma mValue_div_three_eq_fsXp (t : ℝ) :
    t ^ ((mValue : ℝ) / 3) = fsXp t ((mValue : ℝ) * (323 / 3)) := by
  rw [fsXp, mValue]; norm_num

/-- `1 ≤ fsXp t c` for `0 < t ≤ 1` and `c ≤ 0`. -/
lemma one_le_fsXp_of {t c : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) (hc : c ≤ 0) :
    1 ≤ fsXp t c := by
  rw [fsXp]
  exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos h0 h1
    (div_nonpos_of_nonpos_of_nonneg hc (by norm_num))

/-! ## 2. The closed forms of FS's parameters -/

/-- `d = X⁶ = t^{6/323}`. -/
lemma d_eq_fsXp (μ A : ℝ) : (paramsAt μ A).d = fsXp (μ * A ^ 3) 6 := rfl

/-- `K_B = X^{-6} = t^{-6/323}`. -/
lemma KB_eq_fsXp (μ A : ℝ) : (paramsAt μ A).KB = fsXp (μ * A ^ 3) (-6) := rfl

/-- `K_ℓ = X^{-3/2} = t^{-3/646}`. -/
lemma Kl_eq_fsXp (μ A : ℝ) : (paramsAt μ A).Kl = fsXp (μ * A ^ 3) (-(3 / 2)) := rfl

/-- `M = mValue = 48`. -/
lemma M_eq_mValue (μ A : ℝ) : (paramsAt μ A).M = mValue := rfl

/-- **The box side**: `ℓ = sideAt μ A = A t^{-163/323} = A · fsXp t (-163)`. -/
lemma sideAt_eq_fsXp {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) :
    sideAt μ A = A * fsXp (μ * A ^ 3) (-163) := by
  rw [sideAt_eq_rpow hA hμ, fsXp]; norm_num

/-- `ℓ³ = A³ fsXp t (-489)`. -/
lemma sideAt_cube_eq {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) :
    sideAt μ A ^ 3 = A ^ 3 * fsXp (μ * A ^ 3) (-489) := by
  have ht : (0 : ℝ) < μ * A ^ 3 := by positivity
  rw [sideAt_eq_fsXp hA hμ, mul_pow, fsXp_pow ht.le]
  norm_num

/-- `d³ = fsXp t 18`. -/
lemma d_cube_eq {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) :
    (paramsAt μ A).d ^ 3 = fsXp (μ * A ^ 3) 18 := by
  have ht : (0 : ℝ) < μ * A ^ 3 := by positivity
  rw [d_eq_fsXp, fsXp_pow ht.le]
  norm_num

/-- The small-box side: `d ℓ = A fsXp t (-157)`. -/
lemma d_mul_sideAt_eq {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) :
    (paramsAt μ A).d * sideAt μ A = A * fsXp (μ * A ^ 3) (-157) := by
  have ht : (0 : ℝ) < μ * A ^ 3 := by positivity
  rw [d_eq_fsXp, sideAt_eq_fsXp hA hμ]
  calc fsXp (μ * A ^ 3) 6 * (A * fsXp (μ * A ^ 3) (-163))
      = A * (fsXp (μ * A ^ 3) 6 * fsXp (μ * A ^ 3) (-163)) := by ring
    _ = A * fsXp (μ * A ^ 3) (-157) := by rw [fsXp_mul ht]; norm_num

/-- `(d ℓ)³ = A³ fsXp t (-471)`. -/
lemma d_mul_sideAt_cube_eq {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) :
    ((paramsAt μ A).d * sideAt μ A) ^ 3 = A ^ 3 * fsXp (μ * A ^ 3) (-471) := by
  have ht : (0 : ℝ) < μ * A ^ 3 := by positivity
  rw [d_mul_sideAt_eq hA hμ, mul_pow, fsXp_pow ht.le]
  norm_num

/-- `μ (d ℓ)³ = fsXp t (-148)`. -/
lemma mu_d_mul_sideAt_cube_eq {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) :
    μ * ((paramsAt μ A).d * sideAt μ A) ^ 3 = fsXp (μ * A ^ 3) (-148) := by
  have ht : (0 : ℝ) < μ * A ^ 3 := by positivity
  rw [d_mul_sideAt_cube_eq hA hμ]
  calc μ * (A ^ 3 * fsXp (μ * A ^ 3) (-471))
      = (μ * A ^ 3) * fsXp (μ * A ^ 3) (-471) := by ring
    _ = fsXp (μ * A ^ 3) 323 * fsXp (μ * A ^ 3) (-471) := by rw [fsXp_323]
    _ = fsXp (μ * A ^ 3) (-148) := by rw [fsXp_mul ht]; norm_num

/-- `μ ℓ³ = fsXp t (-166)`. -/
lemma mu_ell_cube_eq {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) :
    μ * sideAt μ A ^ 3 = fsXp (μ * A ^ 3) (-166) := by
  have ht : (0 : ℝ) < μ * A ^ 3 := by positivity
  rw [sideAt_cube_eq hA hμ]
  calc μ * (A ^ 3 * fsXp (μ * A ^ 3) (-489))
      = (μ * A ^ 3) * fsXp (μ * A ^ 3) (-489) := by ring
    _ = fsXp (μ * A ^ 3) 323 * fsXp (μ * A ^ 3) (-489) := by rw [fsXp_323]
    _ = fsXp (μ * A ^ 3) (-166) := by rw [fsXp_mul ht]; norm_num

/-- `K_B³ t^{1/2} = fsXp t (287/2)`. -/
lemma KB3_half_eq {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) :
    (paramsAt μ A).KB ^ 3 * (μ * A ^ 3) ^ (1 / 2 : ℝ) = fsXp (μ * A ^ 3) (287 / 2) := by
  have ht : (0 : ℝ) < μ * A ^ 3 := by positivity
  rw [KB_eq_fsXp, fsXp_pow ht.le, half_eq_fsXp]
  rw [fsXp_mul ht]; norm_num

/-- `μ ℓ³ K_B³ t^{1/2} = fsXp t (-(45/2))`. -/
lemma mu_ell_cube_KB3_half_eq {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) :
    μ * sideAt μ A ^ 3 * (paramsAt μ A).KB ^ 3 * (μ * A ^ 3) ^ (1 / 2 : ℝ)
      = fsXp (μ * A ^ 3) (-(45 / 2)) := by
  have ht : (0 : ℝ) < μ * A ^ 3 := by positivity
  calc μ * sideAt μ A ^ 3 * (paramsAt μ A).KB ^ 3 * (μ * A ^ 3) ^ (1 / 2 : ℝ)
      = (μ * sideAt μ A ^ 3) * ((paramsAt μ A).KB ^ 3 * (μ * A ^ 3) ^ (1 / 2 : ℝ)) := by
        ring
    _ = fsXp (μ * A ^ 3) (-166) * fsXp (μ * A ^ 3) (287 / 2) := by
          rw [mu_ell_cube_eq hA hμ, KB3_half_eq hA hμ]
    _ = fsXp (μ * A ^ 3) (-(45 / 2)) := by rw [fsXp_mul ht]; norm_num

/-- `μ^{-1/3} = A · fsXp t (-(323/3))`. -/
lemma mu_inv_third_eq {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) :
    μ ^ (-(1 / 3) : ℝ) = A * fsXp (μ * A ^ 3) (-(323 / 3)) := by
  have ht : (0 : ℝ) < μ * A ^ 3 := by positivity
  have hA3 : (0 : ℝ) < A ^ 3 := by positivity
  have h2 : ((A : ℝ) ^ 3) ^ (-(1 / 3) : ℝ) = A⁻¹ := by
    rw [show ((A : ℝ) ^ 3) = A ^ ((3 : ℕ) : ℝ) by exact (Real.rpow_natCast A 3).symm]
    rw [← Real.rpow_mul hA.le]
    norm_num
    rw [Real.rpow_neg hA.le 1, Real.rpow_one]
  have h3 : ((μ * A ^ 3) / A ^ 3) ^ (-(1 / 3) : ℝ) = (μ * A ^ 3) ^ (-(1 / 3) : ℝ) * A := by
    rw [Real.div_rpow ht.le hA3.le, h2, div_inv_eq_mul]
  calc μ ^ (-(1 / 3) : ℝ) = ((μ * A ^ 3) / A ^ 3) ^ (-(1 / 3) : ℝ) := by
        rw [show (μ * A ^ 3) / A ^ 3 = μ by field_simp]
    _ = (μ * A ^ 3) ^ (-(1 / 3) : ℝ) * A := h3
    _ = A * fsXp (μ * A ^ 3) (-(323 / 3)) := by rw [inv_third_eq_fsXp]; ring

end Work.BoseFixB1
