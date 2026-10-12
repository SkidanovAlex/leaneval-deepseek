import ChallengeDeps
import Submission.Work.BoseBoxFock.errKafz_dominates_uniform
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

/-- **The final diluteness comparison** (the name avoids the existing unrelated
`Work.BoseBoxFock.errKafz_dominates`).  A cost that is bounded by `Ccoef * μ^(5/2) * pL` at small
diluteness `t = μ (a v)³ ≤ 1` is bounded by `½ * errKafz v R μ C * pL` for the *fixed* constant
`C = 4*Ccoef*(a v)^(-11/2) + 1`.

Mathematics: `errKafz v R μ C = C μ² a ℓ³ √t · bracket` with `ℓ = sideAt μ (a v)`, `t = μ a³`,
`bracket = Kl⁻³ + (t^(1/323))² + (R/a)²√t + t^(1/1615) ≥ t^(1/1615)` (all four summands are
non-negative; the last one is `errExp`), and the exact identity `μ ℓ³ = t^(-166/323)`
(`Work.BoseBox.mu_ell_cube_fsParams`), so `a ℓ³ √t ≥ a⁴ t^(-489/323+1/2)` and

`½·errKafz ≥ 2·Ccoef·a^(-11/2)·μ² a ℓ³ t^(1/2+1/1615) = 2·Ccoef·a^(-15/2)·t^(3187/3230)`,

while `Ccoef·μ^(5/2) = Ccoef·a^(-15/2)·t^(5/2)`; dividing by `a^(-15/2)t^(3187/3230)` (`a` and `t`
positive) leaves the elementary `t^(2444/1615) ≤ 2`, which holds because `2444/1615 > 0` and
`t ≤ 1`.  (For `Ccoef = 0` both sides vanish.)

The necessary `rpow` facts: `Real.sqrt_eq_rpow`, `Real.rpow_add`/`Real.rpow_mul`,
`Real.rpow_le_rpow_of_nonpos`/`Real.one_le_rpow` for `t ≤ 1` and positive exponents,
`Work.BoseBox.fsXp_pos`, and `Work.BoseBox.mu_ell_cube_fsParams`; the sign of the bracket is
`Work.BoseFixR.errKafz_ge_errExp`-style (all four summands non-negative). -/
theorem stripImages_arith {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R μ Ccoef Cost pL : ℝ}
    (hav : 0 < BoseGases.a v) (hR : 0 < R) (hμ : 0 < μ)
    (ht1 : μ * (BoseGases.a v) ^ 3 ≤ 1) (hCcoef : 0 ≤ Ccoef) (hpL : 0 ≤ pL)
    (hCost : Cost ≤ Ccoef * μ ^ ((5 : ℝ) / 2) * pL) :
    Cost ≤ (1 / 2) * Work.BoseFixR.errKafz v R μ
          (4 * Ccoef * (BoseGases.a v) ^ (-(11 / 2) : ℝ) + 1) * pL := by
  -- **Route actually used** (weaker than the manifest's sharp route, and much shorter):
  -- the *first* slot `K_ℓ⁻³` of the `errKafz` bracket alone gives
  -- `C·μ·(a v) ≤ errKafz v R μ C` (`errKafz_ge`, via `μ²(a v)ℓ³√(μa³)K_ℓ⁻³ = μ(a v)`), and
  -- `C = 4Ccoef(a v)^{-11/2} + 1 ≥ 4Ccoef(a v)^{-11/2}` turns this into
  -- `½·errKafz ≥ 2·Ccoef·(a v)^{-11/2}·μ·(a v)`.  It therefore suffices to have
  -- `Ccoef·μ^{5/2} ≤ 2·Ccoef·(a v)^{-11/2}·μ·(a v)`, i.e. (for `Ccoef ≥ 0`) `μ^{3/2} ≤ 2(a v)^{-9/2}`,
  -- which is `(μ(a v)³)^{3/2} ≤ 2` — immediate from the diluteness bound `μ(a v)³ ≤ 1`.
  have ha : 0 < BoseGases.a v := hav
  have ht : 0 < μ * (BoseGases.a v) ^ 3 := by positivity
  have ha3 : 0 ≤ (BoseGases.a v) ^ 3 := by positivity
  -- the box constant is non-negative
  have hCn : 0 ≤ 4 * Ccoef * (BoseGases.a v) ^ (-(11 / 2) : ℝ) + 1 := by
    have h1 : 0 ≤ Ccoef * (BoseGases.a v) ^ (-(11 / 2) : ℝ) :=
      mul_nonneg hCcoef (Real.rpow_nonneg ha.le _)
    linarith
  -- `C μ (a v) ≤ errKafz v R μ C` (`errKafz_ge`, the `K_ℓ⁻³`-slot of the bracket)
  have hkafz := errKafz_ge (v := v) (R := R) (μ := μ)
      (C := 4 * Ccoef * (BoseGases.a v) ^ (-(11 / 2) : ℝ) + 1) hμ hav hCn
  -- `(μ (a v)³)^{3/2} ≤ 1 ≤ 2`, i.e. `μ^{3/2} ≤ 2 (a v)^{-9/2}`
  have h_asq : ((BoseGases.a v) ^ 3) ^ (3 / 2 : ℝ) = (BoseGases.a v) ^ (9 / 2 : ℝ) := by
    rw [← Real.rpow_natCast (BoseGases.a v) 3, ← Real.rpow_mul ha.le]
    rw [show (((3 : ℕ) : ℝ)) * (3 / 2) = 9 / 2 by norm_num]
  have hmul : μ ^ (3 / 2 : ℝ) * (BoseGases.a v) ^ (9 / 2 : ℝ)
      = (μ * (BoseGases.a v) ^ 3) ^ (3 / 2 : ℝ) := by
    rw [← h_asq, Real.mul_rpow hμ.le ha3]
  have hle2 : μ ^ (3 / 2 : ℝ) * (BoseGases.a v) ^ (9 / 2 : ℝ) ≤ 2 := by
    rw [hmul]
    have h1 : (μ * (BoseGases.a v) ^ 3) ^ (3 / 2 : ℝ) ≤ 1 :=
      Real.rpow_le_one ht.le ht1 (by norm_num)
    linarith
  have h32 : μ ^ (3 / 2 : ℝ) ≤ 2 * (BoseGases.a v) ^ (-(9 / 2) : ℝ) := by
    have hpos : 0 < (BoseGases.a v) ^ (9 / 2 : ℝ) := Real.rpow_pos_of_pos ha _
    calc μ ^ (3 / 2 : ℝ)
        = (μ ^ (3 / 2 : ℝ) * (BoseGases.a v) ^ (9 / 2 : ℝ))
            / (BoseGases.a v) ^ (9 / 2 : ℝ) := (mul_div_cancel_right₀ _ (ne_of_gt hpos)).symm
      _ ≤ 2 / (BoseGases.a v) ^ (9 / 2 : ℝ) := div_le_div_of_nonneg_right hle2 hpos.le
      _ = 2 * (BoseGases.a v) ^ (-(9 / 2) : ℝ) := by rw [Real.rpow_neg ha.le, div_eq_mul_inv]
  -- `a^{-11/2} · a = a^{-9/2}`
  have hA : (BoseGases.a v) ^ (-(11 / 2) : ℝ) * BoseGases.a v
      = (BoseGases.a v) ^ (-(9 / 2) : ℝ) := by
    have h1 : (BoseGases.a v) ^ (-(9 / 2) : ℝ)
        = (BoseGases.a v) ^ (-(11 / 2) : ℝ) * BoseGases.a v := by
      calc (BoseGases.a v) ^ (-(9 / 2) : ℝ)
          = (BoseGases.a v) ^ ((-(11 / 2)) + 1) := by
              rw [show (-(11 / 2) : ℝ) + 1 = -(9 / 2) by norm_num]
        _ = (BoseGases.a v) ^ (-(11 / 2) : ℝ) * (BoseGases.a v) ^ (1 : ℝ) :=
              Real.rpow_add ha _ _
        _ = (BoseGases.a v) ^ (-(11 / 2) : ℝ) * BoseGases.a v := by rw [Real.rpow_one]
    exact h1.symm
  -- `μ^{5/2} = μ · μ^{3/2}`
  have hmu52 : μ ^ ((5 : ℝ) / 2) = μ * μ ^ (3 / 2 : ℝ) := by
    rw [show (5 : ℝ) / 2 = 1 + 3 / 2 by norm_num, Real.rpow_add hμ, Real.rpow_one]
  -- `μ^{5/2} ≤ 2 (a v)^{-11/2} μ (a v)`
  have hg : μ ^ ((5 : ℝ) / 2) ≤ 2 * (BoseGases.a v) ^ (-(11 / 2) : ℝ) * μ * BoseGases.a v := by
    rw [hmu52]
    calc μ * μ ^ (3 / 2 : ℝ) ≤ μ * (2 * (BoseGases.a v) ^ (-(9 / 2) : ℝ)) :=
          mul_le_mul_of_nonneg_left h32 hμ.le
      _ = 2 * (BoseGases.a v) ^ (-(11 / 2) : ℝ) * μ * BoseGases.a v := by
          rw [← hA]; ring
  have hcmp : Ccoef * μ ^ ((5 : ℝ) / 2)
      ≤ (1 / 2)
        * ((4 * Ccoef * (BoseGases.a v) ^ (-(11 / 2) : ℝ) + 1) * μ * BoseGases.a v) := by
    have h1 := mul_le_mul_of_nonneg_left hg hCcoef
    have h2 : 0 ≤ (1 / 2) * (μ * BoseGases.a v) := by positivity
    have hexp : (1 / 2)
          * ((4 * Ccoef * (BoseGases.a v) ^ (-(11 / 2) : ℝ) + 1) * μ * BoseGases.a v)
        = Ccoef * (2 * (BoseGases.a v) ^ (-(11 / 2) : ℝ) * μ * BoseGases.a v)
          + (1 / 2) * (μ * BoseGases.a v) := by ring
    rw [hexp]
    linarith
  have hmain : Ccoef * μ ^ ((5 : ℝ) / 2)
      ≤ (1 / 2) * Work.BoseFixR.errKafz v R μ
          (4 * Ccoef * (BoseGases.a v) ^ (-(11 / 2) : ℝ) + 1) := by
    have h1 : (1 / 2) * ((4 * Ccoef * (BoseGases.a v) ^ (-(11 / 2) : ℝ) + 1) * μ * BoseGases.a v)
        ≤ (1 / 2) * Work.BoseFixR.errKafz v R μ
            (4 * Ccoef * (BoseGases.a v) ^ (-(11 / 2) : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hkafz (by norm_num)
    linarith
  calc Cost ≤ Ccoef * μ ^ ((5 : ℝ) / 2) * pL := hCost
    _ ≤ (1 / 2) * Work.BoseFixR.errKafz v R μ
          (4 * Ccoef * (BoseGases.a v) ^ (-(11 / 2) : ℝ) + 1) * pL :=
        mul_le_mul_of_nonneg_right hmain hpL

end Work.BoseBoxFock
