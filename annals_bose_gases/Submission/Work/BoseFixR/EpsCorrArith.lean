import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.BoseFixR.MulRpowNegQuarterLe
import Submission.Work.BoseFixR.PayMonomials
import Submission.Work.BoseFixR.RB5FSFixAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR

-- The scalar `ε`-correction comparison of the far leg.
--
-- Vocabulary (all from `Submission.Work.BoseFixR`, `v : ℝ³ → ℝ`):
--   `bigMV v μ      = Work.BoseBox.bigM (paramsAt μ (a v)) (a v) μ`   (FS's `𝓜`)
--   `ell v μ        = Work.BoseBox.sideAt μ (a v)`                    (FS's box side `ℓ`)
--   `epsFar v μ ρ   = Real.sqrt (bigMV v μ / ((ρ + μ) * ell v μ ^ 3))` (FS's `ε`)
--   `ErrRes v μ ρ   = 10^300 * ((ρ+μ) * a v * bigMV v μ
--                       + (ρ+μ) ^ (3/2) * a v * Real.sqrt (ell v μ ^ 3 * bigMV v μ))`
--
-- Strategy (worked out by hand; the only facts needed are `0 ≤ bigMV v μ`,
-- `0 < ρ + μ`, `10^300 ≥ 256` and `ρ ≤ ρ + μ`): writing `x = bigMV v μ / ((ρ+μ)*ell v μ ^3)`,
-- one has `(epsFar v μ ρ) ^ (-(1/2)) = x ^ (-(1/4))`, whence
--   `bigMV v μ * (epsFar v μ ρ)^(-(1/2)) ≤ bigMV v μ + Real.sqrt (bigMV v μ * (ρ+μ) * ell v μ ^ 3)`
-- (the substitution `u = bigMV v μ/((ρ+μ)*ell v μ^3)` reduces it to `u^(3/4) ≤ u + u^(1/2)`), and
-- then the first monomial of `ErrRes` pays `256 ρ a 𝓜` while the second pays
-- `256 ρ a Real.sqrt (𝓜(ρ+μ)ℓ³)` because `ρ ≤ ρ+μ` and `256 ≤ 10^300`.
-- (No diluteness is used: the statement is a purely algebraic inequality, and the
-- hypothesis `0 < ell v μ` is redundant in context but convenient.)
theorem EpsCorrArith {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ ρ : ℝ}
    (hμ : 0 < μ) (hav : 0 < BoseGases.a v) (hρ : 0 ≤ ρ)
    (hℓ : 0 < Work.BoseFixR.ell v μ) :
    256 * ρ * (Work.BoseFixR.epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v
        * Work.BoseFixR.bigMV v μ
      ≤ Work.BoseFixR.ErrRes v μ ρ := by
  set M := Work.BoseFixR.bigMV v μ with hMdef
  set R := ρ + μ with hRdef
  set L := Work.BoseFixR.ell v μ with hLdef
  set a := BoseGases.a v with hadef
  have hM : 0 ≤ M := by rw [hMdef]; exact Work.BoseFixR.bigMV_nonneg hμ hav
  have ha : 0 ≤ a := by rw [hadef]; exact hav.le
  have hL : 0 < L := by rw [hLdef]; exact hℓ
  have hR : 0 < R := by rw [hRdef]; linarith
  have hρR : ρ ≤ R := by rw [hRdef]; linarith
  have hL3 : 0 ≤ L ^ 3 := by positivity
  have hbase : 0 ≤ M / (R * L ^ 3) := div_nonneg hM (by positivity)
  -- `(ε)^(-1/2) = x^(-1/4)` with `x = 𝓜/((ρ+μ)ℓ³)`
  have heps : (Work.BoseFixR.epsFar v μ ρ) ^ (-(1 / 2 : ℝ))
      = (M / (R * L ^ 3)) ^ (-(1 / 4 : ℝ)) := by
    rw [Work.BoseFixR.epsFar, ← hMdef, ← hRdef, ← hLdef]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hbase]
    norm_num
  -- the `u^(3/4) ≤ u + u^(1/2)` step, in product form
  have hkey : M * (Work.BoseFixR.epsFar v μ ρ) ^ (-(1 / 2 : ℝ))
      ≤ M + Real.sqrt (M * R * L ^ 3) := by
    rw [heps]
    calc M * (M / (R * L ^ 3)) ^ (-(1 / 4 : ℝ))
        ≤ M + Real.sqrt (M * (R * L ^ 3)) :=
          MulRpowNegQuarterLe M (R * L ^ 3) hM (by positivity)
      _ = M + Real.sqrt (M * R * L ^ 3) := by rw [← mul_assoc]
  have hC : (256 : ℝ) ≤ 10 ^ 300 := by
    have h1 : (256 : ℝ) ≤ 10 ^ 3 := by norm_num
    have h2 : (10 : ℝ) ^ 3 ≤ 10 ^ 300 := pow_le_pow_right₀ (by norm_num) (by norm_num)
    exact le_trans h1 h2
  have hpay := PayMonomials a M R ρ (L ^ 3) (10 ^ 300) ha hM hρ hL3 hρR hR hC
  have hmul := mul_le_mul_of_nonneg_left hkey (by positivity : (0 : ℝ) ≤ 256 * ρ * a)
  rw [Work.BoseFixR.ErrRes, ← hMdef, ← hRdef, ← hLdef, ← hadef]
  nlinarith [hmul, hpay]

end Work.BoseFixR
