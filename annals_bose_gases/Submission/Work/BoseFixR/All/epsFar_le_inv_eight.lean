import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.BoseFixR.All.RB5FSFixAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `epsFar ≤ 10^{-8}` on the admissible box data

FS `eq:ChoiceEpsilon` chooses the optimisation parameter of `lem:Roughbounds`
(`prop:FarAway`, `final_v2.tex` §9) as

  `ε = √(𝓜 / ((μ+ρ)ℓ³))`,  `𝓜 = K_𝓜(μa³)^{-1/4}`,  `ℓ = K_ℓ(μa)^{-1/2}`

(`Work.BoseFixR.All.epsFar`, `Work.BoseFixR.bigMV`, `Work.BoseFixR.ell`).  The
downstream consumers of the far leg (`FarEnvPos`, `FarResidBaux.farEnvSideB`)
take `ε ≤ 1/10^8` as a hypothesis; this file produces it from the admissibility
`Work.BoseBoxFix.Adm` at the smallness `ε₀ ≤ 10^{-4000}`.

At FS's concrete parameter choice `K_𝓜 = X^{-1}`, `K_ℓ = X^{-3/2}`,
`X = (μa³)^{1/323}` the whole bound is a *monomial comparison*: writing
`t = μa³`, `A = a v`,

  `ε² = 𝓜/((ρ+μ)ℓ³) = fsXp t (-1)·t^{-1/4} / ((ρ+μ)·A³·fsXp t (-489))
      ≤ fsXp t (-1)·t^{-1/4}·fsXp t 489/(μ A³)   (ρ ≥ 0)
      = fsXp t (337/4) ≤ fsXp t (323/4) = t^{1/4}`,

and `t^{1/4} ≤ (10^{-4000})^{1/4} = 10^{-1000} ≤ (1/10^8)²`.  Only the
monotonicity `fsXp_le_fsXp` of `c ↦ t^{c/323}` (for `0 < t ≤ 1`) and the closed
forms `bigMV`, `ell³ = A³ fsXp t (-489)` (`RegimeAux.sideAt_cube_eq`) are used.

The hypothesis `FarCondFS` is not needed for the bound (it holds for every `ρ ≥ 0`);
it is carried because the request states it.
-/

namespace Work.BoseFixR.All.FarResidBaux

open Work.BoseBox

set_option linter.unusedVariables false

/-- **The monomial core of the `ε`-bound**: at `0 < A`, `0 < μ`, `0 ≤ ρ` and
`t = μA³ ≤ 1`,

  `𝓜/((ρ+μ)ℓ³) ≤ (μA³)^{1/4} = t^{1/4}`.

(`𝓜 = fsXp t (-1)·t^{-1/4}`, `ℓ³ = A³·fsXp t (-489)`, so the numerator
`fsXp t (-1) fsXp t 489 = fsXp t 488` pays the `fsXp t (-489)` of the box side,
and the resulting `fsXp t 488·t^{-5/4} = fsXp t (337/4)` is below
`fsXp t (323/4) = t^{1/4}`.) -/
lemma bigMV_div_ell_cube_le_quarter {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ ρ : ℝ}
    (hav : 0 < BoseGases.a v) (hμ : 0 < μ) (hρ : 0 ≤ ρ)
    (hle1 : μ * BoseGases.a v ^ 3 ≤ 1) :
    Work.BoseFixR.bigMV v μ / ((ρ + μ) * Work.BoseFixR.ell v μ ^ 3)
      ≤ (μ * BoseGases.a v ^ 3) ^ (1 / 4 : ℝ) := by
  set t : ℝ := μ * BoseGases.a v ^ 3 with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht1 : t ≤ 1 := by rw [ht]; exact hle1
  have hA : 0 < BoseGases.a v := hav
  have hbigM : Work.BoseFixR.bigMV v μ = fsXp t (-1) * t ^ (-(1 / 4 : ℝ)) := by
    rw [ht]
    simp only [Work.BoseFixR.bigMV, Work.BoseBox.bigM, Work.BoseBox.paramsAt,
      Work.BoseBox.fsParams, Work.BoseBox.fsXp]
  have hell3 : Work.BoseFixR.ell v μ ^ 3 = (BoseGases.a v) ^ 3 * fsXp t (-489) := by
    rw [ht]
    rw [Work.BoseFixR.ell]
    exact Work.BoseFixB1.sideAt_cube_eq hA hμ
  -- the two ends of the chain, both equal to `fsXp t (-(327/4))`
  have hLHS : fsXp t (-1) * t ^ (-(1 / 4 : ℝ)) = fsXp t (-(327 / 4)) := by
    rw [show t ^ (-(1 / 4 : ℝ)) = fsXp t (-(323 / 4)) by rw [fsXp]; norm_num]
    rw [fsXp_mul ht0]
    norm_num
  have hRHS : fsXp t (337 / 4) * t * fsXp t (-489) = fsXp t (-(327 / 4)) := by
    nth_rewrite 2 [show t = fsXp t 323 by rw [fsXp]; norm_num]
    rw [fsXp_mul ht0, fsXp_mul ht0]
    norm_num
  have hden2 : μ * ((BoseGases.a v) ^ 3 * fsXp t (-489)) = t * fsXp t (-489) := by
    rw [ht]; ring
  have hden : μ * ((BoseGases.a v) ^ 3 * fsXp t (-489))
      ≤ (ρ + μ) * ((BoseGases.a v) ^ 3 * fsXp t (-489)) := by
    apply mul_le_mul_of_nonneg_right _ (by
      exact mul_nonneg (pow_nonneg (le_of_lt hA) 3) (le_of_lt (fsXp_pos ht0)))
    linarith
  have hmain : fsXp t (-1) * t ^ (-(1 / 4 : ℝ))
      ≤ fsXp t (337 / 4) * ((ρ + μ) * ((BoseGases.a v) ^ 3 * fsXp t (-489))) := by
    rw [hLHS]
    rw [← hRHS]
    calc fsXp t (337 / 4) * t * fsXp t (-489)
        = fsXp t (337 / 4) * (t * fsXp t (-489)) := by ring
      _ = fsXp t (337 / 4) * (μ * ((BoseGases.a v) ^ 3 * fsXp t (-489))) := by
            rw [← hden2]
      _ ≤ fsXp t (337 / 4) * ((ρ + μ) * ((BoseGases.a v) ^ 3 * fsXp t (-489))) :=
            mul_le_mul_of_nonneg_left hden (le_of_lt (fsXp_pos ht0))
  have hkey : Work.BoseFixR.bigMV v μ / ((ρ + μ) * Work.BoseFixR.ell v μ ^ 3)
      ≤ fsXp t (337 / 4) := by
    rw [hbigM, hell3]
    rw [div_le_iff₀ (mul_pos (by linarith : (0 : ℝ) < ρ + μ)
      (mul_pos (pow_pos hA 3) (fsXp_pos ht0)))]
    exact hmain
  calc Work.BoseFixR.bigMV v μ / ((ρ + μ) * Work.BoseFixR.ell v μ ^ 3)
      ≤ fsXp t (337 / 4) := hkey
    _ ≤ fsXp t (323 / 4) := fsXp_le_fsXp ht0 ht1 (by norm_num)
    _ = (μ * BoseGases.a v ^ 3) ^ (1 / 4 : ℝ) := by rw [fsXp, ht]; norm_num

/-- **The numeric step**: `t^{1/4} ≤ (1/10^8)²` for `0 < t ≤ 10^{-4000}`
(the fourth power of the left side is `t`, that of the right side is
`(1/10^8)^8 = 10^{-64} ≥ 10^{-4000}`). -/
lemma quarter_rpow_le {t : ℝ} (ht0 : 0 < t) (htle : t ≤ (10 : ℝ) ^ (-(4000 : ℤ))) :
    t ^ (1 / 4 : ℝ) ≤ (1 / 10 ^ 8) ^ 2 := by
  have ht64 : t ≤ (1 / 10 ^ 8 : ℝ) ^ 8 := by
    have h2 : (10 : ℝ) ^ (-(4000 : ℤ)) ≤ (1 / 10 ^ 8 : ℝ) ^ 8 := by
      rw [show (1 / 10 ^ 8 : ℝ) ^ 8 = 1 / 10 ^ 64 by norm_num,
          show (10 : ℝ) ^ (-(4000 : ℤ)) = 1 / 10 ^ 4000 by norm_num]
      exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 10 ^ 64)
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 10) (by norm_num : (64 : ℕ) ≤ 4000))
    linarith
  have hx : (0 : ℝ) ≤ t ^ (1 / 4 : ℝ) := Real.rpow_nonneg (le_of_lt ht0) _
  have hy : (0 : ℝ) ≤ (1 / 10 ^ 8 : ℝ) ^ 2 := by norm_num
  rw [← pow_le_pow_iff_left₀ hx hy (by norm_num : (4 : ℕ) ≠ 0)]
  rw [show (t ^ (1 / 4 : ℝ)) ^ 4 = t by
        rw [← Real.rpow_natCast (t ^ (1 / 4 : ℝ)) 4, ← Real.rpow_mul (le_of_lt ht0),
          show (1 / 4 : ℝ) * ((4 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]]
  rw [← pow_mul, show (2 : ℕ) * 4 = 8 by norm_num]
  exact ht64

theorem epsFar_le_inv_eight {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ ρ ε₀ : ℝ}
    (hAdm : Work.BoseBoxFix.Adm v ε₀ μ) (hε₀ : ε₀ ≤ 10 ^ (-(4000 : ℤ)))
    (hav : 0 < BoseGases.a v) (hρ : 0 ≤ ρ) (hfar : Work.BoseBoxFock.FarCondFS v μ ρ) :
    Work.BoseFixR.All.epsFar v μ ρ ≤ 1 / 10 ^ 8 := by
  have hμ : 0 < μ := hAdm.1
  have ht0 : 0 < μ * BoseGases.a v ^ 3 := by positivity
  have htle : μ * BoseGases.a v ^ 3 ≤ (10 : ℝ) ^ (-(4000 : ℤ)) := hAdm.2.1.trans hε₀
  have hle1 : μ * BoseGases.a v ^ 3 ≤ 1 := by
    have h1 : (10 : ℝ) ^ (-(4000 : ℤ)) ≤ 1 := by
      rw [show (10 : ℝ) ^ (-(4000 : ℤ)) = 1 / 10 ^ 4000 by norm_num, one_div]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 10))
    linarith
  have hsq : Work.BoseFixR.bigMV v μ / ((ρ + μ) * Work.BoseFixR.ell v μ ^ 3)
      ≤ (1 / 10 ^ 8) ^ 2 :=
    le_trans (bigMV_div_ell_cube_le_quarter hav hμ hρ hle1) (quarter_rpow_le ht0 htle)
  rw [Work.BoseFixR.All.epsFar]
  exact (Real.sqrt_le_iff).mpr ⟨by norm_num, hsq⟩

end Work.BoseFixR.All.FarResidBaux
