import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseBoxFock.W2Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

/-- **The three-line arithmetic of the box → model bridge** (`box_to_model.lean`'s
`hrĒ`/`hEE`), at FS's parameter choice `paramsAt μ (a v)`:

there is a diluteness threshold `ε₀` and an error constant `C` such that for every
admissible chemical potential `μ` (so `t := μ (a v)³ ≤ ε₀`) and every `J` below the
a-priori level `K_B³`,

* `errB v R μ ≤ errKafz v R μ C` (the bridge error `E = errB` is dominated by the
  `thm:Kafz` error `Ē = errKafz`), and
* `ℓ³·Θ(a v, J, μ) + errKafz v R μ C ≤ 0` (the a-priori threshold `Θ` beats `errKafz`).

Both are pure `rpow` arithmetic at the concrete parameter block `fsParams t`
(`d = t^{6/323}`, `K_ℓ = t^{-3/646}`, `K_B = t^{-6/323}`, `ℓ = a t^{-163/323}`):
with `t → 0⁺` the LHY scale `ℓ³ ∼ t^{-489/323}` (times `a³`) dominates every error
term, and the a-priori level `Θ ≤ 0` is `−4πμ²aℓ³(1 − J√t)` with `J√t ≤ t^{287/646}`.
The proof takes `C = 1` and `ε₀ = min (1/36) ((a²/(2R²))⁴)`: the second entry makes
`max_t (R/a)² t^{160/323} ≤ 1/2` and `max_t (R/a)² t ≤ 1/2`, the first makes
`√t ≤ 1/6` and `t^{1/4} ≤ 1/2`. -/
theorem err_arith {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hav : 0 < BoseGases.a v)
    {R : ℝ} (hR : 0 < R) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 < C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ J : ℝ,
        J ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).KB ^ 3 →
        Work.BoseBoxFock.errB v R μ ≤ Work.BoseFixR.errKafz v R μ C ∧
        Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 * Work.UBB.Theta (BoseGases.a v) J μ
          + Work.BoseFixR.errKafz v R μ C ≤ 0 := by
  refine ⟨min (1/36) (((BoseGases.a v)^2 / (2*R^2))^4), 1, ?_, one_pos, ?_⟩
  · exact lt_min (by norm_num) (by positivity)
  · intro μ hAdm J hJ
    obtain ⟨hμpos, htε, _⟩ := hAdm
    set A := BoseGases.a v with hAdef
    set t := μ * A ^ 3 with htdef
    have ht0 : 0 < t := by rw [htdef]; positivity
    have ht1 : t ≤ 1 := htε.trans (le_trans (min_le_left _ _) (by norm_num))
    have ht36 : t ≤ 1/36 := htε.trans (min_le_left _ _)
    -- the box side, `ℓ = a t^{-163/323}`
    have hside : Work.BoseBox.sideAt μ A = A * t ^ (-(163/323:ℝ)) := by
      rw [Work.BoseBox.sideAt_eq_rpow hav hμpos, ← htdef]
    have hℓpos : 0 < Work.BoseBox.sideAt μ A := by rw [hside]; positivity
    have hpre : 0 ≤ μ^2 * A * (Work.BoseBox.sideAt μ A)^3 := by positivity
    -- `t → 0` bounds
    have hta : t ≤ t^(1/4:ℝ) := by
      have h := Real.rpow_le_rpow_of_exponent_ge ht0 ht1 (by norm_num : (1:ℝ)/4 ≤ 1)
      rwa [Real.rpow_one] at h
    have htquart : t^(1/4:ℝ) ≤ A^2/(2*R^2) := by
      have h1 : t ≤ ((A^2/(2*R^2))^4) := htε.trans (min_le_right _ _)
      have hx0 : 0 ≤ A^2/(2*R^2) := by positivity
      have h := Real.rpow_le_rpow ht0.le h1 (by norm_num : (0:ℝ) ≤ 1/4)
      rw [← Real.rpow_natCast (A^2/(2*R^2)) 4, ← Real.rpow_mul hx0 ((4:ℕ):ℝ) (1/4)] at h
      rw [show ((4:ℕ):ℝ) * (1/4) = (1:ℝ) by norm_num, Real.rpow_one] at h
      exact h
    have hta2 : t ≤ A^2/(2*R^2) := hta.trans htquart
    have hb2 : (R/A)^2 * t^(160/323:ℝ) ≤ 1/2 := by
      have h1 : t^(160/323:ℝ) ≤ t^(1/4:ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge ht0 ht1 (by norm_num : (1:ℝ)/4 ≤ 160/323)
      have hR2 : 0 ≤ (R/A)^2 := by positivity
      have h2 : (R/A)^2 * t^(160/323:ℝ) ≤ (R/A)^2 * (A^2/(2*R^2)) :=
        mul_le_mul_of_nonneg_left (h1.trans htquart) hR2
      have h3 : (R/A)^2 * (A^2/(2*R^2)) = 1/2 := by field_simp
      linarith [h2, le_of_eq h3]
    have hb2' : (R/A)^2 * t ≤ 1/2 := by
      have hR2 : 0 ≤ (R/A)^2 := by positivity
      have h2 : (R/A)^2 * t ≤ (R/A)^2 * (A^2/(2*R^2)) := mul_le_mul_of_nonneg_left hta2 hR2
      have h3 : (R/A)^2 * (A^2/(2*R^2)) = 1/2 := by field_simp
      linarith [h2, le_of_eq h3]
    -- the parameter monomials
    have hd : (Work.BoseBox.paramsAt μ A).d ^
        (2 * ((Work.BoseBox.paramsAt μ A).M - 1)) = t ^ (564 / 323 : ℝ) := by
      have hM : (Work.BoseBox.paramsAt μ A).M = 48 := rfl
      have hdd : (Work.BoseBox.paramsAt μ A).d = (μ * A ^ 3) ^ ((6:ℝ)/323) := rfl
      have htA : (0:ℝ) ≤ μ * A^3 := le_of_lt (by positivity)
      rw [hM, hdd, ← Real.rpow_natCast ((μ * A ^ 3) ^ ((6:ℝ)/323)) 94,
        ← Real.rpow_mul htA ((6:ℝ)/323) ((94:ℕ):ℝ)]
      rw [show ((6:ℝ)/323) * ((94:ℕ):ℝ) = (564:ℝ)/323 by norm_num, ← htdef]
    have hKl : (Work.BoseBox.paramsAt μ A).Kl ^ (-(3:ℝ)) = t ^ (9/646:ℝ) := by
      have hKl0 : (Work.BoseBox.paramsAt μ A).Kl = t ^ (-(3/646:ℝ)) := by
        rw [show (Work.BoseBox.paramsAt μ A).Kl = (μ * A^3) ^ (-(3/646:ℝ)) by
          simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.fsXp]
          norm_num, ← htdef]
      rw [hKl0, ← Real.rpow_mul ht0.le (-(3/646:ℝ)) (-(3:ℝ))]
      norm_num
    have hKB3 : (Work.BoseBox.paramsAt μ A).KB ^ 3 = t ^ (-(18/323):ℝ) := by
      have hKB0 : (Work.BoseBox.paramsAt μ A).KB = t ^ (-(6/323:ℝ)) := by
        rw [show (Work.BoseBox.paramsAt μ A).KB = (μ * A^3) ^ (-(6/323:ℝ)) by
          simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.fsXp]
          norm_num, ← htdef]
      rw [hKB0, ← Real.rpow_natCast (t^(-(6/323:ℝ))) 3,
        ← Real.rpow_mul ht0.le (-(6/323:ℝ)) ((3:ℕ):ℝ)]
      norm_num
    have hfsX0 : Work.BoseFixR.fsX v μ = t ^ (1/323:ℝ) := by
      simp only [Work.BoseFixR.fsX, Work.BoseFixR.dil, Work.BoseBox.fsXp, ← hAdef, ← htdef]
    have hfsX2 : Work.BoseFixR.fsX v μ ^ 2 = t ^ (2/323:ℝ) := by
      rw [hfsX0, ← Real.rpow_natCast (t^(1/323:ℝ)) 2,
        ← Real.rpow_mul ht0.le (1/323:ℝ) ((2:ℕ):ℝ)]
      norm_num
    have herrExp : Work.BoseFixR.errExp v μ = t ^ (1/1615:ℝ) := by
      simp only [Work.BoseFixR.errExp, Work.BoseFixR.dil, ← hAdef, ← htdef]
    -- `errB` and `errKafz` in monomial form
    have herrB : Work.BoseBoxFock.errB v R μ
        = μ^2 * A * (Work.BoseBox.sideAt μ A)^3
          * (t ^ (564/323:ℝ) + R^2 / (Work.BoseBox.sideAt μ A)^2) := by
      simp only [Work.BoseBoxFock.errB]
      rw [hd]
    have hEform : Work.BoseFixR.errKafz v R μ 1
        = (1 * μ^2 * A * (Work.BoseBox.sideAt μ A)^3 * Real.sqrt t)
          * ((Work.BoseBox.paramsAt μ A).Kl ^ (-(3:ℝ)) + Work.BoseFixR.fsX v μ ^ 2
              + (R/A)^2 * Real.sqrt t + Work.BoseFixR.errExp v μ) := by
      simp only [Work.BoseFixR.errKafz, Work.BoseFixR.ell3, Work.BoseFixR.ell,
        Work.BoseFixR.dil, ← hAdef, ← htdef]
    have hΘ : Work.UBB.Theta A J μ = -(4 * Real.pi * μ^2 * A * (1 - J * Real.sqrt t)) := by
      simp only [Work.UBB.Theta, ← htdef]
    constructor
    · -- conjunct 1: `errB ≤ errKafz`
      have hℓ2 : (Work.BoseBox.sideAt μ A)^2 = A^2 * t ^ (-(326/323:ℝ)) := by
        rw [hside, mul_pow, ← Real.rpow_natCast (t ^ (-(163/323:ℝ))) 2,
          ← Real.rpow_mul ht0.le (-(163/323:ℝ)) ((2:ℕ):ℝ)]
        norm_num
      have hinv : R^2 / (Work.BoseBox.sideAt μ A)^2 = (R/A)^2 * t ^ (326/323:ℝ) := by
        have hpt : (t ^ (-(326/323:ℝ)))⁻¹ = t ^ (326/323:ℝ) := by
          rw [← Real.rpow_neg ht0.le, neg_neg]
        rw [div_eq_mul_inv, hℓ2, mul_inv_rev, hpt] ; ring
      have hsp1 : t^(564/323:ℝ) = t^(166/323:ℝ) * t^(398/323:ℝ) := by
        rw [← Real.rpow_add ht0]; norm_num
      have hsp2 : t^(326/323:ℝ) = t^(166/323:ℝ) * t^(160/323:ℝ) := by
        rw [← Real.rpow_add ht0]; norm_num
      have hsplit : t ^ (564/323:ℝ) + R^2 / (Work.BoseBox.sideAt μ A)^2
          = t^(166/323:ℝ) * (t^(398/323:ℝ) + (R/A)^2 * t^(160/323:ℝ)) := by
        rw [hsp1, hinv, hsp2] ; ring
      have hb1 : t^(398/323:ℝ) ≤ 1/2 := by
        have h := Real.rpow_le_rpow_of_exponent_ge ht0 ht1 (by norm_num : (1:ℝ) ≤ 398/323)
        rw [Real.rpow_one] at h
        linarith
      have hbr : t^(398/323:ℝ) + (R/A)^2 * t^(160/323:ℝ) ≤ 1 := by linarith
      have hbr2 : (Work.BoseBox.paramsAt μ A).Kl ^ (-(3:ℝ))
          ≤ (Work.BoseBox.paramsAt μ A).Kl ^ (-(3:ℝ)) + Work.BoseFixR.fsX v μ ^ 2
              + (R/A)^2 * Real.sqrt t + Work.BoseFixR.errExp v μ := by
        have h1 : 0 ≤ Work.BoseFixR.fsX v μ ^ 2 := sq_nonneg _
        have h2 : 0 ≤ (R/A)^2 * Real.sqrt t := mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
        have h3 : 0 ≤ Work.BoseFixR.errExp v μ := by
          rw [herrExp]; exact Real.rpow_nonneg ht0.le _
        linarith
      have hsup : 0 ≤ 1 * μ^2 * A * (Work.BoseBox.sideAt μ A)^3 * Real.sqrt t := by positivity
      have hE : μ^2 * A * (Work.BoseBox.sideAt μ A)^3 * t^(166/323:ℝ)
          ≤ Work.BoseFixR.errKafz v R μ 1 := by
        have hpow166 : (t^(1/2:ℝ)) * t^(9/646:ℝ) = t^(166/323:ℝ) := by
          rw [← Real.rpow_add ht0]; norm_num
        have heq1 : μ^2 * A * (Work.BoseBox.sideAt μ A)^3 * t^(166/323:ℝ)
            = (1 * μ^2 * A * (Work.BoseBox.sideAt μ A)^3 * Real.sqrt t)
              * (Work.BoseBox.paramsAt μ A).Kl ^ (-(3:ℝ)) := by
          rw [hKl, Real.sqrt_eq_rpow, ← hpow166] ; ring
        rw [hEform, heq1]
        exact mul_le_mul_of_nonneg_left hbr2 hsup
      calc Work.BoseBoxFock.errB v R μ
          = μ^2 * A * (Work.BoseBox.sideAt μ A)^3
              * (t ^ (564/323:ℝ) + R^2 / (Work.BoseBox.sideAt μ A)^2) := herrB
        _ = μ^2 * A * (Work.BoseBox.sideAt μ A)^3
              * (t^(166/323:ℝ) * (t^(398/323:ℝ) + (R/A)^2 * t^(160/323:ℝ))) := by rw [hsplit]
        _ ≤ μ^2 * A * (Work.BoseBox.sideAt μ A)^3 * (t^(166/323:ℝ) * 1) := by
            have h166 : 0 ≤ t^(166/323:ℝ) := Real.rpow_nonneg ht0.le _
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbr h166) hpre
        _ = μ^2 * A * (Work.BoseBox.sideAt μ A)^3 * t^(166/323:ℝ) := by ring
        _ ≤ Work.BoseFixR.errKafz v R μ 1 := hE
    · -- conjunct 2: the a-priori level beats `errKafz`
      have hbr3 : (Work.BoseBox.paramsAt μ A).Kl ^ (-(3:ℝ)) + Work.BoseFixR.fsX v μ ^ 2
          + (R/A)^2 * Real.sqrt t + Work.BoseFixR.errExp v μ ≤ 3 + (R/A)^2 * Real.sqrt t := by
        have h1 : (Work.BoseBox.paramsAt μ A).Kl ^ (-(3:ℝ)) ≤ 1 := by
          rw [hKl]; exact Real.rpow_le_one ht0.le ht1 (by norm_num)
        have h2 : Work.BoseFixR.fsX v μ ^ 2 ≤ 1 := by
          rw [hfsX2]; exact Real.rpow_le_one ht0.le ht1 (by norm_num)
        have h3 : Work.BoseFixR.errExp v μ ≤ 1 := by
          rw [herrExp]; exact Real.rpow_le_one ht0.le ht1 (by norm_num)
        linarith
      have hsqrt6 : Real.sqrt t ≤ 1/6 := by
        have h := Real.sqrt_le_sqrt ht36
        have h36 : Real.sqrt ((1:ℝ)/36) = 1/6 := by
          rw [show ((1:ℝ)/36) = (1/6)^2 by norm_num, Real.sqrt_sq_eq_abs]; norm_num
        rwa [h36] at h
      have hEub : Work.BoseFixR.errKafz v R μ 1 ≤ μ^2 * A * (Work.BoseBox.sideAt μ A)^3 := by
        have hb : Real.sqrt t * ((Work.BoseBox.paramsAt μ A).Kl ^ (-(3:ℝ))
            + Work.BoseFixR.fsX v μ ^ 2
            + (R/A)^2 * Real.sqrt t + Work.BoseFixR.errExp v μ) ≤ 1 := by
          have h1 : Real.sqrt t * ((Work.BoseBox.paramsAt μ A).Kl ^ (-(3:ℝ))
              + Work.BoseFixR.fsX v μ ^ 2
              + (R/A)^2 * Real.sqrt t + Work.BoseFixR.errExp v μ)
              ≤ Real.sqrt t * (3 + (R/A)^2 * Real.sqrt t) :=
            mul_le_mul_of_nonneg_left hbr3 (Real.sqrt_nonneg t)
          have hsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt (le_of_lt ht0)
          have h2 : Real.sqrt t * (3 + (R/A)^2 * Real.sqrt t)
              = 3 * Real.sqrt t + (R/A)^2 * t := by
            rw [mul_add, mul_comm (Real.sqrt t) ((R/A)^2 * Real.sqrt t), mul_assoc, hsq]
            ring
          have h3 : 3 * Real.sqrt t + (R/A)^2 * t ≤ 1 := by linarith
          linarith
        calc Work.BoseFixR.errKafz v R μ 1
            = μ^2 * A * (Work.BoseBox.sideAt μ A)^3
                * (Real.sqrt t * ((Work.BoseBox.paramsAt μ A).Kl ^ (-(3:ℝ))
                  + Work.BoseFixR.fsX v μ ^ 2
                  + (R/A)^2 * Real.sqrt t + Work.BoseFixR.errExp v μ)) := by rw [hEform]; ring
          _ ≤ μ^2 * A * (Work.BoseBox.sideAt μ A)^3 * 1 := mul_le_mul_of_nonneg_left hb hpre
          _ = μ^2 * A * (Work.BoseBox.sideAt μ A)^3 := by ring
      have hJt : J * Real.sqrt t ≤ 1/2 := by
        have h1 : J * Real.sqrt t ≤ t ^ (-(18/323):ℝ) * Real.sqrt t := by
          rw [← hKB3]; exact mul_le_mul_of_nonneg_right hJ (Real.sqrt_nonneg t)
        have h2 : t ^ (-(18/323):ℝ) * Real.sqrt t = t ^ (287/646:ℝ) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht0]; norm_num
        have h3 : t ^ (287/646:ℝ) ≤ 1/2 := by
          have ha : t^(287/646:ℝ) ≤ t^(1/4:ℝ) :=
            Real.rpow_le_rpow_of_exponent_ge ht0 ht1 (by norm_num : (1:ℝ)/4 ≤ 287/646)
          have hb : t^(1/4:ℝ) ≤ ((1:ℝ)/36)^(1/4:ℝ) :=
            Real.rpow_le_rpow ht0.le ht36 (by norm_num)
          have hc : ((1:ℝ)/36)^(1/4:ℝ) ≤ 1/2 := by
            have h4 : ((1:ℝ)/36)^(1/4:ℝ) ≤ ((1:ℝ)/16)^(1/4:ℝ) :=
              Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
            have h5 : ((1:ℝ)/16)^(1/4:ℝ) = 1/2 := by
              rw [show ((1:ℝ)/16) = ((1:ℝ)/2)^4 by norm_num,
                ← Real.rpow_natCast ((1:ℝ)/2) 4,
                ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 1/2) ((4:ℕ):ℝ) (1/4)]
              rw [show ((4:ℕ):ℝ)*(1/4) = 1 by norm_num, Real.rpow_one]
            linarith
          linarith
        linarith
      have hTh : (Work.BoseBox.sideAt μ A)^3 * Work.UBB.Theta A J μ
          = -(4 * Real.pi * μ^2 * A * (Work.BoseBox.sideAt μ A)^3)
              * (1 - J * Real.sqrt t) := by
        rw [hΘ]; ring
      have hkey : 1 - 4 * Real.pi * (1 - J * Real.sqrt t) ≤ 0 := by
        nlinarith [hJt, Real.pi_gt_three, Real.pi_pos]
      calc (Work.BoseBox.sideAt μ A)^3 * Work.UBB.Theta A J μ + Work.BoseFixR.errKafz v R μ 1
          ≤ -(4 * Real.pi * μ^2 * A * (Work.BoseBox.sideAt μ A)^3) * (1 - J * Real.sqrt t)
              + μ^2 * A * (Work.BoseBox.sideAt μ A)^3 := by rw [hTh]; linarith
        _ = μ^2 * A * (Work.BoseBox.sideAt μ A)^3
              * (1 - 4 * Real.pi * (1 - J * Real.sqrt t)) := by ring
        _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hpre hkey

end Work.BoseBoxFock
