import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseBogFS.CleanFunAux
import Submission.Work.BoseBogFS.CleanRowDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.cleanBracketArith` — the monomial arithmetic of the clean
# Riemann row

The rows `cleanFun_tsum_le_integral` and `integral_cleanFun_le` both produce errors
proportional to the bracket

`errBracket v R μ = μ²·a v·ℓ³·√(μa³)·(X² + (R/a v)²·√(μa³) + (μa³)^{1/1615})`, `X = (μa³)^{1/323}`,

and the *natural* size of the lattice excess of `cleanFun` is `β²/m²` with
`β = cleanCB = cleanRhoB·16πa` and `m = 2π/ℓ`.  This module records the elementary facts that
make every such comparison close with a **fixed absolute constant**:

* `β²/m² ≤ 256·errBracket`; this uses the `errExp = (μa³)^{1/1615}` term of the bracket
  (the `X²` term is too small by `X^{-1/2}`) and the exact identity `ℓ = a·(μa³)^{-163/323}`.
  The exponent bookkeeping is `-(163/323) + 1/2 + 1/1615 = -13/3230`, so the ratio is
  `256·(μa³)^{13/3230} = 256·X^{13/10} ≤ 256` for `μa³ ≤ 1`.
* `cleanRhoB ≤ 2μ` (the `CloseCondFS` correction is a small fraction of `μ`).

Everything here is `sorry`-free and independent of all analysis.
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The one-body kernel parameter `K_ℓ = fsXp (μa³) (-3/2)` is positive. -/
lemma cleanKl_pos {v : E3 → ℝ} {μ : ℝ} (hav : 0 < a v) (hμ : 0 < μ) :
    0 < (Work.BoseBox.paramsAt μ (a v)).Kl := by
  have ht : 0 < dil v μ := by rw [dil]; positivity
  exact Work.BoseBox.fsXp_pos (t := dil v μ) (c := (-(3 / 2 : ℝ))) ht

/-- **`K_ℓ^{-2} = (μa³)^{3/323}`** at the frozen parameters.  (`K_ℓ = t^{-3/646}` and
`-2·(-3/646) = 3/323`.) -/
lemma cleanKl_inv_sq {v : E3 → ℝ} {μ : ℝ} (hav : 0 < a v) (hμ : 0 < μ) :
    (Work.BoseBox.paramsAt μ (a v)).Kl ^ (-(2 : ℝ)) = (dil v μ) ^ (3 / 323 : ℝ) := by
  have ht : 0 < dil v μ := by rw [dil]; positivity
  show (Work.BoseBox.fsXp (dil v μ) (-(3 / 2))) ^ (-(2 : ℝ)) = (dil v μ) ^ (3 / 323 : ℝ)
  rw [Work.BoseBox.fsXp, ← Real.rpow_mul ht.le]
  congr 1
  norm_num

/-- **The `CloseCondFS` correction is a small fraction of `μ`.**  For diluteness `≤ 1` the
extra term `μ·K_ℓ^{-2}/(2^{14}π)` is at most `μ`. -/
lemma cleanRhoB_le_two_mul {v : E3 → ℝ} {μ : ℝ} (hav : 0 < a v) (hμ : 0 < μ)
    (hdil : dil v μ ≤ 1) : cleanRhoB v μ ≤ 2 * μ := by
  have ht : 0 < dil v μ := by rw [dil]; positivity
  have hpow : (dil v μ) ^ (3 / 323 : ℝ) ≤ 1 := by
    have h := Real.rpow_le_rpow ht.le hdil (show (0 : ℝ) ≤ 3 / 323 by norm_num)
    rwa [Real.one_rpow] at h
  have hKl : (Work.BoseBox.paramsAt μ (a v)).Kl ^ (-(2 : ℝ)) ≤ 1 := by
    rw [cleanKl_inv_sq hav hμ]; exact hpow
  have hden : (0 : ℝ) < (2 : ℝ) ^ 14 * Real.pi := by positivity
  have hfrac : μ * (Work.BoseBox.paramsAt μ (a v)).Kl ^ (-(2 : ℝ)) / ((2 : ℝ) ^ 14 * Real.pi)
      ≤ μ := by
    rw [div_le_iff₀ hden]
    have hKl0 : (0 : ℝ) ≤ (Work.BoseBox.paramsAt μ (a v)).Kl ^ (-(2 : ℝ)) := by
      have := Real.rpow_nonneg (le_of_lt (cleanKl_pos hav hμ)) (-(2 : ℝ))
      simpa using this
    have hbig : (1 : ℝ) ≤ (2 : ℝ) ^ 14 * Real.pi := by
      nlinarith [Real.pi_gt_three]
    nlinarith [hKl, hKl0, hμ, hbig, hden]
  rw [cleanRhoB]
  linarith

/-- **`ℓ/a` is the diluteness power**: `ℓ = a·(μa³)^{-163/323}`. -/
lemma ell_eq_mul_rpow {v : E3 → ℝ} {μ : ℝ} (hav : 0 < a v) (hμ : 0 < μ) :
    ell v μ = a v * (dil v μ) ^ (-(163 / 323 : ℝ)) := by
  rw [ell_eq, Work.BoseBox.sideAt_eq_rpow hav hμ, dil]

/-- **The exponent identity of the bracket**:
`ℓ·√(μa³)·(μa³)^{1/1615} = a·(μa³)^{-13/3230}`. -/
lemma ell_mul_sqrt_mul_errExp {v : E3 → ℝ} {μ : ℝ} (hav : 0 < a v) (hμ : 0 < μ) :
    ell v μ * Real.sqrt (dil v μ) * errExp v μ
      = a v * (dil v μ) ^ (-(13 / 3230 : ℝ)) := by
  have ht : 0 < dil v μ := by rw [dil]; positivity
  have hexp : -(163 / 323 : ℝ) + 1 / 2 + 1 / 1615 = -(13 / 3230 : ℝ) := by norm_num
  have h1 : (dil v μ) ^ (-(163 / 323 : ℝ)) * Real.sqrt (dil v μ) * errExp v μ
      = (dil v μ) ^ (-(13 / 3230 : ℝ)) := by
    have hs : Real.sqrt (dil v μ) = (dil v μ) ^ ((1 / 2 : ℝ)) := Real.sqrt_eq_rpow _
    rw [hs, errExp, ← Real.rpow_add ht, ← Real.rpow_add ht, hexp]
  calc ell v μ * Real.sqrt (dil v μ) * errExp v μ
      = (a v * (dil v μ) ^ (-(163 / 323 : ℝ))) * Real.sqrt (dil v μ) * errExp v μ := by
        rw [ell_eq_mul_rpow hav hμ]
    _ = a v * ((dil v μ) ^ (-(163 / 323 : ℝ)) * Real.sqrt (dil v μ) * errExp v μ) := by ring
    _ = a v * (dil v μ) ^ (-(13 / 3230 : ℝ)) := by rw [h1]

/-- **The clean bracket beats `β²/m²` with a fixed constant.**

With `β = cleanCB v μ` and `m = 2π/ℓ` (= `2π / ell v μ`), the natural scale `β²/m²` of the
per-cell excess of `cleanFun` is at most `256` times the error bracket, for every diluteness
`μa³ ≤ 1`. -/
theorem cleanCB_sq_mul_m_inv_sq_le_errBracket {v : E3 → ℝ} {R μ : ℝ}
    (hav : 0 < a v) (hμ : 0 < μ) (hdil : dil v μ ≤ 1) :
    cleanCB v μ ^ 2 * (2 * Real.pi / ell v μ)⁻¹ ^ 2 ≤ 256 * errBracket v R μ := by
  have ht : 0 < dil v μ := by rw [dil]; positivity
  have ha0 : (0 : ℝ) ≤ a v := hav.le
  have hm0 : (0 : ℝ) ≤ μ := hμ.le
  have hellpos : 0 < ell v μ := by
    rw [ell_eq_mul_rpow hav hμ]
    exact mul_pos hav (Real.rpow_pos_of_pos ht _)
  have hs : 0 ≤ Real.sqrt (dil v μ) := Real.sqrt_nonneg _
  have hell3 : 0 ≤ ell3 v μ := by rw [ell3]; positivity
  have herrExp : 0 < errExp v μ := Real.rpow_pos_of_pos ht _
  -- (1) `0 ≤ cleanCB` and `cleanCB ≤ 32πμa`
  have hRhoBpos : 0 < cleanRhoB v μ := by
    have hKl0 : (0 : ℝ) ≤ (Work.BoseBox.paramsAt μ (a v)).Kl ^ (-(2 : ℝ)) := by
      have := Real.rpow_nonneg (le_of_lt (cleanKl_pos hav hμ)) (-(2 : ℝ))
      simpa using this
    rw [cleanRhoB]
    have := div_nonneg (mul_nonneg hμ.le hKl0) (by positivity : (0:ℝ) ≤ (2:ℝ)^14 * Real.pi)
    linarith
  have hCB0 : 0 ≤ cleanCB v μ := by
    rw [cleanCB]; exact mul_nonneg hRhoBpos.le (by positivity)
  have hCB : cleanCB v μ ≤ 32 * Real.pi * μ * a v := by
    have h1 := cleanRhoB_le_two_mul hav hμ hdil
    have h2 : (0 : ℝ) ≤ 16 * Real.pi * a v := by positivity
    rw [cleanCB]
    nlinarith [h1, h2, hμ]
  have hCB2 : cleanCB v μ ^ 2 ≤ (32 * Real.pi * μ * a v) ^ 2 :=
    pow_le_pow_left₀ hCB0 hCB 2
  -- (2) `(2π/ℓ)^{-1}² = ℓ²/(4π²)`
  have hinv : (2 * Real.pi / ell v μ)⁻¹ ^ 2 = ell v μ ^ 2 / (4 * Real.pi ^ 2) := by
    rw [inv_div, div_pow]
    ring
  -- (3) `(32πμa)²·ℓ²/(4π²) = 256μ²a²ℓ²`
  have hsimple : (32 * Real.pi * μ * a v) ^ 2 * (ell v μ ^ 2 / (4 * Real.pi ^ 2))
      = 256 * μ ^ 2 * a v ^ 2 * ell v μ ^ 2 := by
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  -- (4) `a ≤ ℓ√(μa³)errExp`
  have hkey : a v ≤ ell v μ * Real.sqrt (dil v μ) * errExp v μ := by
    rw [ell_mul_sqrt_mul_errExp hav hμ]
    have hle1 : (1 : ℝ) ≤ (dil v μ) ^ (-(13 / 3230 : ℝ)) := by
      have h : (dil v μ) ^ (13 / 3230 : ℝ) ≤ 1 := by
        have h' := Real.rpow_le_rpow ht.le hdil (show (0 : ℝ) ≤ 13 / 3230 by norm_num)
        rwa [Real.one_rpow] at h'
      have hpos : 0 < (dil v μ) ^ (13 / 3230 : ℝ) := Real.rpow_pos_of_pos ht _
      rw [Real.rpow_neg ht.le]
      exact (one_le_inv₀ hpos).mpr h
    nlinarith [hav, hle1]
  have hstep4 : 256 * μ ^ 2 * a v ^ 2 * ell v μ ^ 2
      ≤ 256 * (μ ^ 2 * a v * ell3 v μ * Real.sqrt (dil v μ) * errExp v μ) := by
    rw [ell3]
    have h4 : a v ≤ ell v μ * Real.sqrt (dil v μ) * errExp v μ := hkey
    have hfac : (0 : ℝ) ≤ 256 * μ ^ 2 * a v * ell v μ ^ 2 := by positivity
    have h5 : 256 * μ ^ 2 * a v * ell v μ ^ 2 * a v
        ≤ 256 * μ ^ 2 * a v * ell v μ ^ 2 * (ell v μ * Real.sqrt (dil v μ) * errExp v μ) :=
      mul_le_mul_of_nonneg_left h4 hfac
    have e1 : 256 * μ ^ 2 * a v * ell v μ ^ 2 * a v = 256 * μ ^ 2 * a v ^ 2 * ell v μ ^ 2 := by
      ring
    have e2 : 256 * μ ^ 2 * a v * ell v μ ^ 2 * (ell v μ * Real.sqrt (dil v μ) * errExp v μ)
        = 256 * (μ ^ 2 * a v * ell v μ ^ 3 * Real.sqrt (dil v μ) * errExp v μ) := by ring
    linarith [h5, e1.symm.le, e1.le, e2.symm.le, e2.le]
  -- (5) `errExp` is one term of the bracket
  have hbr : errExp v μ
      ≤ fsX v μ ^ 2 + (R / a v) ^ 2 * Real.sqrt (dil v μ) + errExp v μ := by
    linarith [sq_nonneg (fsX v μ), mul_nonneg (sq_nonneg (R / a v)) hs]
  have hstep5 : 256 * (μ ^ 2 * a v * ell3 v μ * Real.sqrt (dil v μ) * errExp v μ)
      ≤ 256 * errBracket v R μ := by
    rw [errBracket]
    have hnn : 0 ≤ μ ^ 2 * a v * ell3 v μ * Real.sqrt (dil v μ) :=
      mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) ha0) hell3) hs
    have := mul_le_mul_of_nonneg_left hbr hnn
    linarith [this]
  have h1 : cleanCB v μ ^ 2 * (2 * Real.pi / ell v μ)⁻¹ ^ 2
      ≤ (32 * Real.pi * μ * a v) ^ 2 * (ell v μ ^ 2 / (4 * Real.pi ^ 2)) := by
    rw [hinv]
    exact mul_le_mul_of_nonneg_right hCB2 (by positivity)
  linarith [h1, hsimple.le, hsimple.symm.le, hstep4, hstep5]

/-- **`μ·ℓ³·√(μa³)·(μa³)^{1/1615}` is a diluteness power**: it equals
`(μa³)^{-43/3230} ≥ 1`. -/
lemma mu_mul_ell3_mul_sqrt_mul_errExp {v : E3 → ℝ} {μ : ℝ} (hav : 0 < a v) (hμ : 0 < μ) :
    μ * ell v μ ^ 3 * Real.sqrt (dil v μ) * errExp v μ
      = (dil v μ) ^ (-(43 / 3230 : ℝ)) := by
  have ht : 0 < dil v μ := by rw [dil]; positivity
  have hmeal : μ * a v ^ 3 = dil v μ := rfl
  -- `ℓ³ = a³·(μa³)^{-489/323}`
  have hell3 : ell v μ ^ 3 = a v ^ 3 * (dil v μ) ^ (-(489 / 323 : ℝ)) := by
    have h1 : ell v μ = a v * (dil v μ) ^ (-(163 / 323 : ℝ)) := ell_eq_mul_rpow hav hμ
    rw [h1, mul_pow]
    congr 1
    rw [← Real.rpow_natCast ((dil v μ) ^ (-(163 / 323 : ℝ))) 3, ← Real.rpow_mul ht.le]
    norm_num
  -- `μℓ³ = (μa³)^{1-489/323}`
  have hsplit : (dil v μ) * (dil v μ) ^ (-(489 / 323 : ℝ))
      = (dil v μ) ^ ((1 : ℝ) - 489 / 323) := by
    have h : (dil v μ) ^ ((1 : ℝ) - 489 / 323)
        = (dil v μ) * (dil v μ) ^ (-(489 / 323 : ℝ)) := by
      rw [show (1 : ℝ) - 489 / 323 = (1 : ℝ) + (-(489 / 323 : ℝ)) by ring, Real.rpow_add ht,
        Real.rpow_one]
    exact h.symm
  have hs : Real.sqrt (dil v μ) = (dil v μ) ^ ((1 / 2 : ℝ)) := Real.sqrt_eq_rpow _
  rw [hell3, ← mul_assoc, hmeal, hsplit, hs, errExp, ← Real.rpow_add ht, ← Real.rpow_add ht]
  rw [show (1 : ℝ) - 489 / 323 + 1 / 2 + 1 / 1615 = -(43 / 3230 : ℝ) by norm_num]

/-- **`β = cleanCB` is dominated by the error bracket** with the fixed constant `32π`,
for every diluteness `μa³ ≤ 1`.  (Needed for every `β`-linear term of the per-cell
majorant, in particular for the origin cell.) -/
theorem cleanCB_le_const_mul_errBracket {v : E3 → ℝ} {R μ : ℝ}
    (hav : 0 < a v) (hμ : 0 < μ) (hdil : dil v μ ≤ 1) :
    cleanCB v μ ≤ 32 * Real.pi * errBracket v R μ := by
  have ht : 0 < dil v μ := by rw [dil]; positivity
  have ha0 : (0 : ℝ) ≤ a v := hav.le
  have hpid : (0 : ℝ) < 32 * Real.pi := by positivity
  have hs : 0 ≤ Real.sqrt (dil v μ) := Real.sqrt_nonneg _
  have hellpos : 0 < ell v μ := by
    rw [ell_eq_mul_rpow hav hμ]
    exact mul_pos hav (Real.rpow_pos_of_pos ht _)
  have hell3 : 0 ≤ ell3 v μ := by rw [ell3]; exact pow_nonneg hellpos.le 3
  have hCB : cleanCB v μ ≤ 32 * Real.pi * μ * a v := by
    have h1 := cleanRhoB_le_two_mul hav hμ hdil
    have h2 : (0 : ℝ) ≤ 16 * Real.pi * a v :=
      mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) ha0
    rw [cleanCB]
    nlinarith [h1, h2, hμ]
  have hle1 : (1 : ℝ) ≤ (dil v μ) ^ (-(43 / 3230 : ℝ)) := by
    have h : (dil v μ) ^ (43 / 3230 : ℝ) ≤ 1 := by
      have h' := Real.rpow_le_rpow ht.le hdil (show (0 : ℝ) ≤ 43 / 3230 by norm_num)
      rwa [Real.one_rpow] at h'
    have hpos : 0 < (dil v μ) ^ (43 / 3230 : ℝ) := Real.rpow_pos_of_pos ht _
    rw [Real.rpow_neg ht.le]
    exact (one_le_inv₀ hpos).mpr h
  have hkey : μ * a v ≤ μ ^ 2 * a v * ell3 v μ * Real.sqrt (dil v μ) * errExp v μ := by
    have hid : μ * ell v μ ^ 3 * Real.sqrt (dil v μ) * errExp v μ
        = (dil v μ) ^ (-(43 / 3230 : ℝ)) := mu_mul_ell3_mul_sqrt_mul_errExp hav hμ
    have h2 : (1 : ℝ) ≤ μ * ell v μ ^ 3 * Real.sqrt (dil v μ) * errExp v μ := by
      rw [hid]; exact hle1
    have h4 : μ * a v ≤ μ * a v * (μ * ell v μ ^ 3 * Real.sqrt (dil v μ) * errExp v μ) := by
      have := mul_le_mul_of_nonneg_left h2 (mul_nonneg hμ.le ha0)
      simpa using this
    have h5 : μ * a v * (μ * ell v μ ^ 3 * Real.sqrt (dil v μ) * errExp v μ)
        = μ ^ 2 * a v * ell3 v μ * Real.sqrt (dil v μ) * errExp v μ := by
      rw [ell3]; ring
    linarith [h4, h5.le, h5.symm.le]
  have hbr : errExp v μ
      ≤ fsX v μ ^ 2 + (R / a v) ^ 2 * Real.sqrt (dil v μ) + errExp v μ := by
    linarith [sq_nonneg (fsX v μ), mul_nonneg (sq_nonneg (R / a v)) hs]
  have hstep : μ ^ 2 * a v * ell3 v μ * Real.sqrt (dil v μ) * errExp v μ
      ≤ errBracket v R μ := by
    rw [errBracket]
    have hnn : 0 ≤ μ ^ 2 * a v * ell3 v μ * Real.sqrt (dil v μ) :=
      mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) ha0) hell3) hs
    have := mul_le_mul_of_nonneg_left hbr hnn
    linarith [this]
  have hmid : 32 * Real.pi * μ * a v ≤ 32 * Real.pi * errBracket v R μ := by
    have hmono : 32 * Real.pi * (μ * a v) ≤ 32 * Real.pi * errBracket v R μ :=
      mul_le_mul_of_nonneg_left (le_trans hkey hstep) hpid.le
    linarith [hmono]
  linarith [hCB, hmid]

end Work.BoseBogFS
