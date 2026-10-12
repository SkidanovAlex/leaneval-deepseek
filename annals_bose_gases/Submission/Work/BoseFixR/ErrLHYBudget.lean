import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseFixR.RB5FSDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/ErrLHYBudget.lean` — the LHY margin is absorbed by `πaμ²ℓ³X⁶`

The far-leg arithmetic `RB5FSArith`/`RB5FSArith2` must pay the LHY margin

  `errLHY v μ = 8π·lhyC·μ²aℓ³·√(μa³)`

out of the *pair-condensate* slack `4πa(ρ−μ)²ℓ³`, which in the far region
`FarCond v μ ρ` dominates `4πa·μ²·(μa³)^{6/323}·ℓ³` (that is exactly
`closeThreshold`).  So the arithmetic needs

  `8π·lhyC·μ²aℓ³·√t ≤ 4π·μ²aℓ³·t^{6/323}`,  `t := μa³ = dil v μ`,

i.e. the pure-number statement `8·lhyC·√t ≤ t^{6/323}` on the diluteness window.
This file proves the *stronger* form with `π` on the right (which is the shape
`Work.BoseBoxFix.BoxBoundB`'s absorbing bookkeeping wants):

  `errLHY v μ ≤ π·a v·μ²·(ℓ v μ)³·(fsX v μ)⁶`.

The whole content is the numeric core `eight_lhyC_sqrt_le`.  Since
`6/323 − 1/2 = −311/646 < 0`, dividing by `√t = t^{1/2}` turns
`8·lhyC·√t ≤ t^{6/323}` into `8·lhyC ≤ t^{−311/646}`, and for `0 < t ≤ 10^{−4000}`
the right-hand side is *huge*:

  `t^{−311/646} ≥ (10^{−4000})^{−311/646} = 10^{4000·311/646} ≥ 10³ = 1000 ≥ 8·lhyC`

(`8·lhyC ≤ 800` from `lhyC = 128/(15√π) ≤ 100`, which only needs `π > 3`).
The sharp FS constant `lhyC = 128/(15√π)` is *not* rigid here: what matters is
only the enormous diluteness threshold `10^{−4000}`.

The two effects of the hypothesis `dil v μ ≤ 10^{−4000}` on the analytic side are
`dil v μ > 0` (from `hμ`, `hav`) and `dil v μ ≤ 1`; both are used, the latter only
through `0 < t` in the two `Real.rpow_add`/`Real.rpow_mul` steps.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixR

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 0. The numeric window `0 < t ≤ 10^{−4000}` -/

/-- `lhyC = 128/(15√π) ≤ 100`: from `π > 3` we have `√π ≥ 1`, hence
`128/(15√π) ≤ 128/15 ≤ 100`.  (Only *some* absolute constant is needed.) -/
lemma lhyC_le_hundred : lhyC ≤ 100 := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hs : (1 : ℝ) ≤ Real.sqrt Real.pi := Real.one_le_sqrt.mpr (by linarith)
  rw [lhyC, div_le_iff₀ (by positivity : (0 : ℝ) < 15 * Real.sqrt Real.pi)]
  nlinarith [hs]

/-- **The numeric core**: `8·lhyC·√t ≤ t^{6/323}` for `0 < t ≤ 10^{−4000}`.

Since `6/323 − 1/2 = −311/646 ≤ 0`, the map `s ↦ s^{6/323−1/2}` is *antitone*, so
on the window it is at least its value at `t = 10^{−4000}`, which is
`10^{4000·311/646} ≥ 10³ = 1000 ≥ 8·lhyC`. -/
lemma eight_lhyC_sqrt_le {t : ℝ} (h0 : 0 < t) (h1 : t ≤ (10 : ℝ) ^ (-(4000 : ℤ))) :
    8 * lhyC * Real.sqrt t ≤ t ^ (6 / 323 : ℝ) := by
  have hzle : (6 / 323 : ℝ) - 1 / 2 ≤ 0 := by norm_num
  -- It suffices to dominate `8·lhyC` by the (huge) negative power `t^{6/323 - 1/2}`.
  have hkey : 8 * lhyC ≤ t ^ ((6 / 323 : ℝ) - 1 / 2) := by
    have hbig : 8 * lhyC
        ≤ ((10 : ℝ) ^ (-(4000 : ℤ))) ^ ((6 / 323 : ℝ) - 1 / 2) := by
      -- the value of the negative power at the *largest* allowed `t = 10^{−4000}`
      have hrew : ((10 : ℝ) ^ (-(4000 : ℤ))) ^ ((6 / 323 : ℝ) - 1 / 2)
          = (10 : ℝ) ^ (4000 * (311 / 646) : ℝ) := by
        rw [← Real.rpow_intCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10)]
        congr 1
        norm_num
      rw [hrew]
      have hexp : ((3 : ℕ) : ℝ) ≤ 4000 * (311 / 646) := by norm_num
      have h1000 : (1000 : ℝ) ≤ (10 : ℝ) ^ (4000 * (311 / 646) : ℝ) := by
        have h := Real.rpow_le_rpow_of_exponent_le (x := (10 : ℝ)) (y := ((3 : ℕ) : ℝ))
          (z := 4000 * (311 / 646)) (by norm_num : (1 : ℝ) ≤ 10) hexp
        have h3 : (10 : ℝ) ^ ((3 : ℕ) : ℝ) = 1000 := by
          rw [Real.rpow_natCast]; norm_num
        rwa [h3] at h
      have hlhy : 8 * lhyC ≤ 1000 := by
        have h5 : lhyC ≤ 100 := lhyC_le_hundred
        linarith
      linarith
    -- antitonicity on the window (`x ↦ x^z` decreasing for `z ≤ 0`)
    have hle : ((10 : ℝ) ^ (-(4000 : ℤ))) ^ ((6 / 323 : ℝ) - 1 / 2)
        ≤ t ^ ((6 / 323 : ℝ) - 1 / 2) :=
      Real.rpow_le_rpow_of_nonpos h0 h1 hzle
    linarith
  -- multiply by `√t = t^{1/2}` and add the exponents
  calc 8 * lhyC * Real.sqrt t
      = 8 * lhyC * t ^ (1 / 2 : ℝ) := by rw [Real.sqrt_eq_rpow]
    _ ≤ t ^ ((6 / 323 : ℝ) - 1 / 2) * t ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right hkey (Real.rpow_nonneg h0.le _)
    _ = t ^ (6 / 323 : ℝ) := by
        rw [← Real.rpow_add h0 ((6 / 323 : ℝ) - 1 / 2) (1 / 2)]
        norm_num

/-- `(fsX v μ)^6 = (dil v μ)^{6/323}`: `fsX v μ = (μa³)^{1/323}`. -/
lemma fsX_pow_six (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (hd : 0 ≤ dil v μ) :
    (fsX v μ) ^ 6 = (dil v μ) ^ (6 / 323 : ℝ) := by
  rw [fsX, fsXp_pow hd 1 6, fsXp]
  congr 1
  norm_num

/-! ## 1. The budget -/

/-- **The LHY margin is paid by `π·a·μ²·ℓ³·X⁶`.**  `errLHY v μ` and the target
differ by the common positive factor `π·a v·μ²·(ℓ v μ)³`, so the claim is exactly
the numeric core `eight_lhyC_sqrt_le` for `t = dil v μ`. -/
theorem ErrLHYBudget {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ}
    (hav : 0 < BoseGases.a v) (hμ : 0 < μ)
    (ht : Work.BoseFixR.dil v μ ≤ (10 : ℝ) ^ (-(4000 : ℤ))) :
    Work.BoseFixR.errLHY v μ
      ≤ Real.pi * BoseGases.a v * μ ^ 2 * Work.BoseFixR.ell v μ ^ 3 * (Work.BoseFixR.fsX v μ) ^ 6 := by
  have hdilpos : 0 < dil v μ := by unfold dil; positivity
  have hcore : 8 * lhyC * Real.sqrt (dil v μ) ≤ (dil v μ) ^ (6 / 323 : ℝ) :=
    eight_lhyC_sqrt_le hdilpos ht
  have hfsX : (fsX v μ) ^ 6 = (dil v μ) ^ (6 / 323 : ℝ) := fsX_pow_six v μ hdilpos.le
  have hellnn : 0 ≤ ell v μ := by
    have h := sideAt_pos (μ := μ) (a := BoseGases.a v) hμ hav
    simpa [ell] using h.le
  have hfac : 0 ≤ Real.pi * BoseGases.a v * μ ^ 2 * ell v μ ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg Real.pi_pos.le hav.le) (sq_nonneg μ))
      (pow_nonneg hellnn 3)
  rw [errLHY, ell3, hfsX]
  calc 8 * Real.pi * lhyC * μ ^ 2 * BoseGases.a v * ell v μ ^ 3 * Real.sqrt (dil v μ)
      = (8 * lhyC * Real.sqrt (dil v μ)) * (Real.pi * BoseGases.a v * μ ^ 2 * ell v μ ^ 3) := by
        ring
    _ ≤ (dil v μ) ^ (6 / 323 : ℝ) * (Real.pi * BoseGases.a v * μ ^ 2 * ell v μ ^ 3) :=
        mul_le_mul_of_nonneg_right hcore hfac
    _ = Real.pi * BoseGases.a v * μ ^ 2 * ell v μ ^ 3 * (dil v μ) ^ (6 / 323 : ℝ) := by
        ring

end Work.BoseFixR
