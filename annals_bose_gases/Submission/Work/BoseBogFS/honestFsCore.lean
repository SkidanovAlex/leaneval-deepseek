import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseBogFS.BogFSKernel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.honestFsCore` — the parameter bounds of the honest `FsI1Regime`

This module carries the *shared* arithmetic of `Work.BoseBogFS.honestFsI1Regime`:
at the honest parameter block `paramsAt μ (a v) = fsParams (μ(a v)³)` every parameter
is a monomial in the diluteness `D = μ(a v)³`,

  `s = D^{1/323}`, `d = D^{6/323}`, `ε_T = D^{23/1292}`, `K_ℓ = D^{-3/646}`,

so the box side is `ℓ = K_ℓ(μa)^{-1/2}` and FS's error `ε` of `eq:LebesgueError-Total`
collapses (by `lhyEps_explicit`) to `lhyEpsX`:

  `ε = (μa)^{1/4}√R + D^{23/1292} + D^{1/646}(1 + (162/323)log D^{-1})
        + D^{1/1292}(1 + (156/323)log D^{-1})`.

The momentum cutoff is `T = 10⁶(1 + log D^{-1})/ε` (`bogT`).  Below we collect, for
every `μ` with diluteness `D ≤ coreBound v R` and every `ρ` in FS's close region, the
elementary consequences: the closed form of `ε`, its lower and upper bounds, the
bounds `10⁶/4 ≤ T` and `T ≤ 2·10⁶(323/156)D^{-1/1292}`, the nearness `9/10 μ ≤ ρ ≤ 11/10 μ`,
and `(μa)^{1/4}√R ≤ 1`.  The threshold `coreBound v R` is a min of `a²/R²` (for that last
row), `e^{-1}` (so that `log D^{-1} ≥ 1`) and the huge numeric `2^{-12920}` (so that
`D^{1/1292} ≤ 1/1024` and `D^{3/323} ≤ 2^{-120}`).

Downstream, each dominance row of `FsI1Regime` is proved by taking
`ε₀ = min (row threshold) (coreBound v R)` and consuming `core_bounds`.
-/

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Filter Metric

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.BoseBogFS

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The closed form of FS's error at the honest parameters -/

/-- FS's error `ε(μ,ρ_z)` of `eq:LebesgueError-Total` at the honest parameter block, in
the closed form produced by `lhyEps_explicit`. -/
def lhyEpsX (v : E3 → ℝ) (R μ : ℝ) : ℝ :=
  (μ * _root_.BoseGases.a v) ^ ((1 : ℝ) / 4) * Real.sqrt R
    + (Work.BoseFixR.dil v μ) ^ ((23 : ℝ) / 1292)
    + (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 646)
        * (1 + ((162 : ℝ) / 323) * Real.log (1 / Work.BoseFixR.dil v μ))
    + (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292)
        * (1 + ((156 : ℝ) / 323) * Real.log (1 / Work.BoseFixR.dil v μ))

/-- The logarithm `log D^{-1}` of the inverse diluteness `D = μ(a v)³`. -/
def bogL (v : E3 → ℝ) (μ : ℝ) : ℝ := Real.log (1 / Work.BoseFixR.dil v μ)

/-- The diluteness threshold of the core parameter bounds: `a²/R²` (which makes
`(μa)^{1/4}√R ≤ 1`), `e^{-1}` (which makes `log D^{-1} ≥ 1`) and the numeric
`2^{-12920}` (which makes `D^{1/1292} ≤ 1/1024` and `D^{3/323} ≤ 2^{-120}`). -/
def coreBound (v : E3 → ℝ) (R : ℝ) : ℝ :=
  min ((_root_.BoseGases.a v) ^ 2 / R ^ 2)
    (min (Real.exp (-1)) ((2 : ℝ) ^ (-(12920 : ℝ))))

lemma coreBound_pos {v : E3 → ℝ} {R : ℝ} (hR : 0 < R) (hav : 0 < _root_.BoseGases.a v) :
    0 < coreBound v R := by
  have h : 0 < (_root_.BoseGases.a v) ^ 2 / R ^ 2 := by positivity
  have h2 : 0 < (2 : ℝ) ^ (-(12920 : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  exact lt_min h (lt_min (Real.exp_pos _) h2)

/-! ## 2. The parameter monomials -/

lemma paramsAt_s (v : E3 → ℝ) (μ : ℝ) :
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
      = (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 323) := rfl

lemma paramsAt_d (v : E3 → ℝ) (μ : ℝ) :
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
      = (Work.BoseFixR.dil v μ) ^ ((6 : ℝ) / 323) := rfl

lemma paramsAt_eT (v : E3 → ℝ) (μ : ℝ) :
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
      = (Work.BoseFixR.dil v μ) ^ ((23 : ℝ) / 1292) := by
  show Work.BoseBox.fsXp (μ * _root_.BoseGases.a v ^ 3) ((23 : ℝ) / 4)
      = (μ * _root_.BoseGases.a v ^ 3) ^ ((23 : ℝ) / 1292)
  unfold Work.BoseBox.fsXp
  rw [show ((23 : ℝ) / 4) / 323 = 23 / 1292 by norm_num]

lemma paramsAt_Kl (v : E3 → ℝ) (μ : ℝ) :
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
      = (Work.BoseFixR.dil v μ) ^ (-((3 : ℝ) / 646)) := by
  show Work.BoseBox.fsXp (μ * _root_.BoseGases.a v ^ 3) (-((3 : ℝ) / 2))
      = (μ * _root_.BoseGases.a v ^ 3) ^ (-((3 : ℝ) / 646))
  unfold Work.BoseBox.fsXp
  rw [show (-((3 : ℝ) / 2)) / 323 = -((3 : ℝ) / 646) by norm_num]

/-- The box side is `K_ℓ (μa)^{-1/2}` (by definition of `boxSide`). -/
lemma ell_eq_boxSide (v : E3 → ℝ) (μ : ℝ) :
    Work.BoseFixR.ell v μ = (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
      * (μ * _root_.BoseGases.a v) ^ (-(1 / 2 : ℝ)) := rfl

/-- `K_ℓ^{-2} = D^{3/323}`. -/
lemma paramsAt_Kl_inv_sq (v : E3 → ℝ) (μ : ℝ) (hD : 0 < Work.BoseFixR.dil v μ) :
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl ^ (-(2 : ℝ))
      = (Work.BoseFixR.dil v μ) ^ ((3 : ℝ) / 323) := by
  rw [paramsAt_Kl, ← Real.rpow_mul hD.le]
  norm_num

/-- `(s K_ℓ)^{-1} = D^{1/646}`. -/
lemma sKl_inv (v : E3 → ℝ) (μ : ℝ) (hD : 0 < Work.BoseFixR.dil v μ) :
    ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl)⁻¹
      = (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 646) := by
  rw [paramsAt_s, paramsAt_Kl, ← Real.rpow_add hD]
  rw [show (1 : ℝ) / 323 + (-((3 : ℝ) / 646)) = -((1 : ℝ) / 646) by norm_num]
  rw [← Real.rpow_neg hD.le]
  rw [show -(-((1 : ℝ) / 646)) = (1 : ℝ) / 646 by norm_num]

/-- `d s K_ℓ = D^{11/646}`. -/
lemma dsKl_eq (v : E3 → ℝ) (μ : ℝ) (hD : 0 < Work.BoseFixR.dil v μ) :
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
      = (Work.BoseFixR.dil v μ) ^ ((11 : ℝ) / 646) := by
  rw [paramsAt_d, paramsAt_s, paramsAt_Kl, ← Real.rpow_add hD, ← Real.rpow_add hD]
  rw [show (6 : ℝ) / 323 + 1 / 323 + (-((3 : ℝ) / 646)) = 11 / 646 by norm_num]

/-- `ε_T (d s K_ℓ)^{-1} = D^{1/1292}`. -/
lemma eT_dsKl_inv (v : E3 → ℝ) (μ : ℝ) (hD : 0 < Work.BoseFixR.dil v μ) :
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
        * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl)⁻¹
      = (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292) := by
  rw [dsKl_eq v μ hD, paramsAt_eT, ← Real.rpow_neg hD.le, ← Real.rpow_add hD]
  rw [show (23 : ℝ) / 1292 + (-((11 : ℝ) / 646)) = 1 / 1292 by norm_num]

/-- The diluteness itself is positive. -/
lemma dil_pos (v : E3 → ℝ) {μ : ℝ} (hμ : 0 < μ) (hav : 0 < _root_.BoseGases.a v) :
    0 < Work.BoseFixR.dil v μ := by
  rw [Work.BoseFixR.dil]
  exact mul_pos hμ (pow_pos hav 3)

/-- `√(μa) = √D / a`. -/
lemma sqrt_mua (v : E3 → ℝ) (μ : ℝ) (hμ : 0 < μ) (hav : 0 < _root_.BoseGases.a v) :
    Real.sqrt (μ * _root_.BoseGases.a v)
      = Real.sqrt (Work.BoseFixR.dil v μ) / _root_.BoseGases.a v := by
  have ha := hav
  have hD0 : 0 < Work.BoseFixR.dil v μ := dil_pos v hμ hav
  have h : μ * _root_.BoseGases.a v = Work.BoseFixR.dil v μ / _root_.BoseGases.a v ^ 2 := by
    rw [Work.BoseFixR.dil]; field_simp
  have hsd : Real.sqrt (Work.BoseFixR.dil v μ / _root_.BoseGases.a v ^ 2)
      = Real.sqrt (Work.BoseFixR.dil v μ) / Real.sqrt (_root_.BoseGases.a v ^ 2) :=
    Real.sqrt_div (x := Work.BoseFixR.dil v μ) hD0.le (_root_.BoseGases.a v ^ 2)
  have hss : Real.sqrt (_root_.BoseGases.a v ^ 2) = _root_.BoseGases.a v :=
    Real.sqrt_sq (x := _root_.BoseGases.a v) ha.le
  rw [h, hsd, hss]

/-- `D^{e} ≤ 1` for `0 < D ≤ 1` and `e ≥ 0`. -/
lemma rpow_le_one' {D e : ℝ} (h0 : 0 < D) (h1 : D ≤ 1) (he : 0 ≤ e) : D ^ e ≤ 1 :=
  Real.rpow_le_one h0.le h1 he

lemma rpow_two_le_one {D e : ℝ} (h0 : 0 < D) (h1 : D ≤ 1) (he : 0 ≤ e) : D ^ e ≤ 1 :=
  rpow_le_one' h0 h1 he

/-- **The shared parameter bounds of the honest `FsI1Regime`.**  Every field is a
statement about the honest data `(v, R, μ, ρ)` and the parameter block
`paramsAt μ (a v)`; all are consequences of the diluteness bound
`dil v μ ≤ coreBound v R = min (a²/R²) (min e^{-1} 2^{-12920})` and of FS's close
condition. -/
structure Core (v : E3 → ℝ) (R μ ρ : ℝ) : Prop where
  hμ : 0 < μ
  hD0 : 0 < Work.BoseFixR.dil v μ
  hD1 : Work.BoseFixR.dil v μ ≤ 1
  /-- `D^{1/1292} ≤ 1/1024`: the numeric core bound. -/
  hDs : (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292) ≤ 1 / 1024
  hL1 : 1 ≤ bogL v μ
  hL0 : 0 ≤ bogL v μ
  hρ0 : 0 < ρ
  hρlo : 9 / 10 * μ ≤ ρ
  hρhi : ρ ≤ 11 / 10 * μ
  hρsqrt : Real.sqrt (μ / ρ) ≤ 2
  /-- the closed form of FS's error `ε(μ,ρ_z)`. -/
  hEeq : Work.BoseB6.lhyEps (_root_.BoseGases.a v) R
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ = lhyEpsX v R μ
  hE0 : 0 ≤ lhyEpsX v R μ
  hEμa : (μ * _root_.BoseGases.a v) ^ ((1 : ℝ) / 4) * Real.sqrt R ≤ lhyEpsX v R μ
  hE1 : (Work.BoseFixR.dil v μ) ^ ((23 : ℝ) / 1292) ≤ lhyEpsX v R μ
  hE2 : (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 646) * (1 + ((162 : ℝ) / 323) * bogL v μ)
      ≤ lhyEpsX v R μ
  hE3 : (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292) * (1 + ((156 : ℝ) / 323) * bogL v μ)
      ≤ lhyEpsX v R μ
  hEup : lhyEpsX v R μ ≤ 4 + bogL v μ
  hsmall : (μ * _root_.BoseGases.a v) ^ ((1 : ℝ) / 4) * Real.sqrt R ≤ 1
  /-- `T = 10⁶(1 + log D^{-1})/ε`. -/
  hTdef : bogT v R μ = 10 ^ 6 * (1 + bogL v μ) / lhyEpsX v R μ
  hTpos : 0 < bogT v R μ
  hTlow : 10 ^ 6 / 4 ≤ bogT v R μ
  hTup : bogT v R μ ≤ 2 * 10 ^ 6 * (323 / 156)
      * (Work.BoseFixR.dil v μ) ^ (-(1 / 1292 : ℝ))
  hη0 : 0 ≤ bogEta v R ρ
  /-- `√(ρa) ≤ √(11/10)·√D/a`. -/
  hsqρa : Real.sqrt (ρ * _root_.BoseGases.a v)
      ≤ Real.sqrt (11 / 10) * (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 2)
        / _root_.BoseGases.a v
  /-- `√(μa) = √D/a`. -/
  hsqμa : Real.sqrt (μ * _root_.BoseGases.a v)
      = (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 2) / _root_.BoseGases.a v
  hℓ : Work.BoseFixR.ell v μ = (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
      * (μ * _root_.BoseGases.a v) ^ (-(1 / 2 : ℝ))

theorem core_bounds {v : E3 → ℝ} {R : ℝ} (hR : 0 < R) (hav : 0 < _root_.BoseGases.a v)
    {δ : ℝ} (hδc : δ ≤ coreBound v R) :
    ∀ μ ρ, 0 < μ → Work.BoseFixR.dil v μ ≤ δ → Work.BoseBoxFock.CloseCondFS v μ ρ →
      Core v R μ ρ := by
  intro μ ρ hμ hDδ hclose
  have ha : 0 < _root_.BoseGases.a v := hav
  have hD0 : 0 < Work.BoseFixR.dil v μ := dil_pos v hμ hav
  have hDB : Work.BoseFixR.dil v μ ≤ coreBound v R := le_trans hDδ hδc
  have hDaR : Work.BoseFixR.dil v μ ≤ (_root_.BoseGases.a v) ^ 2 / R ^ 2 :=
    le_trans hDB (min_le_left _ _)
  have hDexp : Work.BoseFixR.dil v μ ≤ Real.exp (-1) :=
    le_trans hDB (le_trans (min_le_right _ _) (min_le_left _ _))
  have hD2 : Work.BoseFixR.dil v μ ≤ (2 : ℝ) ^ (-(12920 : ℝ)) :=
    le_trans hDB (le_trans (min_le_right _ _) (min_le_right _ _))
  have hD1 : Work.BoseFixR.dil v μ ≤ 1 := by
    have hexp : Real.exp (-1) ≤ 1 := by
      have h := Real.exp_le_exp.mpr (show (-1 : ℝ) ≤ 0 by norm_num)
      rwa [Real.exp_zero] at h
    linarith
  have hDs : (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292) ≤ 1 / 1024 := by
    have h1 : (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292)
        ≤ ((2 : ℝ) ^ (-(12920 : ℝ))) ^ ((1 : ℝ) / 1292) :=
      Real.rpow_le_rpow hD0.le hD2 (by norm_num)
    have h2 : ((2 : ℝ) ^ (-(12920 : ℝ))) ^ ((1 : ℝ) / 1292) = (1 : ℝ) / 1024 := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      rw [show (-(12920 : ℝ)) * (1 / 1292) = -(((10 : ℕ)) : ℝ) by norm_num]
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
      norm_num
    linarith [h1, h2.ge, h2.le]
  -- the logarithm of the inverse diluteness is at least `1`
  have hL1 : 1 ≤ bogL v μ := by
    rw [bogL]
    have hmul : Work.BoseFixR.dil v μ * Real.exp 1 ≤ 1 := by
      have h := mul_le_mul_of_nonneg_right hDexp (Real.exp_pos 1).le
      rw [Real.exp_neg 1] at h
      rwa [inv_mul_cancel₀ (ne_of_gt (Real.exp_pos 1))] at h
    have hinv : Real.exp 1 ≤ 1 / Work.BoseFixR.dil v μ := by
      rw [le_div_iff₀ hD0]
      linarith only [hmul]
    exact (Real.le_log_iff_exp_le (by positivity)).mpr hinv
  have hL0 : 0 ≤ bogL v μ := le_trans (by norm_num) hL1
  have hLg1 : 1 ≤ Real.log (1 / Work.BoseFixR.dil v μ) := hL1
  have hLg0 : 0 ≤ Real.log (1 / Work.BoseFixR.dil v μ) := hL0
  -- FS's close condition confines `ρ` to `[9μ/10, 11μ/10]`
  have hct_raw : |ρ - μ| ≤ Work.BoseBoxFock.closeThresholdFS v μ := hclose
  have hKl2 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl ^ (-(2 : ℝ))
      ≤ (2 : ℝ) ^ (-(120 : ℝ)) := by
    rw [paramsAt_Kl_inv_sq v μ hD0]
    have h1 : (Work.BoseFixR.dil v μ) ^ ((3 : ℝ) / 323)
        ≤ ((2 : ℝ) ^ (-(12920 : ℝ))) ^ ((3 : ℝ) / 323) :=
      Real.rpow_le_rpow hD0.le hD2 (by norm_num)
    have h2 : ((2 : ℝ) ^ (-(12920 : ℝ))) ^ ((3 : ℝ) / 323) = (2 : ℝ) ^ (-(120 : ℝ)) := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      rw [show (-(12920 : ℝ)) * (3 / 323) = -(((120 : ℕ)) : ℝ) by norm_num]
      norm_num
    linarith [h1, h2.ge, h2.le]
  have hnum1 : (10 : ℝ) * (2 : ℝ) ^ (-(120 : ℝ)) ≤ 1 := by
    rw [show (-(120 : ℝ)) = -(((120 : ℕ)) : ℝ) by norm_num]
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
    rw [mul_inv_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ 120)]
    norm_num
  have hnum2 : (1 : ℝ) ≤ (2 : ℝ) ^ 14 * Real.pi := by
    have h := Real.pi_gt_three
    nlinarith [Real.pi_pos]
  have h10 : (2 : ℝ) ^ (-(120 : ℝ)) ≤ ((2 : ℝ) ^ 14 * Real.pi) / 10 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 10)]
    nlinarith [hnum1, hnum2]
  have hct : Work.BoseBoxFock.closeThresholdFS v μ ≤ μ / 10 := by
    rw [Work.BoseBoxFock.closeThresholdFS,
      div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ 14 * Real.pi)]
    calc μ * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl ^ (-(2 : ℝ))
        ≤ μ * (2 : ℝ) ^ (-(120 : ℝ)) := mul_le_mul_of_nonneg_left hKl2 hμ.le
      _ ≤ μ * (((2 : ℝ) ^ 14 * Real.pi) / 10) := mul_le_mul_of_nonneg_left h10 hμ.le
      _ = μ / 10 * ((2 : ℝ) ^ 14 * Real.pi) := by ring
  have hρlo : 9 / 10 * μ ≤ ρ := by
    have h := le_trans hct_raw hct
    have h2 := neg_abs_le (ρ - μ)
    linarith only [h, h2]
  have hρhi : ρ ≤ 11 / 10 * μ := by
    have h := le_trans hct_raw hct
    have h2 := le_abs_self (ρ - μ)
    linarith only [h, h2]
  have hρ0 : 0 < ρ := by linarith only [hρlo, hμ]
  have hρsqrt : Real.sqrt (μ / ρ) ≤ 2 := by
    have hμρ : μ / ρ ≤ 10 / 9 := by
      rw [div_le_iff₀ hρ0]
      linarith only [hρlo]
    have h9 : Real.sqrt (10 / 9) ≤ 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 10 / 9 by norm_num),
        Real.sqrt_nonneg (10 / 9)]
    exact le_trans (Real.sqrt_le_sqrt hμρ) h9
  -- the error `ε`
  have hEeq : Work.BoseB6.lhyEps (_root_.BoseGases.a v) R
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ = lhyEpsX v R μ :=
    lhyEps_explicit v R μ hμ hav
  have hEμa : (μ * _root_.BoseGases.a v) ^ ((1 : ℝ) / 4) * Real.sqrt R ≤ lhyEpsX v R μ := by
    simp only [lhyEpsX]
    have h1 : 0 ≤ (Work.BoseFixR.dil v μ) ^ ((23 : ℝ) / 1292) := Real.rpow_nonneg hD0.le _
    have h2 : 0 ≤ (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 646)
        * (1 + ((162 : ℝ) / 323) * Real.log (1 / Work.BoseFixR.dil v μ)) :=
      mul_nonneg (Real.rpow_nonneg hD0.le _) (by linarith only [hLg1])
    have h3 : 0 ≤ (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292)
        * (1 + ((156 : ℝ) / 323) * Real.log (1 / Work.BoseFixR.dil v μ)) :=
      mul_nonneg (Real.rpow_nonneg hD0.le _) (by linarith only [hLg1])
    linarith only [h1, h2, h3]
  have hE1 : (Work.BoseFixR.dil v μ) ^ ((23 : ℝ) / 1292) ≤ lhyEpsX v R μ := by
    simp only [lhyEpsX]
    have h2 : 0 ≤ (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 646)
        * (1 + ((162 : ℝ) / 323) * Real.log (1 / Work.BoseFixR.dil v μ)) :=
      mul_nonneg (Real.rpow_nonneg hD0.le _) (by linarith only [hLg1])
    have h3 : 0 ≤ (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292)
        * (1 + ((156 : ℝ) / 323) * Real.log (1 / Work.BoseFixR.dil v μ)) :=
      mul_nonneg (Real.rpow_nonneg hD0.le _) (by linarith only [hLg1])
    have h0 : 0 ≤ (μ * _root_.BoseGases.a v) ^ ((1 : ℝ) / 4) * Real.sqrt R := by positivity
    linarith only [h0, h2, h3]
  have hE2 : (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 646)
      * (1 + ((162 : ℝ) / 323) * Real.log (1 / Work.BoseFixR.dil v μ)) ≤ lhyEpsX v R μ := by
    simp only [lhyEpsX]
    have h3 : 0 ≤ (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292)
        * (1 + ((156 : ℝ) / 323) * Real.log (1 / Work.BoseFixR.dil v μ)) :=
      mul_nonneg (Real.rpow_nonneg hD0.le _) (by linarith only [hLg1])
    have h0 : 0 ≤ (μ * _root_.BoseGases.a v) ^ ((1 : ℝ) / 4) * Real.sqrt R := by positivity
    have h1 : 0 ≤ (Work.BoseFixR.dil v μ) ^ ((23 : ℝ) / 1292) := Real.rpow_nonneg hD0.le _
    linarith only [h0, h1, h3]
  have hE3 : (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292)
      * (1 + ((156 : ℝ) / 323) * Real.log (1 / Work.BoseFixR.dil v μ)) ≤ lhyEpsX v R μ := by
    simp only [lhyEpsX]
    have h0 : 0 ≤ (μ * _root_.BoseGases.a v) ^ ((1 : ℝ) / 4) * Real.sqrt R := by positivity
    have h1 : 0 ≤ (Work.BoseFixR.dil v μ) ^ ((23 : ℝ) / 1292) := Real.rpow_nonneg hD0.le _
    have h2 : 0 ≤ (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 646)
        * (1 + ((162 : ℝ) / 323) * Real.log (1 / Work.BoseFixR.dil v μ)) :=
      mul_nonneg (Real.rpow_nonneg hD0.le _) (by linarith only [hLg1])
    linarith only [h0, h1, h2]
  have hE0 : 0 ≤ lhyEpsX v R μ := le_trans (by positivity) hEμa
  have hEpos : 0 < lhyEpsX v R μ :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hD0 _) hE1
  -- `(μa)^{1/4}√R ≤ 1`
  have hsmall : (μ * _root_.BoseGases.a v) ^ ((1 : ℝ) / 4) * Real.sqrt R ≤ 1 := by
    have hsqD : Real.sqrt (Work.BoseFixR.dil v μ) * R / _root_.BoseGases.a v ≤ 1 := by
      have h2 : Work.BoseFixR.dil v μ ≤ (_root_.BoseGases.a v / R) ^ 2 := by
        rw [div_pow]
        exact hDaR
      have h1 : Real.sqrt (Work.BoseFixR.dil v μ) ≤ _root_.BoseGases.a v / R :=
        calc Real.sqrt (Work.BoseFixR.dil v μ)
            ≤ Real.sqrt ((_root_.BoseGases.a v / R) ^ 2) := Real.sqrt_le_sqrt h2
          _ = _root_.BoseGases.a v / R := Real.sqrt_sq (by positivity)
      rw [div_le_iff₀ ha]
      calc Real.sqrt (Work.BoseFixR.dil v μ) * R
          ≤ (_root_.BoseGases.a v / R) * R := mul_le_mul_of_nonneg_right h1 hR.le
        _ = 1 * _root_.BoseGases.a v := by field_simp
    have hsq : ((μ * _root_.BoseGases.a v) ^ ((1 : ℝ) / 4) * Real.sqrt R) ^ 2
        = Real.sqrt (Work.BoseFixR.dil v μ) * R / _root_.BoseGases.a v := by
      rw [mul_pow, ← Real.rpow_natCast ((μ * _root_.BoseGases.a v) ^ ((1 : ℝ) / 4)) 2,
        ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ μ * _root_.BoseGases.a v)]
      rw [show ((1 : ℝ) / 4) * (((2 : ℕ)) : ℝ) = 1 / 2 by norm_num]
      rw [Real.sq_sqrt hR.le, ← Real.sqrt_eq_rpow, sqrt_mua v μ hμ hav]
      ring
    have h0 : 0 ≤ (μ * _root_.BoseGases.a v) ^ ((1 : ℝ) / 4) * Real.sqrt R := by positivity
    nlinarith [hsq, h0]
  -- `ε ≤ 4 + log D^{-1}`
  have hEup : lhyEpsX v R μ ≤ 4 + Real.log (1 / Work.BoseFixR.dil v μ) := by
    simp only [lhyEpsX]
    have h1 : (Work.BoseFixR.dil v μ) ^ ((23 : ℝ) / 1292) ≤ 1 :=
      rpow_le_one' hD0 hD1 (by norm_num)
    have h2 : (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 646)
        * (1 + ((162 : ℝ) / 323) * Real.log (1 / Work.BoseFixR.dil v μ))
        ≤ 1 + ((162 : ℝ) / 323) * Real.log (1 / Work.BoseFixR.dil v μ) := by
      have := mul_le_mul_of_nonneg_right
        (rpow_le_one' hD0 hD1 (by norm_num : (0:ℝ) ≤ 1/646))
        (by linarith only [hLg0] : 0 ≤ 1 + (162/323)*Real.log (1 / Work.BoseFixR.dil v μ))
      simpa using this
    have h3 : (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292)
        * (1 + ((156 : ℝ) / 323) * Real.log (1 / Work.BoseFixR.dil v μ))
        ≤ 1 + ((156 : ℝ) / 323) * Real.log (1 / Work.BoseFixR.dil v μ) := by
      have := mul_le_mul_of_nonneg_right
        (rpow_le_one' hD0 hD1 (by norm_num : (0:ℝ) ≤ 1/1292))
        (by linarith only [hLg0] : 0 ≤ 1 + (156/323)*Real.log (1 / Work.BoseFixR.dil v μ))
      simpa using this
    have hLnl : ((162 : ℝ) / 323 + 156 / 323) * Real.log (1 / Work.BoseFixR.dil v μ)
        ≤ Real.log (1 / Work.BoseFixR.dil v μ) := by
      nlinarith only [hLg0]
    linarith only [hsmall, h1, h2, h3, hLnl]
  -- the momentum cutoff `T`
  have hTdef : bogT v R μ = 10 ^ 6 * (1 + Real.log (1 / Work.BoseFixR.dil v μ))
      / lhyEpsX v R μ := by
    simp only [bogT]
    rw [hEeq]
  have hTpos : 0 < bogT v R μ := by
    rw [hTdef]
    exact div_pos (mul_pos (by norm_num) (by linarith only [hLg1])) hEpos
  have hTlow : 10 ^ 6 / 4 ≤ bogT v R μ := by
    rw [hTdef, le_div_iff₀ hEpos]
    have h1 : (10:ℝ) ^ 6 / 4 * lhyEpsX v R μ
        ≤ (10:ℝ) ^ 6 / 4 * (4 + Real.log (1 / Work.BoseFixR.dil v μ)) :=
      mul_le_mul_of_nonneg_left hEup (by norm_num)
    have h2 : (10:ℝ) ^ 6 / 4 * (4 + Real.log (1 / Work.BoseFixR.dil v μ))
        ≤ (10:ℝ) ^ 6 * (1 + Real.log (1 / Work.BoseFixR.dil v μ)) := by
      linarith only [hLg0]
    linarith only [h1, h2]
  have hTup : bogT v R μ ≤ 2 * 10 ^ 6 * (323 / 156)
      * (Work.BoseFixR.dil v μ) ^ (-(1 / 1292 : ℝ)) := by
    have hE3b : (156 : ℝ) / 323
        * ((Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292)
          * Real.log (1 / Work.BoseFixR.dil v μ)) ≤ lhyEpsX v R μ := by
      have h : (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292)
            * (((156 : ℝ) / 323) * Real.log (1 / Work.BoseFixR.dil v μ))
          ≤ (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292)
            * (1 + ((156 : ℝ) / 323) * Real.log (1 / Work.BoseFixR.dil v μ)) :=
        mul_le_mul_of_nonneg_left (by linarith only []) (Real.rpow_nonneg hD0.le _)
      calc (156 : ℝ) / 323
            * ((Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292)
              * Real.log (1 / Work.BoseFixR.dil v μ))
          = (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292)
            * (((156 : ℝ) / 323) * Real.log (1 / Work.BoseFixR.dil v μ)) := by ring
        _ ≤ lhyEpsX v R μ := le_trans h hE3
    have hden : 0 < (156 : ℝ) / 323
        * ((Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292)
          * Real.log (1 / Work.BoseFixR.dil v μ)) := by
      have h1 : 0 < (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292) :=
        Real.rpow_pos_of_pos hD0 _
      have h2 : 0 < Real.log (1 / Work.BoseFixR.dil v μ) := by linarith only [hLg1]
      positivity
    have hrate : (1 + Real.log (1 / Work.BoseFixR.dil v μ))
        / Real.log (1 / Work.BoseFixR.dil v μ) ≤ 2 := by
      rw [div_le_iff₀ (by linarith only [hLg1] : (0:ℝ) < Real.log (1 / Work.BoseFixR.dil v μ))]
      linarith only [hLg1]
    have hnum3 : 0 ≤ (10:ℝ) ^ 6 * (1 + Real.log (1 / Work.BoseFixR.dil v μ)) := by
      have h1 : (0:ℝ) < 1 + Real.log (1 / Work.BoseFixR.dil v μ) := by linarith only [hLg1]
      positivity
    have hstep : 10 ^ 6 * (1 + Real.log (1 / Work.BoseFixR.dil v μ)) / lhyEpsX v R μ
        ≤ 10 ^ 6 * (1 + Real.log (1 / Work.BoseFixR.dil v μ))
          / ((156 : ℝ) / 323 * ((Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292)
              * Real.log (1 / Work.BoseFixR.dil v μ))) :=
      div_le_div_of_nonneg_left hnum3 hden hE3b
    have heq : 10 ^ 6 * (1 + Real.log (1 / Work.BoseFixR.dil v μ))
          / ((156 : ℝ) / 323 * ((Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292)
              * Real.log (1 / Work.BoseFixR.dil v μ)))
        = 10 ^ 6 * (323 / 156) * (Work.BoseFixR.dil v μ) ^ (-(1 / 1292 : ℝ))
          * ((1 + Real.log (1 / Work.BoseFixR.dil v μ))
              / Real.log (1 / Work.BoseFixR.dil v μ)) := by
      rw [Real.rpow_neg hD0.le]
      have hDne : (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292) ≠ 0 :=
        ne_of_gt (Real.rpow_pos_of_pos hD0 _)
      have hLne : Real.log (1 / Work.BoseFixR.dil v μ) ≠ 0 := ne_of_gt (by linarith only [hLg1])
      field_simp
    calc bogT v R μ = 10 ^ 6 * (1 + Real.log (1 / Work.BoseFixR.dil v μ))
          / lhyEpsX v R μ := hTdef
      _ ≤ 10 ^ 6 * (323 / 156) * (Work.BoseFixR.dil v μ) ^ (-(1 / 1292 : ℝ))
            * ((1 + Real.log (1 / Work.BoseFixR.dil v μ))
              / Real.log (1 / Work.BoseFixR.dil v μ)) := le_trans hstep (le_of_eq heq)
      _ ≤ 10 ^ 6 * (323 / 156) * (Work.BoseFixR.dil v μ) ^ (-(1 / 1292 : ℝ)) * 2 := by
        have hpos : (0:ℝ) ≤ 10 ^ 6 * (323 / 156)
            * (Work.BoseFixR.dil v μ) ^ (-(1 / 1292 : ℝ)) := by
          have := Real.rpow_nonneg hD0.le (-(1 / 1292 : ℝ))
          positivity
        exact mul_le_mul_of_nonneg_left hrate hpos
      _ = 2 * 10 ^ 6 * (323 / 156) * (Work.BoseFixR.dil v μ) ^ (-(1 / 1292 : ℝ)) := by ring
  have hη0 : 0 ≤ bogEta v R ρ := bogEta_nonneg v hR.le hρ0.le
  have hsqμa : Real.sqrt (μ * _root_.BoseGases.a v)
      = (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 2) / _root_.BoseGases.a v := by
    rw [sqrt_mua v μ hμ hav, ← Real.sqrt_eq_rpow]
  have hsqρa : Real.sqrt (ρ * _root_.BoseGases.a v)
      ≤ Real.sqrt (11 / 10) * (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 2)
        / _root_.BoseGases.a v := by
    have h1 : Real.sqrt (ρ * _root_.BoseGases.a v)
        ≤ Real.sqrt ((11 : ℝ) / 10 * (μ * _root_.BoseGases.a v)) :=
      Real.sqrt_le_sqrt (by nlinarith)
    have h2 : Real.sqrt ((11 : ℝ) / 10 * (μ * _root_.BoseGases.a v))
        = Real.sqrt (11 / 10) * Real.sqrt (μ * _root_.BoseGases.a v) :=
      Real.sqrt_mul (x := (11:ℝ)/10) (by norm_num) (μ * _root_.BoseGases.a v)
    rw [h2, hsqμa] at h1
    calc Real.sqrt (ρ * _root_.BoseGases.a v)
        ≤ Real.sqrt (11 / 10) * ((Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 2) / _root_.BoseGases.a v) := h1
      _ = Real.sqrt (11 / 10) * (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 2) / _root_.BoseGases.a v := by
          ring
  exact
    { hμ := hμ, hD0 := hD0, hD1 := hD1, hDs := hDs, hL1 := hL1, hL0 := hL0,
      hρ0 := hρ0, hρlo := hρlo, hρhi := hρhi, hρsqrt := hρsqrt, hEeq := hEeq,
      hE0 := hE0, hEμa := hEμa, hE1 := hE1, hE2 := hE2, hE3 := hE3, hEup := hEup,
      hsmall := hsmall, hTdef := hTdef, hTpos := hTpos, hTlow := hTlow, hTup := hTup,
      hη0 := hη0, hsqρa := hsqρa, hsqμa := hsqμa, hℓ := ell_eq_boxSide v μ }

/-- `(μa)^{-1/2}·√(ρa) = √(ρ/μ)`. -/
lemma invsqrt_mul_sqrt (v : E3 → ℝ) (ρ μ : ℝ) (hav : 0 < _root_.BoseGases.a v)
    (hμ : 0 < μ) (hρ : 0 < ρ) :
    (μ * _root_.BoseGases.a v) ^ (-(1 / 2 : ℝ)) * Real.sqrt (ρ * _root_.BoseGases.a v)
      = Real.sqrt (ρ / μ) := by
  have h1 : (μ * _root_.BoseGases.a v) ^ (-(1 / 2 : ℝ))
      = (Real.sqrt (μ * _root_.BoseGases.a v))⁻¹ := by
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow]
  have h2 : ρ * _root_.BoseGases.a v / (μ * _root_.BoseGases.a v) = ρ / μ := by
    field_simp
  rw [h1, inv_mul_eq_div, ← h2]
  exact (Real.sqrt_div (x := ρ * _root_.BoseGases.a v) (by positivity)
    (μ * _root_.BoseGases.a v)).symm

/-- FS's first kinetic cutoff `c₁ = (2 s ℓ √(ρa))⁻¹` in the monomial form
`½(K_ℓs)⁻¹√(μ/ρ)` (the field `hc1val` of `FsI1Regime`). -/
lemma bogC1_eq (v : E3 → ℝ) (ρ μ : ℝ) (hav : 0 < _root_.BoseGases.a v)
    (hμ : 0 < μ) (hρ : 0 < ρ) :
    bogC1 v ρ μ = (1 / 2) * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹ * Real.sqrt (μ / ρ) := by
  have hsq : (μ * _root_.BoseGases.a v) ^ (-(1 / 2 : ℝ)) * Real.sqrt (ρ * _root_.BoseGases.a v)
      = Real.sqrt (ρ / μ) := invsqrt_mul_sqrt v ρ μ hav hμ hρ
  have hsq2 : Real.sqrt (ρ / μ) * Real.sqrt (μ / ρ) = 1 := by
    rw [← Real.sqrt_mul (show 0 ≤ ρ / μ by positivity), show ρ / μ * (μ / ρ) = 1 by field_simp,
      Real.sqrt_one]
  have hspos : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ≠ 0 :=
    ne_of_gt (by rw [paramsAt_s]; exact Real.rpow_pos_of_pos (dil_pos v hμ hav) _)
  have hKpos : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl ≠ 0 :=
    ne_of_gt (by rw [paramsAt_Kl]; exact Real.rpow_pos_of_pos (dil_pos v hμ hav) _)
  have hℓ : Work.BoseFixR.ell v μ = (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
      * (μ * _root_.BoseGases.a v) ^ (-(1 / 2 : ℝ)) := ell_eq_boxSide v μ
  unfold bogC1
  rw [hℓ,
    show 2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
        * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
          * (μ * _root_.BoseGases.a v) ^ (-(1 / 2 : ℝ))) * Real.sqrt (ρ * _root_.BoseGases.a v)
      = 2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl * Real.sqrt (ρ / μ) by
      rw [← hsq]; ring]
  refine inv_eq_of_mul_eq_one_right ?_
  have hsKl : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ≠ 0 := mul_ne_zero hKpos hspos
  calc 2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl * Real.sqrt (ρ / μ)
        * ((1 / 2) * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹ * Real.sqrt (μ / ρ))
      = (2 * (1 / 2)) * (((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)
          * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹)
        * (Real.sqrt (ρ / μ) * Real.sqrt (μ / ρ)) := by ring
    _ = 1 := by rw [hsq2, mul_inv_cancel₀ hsKl]; norm_num

/-- FS's second kinetic cutoff `c₂ = (2 d s ℓ √(ρa))⁻¹` in the monomial form
`½(K_ℓds)⁻¹√(μ/ρ)` (the field `hc2val` of `FsI1Regime`). -/
lemma bogC2_eq (v : E3 → ℝ) (ρ μ : ℝ) (hav : 0 < _root_.BoseGases.a v)
    (hμ : 0 < μ) (hρ : 0 < ρ) :
    bogC2 v ρ μ = (1 / 2) * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹ * Real.sqrt (μ / ρ) := by
  have hsq : (μ * _root_.BoseGases.a v) ^ (-(1 / 2 : ℝ)) * Real.sqrt (ρ * _root_.BoseGases.a v)
      = Real.sqrt (ρ / μ) := invsqrt_mul_sqrt v ρ μ hav hμ hρ
  have hsq2 : Real.sqrt (ρ / μ) * Real.sqrt (μ / ρ) = 1 := by
    rw [← Real.sqrt_mul (show 0 ≤ ρ / μ by positivity), show ρ / μ * (μ / ρ) = 1 by field_simp,
      Real.sqrt_one]
  have hD0 : 0 < Work.BoseFixR.dil v μ := dil_pos v hμ hav
  have hspos : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ≠ 0 :=
    ne_of_gt (by rw [paramsAt_s]; exact Real.rpow_pos_of_pos hD0 _)
  have hKpos : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl ≠ 0 :=
    ne_of_gt (by rw [paramsAt_Kl]; exact Real.rpow_pos_of_pos hD0 _)
  have hdpos : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ≠ 0 :=
    ne_of_gt (by rw [paramsAt_d]; exact Real.rpow_pos_of_pos hD0 _)
  have hℓ : Work.BoseFixR.ell v μ = (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
      * (μ * _root_.BoseGases.a v) ^ (-(1 / 2 : ℝ)) := ell_eq_boxSide v μ
  unfold bogC2
  rw [hℓ,
    show 2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
        * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
          * (μ * _root_.BoseGases.a v) ^ (-(1 / 2 : ℝ))) * Real.sqrt (ρ * _root_.BoseGases.a v)
      = 2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl * Real.sqrt (ρ / μ) by
      rw [← hsq]; ring]
  refine inv_eq_of_mul_eq_one_right ?_
  have hsKl : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ≠ 0 :=
    mul_ne_zero (mul_ne_zero hKpos hdpos) hspos
  calc 2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl * Real.sqrt (ρ / μ)
        * ((1 / 2) * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹ * Real.sqrt (μ / ρ))
      = (2 * (1 / 2)) * (((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)
          * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹)
        * (Real.sqrt (ρ / μ) * Real.sqrt (μ / ρ)) := by ring
    _ = 1 := by rw [hsq2, mul_inv_cancel₀ hsKl]; norm_num

end Work.BoseBogFS
