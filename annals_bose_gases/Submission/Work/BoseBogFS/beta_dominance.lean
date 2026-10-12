import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.BogFSCompare
import Submission.Work.BoseBogFS.honestFsCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.beta_dominance`

FS's *quartic* domination row of the affine-kernel comparison: at FS's parameters
(`s = X`, `d = X⁶`, `ε_T = X^{23/4}`, `K_ℓ = X^{-3/2}`, `X = (μa³)^{1/323}`) the two
`β`-rows of the bulk bracket built from the honest kernel `bogKernel v R ρ μ`,

  `Δ·T³ + η·T⁴`,  `Δ = bogDelta R ℓ chiTC = 16π·chiTC·(R/ℓ)²`,
                    `η = bogEta v R ρ = 16πR√(ρa)`,   `T = bogT v R μ`,

are dominated by FS's error `ε(μ,ρ_z) = lhyEps (a v) R ε_T K_ℓ s d μ` for all small
enough diluteness `μa³` and all `ρ` in FS's close region.

**Mathematics.**  Let `D = μa³ = dil v μ ∈ (0,1]`, and write the box side
`ℓ = K_ℓ(μa)^{-1/2}`, so that `(R/ℓ)² = R²D^{326/323}/a²` (`paramsAt_Kl_inv_sq` +
`μa = D/a²`).  The shared parameter bounds `Core v R μ ρ` (`honestFsCore`, available for
`D ≤ coreBound v R`) give, with `C_T = 2·10⁶·(323/156)`,

  `T ≤ C_T·D^{-1/1292}`,   `√(ρa) ≤ √(11/10)·D^{1/2}/a`,   `ε ≥ D^{1/1292}·(1+(156/323)log D^{-1}) ≥ D^{1/1292}`.

Hence, with `K_A = 16π·chiTC·R²C_T³/a²` and `c_B = 16π√(11/10)·C_T⁴·R/a`,

  `ΔT³ ≤ K_A·D^{1301/1292} = K_A·D^{1/1292}·D^{1300/1292}`,
  `ηT⁴ ≤ c_B·D^{642/1292} = c_B·D^{1/1292}·D^{641/1292}`,

and choosing the diluteness threshold so that `D^{1300/1292} ≤ 1/(2(K_A+1))` and
`D^{641/1292} ≤ 1/(2(c_B+1))` each row is at most `½D^{1/1292}`, so their sum is at most
`D^{1/1292} ≤ ε`.  (The powers are super-small because `D ≤ coreBound v R` is astronomically
small; the two thresholds are `(1/(2(K+1)))^{1/e}` for the exponents `e = 1300/1292` and
`e = 641/1292` respectively.)
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix Work.BoseFixR
open Work.BoseBoxFock

namespace Work.BoseBogFS

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The normalisation constant of FS's momentum cutoff `T`: the parameter bounds of
`Core` give `T ≤ bogCT·D^{-1/1292}` with `bogCT = 2·10⁶·(323/156)`. -/
def bogCT : ℝ := 2 * 10 ^ 6 * (323 / 156)

lemma bogCT_nonneg : 0 ≤ bogCT := by
  rw [bogCT]; norm_num

/-- **The box-scale `(R/ℓ)²` identity**: `(R/ℓ)² = R²D^{326/323}/a²` with
`D = dil v μ = μ(a v)³` and `ℓ = ell v μ = K_ℓ(μa)^{-1/2}`. -/
theorem ell_inv_sq_eq {v : E3 → ℝ} {R μ : ℝ} (hμ : 0 < μ) (hav : 0 < a v) :
    (R / ell v μ)^2 = R^2 * (dil v μ)^((326 : ℝ) / 323) / (a v)^2 := by
  have hmua : 0 < μ * a v := mul_pos hμ hav
  have hD0 : 0 < dil v μ := dil_pos v hμ hav
  have hKlpos : 0 < (paramsAt μ (a v)).Kl := by
    rw [paramsAt_Kl]; exact Real.rpow_pos_of_pos hD0 _
  have hell2 : (ell v μ)^2 = (paramsAt μ (a v)).Kl^2 / (μ * a v) := by
    rw [ell_eq_boxSide v μ, mul_pow]
    have h1 : ((μ * a v) ^ (-(1/2:ℝ)))^2 = (μ * a v)^(-(1:ℝ)) := by
      rw [pow_two, ← Real.rpow_add hmua]; norm_num
    rw [h1, Real.rpow_neg hmua.le, Real.rpow_one, div_eq_mul_inv]
  have hKlneg : ((paramsAt μ (a v)).Kl^2)⁻¹ = (dil v μ)^((3:ℝ)/323) := by
    rw [show ((paramsAt μ (a v)).Kl^2)⁻¹ = (paramsAt μ (a v)).Kl ^ (-(2:ℝ)) by
          rw [Real.rpow_neg hKlpos.le]; norm_num]
    exact paramsAt_Kl_inv_sq v μ hD0
  have hmain : (R / ell v μ)^2 = R^2 * (μ * a v) * (dil v μ)^((3:ℝ)/323) := by
    calc (R / ell v μ)^2 = R^2 * ((ell v μ)^2)⁻¹ := by rw [div_pow, div_eq_mul_inv]
      _ = R^2 * ((paramsAt μ (a v)).Kl^2 / (μ*a v))⁻¹ := by rw [hell2]
      _ = R^2 * ((μ*a v) * ((paramsAt μ (a v)).Kl^2)⁻¹) := by rw [inv_div, div_eq_mul_inv]
      _ = R^2 * ((μ*a v) * (dil v μ)^((3:ℝ)/323)) := by rw [hKlneg]
      _ = R^2 * (μ*a v) * (dil v μ)^((3:ℝ)/323) := by ring
  have hconv : R^2 * (μ * a v) * (dil v μ)^((3:ℝ)/323)
      = R^2 * (dil v μ)^((326:ℝ)/323) / (a v)^2 := by
    have key : (μ * a v) * (dil v μ)^((3:ℝ)/323) = (dil v μ)^((326:ℝ)/323) / (a v)^2 := by
      have ha2 : (a v)^2 ≠ 0 := pow_ne_zero 2 hav.ne'
      rw [eq_div_iff ha2]
      rw [show (μ * a v) * (dil v μ)^((3:ℝ)/323) * (a v)^2
            = (μ * (a v)^3) * (dil v μ)^((3:ℝ)/323) by ring]
      rw [show μ * (a v)^3 = dil v μ from rfl]
      rw [show ((326:ℝ)/323) = 1 + 3/323 by norm_num, Real.rpow_add hD0, Real.rpow_one]
    rw [show R^2 * (μ*a v) * (dil v μ)^((3:ℝ)/323)
          = R^2 * ((μ*a v)*(dil v μ)^((3:ℝ)/323)) by ring]
    rw [key, mul_div_assoc]
  rw [hmain, hconv]

/-- **The diluteness-threshold lemma.**  If `0 < D ≤ 1` and `D ≤ (1/(2(K+1)))^{1/e}` with
`K ≥ 0`, `e > 0`, then `D^b ≤ 1/(2(K+1))` for every `b ≥ e`. -/
theorem rpow_thresh_le {K e D b : ℝ} (hK : 0 ≤ K) (he : 0 < e) (hD0 : 0 < D)
    (hD1 : D ≤ 1) (hD : D ≤ (1/(2*(K+1)))^(1/e)) (hb : e ≤ b) :
    D^b ≤ 1/(2*(K+1)) := by
  have hbase : 0 < 1/(2*(K+1)) := by
    have : (0:ℝ) < K + 1 := by linarith
    positivity
  have h1 : D^b ≤ D^e := Real.rpow_le_rpow_of_exponent_ge hD0 hD1 hb
  have h2 : D^e ≤ ((1/(2*(K+1)))^(1/e))^e := Real.rpow_le_rpow hD0.le hD he.le
  have h3 : ((1/(2*(K+1)))^(1/e))^e = 1/(2*(K+1)) := by
    rw [← Real.rpow_mul hbase.le]
    rw [show (1/e) * e = 1 by rw [div_mul_eq_mul_div, one_mul, div_self he.ne']]
    rw [Real.rpow_one]
  linarith [h1, h2, h3.le, h3.ge]

/-- **The powers of the momentum cutoff**: `T^n ≤ bogCT^n·D^{-n/1292}`. -/
theorem bogT_pow_le {v : E3 → ℝ} {R μ ρ : ℝ} (hcore : Core v R μ ρ) (n : ℕ) :
    (bogT v R μ)^n ≤ bogCT^n * (dil v μ)^(-((n:ℝ)/1292)) := by
  have hD0 := hcore.hD0
  have hTup : bogT v R μ ≤ bogCT * (dil v μ)^(-(1/1292:ℝ)) := by
    rw [bogCT]; exact hcore.hTup
  calc (bogT v R μ)^n ≤ (bogCT * (dil v μ)^(-(1/1292:ℝ)))^n :=
        pow_le_pow_left₀ hcore.hTpos.le hTup n
    _ = bogCT^n * ((dil v μ)^(-(1/1292:ℝ)))^n := by rw [mul_pow]
    _ = bogCT^n * (dil v μ)^(-((n:ℝ)/1292)) := by
        congr 1
        rw [← Real.rpow_natCast ((dil v μ)^(-(1/1292:ℝ))) n, ← Real.rpow_mul hD0.le]
        congr 1
        ring

/-- **The `η`-row**: `bogEta v R ρ ≤ 16π√(11/10)·D^{1/2}·R/a`. -/
theorem bogEta_le {v : E3 → ℝ} {R μ ρ : ℝ} (hR : 0 < R) (hcore : Core v R μ ρ) :
    bogEta v R ρ ≤ 16 * Real.pi * Real.sqrt (11/10) * (dil v μ)^((1:ℝ)/2) * R / (a v) := by
  rw [bogEta]
  have h1 : Real.sqrt (ρ * a v) ≤ Real.sqrt (11/10) * (dil v μ)^((1:ℝ)/2) / (a v) := hcore.hsqρa
  calc 16 * Real.pi * R * Real.sqrt (ρ * a v)
      ≤ 16 * Real.pi * R * (Real.sqrt (11/10) * (dil v μ)^((1:ℝ)/2) / (a v)) := by
          apply mul_le_mul_of_nonneg_left h1; positivity
    _ = 16 * Real.pi * Real.sqrt (11/10) * (dil v μ)^((1:ℝ)/2) * R / (a v) := by ring

theorem beta_dominance {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ}
    (hR : 0 < R) (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ ρ : ℝ,
      Work.BoseBoxFock.CloseCondFS v μ ρ →
      Work.BoseBogFS.bogDelta R (Work.BoseFixR.ell v μ) Work.BoseBogFS.chiTC
          * (Work.BoseBogFS.bogT v R μ) ^ 3
        + Work.BoseBogFS.bogEta v R ρ * (Work.BoseBogFS.bogT v R μ) ^ 4
      ≤ Work.BoseB6.lhyEps (_root_.BoseGases.a v) R
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ := by
  set KA : ℝ := 16 * Real.pi * chiTC * R^2 * bogCT^3 / (a v)^2 with hKA
  set cB : ℝ := 16 * Real.pi * Real.sqrt (11/10) * bogCT^4 * R / (a v) with hcB
  have hKA0 : 0 ≤ KA := by
    rw [hKA]
    have hb3 : 0 ≤ bogCT^3 := pow_nonneg bogCT_nonneg 3
    have hpi : 0 ≤ 16 * Real.pi * chiTC := by
      have := chiTC_nonneg; positivity
    exact div_nonneg (mul_nonneg (mul_nonneg hpi (sq_nonneg R)) hb3) (sq_nonneg _)
  have hcB0 : 0 ≤ cB := by
    rw [hcB]
    have hb4 : 0 ≤ bogCT^4 := pow_nonneg bogCT_nonneg 4
    have hpi : 0 ≤ 16 * Real.pi * Real.sqrt (11/10) := by positivity
    exact div_nonneg (mul_nonneg (mul_nonneg hpi hb4) hR.le) hav.le
  have hApos : 0 < 1/(2*(KA+1)) := by
    have : (0:ℝ) < KA + 1 := by linarith
    positivity
  have hBpos : 0 < 1/(2*(cB+1)) := by
    have : (0:ℝ) < cB + 1 := by linarith
    positivity
  have heApos : 0 < (1/(2*(KA+1)))^((1292:ℝ)/1287) :=
    Real.rpow_pos_of_pos hApos _
  have heBpos : 0 < (1/(2*(cB+1)))^((1292:ℝ)/641) :=
    Real.rpow_pos_of_pos hBpos _
  set eps : ℝ := min (coreBound v R)
    (min ((1/(2*(KA+1)))^((1292:ℝ)/1287)) ((1/(2*(cB+1)))^((1292:ℝ)/641))) with heps
  have heps0 : 0 < eps := by
    rw [heps]
    exact lt_min (coreBound_pos hR hav) (lt_min heApos heBpos)
  have hεcore : eps ≤ coreBound v R := by rw [heps]; exact min_le_left _ _
  have hεA : eps ≤ (1/(2*(KA+1)))^((1292:ℝ)/1287) := by
    rw [heps]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hεB : eps ≤ (1/(2*(cB+1)))^((1292:ℝ)/641) := by
    rw [heps]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨eps, heps0, ?_⟩
  intro μ hAdm ρ hclose
  obtain ⟨hμ, hDε, -⟩ := hAdm
  have hcore : Core v R μ ρ := core_bounds hR hav hεcore μ ρ hμ hDε hclose
  have hD0 : 0 < dil v μ := hcore.hD0
  have hD1 : dil v μ ≤ 1 := hcore.hD1
  have hDnn : 0 ≤ (dil v μ)^((1:ℝ)/1292) := Real.rpow_nonneg hD0.le _
  -- FS's error dominates the surviving power `D^{1/1292}`
  have hlhy : (dil v μ)^((1:ℝ)/1292) ≤
      Work.BoseB6.lhyEps (a v) R (paramsAt μ (a v)).eT (paramsAt μ (a v)).Kl
        (paramsAt μ (a v)).s (paramsAt μ (a v)).d μ := by
    rw [hcore.hEeq]
    calc (dil v μ)^((1:ℝ)/1292) = (dil v μ)^((1:ℝ)/1292) * 1 := by ring
      _ ≤ (dil v μ)^((1:ℝ)/1292) * (1 + ((156:ℝ)/323) * bogL v μ) := by
            apply mul_le_mul_of_nonneg_left _ hDnn
            linarith [hcore.hL0]
      _ ≤ lhyEpsX v R μ := hcore.hE3
  -- the quartic row `ΔT³`
  have hA : bogDelta R (ell v μ) chiTC * (bogT v R μ)^3
      ≤ (1/2) * (dil v μ)^((1:ℝ)/1292) := by
    have hT3 : (bogT v R μ)^3 ≤ bogCT^3 * (dil v μ)^(-((3:ℝ)/1292)) := by
      convert bogT_pow_le hcore 3 using 3 <;> norm_num
    have hbell : bogDelta R (ell v μ) chiTC
        = 16 * Real.pi * chiTC * (R^2 * (dil v μ)^((326:ℝ)/323) / (a v)^2) := by
      rw [bogDelta, ell_inv_sq_eq hμ hav]
    have hb0 : 0 ≤ 16 * Real.pi * chiTC * (R^2 * (dil v μ)^((326:ℝ)/323) / (a v)^2) := by
      have h2 : 0 ≤ (dil v μ)^((326:ℝ)/323) := Real.rpow_nonneg hD0.le _
      have h3 : 0 ≤ R^2 * (dil v μ)^((326:ℝ)/323) / (a v)^2 :=
        div_nonneg (mul_nonneg (sq_nonneg R) h2) (sq_nonneg _)
      exact mul_nonneg (mul_nonneg (by positivity) chiTC_nonneg) h3
    have hstep : bogDelta R (ell v μ) chiTC * (bogT v R μ)^3
        ≤ 16 * Real.pi * chiTC * (R^2 * (dil v μ)^((326:ℝ)/323) / (a v)^2)
            * (bogCT^3 * (dil v μ)^(-((3:ℝ)/1292))) :=
      mul_le_mul hbell.le hT3 (pow_nonneg hcore.hTpos.le 3) hb0
    have hE1 : (dil v μ)^((326:ℝ)/323) * (dil v μ)^(-((3:ℝ)/1292))
        = (dil v μ)^((1301:ℝ)/1292) := by
      rw [← Real.rpow_add hD0,
        show ((326:ℝ)/323) + (-((3:ℝ)/1292)) = 1301/1292 by norm_num]
    have hE2 : (dil v μ)^((1301:ℝ)/1292)
        = (dil v μ)^((1:ℝ)/1292) * (dil v μ)^((1300:ℝ)/1292) := by
      rw [show ((1301:ℝ)/1292) = 1/1292 + 1300/1292 by norm_num, Real.rpow_add hD0]
    have hεA' : dil v μ ≤ (1/(2*(KA+1)))^(1/((1287:ℝ)/1292)) := by
      rw [show (1:ℝ)/((1287:ℝ)/1292) = 1292/1287 by norm_num]
      exact le_trans hDε hεA
    have hE3 : (dil v μ)^((1300:ℝ)/1292) ≤ 1/(2*(KA+1)) :=
      rpow_thresh_le (K := KA) (e := (1287:ℝ)/1292) (D := dil v μ) (b := (1300:ℝ)/1292)
        hKA0 (by norm_num) hD0 hD1 hεA' (by norm_num)
    calc bogDelta R (ell v μ) chiTC * (bogT v R μ)^3
        ≤ 16 * Real.pi * chiTC * (R^2 * (dil v μ)^((326:ℝ)/323) / (a v)^2)
            * (bogCT^3 * (dil v μ)^(-((3:ℝ)/1292))) := hstep
      _ = KA * ((dil v μ)^((326:ℝ)/323) * (dil v μ)^(-((3:ℝ)/1292))) := by
            rw [hKA]; ring
      _ = KA * (dil v μ)^((1301:ℝ)/1292) := by rw [hE1]
      _ = KA * ((dil v μ)^((1:ℝ)/1292) * (dil v μ)^((1300:ℝ)/1292)) := by rw [hE2]
      _ ≤ KA * ((dil v μ)^((1:ℝ)/1292) * (1/(2*(KA+1)))) := by
            apply mul_le_mul_of_nonneg_left _ hKA0
            exact mul_le_mul_of_nonneg_left hE3 (Real.rpow_nonneg hD0.le _)
      _ ≤ (1/2) * (dil v μ)^((1:ℝ)/1292) := by
            have hcoef : KA * (1/(2*(KA+1))) ≤ 1/2 := by
              rw [mul_one_div, div_le_iff₀ (by linarith : (0:ℝ) < 2*(KA+1))]
              linarith
            calc KA * ((dil v μ)^((1:ℝ)/1292) * (1/(2*(KA+1))))
                = (dil v μ)^((1:ℝ)/1292) * (KA * (1/(2*(KA+1)))) := by ring
              _ ≤ (dil v μ)^((1:ℝ)/1292) * (1/2) :=
                  mul_le_mul_of_nonneg_left hcoef hDnn
              _ = (1/2) * (dil v μ)^((1:ℝ)/1292) := by ring
  -- the quartic row `ηT⁴`
  have hB : bogEta v R ρ * (bogT v R μ)^4 ≤ (1/2) * (dil v μ)^((1:ℝ)/1292) := by
    have hT4 : (bogT v R μ)^4 ≤ bogCT^4 * (dil v μ)^(-((4:ℝ)/1292)) := by
      convert bogT_pow_le hcore 4 using 3 <;> norm_num
    have heta : bogEta v R ρ
        ≤ 16 * Real.pi * Real.sqrt (11/10) * (dil v μ)^((1:ℝ)/2) * R / (a v) :=
      bogEta_le hR hcore
    have hb0 : 0 ≤ 16 * Real.pi * Real.sqrt (11/10) * (dil v μ)^((1:ℝ)/2) * R / (a v) := by
      have h2 : 0 ≤ (dil v μ)^((1:ℝ)/2) := Real.rpow_nonneg hD0.le _
      have := Real.sqrt_nonneg (11/10)
      positivity
    have hstep : bogEta v R ρ * (bogT v R μ)^4
        ≤ (16 * Real.pi * Real.sqrt (11/10) * (dil v μ)^((1:ℝ)/2) * R / (a v))
            * (bogCT^4 * (dil v μ)^(-((4:ℝ)/1292))) :=
      mul_le_mul heta hT4 (pow_nonneg hcore.hTpos.le 4) hb0
    have hE1 : (dil v μ)^((1:ℝ)/2) * (dil v μ)^(-((4:ℝ)/1292))
        = (dil v μ)^((642:ℝ)/1292) := by
      rw [← Real.rpow_add hD0,
        show ((1:ℝ)/2) + (-((4:ℝ)/1292)) = 642/1292 by norm_num]
    have hE2 : (dil v μ)^((642:ℝ)/1292)
        = (dil v μ)^((1:ℝ)/1292) * (dil v μ)^((641:ℝ)/1292) := by
      rw [show ((642:ℝ)/1292) = 1/1292 + 641/1292 by norm_num, Real.rpow_add hD0]
    have hεB' : dil v μ ≤ (1/(2*(cB+1)))^(1/((641:ℝ)/1292)) := by
      rw [show (1:ℝ)/((641:ℝ)/1292) = 1292/641 by norm_num]
      exact le_trans hDε hεB
    have hE3 : (dil v μ)^((641:ℝ)/1292) ≤ 1/(2*(cB+1)) :=
      rpow_thresh_le (K := cB) (e := (641:ℝ)/1292) (D := dil v μ) (b := (641:ℝ)/1292)
        hcB0 (by norm_num) hD0 hD1 hεB' (le_refl _)
    calc bogEta v R ρ * (bogT v R μ)^4
        ≤ (16 * Real.pi * Real.sqrt (11/10) * (dil v μ)^((1:ℝ)/2) * R / (a v))
            * (bogCT^4 * (dil v μ)^(-((4:ℝ)/1292))) := hstep
      _ = cB * ((dil v μ)^((1:ℝ)/2) * (dil v μ)^(-((4:ℝ)/1292))) := by
            rw [hcB]; ring
      _ = cB * (dil v μ)^((642:ℝ)/1292) := by rw [hE1]
      _ = cB * ((dil v μ)^((1:ℝ)/1292) * (dil v μ)^((641:ℝ)/1292)) := by rw [hE2]
      _ ≤ cB * ((dil v μ)^((1:ℝ)/1292) * (1/(2*(cB+1)))) := by
            apply mul_le_mul_of_nonneg_left _ hcB0
            exact mul_le_mul_of_nonneg_left hE3 (Real.rpow_nonneg hD0.le _)
      _ ≤ (1/2) * (dil v μ)^((1:ℝ)/1292) := by
            have hcoef : cB * (1/(2*(cB+1))) ≤ 1/2 := by
              rw [mul_one_div, div_le_iff₀ (by linarith : (0:ℝ) < 2*(cB+1))]
              linarith
            calc cB * ((dil v μ)^((1:ℝ)/1292) * (1/(2*(cB+1))))
                = (dil v μ)^((1:ℝ)/1292) * (cB * (1/(2*(cB+1)))) := by ring
              _ ≤ (dil v μ)^((1:ℝ)/1292) * (1/2) :=
                  mul_le_mul_of_nonneg_left hcoef hDnn
              _ = (1/2) * (dil v μ)^((1:ℝ)/1292) := by ring
  calc bogDelta R (ell v μ) chiTC * (bogT v R μ)^3
        + bogEta v R ρ * (bogT v R μ)^4
      ≤ (1/2) * (dil v μ)^((1:ℝ)/1292) + (1/2) * (dil v μ)^((1:ℝ)/1292) := add_le_add hA hB
    _ = (dil v μ)^((1:ℝ)/1292) := by ring
    _ ≤ Work.BoseB6.lhyEps (a v) R (paramsAt μ (a v)).eT (paramsAt μ (a v)).Kl
          (paramsAt μ (a v)).s (paramsAt μ (a v)).d μ := hlhy

end Work.BoseBogFS
