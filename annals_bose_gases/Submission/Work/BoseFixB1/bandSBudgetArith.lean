import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB7A.errA_bounds
import Submission.Work.BoseFixB1.BoxCountBand
import Submission.Work.BoseFixB1.fsRegimeAt
import Submission.Work.BoseFixB1.sbWord_marginal_integrable
import Submission.Work.BoseFixB1B.perBoxCrudeLower
import Submission.Work.LocRepoint.bandSet_measure_le_nohyp
import Submission.Work.LocRepoint.chiSmallB_sq_integral_u
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.bandSBudgetArith` — the band budget is paid by the gap term

The consumer `Work.BoseFixB1.bandWordLower_cond_of_arith` needs the arithmetic input

    2·μ·(a v)·K·|bandSet ℓ d μ|·bandS M ℓ d μ ≤ b/(2ℓ²)

at every admissible point, with the *free* constant `K ≥ 0` (the linear fibre constant of
`Work.BoseFixB1S.PerBoxFibreB1`).  This module proves it.

## The computation

With `A = a v`, `t = μA³`, `ℓ = sideAt μ A = A·fsXp t (-163)`, `d = (paramsAt μ A).d = fsXp t 6`,
`M = 48`, `b = 1/16`, the three factors are

* `|bandSet| ≤ 12·fsXp t (112/3)·(1+d)²` — the band is bounded, with the *exact* fsXp closed form
  (`bandSet_measure_le_nohyp`, valid for all `ℓ,d,μ > 0`, no regime hypothesis needed);
* `bandS 48 ℓ d μ = chiSupAbs·chiSmallDecay 48·2⁴⁸·fsXp t 2368` — `bandS²` is a product of
  squares, so the square root splits (`bandS_eq_prod`), and the two factors
  `d^{-48} = fsXp t (-288)` and `(2μ^{-1/3}/ℓ)^{48} = 2⁴⁸ fsXp t 2656` combine
  (`bandS_eq_fsXp`);
* `μA = A^{-2}·fsXp t 323`, `ℓ^{-2} = A^{-2}·fsXp t 326`, `b = 1/16`.

Hence (with `κ = chiSupAbs·chiSmallDecay 48` and `fsXp_mul` bookkeeping
`112/3 + 2368 + 323 = 8185/3` and `8185/3 = 326 + 7207/3`)

    LHS ≤ 24·2⁴⁸·κ·K·A^{-2}·fsXp t (8185/3)·(1+d)²
        = (A^{-2}·fsXp t 326)·(24·2⁴⁸·κ·K·fsXp t (7207/3)·(1+d)²),

and it remains to make the second factor at most `1/32 = b/2`.  Since `(1+d)² ≤ 4` and
`fsXp t (7207/3) = t^{7207/969}` is increasing in `t`, it suffices that
`3072·2⁴⁸·κ·K·t^{7207/969} ≤ 1`, which holds for `t ≤ min X₀ 1` with `X₀` from
`Work.BoseB7A.exists_small_rpow`.  All powers combine through the single `fsXp` calculus of
`Work.BoseFixB1.RegimeAux`, so no asymptotic estimate is used anywhere.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## 1. The band `χ`-scale in product form -/

private lemma rpow_third (x : ℝ) : x ^ (-1 / 3 : ℝ) = x ^ (-(1 / 3) : ℝ) := by
  congr 1
  norm_num

/-- **`bandS` as a product.**  `bandS²` is the product of the two squares
`(chiSupAbs·chiSmallDecay M·d^{-M})²` and `((2μ^{-1/3}/ℓ)^M)²`, so (for `d, ℓ, μ > 0`) the square
root splits: `bandS = chiSupAbs·chiSmallDecay M·d^{-M}·(2μ^{-1/3}/ℓ)^M`. -/
lemma bandS_eq_prod {M : ℕ} {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hμ : 0 < μ) :
    bandS M ℓ d μ
      = Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
        * (d⁻¹) ^ M * (2 * μ ^ (-1 / 3 : ℝ) / ℓ) ^ M := by
  have hC0 : 0 ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
      * (d⁻¹) ^ M :=
    mul_nonneg (mul_nonneg Submission.BoseGases.chiSupAbs_nonneg
      (Submission.BoseGases.chiSmallDecay_nonneg M))
      (pow_nonneg (inv_nonneg.mpr hd.le) M)
  have hD0 : 0 ≤ (2 * μ ^ (-1 / 3 : ℝ) / ℓ) ^ M :=
    pow_nonneg (div_nonneg (mul_nonneg (by norm_num) (le_of_lt (Real.rpow_pos_of_pos hμ _)))
      (le_of_lt hℓ)) M
  have hsq : bandS M ℓ d μ ^ 2
      = (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M * (d⁻¹) ^ M
          * (2 * μ ^ (-1 / 3 : ℝ) / ℓ) ^ M) ^ 2 := by
    rw [bandS_sq hℓ hd hμ,
      show Submission.BoseGases.chiSmallBandDecay M d
          = (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
              * (d⁻¹) ^ M) ^ 2 by
        rw [Submission.BoseGases.chiSmallBandDecay, mul_pow, mul_pow]
        conv_rhs => rw [← pow_mul, Nat.mul_comm],
      show (2 * μ ^ (-1 / 3 : ℝ) / ℓ) ^ (2 * M)
          = ((2 * μ ^ (-1 / 3 : ℝ) / ℓ) ^ M) ^ 2 by
        conv_rhs => rw [← pow_mul, Nat.mul_comm]]
    ring
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq) with h' | h'
  · exact h'
  · have hb := bandS_nonneg M ℓ d μ
    linarith [mul_nonneg hC0 hD0]

/-! ## 2. The band volume in `fsXp` form -/

/-- **The band volume in closed form.**  The band measure bound `bandSet_measure_le`
(in the `hAδ`-free form of `Work.LocRepoint.bandSet_measure_le_nohyp`) together with the
`fsXp` bookkeeping `(ℓd) = A·fsXp t(-157)`, `μ^{-1/3} = A·fsXp t(-323/3)`,
`ℓ = A·fsXp t(-163)` gives `|bandSet| ≤ 12·fsXp t(112/3)·(1+d)²` — an *identity* in `fsXp`,
no regime hypothesis. -/
lemma bandVolume_le_fsXp' {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) :
    (MeasureTheory.volume (bandSet (sideAt μ A) (paramsAt μ A).d μ)).toReal
      ≤ 12 * fsXp (μ * A ^ 3) (112 / 3) * (1 + (paramsAt μ A).d) ^ 2 := by
  set t : ℝ := μ * A ^ 3 with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have hℓ : 0 < sideAt μ A := sideAt_pos hμ hA
  have hd : 0 < (paramsAt μ A).d := by
    rw [d_eq_fsXp, ← ht]; exact fsXp_pos ht0
  have hb := Work.LocRepoint.bandSet_measure_le_nohyp (L := sideAt μ A)
    (d := (paramsAt μ A).d) (μ := μ) hℓ hd hμ
  have hYid : fsXp t (-(323 / 3)) = fsXp t (112 / 3) * fsXp t (-163) * (fsXp t 6) ^ 3 := by
    rw [fsXp_pow ht0.le 6 3, fsXp_mul ht0, fsXp_mul ht0]
    congr 1
    norm_num
  have hkey : 12 * μ ^ (-1 / 3 : ℝ) * (sideAt μ A) ^ 2
      = (12 * fsXp t (112 / 3)) * (sideAt μ A * (paramsAt μ A).d) ^ 3 := by
    rw [show 12 * μ ^ (-1 / 3 : ℝ) * (sideAt μ A) ^ 2
        = 12 * (μ ^ (-1 / 3 : ℝ) * (sideAt μ A) ^ 2) by ring]
    rw [rpow_third μ, sideAt_eq_fsXp hA hμ, d_eq_fsXp, mu_inv_third_eq hA hμ, ← ht, mul_pow]
    rw [hYid]
    ring
  refine le_trans hb ?_
  have hstep : ((sideAt μ A * (paramsAt μ A).d) ^ 3)⁻¹
        * (12 * μ ^ (-1 / 3 : ℝ) * (sideAt μ A) ^ 2 * (1 + (paramsAt μ A).d) ^ 2)
      = 12 * fsXp t (112 / 3) * (1 + (paramsAt μ A).d) ^ 2 := by
    rw [hkey]
    field_simp
  rw [hstep]

/-! ## 3. `bandS` in `fsXp` form -/

/-- **`bandS` in closed form.**  `μ^{-1/3}/ℓ = fsXp t(166/3)`, `d^{-1} = fsXp t(-6)`, so
`bandS M ℓ d μ = chiSupAbs·chiSmallDecay M·2^M·fsXp t(148M/3)`. -/
lemma bandS_eq_fsXp {M : ℕ} {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) :
    bandS M (sideAt μ A) (paramsAt μ A).d μ
      = Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M * 2 ^ M
        * fsXp (μ * A ^ 3) (148 * M / 3) := by
  set t : ℝ := μ * A ^ 3 with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have hℓ : 0 < sideAt μ A := sideAt_pos hμ hA
  have hd : 0 < (paramsAt μ A).d := by
    rw [d_eq_fsXp, ← ht]; exact fsXp_pos ht0
  rw [bandS_eq_prod hℓ hd hμ]
  have hratio : μ ^ (-1 / 3 : ℝ) / sideAt μ A = fsXp t (166 / 3) := by
    have h1 : μ ^ (-1 / 3 : ℝ) = fsXp t (166 / 3) * sideAt μ A := by
      rw [rpow_third μ, sideAt_eq_fsXp hA hμ, mu_inv_third_eq hA hμ, ← ht]
      rw [show fsXp t (166 / 3) * (A * fsXp t (-163))
          = A * (fsXp t (166 / 3) * fsXp t (-163)) by ring]
      rw [fsXp_mul ht0]
      congr 1
      norm_num
    rw [h1, mul_div_cancel_right₀ _ (ne_of_gt hℓ)]
  have hdinv : ((paramsAt μ A).d)⁻¹ = fsXp t (-6) := by
    rw [d_eq_fsXp, ← ht, fsXp_inv ht0]
  have hbase : 2 * μ ^ (-1 / 3 : ℝ) / sideAt μ A = 2 * fsXp t (166 / 3) := by
    rw [show 2 * μ ^ (-1 / 3 : ℝ) / sideAt μ A
        = 2 * (μ ^ (-1 / 3 : ℝ) / sideAt μ A) by ring, hratio]
  rw [hdinv, hbase, mul_pow, fsXp_pow ht0.le, fsXp_pow ht0.le]
  have hexp : fsXp t (-6 * ↑M) * fsXp t (166 / 3 * ↑M) = fsXp t (148 * ↑M / 3) := by
    rw [fsXp_mul ht0]
    congr 1
    ring
  rw [show Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
        * fsXp t (-6 * ↑M) * (2 ^ M * fsXp t (166 / 3 * ↑M))
      = Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M * 2 ^ M
        * (fsXp t (-6 * ↑M) * fsXp t (166 / 3 * ↑M)) by ring, hexp]

/-! ## 4. The target -/

lemma bandSBudgetArith {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (K : ℝ) (hK : 0 ≤ K) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      2 * μ * (_root_.BoseGases.a v) * K
          * (MeasureTheory.volume (Work.SmallBoxSliding.bandSet
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)).toReal
          * Work.BoseFixB1.bandS (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ
        ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b
            / (2 * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 2) := by
  obtain ⟨X₀, hX₀pos, hX₀le1, hX₀K⟩ :=
    Work.BoseB7A.exists_small_rpow (e := (7207 / 969 : ℝ)) (by norm_num)
      (K := 3072 * 2 ^ 48 * (Submission.BoseGases.chiSupAbs
        * Submission.BoseGases.chiSmallDecay 48) * K)
      (mul_nonneg (mul_nonneg (by norm_num)
        (mul_nonneg Submission.BoseGases.chiSupAbs_nonneg
          (Submission.BoseGases.chiSmallDecay_nonneg 48))) hK)
  refine ⟨min X₀ 1, lt_min hX₀pos one_pos, ?_⟩
  intro μ hadm
  have hμ : 0 < μ := adm_mu_pos hadm
  have hA : 0 < a v := adm_a_pos hadm
  set t : ℝ := μ * (a v) ^ 3 with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have htε : t ≤ min X₀ 1 := by rw [ht]; exact hadm.2.1
  have ht1 : t ≤ 1 := le_trans htε (min_le_right X₀ 1)
  have htX : t ≤ X₀ := le_trans htε (min_le_left X₀ 1)
  have hℓ : 0 < sideAt μ (a v) := sideAt_pos hμ hA
  have hd : 0 < (paramsAt μ (a v)).d := by
    rw [d_eq_fsXp, ← ht]; exact fsXp_pos ht0
  -- ## the volume bound
  have hV := bandVolume_le_fsXp' (A := a v) (μ := μ) hA hμ
  rw [← ht] at hV
  -- ## `bandS` in closed form
  have hS := bandS_eq_fsXp (M := (paramsAt μ (a v)).M) (A := a v) (μ := μ) hA hμ
  rw [← ht] at hS
  have hS48 : bandS (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d μ
      = Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay 48 * 2 ^ 48
        * fsXp t 2368 := by
    rw [hS, show (paramsAt μ (a v)).M = 48 from rfl]
    norm_num
  -- ## the smallness input
  have hdd1 : (paramsAt μ (a v)).d ≤ 1 := by
    rw [d_eq_fsXp, ← ht]
    exact fsXp_le_one ht0 ht1 (by norm_num)
  have hsq : (1 + (paramsAt μ (a v)).d) ^ 2 ≤ 4 := by
    have h0 : 0 ≤ (paramsAt μ (a v)).d := le_of_lt hd
    nlinarith
  have hexpT : fsXp t (7207 / 3) = t ^ (7207 / 969 : ℝ) := by
    rw [fsXp, show (7207 / 3 : ℝ) / 323 = 7207 / 969 by norm_num]
  have hexpX : fsXp X₀ (7207 / 3) = X₀ ^ (7207 / 969 : ℝ) := by
    rw [fsXp, show (7207 / 3 : ℝ) / 323 = 7207 / 969 by norm_num]
  have hX0le : fsXp t (7207 / 3) ≤ fsXp X₀ (7207 / 3) := by
    rw [hexpT, hexpX]
    exact Real.rpow_le_rpow ht0.le htX (by norm_num)
  have hX0K' : 3072 * 2 ^ 48 * (Submission.BoseGases.chiSupAbs
        * Submission.BoseGases.chiSmallDecay 48) * K * fsXp X₀ (7207 / 3) ≤ 1 := by
    rw [hexpX]; exact hX₀K
  have hCnn : 0 ≤ 24 * 2 ^ 48 * (Submission.BoseGases.chiSupAbs
      * Submission.BoseGases.chiSmallDecay 48) * K :=
    mul_nonneg (mul_nonneg (by norm_num)
      (mul_nonneg Submission.BoseGases.chiSupAbs_nonneg
        (Submission.BoseGases.chiSmallDecay_nonneg 48))) hK
  have hstep1 : 24 * 2 ^ 48 * (Submission.BoseGases.chiSupAbs
        * Submission.BoseGases.chiSmallDecay 48) * K * fsXp t (7207 / 3) ≤ 1 / 128 := by
    have h1 : 24 * 2 ^ 48 * (Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmallDecay 48) * K * fsXp t (7207 / 3)
        ≤ 24 * 2 ^ 48 * (Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmallDecay 48) * K * fsXp X₀ (7207 / 3) :=
      mul_le_mul_of_nonneg_left hX0le hCnn
    have h3 : 128 * (24 * 2 ^ 48 * (Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmallDecay 48) * K * fsXp X₀ (7207 / 3)) ≤ 1 := by
      have heq : 128 * (24 * 2 ^ 48 * (Submission.BoseGases.chiSupAbs
            * Submission.BoseGases.chiSmallDecay 48) * K * fsXp X₀ (7207 / 3))
          = 3072 * 2 ^ 48 * (Submission.BoseGases.chiSupAbs
            * Submission.BoseGases.chiSmallDecay 48) * K * fsXp X₀ (7207 / 3) := by ring
      rw [heq]
      exact hX0K'
    linarith
  have hkey : 24 * 2 ^ 48 * (Submission.BoseGases.chiSupAbs
        * Submission.BoseGases.chiSmallDecay 48) * K * fsXp t (7207 / 3)
        * (1 + (paramsAt μ (a v)).d) ^ 2 ≤ 1 / 32 := by
    calc 24 * 2 ^ 48 * (Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmallDecay 48) * K * fsXp t (7207 / 3)
          * (1 + (paramsAt μ (a v)).d) ^ 2
        ≤ (1 / 128) * 4 := mul_le_mul hstep1 hsq (sq_nonneg _) (by norm_num)
      _ = 1 / 32 := by norm_num
  -- ## the `fsXp` bookkeeping
  have hmul1 : fsXp t (112 / 3) * fsXp t 2368 = fsXp t (7216 / 3) := by
    rw [fsXp_mul ht0]; congr 1; norm_num
  have hmul2 : fsXp t 323 * fsXp t (7216 / 3) = fsXp t (8185 / 3) := by
    rw [fsXp_mul ht0]; congr 1; norm_num
  have hmul3 : fsXp t (8185 / 3) = fsXp t 326 * fsXp t (7207 / 3) := by
    rw [show (8185 / 3 : ℝ) = 326 + 7207 / 3 by norm_num, fsXp_mul ht0]
  have hμA : μ * (a v) = ((a v)⁻¹) ^ 2 * fsXp t 323 := by
    rw [fsXp_323, ht]
    field_simp
  have hℓsq : (sideAt μ (a v)) ^ 2 = (a v) ^ 2 * fsXp t (-326) := by
    rw [sideAt_eq_fsXp hA hμ, mul_pow, fsXp_pow ht0.le]
    rw [show (-163 : ℝ) * ↑(2 : ℕ) = -326 by norm_num]
  have hb : (paramsAt μ (a v)).b = (1 / 16 : ℝ) := rfl
  have hRHS : (paramsAt μ (a v)).b / (2 * (sideAt μ (a v)) ^ 2)
      = (1 / 32) * ((a v)⁻¹) ^ 2 * fsXp t 326 := by
    rw [hb, hℓsq, ← fsXp_inv ht0 326]
    field_simp
    ring
  -- ## the chain
  have hVS : (MeasureTheory.volume (bandSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)).toReal
        * bandS (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d μ
      ≤ (12 * fsXp t (112 / 3) * (1 + (paramsAt μ (a v)).d) ^ 2)
        * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay 48 * 2 ^ 48
            * fsXp t 2368) :=
    mul_le_mul hV (le_of_eq hS48)
      (bandS_nonneg (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d μ)
      (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt (fsXp_pos ht0))) (sq_nonneg _))
  have hLHS : 2 * μ * (a v) * K
        * (MeasureTheory.volume (bandSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)).toReal
        * bandS (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d μ
      ≤ 24 * 2 ^ 48 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay 48)
          * K * (μ * (a v)) * fsXp t (7216 / 3)
          * (1 + (paramsAt μ (a v)).d) ^ 2 := by
    have h2 : 0 ≤ 2 * μ * (a v) * K := by positivity
    calc 2 * μ * (a v) * K
          * (MeasureTheory.volume (bandSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)).toReal
          * bandS (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d μ
        = (2 * μ * (a v) * K)
            * ((MeasureTheory.volume (bandSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)).toReal
                * bandS (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d μ) := by
          ring
      _ ≤ (2 * μ * (a v) * K)
            * ((12 * fsXp t (112 / 3) * (1 + (paramsAt μ (a v)).d) ^ 2)
                * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay 48
                    * 2 ^ 48 * fsXp t 2368)) :=
          mul_le_mul_of_nonneg_left hVS h2
      _ = 24 * 2 ^ 48 * (Submission.BoseGases.chiSupAbs
            * Submission.BoseGases.chiSmallDecay 48) * K * (μ * (a v))
            * (fsXp t (112 / 3) * fsXp t 2368) * (1 + (paramsAt μ (a v)).d) ^ 2 := by ring
      _ = 24 * 2 ^ 48 * (Submission.BoseGases.chiSupAbs
            * Submission.BoseGases.chiSmallDecay 48) * K * (μ * (a v)) * fsXp t (7216 / 3)
            * (1 + (paramsAt μ (a v)).d) ^ 2 := by rw [hmul1]
  have hB : 24 * 2 ^ 48 * (Submission.BoseGases.chiSupAbs
        * Submission.BoseGases.chiSmallDecay 48) * K * (μ * (a v)) * fsXp t (7216 / 3)
        * (1 + (paramsAt μ (a v)).d) ^ 2
      ≤ (paramsAt μ (a v)).b / (2 * (sideAt μ (a v)) ^ 2) := by
    rw [hRHS]
    calc 24 * 2 ^ 48 * (Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmallDecay 48) * K * (μ * (a v)) * fsXp t (7216 / 3)
          * (1 + (paramsAt μ (a v)).d) ^ 2
        = 24 * 2 ^ 48 * (Submission.BoseGases.chiSupAbs
              * Submission.BoseGases.chiSmallDecay 48) * K * ((a v)⁻¹) ^ 2
            * (fsXp t 323 * fsXp t (7216 / 3)) * (1 + (paramsAt μ (a v)).d) ^ 2 := by
          rw [hμA]; ring
      _ = 24 * 2 ^ 48 * (Submission.BoseGases.chiSupAbs
              * Submission.BoseGases.chiSmallDecay 48) * K * ((a v)⁻¹) ^ 2 * fsXp t (8185 / 3)
            * (1 + (paramsAt μ (a v)).d) ^ 2 := by rw [hmul2]
      _ = (((a v)⁻¹) ^ 2 * fsXp t 326)
            * (24 * 2 ^ 48 * (Submission.BoseGases.chiSupAbs
                * Submission.BoseGases.chiSmallDecay 48) * K * fsXp t (7207 / 3)
                * (1 + (paramsAt μ (a v)).d) ^ 2) := by
          rw [hmul3]; ring
      _ ≤ (((a v)⁻¹) ^ 2 * fsXp t 326) * (1 / 32) :=
          mul_le_mul_of_nonneg_left hkey (mul_nonneg (sq_nonneg _) (le_of_lt (fsXp_pos ht0)))
      _ = (1 / 32) * ((a v)⁻¹) ^ 2 * fsXp t 326 := by ring
  exact hLHS.trans hB

end Work.BoseFixB1
