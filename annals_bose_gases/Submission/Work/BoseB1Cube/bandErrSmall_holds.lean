import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.CrudePlanAux
import Submission.Work.BoseFixB1.bandSBudgetArith
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.bandErrSmall_holds` — (L3) the band error is small

The lead's design for `Work.BoseB1Cube.cubeCrudeBand_holds` has three leaves; this file closes the
third, **pure parameter arithmetic** at FS's own constants (`M = mValue = 48`):

    ∀ C ≥ 0, ∃ ε₀ > 0, ∀ μ, Adm v ε₀ μ →
      C·bandErr v h μ ≤ (a v)·(K_B³·(μ(a v)³)^{1/2}) ∧ C·bandErr v h μ·K_ℓ² ≤ a v ∧ C·bandErr v h μ ≤ a v.

## The computation

With `A = a v`, `t = μA³`, `ℓ = sideAt μ A`, `d = (paramsAt μ A).d`, `M = 48`, the band error is

    bandErr v h μ = bandK v h M · (bandS M ℓ d μ)² · |bandSet ℓ d μ| .

Both factors are available in closed monomial form, **with no regime hypothesis**:

* `Work.BoseFixB1.bandVolume_le_fsXp'` — `|bandSet ℓ d μ| ≤ 12·fsXp t(112/3)·(1+d)²` (this is
  `Work.LocRepoint.bandSet_measure_le_nohyp`, the `hAδ`-free form of the band-measure bound, plus
  the `fsXp` bookkeeping `μ^{-1/3}/ℓ = fsXp t(166/3)`, `(ℓd)³ = A³fsXp t(-471)`);
* `Work.BoseFixB1.bandS_eq_fsXp` — `bandS M ℓ d μ = χ*·χM(M)·2^M·fsXp t(148M/3)`, i.e. at
  `M = 48`, `bandS = χ*·χM(48)·2⁴⁸·fsXp t 2368`.

Hence, with `κ = χ*·χM(48)·2⁴⁸` and the exponents `4736 + 112/3 = 14320/3`,

    bandErr ≤ 12·bandK v h 48·κ²·(1+d)²·fsXp t(14320/3) ≤ 48·bandK v h 48·κ²·fsXp t(14320/3) ,

the last step because `(1+d)² ≤ 4` for `t ≤ 1` (`d = t^{6/323} ≤ 1`).  So with the fixed constant
`bandErrConst v h = 48·bandK v h 48·κ²`,

    bandErr ≤ bandErrConst·t^{14320/969} ≤ bandErrConst·t^{14}   (`t ≤ 1`).

The three conclusions now follow from `t ≤ ε₀(C)` small, keeping `ε₀ ≤ 1`: taking
`ε₀ = min 1 ((A/(C·bandErrConst + 1))^{1/13})` gives `C·bandErrConst·t^{13} ≤ A`, and then

* `C·bandErr ≤ C·bandErrConst·t^{14} = (C·bandErrConst·t^{13})·t ≤ A·t ≤ A·(K_B³ t^{1/2})`
  (because `K_B³ = t^{-18/323}`, so `K_B³·t^{1/2} = t^{287/646} ≥ t`, `Work.BoseFixB1.KB3_half_eq`);
* `C·bandErr·K_ℓ² ≤ (C·bandErrConst·t^{13})·(t·K_ℓ²) ≤ A·1` (because
  `K_ℓ² = t^{-3/323}`, so `t·K_ℓ² = t^{320/323} ≤ 1`);
* `C·bandErr ≤ (C·bandErrConst·t^{13})·t ≤ A·t ≤ A`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open Work.BoseBox

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-- The fixed constant of the band-error bound:
`bandErrConst v h = 48·bandK v h 48·(χ*·χM(48)·2⁴⁸)²`. -/
noncomputable def bandErrConst (v : E3 → ℝ) (h : Work.UBB.ScatSol v) : ℝ :=
  48 * Work.BoseFixB1.bandK v h 48
    * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay 48 * 2 ^ 48) ^ 2

lemma bandErrConst_nonneg (v : E3 → ℝ) (h : Work.UBB.ScatSol v) : 0 ≤ bandErrConst v h :=
  mul_nonneg (mul_nonneg (by norm_num) (Work.BoseFixB1.bandK_nonneg 48)) (sq_nonneg _)

/-- **The band error in closed form**: `bandErr v h μ ≤ bandErrConst v h·fsXp t(14320/3)` with
`t = μ(a v)³`, for `0 < μ` and `μ(a v)³ ≤ 1` (`a v` positive).  This is the whole analytic content
of (L3): the two corpus closed forms (`bandVolume_le_fsXp'`, `bandS_eq_fsXp`) multiplied out. -/
lemma bandErr_le_fsXp {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {μ : ℝ}
    (hav : 0 < _root_.BoseGases.a v) (hμ : 0 < μ) (ht1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1) :
    CrudePlan.bandErr v h μ ≤ bandErrConst v h
      * fsXp (μ * (_root_.BoseGases.a v) ^ 3) (14320 / 3) := by
  set t : ℝ := μ * (_root_.BoseGases.a v) ^ 3 with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht1' : t ≤ 1 := by rw [ht]; exact ht1
  have hbase := Work.BoseFixB1.bandVolume_le_fsXp' (A := _root_.BoseGases.a v) (μ := μ) hav hμ
  rw [← ht] at hbase
  have hS := Work.BoseFixB1.bandS_eq_fsXp (M := (paramsAt μ (_root_.BoseGases.a v)).M)
    (A := _root_.BoseGases.a v) (μ := μ) hav hμ
  rw [← ht] at hS
  rw [show (paramsAt μ (_root_.BoseGases.a v)).M = 48 from rfl] at hS
  have hS48 : Work.BoseFixB1.bandS 48 (sideAt μ (_root_.BoseGases.a v))
      (paramsAt μ (_root_.BoseGases.a v)).d μ
      = Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay 48 * 2 ^ 48
        * fsXp t 2368 := by
    rw [hS]; norm_num
  have hd : (paramsAt μ (_root_.BoseGases.a v)).d ≤ 1 := by
    rw [Work.BoseFixB1.d_eq_fsXp, ← ht]
    exact fsXp_le_one ht0 ht1' (by norm_num)
  have hd0 : 0 ≤ (paramsAt μ (_root_.BoseGases.a v)).d := by
    rw [Work.BoseFixB1.d_eq_fsXp, ← ht]; exact (fsXp_pos ht0).le
  have hsq : (1 + (paramsAt μ (_root_.BoseGases.a v)).d) ^ 2 ≤ 4 := by nlinarith
  have hpow : (fsXp t 2368) ^ 2 * fsXp t (112 / 3) = fsXp t (14320 / 3) := by
    rw [fsXp_pow ht0.le 2368 2, fsXp_mul ht0]
    congr 1
    norm_num
  have hEq : CrudePlan.bandErr v h μ
      = Work.BoseFixB1.bandK v h 48
        * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay 48 * 2 ^ 48
            * fsXp t 2368) ^ 2
        * (volume (Work.SmallBoxSliding.bandSet (sideAt μ (_root_.BoseGases.a v))
            (paramsAt μ (_root_.BoseGases.a v)).d μ)).toReal := by
    rw [show CrudePlan.bandErr v h μ
      = Work.BoseFixB1.bandK v h (paramsAt μ (_root_.BoseGases.a v)).M
        * (Work.BoseFixB1.bandS (paramsAt μ (_root_.BoseGases.a v)).M
            (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d μ) ^ 2
        * (volume (Work.SmallBoxSliding.bandSet (sideAt μ (_root_.BoseGases.a v))
            (paramsAt μ (_root_.BoseGases.a v)).d μ)).toReal from rfl,
      show (paramsAt μ (_root_.BoseGases.a v)).M = 48 from rfl, hS48]
  rw [hEq]
  clear hS hS48 hEq
  have h2 : (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay 48 * 2 ^ 48
        * fsXp t 2368) ^ 2
      = (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay 48 * 2 ^ 48) ^ 2
        * (fsXp t 2368) ^ 2 := mul_pow _ _ 2
  have hCnn : 0 ≤ (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay 48 * 2 ^ 48) ^ 2 :=
    sq_nonneg _
  have hKnn : 0 ≤ Work.BoseFixB1.bandK v h 48 := Work.BoseFixB1.bandK_nonneg 48
  have hF14 : 0 ≤ fsXp t (14320 / 3) := (fsXp_pos ht0).le
  have hbig : (0 : ℝ) ≤ 12 * Work.BoseFixB1.bandK v h 48
      * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay 48 * 2 ^ 48) ^ 2
      * fsXp t (14320 / 3) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hKnn) hCnn) hF14
  calc Work.BoseFixB1.bandK v h 48
        * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay 48 * 2 ^ 48
            * fsXp t 2368) ^ 2
        * (volume (Work.SmallBoxSliding.bandSet (sideAt μ (_root_.BoseGases.a v))
            (paramsAt μ (_root_.BoseGases.a v)).d μ)).toReal
      = Work.BoseFixB1.bandK v h 48
          * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay 48 * 2 ^ 48) ^ 2
          * (fsXp t 2368) ^ 2
          * (volume (Work.SmallBoxSliding.bandSet (sideAt μ (_root_.BoseGases.a v))
              (paramsAt μ (_root_.BoseGases.a v)).d μ)).toReal := by rw [h2]; ring
    _ ≤ Work.BoseFixB1.bandK v h 48
          * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay 48 * 2 ^ 48) ^ 2
          * (fsXp t 2368) ^ 2
          * (12 * fsXp t (112 / 3) * (1 + (paramsAt μ (_root_.BoseGases.a v)).d) ^ 2) :=
        mul_le_mul_of_nonneg_left hbase
          (mul_nonneg (mul_nonneg hKnn hCnn) (sq_nonneg _))
    _ = 12 * Work.BoseFixB1.bandK v h 48
          * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay 48 * 2 ^ 48) ^ 2
          * fsXp t (14320 / 3) * (1 + (paramsAt μ (_root_.BoseGases.a v)).d) ^ 2 := by
        rw [← hpow]; ring
    _ ≤ 12 * Work.BoseFixB1.bandK v h 48
          * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay 48 * 2 ^ 48) ^ 2
          * fsXp t (14320 / 3) * 4 :=
        mul_le_mul_of_nonneg_left hsq hbig
    _ = bandErrConst v h * fsXp t (14320 / 3) := by
        rw [bandErrConst]; ring

/-- **(L3) The band error is small** (the lead's design for `Work.BoseB1Cube.cubeCrudeBand_holds`,
leaf 3; pure parameter arithmetic at the corpus's `M = 48 = mValue`, no analysis): for every fixed
`C ≥ 0` there is `ε₀ > 0` such that for all admissible `μ`,
`C·bandErr v h μ ≤ a v·(K_B³·(μ(a v)³)^{1/2})`, `C·bandErr·K_l² ≤ a v` and `C·bandErr ≤ a v`.

Recipe (both reviewers confirm the arithmetic, with the corrected exponents):
`bandErr v h μ = bandK·bandS²·(volume bandSet).toReal` with `bandK v h 48` a fixed real,
`bandS² = chiSupAbs²·(chiSmallDecay 48)²·d⁻⁹⁶·(2μ^{-1/3}/ℓ)⁹⁶`, so by the PROVED
`Work.BoseFixB1S.BandSizeArithB1` (`ℓ³·bandK·bandS² ≤ K·(a v)` with the exact identity
`ℓ³bandS² = chiSupAbs²·chiSmallDecay(48)²·2⁹⁶·a³·t^{4247/323}`) and the PROVED
`Work.SmallBoxSliding.bandSet_volume_le_d3` (`vol ≤ 12(1+d)²/d³`),
`bandErr ≲ K''·a v·t^{4718/323} = K''·a v·t^{14.61}`, while the three right-hand sides are
`a v·t^{287/646}/C`, `a v·t^{-3/323}/C`, `a v/C`; all three follow from `t ≤ ε₀(C)` small, keeping
`ε₀ ≤ 1` so that the `t^{4247/323} ≤ 1` smallness inputs apply.  Regime inputs
(`Work.SmallBoxSliding.bandSet_volume_le_d3`'s `hreg`, `hAδ`) come from `Adm`'s
`ParamsOK (paramsAt μ (a v)) (μa³)` and small `t`. -/
theorem bandErrSmall_holds {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) : Work.BoseB1Cube.CrudePlan.BandErrSmall v h := by
  intro C hC
  have hB0 : 0 ≤ bandErrConst v h := bandErrConst_nonneg v h
  have hCB0 : 0 ≤ C * bandErrConst v h := mul_nonneg hC hB0
  have hprodp : 0 < C * bandErrConst v h + 1 := by linarith
  have hdiv : 0 < _root_.BoseGases.a v / (C * bandErrConst v h + 1) := div_pos hav hprodp
  refine ⟨min 1 ((_root_.BoseGases.a v / (C * bandErrConst v h + 1)) ^ (1 / 13 : ℝ)),
    lt_min one_pos (Real.rpow_pos_of_pos hdiv _), ?_⟩
  intro μ hAdm
  have hμ : 0 < μ := hAdm.1
  have htε : μ * (_root_.BoseGases.a v) ^ 3
      ≤ min 1 ((_root_.BoseGases.a v / (C * bandErrConst v h + 1)) ^ (1 / 13 : ℝ)) := hAdm.2.1
  have ht1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 := le_trans htε (min_le_left _ _)
  have htε' : μ * (_root_.BoseGases.a v) ^ 3
      ≤ (_root_.BoseGases.a v / (C * bandErrConst v h + 1)) ^ (1 / 13 : ℝ) :=
    le_trans htε (min_le_right _ _)
  have ht0 : 0 < μ * (_root_.BoseGases.a v) ^ 3 := mul_pos hμ (pow_pos hav 3)
  -- the smallness threshold
  have hpow : (μ * (_root_.BoseGases.a v) ^ 3) ^ (13 : ℝ)
      ≤ _root_.BoseGases.a v / (C * bandErrConst v h + 1) := by
    have h1 := Real.rpow_le_rpow ht0.le htε' (show (0 : ℝ) ≤ 13 by norm_num)
    have h2 : ((_root_.BoseGases.a v / (C * bandErrConst v h + 1)) ^ (1 / 13 : ℝ)) ^ (13 : ℝ)
        = _root_.BoseGases.a v / (C * bandErrConst v h + 1) := by
      rw [← Real.rpow_mul hdiv.le,
        show (1 / 13 : ℝ) * 13 = 1 by norm_num, Real.rpow_one]
    linarith [h1, h2]
  have hmain : C * bandErrConst v h * (μ * (_root_.BoseGases.a v) ^ 3) ^ (13 : ℝ)
      ≤ _root_.BoseGases.a v := by
    have h1 : C * bandErrConst v h * (μ * (_root_.BoseGases.a v) ^ 3) ^ (13 : ℝ)
        ≤ C * bandErrConst v h * (_root_.BoseGases.a v / (C * bandErrConst v h + 1)) :=
      mul_le_mul_of_nonneg_left hpow hCB0
    have h2 : C * bandErrConst v h * (_root_.BoseGases.a v / (C * bandErrConst v h + 1))
        ≤ _root_.BoseGases.a v := by
      rw [mul_div_assoc', div_le_iff₀ hprodp]
      nlinarith [hav.le]
    linarith [h1, h2]
  -- the band error in `t^{14}` form
  have hbe := bandErr_le_fsXp (v := v) h hav hμ ht1
  have hfs1 : fsXp (μ * (_root_.BoseGases.a v) ^ 3) (14320 / 3)
      ≤ fsXp (μ * (_root_.BoseGases.a v) ^ 3) 4522 :=
    fsXp_le_fsXp ht0 ht1 (by norm_num)
  have hfs2 : fsXp (μ * (_root_.BoseGases.a v) ^ 3) 4522
      = (μ * (_root_.BoseGases.a v) ^ 3) ^ (14 : ℝ) := by
    rw [fsXp, show (4522 : ℝ) / 323 = 14 by norm_num]
  have hbe14 : CrudePlan.bandErr v h μ
      ≤ bandErrConst v h * (μ * (_root_.BoseGases.a v) ^ 3) ^ (14 : ℝ) := by
    calc CrudePlan.bandErr v h μ
        ≤ bandErrConst v h * fsXp (μ * (_root_.BoseGases.a v) ^ 3) (14320 / 3) := hbe
      _ ≤ bandErrConst v h * fsXp (μ * (_root_.BoseGases.a v) ^ 3) 4522 :=
          mul_le_mul_of_nonneg_left hfs1 hB0
      _ = bandErrConst v h * (μ * (_root_.BoseGases.a v) ^ 3) ^ (14 : ℝ) := by rw [hfs2]
  have hbe1 : C * CrudePlan.bandErr v h μ
      ≤ C * bandErrConst v h * (μ * (_root_.BoseGases.a v) ^ 3) ^ (14 : ℝ) := by
    calc C * CrudePlan.bandErr v h μ
        ≤ C * (bandErrConst v h * (μ * (_root_.BoseGases.a v) ^ 3) ^ (14 : ℝ)) :=
          mul_le_mul_of_nonneg_left hbe14 hC
      _ = C * bandErrConst v h * (μ * (_root_.BoseGases.a v) ^ 3) ^ (14 : ℝ) := by ring
  have ht14 : (μ * (_root_.BoseGases.a v) ^ 3) ^ (14 : ℝ)
      = (μ * (_root_.BoseGases.a v) ^ 3) ^ (13 : ℝ) * (μ * (_root_.BoseGases.a v) ^ 3) := by
    rw [show (14 : ℝ) = 13 + 1 by norm_num, Real.rpow_add ht0, Real.rpow_one]
  have hbe13 : C * bandErrConst v h * (μ * (_root_.BoseGases.a v) ^ 3) ^ (14 : ℝ)
      = (C * bandErrConst v h * (μ * (_root_.BoseGases.a v) ^ 3) ^ (13 : ℝ))
        * (μ * (_root_.BoseGases.a v) ^ 3) := by rw [ht14]; ring
  have hKl : (paramsAt μ (_root_.BoseGases.a v)).Kl ^ 2
      = fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-3) := by
    rw [Work.BoseFixB1.Kl_eq_fsXp, fsXp_pow ht0.le]
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · -- (1) the `K_B³t^{1/2}` form
    have h4 : _root_.BoseGases.a v * (μ * (_root_.BoseGases.a v) ^ 3)
        ≤ _root_.BoseGases.a v * fsXp (μ * (_root_.BoseGases.a v) ^ 3) (287 / 2) := by
      refine mul_le_mul_of_nonneg_left ?_ hav.le
      have h1 : fsXp (μ * (_root_.BoseGases.a v) ^ 3) 323
          ≤ fsXp (μ * (_root_.BoseGases.a v) ^ 3) (287 / 2) :=
        fsXp_le_fsXp ht0 ht1 (by norm_num)
      rw [Work.BoseFixB1.fsXp_323] at h1
      exact h1
    have h5 : _root_.BoseGases.a v * fsXp (μ * (_root_.BoseGases.a v) ^ 3) (287 / 2)
        = _root_.BoseGases.a v
          * ((paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)) := by
      rw [Work.BoseFixB1.KB3_half_eq hav hμ]
    calc C * CrudePlan.bandErr v h μ
        ≤ C * bandErrConst v h * (μ * (_root_.BoseGases.a v) ^ 3) ^ (14 : ℝ) := hbe1
      _ = (C * bandErrConst v h * (μ * (_root_.BoseGases.a v) ^ 3) ^ (13 : ℝ))
          * (μ * (_root_.BoseGases.a v) ^ 3) := hbe13
      _ ≤ _root_.BoseGases.a v * (μ * (_root_.BoseGases.a v) ^ 3) :=
          mul_le_mul_of_nonneg_right hmain ht0.le
      _ ≤ _root_.BoseGases.a v * fsXp (μ * (_root_.BoseGases.a v) ^ 3) (287 / 2) := h4
      _ = _root_.BoseGases.a v
          * ((paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)) := h5
  · -- (2) the `K_ℓ²` form
    rw [hKl]
    have h3 : (μ * (_root_.BoseGases.a v) ^ 3) * fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-3) ≤ 1 := by
      have hsplit : fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-3)
          = (μ * (_root_.BoseGases.a v) ^ 3) ^ ((-3 : ℝ) / 323) := by
        rw [fsXp]
      rw [hsplit]
      have hkey : (μ * (_root_.BoseGases.a v) ^ 3) * (μ * (_root_.BoseGases.a v) ^ 3) ^ ((-3 : ℝ) / 323)
          = (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 + (-3 : ℝ) / 323) := by
        rw [Real.rpow_add ht0, Real.rpow_one]
      rw [hkey]
      exact Real.rpow_le_one ht0.le ht1 (by norm_num)
    have h1 : C * CrudePlan.bandErr v h μ * fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-3)
        ≤ C * bandErrConst v h * (μ * (_root_.BoseGases.a v) ^ 3) ^ (14 : ℝ)
          * fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-3) :=
      mul_le_mul_of_nonneg_right hbe1 (fsXp_nonneg ht0.le)
    calc C * CrudePlan.bandErr v h μ * fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-3)
        ≤ C * bandErrConst v h * (μ * (_root_.BoseGases.a v) ^ 3) ^ (14 : ℝ)
            * fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-3) := h1
      _ = (C * bandErrConst v h * (μ * (_root_.BoseGases.a v) ^ 3) ^ (13 : ℝ))
            * ((μ * (_root_.BoseGases.a v) ^ 3) * fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-3)) := by
          rw [ht14]; ring
      _ ≤ (C * bandErrConst v h * (μ * (_root_.BoseGases.a v) ^ 3) ^ (13 : ℝ)) * 1 :=
          mul_le_mul_of_nonneg_left h3 (mul_nonneg hCB0 (Real.rpow_nonneg ht0.le 13))
      _ = C * bandErrConst v h * (μ * (_root_.BoseGases.a v) ^ 3) ^ (13 : ℝ) := by ring
      _ ≤ _root_.BoseGases.a v := hmain
  · -- (3) the bare form
    calc C * CrudePlan.bandErr v h μ
        ≤ C * bandErrConst v h * (μ * (_root_.BoseGases.a v) ^ 3) ^ (14 : ℝ) := hbe1
      _ = (C * bandErrConst v h * (μ * (_root_.BoseGases.a v) ^ 3) ^ (13 : ℝ))
          * (μ * (_root_.BoseGases.a v) ^ 3) := hbe13
      _ ≤ _root_.BoseGases.a v * (μ * (_root_.BoseGases.a v) ^ 3) :=
          mul_le_mul_of_nonneg_right hmain ht0.le
      _ ≤ _root_.BoseGases.a v * 1 := mul_le_mul_of_nonneg_left ht1 hav.le
      _ = _root_.BoseGases.a v := by ring

end Work.BoseB1Cube
