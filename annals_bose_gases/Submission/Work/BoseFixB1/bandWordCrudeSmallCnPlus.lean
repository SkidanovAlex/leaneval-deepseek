import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.BoxCountBand
import Submission.Work.BoseFixB1.fsRegimeAt
import Submission.Work.BoseFixB1.sbWord_marginal_integrable
import Submission.Work.BoseFixB1B.bandCondensedArm
import Submission.Work.LocRepoint.bandSet_measure_le_nohyp
import Submission.Work.LocRepoint.chiSmallB_sq_integral_u
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.bandWordCrudeSmallCnPlus` — FS's per-box rough estimate on the bad band
  in the large-count / small-cushion class

## What the target is

FS `final_v2.tex` l.4083 (the rough estimate obtained from `thm:smallbox` by dropping the
non-negative bracket), restricted to the `μ ↦ 4μ` band `bandSet ℓ d μ`
(`ℓ = sideAt μ (a v)`, `d = (paramsAt μ (a v)).d`), on the class of states with

* `2·cnPlus(ℓ)(Φ) < n·‖Φ‖²`  (the *big-box* cushion `(b/2ℓ²)cnPlus(Λ)` is small), and
* `C₀/bandS M ℓ d μ < n`  (the count is above the band's `χ`-scale threshold),

for every `C₀ > 0`:

    -(C·(μ²(a v)·χ-mass(u) + μ(a v)))·‖Φ‖² ≤ sbWord h μ u Φ .

## The dichotomy used here

Write `χ = chiSmallB M ℓ d μ u` (the two-factor small-box cutoff), `Q = boxQCount` (the
localised excited count `n₊(B(u)) = cnPlusBoxInd ℓ (dlBox ℓ d μ u) (boxMass ℓ d μ u) Φ`),
`S = boxFlatCount` (the localised flat count) and `cnt = S + Q = Σᵢ∫Φ² 1_{B(u)}(xᵢ)`
(the box-indicator count; `SlabCountSplit`).

On the band `χ ≤ bandS M ℓ d μ` pointwise (`chiSmallB_le_bandS`), whence

* `occChi = chiSum ≤ bandS · cnt` (`occChi_le_bandS_count`),
* the fibre loss obeys `fibSum ≤ kav·(a v)·occChi` (`fibSum_le`), and
* the definitional gap payment `sbKin ≥ c'²μ(a v)·Q` holds for the free constant `c'`
  (`sbKin_ge_mu_av_cnPlus` + `gapRegime_of_adm`).

**Regime (A) (`Q ≥ kav·bandS·cnt`).**  Then
`sbWord = sbKin + pairSum − μ·fibSum ≥ μ(a v)Q − μ·kav·(a v)·bandS·cnt ≥ 0`, so the target's
inequality holds with *any* constant `C ≥ 0`.  This case is **proved in this file**
(`bandWordCrudeSmallCnPlus_of_largeQ`), using only `sbKin_ge_mu_av_cnPlus`, `pairSum_nonneg`,
`fibSum_le`, `occChi_le_bandS_count` and `SlabCountSplit`.

**Regime (B) (`Q < kav·bandS·cnt`, the almost-flat branch).**  This is FS §5's flat branch at
the sliding box: the pair/mean-field energy must pay the fibre line above the allowance.  It is
the single residual of this file, stated as the `sorry`-free interface
`bandWordCrudeSmallCnPlus_flatBranch` below (delegated).

The target is then the two-line case split `bandWordCrudeSmallCnPlus`.

## Status

The residual `bandWordCrudeSmallCnPlus_flatBranch` is *not* proved here.  It is the corpus's
central per-box node (`Work.BoseFixR.SlabCondensedHalf` / `Work.BoseFixB1S.PayB1` /
`Work.BoseFixB1S.flatArmSliding` / `Work.BoseFixB1B.bandFlatArm`) in this file's hypothesis
class; the refutations on record (`FINDING_bandPairManifest_FALSE.md`,
`FINDING_bandWindow_FALSE.md`, `FINDING_flatArmSlidingHole_cornerBox.md`) are all of statements
that *drop* one of the two hypotheses above (the cap state `ψ ≈ 1` off the window support has
`pairSum = fibSum = 0` and satisfies `2cnPlus < n·normB`, but no per-box constant can pay a
pair-only manifest credit for it — the target itself is fine there because the *fibre* is dead
as well).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases Work.BoseBox Work.UBB Work.BoseBoxFix
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The fibre constant of `Work.BoseFixB1.fibSum_le`
(`16π·chiSupAbs·chiSmallDecay M / smallConvLower M`). -/
noncomputable def kavConst (M : ℕ) : ℝ :=
  16 * Real.pi * chiSupAbs * chiSmallDecay M / Work.SmallBoxSliding.smallConvLower M

lemma kavConst_nonneg (M : ℕ) : 0 ≤ kavConst M := by
  rw [kavConst]
  refine div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg)
    chiSupAbs_nonneg) (chiSmallDecay_nonneg M)) ?_
  exact le_of_lt (Work.SmallBoxSliding.smallConvLower_pos M)

/-- The box-indicator count of the sliding box: `Σᵢ∫Φ² 1_{B(u)}(xᵢ)`. -/
noncomputable def boxCount {n : ℕ} (ℓ d : ℝ) (u : E3) (Φ : X n → ℝ) : ℝ :=
  ∑ i : Fin n, ∫ x in abox n ℓ, (Φ x) ^ 2 * (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i)

/-! ## Regime (A): the gap pays — proved here -/

/-- **Regime (A) of the band ledger.**  If the localised excited count `Q = boxQCount` of the
sliding box dominates `kav·bandS·cnt`, then the sliding word is *nonnegative*, so the target's
inequality holds with every constant `C ≥ 0`.

Proof: `sbWord = sbKin + pairSum − μ·fibSum` (`sbPot_split`), `pairSum ≥ 0`
(`pairSum_nonneg`), `fibSum ≤ kav·(a v)·occChi` (`fibSum_le`), `occChi ≤ bandS·cnt`
(`occChi_le_bandS_count`, band), `cnt = S + Q` (`SlabCountSplit`) and `sbKin ≥ μ(a v)Q`
(`sbKin_ge_mu_av_cnPlus` at `c' = 1`). -/
theorem sbWord_nonneg_of_largeQ {v : E3 → ℝ} {h : Work.UBB.ScatSol v}
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < a v)
    {ε₀ μ : ℝ} (hadm : Work.BoseBoxFix.Adm v ε₀ μ)
    (hreg : R ≤ sideAt μ (a v) * (paramsAt μ (a v)).d / 16)
    (hregχ : R ≤ sideAt μ (a v) * chiR0)
    (hgap : 2 * (1 + (Real.pi ^ 2)⁻¹)
        * ((paramsAt μ (a v)).d * sideAt μ (a v) * 1 * Real.sqrt (μ * a v)) ^ 2
        ≤ (paramsAt μ (a v)).eT)
    {n : ℕ} (Φ : X n → ℝ) (hΦc : Continuous Φ) {u : E3}
    (hu : u ∈ bandSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)
    (hQ : kavConst (paramsAt μ (a v)).M * bandS (paramsAt μ (a v)).M (sideAt μ (a v))
            (paramsAt μ (a v)).d μ * boxCount (sideAt μ (a v)) (paramsAt μ (a v)).d u Φ
          ≤ Work.BoseFixB1S.boxQCount (boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u)
              (sideAt μ (a v)) (dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u) Φ) :
    0 ≤ sbWord h μ u Φ := by
  have hμ : 0 < μ := adm_mu_pos hadm
  have ha : 0 ≤ a v := le_of_lt hav
  have hℓ : 0 < sideAt μ (a v) := adm_ell_pos hadm
  have hd : 0 < (paramsAt μ (a v)).d := adm_d_pos hadm
  have hM : 1 ≤ (paramsAt μ (a v)).M := M_ge_one μ (a v)
  -- the gap payment
  have hkin : μ * (a v) * Work.BoseFixB1S.boxQCount (boxMass (sideAt μ (a v))
        (paramsAt μ (a v)).d u) (sideAt μ (a v)) (dlBox (sideAt μ (a v))
        (paramsAt μ (a v)).d u) Φ
      ≤ sbKin (v := v) μ (paramsAt μ (a v)).M u Φ := by
    have h := sbKin_ge_mu_av_cnPlus (v := v) (μ := μ) (c' := 1) (M := (paramsAt μ (a v)).M)
      (u := u) (Φ := Φ) ha hμ.le (by norm_num) (by positivity) (adm_eT_pos hadm) hgap
      (tBwordKinInd_nonneg _)
    have h1 : (1 : ℝ) ^ 2 * μ * (a v)
        * Work.UBBInputs8.cnPlusBoxInd (sideAt μ (a v)) (dlBox (sideAt μ (a v))
            (paramsAt μ (a v)).d u) (boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u) Φ
        = μ * (a v) * Work.BoseFixB1S.boxQCount (boxMass (sideAt μ (a v))
            (paramsAt μ (a v)).d u) (sideAt μ (a v)) (dlBox (sideAt μ (a v))
            (paramsAt μ (a v)).d u) Φ := by
      rw [Work.BoseFixB1S.boxQCount, Work.UBBInputs8.cnPlusBoxInd]; ring
    rwa [h1] at h
  -- the fibre loss
  have hfib : fibSum h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u Φ
      ≤ kavConst (paramsAt μ (a v)).M * (a v)
          * chiSum (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u Φ := by
    have h := fibSum_le (v := v) (h := h) (R0 := R) hv hvrad hR hv_supp hM hℓ hd hreg hregχ u hΦc
    simpa only [kavConst] using h
  -- the band count bound
  have hchi : chiSum (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u Φ
      ≤ bandS (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d μ
          * boxCount (sideAt μ (a v)) (paramsAt μ (a v)).d u Φ := by
    have h := Work.BoseFixB1B.occChi_le_bandS_count (M := (paramsAt μ (a v)).M)
      (ℓ := sideAt μ (a v)) (d := (paramsAt μ (a v)).d) (μ := μ) (u := u) (n := n)
      (Φ := Φ) hM hℓ hd hμ hu hΦc
    simpa only [Work.BoseFixR.occChi, chiSum, boxCount] using h
  -- the pair is nonnegative
  have hpair : 0 ≤ pairSum v (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u Φ :=
    pairSum_nonneg (v := v) hv (M := (paramsAt μ (a v)).M) (ℓ := sideAt μ (a v))
      (d := (paramsAt μ (a v)).d) (u := u) Φ
  -- the split of the word
  have hsplit : Work.SmallBoxSliding.qLHSwordB h (paramsAt μ (a v)).M (sideAt μ (a v))
      (paramsAt μ (a v)).d μ u Φ
      = pairSum v (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u Φ
        - μ * fibSum h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u Φ := by
    have h := sbPot_split (v := v) (h := h) (R := R) hv_supp hR hv hvrad hv1 hadm hΦc u
      hreg hregχ
    rw [sbPot] at h
    linarith [h]
  have hsw : sbWord h μ u Φ
      = sbKin (v := v) μ (paramsAt μ (a v)).M u Φ
        + pairSum v (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u Φ
        - μ * fibSum h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u Φ := by
    rw [sbWord, sbPot, hsplit]
    ring
  have hchain : μ * fibSum h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u Φ
      ≤ μ * (a v) * Work.BoseFixB1S.boxQCount (boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u)
          (sideAt μ (a v)) (dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u) Φ := by
    calc μ * fibSum h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u Φ
        ≤ μ * (kavConst (paramsAt μ (a v)).M * (a v)
            * chiSum (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u Φ) :=
          mul_le_mul_of_nonneg_left hfib hμ.le
      _ ≤ μ * (kavConst (paramsAt μ (a v)).M * (a v)
            * (bandS (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d μ
                * boxCount (sideAt μ (a v)) (paramsAt μ (a v)).d u Φ)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hchi (mul_nonneg (kavConst_nonneg _) ha)) hμ.le
      _ = (μ * (a v)) * (kavConst (paramsAt μ (a v)).M * bandS (paramsAt μ (a v)).M
              (sideAt μ (a v)) (paramsAt μ (a v)).d μ
            * boxCount (sideAt μ (a v)) (paramsAt μ (a v)).d u Φ) := by ring
      _ ≤ (μ * (a v)) * Work.BoseFixB1S.boxQCount (boxMass (sideAt μ (a v))
            (paramsAt μ (a v)).d u) (sideAt μ (a v)) (dlBox (sideAt μ (a v))
            (paramsAt μ (a v)).d u) Φ :=
          mul_le_mul_of_nonneg_left hQ (mul_nonneg hμ.le ha)
      _ = μ * (a v) * Work.BoseFixB1S.boxQCount (boxMass (sideAt μ (a v))
            (paramsAt μ (a v)).d u) (sideAt μ (a v)) (dlBox (sideAt μ (a v))
            (paramsAt μ (a v)).d u) Φ := by ring
  rw [hsw]
  linarith [hchain, hkin, hpair]

/-! ## The residual: the almost-flat branch -/

/-- **The residual of this file: FS's flat branch on the band, in the target's hypothesis class.**

For states whose localised excited count `Q = boxQCount` is below `kav·bandS·cnt` (the
"almost box-flat" regime), the crude per-box bound holds on the band.

This is FS §5's flat branch at the sliding box (`Work.BoseFixR.SlabCondensedHalf`,
`Work.BoseFixB1S.PayB1`, `Work.BoseFixB1S.flatArmSliding`, `Work.BoseFixB1B.bandFlatArm`), in the
class fixed by the two hypotheses `2·cnPlus(ℓ)(Φ) < n·‖Φ‖²` and `C₀/bandS < n`.  It is the single
open input of `bandWordCrudeSmallCnPlus`. -/
theorem bandWordCrudeSmallCnPlus_flatBranch {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < a v) :
    ∀ C₀ : ℝ, 0 < C₀ → ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))),
          2 * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
            < (n : ℝ) * normB v μ n (Φ : X n → ℝ) →
          C₀ / bandS (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d μ < (n : ℝ) →
          ∀ u ∈ bandSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ,
            Work.BoseFixB1S.boxQCount (boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u)
                (sideAt μ (a v)) (dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u)
                (Φ : X n → ℝ)
              < kavConst (paramsAt μ (a v)).M * bandS (paramsAt μ (a v)).M (sideAt μ (a v))
                  (paramsAt μ (a v)).d μ * boxCount (sideAt μ (a v)) (paramsAt μ (a v)).d u
                    (Φ : X n → ℝ) →
            -(C * (μ ^ 2 * (a v)
                    * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
                  + μ * (a v)))
              * normB v μ n (Φ : X n → ℝ)
            ≤ sbWord h μ u (Φ : X n → ℝ) := by sorry

/-! ## The target -/

theorem bandWordCrudeSmallCnPlus {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∀ C₀ : ℝ, 0 < C₀ → ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          2 * Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Φ : Submission.BoseGases.X n → ℝ)
            < (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
          C₀ / Work.BoseFixB1.bandS (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ < (n : ℝ) →
          ∀ u ∈ Work.SmallBoxSliding.bandSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
            -(C * (μ ^ 2 * (_root_.BoseGases.a v)
                    * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                  + μ * (_root_.BoseGases.a v)))
              * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
            ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
  intro C₀ hC₀
  obtain ⟨ε₀F, CF, hε₀F, hCF, hF⟩ :=
    bandWordCrudeSmallCnPlus_flatBranch (v := v) h hv hv1 hvrad hR hv_supp hav C₀ hC₀
  -- the large-`Q` regime with the *same* kind of constants
  obtain ⟨ε₀r, hε₀r, hreg⟩ := regime_sideAt_ge (v := v) hav hR
  obtain ⟨ε₀g, hε₀g, hgap0⟩ := gapRegime_of_adm (v := v) hav (c' := 1) (by norm_num)
  refine ⟨min ε₀r (min ε₀g (min ε₀F 1)), max CF 0, lt_min hε₀r (lt_min hε₀g (lt_min hε₀F one_pos)),
    le_max_right _ _, ?_⟩
  intro μ hadm n Φ hcn hn u hu
  have hAdmr : Work.BoseBoxFix.Adm v ε₀r μ := Adm.mono hadm (min_le_left _ _)
  have hAdmg : Work.BoseBoxFix.Adm v ε₀g μ :=
    Adm.mono hadm (le_trans (min_le_right _ _) (min_le_left _ _))
  have hAdmF : Work.BoseBoxFix.Adm v ε₀F μ :=
    Adm.mono hadm (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  obtain ⟨hregd, hregχ⟩ := hreg μ (adm_mu_pos hAdmr) hAdmr.2.1
  have hX0 : 0 ≤ μ ^ 2 * (a v)
        * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
      + μ * (a v) :=
    add_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) (le_of_lt hav))
      (chiMass_nonneg _ _ _ _)) (mul_nonneg (adm_mu_pos hAdmr).le (le_of_lt hav))
  have hJ0 : 0 ≤ normB v μ n (Φ : X n → ℝ) := normB_nonneg _
  by_cases hcase : kavConst (paramsAt μ (a v)).M * bandS (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d μ * boxCount (sideAt μ (a v)) (paramsAt μ (a v)).d u
          (Φ : X n → ℝ)
      ≤ Work.BoseFixB1S.boxQCount (boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u)
          (sideAt μ (a v)) (dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u)
          (Φ : X n → ℝ)
  · have hword : 0 ≤ sbWord h μ u (Φ : X n → ℝ) :=
      sbWord_nonneg_of_largeQ (v := v) (h := h) hv hv1 hvrad hR hv_supp hav hAdmr hregd hregχ
        (hgap0 μ hAdmg) (Φ : X n → ℝ) Φ.contDiff.continuous hu hcase
    have hcoef : 0 ≤ max CF 0 * (μ ^ 2 * (a v)
          * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
        + μ * (a v)) * normB v μ n (Φ : X n → ℝ) :=
      mul_nonneg (mul_nonneg (le_max_right _ _) hX0) hJ0
    linarith [hword, hcoef]
  · push_neg at hcase
    have hflat := hF μ hAdmF n Φ hcn hn u hu hcase
    have hmono : CF * (μ ^ 2 * (a v)
          * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
        + μ * (a v)) * normB v μ n (Φ : X n → ℝ)
        ≤ max CF 0 * (μ ^ 2 * (a v)
            * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
          + μ * (a v)) * normB v μ n (Φ : X n → ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hX0) hJ0
    linarith [hflat, hmono]

end Work.BoseFixB1
