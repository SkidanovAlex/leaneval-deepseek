import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixR.All.RB5FSFixAux
import Submission.Work.BoseFixR.EpsCorrArith
import Submission.Work.BoseFixR.RB5FSFixSplit
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/FarCorr.lean` — the `ε`-correction slot of the far leg

FS §9, proof of `lem:Roughbounds` (`eq:Rough2`): after the `ε`-split
`KzBogFS F E ρ = KzBogFS F (farEnv …) ρ + Σ_k ½•((ετ_k − ρε^{-1/2}a)•(n_k + n_{−k}))`
(`Work.BoseFixR.KzBogFS_split`), the *correction* term
`−Σ_k ½•((ρε^{-1/2}a)•(n_k + n_{−k}))` must be paid out of the error budget `ErrRes`.

Since each mode number operator is nonnegative (`aDag` is the adjoint of `a`) and the
`𝓜`-window bounds the total mode occupation by `16𝓜‖f‖²` (the Bessel conjunct of the
view `RViewFSAll` plus `NWindow_bp_N_le`), the correction is `≥ −16ρε^{-1/2}a𝓜‖f‖²`, and the
scalar comparison `256ρε^{-1/2}a𝓜 ≤ ErrRes` (`Work.BoseFixR.EpsCorrArith`, a pure
`Real.rpow`/`Real.sqrt` inequality that uses only `10^300 ≥ 256` and `ρ ≤ ρ+μ`) closes
the slot.

The slot is stated for the honest family `HonestBoxFam v h fc fu HM`, but every step is
generic in the datum, so the helpers below are stated for a general `FockData`/`KzDatum`.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixR.All

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox
open Work.BoseBoxFix Work.BoseBoxFock Work.BoseB7 Work.BoseB7A

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. Extractors of the corrected view -/

/-- The Bessel conjunct of `RViewFSAll`: there is `Cn ≤ 16` with
`⟨Σ_k n_k g, g⟩ ≤ Cn⟨T.N g, g⟩` for every `g`. -/
lemma farCorr_bessel {v : ℝ³ → ℝ} {h : ScatSol v} {μ : ℝ}
    (D : KzDatum) (hview : D.viewFSAll v h μ) :
    ∃ Cn : ℝ, 0 ≤ Cn ∧ Cn ≤ 16 ∧ ∀ g : D.F.H,
      D.F.bp ((∑ k : D.Mode, D.F.nOp k) g) g ≤ Cn * D.F.bp (D.T.N g) g := by
  unfold KzDatum.viewFSAll RViewFSAll at hview
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hB, -⟩ := hview
  exact hB

/-- `0 ≤ 𝓜 = E.bigM` (the view's `FSParamsView` conjunct gives `1 ≤ 𝓜`). -/
lemma farCorr_bigM_nonneg {v : ℝ³ → ℝ} {h : ScatSol v} {μ : ℝ}
    (D : KzDatum) (hview : D.viewFSAll v h μ) : 0 ≤ D.E.bigM := by
  unfold KzDatum.viewFSAll RViewFSAll at hview
  obtain ⟨hFSP, -⟩ := hview
  exact le_trans zero_le_one (Classical.choice hFSP).one_le_bigM

/-- The view pins `E.bigM` to FS's window parameter `𝓜 = bigMV v μ`. -/
lemma farCorr_bigM_eq {v : ℝ³ → ℝ} {h : ScatSol v} {μ : ℝ}
    (D : KzDatum) (hview : D.viewFSAll v h μ) : D.E.bigM = bigMV v μ := by
  unfold KzDatum.viewFSAll RViewFSAll at hview
  obtain ⟨-, -, -, -, hb, -⟩ := hview
  simpa [bigMV] using hb

/-- `0 < ℓ = ell v μ = K_ℓ (μa)^{-1/2}` at the FS parameters. -/
lemma ell_pos_far {v : ℝ³ → ℝ} {μ : ℝ} (hμ : 0 < μ) (hav : 0 < a v) :
    0 < ell v μ := by
  have hdil : 0 < dil v μ := by unfold dil; positivity
  rw [ell, sideAt]
  refine Work.BoseBox.boxSide_pos hμ hav ?_
  simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
  exact Work.BoseBox.fsXp_pos hdil

/-! ## 2. The operator identity of the correction term -/

/-- **The `ε`-correction as a scalar multiple of `Σ_k n_k`.**  The sum
`Σ_k ½•(c•(n_k + n_{−k}))` collapses, using the involution `k ↦ −k` of the mode
lattice, to the scalar multiple `c • Σ_k n_k`. -/
lemma farCorr_epsOp {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (c : ℝ) :
    (∑ k : Mode, (1 / 2 : ℝ) • (c • (F.nOp k + F.nOp (-k)))) = c • (∑ k : Mode, F.nOp k) := by
  have h1 : (∑ k : Mode, (1 / 2 : ℝ) • (c • (F.nOp k + F.nOp (-k))))
      = (c / 2) • ∑ k : Mode, (F.nOp k + F.nOp (-k)) := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl (fun k _ => by rw [smul_smul]; ring_nf)
  rw [h1, Finset.sum_add_distrib]
  have h2 : (∑ k : Mode, F.nOp (-k)) = ∑ k : Mode, F.nOp k := by
    refine Fintype.sum_equiv (Equiv.neg Mode) (fun k => F.nOp (-k)) (fun k => F.nOp k)
      (fun k => ?_)
    simp
  rw [h2, ← two_smul ℝ (∑ k : Mode, F.nOp k), smul_smul]
  norm_num

/-- The quadratic form of a scalar multiple of an operator. -/
lemma farCorr_qw_smul {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (f : F.H) (X : F.H →ₗ[ℝ] F.H) (c : ℝ) :
    F.qw f (c • X) = c * F.qw f X := by
  rw [FockData.qw, FockData.qw, LinearMap.smul_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul]

/-! ## 3. The slot -/

theorem FarCorr {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hav : 0 < BoseGases.a v) (fc fu : Work.BoseBoxFix.LowCut)
    (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ)
    {μ : ℝ} (hμ : 0 < μ)
    (hview : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFSAll v h μ)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (f : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.H)
    (hf : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.NWindow
        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM f) :
    -((1 / 16) * Work.BoseFixR.ErrRes v μ ρ)
        * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.normSq f
      ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f
          (∑ k : Work.BoseBoxFock.Lab (HM μ).N, (1 / 2 : ℝ) •
            ((-(ρ * (Work.BoseFixR.All.epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v)) •
              ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.nOp k
                + (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.nOp (-k)))) := by
  let D : KzDatum := Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ
  change -((1 / 16) * Work.BoseFixR.ErrRes v μ ρ) * D.F.normSq f
      ≤ D.F.qw f
          (∑ k : D.Mode, (1 / 2 : ℝ) •
            ((-(ρ * (Work.BoseFixR.All.epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v)) •
              (D.F.nOp k + D.F.nOp (-k))))
  -- the three inputs from the view
  obtain ⟨Cn, hCn0, hCn16, hCn⟩ := farCorr_bessel D hview
  have hM0 : 0 ≤ D.E.bigM := farCorr_bigM_nonneg D hview
  have hbigM : D.E.bigM = bigMV v μ := farCorr_bigM_eq D hview
  have hℓ : 0 < ell v μ := ell_pos_far hμ hav
  -- the scalar comparison of `ErrRes` with the correction constant
  have harith : 256 * ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * a v * bigMV v μ
      ≤ ErrRes v μ ρ :=
    EpsCorrArith hμ hav hρ hℓ
  -- the window bound on the total mode occupation
  have hwin : D.F.qw f (∑ k : D.Mode, D.F.nOp k) ≤ 16 * D.E.bigM * D.F.normSq f := by
    have hbase := nPlus_window_le D.F D.T hCn0 hM0 hCn hf
    have hns : 0 ≤ D.F.normSq f := D.F.normSq_nonneg f
    have h1 : Cn * D.E.bigM ≤ 16 * D.E.bigM := mul_le_mul_of_nonneg_right hCn16 hM0
    have h2 : Cn * D.E.bigM * D.F.normSq f ≤ 16 * D.E.bigM * D.F.normSq f :=
      mul_le_mul_of_nonneg_right h1 hns
    exact le_trans hbase h2
  -- the operator identity of the correction term
  have hval : D.F.qw f (∑ k : D.Mode,
        (1 / 2 : ℝ) • ((-(ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * a v)) •
          (D.F.nOp k + D.F.nOp (-k))))
      = (-(ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * a v)) *
          D.F.qw f (∑ k : D.Mode, D.F.nOp k) := by
    rw [farCorr_epsOp D.F _, farCorr_qw_smul D.F f]
  -- `c ≤ 0`
  have hc_le : (-(ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * a v)) ≤ 0 := by
    have hy : 0 ≤ (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_nonneg (Real.sqrt_nonneg _) _
    have hpos : 0 ≤ ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * a v :=
      mul_nonneg (mul_nonneg hρ hy) hav.le
    linarith
  have hstep1 : (-(ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * a v)) *
        (16 * D.E.bigM * D.F.normSq f)
      ≤ (-(ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * a v)) *
        D.F.qw f (∑ k : D.Mode, D.F.nOp k) :=
    mul_le_mul_of_nonpos_left hwin hc_le
  have hstep2 : -((1 / 16) * ErrRes v μ ρ) * D.F.normSq f
      ≤ (-(ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * a v)) *
        (16 * D.E.bigM * D.F.normSq f) := by
    have hns : 0 ≤ D.F.normSq f := D.F.normSq_nonneg f
    rw [hbigM]
    nlinarith [harith, hns]
  rw [hval]
  linarith [hstep1, hstep2]

end Work.BoseFixR.All
