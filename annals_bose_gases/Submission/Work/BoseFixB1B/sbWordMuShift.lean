import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1B.perBoxCrudeLower
import Submission.Work.BoseFixB1S.boxFibLine
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.sbWordMuShift` — the **chemical-potential shift** of the sliding word

Written by the holder of `Submission/Work/BoseFixB1B/lowState_count_leAlt.lean` — the first
(small) piece of the direct route to the band (FS `eq:badset`).

## Why

FS `eq:badset` bounds `∫_I H_B(4μ) du` and concludes for `H_B(μ)`.  The passage uses

    H_B(μ) = H_B(4μ) + 3μ·(the one-body fibre mass)  ≥  H_B(4μ) ,

i.e. the chemical-potential dependence of the box word sits *entirely* in the linear `−μ·fibSum`
term, so raising the chemical potential can only *lower* the word.  In the corpus the word family
`Work.BoseFixB1.sbWord h μ u Φ` uses the *same* `μ` for the box parameters (`sideAt μ`, `d`, `M`)
and for the chemical potential, so `H_B(4μ)` is **not** expressible in it.  This module supplies the
missing family and the shift identity:

* `Work.BoseFixB1B.sbWordAt h μ μ' u Φ` — the sliding word with the **parameters of `μ`** and the
  **chemical potential `μ'`** (so `sbWordAt h μ μ u Φ = sbWord h μ u Φ` by `rfl`);
* `Work.BoseFixB1B.qLHSwordB_mu_sub` — the exact shift identity, a one-liner from the PROVED
  `Work.BoseFixB1.qLHSwordB_split` (whose chemical potential is a *free* argument);
* `Work.BoseFixB1B.fibSum_nonneg` — the fibre mass is nonnegative
  (`Work.BoseFixB1S.boxFibLine_fibre_nonneg`, the same row the `a0`/A₂ chapter uses);
* **`Work.BoseFixB1B.sbWordAt_four_mu_le_sbWord`** — FS's `H_B(μ) ≥ H_B(4μ)`, hence any lower bound
  for `sbWordAt h μ (4μ) u Φ` is a lower bound for `sbWord h μ u Φ` (the band *and* the good-set
  estimates can therefore be run at `4μ` and transported back).

Together with the total-density `thm:smallbox` at the chemical potential `4μ`
(`Work.BoseFixB1B.PerBoxFTotal`, file `perBoxFTotalDefs.lean`, being built in parallel) this is
FS `eq:badset`'s exact structure.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.BoseBox Work.UBB

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The sliding box word at the parameters of `μ` and the chemical potential `μ'`.**  At `μ' = μ`
this is `Work.BoseFixB1.sbWord h μ u Φ` (`rfl`); at `μ' = 4μ` it is FS `eq:badset`'s `H_B(4μ)`. -/
noncomputable def sbWordAt {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (μ μ' : ℝ) {n : ℕ}
    (u : E3) (Φ : Submission.BoseGases.X n → ℝ) : ℝ :=
  Work.BoseFixB1.sbKin (v := v) μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M u Φ
    + Work.SmallBoxSliding.qLHSwordB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ' u Φ

@[simp] lemma sbWordAt_self {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ} {n : ℕ} (u : E3)
    (Φ : Submission.BoseGases.X n → ℝ) :
    sbWordAt h μ μ u Φ = Work.BoseFixB1.sbWord h μ u Φ := rfl

/-- **The chemical-potential shift identity**: the localised per-box word is *affine* in the
chemical potential, with slope `−fibSum`.  A one-liner from the PROVED
`Work.BoseFixB1.qLHSwordB_split`, whose chemical potential is a free argument. -/
theorem qLHSwordB_mu_sub {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R0) (hR0 : 0 < R0) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hR : R0 ≤ ℓ * d / 16)
    (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0) (u : E3) {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) (μ₁ μ₂ : ℝ) :
    Work.SmallBoxSliding.qLHSwordB h M ℓ d μ₁ u Φ
        - Work.SmallBoxSliding.qLHSwordB h M ℓ d μ₂ u Φ
      = - (μ₁ - μ₂) * Work.BoseFixB1.fibSum h M ℓ d u Φ := by
  rw [Work.BoseFixB1.qLHSwordB_split (v := v) hv_supp hR0 hv hvrad hv1 M hM hℓ hd hR hRχ u hΦc,
    Work.BoseFixB1.qLHSwordB_split (v := v) hv_supp hR0 hv hvrad hv1 M hM hℓ hd hR hRχ u hΦc]
  ring

/-- **The fibre mass is nonnegative** (`fibSum ≥ 0`): its integrand is `Φ²·Σᵢ w1Fibre(xᵢ)` with
both factors nonnegative (`Work.BoseFixB1S.boxFibLine_fibre_nonneg`). -/
theorem fibSum_nonneg {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R0 : ℝ} (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R0) {M : ℕ} {ℓ d : ℝ} (u : E3) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) :
    0 ≤ Work.BoseFixB1.fibSum h M ℓ d u Φ := by
  rw [Work.BoseFixB1.fibSum]
  refine integral_nonneg fun x => ?_
  refine mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => ?_)
  exact Work.BoseFixB1S.boxFibLine_fibre_nonneg hR0 hv hvrad hv_supp h u (x i)

/-- **FS's `H_B(μ) ≥ H_B(4μ)`**: the sliding word at the chemical potential `4μ` (parameters of
`μ`) is a lower bound for the word at `μ`.  Consequently *any* lower bound proved for
`sbWordAt h μ (4μ) u Φ` transports to `sbWord h μ u Φ` — which is exactly what FS `eq:badset` does
(whence the total-density `thm:smallbox` at `4μ` gives the band bound at `μ`). -/
theorem sbWordAt_four_mu_le_sbWord {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < _root_.BoseGases.a v)
    {ε₀ μ : ℝ} (hAdm : Work.BoseBoxFix.Adm v ε₀ μ) {n : ℕ}
    (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) (u : E3)
    (hR16 : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d / 16)
    (hRχ : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0) :
    sbWordAt (v := v) h μ (4 * μ) u (Φ : Submission.BoseGases.X n → ℝ)
      ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
  have hμ : 0 < μ := hAdm.1
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  have hM : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
    rw [Work.BoseFixB1.M_eq_mValue]; norm_num [Work.BoseBox.mValue]
  have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  have hshift := qLHSwordB_mu_sub (v := v) (h := h) (R0 := R) hv_supp hR hv hvrad hv1
    (M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M) hM hℓ hd hR16 hRχ u hΦc μ (4 * μ)
  have hfib := fibSum_nonneg (v := v) (h := h) (R0 := R) hR hv hvrad hv_supp
    (M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
    (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) u
    (Φ : Submission.BoseGases.X n → ℝ)
  have hsub : Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ)
      - sbWordAt (v := v) h μ (4 * μ) u (Φ : Submission.BoseGases.X n → ℝ)
      = - (μ - 4 * μ) * Work.BoseFixB1.fibSum h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
          (Φ : Submission.BoseGases.X n → ℝ) := by
    simp only [sbWordAt, Work.BoseFixB1.sbWord, Work.BoseFixB1.sbPot]
    linarith [hshift]
  have hpos : 0 ≤ (4 * μ - μ) * Work.BoseFixB1.fibSum h
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
      (Φ : Submission.BoseGases.X n → ℝ) := mul_nonneg (by linarith) hfib
  have hsub' : Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ)
      - sbWordAt (v := v) h μ (4 * μ) u (Φ : Submission.BoseGases.X n → ℝ)
      = (4 * μ - μ) * Work.BoseFixB1.fibSum h
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
          (Φ : Submission.BoseGases.X n → ℝ) := by
    rw [hsub]; ring
  linarith [hsub', hpos]

end Work.BoseFixB1B
