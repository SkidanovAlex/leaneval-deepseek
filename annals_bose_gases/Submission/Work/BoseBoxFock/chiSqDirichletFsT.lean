import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.boxMeanSub_sq_integral_le
import Submission.Work.BoseBoxFock.chiSqGrad_le_two_dirichlet
import Submission.Work.BoseFixB1S.bsOneBody_fsKinCoeff_ge_mass
import Submission.Work.BoseFixB1S.fsTBumpDefs
import Submission.Work.BoseKinLoc.Word.fsT_nonneg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.chiSqDirichletFsT`

The corpus bump `χ = chiScale ℓ` (supported in the centred cube `boxL ℓ = [-ℓ/2,ℓ/2]³`) is a
*partition weight*: the windowed Dirichlet word `∫_{boxL ℓ}χ(z)²Σ_j(∂_jψ(z))²` of an arbitrary
smooth one-body state `ψ` is dominated by the localised kinetic word `fsT ℓ d s εT b 0 ψ` of FS
`eq:DefT` at the anchored box `Λ(0)`, plus the `L²` mass of `ψ` on the box:

    `∫_{boxL ℓ}χ(z)²Σ_j(∂_jψ(z))² ≤ C·fsT ℓ d s εT b 0 ψ + C·∫_{boxL ℓ}ψ(z)²`

with `C > 0` depending only on `(ℓ,d,s,εT,b)`, for every `C^∞` one-body state `ψ` (no support
condition on `ψ`).

## The chain (each input an independently verified lemma of the workspace)

* `chiSqAux.chiScale_sq_mul_sum_fderiv_le` — the pointwise product rule
  `χ(z)²Σ_j(∂_jψ)² ≤ 2Σ_j(∂_j(χ(ψ−m)))² + 2(Σ_j(∂_jχ)²)(ψ(z)−m)²` for every constant `m`.
* `chiSqGrad_le_two_dirichlet` — integrating it over the box at the box mean
  `m = bsMean ℓ 0 ψ` gives `LHS ≤ 2·bsOneBody ℓ (·)² 0 ψ + K·∫_{boxL}(ψ − bsMean ℓ 0 ψ)²` with
  a constant `K ≥ 0` uniform in `ψ` (the first term is the Dirichlet form of the windowed
  mean-free state, `BSKinetic.bsOneBody_eq_dirichlet`; the second is the bounded derivative of
  the bump).
* `boxMeanSub_sq_integral_le` — the box variance is at most four times the box mass,
  `∫_{boxL}(ψ − bsMean ℓ 0 ψ)² ≤ 4∫_{boxL}ψ²`.
* `BoseFixB1S.bsOneBody_fsKinCoeff_ge_mass` at the two cut-offs `(2sℓ)⁻¹`, `(2dsℓ)⁻¹` of
  `mainWord` gives `½·bsOneBody ℓ (·)² 0 ψ ≤ mainWord ℓ d s εT 0 ψ + κ·∫_z(bsWin ℓ 0·bsQ ℓ 0ψ)²`
  with `κ = (1−εT)(2sℓ)⁻² + εT(2dsℓ)⁻²`, i.e. the Dirichlet word is paid by the main (cut-off)
  word.  The remaining windowed mass is `∫χ²(ψ−m)² ≤ chiPlateau²∫_{boxL}(ψ−m)²`, using
  `|χ| ≤ chiPlateau` and the support of `χ`.
* the other three words of `fsT` are nonnegative (`Word.neuFrac_nonneg_of_integrableSq`,
  `gapWord_nonneg`, `momWord_nonneg`), so `mainWord ≤ fsT`.

Assembling: `LHS ≤ 4·fsT + (16κ·chiPlateau² + 4K)·∫_{boxL}ψ²`, so the constant of the target may
be taken to be `4 + 16κ·chiPlateau² + 4K > 0`.

The same assembly (with the basis vectors written as `EuclideanSpace.single j 1` rather than the
definitionally equal `kcStdBasis j`) is the theorem `Work.BoseBoxFock.chiSq_dirichlet_le_fsT` of
`Submission/Work/BoseBoxFock/chiSq_dirichlet_le_fsT.lean`; the version proved here is written out
in this file so that the node is self-contained, resting only on the four input lemmas above.
-/

namespace Work.BoseBoxFock

noncomputable section

open MeasureTheory

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The anchored window is the corpus bump**: `bsWin ℓ 0 = chiScale ℓ`. -/
theorem chiSqDirichletFsT_bsWin_zero (ℓ : ℝ) :
    Work.BSKinetic.bsWin ℓ 0 = Submission.BoseGases.chiScale ℓ :=
  bsWin_zero_eq_chiScale ℓ

/-- The localised word `fsT` dominates its main (cut-off) piece: the other three words
(`neuWord`, `gapWord`, `momWord`) are nonnegative. -/
theorem chiSqDirichletFsT_mainWord_le_fsT {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hs : 0 < s) (hb : 0 ≤ b) (hεT0 : 0 ≤ εT) (hεT1 : εT ≤ 1)
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ) :
    Work.BoseKinLoc.mainWord ℓ d s εT 0 ψ ≤ Work.BoseKinLoc.fsT ℓ d s εT b 0 ψ := by
  have hgap : 0 ≤ Work.BoseKinLoc.gapWord ℓ b 0 ψ :=
    Work.BoseKinLoc.gapWord_nonneg hb hℓ.le 0 ψ
  have hmom : 0 ≤ Work.BoseKinLoc.momWord ℓ d εT b 0 ψ :=
    Work.BoseKinLoc.momWord_nonneg hb hεT0 (by positivity : 0 ≤ d * ℓ) 0 ψ
  have hneu : 0 ≤ Work.BoseKinLoc.neuWord ℓ d εT 0 ψ := by
    have ha2 : 0 ≤ (d * ℓ) ^ (-2 : ℤ) := zpow_nonneg (by positivity) _
    have hcont : Continuous (Work.BoseKinLoc.Qfree ℓ 0 ψ) := hψ.continuous.sub continuous_const
    have hI : MeasureTheory.Integrable
        (fun z : EuclideanSpace ℝ (Fin 3) => (Work.BoseKinLoc.Qfree ℓ 0 ψ z) ^ 2)
        (MeasureTheory.volume.restrict (Work.BoseKinLoc.lamBox ℓ 0)) :=
      (ContinuousOn.integrableOn_compact
        (isCompact_closedBall (ℓ • (0 : EuclideanSpace ℝ (Fin 3))) (2 * (|ℓ| + 1)))
        (hcont.pow 2).continuousOn).mono_set
          (Work.BoseKinLoc.NeuFrac.lamBox_subset_closedBall ℓ 0)
    have hn := Work.BoseKinLoc.Word.neuFrac_nonneg_of_integrableSq (ℓ := ℓ)
      (a2 := (d * ℓ) ^ (-2 : ℤ)) ha2 0 hI
    unfold Work.BoseKinLoc.neuWord
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hεT0) ha2) hn
  rw [Work.BoseKinLoc.fsT_eq_sum]
  linarith

/-- The main (cut-off) word dominates half of the Dirichlet word `bsOneBody ℓ (·)² 0 ψ`, up to
the windowed mass term at the two cut-off constants of `mainWord`. -/
theorem chiSqDirichletFsT_half_le_mainWord {ℓ d s εT : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hs : 0 < s) (hεT0 : 0 ≤ εT) (hεT1 : εT ≤ 1)
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ) :
    (1 / 2) * Work.BSKinetic.bsOneBody ℓ (fun r => r ^ 2) 0 ψ
      ≤ Work.BoseKinLoc.mainWord ℓ d s εT 0 ψ
        + ((1 - εT) * ((2 * (s * ℓ))⁻¹) ^ 2 + εT * ((2 * (d * s * ℓ))⁻¹) ^ 2)
          * (∫ z : EuclideanSpace ℝ (Fin 3),
              (Work.BSKinetic.bsWin ℓ 0 z * Work.BSKinetic.bsQ ℓ 0 ψ z) ^ 2) := by
  have hc1 : 0 ≤ (2 * (s * ℓ))⁻¹ := by positivity
  have hc2 : 0 ≤ (2 * (d * s * ℓ))⁻¹ := by positivity
  have h1 := Work.BoseFixB1S.bsOneBody_fsKinCoeff_ge_mass (ℓ := ℓ) (c := (2 * (s * ℓ))⁻¹)
    hℓ hc1 hψ
  have h2 := Work.BoseFixB1S.bsOneBody_fsKinCoeff_ge_mass (ℓ := ℓ) (c := (2 * (d * s * ℓ))⁻¹)
    hℓ hc2 hψ
  have hm1 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 1 - εT)
  have hm2 := mul_le_mul_of_nonneg_left h2 hεT0
  have hmain : Work.BoseKinLoc.mainWord ℓ d s εT 0 ψ
      = (1 - εT) * Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹))
          0 ψ
        + εT * Work.BSKinetic.bsOneBody ℓ
            (Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹)) 0 ψ := rfl
  rw [hmain]
  linarith

/-- The windowed mean-free mass is dominated by the plateau weight times the box variance
(the window vanishes off the box, where it is bounded by `chiPlateau`). -/
theorem chiSqDirichletFsT_windowMass_le {ℓ : ℝ} (hℓ : 0 < ℓ)
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ) :
    (∫ z : EuclideanSpace ℝ (Fin 3),
        (Work.BSKinetic.bsWin ℓ 0 z * Work.BSKinetic.bsQ ℓ 0 ψ z) ^ 2)
      ≤ Work.BoseFixB1S.chiPlateau ^ 2 *
          (∫ z in Work.BoseK15.corpusBox.boxL ℓ,
            (ψ z - Work.BSKinetic.bsMean ℓ 0 ψ) ^ 2) := by
  have hχ : Work.BSKinetic.bsWin ℓ 0 = Submission.BoseGases.chiScale ℓ :=
    bsWin_zero_eq_chiScale ℓ
  have hcomp : IsCompact (Work.BoseK15.corpusBox.boxL ℓ) := by
    rw [boxL_eq_acube hℓ]
    exact Submission.BoseGases.acube_compact hℓ
  have hcontχ : Continuous (Submission.BoseGases.chiScale ℓ) :=
    Submission.BoseGases.chiScale_continuous ℓ
  have hcontQ : Continuous (fun z : EuclideanSpace ℝ (Fin 3) =>
      ψ z - Work.BSKinetic.bsMean ℓ 0 ψ) := hψ.continuous.sub continuous_const
  have hcontg : Continuous (fun z : EuclideanSpace ℝ (Fin 3) =>
      (Submission.BoseGases.chiScale ℓ z * (ψ z - Work.BSKinetic.bsMean ℓ 0 ψ)) ^ 2) :=
    (hcontχ.mul hcontQ).pow 2
  have hcontr : Continuous (fun z : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseFixB1S.chiPlateau ^ 2 * (ψ z - Work.BSKinetic.bsMean ℓ 0 ψ) ^ 2) :=
    continuous_const.mul (hcontQ.pow 2)
  have hzero : ∀ z : EuclideanSpace ℝ (Fin 3), z ∉ Work.BoseK15.corpusBox.boxL ℓ →
      (Submission.BoseGases.chiScale ℓ z * (ψ z - Work.BSKinetic.bsMean ℓ 0 ψ)) ^ 2 = 0 := by
    intro z hz
    have hz' : z ∉ Submission.BoseGases.acube ℓ := by
      rwa [← boxL_eq_acube hℓ]
    rw [Work.UBBInputs9.B.chiScale_eq_zero_of_not_mem_acube hℓ hz']
    ring
  have hstep1 : (∫ z : EuclideanSpace ℝ (Fin 3),
        (Submission.BoseGases.chiScale ℓ z * (ψ z - Work.BSKinetic.bsMean ℓ 0 ψ)) ^ 2)
      = ∫ z in Work.BoseK15.corpusBox.boxL ℓ,
          (Submission.BoseGases.chiScale ℓ z * (ψ z - Work.BSKinetic.bsMean ℓ 0 ψ)) ^ 2 :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
  have hInt1 : MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) =>
        (Submission.BoseGases.chiScale ℓ z * (ψ z - Work.BSKinetic.bsMean ℓ 0 ψ)) ^ 2)
      (MeasureTheory.volume.restrict (Work.BoseK15.corpusBox.boxL ℓ)) :=
    ContinuousOn.integrableOn_compact hcomp hcontg.continuousOn
  have hInt2 : MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseFixB1S.chiPlateau ^ 2 * (ψ z - Work.BSKinetic.bsMean ℓ 0 ψ) ^ 2)
      (MeasureTheory.volume.restrict (Work.BoseK15.corpusBox.boxL ℓ)) :=
    ContinuousOn.integrableOn_compact hcomp hcontr.continuousOn
  have hpt : ∀ z : EuclideanSpace ℝ (Fin 3),
      (Submission.BoseGases.chiScale ℓ z * (ψ z - Work.BSKinetic.bsMean ℓ 0 ψ)) ^ 2
        ≤ Work.BoseFixB1S.chiPlateau ^ 2
            * (ψ z - Work.BSKinetic.bsMean ℓ 0 ψ) ^ 2 := by
    intro z
    have habs : |Submission.BoseGases.chiScale ℓ z| ≤ Work.BoseFixB1S.chiPlateau := by
      simpa only [Work.BoseFixB1S.chiPlateau] using Submission.BoseGases.abs_chiScale_le ℓ z
    have hsq : (Submission.BoseGases.chiScale ℓ z) ^ 2 ≤ Work.BoseFixB1S.chiPlateau ^ 2 :=
      sq_le_sq' (by linarith [abs_le.mp habs |>.1]) (abs_le.mp habs |>.2)
    have := mul_le_mul_of_nonneg_right hsq (sq_nonneg (ψ z - Work.BSKinetic.bsMean ℓ 0 ψ))
    calc (Submission.BoseGases.chiScale ℓ z * (ψ z - Work.BSKinetic.bsMean ℓ 0 ψ)) ^ 2
        = (Submission.BoseGases.chiScale ℓ z) ^ 2
            * (ψ z - Work.BSKinetic.bsMean ℓ 0 ψ) ^ 2 := by ring
      _ ≤ Work.BoseFixB1S.chiPlateau ^ 2
            * (ψ z - Work.BSKinetic.bsMean ℓ 0 ψ) ^ 2 := this
  have hstep2 : (∫ z in Work.BoseK15.corpusBox.boxL ℓ,
        (Submission.BoseGases.chiScale ℓ z * (ψ z - Work.BSKinetic.bsMean ℓ 0 ψ)) ^ 2)
      ≤ ∫ z in Work.BoseK15.corpusBox.boxL ℓ,
          Work.BoseFixB1S.chiPlateau ^ 2 * (ψ z - Work.BSKinetic.bsMean ℓ 0 ψ) ^ 2 :=
    integral_mono hInt1 hInt2 hpt
  have hstep3 : (∫ z in Work.BoseK15.corpusBox.boxL ℓ,
          Work.BoseFixB1S.chiPlateau ^ 2 * (ψ z - Work.BSKinetic.bsMean ℓ 0 ψ) ^ 2)
      = Work.BoseFixB1S.chiPlateau ^ 2 *
          (∫ z in Work.BoseK15.corpusBox.boxL ℓ,
            (ψ z - Work.BSKinetic.bsMean ℓ 0 ψ) ^ 2) :=
    integral_const_mul _ _
  have hQ : Work.BSKinetic.bsQ ℓ 0 ψ
      = fun z : EuclideanSpace ℝ (Fin 3) => ψ z - Work.BSKinetic.bsMean ℓ 0 ψ := rfl
  rw [hχ, hQ]
  rw [hstep1, ← hstep3]
  exact hstep2

/-- **`chiSqDirichletFsT`**: the windowed Dirichlet word of a smooth one-body state on the box
`boxL ℓ` is dominated by the localised kinetic word `fsT ℓ d s εT b 0 ψ` plus the box mass. -/
theorem chiSqDirichletFsT {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hs : 0 < s)
    (hb : 0 ≤ b) (hεT0 : 0 ≤ εT) (hεT1 : εT ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ ψ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      (∫ z in Work.BoseK15.corpusBox.boxL ℓ,
          (Submission.BoseGases.chiScale ℓ z) ^ 2 *
            (∑ j : Fin 3, (fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis j)) ^ 2))
        ≤ C * Work.BoseKinLoc.fsT ℓ d s εT b 0 ψ
          + C * (∫ z in Work.BoseK15.corpusBox.boxL ℓ, (ψ z) ^ 2) := by
  obtain ⟨K₁, hK₁0, hK₁⟩ := chiSqGrad_le_two_dirichlet (ℓ := ℓ) hℓ
  set κ : ℝ := (1 - εT) * ((2 * (s * ℓ))⁻¹) ^ 2 + εT * ((2 * (d * s * ℓ))⁻¹) ^ 2 with hκdef
  set P : ℝ := Work.BoseFixB1S.chiPlateau with hPdef
  have hκnn : 0 ≤ κ := by
    rw [hκdef]
    have h1 : 0 ≤ (1 - εT) := by linarith
    nlinarith [mul_nonneg h1 (sq_nonneg ((2 * (s * ℓ))⁻¹)),
      mul_nonneg hεT0 (sq_nonneg ((2 * (d * s * ℓ))⁻¹))]
  have hP2 : 0 ≤ P ^ 2 := sq_nonneg P
  have hCpos : 0 < 4 + 16 * κ * P ^ 2 + 4 * K₁ := by
    have hxy : 0 ≤ 16 * κ * P ^ 2 := by
      have := mul_nonneg hκnn hP2
      linarith
    linarith
  refine ⟨4 + 16 * κ * P ^ 2 + 4 * K₁, hCpos, ?_⟩
  intro ψ hψ
  -- Restate the Dirichlet bound with the `kcStdBasis` spelling of the statement (the two
  -- spellings are definitionally equal, `kcStdBasis j = EuclideanSpace.single j 1`), so that
  -- the final arithmetic sees the goal's atoms syntactically.
  have hL : (∫ z in Work.BoseK15.corpusBox.boxL ℓ,
          (Submission.BoseGases.chiScale ℓ z) ^ 2 *
            (∑ j : Fin 3, (fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis j)) ^ 2))
        ≤ 2 * Work.BSKinetic.bsOneBody ℓ (fun r => r ^ 2) 0 ψ
          + K₁ * (∫ z in Work.BoseK15.corpusBox.boxL ℓ,
              (ψ z - Work.BSKinetic.bsMean ℓ 0 ψ) ^ 2) := hK₁ hψ
  have hVar := boxMeanSub_sq_integral_le hℓ hψ
  have hE := chiSqDirichletFsT_half_le_mainWord (ℓ := ℓ) (d := d) (s := s) (εT := εT)
    hℓ hd hs hεT0 hεT1 hψ
  have hF := chiSqDirichletFsT_mainWord_le_fsT (ℓ := ℓ) (d := d) (s := s) (εT := εT) (b := b)
    hℓ hd hs hb hεT0 hεT1 hψ
  have hM := chiSqDirichletFsT_windowMass_le (ℓ := ℓ) hℓ hψ
  rw [← hκdef] at hE
  rw [← hPdef] at hM
  set S : ℝ := ∫ z in Work.BoseK15.corpusBox.boxL ℓ, (ψ z) ^ 2 with hSdef
  set V : ℝ := ∫ z in Work.BoseK15.corpusBox.boxL ℓ,
    (ψ z - Work.BSKinetic.bsMean ℓ 0 ψ) ^ 2 with hVdef
  set M : ℝ := ∫ z : EuclideanSpace ℝ (Fin 3),
    (Work.BSKinetic.bsWin ℓ 0 z * Work.BSKinetic.bsQ ℓ 0 ψ z) ^ 2 with hMdef
  set D : ℝ := Work.BSKinetic.bsOneBody ℓ (fun r => r ^ 2) 0 ψ with hDdef
  set W : ℝ := Work.BoseKinLoc.mainWord ℓ d s εT 0 ψ with hWdef
  set T : ℝ := Work.BoseKinLoc.fsT ℓ d s εT b 0 ψ with hTdef
  have hS0 : 0 ≤ S := by rw [hSdef]; exact integral_nonneg (fun z => sq_nonneg _)
  have hT0 : 0 ≤ T := by
    rw [hTdef]
    exact le_trans (Work.BoseKinLoc.mainWord_nonneg hεT0 hεT1 0 ψ) hF
  have h1 : 2 * D + K₁ * V ≤ 2 * (2 * W + 2 * κ * M) + K₁ * (4 * S) := by
    have a : 2 * D ≤ 2 * (2 * W + 2 * κ * M) := by
      have := mul_le_mul_of_nonneg_left (by linarith [hE] : D ≤ 2 * W + 2 * κ * M)
        (by norm_num : (0:ℝ) ≤ 2)
      linarith [this]
    have b : K₁ * V ≤ K₁ * (4 * S) := mul_le_mul_of_nonneg_left (by linarith [hVar]) hK₁0
    linarith
  have h2 : 4 * W ≤ 4 * T := by linarith [hF]
  have h3 : 4 * κ * M ≤ 4 * κ * (P ^ 2 * V) :=
    mul_le_mul_of_nonneg_left (by linarith [hM]) (by nlinarith [hκnn])
  have h4 : 4 * κ * (P ^ 2 * V) ≤ 4 * κ * (P ^ 2 * (4 * S)) := by
    have : P ^ 2 * V ≤ P ^ 2 * (4 * S) := mul_le_mul_of_nonneg_left (by linarith [hVar]) hP2
    exact mul_le_mul_of_nonneg_left this (by nlinarith [hκnn])
  have h5 : 4 * T ≤ (4 + 16 * κ * P ^ 2 + 4 * K₁) * T := by
    have : (0:ℝ) ≤ 16 * κ * P ^ 2 + 4 * K₁ := by
      have := mul_nonneg hκnn hP2
      linarith
    nlinarith [hT0, this]
  have h6 : (16 * κ * P ^ 2 + 4 * K₁) * S ≤ (4 + 16 * κ * P ^ 2 + 4 * K₁) * S := by
    nlinarith [hS0]
  simp only [hDdef, hWdef, hMdef, hVdef, hSdef] at h1 h2 h3 h4
  simp only [hTdef, hSdef] at h5 h6
  linarith

end

end Work.BoseBoxFock
