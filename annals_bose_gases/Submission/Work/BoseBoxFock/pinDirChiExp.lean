import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.pinDirChi_le_kinFormB
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pinDirChiExp`

The same chain as `Work.BoseBoxFock.pinDirChi_le_kinFormB`, with the whole *constant* exposed:
instead of feeding the one-body bound `chiSqGrad_le_two_dirichlet` (whose constant comes from
`Classical.choose` applied to `BSKinetic.exists_chiScale_bound` **after** the box side `l` is
fixed), the bound on the derivative of the window is taken as a hypothesis `hD`, so that the
constant of the final statement is *explicit*:

    `pinDirChi l Φ_ℂ ≤ (4 + 16·κ·chiPlateau² + 24·D²)·(kinFormB n l d s εT b Φ + n·∫_{Λ}Φ²)`

with `κ = (1−εT)(2sl)⁻² + εT(2dsl)⁻²` and `D` the given bound on `fderiv (chiScale l)`.

Contents:

* `chiSqGrad_le_two_dirichletExp` — the one-body Dirichlet bound
  `∫_{boxL}χ²Σ_j(∂_jψ)² ≤ 2·bsOneBody l (·)² 0 ψ + 6·D²·∫_{boxL}(ψ − bsMean l 0 ψ)²`,
  i.e. `chiSqGrad_le_two_dirichlet` with the constant `6·D²` from the hypothesis (the proof uses
  only `hD`, `0 ≤ D` and the pointwise product rule `chiScale_sq_mul_sum_fderiv_le`).

* `chiSqDirichletFsTExp` — the one-body bound
  `∫χ²Σ_j(∂_jψ)² ≤ C·fsT l d s εT b 0 ψ + C·∫_{boxL}ψ²` with
  `C = 4 + 16·κ·chiPlateau² + 24·D²`; the assembly of `chiSqGrad_le_two_dirichletExp`,
  `boxMeanSub_sq_integral_le`, `chiSqDirichletFsT_half_le_mainWord`,
  `chiSqDirichletFsT_mainWord_le_fsT` and `chiSqDirichletFsT_windowMass_le` — i.e. the *proof*
  of `chiSqDirichletFsT`, with no `Classical.choose` in the constant.

* `pinDirChiExp` — the slot assembly of `pinDirChi_le_kinFormB` with that explicit constant.

The chain never calls `chiSqDirichletFsT` (whose constant is a `Classical.choose` value sitting
after `l`), only its proof, replicated here with `D` in place of the chosen constant.
-/

noncomputable section

open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## 1. The one-body Dirichlet bound with the exposed derivative constant -/

/-- The product-rule integration bound of `chiSqGrad_le_two_dirichlet`, with the constant `6·D²`
of the derivative bound supplied as a hypothesis instead of being extracted from
`Work.BSKinetic.exists_chiScale_bound` (which hides a `Classical.choose` in the constant). -/
theorem chiSqGrad_le_two_dirichletExp {l D : ℝ} (hl : 0 < l) (hD0 : 0 ≤ D)
    (hD : ∀ x v : EuclideanSpace ℝ (Fin 3),
      |fderiv ℝ (Submission.BoseGases.chiScale l) x v| ≤ D * ‖v‖) :
    ∀ {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}, ContDiff ℝ (⊤ : ℕ∞) ψ →
      (∫ z in Work.BoseK15.corpusBox.boxL l,
          (Submission.BoseGases.chiScale l z) ^ 2 *
            (∑ j : Fin 3, (fderiv ℝ ψ z (EuclideanSpace.single j (1 : ℝ))) ^ 2))
        ≤ 2 * Work.BSKinetic.bsOneBody l (fun r => r ^ 2) 0 ψ
          + 6 * D ^ 2 * (∫ z in Work.BoseK15.corpusBox.boxL l,
              (ψ z - Work.BSKinetic.bsMean l 0 ψ) ^ 2) := by
  intro ψ hψ
  -- local abbreviations (all transparent for elaboration)
  let χ : EuclideanSpace ℝ (Fin 3) → ℝ := Submission.BoseGases.chiScale l
  let m : ℝ := Work.BSKinetic.bsMean l 0 ψ
  let S : Set (EuclideanSpace ℝ (Fin 3)) := Work.BoseK15.corpusBox.boxL l
  let H : EuclideanSpace ℝ (Fin 3) → ℝ := fun z =>
    ∑ j : Fin 3, (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) => χ y * (ψ y - m)) z
      (EuclideanSpace.single j (1 : ℝ))) ^ 2
  let G : EuclideanSpace ℝ (Fin 3) → ℝ := fun z => (ψ z - m) ^ 2
  have hχcd : ContDiff ℝ (⊤ : ℕ∞) χ := Submission.BoseGases.chiScale_contDiff (ne_of_gt hl)
  have hχcs : HasCompactSupport χ :=
    Submission.BoseGases.chiScale_hasCompactSupport (ne_of_gt hl)
  -- 1. the uniform bound on the squared gradient of the window
  have hgrad : ∀ z : EuclideanSpace ℝ (Fin 3),
      2 * (∑ j : Fin 3, (fderiv ℝ (Submission.BoseGases.chiScale l) z
            (EuclideanSpace.single j (1 : ℝ))) ^ 2) ≤ 6 * D ^ 2 := by
    intro z
    have hterm : ∀ j : Fin 3,
        (fderiv ℝ (Submission.BoseGases.chiScale l) z
          (EuclideanSpace.single j (1 : ℝ))) ^ 2 ≤ D ^ 2 := by
      intro j
      have h1 : |fderiv ℝ (Submission.BoseGases.chiScale l) z
          (EuclideanSpace.single j (1 : ℝ))| ≤ D := by
        have h2 := hD z (EuclideanSpace.single j (1 : ℝ))
        simpa using h2
      rw [sq_le_sq, abs_of_nonneg hD0]
      exact h1
    have hsum : (∑ j : Fin 3, (fderiv ℝ (Submission.BoseGases.chiScale l) z
          (EuclideanSpace.single j (1 : ℝ))) ^ 2) ≤ 3 * D ^ 2 := by
      calc (∑ j : Fin 3, (fderiv ℝ (Submission.BoseGases.chiScale l) z
              (EuclideanSpace.single j (1 : ℝ))) ^ 2)
          ≤ ∑ _j : Fin 3, D ^ 2 := Finset.sum_le_sum (fun j _ => hterm j)
        _ = 3 * D ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
    linarith
  -- 2. the pointwise inequality
  have hpt : ∀ z : EuclideanSpace ℝ (Fin 3),
      χ z ^ 2 * (∑ j : Fin 3, (fderiv ℝ ψ z (EuclideanSpace.single j (1 : ℝ))) ^ 2)
        ≤ 2 * H z + (6 * D ^ 2) * G z := by
    intro z
    have h1 := chiScale_sq_mul_sum_fderiv_le (ℓ := l) (m := m) hl hψ z
    have h2 : 2 * ((∑ j : Fin 3, (fderiv ℝ (Submission.BoseGases.chiScale l) z
            (EuclideanSpace.single j (1 : ℝ))) ^ 2) * (ψ z - m) ^ 2)
        ≤ (6 * D ^ 2) * (ψ z - m) ^ 2 := by
      nlinarith [hgrad z, sq_nonneg (ψ z - m)]
    have h3 : 2 * (∑ j : Fin 3, (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) =>
            Submission.BoseGases.chiScale l y * (ψ y - m)) z
            (EuclideanSpace.single j (1 : ℝ))) ^ 2)
          + 2 * ((∑ j : Fin 3, (fderiv ℝ (Submission.BoseGases.chiScale l) z
                (EuclideanSpace.single j (1 : ℝ))) ^ 2) * (ψ z - m) ^ 2)
        ≤ 2 * (∑ j : Fin 3, (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) =>
            Submission.BoseGases.chiScale l y * (ψ y - m)) z
            (EuclideanSpace.single j (1 : ℝ))) ^ 2)
          + (6 * D ^ 2) * (ψ z - m) ^ 2 :=
      add_le_add (le_refl _) h2
    exact h1.trans h3
  -- 3. continuity and integrability of the integrands
  have hQcd : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin 3) => χ y * (ψ y - m)) :=
    hχcd.mul (hψ.sub contDiff_const)
  have hQcs : HasCompactSupport (fun y : EuclideanSpace ℝ (Fin 3) => χ y * (ψ y - m)) :=
    hχcs.mul_right
  have hHcont : Continuous H :=
    continuous_finsetSum _ (fun j _ =>
      ((hQcd.continuous_fderiv (by simp)).clm_apply continuous_const).pow 2)
  have hHcs : HasCompactSupport H := by
    have hterm : ∀ v : EuclideanSpace ℝ (Fin 3),
        HasCompactSupport (fun z : EuclideanSpace ℝ (Fin 3) =>
          (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) => χ y * (ψ y - m)) z v) ^ 2) := by
      intro v
      have h1 : HasCompactSupport (fun z : EuclideanSpace ℝ (Fin 3) =>
          fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) => χ y * (ψ y - m)) z v) := by
        have h := (hQcs.fderiv ℝ).comp_left
          (g := fun L : (EuclideanSpace ℝ (Fin 3)) →L[ℝ] ℝ => L v) (by simp)
        simpa [Function.comp_def] using h
      have h2 := h1.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
      simpa [Function.comp_def] using h2
    have hsum : HasCompactSupport (∑ j : Fin 3, (fun z : EuclideanSpace ℝ (Fin 3) =>
        (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) => χ y * (ψ y - m)) z
          (EuclideanSpace.single j (1 : ℝ))) ^ 2)) := by
      rw [Fin.sum_univ_three]
      exact ((hterm (EuclideanSpace.single 0 (1 : ℝ))).add
        (hterm (EuclideanSpace.single 1 (1 : ℝ)))).add
        (hterm (EuclideanSpace.single 2 (1 : ℝ)))
    exact hsum
  have hHint : Integrable H := Continuous.integrable_of_hasCompactSupport hHcont hHcs
  have hGcont : Continuous G := (hψ.continuous.sub continuous_const).pow 2
  have hRcont : Continuous (fun z : EuclideanSpace ℝ (Fin 3) => 2 * H z + (6 * D ^ 2) * G z) :=
    (continuous_const.mul hHcont).add (continuous_const.mul hGcont)
  have hLcont : Continuous (fun z : EuclideanSpace ℝ (Fin 3) => χ z ^ 2 *
      (∑ j : Fin 3, (fderiv ℝ ψ z (EuclideanSpace.single j (1 : ℝ))) ^ 2)) :=
    (hχcd.continuous.pow 2).mul
      (continuous_finsetSum _ (fun j _ =>
        ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).pow 2))
  have hScompact : IsCompact S := by
    show IsCompact (Work.BoseK15.corpusBox.boxL l)
    rw [boxL_eq_acube hl]
    exact Submission.BoseGases.acube_compact hl
  have hLintS : IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) => χ z ^ 2 *
      (∑ j : Fin 3, (fderiv ℝ ψ z (EuclideanSpace.single j (1 : ℝ))) ^ 2)) S :=
    ContinuousOn.integrableOn_compact hScompact hLcont.continuousOn
  have hRintS : IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) => 2 * H z + (6 * D ^ 2) * G z) S :=
    ContinuousOn.integrableOn_compact hScompact hRcont.continuousOn
  have hHintS : IntegrableOn H S :=
    ContinuousOn.integrableOn_compact hScompact hHcont.continuousOn
  have hGintS : IntegrableOn G S :=
    ContinuousOn.integrableOn_compact hScompact hGcont.continuousOn
  -- 4. integration
  have hmono : (∫ z in S, χ z ^ 2 *
        (∑ j : Fin 3, (fderiv ℝ ψ z (EuclideanSpace.single j (1 : ℝ))) ^ 2))
      ≤ ∫ z in S, (2 * H z + (6 * D ^ 2) * G z) :=
    setIntegral_mono hLintS hRintS (fun z => hpt z)
  have hsplit : (∫ z in S, (2 * H z + (6 * D ^ 2) * G z))
      = 2 * (∫ z in S, H z) + (6 * D ^ 2) * (∫ z in S, G z) := by
    rw [MeasureTheory.integral_add (f := fun z : EuclideanSpace ℝ (Fin 3) => 2 * H z)
      (g := fun z : EuclideanSpace ℝ (Fin 3) => (6 * D ^ 2) * G z)
      (hHintS.const_mul 2) (hGintS.const_mul (6 * D ^ 2))]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have hHnn : 0 ≤ᵐ[volume] H :=
    ae_of_all _ (fun z => Finset.sum_nonneg (fun j _ => sq_nonneg _))
  have hHle : (∫ z in S, H z) ≤ ∫ z : EuclideanSpace ℝ (Fin 3), H z :=
    setIntegral_le_integral hHint hHnn
  have hbs : (∫ z : EuclideanSpace ℝ (Fin 3), H z)
      = Work.BSKinetic.bsOneBody l (fun r => r ^ 2) 0 ψ := by
    rw [Work.BSKinetic.bsOneBody_eq_dirichlet hl 0 ψ hψ]
    dsimp only [H, χ, m]
    apply integral_congr_ae
    filter_upwards with x
    simp only [Work.BoseBoxFock.bsWin_zero_eq_chiScale, Work.BSKinetic.bsQ,
      Submission.BoseGases.kcStdBasis]
  calc (∫ z in Work.BoseK15.corpusBox.boxL l,
          (Submission.BoseGases.chiScale l z) ^ 2 *
            (∑ j : Fin 3, (fderiv ℝ ψ z (EuclideanSpace.single j (1 : ℝ))) ^ 2))
      ≤ ∫ z in S, (2 * H z + (6 * D ^ 2) * G z) := hmono
    _ = 2 * (∫ z in S, H z) + (6 * D ^ 2) * (∫ z in S, G z) := hsplit
    _ ≤ 2 * (∫ z : EuclideanSpace ℝ (Fin 3), H z) + (6 * D ^ 2) * (∫ z in S, G z) := by
        have h2 := mul_le_mul_of_nonneg_left hHle (by norm_num : (0 : ℝ) ≤ 2)
        linarith
    _ = 2 * Work.BSKinetic.bsOneBody l (fun r => r ^ 2) 0 ψ
          + (6 * D ^ 2) * (∫ z in Work.BoseK15.corpusBox.boxL l,
              (ψ z - Work.BSKinetic.bsMean l 0 ψ) ^ 2) := by
        rw [hbs]

/-! ## 2. The `fsT` bound with the exposed derivative constant -/

/-- The windowed Dirichlet word of a smooth one-body state is dominated by the localised kinetic
word `fsT` plus the box mass, with the *explicit* constant
`4 + 16·κ·chiPlateau² + 24·D²`, `κ = (1−εT)(2sl)⁻² + εT(2dsl)⁻²`. -/
theorem chiSqDirichletFsTExp {l d s εT b D : ℝ} (hl : 0 < l) (hd : 0 < d) (hs : 0 < s)
    (hb : 0 ≤ b) (hεT0 : 0 ≤ εT) (hεT1 : εT ≤ 1) (hD0 : 0 ≤ D)
    (hD : ∀ x v : EuclideanSpace ℝ (Fin 3),
      |fderiv ℝ (Submission.BoseGases.chiScale l) x v| ≤ D * ‖v‖) :
    ∀ ψ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      (∫ z in Work.BoseK15.corpusBox.boxL l,
          (Submission.BoseGases.chiScale l z) ^ 2 *
            (∑ j : Fin 3, (fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis j)) ^ 2))
        ≤ (4 + 16 * ((1 - εT) * ((2 * (s * l))⁻¹) ^ 2 + εT * ((2 * (d * s * l))⁻¹) ^ 2)
              * Work.BoseFixB1S.chiPlateau ^ 2 + 24 * D ^ 2)
            * Work.BoseKinLoc.fsT l d s εT b 0 ψ
          + (4 + 16 * ((1 - εT) * ((2 * (s * l))⁻¹) ^ 2 + εT * ((2 * (d * s * l))⁻¹) ^ 2)
              * Work.BoseFixB1S.chiPlateau ^ 2 + 24 * D ^ 2)
            * (∫ z in Work.BoseK15.corpusBox.boxL l, (ψ z) ^ 2) := by
  intro ψ hψ
  set κ : ℝ := (1 - εT) * ((2 * (s * l))⁻¹) ^ 2 + εT * ((2 * (d * s * l))⁻¹) ^ 2 with hκdef
  set P : ℝ := Work.BoseFixB1S.chiPlateau with hPdef
  have hκnn : 0 ≤ κ := by
    rw [hκdef]
    have h1 : 0 ≤ (1 - εT) := by linarith
    nlinarith [mul_nonneg h1 (sq_nonneg ((2 * (s * l))⁻¹)),
      mul_nonneg hεT0 (sq_nonneg ((2 * (d * s * l))⁻¹))]
  have hP2 : 0 ≤ P ^ 2 := sq_nonneg P
  -- Restate the Dirichlet bound with the `kcStdBasis` spelling of the statement (the two
  -- spellings are definitionally equal, `kcStdBasis j = EuclideanSpace.single j 1`), so that
  -- the final arithmetic sees the goal's atoms syntactically.
  have hL : (∫ z in Work.BoseK15.corpusBox.boxL l,
          (Submission.BoseGases.chiScale l z) ^ 2 *
            (∑ j : Fin 3, (fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis j)) ^ 2))
        ≤ 2 * Work.BSKinetic.bsOneBody l (fun r => r ^ 2) 0 ψ
          + 6 * D ^ 2 * (∫ z in Work.BoseK15.corpusBox.boxL l,
              (ψ z - Work.BSKinetic.bsMean l 0 ψ) ^ 2) :=
    chiSqGrad_le_two_dirichletExp (l := l) (D := D) hl hD0 hD hψ
  have hVar := boxMeanSub_sq_integral_le hl hψ
  have hE := chiSqDirichletFsT_half_le_mainWord (ℓ := l) (d := d) (s := s) (εT := εT)
    hl hd hs hεT0 hεT1 hψ
  have hF := chiSqDirichletFsT_mainWord_le_fsT (ℓ := l) (d := d) (s := s) (εT := εT) (b := b)
    hl hd hs hb hεT0 hεT1 hψ
  have hM := chiSqDirichletFsT_windowMass_le (ℓ := l) hl hψ
  rw [← hκdef] at hE
  rw [← hPdef] at hM
  set S : ℝ := ∫ z in Work.BoseK15.corpusBox.boxL l, (ψ z) ^ 2 with hSdef
  set V : ℝ := ∫ z in Work.BoseK15.corpusBox.boxL l,
    (ψ z - Work.BSKinetic.bsMean l 0 ψ) ^ 2 with hVdef
  set Mb : ℝ := ∫ z : EuclideanSpace ℝ (Fin 3),
    (Work.BSKinetic.bsWin l 0 z * Work.BSKinetic.bsQ l 0 ψ z) ^ 2 with hMbdef
  set Dv : ℝ := Work.BSKinetic.bsOneBody l (fun r => r ^ 2) 0 ψ with hDvdef
  set W : ℝ := Work.BoseKinLoc.mainWord l d s εT 0 ψ with hWdef
  set T : ℝ := Work.BoseKinLoc.fsT l d s εT b 0 ψ with hTdef
  have hS0 : 0 ≤ S := by rw [hSdef]; exact integral_nonneg (fun z => sq_nonneg _)
  have hT0 : 0 ≤ T := by
    rw [hTdef]
    exact le_trans (Work.BoseKinLoc.mainWord_nonneg hεT0 hεT1 0 ψ) hF
  have h6D : 0 ≤ 6 * D ^ 2 := by nlinarith [hD0]
  have h1 : 2 * Dv + 6 * D ^ 2 * V ≤ 2 * (2 * W + 2 * κ * Mb) + 6 * D ^ 2 * (4 * S) := by
    have a : 2 * Dv ≤ 2 * (2 * W + 2 * κ * Mb) := by
      have := mul_le_mul_of_nonneg_left (by linarith [hE] : Dv ≤ 2 * W + 2 * κ * Mb)
        (by norm_num : (0 : ℝ) ≤ 2)
      linarith [this]
    have b : 6 * D ^ 2 * V ≤ 6 * D ^ 2 * (4 * S) :=
      mul_le_mul_of_nonneg_left (by linarith [hVar]) h6D
    linarith
  have h2 : 4 * W ≤ 4 * T := by linarith [hF]
  have h3 : 4 * κ * Mb ≤ 4 * κ * (P ^ 2 * V) :=
    mul_le_mul_of_nonneg_left (by linarith [hM]) (by nlinarith [hκnn])
  have h4 : 4 * κ * (P ^ 2 * V) ≤ 4 * κ * (P ^ 2 * (4 * S)) := by
    have : P ^ 2 * V ≤ P ^ 2 * (4 * S) := mul_le_mul_of_nonneg_left (by linarith [hVar]) hP2
    exact mul_le_mul_of_nonneg_left this (by nlinarith [hκnn])
  have h5 : 4 * T ≤ (4 + 16 * κ * P ^ 2 + 24 * D ^ 2) * T := by
    have hc : (0 : ℝ) ≤ 16 * κ * P ^ 2 + 24 * D ^ 2 := by nlinarith [hκnn, hP2, hD0]
    nlinarith [hT0, hc]
  have h6 : (16 * κ * P ^ 2 + 24 * D ^ 2) * S ≤ (4 + 16 * κ * P ^ 2 + 24 * D ^ 2) * S := by
    nlinarith [hS0]
  simp only [hDvdef, hWdef, hMbdef, hVdef, hSdef] at h1 h2 h3 h4
  simp only [hTdef, hSdef] at h5 h6
  linarith

/-! ## 3. The slot assembly -/

/-- The state's windowed Dirichlet content `pinDirChi` is bounded by the box kinetic word
`kinFormB` plus `n·(box mass)`, with the *explicit* constant `4 + 16·κ·chiPlateau² + 24·D²`
(where `κ = (1-εT)(2sℓ)⁻² + εT(2dsℓ)⁻²` is the two-cut-off constant of `mainWord`), and where `D`
is an explicit bound on the derivative of the window `chiScale l`, supplied as a hypothesis so that
no per-`l` `Classical.choose` can hide in the constant.

Proof recipe (copy of the chain that already exists, with `D` exposed):
* `chiSqGrad_le_two_dirichlet` (`chiSqGrad_le_two_dirichlet.lean`) is the one-body bound
  `∫_{boxL l} χ² Σ_j(∂_jψ)² ≤ 2·bsOneBody l (·)² 0 ψ + K·∫_{boxL l}(ψ − bsMean l 0 ψ)²` with
  `K = 6·D'²`, where `D'` is the per-`l` constant of `exists_chiScale_bound`; its proof only uses
  `hDbd : |fderiv (chiScale l) x v| ≤ D' * ‖v‖` (plus `0 ≤ D'`), so it goes through verbatim with
  the hypothesis `hD` and constant `6*D^2`.
* `chiSqDirichletFsT` (`chiSqDirichletFsT.lean`) then gives
  `∫ χ² Σ_j(∂_jψ)² ≤ C·fsT l d s εT b 0 ψ + C·∫_{boxL l} ψ²` with `C = 4 + 16·κ·P² + 4·K`
  (`P = chiPlateau`, `K = 6*D^2`), i.e. exactly the constant in the statement; its proof is the
  assembly of `chiSqDirichletFsT_half_le_mainWord`, `chiSqDirichletFsT_mainWord_le_fsT`,
  `chiSqDirichletFsT_windowMass_le` (`abs_chiScale_le` gives `P`), `chiSqGrad_le_two_dirichlet`
  and `boxMeanSub_sq_integral_le`.
* `pinDirChi_le_kinFormB` (`pinDirChi_le_kinFormB.lean`) is then the slot assembly: it applies the
  one-body bound to the slot fibres via `pinDirChi_slot_le` (which takes the one-body constant `C₁`
  as a *parameter*, hypothesis `h₁`) together with `pinDirChi_slot_slice`, `kinFormB_slot_fsT`,
  `mass_slice`, and the two `Finset` identifications, giving
  `pinDirChi l ↑Φ ≤ C₁ * (kinFormB n l d s εT b Φ + n * normB)`.  Copy that final assembly with
  `C₁ := 4 + 16·κ·P² + 24·D²`, and rewrite `(n : ℝ) * normB v μ n Φ` as
  `(n : ℝ) * ∫ x in abox n l, (Φ x)^2` (that is `Work.BoseBoxFix.normB`'s definition at
  `l = sideAt μ (a v)`).

WARNING: do not call `chiSqDirichletFsT` for the *constant* (its `Classical.choose` sits after `l`);
only its *proof* (with `exists_chiScale_bound`'s `D'` replaced by `D`) may be replicated. -/
theorem pinDirChiExp {n : ℕ} {l d s εT b D : ℝ}
    (hl : 0 < l) (hd : 0 < d) (hs : 0 < s) (hb : 0 ≤ b) (hεT0 : 0 ≤ εT) (hεT1 : εT ≤ 1)
    (hD0 : 0 ≤ D)
    (hD : ∀ x v : EuclideanSpace ℝ (Fin 3),
      |fderiv ℝ (Submission.BoseGases.chiScale l) x v| ≤ D * ‖v‖) :
    ∀ Φ : Work.BoseKinLoc.BoxState n l,
      Work.BoseBoxFock.pinDirChi l (fun x => ((Φ x : ℝ) : ℂ))
        ≤ (4 + 16 * ((1 - εT) * ((2 * (s * l))⁻¹) ^ 2 + εT * ((2 * (d * s * l))⁻¹) ^ 2)
              * Work.BoseFixB1S.chiPlateau ^ 2 + 24 * D ^ 2)
          * (Work.BoseKinLoc.kinFormB n l d s εT b (Φ : Submission.BoseGases.X n → ℝ)
              + (n : ℝ) * ∫ x in Submission.BoseGases.abox n l,
                  ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2) := by
  intro Φ
  set C₁ : ℝ := 4 + 16 * ((1 - εT) * ((2 * (s * l))⁻¹) ^ 2 + εT * ((2 * (d * s * l))⁻¹) ^ 2)
              * Work.BoseFixB1S.chiPlateau ^ 2 + 24 * D ^ 2 with hC₁def
  have hΦc : ContDiff ℝ (⊤ : ℕ∞) (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff
  -- the complexification of the fibre derivative
  have hcpx : ∀ (v : Submission.BoseGases.X n) (x : Submission.BoseGases.X n),
      fderiv ℝ (fun y : Submission.BoseGases.X n => ((Φ y : ℝ) : ℂ)) x v
        = ((fderiv ℝ (Φ : Submission.BoseGases.X n → ℝ) x v : ℝ) : ℂ) := by
    intro v x
    have h1 : HasFDerivAt (fun y : Submission.BoseGases.X n => ((Φ y : ℝ) : ℂ))
        ((Complex.ofRealCLM).comp (fderiv ℝ (Φ : Submission.BoseGases.X n → ℝ) x)) x :=
      Complex.ofRealCLM.hasFDerivAt.comp _
        ((hΦc.differentiable (by simp) x).hasFDerivAt)
    rw [h1.fderiv, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
  -- continuity of the slot integrands
  have hcont (i : Fin n) (j : Fin 3) : Continuous (fun x : Submission.BoseGases.X n =>
      (Submission.BoseGases.chiScale l (x i)) ^ 2 *
        ‖fderiv ℝ (fun y : Submission.BoseGases.X n => ((Φ y : ℝ) : ℂ)) x
          (Work.BoseBoxFock.slotDirVec i j)‖ ^ 2) := by
    have hfun : (fun x : Submission.BoseGases.X n =>
        (Submission.BoseGases.chiScale l (x i)) ^ 2 *
          ‖fderiv ℝ (fun y : Submission.BoseGases.X n => ((Φ y : ℝ) : ℂ)) x
            (Work.BoseBoxFock.slotDirVec i j)‖ ^ 2)
        = fun x : Submission.BoseGases.X n =>
            (Submission.BoseGases.chiScale l (x i)) ^ 2 *
              (fderiv ℝ (Φ : Submission.BoseGases.X n → ℝ) x
                (Work.BoseBoxFock.slotDirVec i j)) ^ 2 := by
      funext x
      rw [hcpx (Work.BoseBoxFock.slotDirVec i j) x, ← Complex.normSq_eq_norm_sq,
        Complex.normSq_ofReal]
      ring
    rw [hfun]
    exact (((Submission.BoseGases.chiScale_continuous l).comp (continuous_apply i)).pow 2).mul
      (((hΦc.continuous_fderiv (by simp)).clm_apply continuous_const).pow 2)
  -- `pinDirChi` splits into its slot-`(i,j)` summands
  have hpin : Work.BoseBoxFock.pinDirChi l (fun x => ((Φ x : ℝ) : ℂ))
      = ∑ i : Fin n, ∑ j : Fin 3, ∫ x in Submission.BoseGases.abox n l,
          (Submission.BoseGases.chiScale l (x i)) ^ 2 *
            ‖fderiv ℝ (fun y : Submission.BoseGases.X n => ((Φ y : ℝ) : ℂ)) x
              (Work.BoseBoxFock.slotDirVec i j)‖ ^ 2 := by
    rw [Work.BoseBoxFock.pinDirChi]
    rw [MeasureTheory.integral_finsetSum]
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [MeasureTheory.integral_finsetSum]
      exact fun j _ => Work.BoseBoxFock.integrableOn_abox_of_continuous hl (hcont i j)
    · intro i _
      exact Work.BoseBoxFock.integrableOn_abox_of_continuous hl
        (continuous_finsetSum _ (fun j _ => hcont i j))
  -- the per-slot bound
  have hslot (i : Fin n) : (∑ j : Fin 3, ∫ x in Submission.BoseGases.abox n l,
        (Submission.BoseGases.chiScale l (x i)) ^ 2 *
          ‖fderiv ℝ (fun y : Submission.BoseGases.X n => ((Φ y : ℝ) : ℂ)) x
            (Work.BoseBoxFock.slotDirVec i j)‖ ^ 2)
      ≤ C₁ * (l ^ (-3 : ℤ) * (∫ x in Submission.BoseGases.abox n l,
            Work.BoseKinLoc.indU l 0 (x i) *
              Work.BoseKinLoc.fsT l d s εT b 0
                (Work.BoseKinLoc.fibre n i (Φ : Submission.BoseGases.X n → ℝ) x))
          + (∫ x in Submission.BoseGases.abox n l,
              ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2)) :=
    pinDirChi_slot_le (ℓ := l) (d := d) (s := s) (εT := εT) (b := b)
      (Φ := (Φ : Submission.BoseGases.X n → ℝ)) hl hΦc i
      (chiSqDirichletFsTExp (l := l) (d := d) (s := s) (εT := εT) (b := b) (D := D)
        hl hd hs hb hεT0 hεT1 hD0 hD)
      (fun j => pinDirChi_slot_slice hl hΦc i j)
      (kinFormB_slot_fsT hl hΦc i).2 (kinFormB_slot_fsT hl hΦc i).1
      (mass_slice hl hΦc.continuous i)
  -- the two `Finset` identifications
  have hkinSum : (∑ i : Fin n, l ^ (-3 : ℤ) * (∫ x in Submission.BoseGases.abox n l,
        Work.BoseKinLoc.indU l 0 (x i) *
          Work.BoseKinLoc.fsT l d s εT b 0
            (Work.BoseKinLoc.fibre n i (Φ : Submission.BoseGases.X n → ℝ) x)))
      = Work.BoseKinLoc.kinFormB n l d s εT b (Φ : Submission.BoseGases.X n → ℝ) := by
    rw [Work.BoseKinLoc.kinFormB, Finset.mul_sum]
  have hmassSum : (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n l,
        ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2)
      = (n : ℝ) * ∫ x in Submission.BoseGases.abox n l,
          ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc Work.BoseBoxFock.pinDirChi l (fun x => ((Φ x : ℝ) : ℂ))
      = ∑ i : Fin n, ∑ j : Fin 3, ∫ x in Submission.BoseGases.abox n l,
          (Submission.BoseGases.chiScale l (x i)) ^ 2 *
            ‖fderiv ℝ (fun y : Submission.BoseGases.X n => ((Φ y : ℝ) : ℂ)) x
              (Work.BoseBoxFock.slotDirVec i j)‖ ^ 2 := hpin
    _ ≤ ∑ i : Fin n, C₁ * (l ^ (-3 : ℤ) * (∫ x in Submission.BoseGases.abox n l,
            Work.BoseKinLoc.indU l 0 (x i) *
              Work.BoseKinLoc.fsT l d s εT b 0
                (Work.BoseKinLoc.fibre n i (Φ : Submission.BoseGases.X n → ℝ) x))
          + (∫ x in Submission.BoseGases.abox n l,
              ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2)) :=
        Finset.sum_le_sum (fun i _ => hslot i)
    _ = C₁ * ((∑ i : Fin n, l ^ (-3 : ℤ) * (∫ x in Submission.BoseGases.abox n l,
            Work.BoseKinLoc.indU l 0 (x i) *
              Work.BoseKinLoc.fsT l d s εT b 0
                (Work.BoseKinLoc.fibre n i (Φ : Submission.BoseGases.X n → ℝ) x)))
          + (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n l,
              ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2)) := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    _ = C₁ * (Work.BoseKinLoc.kinFormB n l d s εT b (Φ : Submission.BoseGases.X n → ℝ)
          + (n : ℝ) * ∫ x in Submission.BoseGases.abox n l,
              ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2) := by
        rw [hkinSum, hmassSum]

end Work.BoseBoxFock
