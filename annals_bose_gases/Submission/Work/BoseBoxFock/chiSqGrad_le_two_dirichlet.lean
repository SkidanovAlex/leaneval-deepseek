import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.bsOneBody_eq_dirichlet
import Submission.Work.BSKinetic.exists_chiScale_bound
import Submission.Work.BoseBoxFock.acubePVFacts
import Submission.Work.BoseBoxFock.chiSqAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.chiSqGrad_le_two_dirichlet`

The windowed Dirichlet word of an arbitrary smooth one-body state `ψ` is dominated by the
big-box one-body kinetic form at the symbol `F(r) = r²`, plus a *state-dependent* mass term:

    `∫_{boxL ℓ} χ(z)²·Σ_j(∂_jψ(z))²  ≤  2·bsOneBody ℓ (·)² 0 ψ  +  K·∫_{boxL ℓ}(ψ − bsMean ℓ 0 ψ)²`

for every smooth `ψ`, with a constant `K` uniform in `ψ`.

The proof is the integration of the pointwise product rule `chiSqAux.chiScale_sq_mul_sum_fderiv_le`
at the box mean `m = bsMean ℓ 0 ψ`:

* `χ(ψ−m) = bsWin ℓ 0 · bsQ ℓ 0 ψ`, so the first term is the full-space Dirichlet word
  `∫_z Σ_k (∂_k(χ·(ψ−m)))²`, which *is* `bsOneBody ℓ (·)² 0 ψ` (`bsOneBody_eq_dirichlet`); the
  passage from the box to the full space uses the non-negativity of the integrand;
* the second term carries the *bounded* factor `Σ_j(∂_jχ)²`, whose sup on all of `ℝ³` is finite
  because `χ` is smooth with compact support (`Work.BSKinetic.exists_chiScale_bound`).

Everything is Bochner-integrable: on the compact box by continuity
(`ContinuousOn.integrableOn_compact`), and on all of `ℝ³` the compactly supported pieces by
`Continuous.integrable_of_hasCompactSupport`.
-/

noncomputable section

open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false

theorem chiSqGrad_le_two_dirichlet {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}, ContDiff ℝ (⊤ : ℕ∞) ψ →
      (∫ z in Work.BoseK15.corpusBox.boxL ℓ,
          (Submission.BoseGases.chiScale ℓ z) ^ 2 *
            (∑ j : Fin 3, (fderiv ℝ ψ z (EuclideanSpace.single j (1 : ℝ))) ^ 2))
        ≤ 2 * Work.BSKinetic.bsOneBody ℓ (fun r => r ^ 2) 0 ψ
          + K * (∫ z in Work.BoseK15.corpusBox.boxL ℓ,
              (ψ z - Work.BSKinetic.bsMean ℓ 0 ψ) ^ 2) := by
  obtain ⟨C, D, hC0, hD0, hCbd, hDbd⟩ := Work.BSKinetic.exists_chiScale_bound (ne_of_gt hℓ)
  refine ⟨6 * D ^ 2, by positivity, ?_⟩
  intro ψ hψ
  -- local abbreviations (all transparent for elaboration)
  let χ : EuclideanSpace ℝ (Fin 3) → ℝ := Submission.BoseGases.chiScale ℓ
  let m : ℝ := Work.BSKinetic.bsMean ℓ 0 ψ
  let S : Set (EuclideanSpace ℝ (Fin 3)) := Work.BoseK15.corpusBox.boxL ℓ
  let H : EuclideanSpace ℝ (Fin 3) → ℝ := fun z =>
    ∑ j : Fin 3, (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) => χ y * (ψ y - m)) z
      (EuclideanSpace.single j (1 : ℝ))) ^ 2
  let G : EuclideanSpace ℝ (Fin 3) → ℝ := fun z => (ψ z - m) ^ 2
  have hχcd : ContDiff ℝ (⊤ : ℕ∞) χ := Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)
  have hχcs : HasCompactSupport χ :=
    Submission.BoseGases.chiScale_hasCompactSupport (ne_of_gt hℓ)
  -- 1. the uniform bound on the squared gradient of the window
  have hgrad : ∀ z : EuclideanSpace ℝ (Fin 3),
      2 * (∑ j : Fin 3, (fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
            (EuclideanSpace.single j (1 : ℝ))) ^ 2) ≤ 6 * D ^ 2 := by
    intro z
    have hterm : ∀ j : Fin 3,
        (fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
          (EuclideanSpace.single j (1 : ℝ))) ^ 2 ≤ D ^ 2 := by
      intro j
      have h1 : |fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
          (EuclideanSpace.single j (1 : ℝ))| ≤ D := by
        have h2 := hDbd z (EuclideanSpace.single j (1 : ℝ))
        simpa using h2
      rw [sq_le_sq, abs_of_nonneg hD0]
      exact h1
    have hsum : (∑ j : Fin 3, (fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
          (EuclideanSpace.single j (1 : ℝ))) ^ 2) ≤ 3 * D ^ 2 := by
      calc (∑ j : Fin 3, (fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
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
    have h1 := chiScale_sq_mul_sum_fderiv_le (ℓ := ℓ) (m := m) hℓ hψ z
    have h2 : 2 * ((∑ j : Fin 3, (fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
            (EuclideanSpace.single j (1 : ℝ))) ^ 2) * (ψ z - m) ^ 2)
        ≤ (6 * D ^ 2) * (ψ z - m) ^ 2 := by
      nlinarith [hgrad z, sq_nonneg (ψ z - m)]
    have h3 : 2 * (∑ j : Fin 3, (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) =>
            Submission.BoseGases.chiScale ℓ y * (ψ y - m)) z
            (EuclideanSpace.single j (1 : ℝ))) ^ 2)
          + 2 * ((∑ j : Fin 3, (fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
                (EuclideanSpace.single j (1 : ℝ))) ^ 2) * (ψ z - m) ^ 2)
        ≤ 2 * (∑ j : Fin 3, (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) =>
            Submission.BoseGases.chiScale ℓ y * (ψ y - m)) z
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
    show IsCompact (Work.BoseK15.corpusBox.boxL ℓ)
    rw [boxL_eq_acube hℓ]
    exact Submission.BoseGases.acube_compact hℓ
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
      = Work.BSKinetic.bsOneBody ℓ (fun r => r ^ 2) 0 ψ := by
    rw [Work.BSKinetic.bsOneBody_eq_dirichlet hℓ 0 ψ hψ]
    dsimp only [H, χ, m]
    apply integral_congr_ae
    filter_upwards with x
    simp only [Work.BoseBoxFock.bsWin_zero_eq_chiScale, Work.BSKinetic.bsQ,
      Submission.BoseGases.kcStdBasis]
  calc (∫ z in Work.BoseK15.corpusBox.boxL ℓ,
          (Submission.BoseGases.chiScale ℓ z) ^ 2 *
            (∑ j : Fin 3, (fderiv ℝ ψ z (EuclideanSpace.single j (1 : ℝ))) ^ 2))
      ≤ ∫ z in S, (2 * H z + (6 * D ^ 2) * G z) := hmono
    _ = 2 * (∫ z in S, H z) + (6 * D ^ 2) * (∫ z in S, G z) := hsplit
    _ ≤ 2 * (∫ z : EuclideanSpace ℝ (Fin 3), H z) + (6 * D ^ 2) * (∫ z in S, G z) := by
        have h2 := mul_le_mul_of_nonneg_left hHle (by norm_num : (0 : ℝ) ≤ 2)
        linarith
    _ = 2 * Work.BSKinetic.bsOneBody ℓ (fun r => r ^ 2) 0 ψ
          + (6 * D ^ 2) * (∫ z in Work.BoseK15.corpusBox.boxL ℓ,
              (ψ z - Work.BSKinetic.bsMean ℓ 0 ψ) ^ 2) := by
        rw [hbs]

end Work.BoseBoxFock
