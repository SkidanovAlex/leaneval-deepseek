import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.pairGCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairGAssembly` — the assembly lemma of the `pairG_dir_leB` estimate

This module contains the *measure-theoretic* core of the D2 estimate: if the clean fibre `G` has
finite box-squared mass `A` and Dirichlet content `B`, then

    pairEnergy ℓ G ≤ (2·Kg + ℓ⁻²·Kc)·A + 2·Kc·B ,

where `Kg` bounds `Σ_j ‖∂_j χ_ℓ‖²` and `Kc` bounds `‖χ_ℓ‖²` (so that the product rule
`∂_j(χ_ℓ G) = (∂_jχ_ℓ)·G + χ_ℓ·∂_j G` and the elementary `(a+b)² ≤ 2a² + 2b²` close the estimate).

Also proved here: the two window bounds `Kg`, `Kc`, and the fact that the box differs from its
interior by a null set (used to transfer the pointwise derivative formula from the interior).

`sorry`-free.
-/

noncomputable section

open scoped BigOperators Topology
open MeasureTheory Filter

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn
local notation "boxL" => Work.BoseK15.corpusBox.boxL

/-- The complexified window `χ_ℓ` (the same function as `L1Tails.chiC`). -/
noncomputable def chiS (ℓ : ℝ) (x : E3) : ℂ := ((Submission.BoseGases.chiScale ℓ x : ℝ) : ℂ)

@[simp] theorem chiS_eq (ℓ : ℝ) (x : E3) :
    chiS ℓ x = ((Submission.BoseGases.chiScale ℓ x : ℝ) : ℂ) := rfl

/-- `χ_ℓ` is `C^∞` (as a `ℂ`-valued function). -/
theorem contDiff_chiS (ℓ : ℝ) (hℓ : 0 < ℓ) : ContDiff ℝ (⊤ : ℕ∞) (chiS ℓ) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (Submission.BoseGases.chiScale ℓ) :=
    Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)
  exact Complex.ofRealCLM.contDiff.comp h1

theorem hasCompactSupport_chiS (ℓ : ℝ) (hℓ : 0 < ℓ) : HasCompactSupport (chiS ℓ) := by
  have h1 : HasCompactSupport (Submission.BoseGases.chiScale ℓ) :=
    Submission.BoseGases.chiScale_hasCompactSupport (ne_of_gt hℓ)
  exact h1.comp_left (g := fun r : ℝ => ((r : ℝ) : ℂ)) (by simp)

/-- **A bound for `Σ_j ‖∂_j χ_ℓ‖²`.** -/
theorem exists_chiS_grad_bound (ℓ : ℝ) (hℓ : 0 < ℓ) :
    ∃ Kg : ℝ, 0 ≤ Kg ∧ ∀ w : E3,
      ∑ j : Fin 3, ‖fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ≤ Kg := by
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (chiS ℓ) := contDiff_chiS ℓ hℓ
  have hcs : HasCompactSupport (chiS ℓ) := hasCompactSupport_chiS ℓ hℓ
  have key : ∀ j : Fin 3, ∃ M : ℝ, 0 ≤ M ∧ ∀ w : E3,
      ‖fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))‖ ≤ M := by
    intro j
    have hcont : Continuous (fun w : E3 => fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))) :=
      (hcd.continuous_fderiv (by simp)).clm_apply continuous_const
    have hcpt : HasCompactSupport (fun w : E3 =>
        fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))) :=
      hcs.fderiv_apply ℝ (EuclideanSpace.single j (1 : ℝ))
    obtain ⟨M, hM⟩ := hcpt.exists_bound_of_continuous hcont
    exact ⟨M, le_trans (norm_nonneg _) (hM 0), fun w => hM w⟩
  choose M hM0 hM using key
  refine ⟨∑ j : Fin 3, M j ^ 2, by positivity, fun w => ?_⟩
  exact Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hM j w) 2

/-- **A bound for `‖χ_ℓ‖²`.** -/
theorem exists_chiS_bound (ℓ : ℝ) (hℓ : 0 < ℓ) :
    ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ w : E3, ‖chiS ℓ w‖ ^ 2 ≤ Kc := by
  have hcs : HasCompactSupport (Submission.BoseGases.chiScale ℓ) :=
    Submission.BoseGases.chiScale_hasCompactSupport (ne_of_gt hℓ)
  have hcont : Continuous (Submission.BoseGases.chiScale ℓ) :=
    (Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).continuous
  obtain ⟨M, hM⟩ := hcs.exists_bound_of_continuous hcont
  refine ⟨M ^ 2, by positivity, fun w => ?_⟩
  have h1 : ‖chiS ℓ w‖ = ‖Submission.BoseGases.chiScale ℓ w‖ := by
    simp [chiS]
  rw [h1]
  exact pow_le_pow_left₀ (norm_nonneg _) (hM w) 2


/-- **Parametric differentiation of `w ↦ ∫ z, Φ w z · c z`.**  A wrapper around
`hasFDerivAt_integral_of_dominated_of_fderiv_le` in the shape needed by the three row fibres: the
`w`-dependence sits in `Φ`, the factor `c` is an arbitrary bounded measurable function of `z`, and
the derivative bound is only required on a neighbourhood `s` of the base point. -/
theorem hasFDerivAt_integral_mul_const {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}
    [IsFiniteMeasure μ] {Φ : E3 → Z → ℂ} {c : Z → ℂ} {s : Set E3} {M : ℝ} {w₀ : E3}
    (hs : s ∈ 𝓝 w₀)
    (hM : ∀ᵐ z ∂μ, ∀ x ∈ s, ‖c z • fderiv ℝ (fun w' => Φ w' z) x‖ ≤ M)
    (hΦm : ∀ᶠ x in 𝓝 w₀, AEStronglyMeasurable (fun z => Φ x z * c z) μ)
    (hΦint : Integrable (fun z => Φ w₀ z * c z) μ)
    (hF'm : AEStronglyMeasurable (fun z => c z • fderiv ℝ (fun w' => Φ w' z) w₀) μ)
    (hΦd : ∀ z, ∀ x ∈ s, HasFDerivAt (fun w' => Φ w' z) (fderiv ℝ (fun w' => Φ w' z) x) x) :
    HasFDerivAt (fun w => ∫ z, Φ w z * c z ∂μ)
      (∫ z, c z • fderiv ℝ (fun w' => Φ w' z) w₀ ∂μ) w₀ := by
  have hbound_int : Integrable (fun _ : Z => M) μ := integrable_const M
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ) (𝕜 := ℝ) (E := ℂ)
    (F := fun (x : E3) (z : Z) => Φ x z * c z)
    (F' := fun (x : E3) (z : Z) => c z • fderiv ℝ (fun w' => Φ w' z) x)
    (x₀ := w₀) (bound := fun _ => M) (s := s) hs hΦm hΦint hF'm
    hM hbound_int
    (Filter.Eventually.of_forall fun z => fun x hx => (hΦd z x hx).mul_const (c z))

/-- Elementary: `(a+b)² ≤ 2a² + 2b²`. -/
private lemma sq_add_le_two (a b : ℝ) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- **The assembly lemma.**  If the fibre `G` has finite box-squared mass `A` and Dirichlet
content `B`, and the window bounds `Kg ⊇ Σ_j‖∂_jχ_ℓ‖²`, `Kc ⊇ ‖χ_ℓ‖²` hold, then the Dirichlet
energy `pairEnergy ℓ G` of the windowed fibre `χ_ℓ·G` is bounded by
`(2Kg + ℓ⁻²Kc)·A + 2Kc·B`.

The hypotheses `hIntLHS`/`hIntG`/`hIntD` are the (concrete) integrability statements of the
integrands, `hderiv` the a.e. differentiability of `G` in its first variable. -/
theorem pairEnergy_le_of_box_bounds {ℓ : ℝ} (hℓ : 0 < ℓ) {G : E3 → E3 → ℂ} {A B Kg Kc : ℝ}
    (hKg0 : 0 ≤ Kg) (hKc0 : 0 ≤ Kc) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hKg : ∀ w : E3,
      ∑ j : Fin 3, ‖fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ≤ Kg)
    (hKc : ∀ w : E3, ‖chiS ℓ w‖ ^ 2 ≤ Kc)
    (hIntLHS : IntegrableOn (fun z : E3 × E3 => ∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => chiS ℓ w' * G w' z.2) z.1 (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
          + (ℓ ^ 2)⁻¹ * ‖chiS ℓ z.1 * G z.1 z.2‖ ^ 2) (boxL ℓ ×ˢ boxL ℓ))
    (hIntG : IntegrableOn (fun z : E3 × E3 => ‖G z.1 z.2‖ ^ 2) (boxL ℓ ×ˢ boxL ℓ))
    (hIntD : IntegrableOn (fun z : E3 × E3 => ∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => G w' z.2) z.1 (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
        (boxL ℓ ×ˢ boxL ℓ))
    (hderiv : ∀ᵐ z ∂(volume.restrict (boxL ℓ ×ˢ boxL ℓ)),
        DifferentiableAt ℝ (fun w' => G w' z.2) z.1)
    (hmass : ∫ z in boxL ℓ ×ˢ boxL ℓ, ‖G z.1 z.2‖ ^ 2 ≤ A)
    (hdir : ∫ z in boxL ℓ ×ˢ boxL ℓ, ∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => G w' z.2) z.1 (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ≤ B) :
    L1Tails.pairEnergy ℓ G ≤ (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) * A + 2 * Kc * B := by
  have hchi : ∀ w : E3, DifferentiableAt ℝ (chiS ℓ) w :=
    fun w => (contDiff_chiS ℓ hℓ).differentiable (by simp) w
  set F : E3 × E3 → ℝ := fun z => ∑ j : Fin 3,
      ‖fderiv ℝ (fun w' => chiS ℓ w' * G w' z.2) z.1 (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
        + (ℓ ^ 2)⁻¹ * ‖chiS ℓ z.1 * G z.1 z.2‖ ^ 2 with hFdef
  set H : E3 × E3 → ℝ := fun z => (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) * ‖G z.1 z.2‖ ^ 2
      + 2 * Kc * (∑ j : Fin 3,
          ‖fderiv ℝ (fun w' => G w' z.2) z.1 (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) with hHdef
  have hPt : ∀ z : E3 × E3, DifferentiableAt ℝ (fun w' => G w' z.2) z.1 → F z ≤ H z := by
    rintro ⟨w, y⟩ hz
    -- a local notation for the two sums
    have hper : ∀ j : Fin 3,
        ‖fderiv ℝ (fun w' => chiS ℓ w' * G w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
          ≤ 2 * (‖chiS ℓ w‖ * ‖fderiv ℝ (fun w' => G w' y) w
                  (EuclideanSpace.single j (1 : ℝ))‖) ^ 2
            + 2 * (‖G w y‖ * ‖fderiv ℝ (chiS ℓ) w
                  (EuclideanSpace.single j (1 : ℝ))‖) ^ 2 := by
      intro j
      have hd : HasFDerivAt (fun w' => chiS ℓ w' * G w' y)
          ((chiS ℓ w) • fderiv ℝ (fun w' => G w' y) w
            + (G w y) • fderiv ℝ (chiS ℓ) w) w :=
        (hchi w).hasFDerivAt.mul hz.hasFDerivAt
      have hval : fderiv ℝ (fun w' => chiS ℓ w' * G w' y) w (EuclideanSpace.single j (1 : ℝ))
          = chiS ℓ w * fderiv ℝ (fun w' => G w' y) w (EuclideanSpace.single j (1 : ℝ))
            + G w y * fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ)) := by
        rw [hd.fderiv, add_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul]
      rw [hval]
      have h1 : ‖chiS ℓ w * fderiv ℝ (fun w' => G w' y) w (EuclideanSpace.single j (1 : ℝ))
            + G w y * fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))‖
          ≤ ‖chiS ℓ w‖ * ‖fderiv ℝ (fun w' => G w' y) w (EuclideanSpace.single j (1 : ℝ))‖
            + ‖G w y‖ * ‖fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))‖ :=
        (norm_add_le _ _).trans_eq (by rw [norm_mul, norm_mul])
      exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans (sq_add_le_two _ _)
    have hsum : ∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => chiS ℓ w' * G w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
          ≤ 2 * Kc * (∑ j : Fin 3,
              ‖fderiv ℝ (fun w' => G w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
            + 2 * Kg * ‖G w y‖ ^ 2 := by
      have hS : (0 : ℝ) ≤ ∑ j : Fin 3,
          ‖fderiv ℝ (fun w' => G w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 :=
        Finset.sum_nonneg fun j _ => by positivity
      have hT : (0 : ℝ) ≤ ∑ j : Fin 3,
          ‖fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 :=
        Finset.sum_nonneg fun j _ => by positivity
      have hG' : (0 : ℝ) ≤ ‖G w y‖ ^ 2 := by positivity
      have hsum_eq : ∑ j : Fin 3,
          (2 * (‖chiS ℓ w‖ * ‖fderiv ℝ (fun w' => G w' y) w
                (EuclideanSpace.single j (1 : ℝ))‖) ^ 2
            + 2 * (‖G w y‖ * ‖fderiv ℝ (chiS ℓ) w
                (EuclideanSpace.single j (1 : ℝ))‖) ^ 2)
          = 2 * ‖chiS ℓ w‖ ^ 2 * (∑ j : Fin 3,
                ‖fderiv ℝ (fun w' => G w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
            + 2 * ‖G w y‖ ^ 2 * (∑ j : Fin 3,
                ‖fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) := by
        rw [Finset.sum_add_distrib]
        congr 1
        · rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
        · rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      have hstep1 : 2 * ‖chiS ℓ w‖ ^ 2 * (∑ j : Fin 3,
              ‖fderiv ℝ (fun w' => G w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
            ≤ 2 * Kc * (∑ j : Fin 3,
              ‖fderiv ℝ (fun w' => G w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ hS
        linarith [hKc w]
      have hstep2 : 2 * ‖G w y‖ ^ 2 * (∑ j : Fin 3,
              ‖fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
            ≤ 2 * Kg * ‖G w y‖ ^ 2 := by
        have h1 : 2 * ‖G w y‖ ^ 2 * (∑ j : Fin 3,
              ‖fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
            ≤ 2 * ‖G w y‖ ^ 2 * Kg :=
          mul_le_mul_of_nonneg_left (hKg w) (by positivity)
        linarith [h1]
      calc ∑ j : Fin 3,
            ‖fderiv ℝ (fun w' => chiS ℓ w' * G w' y) w
              (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
          ≤ ∑ j : Fin 3, (2 * (‖chiS ℓ w‖ * ‖fderiv ℝ (fun w' => G w' y) w
                    (EuclideanSpace.single j (1 : ℝ))‖) ^ 2
                + 2 * (‖G w y‖ * ‖fderiv ℝ (chiS ℓ) w
                    (EuclideanSpace.single j (1 : ℝ))‖) ^ 2) :=
            Finset.sum_le_sum fun j _ => hper j
        _ = 2 * ‖chiS ℓ w‖ ^ 2 * (∑ j : Fin 3,
                ‖fderiv ℝ (fun w' => G w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
            + 2 * ‖G w y‖ ^ 2 * (∑ j : Fin 3,
                ‖fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) := hsum_eq
        _ ≤ 2 * Kc * (∑ j : Fin 3,
                ‖fderiv ℝ (fun w' => G w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
            + 2 * Kg * ‖G w y‖ ^ 2 := by linarith
    have hlast : (ℓ ^ 2)⁻¹ * ‖chiS ℓ w * G w y‖ ^ 2 ≤ (ℓ ^ 2)⁻¹ * Kc * ‖G w y‖ ^ 2 := by
      rw [norm_mul, mul_pow]
      have h3 : (0 : ℝ) ≤ (ℓ ^ 2)⁻¹ := by positivity
      have : ‖chiS ℓ w‖ ^ 2 * ‖G w y‖ ^ 2 ≤ Kc * ‖G w y‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (hKc w) (by positivity)
      calc (ℓ ^ 2)⁻¹ * (‖chiS ℓ w‖ ^ 2 * ‖G w y‖ ^ 2)
          = (ℓ ^ 2)⁻¹ * ‖chiS ℓ w‖ ^ 2 * ‖G w y‖ ^ 2 := by ring
        _ ≤ (ℓ ^ 2)⁻¹ * Kc * ‖G w y‖ ^ 2 := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_left (hKc w) h3
    rw [hFdef, hHdef]
    linarith
  have hAG : ∀ᵐ z ∂(volume.restrict (boxL ℓ ×ˢ boxL ℓ)), F z ≤ H z :=
    hderiv.mono fun z hz => hPt z hz
  have hF0 : ∀ᵐ z ∂(volume.restrict (boxL ℓ ×ˢ boxL ℓ)), 0 ≤ F z :=
    Filter.Eventually.of_forall fun z => by
      rw [hFdef]
      have h3 : (0 : ℝ) ≤ (ℓ ^ 2)⁻¹ := by positivity
      positivity
  have hGint : Integrable (fun z : E3 × E3 => ‖G z.1 z.2‖ ^ 2)
      (volume.restrict (boxL ℓ ×ˢ boxL ℓ)) := hIntG
  have hDint : Integrable (fun z : E3 × E3 => ∑ j : Fin 3,
      ‖fderiv ℝ (fun w' => G w' z.2) z.1 (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
      (volume.restrict (boxL ℓ ×ˢ boxL ℓ)) := hIntD
  have hHint : Integrable H (volume.restrict (boxL ℓ ×ˢ boxL ℓ)) := by
    rw [hHdef]
    exact (hGint.const_mul _).add (hDint.const_mul _)
  have hmono : ∫ z, F z ∂(volume.restrict (boxL ℓ ×ˢ boxL ℓ))
      ≤ ∫ z, H z ∂(volume.restrict (boxL ℓ ×ˢ boxL ℓ)) :=
    integral_mono_of_nonneg hF0 hHint hAG
  have hHval : (∫ z in boxL ℓ ×ˢ boxL ℓ, H z)
      = (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) * (∫ z in boxL ℓ ×ˢ boxL ℓ, ‖G z.1 z.2‖ ^ 2)
        + 2 * Kc * (∫ z in boxL ℓ ×ˢ boxL ℓ, ∑ j : Fin 3,
            ‖fderiv ℝ (fun w' => G w' z.2) z.1 (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) := by
    show (∫ z, H z ∂(volume.restrict (boxL ℓ ×ˢ boxL ℓ))) = _
    rw [show H = (fun z : E3 × E3 => (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) * ‖G z.1 z.2‖ ^ 2
        + 2 * Kc * (∑ j : Fin 3, ‖fderiv ℝ (fun w' => G w' z.2) z.1
            (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)) from hHdef]
    rw [integral_add (hGint.const_mul _) (hDint.const_mul _), integral_const_mul,
      integral_const_mul]
  have hlin' : (∫ z in boxL ℓ ×ˢ boxL ℓ, F z) = L1Tails.pairEnergy ℓ G := by
    rw [show (∫ z in boxL ℓ ×ˢ boxL ℓ, F z)
        = ∫ z in boxL ℓ ×ˢ boxL ℓ, F z ∂(volume.prod volume) from rfl]
    rw [MeasureTheory.setIntegral_prod F hIntLHS]
    unfold L1Tails.pairEnergy
    rw [hFdef]
    rfl
  have hcoef1 : 0 ≤ 2 * Kg + (ℓ ^ 2)⁻¹ * Kc := by positivity
  have hcoef2 : 0 ≤ 2 * Kc := by positivity
  have hfinal : ∫ z in boxL ℓ ×ˢ boxL ℓ, F z
      ≤ (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) * A + 2 * Kc * B := by
    calc ∫ z in boxL ℓ ×ˢ boxL ℓ, F z
        ≤ ∫ z in boxL ℓ ×ˢ boxL ℓ, H z := hmono
      _ = (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) * (∫ z in boxL ℓ ×ˢ boxL ℓ, ‖G z.1 z.2‖ ^ 2)
          + 2 * Kc * (∫ z in boxL ℓ ×ˢ boxL ℓ, ∑ j : Fin 3,
              ‖fderiv ℝ (fun w' => G w' z.2) z.1 (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) :=
          hHval
      _ ≤ (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) * A + 2 * Kc * B :=
          add_le_add (mul_le_mul_of_nonneg_left hmass hcoef1)
            (mul_le_mul_of_nonneg_left hdir hcoef2)
  rw [← hlin']
  exact hfinal

end Work.BoseBoxFock
