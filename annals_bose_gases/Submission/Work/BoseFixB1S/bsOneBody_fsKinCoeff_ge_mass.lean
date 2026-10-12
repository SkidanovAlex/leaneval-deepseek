import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Decomp.integrable_fsKinCoeff_mul_bsPsi_sq
import Submission.Work.BoseFixB3.HighMassAux.parseval_L1L2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The cutoff kinetic symbol `[r−c]₊²` dominates `½r² − c²`

`Work.BoseFixB1S.bsOneBody_fsKinCoeff_ge_mass`: for a smooth one-body state `ψ` and `ℓ > 0`,
`c ≥ 0`,

    `½·bsOneBody ℓ (·)² 0 ψ − c²·∫_z (bsWin ℓ 0 z · bsQ ℓ 0 ψ z)²
        ≤ bsOneBody ℓ (fsKinCoeff c) 0 ψ`,

i.e. the `[√−Δ − c]₊²` spectral word at the anchored moving box `Λ(0)` dominates **half** of the
Dirichlet word of the localised state, minus the mass term `c²‖χ₀Q₀ψ‖²`.  This is the one-body
"symbol bound" that lets a cutoff kinetic term pay for a Dirichlet form (FS Fournais–Solovej,
*The energy of dilute Bose gases*, `lem:LocKinEn`/`eq:DefT`).

## The mathematics

Write `g := bsWin ℓ 0 · bsQ ℓ 0 ψ` (smooth, compactly supported since `bsWin ℓ 0 = chiScale ℓ`
has compact support) and `K p := ‖kinFT ĝ p‖² ≥ 0`, the `p`-space mass density.

* Both `bsOneBody`'s are, by definition, `(2π)⁻³∫_p F(‖p‖)·K p`, and `(fun r => r^2) ‖p‖ = ‖p‖²`.
* Plancherel in the corpus's `p`-convention (`Work.BSKinetic.plancherel_pconv`, whose normalisation
  `(2π)⁻³∫_p ‖kinFT u p‖² = ∫_x u(x)²` matches the prefactor of `bsOneBody`) turns the mass term
  `∫_z g z²` into `(2π)⁻³∫_p K p`.
* Pointwise in `p`, for `r = ‖p‖ ≥ 0`,

      `½r² − c² ≤ [r−c]₊²`,

  because for `r ≤ c` the left side is `≤ 0`, and for `r ≥ c` the difference is `½(r−2c)² ≥ 0`
  (equality at `r = 2c`; the bound is the sharp "half" constant of the `1/2`-vs-`2c²` trade).
  Multiplying by `K p ≥ 0` and integrating gives the claim, the two integrals being honest because
  `p ↦ K p` and `p ↦ ‖p‖²K p` are integrable for a smooth compactly supported state
  (`integrable_kinFT_sq`, `integrable_kinFT_energy_cspt`).

The integrability hypotheses matter: Lean's Bochner integral is `0` on non-integrable functions,
and here every integral appearing is of a nonnegative (hence honestly finite) function.
-/

namespace Work.BoseFixB1S

open MeasureTheory
open scoped ContDiff Topology Real

theorem bsOneBody_fsKinCoeff_ge_mass {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 ≤ c)
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ) :
    (1 / 2) * Work.BSKinetic.bsOneBody ℓ (fun r => r ^ 2) 0 ψ
      - c ^ 2 * ∫ z : EuclideanSpace ℝ (Fin 3),
          (Work.BSKinetic.bsWin ℓ 0 z * Work.BSKinetic.bsQ ℓ 0 ψ z) ^ 2
      ≤ Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) 0 ψ := by
  have hpi : (0 : ℝ) < (2 * Real.pi) ^ 3 := by positivity
  -- the localised mean-free one-body state and its complexification
  set g : ℝ³ → ℝ := fun z => Work.BSKinetic.bsWin ℓ 0 z * Work.BSKinetic.bsQ ℓ 0 ψ z with hg
  set H : ℝ³ → ℂ :=
    fun z => (Work.BSKinetic.bsWin ℓ 0 z : ℂ) * (Work.BSKinetic.bsQ ℓ 0 ψ z : ℂ) with hH
  -- regularity of the localised state: the window is a rescaled bump, the mean-free part is smooth
  have hWcd : ContDiff ℝ (⊤ : ENat) (Work.BSKinetic.bsWin ℓ 0) := by
    have h' : Work.BSKinetic.bsWin ℓ 0
        = fun z : ℝ³ => Submission.BoseGases.chiScale ℓ (z - ℓ • (0 : ℝ³)) := rfl
    rw [h']
    exact (Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).comp
      (contDiff_id.sub contDiff_const)
  have hWcs : HasCompactSupport (Work.BSKinetic.bsWin ℓ 0) := by
    have h' : Work.BSKinetic.bsWin ℓ 0
        = Submission.BoseGases.chiScale ℓ ∘ ⇑(Homeomorph.subRight (ℓ • (0 : ℝ³))) := rfl
    rw [h']
    exact (Submission.BoseGases.chiScale_hasCompactSupport (ne_of_gt hℓ)).comp_homeomorph _
  have hQcd : ContDiff ℝ (⊤ : ENat) (Work.BSKinetic.bsQ ℓ 0 ψ) := by
    have h' : Work.BSKinetic.bsQ ℓ 0 ψ
        = fun z : ℝ³ => ψ z - Work.BSKinetic.bsMean ℓ 0 ψ := rfl
    rw [h']
    exact hψ.sub contDiff_const
  have hgcd : ContDiff ℝ (⊤ : ENat) g := by rw [hg]; exact hWcd.mul hQcd
  have hgcs : HasCompactSupport g := by rw [hg]; exact HasCompactSupport.mul_right hWcs
  -- the complexified state is the pointwise extension of `g`
  have hHg : H = fun z : ℝ³ => ((g z : ℝ) : ℂ) := by
    funext z
    rw [hH, hg]
    exact (Complex.ofReal_mul _ _).symm
  have hKfz : (fun z : ℝ³ => ((g z : ℝ) : ℂ)) = H := hHg.symm
  -- the `p`-space mass densities agree
  have hKf : (fun p : ℝ³ =>
        ‖Submission.BoseGases.kinFT (fun z : ℝ³ => ((g z : ℝ) : ℂ)) p‖ ^ 2)
      = fun p : ℝ³ => ‖Submission.BoseGases.kinFT H p‖ ^ 2 := by
    funext p
    rw [hKfz]
  -- integrability of the mass density and of its `‖p‖²`-weighted version
  have hI1g : Integrable (fun p : ℝ³ =>
      ‖Submission.BoseGases.kinFT (fun z : ℝ³ => ((g z : ℝ) : ℂ)) p‖ ^ 2) :=
    Work.BSKinetic.integrable_kinFT_sq g hgcd hgcs
  have hI1 : Integrable (fun p : ℝ³ => ‖Submission.BoseGases.kinFT H p‖ ^ 2) :=
    hI1g.congr (Filter.Eventually.of_forall (fun p => congrFun hKf p))
  have hI2g : Integrable (fun p : ℝ³ =>
      ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT (fun z : ℝ³ => ((g z : ℝ) : ℂ)) p‖ ^ 2) :=
    Work.SmallBoxTBWord.integrable_kinFT_energy_cspt g hgcd hgcs
  have hI2 : Integrable (fun p : ℝ³ => ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT H p‖ ^ 2) :=
    hI2g.congr (Filter.Eventually.of_forall (fun p => by
      dsimp only; rw [congrFun hKf p]))
  have hI3g : Integrable (fun p : ℝ³ => Submission.BoseGases.fsKinCoeff c ‖p‖ *
      ‖Submission.BoseGases.kinFT (fun z : ℝ³ => ((g z : ℝ) : ℂ)) p‖ ^ 2) :=
    Work.BSKinetic.Decomp.integrable_fsKinCoeff_mul_bsPsi_sq (c := c) (h := g) hgcd hgcs
  have hI3 : Integrable (fun p : ℝ³ =>
      Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Submission.BoseGases.kinFT H p‖ ^ 2) :=
    hI3g.congr (Filter.Eventually.of_forall (fun p => by
      dsimp only; rw [congrFun hKf p]))
  -- Plancherel in the corpus's `p`-convention: `(2π)⁻³∫_p K p = ∫_z g z²`
  have hPl := Work.BSKinetic.plancherel_pconv g hgcd hgcs
  have hIntK : (∫ p : ℝ³,
        ‖Submission.BoseGases.kinFT (fun x : ℝ³ => ((g x : ℝ) : ℂ)) p‖ ^ 2)
      = ∫ p : ℝ³, ‖Submission.BoseGases.kinFT H p‖ ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    rw [show (fun x : ℝ³ => ((g x : ℝ) : ℂ)) = H from hHg.symm]
  have h1 : (∫ x : ℝ³, (g x) ^ 2)
      = ∫ z : ℝ³, (Work.BSKinetic.bsWin ℓ 0 z * Work.BSKinetic.bsQ ℓ 0 ψ z) ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    rw [hg]
  have hM : (∫ z : ℝ³, (Work.BSKinetic.bsWin ℓ 0 z * Work.BSKinetic.bsQ ℓ 0 ψ z) ^ 2)
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, ‖Submission.BoseGases.kinFT H p‖ ^ 2 := by
    rw [← h1, ← hPl, hIntK]
  -- the two words in `p`-space form
  have hA : Work.BSKinetic.bsOneBody ℓ (fun r => r ^ 2) 0 ψ
      = ((2 * Real.pi) ^ 3)⁻¹ *
          ∫ p : ℝ³, ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT H p‖ ^ 2 := by
    rw [Work.BSKinetic.bsOneBody, ← hH]
  have hC : Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) 0 ψ
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³,
          Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Submission.BoseGases.kinFT H p‖ ^ 2 := by
    rw [Work.BSKinetic.bsOneBody, ← hH]
  -- the pointwise symbol inequality `½r² − c² ≤ [r−c]₊²` for `r = ‖p‖ ≥ 0`
  have hsym : ∀ p : ℝ³,
      (1 / 2) * ‖p‖ ^ 2 - c ^ 2 ≤ Submission.BoseGases.fsKinCoeff c ‖p‖ := by
    intro p
    have hr := norm_nonneg p
    rw [Submission.BoseGases.fsKinCoeff]
    rcases le_or_gt ‖p‖ c with h | h
    · have h2 : ‖p‖ ^ 2 ≤ c ^ 2 := by nlinarith
      rw [max_eq_right (by linarith : ‖p‖ - c ≤ 0)]
      nlinarith [sq_nonneg c]
    · rw [max_eq_left (by linarith : (0 : ℝ) ≤ ‖p‖ - c)]
      nlinarith [sq_nonneg (‖p‖ - 2 * c)]
  have hIleft : Integrable (fun p : ℝ³ =>
      ((1 / 2) * ‖p‖ ^ 2 - c ^ 2) * ‖Submission.BoseGases.kinFT H p‖ ^ 2) :=
    ((hI2.const_mul (1 / 2)).sub (hI1.const_mul (c ^ 2))).congr
      (Filter.Eventually.of_forall (fun p => by simp only [Pi.sub_apply]; ring))
  have hkey : (∫ p : ℝ³,
        ((1 / 2) * ‖p‖ ^ 2 - c ^ 2) * ‖Submission.BoseGases.kinFT H p‖ ^ 2)
      ≤ ∫ p : ℝ³,
          Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Submission.BoseGases.kinFT H p‖ ^ 2 :=
    integral_mono_ae hIleft hI3 (Filter.Eventually.of_forall (fun p =>
      mul_le_mul_of_nonneg_right (hsym p) (sq_nonneg _)))
  -- split the `p`-integral of the difference
  have hEq : (1 / 2) * (∫ p : ℝ³, ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT H p‖ ^ 2)
        - c ^ 2 * (∫ p : ℝ³, ‖Submission.BoseGases.kinFT H p‖ ^ 2)
      = ∫ p : ℝ³, ((1 / 2) * ‖p‖ ^ 2 - c ^ 2) * ‖Submission.BoseGases.kinFT H p‖ ^ 2 := by
    have hpt : (∫ p : ℝ³, (1 / 2) * (‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT H p‖ ^ 2)
            - c ^ 2 * ‖Submission.BoseGases.kinFT H p‖ ^ 2)
        = ∫ p : ℝ³,
            ((1 / 2) * ‖p‖ ^ 2 - c ^ 2) * ‖Submission.BoseGases.kinFT H p‖ ^ 2 :=
      integral_congr_ae (Filter.Eventually.of_forall (fun p => by ring_nf))
    rw [← hpt, integral_sub (hI2.const_mul (1 / 2)) (hI1.const_mul (c ^ 2)),
      integral_const_mul, integral_const_mul]
  rw [hA, hM, hC]
  calc (1 / 2) * (((2 * Real.pi) ^ 3)⁻¹ *
          ∫ p : ℝ³, ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT H p‖ ^ 2)
        - c ^ 2 * (((2 * Real.pi) ^ 3)⁻¹ *
          ∫ p : ℝ³, ‖Submission.BoseGases.kinFT H p‖ ^ 2)
      = ((2 * Real.pi) ^ 3)⁻¹ *
          ((1 / 2) * (∫ p : ℝ³, ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT H p‖ ^ 2)
            - c ^ 2 * (∫ p : ℝ³, ‖Submission.BoseGases.kinFT H p‖ ^ 2)) := by ring
    _ = ((2 * Real.pi) ^ 3)⁻¹ *
          (∫ p : ℝ³,
            ((1 / 2) * ‖p‖ ^ 2 - c ^ 2) * ‖Submission.BoseGases.kinFT H p‖ ^ 2) := by
        rw [hEq]
    _ ≤ ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : ℝ³,
          Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Submission.BoseGases.kinFT H p‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hkey (le_of_lt (inv_pos.mpr hpi))

end Work.BoseFixB1S
