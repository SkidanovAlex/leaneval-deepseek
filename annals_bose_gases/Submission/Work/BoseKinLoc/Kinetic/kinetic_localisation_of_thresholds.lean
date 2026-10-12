import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Decomp.continuous_bsOneBody
import Submission.Work.BoseKinLoc.Kinetic.gapWord_measurable
import Submission.Work.BoseKinLoc.Kinetic.momWord_measurable
import Submission.Work.BoseKinLoc.Kinetic.tprSym_integrable
import Submission.Work.BoseKinLoc.NeuFrac.box_avg
import Submission.Work.BoseKinLoc.NeuFrac.neuFrac_add_const_L2
import Submission.Work.BoseKinLoc.Word.fsT_nonneg
import Submission.Work.OneBodyKin.dSpace_eq_fourier
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Kinetic.kinetic_localisation_of_thresholds`

**FS `lem:LocKinEn` with the threshold constants explicit.**  This module proves

`kinetic_localisation_of_thresholds` : from `NeumannBound`, `GapBound β`, the pointwise
(`b ≤ b₀`) form of `MomBound`, the pointwise (`σ ≤ s₀`) form of `TprimeBound C` and the
momentum-space budget `AssemblySymbolAt β C cA`, one gets

`KineticLocalisation c₀` with `c₀ := min (min cA (min b₀ (min 1 (s₀/2)))) 1` :
`∫_u fsT ℓ d s ε_T b u ψ ≤ dSpace ψ`
for every `ψ` smooth of compact support and every `(ℓ,d,s,ε_T,b) ∈ KinRegime c₀`.

This is `kinetic_localisation_of_pieces` with the existential thresholds of
`MomBound`/`TprimeBound`/`AssemblySymbol` replaced by the caller's explicit `b₀`, `s₀`, `cA`,
which is what the downstream assembly (`BoseFixGlue`) needs: the caller knows its own
constants, so it wants the resulting regime at the *aligned* constant rather than at an
existential witness.

## The argument

`fsT = neuWord + gapWord + momWord + mainWord` (`Defs.fsT_eq_sum`).  Each of the four words is
nonnegative on `KinRegime c₀`, and `fsT` is integrable by hypothesis; hence the `u`-integral
splits, `∫fsT = ∫neuWord + ∫gapWord + ∫momWord + ∫mainWord`.  The three words `gapWord`,
`momWord`, `mainWord` are parametric integrals / continuous functions of `u` (hence a.e.
strongly measurable — `gapWord_measurable`, `momWord_measurable` and
`BSKinetic.Decomp.continuous_bsOneBody`), which makes `neuWord = fsT − (gap+mom+main)`
measurable as well; since all four pieces lie in `[0, fsT]` they are integrable.

The four integral bounds are then exactly the residuals:

* `neuWord` — pull out `½ε_T(dℓ)⁻²`; `neuFrac` is blind to additive constants
  (`neuFrac_add_const_of_integrableSq`, applied to `Q_uψ = ψ − m_u`), and `NeumannBound` gives
  `∫_u neuFrac ℓ (dℓ)⁻² u ψ ≤ raFrac ℓ d ψ`;
* `gapWord` — `bℓ⁻²∫_u gapBare ≤ bℓ⁻² gapFrac ℓ β ψ` is `GapBound β`;
* `momWord` — `hmom` gives `b∫_u momForm ≤ ½ raFrac ℓ d ψ` for `b ≤ b₀`;
* `mainWord` — split into the two cut-offs `σ = 2s` (resp. `2ds`), each dominated by
  `htpr` (which needs `σ ≤ s₀`, hence `s ≤ c₀ ≤ s₀/2`), the two `bsOneBody` being
  integrable in `u` because they are dominated by the uncut family form
  (`BSKinetic.integrable_bsOneBody_fsKinCoeff_zero`).

Summing, `∫fsT ≤ ½ε_T(dℓ)⁻² raFrac + bℓ⁻² gapFrac + ½ε_T(dℓ)⁻² raFrac
+ ((1−ε_T)A₁ + ε_T A₂)`, and the momentum-space bookkeeping (`budget_le_dSpace`) rewrites this
as `(2π)⁻³∫_p (budget)(p)·‖ψ̂(p)‖²` with `(budget)` the symbol of `AssemblySymbolAt β C cA`;
that symbol is pointwise `≤ ‖p‖²`, and `(2π)⁻³∫_p ‖p‖²‖ψ̂(p)‖² = dSpace ψ`
(`OneBodyKin.dSpace_eq_fourier`).

The constants are aligned by taking `c₀ := min (min c_A (min b₀ (min 1 (s₀/2)))) 1`.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Kinetic

set_option maxHeartbeats 3200000

/-! ## 1. The momentum-space bookkeeping

Given the pointwise momentum budget of `AssemblySymbol` and the `p`-integrability of the two
`tprSym`-weighted densities, the combination
`½ε_T(dℓ)⁻² raFrac + bℓ⁻² gapFrac + ½ε_T(dℓ)⁻² raFrac + ((1−ε_T)A₁ + ε_T A₂)`
is dominated by `dSpace ψ`. -/

private lemma budget_le_dSpace {β C ℓ d s εT b : ℝ} (hβ : 0 < β) (hC : 0 < C) (hℓ : 0 < ℓ)
    (hd : 0 < d) (hs : 0 < s) (hεT : 0 ≤ εT) (hεT1 : εT ≤ 1) (hb : 0 ≤ b)
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hcs : HasCompactSupport ψ)
    (hbud : ∀ p : EuclideanSpace ℝ (Fin 3),
      εT * (d * ℓ) ^ (-2 : ℤ) * Work.BoseKinLoc.raSym ℓ d p
      + b * β⁻¹ * (‖p‖ ^ 2 / (ℓ ^ 2 * ‖p‖ ^ 2 + β))
      + ((1 - εT) * Work.BoseKinLoc.tprSym ℓ (2 * s) C p
          + εT * Work.BoseKinLoc.tprSym ℓ (2 * (d * s)) C p) ≤ ‖p‖ ^ 2)
    (hT1 : Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseKinLoc.tprSym ℓ (2 * s) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2))
    (hT2 : Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseKinLoc.tprSym ℓ (2 * (d * s)) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)) :
    (1 / 2) * (εT * (d * ℓ) ^ (-2 : ℤ)) * Work.BoseKinLoc.raFrac ℓ d ψ
      + b * ℓ ^ (-2 : ℤ) * Work.BoseKinLoc.gapFrac ℓ β ψ
      + (1 / 2) * (εT * (d * ℓ) ^ (-2 : ℤ)) * Work.BoseKinLoc.raFrac ℓ d ψ
      + ((1 - εT) * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
            Work.BoseKinLoc.tprSym ℓ (2 * s) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)
          + εT * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
            Work.BoseKinLoc.tprSym ℓ (2 * (d * s)) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2))
      ≤ Work.BSKinetic.dSpace ψ := by
  have hf2 : Integrable (fun p : EuclideanSpace ℝ (Fin 3) => ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2) :=
    Work.BSKinetic.integrable_kinFT_sq ψ hψ hcs
  have hIE : Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      ‖p‖ ^ 2 * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2) :=
    Work.SmallBoxTBWord.integrable_kinFT_energy_cspt ψ hψ hcs
  have hra_cont : Continuous (fun p : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseKinLoc.raSym ℓ d p) := by
    unfold Work.BoseKinLoc.raSym
    exact Continuous.div (by fun_prop) (by fun_prop) (fun p => by positivity)
  have hga_cont : Continuous (fun p : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseKinLoc.gapSym ℓ β p) := by
    unfold Work.BoseKinLoc.gapSym
    exact continuous_const.mul (Continuous.div (by fun_prop) (by fun_prop) (fun p => by positivity))
  have hra_le : ∀ p : EuclideanSpace ℝ (Fin 3), ‖Work.BoseKinLoc.raSym ℓ d p‖ ≤ 1 := by
    intro p
    have hden : (0:ℝ) < ‖p‖ ^ 2 + (d * ℓ) ^ (-2 : ℤ) := by positivity
    have hpos : 0 ≤ Work.BoseKinLoc.raSym ℓ d p := by unfold Work.BoseKinLoc.raSym; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hpos, Work.BoseKinLoc.raSym, div_le_one hden]
    linarith [sq_nonneg ‖p‖, show (0:ℝ) ≤ (d * ℓ) ^ (-2 : ℤ) from by positivity]
  have hga_le : ∀ p : EuclideanSpace ℝ (Fin 3), ‖Work.BoseKinLoc.gapSym ℓ β p‖ ≤ β⁻¹ := by
    intro p
    have hden : (0:ℝ) < ℓ ^ 2 * ‖p‖ ^ 2 + β := by positivity
    have hpos : 0 ≤ Work.BoseKinLoc.gapSym ℓ β p := by unfold Work.BoseKinLoc.gapSym; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hpos, Work.BoseKinLoc.gapSym]
    have hle : (ℓ ^ 2 * ‖p‖ ^ 2) / (ℓ ^ 2 * ‖p‖ ^ 2 + β) ≤ 1 := by
      rw [div_le_one hden]; linarith [sq_nonneg ‖p‖, sq_nonneg ℓ]
    calc β⁻¹ * ((ℓ ^ 2 * ‖p‖ ^ 2) / (ℓ ^ 2 * ‖p‖ ^ 2 + β))
        ≤ β⁻¹ * 1 := mul_le_mul_of_nonneg_left hle (by positivity)
      _ = β⁻¹ := mul_one _
  have hIra : Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseKinLoc.raSym ℓ d p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2) :=
    hf2.bdd_mul hra_cont.aestronglyMeasurable (ae_of_all _ hra_le)
  have hIgap : Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseKinLoc.gapSym ℓ β p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2) :=
    hf2.bdd_mul hga_cont.aestronglyMeasurable (ae_of_all _ hga_le)
  set Bd : EuclideanSpace ℝ (Fin 3) → ℝ := fun p =>
      εT * (d * ℓ) ^ (-2 : ℤ) * Work.BoseKinLoc.raSym ℓ d p
      + b * ℓ ^ (-2 : ℤ) * Work.BoseKinLoc.gapSym ℓ β p
      + ((1 - εT) * Work.BoseKinLoc.tprSym ℓ (2 * s) C p
          + εT * Work.BoseKinLoc.tprSym ℓ (2 * (d * s)) C p) with hBd_def
  have hptgap : ∀ p : EuclideanSpace ℝ (Fin 3), b * ℓ ^ (-2 : ℤ) * Work.BoseKinLoc.gapSym ℓ β p
      = b * β⁻¹ * (‖p‖ ^ 2 / (ℓ ^ 2 * ‖p‖ ^ 2 + β)) := by
    intro p
    rw [Work.BoseKinLoc.gapSym]
    field_simp
  have hbud' : ∀ p : EuclideanSpace ℝ (Fin 3), Bd p ≤ ‖p‖ ^ 2 := by
    intro p
    rw [hBd_def]
    beta_reduce
    rw [hptgap p]
    exact hbud p
  have hBdnn : ∀ p : EuclideanSpace ℝ (Fin 3), 0 ≤ Bd p := by
    intro p
    rw [hBd_def]
    have h1 : 0 ≤ Work.BoseKinLoc.raSym ℓ d p := by unfold Work.BoseKinLoc.raSym; positivity
    have h2 : 0 ≤ Work.BoseKinLoc.gapSym ℓ β p := by unfold Work.BoseKinLoc.gapSym; positivity
    have ht1 : 0 ≤ Work.BoseKinLoc.tprSym ℓ (2 * s) C p := by
      rw [Work.BoseKinLoc.tprSym]; split
      · exact Submission.BoseGases.fsKinCoeff_nonneg _ _
      · positivity
    have ht2 : 0 ≤ Work.BoseKinLoc.tprSym ℓ (2 * (d * s)) C p := by
      rw [Work.BoseKinLoc.tprSym]; split
      · exact Submission.BoseGases.fsKinCoeff_nonneg _ _
      · positivity
    have h3 : 0 ≤ (1 - εT) * Work.BoseKinLoc.tprSym ℓ (2 * s) C p := mul_nonneg (by linarith) ht1
    have h4 : 0 ≤ εT * Work.BoseKinLoc.tprSym ℓ (2 * (d * s)) C p := mul_nonneg hεT ht2
    have h5 : 0 ≤ εT * (d * ℓ) ^ (-2 : ℤ) * Work.BoseKinLoc.raSym ℓ d p := by
      have : (0:ℝ) ≤ ℓ ^ (-2 : ℤ) := by positivity
      positivity
    have h6 : 0 ≤ b * ℓ ^ (-2 : ℤ) * Work.BoseKinLoc.gapSym ℓ β p := by
      have : (0:ℝ) ≤ ℓ ^ (-2 : ℤ) := by positivity
      positivity
    linarith
  have hLE : (∫ p : EuclideanSpace ℝ (Fin 3), Bd p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)
      ≤ ∫ p : EuclideanSpace ℝ (Fin 3), ‖p‖ ^ 2 * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2 :=
    integral_mono_of_nonneg (ae_of_all _ (fun p => mul_nonneg (hBdnn p) (sq_nonneg _))) hIE
      (ae_of_all _ (fun p => mul_le_mul_of_nonneg_right (hbud' p) (sq_nonneg _)))
  have hExp : (∫ p : EuclideanSpace ℝ (Fin 3), Bd p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)
      = εT * (d * ℓ) ^ (-2 : ℤ) * (∫ p : EuclideanSpace ℝ (Fin 3),
            Work.BoseKinLoc.raSym ℓ d p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)
        + b * ℓ ^ (-2 : ℤ) * (∫ p : EuclideanSpace ℝ (Fin 3),
            Work.BoseKinLoc.gapSym ℓ β p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)
        + ((1 - εT) * (∫ p : EuclideanSpace ℝ (Fin 3),
              Work.BoseKinLoc.tprSym ℓ (2 * s) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)
            + εT * (∫ p : EuclideanSpace ℝ (Fin 3),
              Work.BoseKinLoc.tprSym ℓ (2 * (d * s)) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)) := by
    have h1 : Integrable (fun p : EuclideanSpace ℝ (Fin 3) => εT * (d * ℓ) ^ (-2 : ℤ) *
        (Work.BoseKinLoc.raSym ℓ d p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)) := hIra.const_mul _
    have h2 : Integrable (fun p : EuclideanSpace ℝ (Fin 3) => b * ℓ ^ (-2 : ℤ) *
        (Work.BoseKinLoc.gapSym ℓ β p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)) := hIgap.const_mul _
    have h3 : Integrable (fun p : EuclideanSpace ℝ (Fin 3) => (1 - εT) *
        (Work.BoseKinLoc.tprSym ℓ (2 * s) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)) :=
      hT1.const_mul _
    have h4 : Integrable (fun p : EuclideanSpace ℝ (Fin 3) => εT *
        (Work.BoseKinLoc.tprSym ℓ (2 * (d * s)) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)) :=
      hT2.const_mul _
    have h12 : Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
        εT * (d * ℓ) ^ (-2 : ℤ) * (Work.BoseKinLoc.raSym ℓ d p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)
        + b * ℓ ^ (-2 : ℤ) * (Work.BoseKinLoc.gapSym ℓ β p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)) :=
      (h1.add h2).congr (ae_of_all _ (fun p => rfl))
    have h34 : Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
        (1 - εT) * (Work.BoseKinLoc.tprSym ℓ (2 * s) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)
        + εT * (Work.BoseKinLoc.tprSym ℓ (2 * (d * s)) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)) :=
      (h3.add h4).congr (ae_of_all _ (fun p => rfl))
    rw [show (∫ p : EuclideanSpace ℝ (Fin 3), Bd p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)
        = ∫ p : EuclideanSpace ℝ (Fin 3), (εT * (d * ℓ) ^ (-2 : ℤ) *
              (Work.BoseKinLoc.raSym ℓ d p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)
            + b * ℓ ^ (-2 : ℤ) *
              (Work.BoseKinLoc.gapSym ℓ β p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)
            + ((1 - εT) * (Work.BoseKinLoc.tprSym ℓ (2 * s) C p
                  * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)
              + εT * (Work.BoseKinLoc.tprSym ℓ (2 * (d * s)) C p
                  * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2))) from by
      refine integral_congr_ae (ae_of_all _ (fun p => ?_))
      rw [hBd_def]; ring]
    rw [integral_add h12 h34, integral_add h1 h2, integral_add h3 h4,
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
  have hStep1 : (1 / 2) * (εT * (d * ℓ) ^ (-2 : ℤ)) * Work.BoseKinLoc.raFrac ℓ d ψ
        + b * ℓ ^ (-2 : ℤ) * Work.BoseKinLoc.gapFrac ℓ β ψ
        + (1 / 2) * (εT * (d * ℓ) ^ (-2 : ℤ)) * Work.BoseKinLoc.raFrac ℓ d ψ
        + ((1 - εT) * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
              Work.BoseKinLoc.tprSym ℓ (2 * s) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)
            + εT * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
              Work.BoseKinLoc.tprSym ℓ (2 * (d * s)) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2))
      = ((2 * Real.pi) ^ 3)⁻¹ * (εT * (d * ℓ) ^ (-2 : ℤ) * (∫ p : EuclideanSpace ℝ (Fin 3),
              Work.BoseKinLoc.raSym ℓ d p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)
          + b * ℓ ^ (-2 : ℤ) * (∫ p : EuclideanSpace ℝ (Fin 3),
              Work.BoseKinLoc.gapSym ℓ β p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)
          + ((1 - εT) * (∫ p : EuclideanSpace ℝ (Fin 3),
                Work.BoseKinLoc.tprSym ℓ (2 * s) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)
              + εT * (∫ p : EuclideanSpace ℝ (Fin 3),
                Work.BoseKinLoc.tprSym ℓ (2 * (d * s)) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2))) := by
    rw [Work.BoseKinLoc.raFrac, Work.BoseKinLoc.gapFrac]
    ring
  calc (1 / 2) * (εT * (d * ℓ) ^ (-2 : ℤ)) * Work.BoseKinLoc.raFrac ℓ d ψ
        + b * ℓ ^ (-2 : ℤ) * Work.BoseKinLoc.gapFrac ℓ β ψ
        + (1 / 2) * (εT * (d * ℓ) ^ (-2 : ℤ)) * Work.BoseKinLoc.raFrac ℓ d ψ
        + ((1 - εT) * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
              Work.BoseKinLoc.tprSym ℓ (2 * s) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)
            + εT * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
              Work.BoseKinLoc.tprSym ℓ (2 * (d * s)) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2))
      = ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3),
          Bd p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2) := by
        rw [hStep1, hExp]
    _ ≤ ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3),
          ‖p‖ ^ 2 * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hLE (by positivity)
    _ = Work.BSKinetic.dSpace ψ := (Work.OneBodyKin.dSpace_eq_fourier ψ hψ hcs).symm

/-! ## 2. The derivation at explicit thresholds -/

/-- **FS `lem:LocKinEn` at explicit thresholds.**  Same assembly as
`kinetic_localisation_of_pieces`, but with the three threshold constants (`c_A`, `b₀`, `s₀`)
supplied by the caller instead of existentially quantified: the word bounds `hmom`/`htpr` are
the pointwise forms of `MomBound`/`TprimeBound`, and the momentum budget comes from
`AssemblySymbolAt β C cA`.  The resulting regime constant is the aligned
`min (min cA (min b₀ (min 1 (s₀ / 2)))) 1`. -/
theorem kinetic_localisation_of_thresholds {β C cA b₀ s₀ : ℝ} (hcA : 0 < cA) (hb₀ : 0 < b₀)
    (hs₀ : 0 < s₀) (hSymAt : Work.BoseKinLoc.AssemblySymbolAt β C cA)
    (hgap : Work.BoseKinLoc.GapBound β) (hneu : Work.BoseKinLoc.NeumannBound)
    (hmom : ∀ b : ℝ, 0 < b → b ≤ b₀ → ∀ ψ : ℝ³ → ℝ, ContDiff ℝ (⊤ : ENat) ψ →
      HasCompactSupport ψ → ∀ ℓ d : ℝ, 0 < ℓ → 0 < d → d ≤ 1 →
        MeasureTheory.Integrable (fun u : ℝ³ => Work.BoseKinLoc.momForm ℓ d u ψ) →
          b * (∫ u : ℝ³, Work.BoseKinLoc.momForm ℓ d u ψ)
            ≤ (1 / 2) * Work.BoseKinLoc.raFrac ℓ d ψ)
    (htpr : ∀ σ : ℝ, 0 < σ → σ ≤ s₀ → ∀ ψ : ℝ³ → ℝ, ContDiff ℝ (⊤ : ENat) ψ →
      HasCompactSupport ψ → ∀ ℓ : ℝ, 0 < ℓ →
        MeasureTheory.Integrable (fun u : ℝ³ =>
          Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff ((σ * ℓ)⁻¹)) u ψ) →
          ∫ u : ℝ³,
              Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff ((σ * ℓ)⁻¹)) u ψ
            ≤ ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³,
                Work.BoseKinLoc.tprSym ℓ σ C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2) :
    Work.BoseKinLoc.KineticLocalisation (min (min cA (min b₀ (min 1 (s₀ / 2)))) 1) := by
  obtain ⟨hβ, hβ1, hC, hcAbud⟩ := hSymAt
  have hGmeas : ∀ (ℓ b : ℝ) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ), 0 < ℓ → ContDiff ℝ ∞ ψ →
      HasCompactSupport ψ → AEStronglyMeasurable (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseKinLoc.gapWord ℓ b u ψ) :=
    fun ℓ b ψ hℓ hψ hcs => gapWord_measurable hℓ hψ hcs
  have hMmeas : ∀ (ℓ d εT b : ℝ) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ), 0 < ℓ → ContDiff ℝ ∞ ψ →
      HasCompactSupport ψ → AEStronglyMeasurable (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseKinLoc.momWord ℓ d εT b u ψ) :=
    fun ℓ d εT b ψ hℓ hψ hcs => momWord_measurable hℓ hψ hcs
  intro ℓ d s εT b hreg ψ hψ hcs hint
  obtain ⟨hℓ, hd, hdc, hd1, hs, hsc, hεT, hεTc, hb, hbc⟩ := hreg
  -- the smallness of `c₀` against the four constants
  have hcA' : min (min cA (min b₀ (min 1 (s₀ / 2)))) 1 ≤ cA :=
    le_trans (min_le_left _ _) (min_le_left _ _)
  have hb₀' : min (min cA (min b₀ (min 1 (s₀ / 2)))) 1 ≤ b₀ :=
    le_trans (le_trans (min_le_left _ _) (min_le_right _ _)) (min_le_left _ _)
  have h1' : min (min cA (min b₀ (min 1 (s₀ / 2)))) 1 ≤ 1 :=
    le_trans (le_trans (le_trans (min_le_left _ _) (min_le_right _ _)) (min_le_right _ _))
      (min_le_left _ _)
  have hs' : min (min cA (min b₀ (min 1 (s₀ / 2)))) 1 ≤ s₀ / 2 :=
    le_trans (le_trans (le_trans (min_le_left _ _) (min_le_right _ _)) (min_le_right _ _))
      (min_le_right _ _)
  have hregA : Work.BoseKinLoc.KinRegime cA ℓ d s εT b :=
    ⟨hℓ, hd, le_trans hdc hcA', hd1, hs, le_trans hsc hcA', hεT, le_trans hεTc hcA', hb,
      le_trans hbc hcA'⟩
  have hεT1 : εT ≤ 1 := le_trans hεTc h1'
  have hbb₀ : b ≤ b₀ := le_trans hbc hb₀'
  have hs2s₀ : 2 * s ≤ s₀ := by linarith
  have h2ds₀ : 2 * (d * s) ≤ s₀ := by nlinarith [hd, hs, hd1, hs2s₀, sq_nonneg d, sq_nonneg s]
  -- the pointwise budget
  have hbud : ∀ p : EuclideanSpace ℝ (Fin 3),
      εT * (d * ℓ) ^ (-2 : ℤ) * Work.BoseKinLoc.raSym ℓ d p
      + b * β⁻¹ * (‖p‖ ^ 2 / (ℓ ^ 2 * ‖p‖ ^ 2 + β))
      + ((1 - εT) * Work.BoseKinLoc.tprSym ℓ (2 * s) C p
          + εT * Work.BoseKinLoc.tprSym ℓ (2 * (d * s)) C p) ≤ ‖p‖ ^ 2 :=
    fun p => hcAbud ℓ d s εT b hregA p
  -- integrability of the two `tprSym` weights
  have hT1 : Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseKinLoc.tprSym ℓ (2 * s) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2) :=
    tprSym_integrable hℓ (by linarith) hC hψ hcs
  have hT2 : Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseKinLoc.tprSym ℓ (2 * (d * s)) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2) :=
    tprSym_integrable hℓ (by positivity) hC hψ hcs
  -- measurability of the three parametric pieces, and the resulting splitting
  have hGm : AEStronglyMeasurable (fun u : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseKinLoc.gapWord ℓ b u ψ) := hGmeas ℓ b ψ hℓ hψ hcs
  have hMm : AEStronglyMeasurable (fun u : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseKinLoc.momWord ℓ d εT b u ψ) := hMmeas ℓ d εT b ψ hℓ hψ hcs
  have hPm : AEStronglyMeasurable (fun u : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseKinLoc.mainWord ℓ d s εT u ψ) := by
    have hc1 : Continuous (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹))
          u ψ) := Work.BSKinetic.Decomp.continuous_bsOneBody hℓ _ ψ hψ hcs
    have hc2 : Continuous (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹))
          u ψ) := Work.BSKinetic.Decomp.continuous_bsOneBody hℓ _ ψ hψ hcs
    have hfun : (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseKinLoc.mainWord ℓ d s εT u ψ)
        = fun u : EuclideanSpace ℝ (Fin 3) => (1 - εT) * Work.BSKinetic.bsOneBody ℓ
              (Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹)) u ψ
            + εT * Work.BSKinetic.bsOneBody ℓ
              (Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹)) u ψ := rfl
    rw [hfun]
    exact ((hc1.const_mul _).add (hc2.const_mul _)).aestronglyMeasurable
  have hAn : ∀ u : EuclideanSpace ℝ (Fin 3), 0 ≤ Work.BoseKinLoc.neuWord ℓ d εT u ψ := by
    intro u
    have hcont : Continuous (Work.BoseKinLoc.Qfree ℓ u ψ) := hψ.continuous.sub continuous_const
    have hI : Integrable (fun z : EuclideanSpace ℝ (Fin 3) => (Work.BoseKinLoc.Qfree ℓ u ψ z) ^ 2)
        (volume.restrict (Work.BoseKinLoc.lamBox ℓ u)) :=
      (ContinuousOn.integrableOn_compact (isCompact_closedBall (ℓ • u) (2 * (|ℓ| + 1)))
        (hcont.pow 2).continuousOn).mono_set
          (Work.BoseKinLoc.NeuFrac.lamBox_subset_closedBall ℓ u)
    have ha2 : 0 ≤ (d * ℓ) ^ (-2 : ℤ) := zpow_nonneg (le_of_lt (mul_pos hd hℓ)) _
    have hn := Work.BoseKinLoc.Word.neuFrac_nonneg_of_integrableSq (ℓ := ℓ)
      (a2 := (d * ℓ) ^ (-2 : ℤ)) ha2 u hI
    simp only [Work.BoseKinLoc.neuWord]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hεT.le) ha2) hn
  have hGn : ∀ u : EuclideanSpace ℝ (Fin 3), 0 ≤ Work.BoseKinLoc.gapWord ℓ b u ψ :=
    fun u => Work.BoseKinLoc.gapWord_nonneg hb.le hℓ.le u ψ
  have hMn : ∀ u : EuclideanSpace ℝ (Fin 3), 0 ≤ Work.BoseKinLoc.momWord ℓ d εT b u ψ :=
    fun u => Work.BoseKinLoc.momWord_nonneg hb.le hεT.le (le_of_lt (mul_pos hd hℓ)) u ψ
  have hPn : ∀ u : EuclideanSpace ℝ (Fin 3), 0 ≤ Work.BoseKinLoc.mainWord ℓ d s εT u ψ :=
    fun u => Work.BoseKinLoc.mainWord_nonneg hεT.le hεT1 u ψ
  have hRn : ∀ u : EuclideanSpace ℝ (Fin 3), 0 ≤ Work.BoseKinLoc.gapWord ℓ b u ψ
      + Work.BoseKinLoc.momWord ℓ d εT b u ψ + Work.BoseKinLoc.mainWord ℓ d s εT u ψ :=
    fun u => by linarith [hGn u, hMn u, hPn u]
  have hRle : ∀ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.gapWord ℓ b u ψ
      + Work.BoseKinLoc.momWord ℓ d εT b u ψ + Work.BoseKinLoc.mainWord ℓ d s εT u ψ
      ≤ Work.BoseKinLoc.fsT ℓ d s εT b u ψ := by
    intro u; rw [Work.BoseKinLoc.fsT_eq_sum]; linarith [hAn u]
  have hRm : AEStronglyMeasurable (fun u : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseKinLoc.gapWord ℓ b u ψ + Work.BoseKinLoc.momWord ℓ d εT b u ψ
        + Work.BoseKinLoc.mainWord ℓ d s εT u ψ) := (hGm.add hMm).add hPm
  have hRint : Integrable (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseKinLoc.gapWord ℓ b u ψ
      + Work.BoseKinLoc.momWord ℓ d εT b u ψ + Work.BoseKinLoc.mainWord ℓ d s εT u ψ) :=
    hint.mono' hRm (ae_of_all _ (fun u => by
      rw [Real.norm_of_nonneg (hRn u)]; exact hRle u))
  have hGint : Integrable (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseKinLoc.gapWord ℓ b u ψ) :=
    hRint.mono' hGm (ae_of_all _ (fun u => by
      rw [Real.norm_of_nonneg (hGn u)]; linarith [hMn u, hPn u]))
  have hMint : Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseKinLoc.momWord ℓ d εT b u ψ) :=
    hRint.mono' hMm (ae_of_all _ (fun u => by
      rw [Real.norm_of_nonneg (hMn u)]; linarith [hGn u, hPn u]))
  have hPint : Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseKinLoc.mainWord ℓ d s εT u ψ) :=
    hRint.mono' hPm (ae_of_all _ (fun u => by
      rw [Real.norm_of_nonneg (hPn u)]; linarith [hGn u, hMn u]))
  have hAm : AEStronglyMeasurable (fun u : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseKinLoc.neuWord ℓ d εT u ψ) := by
    have hfun : (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseKinLoc.neuWord ℓ d εT u ψ)
        = fun u => Work.BoseKinLoc.fsT ℓ d s εT b u ψ - (Work.BoseKinLoc.gapWord ℓ b u ψ
            + Work.BoseKinLoc.momWord ℓ d εT b u ψ + Work.BoseKinLoc.mainWord ℓ d s εT u ψ) := by
      funext u; rw [Work.BoseKinLoc.fsT_eq_sum]; ring
    rw [hfun]
    exact hint.aestronglyMeasurable.sub hRm
  have hAint : Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseKinLoc.neuWord ℓ d εT u ψ) :=
    hint.mono' hAm (ae_of_all _ (fun u => by
      rw [Real.norm_of_nonneg (hAn u)]; rw [Work.BoseKinLoc.fsT_eq_sum]
      linarith [hGn u, hMn u, hPn u]))
  have hsplit : (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.fsT ℓ d s εT b u ψ)
      = (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.neuWord ℓ d εT u ψ)
        + (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.gapWord ℓ b u ψ)
        + (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.momWord ℓ d εT b u ψ)
        + (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.mainWord ℓ d s εT u ψ) := by
    have hsplit1 : (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.fsT ℓ d s εT b u ψ)
        = ∫ u : EuclideanSpace ℝ (Fin 3), (Work.BoseKinLoc.neuWord ℓ d εT u ψ
            + Work.BoseKinLoc.gapWord ℓ b u ψ + Work.BoseKinLoc.momWord ℓ d εT b u ψ
            + Work.BoseKinLoc.mainWord ℓ d s εT u ψ) := rfl
    have h12 : Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseKinLoc.neuWord ℓ d εT u ψ + Work.BoseKinLoc.gapWord ℓ b u ψ) :=
      (hAint.add hGint).congr (ae_of_all _ (fun u => rfl))
    have h123 : Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
        (Work.BoseKinLoc.neuWord ℓ d εT u ψ + Work.BoseKinLoc.gapWord ℓ b u ψ)
          + Work.BoseKinLoc.momWord ℓ d εT b u ψ) :=
      (h12.add hMint).congr (ae_of_all _ (fun u => rfl))
    have h1234 : Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
        ((Work.BoseKinLoc.neuWord ℓ d εT u ψ + Work.BoseKinLoc.gapWord ℓ b u ψ)
          + Work.BoseKinLoc.momWord ℓ d εT b u ψ)
          + Work.BoseKinLoc.mainWord ℓ d s εT u ψ) :=
      (h123.add hPint).congr (ae_of_all _ (fun u => rfl))
    rw [hsplit1]
    rw [show (∫ u : EuclideanSpace ℝ (Fin 3), (Work.BoseKinLoc.neuWord ℓ d εT u ψ
            + Work.BoseKinLoc.gapWord ℓ b u ψ + Work.BoseKinLoc.momWord ℓ d εT b u ψ
            + Work.BoseKinLoc.mainWord ℓ d s εT u ψ))
        = ∫ u : EuclideanSpace ℝ (Fin 3), (((Work.BoseKinLoc.neuWord ℓ d εT u ψ
              + Work.BoseKinLoc.gapWord ℓ b u ψ) + Work.BoseKinLoc.momWord ℓ d εT b u ψ)
            + Work.BoseKinLoc.mainWord ℓ d s εT u ψ) from by
      refine integral_congr_ae (ae_of_all _ (fun u => by ring))]
    rw [integral_add h123 hPint, integral_add h12 hMint, integral_add hAint hGint]
  -- the four termwise bounds
  have hA_bound : (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.neuWord ℓ d εT u ψ)
      ≤ (1 / 2) * (εT * (d * ℓ) ^ (-2 : ℤ)) * Work.BoseKinLoc.raFrac ℓ d ψ := by
    have hdℓ : 0 < d * ℓ := mul_pos hd hℓ
    have ha2pos : 0 < (d * ℓ) ^ (-2 : ℤ) := zpow_pos hdℓ _
    have h1 : (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.neuWord ℓ d εT u ψ)
        = ((1/2) * εT * (d * ℓ) ^ (-2 : ℤ)) * (∫ u : EuclideanSpace ℝ (Fin 3),
            Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) u (Work.BoseKinLoc.Qfree ℓ u ψ)) := by
      rw [show (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseKinLoc.neuWord ℓ d εT u ψ)
          = fun u : EuclideanSpace ℝ (Fin 3) =>
              ((1/2) * εT * (d * ℓ) ^ (-2 : ℤ)) *
                Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) u (Work.BoseKinLoc.Qfree ℓ u ψ)
          from rfl]
      exact integral_const_mul _ _
    have hψ2 : Integrable (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z) ^ 2) :=
      Continuous.integrable_of_hasCompactSupport (hψ.continuous.pow 2)
        (hcs.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num))
    have hQ : ∀ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) u
        (Work.BoseKinLoc.Qfree ℓ u ψ) = Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) u ψ := by
      intro u
      have hQfun : Work.BoseKinLoc.Qfree ℓ u ψ = fun z : EuclideanSpace ℝ (Fin 3) =>
          ψ z + (-(Work.BSKinetic.bsMean ℓ u ψ)) := by
        funext z; simp only [Work.BoseKinLoc.Qfree, Work.BSKinetic.bsQ]; ring
      rw [hQfun, Work.BoseKinLoc.NeuFrac.neuFrac_add_const_of_integrableSq (ℓ := ℓ)
        (a2 := (d * ℓ) ^ (-2 : ℤ)) ha2pos u ψ (-(Work.BSKinetic.bsMean ℓ u ψ))
        hψ.continuous.measurable hψ2]
    have hcne : ((1/2) * εT * (d * ℓ) ^ (-2 : ℤ)) ≠ 0 := by positivity
    have hIntQ : Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) u (Work.BoseKinLoc.Qfree ℓ u ψ)) := by
      have h0 := hAint.const_mul (((1/2) * εT * (d * ℓ) ^ (-2 : ℤ))⁻¹)
      refine h0.congr (ae_of_all _ (fun u => ?_))
      show (((1/2) * εT * (d * ℓ) ^ (-2 : ℤ))⁻¹ * Work.BoseKinLoc.neuWord ℓ d εT u ψ)
        = Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) u (Work.BoseKinLoc.Qfree ℓ u ψ)
      simp only [Work.BoseKinLoc.neuWord]
      rw [← mul_assoc, inv_mul_cancel₀ hcne, one_mul]
    have hIntψ : Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) u ψ) :=
      hIntQ.congr (ae_of_all _ (fun u => hQ u))
    have h3 : (∫ u : EuclideanSpace ℝ (Fin 3),
        Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) u ψ) ≤ Work.BoseKinLoc.raFrac ℓ d ψ :=
      hneu ψ hψ hcs ℓ d hℓ hd hIntψ
    have h2eq : (∫ u : EuclideanSpace ℝ (Fin 3),
          Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) u (Work.BoseKinLoc.Qfree ℓ u ψ))
        = ∫ u : EuclideanSpace ℝ (Fin 3),
            Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) u ψ :=
      integral_congr_ae (ae_of_all _ hQ)
    rw [h1, h2eq]
    have hc : ((1/2) * εT * (d * ℓ) ^ (-2 : ℤ)) = (1/2) * (εT * (d * ℓ) ^ (-2 : ℤ)) := by ring
    rw [hc]
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  have hG_bound : (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.gapWord ℓ b u ψ)
      ≤ b * ℓ ^ (-2 : ℤ) * Work.BoseKinLoc.gapFrac ℓ β ψ := by
    have h1 : (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.gapWord ℓ b u ψ)
        = (b * ℓ ^ (-2 : ℤ)) * (∫ u : EuclideanSpace ℝ (Fin 3),
            Work.BoseKinLoc.gapBare ℓ u ψ) := by
      rw [show (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseKinLoc.gapWord ℓ b u ψ)
          = fun u : EuclideanSpace ℝ (Fin 3) =>
              (b * ℓ ^ (-2 : ℤ)) * Work.BoseKinLoc.gapBare ℓ u ψ from rfl]
      exact integral_const_mul _ _
    have hbb : b * ℓ ^ (-2 : ℤ) ≠ 0 := by
      have h : (0:ℝ) < ℓ ^ (-2 : ℤ) := by positivity
      exact mul_ne_zero (ne_of_gt hb) (ne_of_gt h)
    have hIntBare : Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseKinLoc.gapBare ℓ u ψ) := by
      have h0 := hGint.const_mul ((b * ℓ ^ (-2 : ℤ))⁻¹)
      refine h0.congr (ae_of_all _ (fun u => ?_))
      show (b * ℓ ^ (-2 : ℤ))⁻¹ * Work.BoseKinLoc.gapWord ℓ b u ψ
        = Work.BoseKinLoc.gapBare ℓ u ψ
      simp only [Work.BoseKinLoc.gapWord]
      rw [← mul_assoc, inv_mul_cancel₀ hbb, one_mul]
    have h2 := hgap ψ hψ hcs ℓ hℓ hIntBare
    rw [h1]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hM_bound : (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.momWord ℓ d εT b u ψ)
      ≤ εT * (d * ℓ) ^ (-2 : ℤ) * ((1 / 2) * Work.BoseKinLoc.raFrac ℓ d ψ) := by
    have h1 : (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.momWord ℓ d εT b u ψ)
        = (b * εT * (d * ℓ) ^ (-2 : ℤ)) * (∫ u : EuclideanSpace ℝ (Fin 3),
            Work.BoseKinLoc.momForm ℓ d u ψ) := by
      rw [show (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseKinLoc.momWord ℓ d εT b u ψ)
          = fun u : EuclideanSpace ℝ (Fin 3) =>
              (b * εT * (d * ℓ) ^ (-2 : ℤ)) * Work.BoseKinLoc.momForm ℓ d u ψ from rfl]
      exact integral_const_mul _ _
    have hco : b * εT * (d * ℓ) ^ (-2 : ℤ) ≠ 0 := by
      have h : (0:ℝ) < (d * ℓ) ^ (-2 : ℤ) := by positivity
      exact mul_ne_zero (mul_ne_zero (ne_of_gt hb) (ne_of_gt hεT)) (ne_of_gt h)
    have hIntForm : Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseKinLoc.momForm ℓ d u ψ) := by
      have h0 := hMint.const_mul ((b * εT * (d * ℓ) ^ (-2 : ℤ))⁻¹)
      refine h0.congr (ae_of_all _ (fun u => ?_))
      show (b * εT * (d * ℓ) ^ (-2 : ℤ))⁻¹ * Work.BoseKinLoc.momWord ℓ d εT b u ψ
        = Work.BoseKinLoc.momForm ℓ d u ψ
      simp only [Work.BoseKinLoc.momWord]
      rw [← mul_assoc, inv_mul_cancel₀ hco, one_mul]
    have h2 : b * (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.momForm ℓ d u ψ)
        ≤ (1 / 2) * Work.BoseKinLoc.raFrac ℓ d ψ :=
      hmom b hb hbb₀ ψ hψ hcs ℓ d hℓ hd hd1 hIntForm
    rw [h1]
    have h3 : b * εT * (d * ℓ) ^ (-2 : ℤ) * (∫ u : EuclideanSpace ℝ (Fin 3),
          Work.BoseKinLoc.momForm ℓ d u ψ)
        = εT * (d * ℓ) ^ (-2 : ℤ) * (b * (∫ u : EuclideanSpace ℝ (Fin 3),
            Work.BoseKinLoc.momForm ℓ d u ψ)) := by ring
    rw [h3]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hP_bound : (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.mainWord ℓ d s εT u ψ)
      ≤ (1 - εT) * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
            Work.BoseKinLoc.tprSym ℓ (2 * s) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)
          + εT * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
            Work.BoseKinLoc.tprSym ℓ (2 * (d * s)) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2) := by
    have hcoef1 : (2 * (s * ℓ))⁻¹ = ((2 * s) * ℓ)⁻¹ := by congr 1; ring
    have hcoef2 : (2 * (d * s * ℓ))⁻¹ = ((2 * (d * s)) * ℓ)⁻¹ := by congr 1; ring
    have hB0 : Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff 0) u ψ) :=
      Work.BSKinetic.integrable_bsOneBody_fsKinCoeff_zero (ne_of_gt hℓ) hψ hcs
    have hmono1 : ∀ u : EuclideanSpace ℝ (Fin 3), Work.BSKinetic.bsOneBody ℓ
        (Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹)) u ψ
        ≤ Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff 0) u ψ := by
      intro u
      exact Work.BSKinetic.bsOneBody_mono_coeff
        (fun r => Submission.BoseGases.fsKinCoeff_nonneg _ r)
        (fun r => Work.BSKinetic.fsKinCoeff_zero_le (by positivity) r)
        (Work.BSKinetic.integrable_bsKinWeight_zero u hψ hcs)
    have hB1int : Integrable (fun u : EuclideanSpace ℝ (Fin 3) => Work.BSKinetic.bsOneBody ℓ
        (Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹)) u ψ) :=
      hB0.mono' ((Work.BSKinetic.Decomp.continuous_bsOneBody hℓ _ ψ hψ hcs).aestronglyMeasurable)
        (ae_of_all _ (fun u => by
          rw [Real.norm_of_nonneg (Work.BSKinetic.bsOneBody_nonneg
            (fun r => Submission.BoseGases.fsKinCoeff_nonneg _ r) u ψ)]
          exact hmono1 u))
    have hmono2 : ∀ u : EuclideanSpace ℝ (Fin 3), Work.BSKinetic.bsOneBody ℓ
        (Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹)) u ψ
        ≤ Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff 0) u ψ := by
      intro u
      exact Work.BSKinetic.bsOneBody_mono_coeff
        (fun r => Submission.BoseGases.fsKinCoeff_nonneg _ r)
        (fun r => Work.BSKinetic.fsKinCoeff_zero_le (by positivity) r)
        (Work.BSKinetic.integrable_bsKinWeight_zero u hψ hcs)
    have hB2int : Integrable (fun u : EuclideanSpace ℝ (Fin 3) => Work.BSKinetic.bsOneBody ℓ
        (Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹)) u ψ) :=
      hB0.mono' ((Work.BSKinetic.Decomp.continuous_bsOneBody hℓ _ ψ hψ hcs).aestronglyMeasurable)
        (ae_of_all _ (fun u => by
          rw [Real.norm_of_nonneg (Work.BSKinetic.bsOneBody_nonneg
            (fun r => Submission.BoseGases.fsKinCoeff_nonneg _ r) u ψ)]
          exact hmono2 u))
    have hmainEq : (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseKinLoc.mainWord ℓ d s εT u ψ)
        = fun u : EuclideanSpace ℝ (Fin 3) =>
            (1 - εT) * Work.BSKinetic.bsOneBody ℓ
                (Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹)) u ψ
              + εT * Work.BSKinetic.bsOneBody ℓ
                (Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹)) u ψ := rfl
    have hs1 : Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
        (1 - εT) * Work.BSKinetic.bsOneBody ℓ
          (Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹)) u ψ) := hB1int.const_mul _
    have hs2 : Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
        εT * Work.BSKinetic.bsOneBody ℓ
          (Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹)) u ψ) := hB2int.const_mul _
    have hsplitmain : (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.mainWord ℓ d s εT u ψ)
        = (1 - εT) * (∫ u : EuclideanSpace ℝ (Fin 3), Work.BSKinetic.bsOneBody ℓ
              (Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹)) u ψ)
          + εT * (∫ u : EuclideanSpace ℝ (Fin 3), Work.BSKinetic.bsOneBody ℓ
              (Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹)) u ψ) := by
      rw [hmainEq, integral_add hs1 hs2, integral_const_mul, integral_const_mul]
    have hB1'int : Integrable (fun u : EuclideanSpace ℝ (Fin 3) => Work.BSKinetic.bsOneBody ℓ
        (Submission.BoseGases.fsKinCoeff (((2 * s) * ℓ)⁻¹)) u ψ) :=
      hB1int.congr (ae_of_all _ (fun u => by rw [hcoef1]))
    have hB2'int : Integrable (fun u : EuclideanSpace ℝ (Fin 3) => Work.BSKinetic.bsOneBody ℓ
        (Submission.BoseGases.fsKinCoeff (((2 * (d * s)) * ℓ)⁻¹)) u ψ) :=
      hB2int.congr (ae_of_all _ (fun u => by rw [hcoef2]))
    have ht1 := htpr (2 * s) (by linarith) hs2s₀ ψ hψ hcs ℓ hℓ hB1'int
    have ht2 := htpr (2 * (d * s)) (by positivity) h2ds₀ ψ hψ hcs ℓ hℓ hB2'int
    have ht1' : (∫ u : EuclideanSpace ℝ (Fin 3), Work.BSKinetic.bsOneBody ℓ
          (Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹)) u ψ)
        ≤ ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
            Work.BoseKinLoc.tprSym ℓ (2 * s) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2 := by
      rw [← hcoef1] at ht1; exact ht1
    have ht2' : (∫ u : EuclideanSpace ℝ (Fin 3), Work.BSKinetic.bsOneBody ℓ
          (Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹)) u ψ)
        ≤ ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
            Work.BoseKinLoc.tprSym ℓ (2 * (d * s)) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2 := by
      rw [← hcoef2] at ht2; exact ht2
    rw [hsplitmain]
    exact add_le_add (mul_le_mul_of_nonneg_left ht1' (by linarith))
      (mul_le_mul_of_nonneg_left ht2' (by linarith))
  -- assemble
  have hsum : (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.fsT ℓ d s εT b u ψ)
      ≤ (1 / 2) * (εT * (d * ℓ) ^ (-2 : ℤ)) * Work.BoseKinLoc.raFrac ℓ d ψ
        + b * ℓ ^ (-2 : ℤ) * Work.BoseKinLoc.gapFrac ℓ β ψ
        + (1 / 2) * (εT * (d * ℓ) ^ (-2 : ℤ)) * Work.BoseKinLoc.raFrac ℓ d ψ
        + ((1 - εT) * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
              Work.BoseKinLoc.tprSym ℓ (2 * s) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)
            + εT * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
              Work.BoseKinLoc.tprSym ℓ (2 * (d * s)) C p * ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2)) := by
    rw [hsplit]
    have key1 : b * (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.momForm ℓ d u ψ)
        ≤ (1 / 2) * Work.BoseKinLoc.raFrac ℓ d ψ :=
      hmom b hb hbb₀ ψ hψ hcs ℓ d hℓ hd hd1
        (by
          have hco : b * εT * (d * ℓ) ^ (-2 : ℤ) ≠ 0 := by
            have h : (0:ℝ) < (d * ℓ) ^ (-2 : ℤ) := by positivity
            exact mul_ne_zero (mul_ne_zero (ne_of_gt hb) (ne_of_gt hεT)) (ne_of_gt h)
          have h0 := hMint.const_mul ((b * εT * (d * ℓ) ^ (-2 : ℤ))⁻¹)
          refine h0.congr (ae_of_all _ (fun u => ?_))
          show (b * εT * (d * ℓ) ^ (-2 : ℤ))⁻¹ * Work.BoseKinLoc.momWord ℓ d εT b u ψ
            = Work.BoseKinLoc.momForm ℓ d u ψ
          simp only [Work.BoseKinLoc.momWord]
          rw [← mul_assoc, inv_mul_cancel₀ hco, one_mul])
    linarith [hA_bound, hG_bound, hM_bound, hP_bound, key1]
  exact le_trans hsum (budget_le_dSpace hβ hC hℓ hd hs hεT.le hεT1 hb.le hψ hcs hbud hT1 hT2)

end Work.BoseKinLoc.Kinetic
