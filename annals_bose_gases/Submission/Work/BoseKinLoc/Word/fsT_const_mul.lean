import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.NeuFrac.neuFrac_const_mul
import Submission.Work.BoseKinLoc.Word.bsOneBody_const_mul
import Submission.Work.BoseKinLoc.Word.momForm_const_mul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Word.fsT_const_mul` — the localised kinetic word is `2`-homogeneous

`Work.BoseKinLoc.fsT ℓ d s εT b u` (FS `eq:DefT`) is a **one-body quadratic form** in the
one-body state `ψ`: scaling `ψ ↦ c·ψ` scales the word by `c²`.  This file records the
homogeneity in the exact form the localisation assembly needs,

    `fsT ℓ d s εT b u (fun z => c * ψ z) = c ^ 2 * fsT ℓ d s εT b u ψ`,

by proving it for each of the four summands of FS `eq:DefT` (`fsT_eq_sum`):

* `gapWord` — the box-mean-free mass `∫_{Λ(u)}(Q_uψ)²` is quadratic because `Q_u = 1 − mean`
  and the box mean is linear (`bsQ_const_mul`, `gapBare_const_mul`);
* `momWord` — the large-momentum word `⟨1_{(d⁻²ℓ⁻¹,∞)}(√−Δ)⟩` is quadratic because the
  `p`-convention Fourier transform `kinFT` is linear (`Word.momForm_const_mul`);
* `mainWord` — the windowed `[√−Δ−c]₊²` word, i.e. `bsOneBody`, is quadratic for the same
  reason (`Word.bsOneBody_const_mul`);
* `neuWord` — the Neumann-resolvent fraction is an `sInf` over the smooth compactly
  supported trial functions `g`, a set which is stable under `g ↦ c·g`; the trial
  functional is exactly `2`-homogeneous in `(ϕ, g)`, so the infimum of the rescaled set is
  `c²` times the original one (`NeuFrac.neuFrac_const_mul`, whose `0 ≤ a²` hypothesis is
  what covers the degenerate `c = 0` case: then the trial values are nonnegative and `0`
  is attained).

None of the four steps needs any smoothness/support/integrability hypothesis on `ψ`: the
Bochner-integral identities used (`MeasureTheory.integral_const_mul`, linearity of `kinFT`)
are unconditional, and the junk convention for non-integrable integrands is itself
`2`-homogeneous.  The hypotheses `hψ`, `hcs` of the theorem are carried only because the
consumers state the word on smooth compactly supported states.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseKinLoc.Word

open Work.BoseKinLoc
open Work.BSKinetic

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. Linearity of the box mean and the mean-free projection -/

namespace FsTAux

/-- The moving-box mean is linear in the state. -/
lemma bsMean_const_mul (ℓ : ℝ) (u : ℝ³) (c : ℝ) (ψ : ℝ³ → ℝ) :
    bsMean ℓ u (fun z => c * ψ z) = c * bsMean ℓ u ψ := by
  unfold bsMean
  rw [MeasureTheory.integral_const_mul]
  ring

/-- The box-mean-free projection `Q_u = 1 − (box mean)` is linear in the state. -/
lemma bsQ_const_mul (ℓ : ℝ) (u : ℝ³) (c : ℝ) (ψ : ℝ³ → ℝ) :
    bsQ ℓ u (fun z => c * ψ z) = fun x => c * bsQ ℓ u ψ x := by
  funext x
  unfold bsQ
  rw [bsMean_const_mul]
  ring

/-- `Qfree` (the chapter's name for `bsQ`) is linear in the state. -/
lemma Qfree_const_mul (ℓ : ℝ) (u : ℝ³) (c : ℝ) (ψ : ℝ³ → ℝ) :
    Qfree ℓ u (fun z => c * ψ z) = fun x => c * Qfree ℓ u ψ x :=
  bsQ_const_mul ℓ u c ψ

/-! ## 2. The gap word -/

/-- The mean-free mass `∫_{Λ(u)}(Q_uψ)²` is quadratic in `ψ`. -/
lemma gapBare_const_mul (ℓ : ℝ) (u : ℝ³) (c : ℝ) (ψ : ℝ³ → ℝ) :
    gapBare ℓ u (fun z => c * ψ z) = c ^ 2 * gapBare ℓ u ψ := by
  unfold gapBare Qfree
  rw [bsQ_const_mul]
  simp only
  rw [show (∫ z in lamBox ℓ u, (c * bsQ ℓ u ψ z) ^ 2)
      = ∫ z in lamBox ℓ u, c ^ 2 * (bsQ ℓ u ψ z) ^ 2 from by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with z
    ring,
    MeasureTheory.integral_const_mul]

end FsTAux

open FsTAux

/-! ## 3. Assembly of the four summands of FS `eq:DefT` -/

theorem fsT_const_mul {ℓ d s εT b c : ℝ} (u : EuclideanSpace ℝ (Fin 3)) {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    Work.BoseKinLoc.fsT ℓ d s εT b u (fun z => c * ψ z) = c ^ 2 * Work.BoseKinLoc.fsT ℓ d s εT b u ψ := by
  have ha2 : 0 ≤ (d * ℓ) ^ (-2 : ℤ) := by
    rw [zpow_neg]
    exact inv_nonneg.mpr (sq_nonneg _)
  have hQ : Qfree ℓ u (fun z => c * ψ z) = fun z => c * Qfree ℓ u ψ z :=
    Qfree_const_mul ℓ u c ψ
  have hgap : gapWord ℓ b u (fun z => c * ψ z) = c ^ 2 * gapWord ℓ b u ψ := by
    unfold gapWord
    rw [gapBare_const_mul]
    ring
  have hmom : momWord ℓ d εT b u (fun z => c * ψ z) = c ^ 2 * momWord ℓ d εT b u ψ := by
    unfold momWord
    rw [momForm_const_mul u c ψ]
    ring
  have hmain : mainWord ℓ d s εT u (fun z => c * ψ z) = c ^ 2 * mainWord ℓ d s εT u ψ := by
    unfold mainWord
    rw [bsOneBody_const_mul (Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹)) u c ψ,
        bsOneBody_const_mul (Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹)) u c ψ]
    ring
  have hneu : neuWord ℓ d εT u (fun z => c * ψ z) = c ^ 2 * neuWord ℓ d εT u ψ := by
    unfold neuWord
    rw [hQ, NeuFrac.neuFrac_const_mul ha2 u (Qfree ℓ u ψ)]
    ring
  rw [fsT_eq_sum, fsT_eq_sum, hneu, hgap, hmom, hmain]
  ring

end Work.BoseKinLoc.Word
