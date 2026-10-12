import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.pinDirChiExp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.oneBodySplit`

The one-body windowed Dirichlet word of an arbitrary smooth one-body state `ψ` is dominated by
the localised kinetic word `fsT ℓ d s εT b 0 ψ` of FS `eq:DefT` *with coefficient `4`* plus the
box `L²`-mass of `ψ`, with the **explicit** mass coefficient

    `16·κ·chiPlateau² + 24·D²`,

`κ = (1−εT)(2sℓ)⁻² + εT(2dsℓ)⁻²` being the two-cut-off constant of `mainWord` and `D` an explicit
bound on the derivative of the window `chiScale ℓ` (a hypothesis, so that no per-`ℓ`
`Classical.choose` can hide in the constant).

This is the *one-body* (non-slot) form of `Work.BoseBoxFock.pinDirChiExp`, and it is the exact
combination of the four ingredients that `pinDirChiExp.chiSqDirichletFsTExp` assembles, with the
final arithmetic regrouped so that `fsT` carries the coefficient `4` alone:

* `chiSqGrad_le_two_dirichletExp` — the product rule integrated at the box mean, with the
  derivative constant `D` exposed:
  `LHS ≤ 2·bsOneBody ℓ (·)² 0 ψ + 6·D²·∫_{boxL}(ψ − m)²`;
* `chiSqDirichletFsT_half_le_mainWord` — the two cut-offs of `mainWord` pay for the Dirichlet
  word: `½·bsOneBody ℓ (·)² 0 ψ ≤ mainWord + κ·∫(χ·(ψ−m))²`;
* `chiSqDirichletFsT_mainWord_le_fsT` — the other three words of `fsT` are `≥ 0`;
* `chiSqDirichletFsT_windowMass_le` — `∫(χ·(ψ−m))² ≤ chiPlateau²·∫_{boxL}(ψ−m)²`;
* `boxMeanSub_sq_integral_le` — `∫_{boxL}(ψ−m)² ≤ 4∫_{boxL}ψ²`.

Chaining: `LHS ≤ 2·bsOneBody + 6D²V ≤ 4·mainWord + 4κ·∫(χ(ψ−m))² + 6D²V ≤ 4·fsT + 16κP²S + 24D²S`.
-/

namespace Work.BoseBoxFock.PCFU

set_option maxHeartbeats 1000000

theorem oneBodySplit {ℓ d s εT b D : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hs : 0 < s) (hb : 0 ≤ b)
    (hεT0 : 0 ≤ εT) (hεT1 : εT ≤ 1) (hD0 : 0 ≤ D)
    (hD : ∀ x v : EuclideanSpace ℝ (Fin 3),
      |fderiv ℝ (Submission.BoseGases.chiScale ℓ) x v| ≤ D * ‖v‖) :
    ∀ ψ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      (∫ z in Work.BoseK15.corpusBox.boxL ℓ,
          (Submission.BoseGases.chiScale ℓ z) ^ 2 *
            (∑ j : Fin 3, (fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis j)) ^ 2))
        ≤ 4 * Work.BoseKinLoc.fsT ℓ d s εT b 0 ψ
          + (16 * ((1 - εT) * ((2 * (s * ℓ))⁻¹) ^ 2 + εT * ((2 * (d * s * ℓ))⁻¹) ^ 2)
                * Work.BoseFixB1S.chiPlateau ^ 2 + 24 * D ^ 2)
            * (∫ z in Work.BoseK15.corpusBox.boxL ℓ, ψ z ^ 2) := by
  intro ψ hψ
  -- the standard basis vectors `kcStdBasis j` are `EuclideanSpace.single j 1`
  simp only [Submission.BoseGases.kcStdBasis]
  -- abbreviations for the atoms of the arithmetic
  set A : ℝ := (1 - εT) * ((2 * (s * ℓ))⁻¹) ^ 2 + εT * ((2 * (d * s * ℓ))⁻¹) ^ 2 with hAdef
  set P : ℝ := Work.BoseFixB1S.chiPlateau with hPdef
  set S : ℝ := ∫ z in Work.BoseK15.corpusBox.boxL ℓ, ψ z ^ 2 with hSdef
  set V : ℝ := ∫ z in Work.BoseK15.corpusBox.boxL ℓ,
    (ψ z - Work.BSKinetic.bsMean ℓ 0 ψ) ^ 2 with hVdef
  set Mb : ℝ := ∫ z : EuclideanSpace ℝ (Fin 3),
    (Work.BSKinetic.bsWin ℓ 0 z * Work.BSKinetic.bsQ ℓ 0 ψ z) ^ 2 with hMbdef
  set Dv : ℝ := Work.BSKinetic.bsOneBody ℓ (fun r => r ^ 2) 0 ψ with hDvdef
  set W : ℝ := Work.BoseKinLoc.mainWord ℓ d s εT 0 ψ with hWdef
  set T : ℝ := Work.BoseKinLoc.fsT ℓ d s εT b 0 ψ with hTdef
  -- the five input lemmas of the chain
  have hL := Work.BoseBoxFock.chiSqGrad_le_two_dirichletExp (l := ℓ) (D := D) hℓ hD0 hD hψ
  rw [← hDvdef, ← hVdef] at hL
  have hVar := Work.BoseBoxFock.boxMeanSub_sq_integral_le hℓ hψ
  rw [← hVdef, ← hSdef] at hVar
  have hE := Work.BoseBoxFock.chiSqDirichletFsT_half_le_mainWord (ℓ := ℓ) (d := d) (s := s)
    (εT := εT) hℓ hd hs hεT0 hεT1 hψ
  rw [← hWdef, ← hAdef, ← hMbdef, ← hDvdef] at hE
  have hF := Work.BoseBoxFock.chiSqDirichletFsT_mainWord_le_fsT (ℓ := ℓ) (d := d) (s := s)
    (εT := εT) (b := b) hℓ hd hs hb hεT0 hεT1 hψ
  rw [← hWdef, ← hTdef] at hF
  have hM := Work.BoseBoxFock.chiSqDirichletFsT_windowMass_le (ℓ := ℓ) hℓ hψ
  rw [← hMbdef, ← hPdef, ← hVdef] at hM
  -- the nonnegativity of the atoms that get multiplied
  have hAnn : 0 ≤ A := by
    rw [hAdef]
    have h1 : 0 ≤ 1 - εT := by linarith
    exact add_nonneg (mul_nonneg h1 (sq_nonneg _)) (mul_nonneg hεT0 (sq_nonneg _))
  have hP2 : 0 ≤ P ^ 2 := sq_nonneg P
  have hS0 : 0 ≤ S := by rw [hSdef]; exact MeasureTheory.integral_nonneg (fun z => sq_nonneg _)
  -- the arithmetic chain
  have hE2 : Dv ≤ 2 * W + 2 * A * Mb := by linarith [hE]
  have hA3 : 4 * A * Mb ≤ 4 * A * (P ^ 2 * V) :=
    mul_le_mul_of_nonneg_left (by linarith [hM]) (by linarith [hAnn] : (0:ℝ) ≤ 4 * A)
  have hA4 : 4 * A * (P ^ 2 * V) ≤ 4 * A * (P ^ 2 * (4 * S)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith [hVar]) hP2)
      (by linarith [hAnn] : (0:ℝ) ≤ 4 * A)
  have hA5 : 4 * A * Mb ≤ 16 * A * P ^ 2 * S := by
    have h35 : 4 * A * Mb ≤ 4 * A * (P ^ 2 * (4 * S)) := le_trans hA3 hA4
    have heq : 4 * A * (P ^ 2 * (4 * S)) = 16 * A * P ^ 2 * S := by ring
    linarith [h35, heq]
  have hB : 6 * D ^ 2 * V ≤ 24 * D ^ 2 * S := by
    have h6D : (0:ℝ) ≤ 6 * D ^ 2 := by nlinarith [hD0]
    have h0 : 6 * D ^ 2 * V ≤ 6 * D ^ 2 * (4 * S) :=
      mul_le_mul_of_nonneg_left (by linarith [hVar]) h6D
    have heq : 6 * D ^ 2 * (4 * S) = 24 * D ^ 2 * S := by ring
    linarith [h0, heq]
  have hgoal : (∫ z in Work.BoseK15.corpusBox.boxL ℓ,
        (Submission.BoseGases.chiScale ℓ z) ^ 2 *
          (∑ j : Fin 3, (fderiv ℝ ψ z (EuclideanSpace.single j (1:ℝ))) ^ 2))
      ≤ 4 * T + (16 * A * P ^ 2 + 24 * D ^ 2) * S := by
    nlinarith [hL, hE2, hF, hA5, hB]
  exact hgoal

end Work.BoseBoxFock.PCFU
