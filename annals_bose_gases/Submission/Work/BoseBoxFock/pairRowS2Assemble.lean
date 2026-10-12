import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.blockTwo3_II1_Ksub_stateDir
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairRowS2Assemble` — the row-level (S2) substitution at the state hypotheses

This is the assembly of the (S2) step of `FINDING_PotPairRows_exists.md` §10.  The block-`I/II` part of
the `Q₂` row is, by `Work.BoseBoxFock.potPairRows_kernelExpanded`, exactly

    rowPairSubC (ℓ³)⁻¹ Θ A KI KII
      = (ℓ³)⁻¹ • Σ_p (block I shape at KI)
        + ((1/2)·(ℓ³)⁻¹) • ( Σ_p (block II.1 shape at KII) + Σ_p (block II.2 shape at KII) )

(the block III term is carried separately — it has no function kernel limit), where at the honest data
`KI = K1exp v μ N (k1cfun fu W₁ W₂ ℓ N)`, `KII = K1exp v μ N (uvCut·chat W₁)`,
`KI' = K1lim ℓ W₁'`, `KII' = K1lim ℓ W₂'`, `Θ = boxRestrictC ℓ Φ`, `A = pinCond v μ c`.

Here the substitution `KI → KI'`, `KII → KII'` is performed with *all* the state hypotheses of the
three block lemmas discharged (through `block13_Ksub_stateDir` and `blockTwo3_II1_Ksub_stateDir`, which
in turn use `pairG13_bounded`, `block13_inner_weak`, `pairG13_measurable`, `pairG_supports`,
`block13_pair_integrable`, `block13_inner_integrable`, `K1lim_mul_integrable`,
`K1lim_mul_integrable_slot`, `boxSmooth_fibres`).  The only inputs left are

* the two pairing bounds — at the honest data supplied verbatim by
  `Work.BoseBoxFock.K1exp_sub_K1lim_pairing_dirB` (once for the block-`I` weight `W₁ + W₂` with
  `W₁' = W₁ + W₂`, once for the block-`II` weight `W₁` with `W₂' = W₁`);
* measurability and boundedness of the two *truncated* kernels `KI`, `KII` (at the honest data
  `Work.BoseBoxFock.K1exp_meas_bdd`), and `L¹` of the two limit weights.

The conclusion is the sum of the six per-pair Dirichlet/mass roots; the final arithmetic of (S2)
bounds it by the state's content and picks `Nmin μ` from the pairing bound's `ε`.

`sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn

/-- **The (S2) substitution of the block-`I/II` part of the `Q₂` row**, at the state hypotheses, with
the two pairing bounds as the only analytic inputs. -/
theorem rowPairSubC_stateDir {n : ℕ} {ℓ ε₁ ε₂ : ℝ} (hℓ : 0 < ℓ)
    {Θ Θ₀ : Xn n → ℂ} {A : E3 → ℂ} {KI KII : E3 → E3 → ℂ} {W₁' W₂' : E3 → ℝ}
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n ℓ)
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀)
    (hΘind : ∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n ℓ) Θ₀ x)
    (hAm : Measurable A) (hAb : ∃ C : ℝ, ∀ x, ‖A x‖ ≤ C) (hCutA : CutSmooth1 ℓ A)
    (hKIm : Measurable (Function.uncurry KI)) (hKIb : ∃ C : ℝ, ∀ w y, ‖KI w y‖ ≤ C)
    (hKIIm : Measurable (Function.uncurry KII)) (hKIIb : ∃ C : ℝ, ∀ w y, ‖KII w y‖ ≤ C)
    (hWi₁ : MeasureTheory.Integrable W₁') (hWi₂ : MeasureTheory.Integrable W₂')
    (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂)
    (hPairI : ∀ G : E3 → E3 → ℂ, BoxSmooth ℓ G →
      ‖∫ w in Work.BoseK15.corpusBox.boxL ℓ,
         ∫ y in Work.BoseK15.corpusBox.boxL ℓ, (KI w y - K1lim ℓ W₁' w y) * G w y‖
        ≤ ε₁ * (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ G)
            + Real.sqrt (massBox ℓ G)))
    (hPairII : ∀ G : E3 → E3 → ℂ, BoxSmooth ℓ G →
      ‖∫ w in Work.BoseK15.corpusBox.boxL ℓ,
         ∫ y in Work.BoseK15.corpusBox.boxL ℓ, (KII w y - K1lim ℓ W₂' w y) * G w y‖
        ≤ ε₂ * (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ G)
            + Real.sqrt (massBox ℓ G))) :
    ‖rowPairSubC ((ℓ ^ 3)⁻¹) Θ A KI KII
        - rowPairSubC ((ℓ ^ 3)⁻¹) Θ A (K1lim ℓ W₁') (K1lim ℓ W₂')‖
      ≤ 2 * (ℓ ^ 3)⁻¹ * max ε₁ ε₂
          * ∑ p ∈ Submission.BoseGases.pairSet n,
              ((Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ (pairG13 p Θ A A))
                + Real.sqrt (massBox ℓ (pairG13 p Θ A A)))
              + (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ (pairG21 p Θ A))
                + Real.sqrt (massBox ℓ (pairG21 p Θ A)))
              + (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ (pairG23 p Θ A A))
                + Real.sqrt (massBox ℓ (pairG23 p Θ A A)))) := by
  classical
  have hmax0 : 0 ≤ max ε₁ ε₂ := le_trans hε₁ (le_max_left ε₁ ε₂)
  have h13 : ∀ p ∈ Submission.BoseGases.pairSet n,
      ‖rowShape13 Θ A A KI p - rowShape13 Θ A A (K1lim ℓ W₁') p‖
        ≤ max ε₁ ε₂ * (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ (pairG13 p Θ A A))
            + Real.sqrt (massBox ℓ (pairG13 p Θ A A))) := by
    intro p hp
    have hpne := mem_pairSet_iff.mp hp
    have hx : (0 : ℝ) ≤ Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ (pairG13 p Θ A A))
        + Real.sqrt (massBox ℓ (pairG13 p Θ A A)) := by positivity
    have h := block13_Ksub_stateDir p hpne hℓ hΘm hΘb hΘs hΘ₀ hΘind hAm hAb hAm hAb
      hCutA hCutA hKIm hKIb hWi₁ hmax0
      (fun G hG => le_trans (hPairI G hG) (mul_le_mul_of_nonneg_right (le_max_left ε₁ ε₂) (by positivity)))
    simpa only [rowShape13] using h
  have h23 : ∀ p ∈ Submission.BoseGases.pairSet n,
      ‖rowShape23 Θ A A KII p - rowShape23 Θ A A (K1lim ℓ W₂') p‖
        ≤ max ε₁ ε₂ * (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ (pairG23 p Θ A A))
            + Real.sqrt (massBox ℓ (pairG23 p Θ A A))) := by
    intro p hp
    have hpne := mem_pairSet_iff.mp hp
    have hx : (0 : ℝ) ≤ Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ (pairG23 p Θ A A))
        + Real.sqrt (massBox ℓ (pairG23 p Θ A A)) := by positivity
    have h := (blockTwo3_II1_Ksub_stateDir (l := ℓ) p hpne hℓ).1 (ε := max ε₁ ε₂)
      hΘm hΘb hΘs hΘ₀ hΘind hAm hAb hAm hAb hCutA hCutA hKIIm hKIIb hWi₂
      hmax0
      (fun G hG => le_trans (hPairII G hG) (mul_le_mul_of_nonneg_right (le_max_right ε₁ ε₂) (by positivity)))
    simpa only [rowShape23] using h
  have h21 : ∀ p ∈ Submission.BoseGases.pairSet n,
      ‖rowShape21 Θ A KII p - rowShape21 Θ A (K1lim ℓ W₂') p‖
        ≤ max ε₁ ε₂ * (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ (pairG21 p Θ A))
            + Real.sqrt (massBox ℓ (pairG21 p Θ A))) := by
    intro p hp
    have hpne := mem_pairSet_iff.mp hp
    have hx : (0 : ℝ) ≤ Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ (pairG21 p Θ A))
        + Real.sqrt (massBox ℓ (pairG21 p Θ A)) := by positivity
    have h := (blockTwo3_II1_Ksub_stateDir (l := ℓ) p hpne hℓ).2 (ε := max ε₁ ε₂)
      hΘm hΘb hΘs hΘ₀ hΘind hAm hAb hCutA hKIIm hKIIb hWi₂
      hmax0
      (fun G hG => le_trans (hPairII G hG) (mul_le_mul_of_nonneg_right (le_max_right ε₁ ε₂) (by positivity)))
    simpa only [rowShape21] using h
  have hmain := rowPairSubC_KsubDir (n := n) (ℓ := ℓ) (ε := max ε₁ ε₂) (a := (ℓ ^ 3)⁻¹)
    (Θ := Θ) (A := A) (KI := KI) (KI' := K1lim ℓ W₁') (KII := KII) (KII' := K1lim ℓ W₂')
    hmax0 h13 h21 h23
  rwa [abs_of_pos (inv_pos.mpr (pow_pos hℓ 3))] at hmain

end Work.BoseBoxFock
