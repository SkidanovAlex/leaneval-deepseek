import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.OneBodyKin.bsMean_bsPair_eq_symbol
import Submission.Work.OneBodyKin.bsOneBody_eq_decomp
import Submission.Work.OneBodyKin.integrable_q_pieces
import Submission.Work.OneBodyKin.integrable_u_pieces
import Submission.Work.OneBodyKin.integral_bsMean_sq_eq_symbol
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.OneBodyKin.bsFamilyForm_eq_symbolIntegral` — the projected half of BS Lemma 3.3

This is the *assembly*: the projected moving-box family form

  `bsFamilyForm ℓ F ψ = ∫_u ⟨χ_u Q_{Λ(u)}ψ, F(√−Δ) χ_u Q_{Λ(u)}ψ⟩ du`

is diagonal in the `p`-convention Fourier transform with the explicit radial symbol
`famSym ℓ F q = symA ℓ F q − 2(2π)⁻³ boxHat ℓ q · symD ℓ F q + symC ℓ F q`
(`Work.OneBodyKin.Defs.famSym`):

  `bsFamilyForm ℓ F ψ = (2π)⁻³ ∫_q famSym ℓ F q · ‖kinFT ψ q‖² dq`.

## Structure of the proof

Write `m_u = bsMean ℓ u ψ` for the box mean and `Q_u = 1 − m_u` for the mean-free projection.
Pointwise in `u` the expansion `Q_uψ = ψ − m_u` gives

  `bsOneBody ℓ F u ψ = bsOneBodyUnproj ℓ F u ψ − 2 m_u · bsPair ℓ F u ψ + m_u² · bsPair ℓ F u 1`

(`Work.OneBodyKin.bsOneBody_eq_decomp`), and each of the three `u`-integrands is `L¹`
(`Work.OneBodyKin.integrable_u_pieces`), so the `u`-integral splits:

  `bsFamilyForm ℓ F ψ = bsFamilyFormUnproj ℓ F ψ − 2 ∫_u m_u bsPair ℓ F u ψ
      + ∫_u m_u² bsPair ℓ F u 1`.

The three pieces are then the *three symbols*:

* `bsFamilyFormUnproj ℓ F ψ = (2π)⁻³ ∫_q symA ℓ F q ‖kinFT ψ q‖²`
  (`bsFamilyFormUnproj_eq_symbol`);
* `∫_u m_u bsPair ℓ F u ψ = (2π)⁻⁶ ∫_q boxHat ℓ q · symD ℓ F q ‖kinFT ψ q‖²`
  (`bsMean_bsPair_eq_symbol`);
* `∫_u m_u² bsPair ℓ F u 1 = symA ℓ F 0 · ℓ³ · ∫_u m_u²
    = (2π)⁻³ ∫_q symC ℓ F q ‖kinFT ψ q‖²`
  (`bsPair_const_eq` + `integral_bsMean_sq_eq_symbol`).

Finally the three `q`-integrands are `L¹` (`Work.OneBodyKin.integrable_q_pieces`), so the
`q`-integral of the combination is the combination of the `q`-integrals, and `famSym` is by
definition exactly that combination.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.OneBodyKin

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

theorem bsFamilyForm_eq_symbolIntegral {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ → ℝ}
    (hFi : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖))
    (hFnn : ∀ r : ℝ, 0 ≤ F r) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    Work.BSKinetic.bsFamilyForm ℓ F ψ
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : EuclideanSpace ℝ (Fin 3),
          Work.OneBodyKin.famSym ℓ F q *
            ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z : ℂ)) q‖ ^ 2 := by
  -- ## the three pieces of the expansion, as functions of the box shift `u`
  set A : ℝ³ → ℝ := fun u => Work.BSKinetic.bsOneBodyUnproj ℓ F u ψ with hA
  set B : ℝ³ → ℝ := fun u => Work.BSKinetic.bsMean ℓ u ψ * Work.OneBodyKin.bsPair ℓ F u ψ with hB
  set C : ℝ³ → ℝ := fun u => (Work.BSKinetic.bsMean ℓ u ψ) ^ 2 *
      Work.OneBodyKin.bsPair ℓ F u (fun _ => 1) with hC
  obtain ⟨hAi, hBi, hCi⟩ := integrable_u_pieces hℓ hFi hFnn ψ hψ hcs
  have hAi' : MeasureTheory.Integrable A := by rw [hA]; exact hAi
  have hBi' : MeasureTheory.Integrable B := by rw [hB]; exact hBi
  have hCi' : MeasureTheory.Integrable C := by rw [hC]; exact hCi
  -- ## step 1: the pointwise expansion, and the split of the `u`-integral
  have hpoint : ∀ u : ℝ³, Work.BSKinetic.bsOneBody ℓ F u ψ = A u - 2 * B u + C u := by
    intro u
    rw [bsOneBody_eq_decomp hℓ hFi ψ hψ hcs u]
  have hsplit : Work.BSKinetic.bsFamilyForm ℓ F ψ
      = (∫ u : ℝ³, A u) - 2 * (∫ u : ℝ³, B u) + (∫ u : ℝ³, C u) := by
    rw [Work.BSKinetic.bsFamilyForm]
    calc (∫ u : ℝ³, Work.BSKinetic.bsOneBody ℓ F u ψ)
        = ∫ u : ℝ³, (A u - 2 * B u + C u) :=
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint)
      _ = (∫ u : ℝ³, (A u - 2 * B u)) + ∫ u : ℝ³, C u := by
          rw [MeasureTheory.integral_add]
          · exact hAi'.sub (hBi'.const_mul 2)
          · exact hCi'
      _ = ((∫ u : ℝ³, A u) - ∫ u : ℝ³, (2 * B u)) + ∫ u : ℝ³, C u := by
          rw [MeasureTheory.integral_sub hAi' (hBi'.const_mul 2)]
      _ = ((∫ u : ℝ³, A u) - 2 * (∫ u : ℝ³, B u)) + ∫ u : ℝ³, C u := by
          rw [MeasureTheory.integral_const_mul]
      _ = (∫ u : ℝ³, A u) - 2 * (∫ u : ℝ³, B u) + (∫ u : ℝ³, C u) := rfl
  -- ## step 2: the values of the three `u`-integrals
  have hAval : (∫ u : ℝ³, A u)
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : ℝ³, Work.OneBodyKin.symA ℓ F q *
          ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2 := by
    rw [hA]
    exact bsFamilyFormUnproj_eq_symbol hℓ hFi hFnn ψ hψ hcs
  have hBval : (∫ u : ℝ³, B u)
      = ((2 * Real.pi) ^ 3)⁻¹ * ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : ℝ³,
          Work.OneBodyKin.boxHat ℓ q * Work.OneBodyKin.symD ℓ F q *
            ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2 := by
    rw [hB]
    exact bsMean_bsPair_eq_symbol hℓ hFi ψ hψ hcs
  have hCval : (∫ u : ℝ³, C u)
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : ℝ³, Work.OneBodyKin.symC ℓ F q *
          ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2 := by
    -- the third term is a constant (`bsPair_const_eq`) times `m_u²`
    have hpt : ∀ u : ℝ³, C u = (Work.BSKinetic.bsMean ℓ u ψ) ^ 2 *
        (Work.OneBodyKin.symA ℓ F 0 * ℓ ^ 3) := by
      intro u
      simp only [hC]
      rw [bsPair_const_eq hℓ hFi u]
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
      MeasureTheory.integral_mul_const]
    rw [integral_bsMean_sq_eq_symbol hℓ ψ hψ hcs]
    -- `symC ℓ F q · W = symA ℓ F 0 · ℓ⁻⁶ · (boxHat ℓ q)² · W`: the constant comes out
    have h2 : (∫ q : ℝ³, Work.OneBodyKin.symC ℓ F q *
          ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2)
        = (Work.OneBodyKin.symA ℓ F 0 * (ℓ ^ 6)⁻¹) *
            ∫ q : ℝ³, (Work.OneBodyKin.boxHat ℓ q) ^ 2 *
              ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2 := by
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with q
      simp only [Work.OneBodyKin.symC]
      ring
    rw [h2]
    have hℓid : (ℓ ^ 9)⁻¹ * ℓ ^ 3 = (ℓ ^ 6)⁻¹ := by
      have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
      field_simp
    calc ((2 * Real.pi) ^ 3)⁻¹ * (ℓ ^ 9)⁻¹ *
            (∫ q : ℝ³, (Work.OneBodyKin.boxHat ℓ q) ^ 2 *
              ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2) *
            (Work.OneBodyKin.symA ℓ F 0 * ℓ ^ 3)
        = ((2 * Real.pi) ^ 3)⁻¹ * ((ℓ ^ 9)⁻¹ * ℓ ^ 3) *
            ((Work.OneBodyKin.symA ℓ F 0) *
              (∫ q : ℝ³, (Work.OneBodyKin.boxHat ℓ q) ^ 2 *
                ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2)) := by ring
      _ = ((2 * Real.pi) ^ 3)⁻¹ * (ℓ ^ 6)⁻¹ *
            ((Work.OneBodyKin.symA ℓ F 0) *
              (∫ q : ℝ³, (Work.OneBodyKin.boxHat ℓ q) ^ 2 *
                ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2)) := by rw [hℓid]
      _ = ((2 * Real.pi) ^ 3)⁻¹ * (Work.OneBodyKin.symA ℓ F 0 * (ℓ ^ 6)⁻¹ *
              (∫ q : ℝ³, (Work.OneBodyKin.boxHat ℓ q) ^ 2 *
                ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2)) := by ring
  -- ## step 3: the `q`-integral of the combination splits (the three `q`-integrands are `L¹`)
  have hmerge : (∫ q : ℝ³, Work.OneBodyKin.famSym ℓ F q *
        ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2)
      = (∫ q : ℝ³, Work.OneBodyKin.symA ℓ F q *
            ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2)
        - (2 * ((2 * Real.pi) ^ 3)⁻¹) * (∫ q : ℝ³, Work.OneBodyKin.boxHat ℓ q *
            Work.OneBodyKin.symD ℓ F q *
              ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2)
        + (∫ q : ℝ³, Work.OneBodyKin.symC ℓ F q *
              ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2) := by
    have hpt : ∀ q : ℝ³, Work.OneBodyKin.famSym ℓ F q *
        ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2
        = Work.OneBodyKin.symA ℓ F q * ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2
          - (2 * ((2 * Real.pi) ^ 3)⁻¹) * (Work.OneBodyKin.boxHat ℓ q * Work.OneBodyKin.symD ℓ F q *
              ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2)
          + Work.OneBodyKin.symC ℓ F q * ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2 := by
      intro q
      simp only [Work.OneBodyKin.famSym]
      ring
    obtain ⟨hgAi, hgBi, hgCi⟩ := integrable_q_pieces hℓ hFi hFnn ψ hψ hcs
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
    rw [MeasureTheory.integral_add]
    · rw [MeasureTheory.integral_sub]
      · rw [MeasureTheory.integral_const_mul]
      · exact hgAi
      · exact hgBi.const_mul _
    · exact hgAi.sub (hgBi.const_mul _)
    · exact hgCi
  -- ## step 4: algebra
  rw [hsplit, hAval, hBval, hCval, hmerge]
  ring

end Work.OneBodyKin
