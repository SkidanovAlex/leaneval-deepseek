/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The interior `C^{1,α}` estimate for `∂̄_{Jstd+A}` with a `C^{0,α}`-small perturbation

`Work.NN.Core.Lev.perturbed_C1a_L2_interior` proves the interior Schauder estimate for `∂̄_J`
under the hypothesis that the perturbation `A` is *componentwise* `C^{1,α}`-small on the outer
polydisc.  The target `Work.NN.Final.l2Solvability_core` (and every `L²`-route to it) only gives
`C^{0,α}`-smallness of `A`, so this file provides the same estimate under the weaker hypothesis.

The proof is a verbatim copy of the two-piece assembly of `perturbed_C1a_L2_interior`, with the
two pillars replaced by their level-`0` versions (already proved in the workspace):

* `Work.NN.Final.LevJ.supRemainderSchauder_v` — the classical interior Schauder estimate with a
  `sup` remainder, with componentwise `C^{0,α}`-smallness;
* `Work.NN.Final.LevJLoc.supEstimateL2_v` — the conversion of the `sup` of a solution into its
  `L²`-norm, again with `C^{0,α}`-smallness.

The conclusion is the statement reviewed and approved as
`Work.NN.Core.Lev.perturbed_C1a_L2_interior_C0`.
-/
import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Core.Defs
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Final.LevJ.SupRemainder
import Submission.Work.NN.Final.LevJLoc.SupEstimate

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set MeasureTheory

namespace Work.NN.Final

/-- **Auxiliary arithmetic of the two-piece assembly.** If `T ≤ S` and `U ≤ ofReal C₂ * (S + V)`,
then `ofReal C₁ * (T + U) ≤ ofReal (C₁ * (1 + C₂)) * (S + V)`. -/
private lemma ennreal_interp_arith_C0 {S V T U : ℝ≥0∞} {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁)
    (hC₂ : 0 ≤ C₂) (hT : T ≤ S) (hU : U ≤ ENNReal.ofReal C₂ * (S + V)) :
    ENNReal.ofReal C₁ * (T + U) ≤ ENNReal.ofReal (C₁ * (1 + C₂)) * (S + V) := by
  have h1 : T + U ≤ ENNReal.ofReal (1 + C₂) * (S + V) := by
    refine (add_le_add hT hU).trans ?_
    have hS : S ≤ S + V := le_add_right le_rfl
    calc S + ENNReal.ofReal C₂ * (S + V)
        = ENNReal.ofReal 1 * S + ENNReal.ofReal C₂ * (S + V) := by
          rw [ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal 1 * (S + V) + ENNReal.ofReal C₂ * (S + V) :=
          add_le_add (mul_le_mul' le_rfl hS) le_rfl
      _ = (ENNReal.ofReal 1 + ENNReal.ofReal C₂) * (S + V) := by rw [add_mul]
      _ = ENNReal.ofReal (1 + C₂) * (S + V) := by
          rw [ENNReal.ofReal_add zero_le_one hC₂]
  calc ENNReal.ofReal C₁ * (T + U)
      ≤ ENNReal.ofReal C₁ * (ENNReal.ofReal (1 + C₂) * (S + V)) := mul_le_mul' le_rfl h1
    _ = ENNReal.ofReal (C₁ * (1 + C₂)) * (S + V) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hC₁]

/-- **The interior `C^{1,α}`-estimate with an `L²`-remainder for `∂̄_{Jstd+A}`, `C^{0,α}`-small
perturbation.**  For positive nested multiradii `σ < ρ` (coordinatewise strict) there are
`ε₀ > 0` and `C > 0` such that, for every smooth field `A` which is `ε`-small
*componentwise in `C^{0,α}`* on `polydisc 0 ρ` with `ε ≤ ε₀` (and `J := JstdCn n + A` an almost
complex structure there), and every `u` of class `C¹` on `polydisc 0 ρ`,

  `‖u‖_{C^{1,α}(polydisc 0 σ)} ≤ C · ( Σ_j ‖(∂̄_J u)_j‖_{C^{0,α}(polydisc 0 ρ)}
      + ‖u‖_{L²(polydisc 0 ρ)} )`. -/
theorem perturbed_C1a_L2_interior_C0 {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {σ ρ : Fin n → ℝ} (hσ0 : ∀ j, 0 < σ j) (hρ0 : ∀ j, 0 < ρ j) (hσρ : ∀ j, σ j < ρ j) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ {A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n},
        (∀ m : ℕ, ContDiff ℝ m A) → ∀ {ε : ℝ}, ε ≤ ε₀ →
        (∀ i j : Fin n, Work.CR.Flat.holderNorm 0 α
            (fun z => A z (Pi.single i 1) j) (Work.CR.Flat.polydisc 0 ρ)
          ≤ ENNReal.ofReal ε) →
        (∀ z, z ∈ Work.CR.Flat.polydisc 0 ρ → ∀ v : Work.NN.Core.Cn n,
          (Work.NN.Core.JstdCn n + A) z ((Work.NN.Core.JstdCn n + A) z v) = -v) →
        ∀ u : Work.NN.Core.Cn n → ℂ,
          ContDiffOn ℝ 1 u (Work.CR.Flat.polydisc 0 ρ) →
          Work.CR.Flat.holderNorm 1 α u (Work.CR.Flat.polydisc 0 σ)
            ≤ ENNReal.ofReal C * ((∑ j : Fin n,
                  Work.CR.Flat.holderNorm 0 α
                    (fun z => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u z (Pi.single j 1))
                    (Work.CR.Flat.polydisc 0 ρ))
                + MeasureTheory.eLpNorm u 2
                    (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 ρ))) := by
  classical
  -- ### an intermediate polydisc `σ ⊂⊂ ρ'' ⊂⊂ ρ`
  set ρ'' : Fin n → ℝ := fun j => (σ j + ρ j) / 2 with hρ''def
  have hρ''0 : ∀ j, 0 < ρ'' j := fun j => by
    rw [hρ''def]; linarith [hσ0 j, hρ0 j]
  have hσρ'' : ∀ j, σ j < ρ'' j := fun j => by
    rw [hρ''def]; linarith [hσρ j]
  have hρ''ρ : ∀ j, ρ'' j < ρ j := fun j => by
    rw [hρ''def]; linarith [hσρ j]
  have hsub'' : Work.CR.Flat.polydisc 0 ρ'' ⊆ Work.CR.Flat.polydisc 0 ρ :=
    Work.CR.Flat.polydisc_mono (fun j => le_of_lt (hρ''ρ j))
  -- ### the two pillars, at Hölder level `0`
  obtain ⟨ε₁, hε₁, C₁, hC₁, H₁⟩ :=
    Work.NN.Final.LevJ.supRemainderSchauder_v (n := n) hn hα0 hα1
      (ρ := ρ'') (ρ' := σ) hρ''0 hσ0 hσρ''
  obtain ⟨ε₂, hε₂, C₂, hC₂, H₂⟩ :=
    Work.NN.Final.LevJLoc.supEstimateL2_v (n := n) hn hα0 hα1
      (σ := ρ'') (ρ := ρ) hρ''0 hρ0 hρ''ρ
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, C₁ * (1 + C₂), by positivity, ?_⟩
  intro A hA ε hε hsmall hJ u hu
  have hε₁' : ε ≤ ε₁ := le_trans hε (min_le_left _ _)
  have hε₂' : ε ≤ ε₂ := le_trans hε (min_le_right _ _)
  -- ### the smallness descends to `polydisc 0 ρ''`, and the almost-complexity restricts
  have hsmall'' : ∀ i j : Fin n, Work.CR.Flat.holderNorm 0 α
      (fun z => A z (Pi.single i 1) j) (Work.CR.Flat.polydisc 0 ρ'') ≤ ENNReal.ofReal ε :=
    fun i j => (Work.CR.Flat.holderNorm_mono_set (Work.CR.Flat.isOpen_polydisc 0 ρ)
      (Work.CR.Flat.isOpen_polydisc 0 ρ'') hsub'' 0 α _).trans (hsmall i j)
  have hJ'' : ∀ z, z ∈ Work.CR.Flat.polydisc 0 ρ'' → ∀ v : Work.NN.Core.Cn n,
      (Work.NN.Core.JstdCn n + A) z ((Work.NN.Core.JstdCn n + A) z v) = -v :=
    fun z hz v => hJ z (hsub'' hz) v
  -- ### the two estimates
  have hF := H₁ hA hε₁' hsmall'' hJ'' u (hu.mono hsub'')
  have hsup := H₂ hA hε₂' hsmall hJ u hu
  set S : ℝ≥0∞ := ∑ j : Fin n, Work.CR.Flat.holderNorm 0 α
    (fun z => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u z (Pi.single j 1))
    (Work.CR.Flat.polydisc 0 ρ) with hSdef
  set Z : ℝ≥0∞ := MeasureTheory.eLpNorm u 2
    (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 ρ)) with hZdef
  have hsum : (∑ j : Fin n, Work.CR.Flat.holderNorm 0 α
      (fun z => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u z (Pi.single j 1))
      (Work.CR.Flat.polydisc 0 ρ'')) ≤ S := by
    rw [hSdef]
    exact Finset.sum_le_sum fun j _ => Work.CR.Flat.holderNorm_mono_set
      (Work.CR.Flat.isOpen_polydisc 0 ρ) (Work.CR.Flat.isOpen_polydisc 0 ρ'') hsub'' 0 α _
  have hsup' : (⨆ z ∈ Work.CR.Flat.polydisc 0 ρ'', ENNReal.ofReal ‖u z‖)
      ≤ ENNReal.ofReal C₂ * (S + Z) := by
    rw [hSdef, hZdef]
    exact hsup
  calc Work.CR.Flat.holderNorm 1 α u (Work.CR.Flat.polydisc 0 σ)
      ≤ ENNReal.ofReal C₁ * ((∑ j : Fin n, Work.CR.Flat.holderNorm 0 α
            (fun z => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u z (Pi.single j 1))
            (Work.CR.Flat.polydisc 0 ρ''))
          + ⨆ z ∈ Work.CR.Flat.polydisc 0 ρ'', ENNReal.ofReal ‖u z‖) := hF
    _ ≤ ENNReal.ofReal (C₁ * (1 + C₂)) * (S + Z) :=
        ennreal_interp_arith_C0 (le_of_lt hC₁) (le_of_lt hC₂) hsum hsup'
    _ = ENNReal.ofReal (C₁ * (1 + C₂)) * ((∑ j : Fin n, Work.CR.Flat.holderNorm 0 α
            (fun z => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u z (Pi.single j 1))
            (Work.CR.Flat.polydisc 0 ρ))
          + MeasureTheory.eLpNorm u 2
              (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 ρ))) := by
        rw [hSdef, hZdef]

end Work.NN.Final
