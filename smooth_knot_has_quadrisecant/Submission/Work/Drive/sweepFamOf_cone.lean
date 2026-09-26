import Mathlib
import Submission.Work.Drive.sweepFamOf
import Submission.Work.Drive.halfspace_of_doubleBlur
import Submission.Work.Drive.chordSweepDefs
import Submission.Work.Drive.avgChordOf_eq_inner_sweepFamOf

namespace Work.Drive

open scoped Real Topology intervalIntegral
open LeanEval.KnotTheory.Quadrisecant

/-- **The double bump-blur of a loop inherits a cone.**  If `Γ` is continuous and on the box
`|s-σ| ≤ ε`, `|t-t₀| ≤ ε` the loop grows at least at rate `c` in a fixed direction `n`
(`c*(t₂-t₁) ≤ ⟪n, Γ s t₂ - Γ s t₁⟫` for `t₀-ε ≤ t₁ ≤ t₂ ≤ t₀+ε`, `s ∈ [σ-ε,σ+ε]`), then the
double bump-blur `Work.Drive.sweepFamOf Γ δ₁ δ₂ σ` — convolution in the loop parameter (width `δ₁`)
and in the sweep parameter (width `δ₂`) against the nonnegative unit-mass bump
`Work.Drive.sweepBump` supported in `[-1,1]` — inherits the *same* direction and the *same* rate on
the shrunken `t`-window `[t₀-ε+δ₁, t₀+ε-δ₁]`, provided `δ₂ ≤ ε` (so `σ - δ₂v ∈ [σ-ε,σ+ε]` for
`|v| ≤ 1`), `0 ≤ δ₁`, `0 ≤ δ₂`.  The continuity hypothesis is used only to make the interval
integrals meaningful.

Proof route for the prover: two applications of `intervalIntegral.integral_sub` give
`Φ t₂ - Φ t₁ = ∫v, b v • ∫u, b u • (Γ (σ-δ₂v) (t₂-δ₁u) - Γ (σ-δ₂v) (t₁-δ₁u))` for
`Φ := sweepFamOf Γ δ₁ δ₂ σ`; `Work.Drive.inner_intervalIntegral_smul` (twice) moves `⟪n, ·⟫`
inside; apply the cone hypothesis at `t₁-δ₁u`, `t₂-δ₁u` (they lie in `[t₀-ε, t₀+ε]` because
`|t_i - t₀| ≤ ε - δ₁` and `|u| ≤ 1`); `Work.Drive.integral_bump_mul_ge` (twice, using
`(∫ u in (-1)..1, sweepBump u) = 1` — see `Work.Drive.sweepBump_integral`) turns the weighted
average into `c*(t₂-t₁)`.  Compare `Work.Drive.velNz_*` in `sweepFamVelNz.lean`, which does the
same computation for `Γ = sweepLoopChamfer` (and `Work.Drive.avgChordOf_eq_inner_sweepFamOf`). -/
theorem sweepFamOf_cone {Γ : ℝ → ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hΓ : Continuous (fun p : ℝ × ℝ => Γ p.1 p.2))
    {σ t₀ ε c δ₁ δ₂ : ℝ} {n : LeanEval.KnotTheory.Quadrisecant.Space}
    (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂) (hδ₂ε : δ₂ ≤ ε)
    (hcone : ∀ s ∈ Set.Icc (σ - ε) (σ + ε), ∀ t₁ t₂ : ℝ, t₀ - ε ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ t₀ + ε →
      c * (t₂ - t₁) ≤ inner ℝ n (Γ s t₂ - Γ s t₁)) :
    ∀ t₁ t₂ : ℝ, t₀ - ε + δ₁ ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ t₀ + ε - δ₁ →
      c * (t₂ - t₁) ≤ inner ℝ n (Work.Drive.sweepFamOf Γ δ₁ δ₂ σ t₂
        - Work.Drive.sweepFamOf Γ δ₁ δ₂ σ t₁) := by
  intro t₁ t₂ ht₁ ht₂ ht₃
  set g : ℝ := t₂ - t₁ with hgdef
  have hg : 0 ≤ g := by rw [hgdef]; linarith
  have hgt : t₁ + g = t₂ := by rw [hgdef]; ring
  -- The difference of the two blurred slices is the box average of the `n`-chords.
  have hbridge := avgChordOf_eq_inner_sweepFamOf Γ hΓ δ₁ δ₂ σ n t₁ g
  rw [hgt] at hbridge
  rw [← hbridge]
  -- The cone hypothesis, averaged twice against the bump, gives the box average bound.
  have hAvg : c * g ≤ avgChordOf Γ δ₁ δ₂ σ n t₁ g := by
    rw [avgChordOf]
    refine integral_bump_mul_ge sweepBump_cont' ?_ (fun v _ => sweepBump_nonneg' v)
      sweepBump_integral ?_
    · -- continuity in `v` of the inner weighted average (parametric interval integral)
      refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (μ := MeasureTheory.volume)
        (f := fun (v : ℝ) (u : ℝ) => sweepBump u * inner ℝ n
          (Γ (σ - δ₂ * v) (t₁ + g - δ₁ * u) - Γ (σ - δ₂ * v) (t₁ - δ₁ * u))) ?_ (-1) 1
      show Continuous (fun p : ℝ × ℝ => sweepBump p.2 * inner ℝ n
        (Γ (σ - δ₂ * p.1) (t₁ + g - δ₁ * p.2) - Γ (σ - δ₂ * p.1) (t₁ - δ₁ * p.2)))
      exact (sweepBump_cont'.comp continuous_snd).mul
        (continuous_inner.comp (continuous_const.prodMk
          ((hΓ.comp (by fun_prop : Continuous fun p : ℝ × ℝ =>
              (σ - δ₂ * p.1, t₁ + g - δ₁ * p.2))).sub
           (hΓ.comp (by fun_prop : Continuous fun p : ℝ × ℝ =>
              (σ - δ₂ * p.1, t₁ - δ₁ * p.2))))))
    · -- the bound `c * g ≤ g u` is pointwise in `u`, hence survives the inner average
      intro v hv
      refine integral_bump_mul_ge sweepBump_cont' ?_ (fun u _ => sweepBump_nonneg' u)
        sweepBump_integral ?_
      · exact continuous_inner.comp (continuous_const.prodMk
          ((hΓ.comp (by fun_prop : Continuous fun u : ℝ =>
              (σ - δ₂ * v, t₁ + g - δ₁ * u))).sub
           (hΓ.comp (by fun_prop : Continuous fun u : ℝ =>
              (σ - δ₂ * v, t₁ - δ₁ * u)))))
      · intro u hu
        rw [Set.mem_Icc] at hv hu
        -- the sweep parameter stays in the `s`-window
        have hvσ : σ - δ₂ * v ∈ Set.Icc (σ - ε) (σ + ε) := by
          rw [Set.mem_Icc]
          have hεv : δ₂ * v ≤ ε := le_trans (mul_le_of_le_one_right hδ₂ hv.2) hδ₂ε
          have hvn : -ε ≤ δ₂ * v := by
            have h1 : -δ₂ ≤ δ₂ * v := by
              simpa using mul_le_mul_of_nonneg_left hv.1 hδ₂
            linarith
          exact ⟨by linarith, by linarith⟩
        -- the two loop parameters stay in the `t`-window
        have hA : t₀ - ε ≤ t₁ - δ₁ * u := by
          have hu₁ : δ₁ * u ≤ δ₁ := mul_le_of_le_one_right hδ₁ hu.2
          linarith
        have hB : t₁ - δ₁ * u ≤ t₁ + g - δ₁ * u := by linarith
        have hC : t₁ + g - δ₁ * u ≤ t₀ + ε := by
          rw [hgt]
          nlinarith [ht₃, hδ₁, hu.1]
        have hkey := hcone (σ - δ₂ * v) hvσ (t₁ - δ₁ * u) (t₁ + g - δ₁ * u) hA hB hC
        have hsub : (t₁ + g - δ₁ * u) - (t₁ - δ₁ * u) = g := by ring
        rwa [hsub] at hkey
  exact hAvg

end Work.Drive
