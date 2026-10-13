/-
Auxiliary module for `Work.FTS.StrongPersist.N6Trans.T1SixAux.hardSlotSliceSixZero`.

The single-slot cut-off angular bound: for a cut-off `chi ζ` (vanishing off `[ζ/2, π/2-ζ/2]`,
identically `1` on `[ζ, π/2-ζ]`, with `|sin(2θ) ∂_θ χ| ≤ B`) and a fixed radius `z > 0`,

`|∫_θ χ·(sin(2θ)^{-q}·F·(D_θ V)·V)| ≤ (3/2)Kf·∫_θ V²sin(2θ)^{-q}
    + (Kf·B/2)·(∫_{(0,2ζ)} V²sin(2θ)^{-q} + ∫_{(π/2-2ζ,π/2)} V²sin(2θ)^{-q})`,

where `|F| ≤ Kf` and `|(1/2)sin(2θ)F' + (1-q)cos(2θ)F| ≤ (3/2)Kf` on `(0,π/2)`.

This is `Work.H2.T1Q.slotBound_cutoff` with its two hypotheses `hAint`/`hIBP` discharged by
`ibpCutoff_nonneg` (the `0 ≤ q` variant of the cut-off integration by parts), instantiated on
the slices `F = f z ·`, `V = Y z ·` with `δ = ζ/2`.  It is the per-cut-off-parameter estimate
of the exceptional (`q = 0`, i.e. `0 ≤ q ≤ 2`) slot of the level-six angular pairing; the
consuming lemma `hardSlotSliceSixZero` lets `ζ → 0⁺` (via dominated convergence and
`Work.H2.T1Q.ShrinkInt`) to remove the cut-off.
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.H2.T1Q.HardBoundQ
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.SixZeroAux.IbpCutoffNonneg

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.T1SixAux.SixZeroAux

set_option maxHeartbeats 1200000

theorem singleSlotCutBoundMine {q Kf B : ℝ} {z : ℝ} {f Y : ℝ → ℝ → ℝ} {chi : ℝ → ℝ → ℝ}
    (hq0 : 0 ≤ q) (hKf0 : 0 ≤ Kf) (hB0 : 0 ≤ B) (hz : 0 < z)
    (hχsm : ∀ ζ : ℝ, ContDiff ℝ (⊤ : ℕ∞) (chi ζ))
    (hχnn : ∀ ζ θ : ℝ, 0 ≤ chi ζ θ)
    (hχle : ∀ ζ θ : ℝ, chi ζ θ ≤ 1)
    (hχone : ∀ ζ θ : ℝ, 0 < ζ → ζ ≤ θ → θ ≤ π / 2 - ζ → chi ζ θ = 1)
    (hχz0l : ∀ ζ θ : ℝ, 0 < ζ → θ ≤ ζ / 2 → chi ζ θ = 0)
    (hχz0r : ∀ ζ θ : ℝ, 0 < ζ → π / 2 - ζ / 2 ≤ θ → chi ζ θ = 0)
    (hχd0l : ∀ ζ θ : ℝ, 0 < ζ → θ < ζ / 2 → deriv (chi ζ) θ = 0)
    (hχd0r : ∀ ζ θ : ℝ, 0 < ζ → π / 2 - ζ / 2 < θ → deriv (chi ζ) θ = 0)
    (hχbd : ∀ ζ : ℝ, 0 < ζ → ∀ θ : ℝ, |Real.sin (2 * θ) * deriv (chi ζ) θ| ≤ B)
    (hFcd : ContDiffOn ℝ 1 (fun θ => f z θ) (Set.Ioo 0 (π / 2)))
    (hVcd : ContDiffOn ℝ 1 (fun θ => Y z θ) (Set.Ioo 0 (π / 2)))
    (hFb : ∀ θ : ℝ, 0 < θ → θ < π / 2 → |f z θ| ≤ Kf)
    (hWq : ∀ θ : ℝ, 0 < θ → θ < π / 2 →
      |(1 / 2) * (Real.sin (2 * θ) * deriv (fun θ' => f z θ') θ)
        + (1 - q) * Real.cos (2 * θ) * f z θ| ≤ (3 / 2) * Kf)
    (hVint : MeasureTheory.IntegrableOn (fun θ => (Y z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
      Work.Spaces.Iθ)
    {ζ : ℝ} (hζ : 0 < ζ) (hζ4 : ζ ≤ 1 / 4) :
    |∫ θ in Work.Spaces.Iθ, chi ζ θ * ((Real.sin (2 * θ)) ^ (-q) * f z θ
        * Work.Spaces.Dth Y z θ * Y z θ)|
      ≤ (3 / 2) * Kf * (∫ θ in Work.Spaces.Iθ, (Y z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
        + (Kf * B / 2) * ((∫ θ in Set.Ioc 0 (2 * ζ), (Y z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
          + ∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2),
              (Y z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) := by
  have hζ2' : 2 * ζ ≤ π / 2 := by linarith [Real.pi_gt_three, hζ4]
  have hχmid : ∀ θ ∈ Set.Ioo ζ (π / 2 - ζ), deriv (chi ζ) θ = 0 := by
    intro θ hθ
    have hev : chi ζ =ᶠ[𝓝 θ] (fun _ => (1 : ℝ)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
      exact hχone ζ θ' hζ (le_of_lt hθ'.1) (le_of_lt hθ'.2)
    exact Work.H2.T1Q.deriv_eq_zero_of_eventuallyEq_one hev
  have hindnn : ∀ θ : ℝ, 0 ≤ (Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ
      + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ := by
    intro θ
    have ha : 0 ≤ (Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ := by
      by_cases hm : θ ∈ Set.Ioc 0 (2 * ζ)
      · simp [Set.indicator_of_mem hm]
      · simp [Set.indicator_of_notMem hm]
    have hb : 0 ≤ (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ := by
      by_cases hm : θ ∈ Set.Ioc (π / 2 - 2 * ζ) (π / 2)
      · simp [Set.indicator_of_mem hm]
      · simp [Set.indicator_of_notMem hm]
    linarith
  have hsd : ∀ θ ∈ Set.Ioo 0 (π / 2), |Real.sin (2 * θ) * deriv (chi ζ) θ|
      ≤ B * ((Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ
          + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ) := by
    intro θ hθ
    by_cases h1 : θ < ζ / 2
    · rw [hχd0l ζ θ hζ h1, mul_zero, abs_zero]
      exact mul_nonneg hB0 (hindnn θ)
    by_cases h2 : π / 2 - ζ / 2 < θ
    · rw [hχd0r ζ θ hζ h2, mul_zero, abs_zero]
      exact mul_nonneg hB0 (hindnn θ)
    by_cases h3 : θ ≤ 2 * ζ
    · have hA : θ ∈ Set.Ioc 0 (2 * ζ) := ⟨by linarith, h3⟩
      have hind : 1 ≤ (Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ
          + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ := by
        have ha : (Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ = 1 :=
          Set.indicator_of_mem hA _
        have hb : 0 ≤ (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator
            (fun _ => (1 : ℝ)) θ := by
          by_cases hm : θ ∈ Set.Ioc (π / 2 - 2 * ζ) (π / 2)
          · simp [Set.indicator_of_mem hm]
          · simp [Set.indicator_of_notMem hm]
        rw [ha]; linarith
      calc |Real.sin (2 * θ) * deriv (chi ζ) θ| ≤ B := hχbd ζ hζ θ
        _ = B * 1 := by ring
        _ ≤ B * ((Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ
              + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ) :=
            mul_le_mul_of_nonneg_left hind hB0
    · have h3' : 2 * ζ < θ := not_le.mp h3
      by_cases h4 : π / 2 - 2 * ζ < θ
      · have hA : θ ∈ Set.Ioc (π / 2 - 2 * ζ) (π / 2) :=
          ⟨h4, by linarith [not_lt.mp h2, Real.pi_pos]⟩
        have hind : 1 ≤ (Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ
            + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ := by
          have hb : (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ = 1 :=
            Set.indicator_of_mem hA _
          have ha : 0 ≤ (Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ := by
            by_cases hm : θ ∈ Set.Ioc 0 (2 * ζ)
            · simp [Set.indicator_of_mem hm]
            · simp [Set.indicator_of_notMem hm]
          rw [hb]; linarith
        calc |Real.sin (2 * θ) * deriv (chi ζ) θ| ≤ B := hχbd ζ hζ θ
          _ = B * 1 := by ring
          _ ≤ B * ((Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ
                + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ) :=
              mul_le_mul_of_nonneg_left hind hB0
      · have hmid : deriv (chi ζ) θ = 0 :=
          hχmid θ ⟨by linarith, by linarith [not_lt.mp h4]⟩
        rw [hmid, mul_zero, abs_zero]
        exact mul_nonneg hB0 (hindnn θ)
  have hFb' : ∀ θ ∈ Set.Ioo 0 (π / 2), |f z θ| ≤ Kf := fun θ hθ => hFb θ hθ.1 hθ.2
  have hWq' : ∀ θ ∈ Set.Ioo 0 (π / 2),
      |(1 / 2) * (Real.sin (2 * θ) * deriv (fun θ' => f z θ') θ)
        + (1 - q) * Real.cos (2 * θ) * f z θ| ≤ (3 / 2) * Kf :=
    fun θ hθ => hWq θ hθ.1 hθ.2
  have hIBP := Work.FTS.StrongPersist.N6Trans.T1SixAux.ibpCutoff_nonneg (q := q) (δ := ζ / 2)
    hq0 (χ := chi ζ) (hf := fun θ => f z θ) (hv := fun θ => Y z θ)
    (hχsm ζ) (by linarith) (by linarith [Real.pi_pos])
    (fun θ hθ => hχz0l ζ θ hζ hθ) (fun θ hθ => hχz0r ζ θ hζ hθ) hFcd hVcd
  have h := Work.H2.T1Q.slotBound_cutoff (q := q) (Kf := Kf) (B := B) (ζ := ζ)
    (χ := chi ζ) (F := fun θ => f z θ) (V := fun θ => Y z θ)
    hKf0 hB0 hζ hζ2' (fun θ => hχnn ζ θ) (fun θ => hχle ζ θ) hsd hFb' hWq' hVint
    hIBP.1 hIBP.2
  have hconv : (∫ θ in Work.Spaces.Iθ, chi ζ θ * ((Real.sin (2 * θ)) ^ (-q) * f z θ
        * Work.Spaces.Dth Y z θ * Y z θ))
      = ∫ θ in Work.Spaces.Iθ, chi ζ θ * (f z θ
          * (Real.sin (2 * θ) * deriv (fun θ' => Y z θ') θ) * Y z θ
          * (Real.sin (2 * θ)) ^ (-q)) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
    simp only [Work.Spaces.Dth, Work.Spaces.pth]
    ring
  rw [hconv]
  exact h

end Work.FTS.StrongPersist.N6Trans.T1SixAux.SixZeroAux
