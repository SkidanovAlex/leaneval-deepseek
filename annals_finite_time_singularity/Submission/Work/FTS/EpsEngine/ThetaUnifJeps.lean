/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/ThetaUnifJeps.lean`

`Work.FTS.EpsEngine.ThetaUnifJeps`: the **uniform angular flatness** `ThetaUnif α k` is preserved
by the log-coordinate mollifier `J_ε` (`Work.FTS.StrongEps.Jeps`).

`ThetaUnif α k f` is the two `ε`-`δ` conditions (`UnifTraceDefs`)

  `∀ θ → 0⁺, ∀ z > 0,  sin(2θ)^{1-γ} · (D_z^b D_θ^a f z θ)² ≤ ε'`,
  `∀ θ → (π/2)⁻, ∀ z > 0,  sin(2θ)^{1-γ} · (D_z^b D_θ^a f z θ)² ≤ ε'`,

*uniform in `z`*, for every slot `a + b ≤ k`.

The proof is the θ-half of `StrongEps.BdryTraces_Jeps`, with the `ε`-`δ` uniformity made explicit
(the hypothesis about `f` is already uniform in `z`, so nothing is lost).  The three ingredients
are the same:

* `J_ε` commutes with the mixed derivatives: `mixed b a (J_ε f) = J_ε (mixed b a f)` on the open
  quadrant (`StrongEps.mixed_Jeps`);
* `J_ε g` is a weighted average of the shifted values `g (z e^{-p₁}) (thShift θ p₂)` of `g`, hence
  bounded by any bound valid on the window `|p₁|, |p₂| ≤ ε` (`StrongEps.abs_Jeps_le_sup`);
* the angular weight at a shifted point differs from the weight at `θ` by at most
  `e^{ε|1-γ|}` (`Traces.sin_rpow_thShift_le`), and the shifted angles converge to the endpoints,
  uniformly in the shift (`Traces.eventually_thShift_{lt,gt}`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EpsEngine.UnifTraceDefs
import Submission.Work.FTS.StrongEps.BdryTraces_Jeps
import Submission.Work.FTS.StrongEps.axis_Jeps

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EpsEngine

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The `θ → 0⁺` half of `ThetaUnifJeps`.**  If `g` is uniformly `sin(2θ)^{1-γ}`-flat at `0⁺`
(uniformly in `z`), then so is the mollified profile `J_ε g`. -/
theorem jeps_thetaFlat_left {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {ε α : ℝ} (hε : 0 < ε) {g : ℝ → ℝ → ℝ}
    (hg : ∀ ε' > 0, ∃ δ > 0, ∀ θ : ℝ, 0 < θ → θ < δ → ∀ z : ℝ, 0 < z →
      Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (g z θ) ^ 2 ≤ ε') :
    ∀ ε' > 0, ∃ δ > 0, ∀ θ : ℝ, 0 < θ → θ < δ → ∀ z : ℝ, 0 < z →
      Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.FTS.StrongEps.Jeps ρ ε g z θ) ^ 2 ≤ ε' := by
  intro ε' hε'
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ :=
    hg (ε' / Real.exp (ε * |(1 - Work.Spaces.gam α)|)) (div_pos hε' (Real.exp_pos _))
  have hev : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ p : ℝ, |p| ≤ ε →
      Work.FTS.StrongEps.thShift θ p < δ₁ :=
    Work.FTS.StrongEps.Traces.eventually_thShift_lt ε δ₁ hδ₁pos
  rw [(nhdsGT_basis (0 : ℝ)).eventually_iff] at hev
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := hev
  refine ⟨min δ₂ (Real.pi / 4), lt_min hδ₂pos (by linarith [Real.pi_pos]), ?_⟩
  intro θ hθ hθδ z hz
  have hθδ₂ : θ < δ₂ := lt_of_lt_of_le hθδ (min_le_left _ _)
  have hθπ : θ < Real.pi / 2 := by
    have h := lt_of_lt_of_le hθδ (min_le_right _ _)
    linarith [Real.pi_pos]
  have hθmem : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ, hθπ⟩
  have hsE : 0 < Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
    Real.rpow_pos_of_pos (Work.FTS.StrongEps.sin_two_pos hθmem) _
  set M : ℝ := Real.sqrt (ε' / Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)) with hM
  have hMn : 0 ≤ M := Real.sqrt_nonneg _
  have hMsq : M ^ 2 = ε' / Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
    Real.sq_sqrt (div_nonneg hε'.le hsE.le)
  have hMb : ∀ p : ℝ × ℝ, |p.1| ≤ ε → |p.2| ≤ ε →
      |g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)| ≤ M := by
    intro p hp1 hp2
    have hz1 : 0 < Work.FTS.StrongEps.zShift z p.1 := Work.FTS.StrongEps.zShift_pos hz
    have hth : Work.FTS.StrongEps.thShift θ p.2 ∈ Set.Ioo 0 (Real.pi / 2) :=
      Work.FTS.StrongEps.thShift_mem hθmem
    have hthδ : Work.FTS.StrongEps.thShift θ p.2 < δ₁ := hδ₂ ⟨hθ, hθδ₂⟩ p.2 hp2
    have hhyp := hδ₁ (Work.FTS.StrongEps.thShift θ p.2) hth.1 hthδ
      (Work.FTS.StrongEps.zShift z p.1) hz1
    have hcmp := Work.FTS.StrongEps.Traces.sin_rpow_thShift_le θ p.2 ε
      (1 - Work.Spaces.gam α) hθmem hε.le hp2
    have hsq : (g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) ^ 2
        ≤ M ^ 2 := by
      rw [hMsq, le_div_iff₀ hsE]
      calc (g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) ^ 2
            * Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          ≤ (g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) ^ 2
              * (Real.exp (ε * |(1 - Work.Spaces.gam α)|)
                  * Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2)
                      ^ (1 - Work.Spaces.gam α)) :=
            mul_le_mul_of_nonneg_left hcmp (sq_nonneg _)
        _ = Real.exp (ε * |(1 - Work.Spaces.gam α)|)
              * (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2) ^ (1 - Work.Spaces.gam α)
                  * (g (Work.FTS.StrongEps.zShift z p.1)
                      (Work.FTS.StrongEps.thShift θ p.2)) ^ 2) := by ring
        _ ≤ Real.exp (ε * |(1 - Work.Spaces.gam α)|)
              * (ε' / Real.exp (ε * |(1 - Work.Spaces.gam α)|)) :=
            mul_le_mul_of_nonneg_left hhyp (Real.exp_pos _).le
        _ = ε' := by rw [mul_div_cancel₀ _ (Real.exp_pos _).ne']
    have hsq' : |g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)| ≤ |M| :=
      sq_le_sq.mp hsq
    rwa [abs_of_nonneg hMn] at hsq'
  have hjep : |Work.FTS.StrongEps.Jeps ρ ε g z θ| ≤ M :=
    Work.FTS.StrongEps.abs_Jeps_le_sup ρ hρ hε hz hθmem hMb hMn
  have hjsq : (Work.FTS.StrongEps.Jeps ρ ε g z θ) ^ 2 ≤ M ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hjep 2
  calc Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.FTS.StrongEps.Jeps ρ ε g z θ) ^ 2
      ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * M ^ 2 :=
        mul_le_mul_of_nonneg_left hjsq hsE.le
    _ = Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (ε' / Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)) := by rw [hMsq]
    _ = ε' := by rw [mul_div_cancel₀ _ hsE.ne']

/-- **The `θ → (π/2)⁻` half of `ThetaUnifJeps`** (the left-end statement with `θ ↦ π/2 - θ`). -/
theorem jeps_thetaFlat_right {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {ε α : ℝ} (hε : 0 < ε) {g : ℝ → ℝ → ℝ}
    (hg : ∀ ε' > 0, ∃ δ > 0, ∀ θ : ℝ, θ < Real.pi / 2 → Real.pi / 2 - δ < θ →
      ∀ z : ℝ, 0 < z →
      Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (g z θ) ^ 2 ≤ ε') :
    ∀ ε' > 0, ∃ δ > 0, ∀ θ : ℝ, θ < Real.pi / 2 → Real.pi / 2 - δ < θ →
      ∀ z : ℝ, 0 < z →
      Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.FTS.StrongEps.Jeps ρ ε g z θ) ^ 2 ≤ ε' := by
  intro ε' hε'
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ :=
    hg (ε' / Real.exp (ε * |(1 - Work.Spaces.gam α)|)) (div_pos hε' (Real.exp_pos _))
  have hev : ∀ᶠ θ in 𝓝[<] (Real.pi / 2), ∀ p : ℝ, |p| ≤ ε →
      Real.pi / 2 - δ₁ < Work.FTS.StrongEps.thShift θ p :=
    Work.FTS.StrongEps.Traces.eventually_thShift_gt ε δ₁ hδ₁pos
  rw [(nhdsLT_basis (Real.pi / 2)).eventually_iff] at hev
  obtain ⟨δ₂, hδ₂lt, hδ₂⟩ := hev
  refine ⟨min (Real.pi / 2 - δ₂) (Real.pi / 4),
    lt_min (by linarith) (by linarith [Real.pi_pos]), ?_⟩
  intro θ hθπ hθδ z hz
  have hθlo₂ : δ₂ < θ := by
    have h : δ₂ ≤ Real.pi / 2 - min (Real.pi / 2 - δ₂) (Real.pi / 4) := by
      linarith [min_le_left (Real.pi / 2 - δ₂) (Real.pi / 4)]
    linarith
  have hθpos : 0 < θ := by
    have h2 : min (Real.pi / 2 - δ₂) (Real.pi / 4) ≤ Real.pi / 4 := min_le_right _ _
    linarith [Real.pi_pos]
  have hθmem : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθpos, hθπ⟩
  have hsE : 0 < Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
    Real.rpow_pos_of_pos (Work.FTS.StrongEps.sin_two_pos hθmem) _
  set M : ℝ := Real.sqrt (ε' / Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)) with hM
  have hMn : 0 ≤ M := Real.sqrt_nonneg _
  have hMsq : M ^ 2 = ε' / Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
    Real.sq_sqrt (div_nonneg hε'.le hsE.le)
  have hMb : ∀ p : ℝ × ℝ, |p.1| ≤ ε → |p.2| ≤ ε →
      |g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)| ≤ M := by
    intro p hp1 hp2
    have hz1 : 0 < Work.FTS.StrongEps.zShift z p.1 := Work.FTS.StrongEps.zShift_pos hz
    have hth : Work.FTS.StrongEps.thShift θ p.2 ∈ Set.Ioo 0 (Real.pi / 2) :=
      Work.FTS.StrongEps.thShift_mem hθmem
    have hthδ : Real.pi / 2 - δ₁ < Work.FTS.StrongEps.thShift θ p.2 :=
      hδ₂ ⟨hθlo₂, hθπ⟩ p.2 hp2
    have hhyp := hδ₁ (Work.FTS.StrongEps.thShift θ p.2) hth.2 hthδ
      (Work.FTS.StrongEps.zShift z p.1) hz1
    have hcmp := Work.FTS.StrongEps.Traces.sin_rpow_thShift_le θ p.2 ε
      (1 - Work.Spaces.gam α) hθmem hε.le hp2
    have hsq : (g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) ^ 2
        ≤ M ^ 2 := by
      rw [hMsq, le_div_iff₀ hsE]
      calc (g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) ^ 2
            * Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          ≤ (g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) ^ 2
              * (Real.exp (ε * |(1 - Work.Spaces.gam α)|)
                  * Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2)
                      ^ (1 - Work.Spaces.gam α)) :=
            mul_le_mul_of_nonneg_left hcmp (sq_nonneg _)
        _ = Real.exp (ε * |(1 - Work.Spaces.gam α)|)
              * (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2) ^ (1 - Work.Spaces.gam α)
                  * (g (Work.FTS.StrongEps.zShift z p.1)
                      (Work.FTS.StrongEps.thShift θ p.2)) ^ 2) := by ring
        _ ≤ Real.exp (ε * |(1 - Work.Spaces.gam α)|)
              * (ε' / Real.exp (ε * |(1 - Work.Spaces.gam α)|)) :=
            mul_le_mul_of_nonneg_left hhyp (Real.exp_pos _).le
        _ = ε' := by rw [mul_div_cancel₀ _ (Real.exp_pos _).ne']
    have hsq' : |g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)| ≤ |M| :=
      sq_le_sq.mp hsq
    rwa [abs_of_nonneg hMn] at hsq'
  have hjep : |Work.FTS.StrongEps.Jeps ρ ε g z θ| ≤ M :=
    Work.FTS.StrongEps.abs_Jeps_le_sup ρ hρ hε hz hθmem hMb hMn
  have hjsq : (Work.FTS.StrongEps.Jeps ρ ε g z θ) ^ 2 ≤ M ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hjep 2
  calc Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.FTS.StrongEps.Jeps ρ ε g z θ) ^ 2
      ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * M ^ 2 :=
        mul_le_mul_of_nonneg_left hjsq hsE.le
    _ = Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (ε' / Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)) := by rw [hMsq]
    _ = ε' := by rw [mul_div_cancel₀ _ hsE.ne']

theorem ThetaUnifJeps {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {k : ℕ} {ε : ℝ} (hε : 0 < ε) {f : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (htheta : Work.FTS.EpsEngine.ThetaUnif α k f) :
    Work.FTS.EpsEngine.ThetaUnif α k (Work.FTS.StrongEps.Jeps ρ ε f) := by
  have hsmQ : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad := by
    intro n
    simpa only [Work.FTS.StrongEps.Quad] using hsm n
  refine ⟨?_, ?_⟩
  · intro a b hab ε' hε'
    obtain ⟨δ, hδpos, hδ⟩ :=
      jeps_thetaFlat_left hρ.moll hε (fun ε'' hε'' => htheta.t0 a b hab ε'' hε'') ε' hε'
    refine ⟨min δ (Real.pi / 4), lt_min hδpos (by linarith [Real.pi_pos]), ?_⟩
    intro θ hθ hθδ z hz
    have hθδ' : θ < δ := lt_of_lt_of_le hθδ (min_le_left _ _)
    have hθπ : θ < Real.pi / 2 := by
      have h := lt_of_lt_of_le hθδ (min_le_right _ _)
      linarith [Real.pi_pos]
    have hθmem : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ, hθπ⟩
    rw [Work.FTS.StrongEps.mixed_Jeps ρ hρ.moll hε hsmQ hz hθmem b a]
    exact hδ θ hθ hθδ' z hz
  · intro a b hab ε' hε'
    obtain ⟨δ, hδpos, hδ⟩ :=
      jeps_thetaFlat_right hρ.moll hε (fun ε'' hε'' => htheta.t1 a b hab ε'' hε'') ε' hε'
    refine ⟨min δ (Real.pi / 4), lt_min hδpos (by linarith [Real.pi_pos]), ?_⟩
    intro θ hθπ hθδ z hz
    have hθlo : Real.pi / 2 - δ < θ := by
      have h : Real.pi / 2 - δ ≤ Real.pi / 2 - min δ (Real.pi / 4) := by
        linarith [min_le_left δ (Real.pi / 4)]
      linarith
    have hθpos : 0 < θ := by
      have h2 : min δ (Real.pi / 4) ≤ Real.pi / 4 := min_le_right _ _
      linarith [Real.pi_pos]
    have hθmem : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθpos, hθπ⟩
    rw [Work.FTS.StrongEps.mixed_Jeps ρ hρ.moll hε hsmQ hz hθmem b a]
    exact hδ θ hθπ hθlo z hz

end Work.FTS.EpsEngine
