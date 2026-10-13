/-
Local integrability of the `(σ,θ)`-pullback `(σ,θ) ↦ Ψ (exp (ασ), θ)` of a function `Ψ` which is
locally integrable on the open quadrant `Q0 = (0,∞) × (0,π/2)`, on compact subsets of the
half-strip.

The proof: for a compact `K ⊆ stripRR`, the change of variables `integrableOn_Q0_iff_strip`
together with a cut-off supported in the (compact) image `Φ '' K ⊆ Q0` reduces the claim to the
integrability of `Ψ` on a compact subset of `Q0`, which is the hypothesis.
-/
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.EllipticEst.InteriorRegularity.Q0.RRDefs
import Submission.Work.EllipticEst.InteriorRegularity.Q0.integrableOn_Q0_iff_strip

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.InteriorRegularity.Q0

set_option autoImplicit false
set_option linter.unusedVariables false

theorem integrableOn_barPsi_compact {α : ℝ} (hα : 0 < α) {Ψ : ℝ → ℝ → ℝ}
    (hΨ : MeasureTheory.LocallyIntegrableOn (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKs : K ⊆ stripRR) :
    MeasureTheory.IntegrableOn
      (fun q : ℝ × ℝ => if q.2 ∈ Set.Ioo 0 (Real.pi / 2) then Ψ (Real.exp (α * q.1)) q.2 else 0)
      K := by
  -- the image of `K` under `(σ,θ) ↦ (exp (ασ), θ)`
  set Φ : ℝ × ℝ → ℝ × ℝ := fun p => (Real.exp (α * p.1), p.2) with hΦ
  have hΦc : Continuous Φ := by
    rw [hΦ]
    exact (Real.continuous_exp.comp (continuous_fst.const_mul α)).prodMk continuous_snd
  have hK'c : IsCompact (Φ '' K) := hK.image hΦc
  have hK'Q : Φ '' K ⊆ Work.FTS.EllipticEst.Q0 := by
    rintro p ⟨q, hq, rfl⟩
    exact ⟨Real.exp_pos _, (hKs hq).2⟩
  have hΨK' : MeasureTheory.IntegrableOn (Function.uncurry Ψ) (Φ '' K) :=
    hΨ.integrableOn_compact_subset hK'Q hK'c
  -- a cut-off on the `Q0`-side, supported in the image
  classical
  set Y : ℝ × ℝ → ℝ :=
    fun p => if p ∈ Φ '' K then (α * p.1)⁻¹ * Ψ p.1 p.2 else 0 with hY
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (α * p.1)⁻¹) (Φ '' K) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => α * p.1) (Φ '' K) :=
      (continuous_const.mul continuous_fst).continuousOn
    refine h1.inv₀ (fun p hp => ?_)
    have hp1 : 0 < p.1 := by
      obtain ⟨q, hq, hq'⟩ := hp
      have hq1 : (Φ q).1 = Real.exp (α * q.1) := by rw [hΦ]
      rw [← hq', hq1]
      exact Real.exp_pos _
    positivity
  have hIntK' : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => Function.uncurry Ψ p * (α * p.1)⁻¹) (Φ '' K) :=
    hΨK'.mul_continuousOn hcont hK'c
  have hYK : MeasureTheory.IntegrableOn Y (Φ '' K) :=
    (integrableOn_congr_fun
      (fun p hp => by simp only [hY, hp, if_true, Function.uncurry]; rw [mul_comm])
      hK'c.measurableSet).mpr hIntK'
  have hYQ : MeasureTheory.IntegrableOn Y Work.FTS.EllipticEst.Q0 := by
    have hsupp : Function.support Y ⊆ Φ '' K := by
      intro p hp
      by_contra hcon
      exact (Function.mem_support.mp hp) (by simp only [hY, hcon, if_false])
    have hind : (Φ '' K).indicator Y = Y := by
      funext p
      by_cases hp : p ∈ Φ '' K
      · rw [Set.indicator_of_mem hp]
      · rw [Set.indicator_of_notMem hp]
        by_contra hne
        exact hp (hsupp (Function.mem_support.mpr (fun h => hne h.symm)))
    have hInt : MeasureTheory.Integrable Y := by
      rw [← hind, integrable_indicator_iff hK'c.measurableSet]
      exact hYK
    exact hInt.integrableOn
  -- transfer to the strip
  have hpull : MeasureTheory.IntegrableOn
      (fun q : ℝ × ℝ => (α * Real.exp (α * q.1)) • Y (Real.exp (α * q.1), q.2)) stripRR :=
    (integrableOn_Q0_iff_strip hα Y).mp hYQ
  have hEq : Set.EqOn (fun q : ℝ × ℝ => (α * Real.exp (α * q.1)) • Y (Real.exp (α * q.1), q.2))
      (fun q : ℝ × ℝ =>
        if q.2 ∈ Set.Ioo 0 (Real.pi / 2) then Ψ (Real.exp (α * q.1)) q.2 else 0) K := by
    intro q hq
    have hq2 : q.2 ∈ Set.Ioo 0 (Real.pi / 2) := (hKs hq).2
    have hmem : (Real.exp (α * q.1), q.2) ∈ Φ '' K := ⟨q, hq, by rw [hΦ]⟩
    simp only [hY, hmem, if_true, hq2, smul_eq_mul]
    have hne : α * Real.exp (α * q.1) ≠ 0 := by positivity
    field_simp
  exact (integrableOn_congr_fun hEq hK.measurableSet).mp (hpull.mono_set hKs)

end Work.EllipticEst.InteriorRegularity.Q0
