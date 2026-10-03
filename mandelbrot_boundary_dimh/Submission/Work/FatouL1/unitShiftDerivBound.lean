import Mathlib
import Submission.Work.FatouL1.fatouSecondDerivWStrip

/-!
# FATOU-L1: the unit-shift *first*-derivative bound

Same rigidity route as `Work.FatouL1.secondDeriv_le_of_unitShift`, but for `deriv T` on the
full holomorphy region `(a + 1/2, b + 1/2)`: the shift rigidity
(`Work.FatouL1.hcSolverShiftRigidity`) gives `T = c - hcSolver h` on `(a + 1/2, b - 1)`; since
`T` is holomorphic on the *bigger* strip `(a + 1/2, b + 1/2)` (hypothesis `hTbig`) and
`hcSolver h` is holomorphic on the same strip (`Work.FatouL1.hcSolverBound`), the identity
extends by analytic uniqueness to the whole strip.  The `π`-trick form of the derivative bound,
`Work.FatouL1.hcSolverDerivBoundMr`, then gives `‖deriv T z‖ ≤ M`.
-/

namespace Work.FatouL1

open MeasureTheory Filter
open scoped Topology ENNReal

noncomputable section

theorem unitShiftDerivBound {a b m B : ℝ} (hab : a < b) (hab' : 2 < b - a) {T h : ℂ → ℂ}
    (hT : DifferentiableOn ℂ T {z : ℂ | a < z.re ∧ z.re < b})
    (hTbig : DifferentiableOn ℂ T {z : ℂ | a + 1 / 2 < z.re ∧ z.re < b + 1 / 2})
    (hh : DifferentiableOn ℂ h {z : ℂ | a < z.re ∧ z.re < b})
    (hint : ∀ x ∈ Set.Ioo a b, MeasureTheory.Integrable (fun y : ℝ => h ((x : ℂ) + y * Complex.I)))
    (hmass : ∀ x ∈ Set.Ioo a b,
      ∫⁻ y : ℝ, ENNReal.ofReal ‖h ((x : ℂ) + y * Complex.I)‖ ≤ ENNReal.ofReal m)
    (heq : ∀ z : ℂ, a < z.re → z.re < b → T (z + 1) - T z = h z)
    (hbdd : ∀ z : ℂ, a < z.re → z.re < b → ‖T z‖ ≤ B) :
    ∀ z : ℂ, a + 1 / 2 < z.re → z.re < b + 1 / 2 → ∀ M : ℝ, 0 ≤ M →
      (∀ y : ℝ, ‖h (z - 1 / 2 + y * Complex.I)‖ ≤ M) → ‖deriv T z‖ ≤ M := by
  intro z hz1 hz2 M hMnn hM
  -- shift rigidity on `(a + 1/2, b - 1)`
  obtain ⟨c, hc⟩ := hcSolverShiftRigidity hab hab' hT hh hint hmass heq hbdd
  -- analytic uniqueness extends the identity to `(a + 1/2, b + 1/2)`
  have hSopen : IsOpen {z : ℂ | a + 1 / 2 < z.re ∧ z.re < b + 1 / 2} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hSconn : IsPreconnected {z : ℂ | a + 1 / 2 < z.re ∧ z.re < b + 1 / 2} := by
    have heq' : {z : ℂ | a + 1 / 2 < z.re ∧ z.re < b + 1 / 2}
        = Complex.reCLM ⁻¹' (Set.Ioo (a + 1 / 2) (b + 1 / 2)) := by
      ext z; simp [Complex.reCLM_apply]
    rw [heq']
    exact (Convex.linear_preimage (convex_Ioo _ _) Complex.reCLM.toLinearMap).isPreconnected
  have hS₀open : IsOpen {z : ℂ | a + 1 / 2 < z.re ∧ z.re < b - 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hS₀sub : {z : ℂ | a + 1 / 2 < z.re ∧ z.re < b - 1}
      ⊆ {z : ℂ | a + 1 / 2 < z.re ∧ z.re < b + 1 / 2} :=
    fun z hz => ⟨hz.1, by linarith [hz.2]⟩
  have hz₀ : (((a + 1 / 2 + (b - 1)) / 2 : ℝ) : ℂ)
      ∈ {z : ℂ | a + 1 / 2 < z.re ∧ z.re < b - 1} := by
    constructor <;> simp only [Complex.ofReal_re] <;> linarith
  have hcS_hol : DifferentiableOn ℂ (Work.FatouL1.hcSolver h)
      {z : ℂ | a + 1 / 2 < z.re ∧ z.re < b + 1 / 2} := (hcSolverBound hab hh hint hmass).1
  have hT_an : AnalyticOnNhd ℂ T {z : ℂ | a + 1 / 2 < z.re ∧ z.re < b + 1 / 2} :=
    hTbig.analyticOnNhd hSopen
  have hR_an : AnalyticOnNhd ℂ (fun z : ℂ => c - Work.FatouL1.hcSolver h z)
      {z : ℂ | a + 1 / 2 < z.re ∧ z.re < b + 1 / 2} :=
    (hcS_hol.const_sub c).analyticOnNhd hSopen
  have hEq : Set.EqOn T (fun z : ℂ => c - Work.FatouL1.hcSolver h z)
      {z : ℂ | a + 1 / 2 < z.re ∧ z.re < b + 1 / 2} :=
    hT_an.eqOn_of_preconnected_of_eventuallyEq hR_an hSconn (hS₀sub hz₀)
      (Filter.eventually_of_mem (hS₀open.mem_nhds hz₀) (fun w hw => hc w hw.1 hw.2))
  have hne : T =ᶠ[nhds z] (fun w : ℂ => c - Work.FatouL1.hcSolver h w) :=
    Filter.eventually_of_mem (hSopen.mem_nhds ⟨hz1, hz2⟩) hEq
  have h1 : deriv T z = -deriv (Work.FatouL1.hcSolver h) z := by
    rw [hne.deriv_eq, deriv_const_sub]
  rw [h1, norm_neg]
  exact (hcSolverDerivBoundMr hab hh hint hmass hz1 hz2 hMnn hM).1

end

end Work.FatouL1
