import Mathlib
import Submission.Work.Drive.greenEnergyPairing
import Submission.Work.Drive.energyGreenRung

/-!
# The value of a function at its own pole is invisible to the chart pairing

An `IsGreenOn` statement constrains a Green function only *off* its pole
(`Work.Drive.isGreenOn_update_of_isGreenOn`), and the chart-local Dirichlet pairing
`Work.Drive.pairTerm` integrates a *gradient*, so it cannot see the value of its arguments at a
single point either.  This file records that: if two functions agree off a single point `q`, then
(everywhere the clamped chart ball lies in the chart target) every `pairTerm`, and hence every
`pairing`, takes the same value on them.

This is what makes the pole identity `Work.Kernel.pairing_pole_smooth` usable: its logarithmic
expansion hypothesis is stated at *every* point of a ball, **including the image of the pole**, where
it pins the value of the first argument at its own pole to the expansion's constant; that value is
free (`Work.Drive.isGreenOn_update_of_isGreenOn`), and this lemma lets one adjust it at will without
changing the pairing.

The proof is elementary: the two clamped pullbacks differ only at the single point `(chartAt ℂ x) q`
(a Lebesgue-null set), hence their gradients agree a.e., hence the two integrands of `pairTerm` agree
a.e., hence the integrals agree.
-/

open MeasureTheory Set Filter
open scoped Manifold Topology Gradient

noncomputable section

set_option linter.unusedSectionVars false

namespace Work.Drive

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]

/-- **Functions that agree off a single point have the same clamped pullback** away from the image of
that point. -/
theorem clampedPullback_eq_of_eq_off {x : X} {ρ : ℝ}
    (htgt : Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target)
    {u u' : X → ℝ} {q : X}
    (h : ∀ y : X, y ≠ q → u' y = u y) {z : ℂ} (hz : z ≠ (chartAt ℂ x) q) :
    clampedPullback x ρ u' z = clampedPullback x ρ u z := by
  by_cases hb : z ∈ Metric.ball ((chartAt ℂ x) x) ρ
  · rw [clampedPullback_apply_of_mem hb, clampedPullback_apply_of_mem hb]
    refine h _ (fun hcon => hz ?_)
    have h1 : (chartAt ℂ x) ((chartAt ℂ x).symm z) = (chartAt ℂ x) q := congrArg _ hcon
    rwa [(chartAt ℂ x).right_inv (htgt hb)] at h1
  · rw [clampedPullback_eq_zero_of_notMem_ball hb, clampedPullback_eq_zero_of_notMem_ball hb]

/-- **Functions that agree off a single point have the same clamped-pullback gradient** almost
everywhere. -/
theorem gradient_clampedPullback_eq_of_eq_off {x : X} {ρ : ℝ}
    (htgt : Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target)
    {u u' : X → ℝ} {q : X}
    (h : ∀ y : X, y ≠ q → u' y = u y) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      gradient (clampedPullback x ρ u') z = gradient (clampedPullback x ρ u) z := by
  filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr
    (MeasureTheory.measure_singleton ((chartAt ℂ x) q))] with z hz
  have hz' : z ≠ (chartAt ℂ x) q := by simpa using hz
  have hev : clampedPullback x ρ u' =ᶠ[𝓝 z] clampedPullback x ρ u := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (by simpa using hz')] with w hw
    exact clampedPullback_eq_of_eq_off htgt h (by simpa using hw)
  exact hev.gradient_eq

/-- **The chart-local pairing does not see a modification at a single point.** -/
theorem pairTerm_eq_of_eq_off {x : X} {ρ σ : ℝ}
    (htgt : Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target)
    {W u u' χ : X → ℝ} {q : X}
    (h : ∀ y : X, y ≠ q → u' y = u y) :
    pairTerm x ρ σ W u' χ = pairTerm x ρ σ W u χ := by
  rw [pairTerm, pairTerm]
  refine integral_congr_ae ?_
  filter_upwards [gradient_clampedPullback_eq_of_eq_off (x := x) (ρ := ρ) (u := u) (u' := u')
    (q := q) htgt h] with z hz
  rw [hz]

/-- **The whole pairing does not see a modification of its first argument at a single point.** -/
theorem pairing_eq_of_eq_off {ι : Type*} [Fintype ι] {y : ι → X} {ρ σ : ι → ℝ} {ψ : ι → X → ℝ}
    (htgt : ∀ i, Metric.ball ((chartAt ℂ (y i)) (y i)) (ρ i) ⊆ (chartAt ℂ (y i)).target)
    {u u' χ : X → ℝ} {q : X} (h : ∀ y : X, y ≠ q → u' y = u y) :
    pairing y ρ σ ψ u' χ = pairing y ρ σ ψ u χ := by
  simp only [pairing]
  exact Finset.sum_congr rfl fun i _ => pairTerm_eq_of_eq_off (x := y i) (ρ := ρ i) (σ := σ i)
    (htgt i) (W := ψ i) (χ := χ) (u := u) (u' := u') h

/-- **The whole pairing does not see a modification of its second argument at a single point.** -/
theorem pairing_eq_of_eq_off_right {ι : Type*} [Fintype ι] {y : ι → X} {ρ σ : ι → ℝ}
    {ψ : ι → X → ℝ}
    (htgt : ∀ i, Metric.ball ((chartAt ℂ (y i)) (y i)) (ρ i) ⊆ (chartAt ℂ (y i)).target)
    {u u' χ : X → ℝ} {q : X} (h : ∀ y : X, y ≠ q → u' y = u y) :
    pairing y ρ σ ψ χ u' = pairing y ρ σ ψ χ u := by
  simp only [pairing]
  exact Finset.sum_congr rfl fun i _ =>
    (Work.Drive.GreenRung.pairTerm_symm (y i) (ρ i) (σ i) (ψ i) u' χ).symm.trans
      ((pairTerm_eq_of_eq_off (x := y i) (ρ := ρ i) (σ := σ i) (htgt i) (W := ψ i) (χ := χ)
          (u := u) (u' := u') h).trans
        (Work.Drive.GreenRung.pairTerm_symm (y i) (ρ i) (σ i) (ψ i) u χ))

/-- **The value of a function at its own pole is free in the chart pairing.**  Replacing `u` by
`Function.update u q c` leaves every `pairTerm` (and every `pairing`) unchanged. -/
theorem pairTerm_update_eq {x : X} {ρ σ : ℝ}
    (htgt : Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target)
    [DecidableEq X] (W u χ : X → ℝ) (q : X) (c : ℝ) :
    pairTerm x ρ σ W (Function.update u q c) χ = pairTerm x ρ σ W u χ :=
  pairTerm_eq_of_eq_off htgt fun _ hy => Function.update_of_ne hy c u

/-- **The value of a function at its own pole is free in the pairing.** -/
theorem pairing_update_eq {ι : Type*} [Fintype ι] {y : ι → X} {ρ σ : ι → ℝ} {ψ : ι → X → ℝ}
    (htgt : ∀ i, Metric.ball ((chartAt ℂ (y i)) (y i)) (ρ i) ⊆ (chartAt ℂ (y i)).target)
    [DecidableEq X] (u : X → ℝ) (q : X) (c : ℝ) (χ : X → ℝ) :
    pairing y ρ σ ψ (Function.update u q c) χ = pairing y ρ σ ψ u χ :=
  pairing_eq_of_eq_off htgt fun _ hy => Function.update_of_ne hy c u

end Work.Drive
