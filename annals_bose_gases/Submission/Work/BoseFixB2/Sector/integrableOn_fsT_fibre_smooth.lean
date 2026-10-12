import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.Defs
import Submission.Work.BoseFixB2.Sector.exists_contDiff_cutoff_abox
import Submission.Work.BoseKinLoc.Sector.integrable_indU_mul_fsT_fibre_anyL
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth`

**The slot-`i` kinetic integrand of a *globally smooth* state is integrable on the box.**

For a globally smooth (not necessarily compactly supported) state `Φ : X n → ℝ`, the slot-`i`
summand of the box-restricted kinetic word,

    `x ↦ 1_{Λ(0)}(xᵢ) · fsT ℓ d s ε_T b 0 (fibre n i Φ x)`,

is integrable on the configuration box `abox n ℓ`.  Equivalently, this is the box-restricted
version of `Work.BoseKinLoc.Sector.integrable_indU_mul_fsT_fibre_anyL`, whose hypothesis is
`tsupport Ψ ⊆ abox N L` — a support condition that `Φ` does not satisfy.

## Proof

The word `fsT` is blind to the values of its argument off the anchored box `Λ(0) = acube ℓ`
(`Work.BoseKinLoc.Sector.fsT_box_invariant`), and the slot-`i` fibre of `x ∈ abox n ℓ` only
sees `Φ` at points of `abox n ℓ` (updating the `i`-th slot by a point of `acube ℓ` keeps the
configuration inside the box).  Hence any smooth *compactly supported* modification `Ψ` of
`Φ` which agrees with `Φ` on `abox n ℓ` — provided by
`Work.BoseFixB2.Sector.exists_contDiff_cutoff_abox` — gives the same integrand on the box, and
the integrability of the compactly supported version (the sibling module) transfers by
`IntegrableOn.congr_fun`.
-/

namespace Work.BoseFixB2.Sector

open Submission.BoseGases MeasureTheory

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The box is stable under updating a coordinate -/

/-- **Updating one coordinate of a point of the box by a point of `acube ℓ` keeps it in the
box.** -/
lemma update_mem_abox {n : ℕ} {ℓ : ℝ} {x : Submission.BoseGases.X n}
    (hx : x ∈ Submission.BoseGases.abox n ℓ) (i : Fin n) {z : EuclideanSpace ℝ (Fin 3)}
    (hz : z ∈ Submission.BoseGases.acube ℓ) :
    Function.update x i z ∈ Submission.BoseGases.abox n ℓ := by
  rw [Submission.BoseGases.mem_abox_iff] at hx ⊢
  intro j
  rw [Function.update_apply]
  split
  · exact hz
  · exact hx j

/-- The anchored moving box is the centred cube: `Λ(0) = acube ℓ`. -/
lemma lamBox_zero_eq_acube {ℓ : ℝ} : Work.BoseKinLoc.lamBox ℓ 0 = Submission.BoseGases.acube ℓ := by
  ext z
  simp [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox]

/-! ## 2. Box locality of `fsT` along the slot fibres -/

/-- **The slot-`i` fibre word of `x ∈ abox n ℓ` only depends on the values of the state on the
box.**  If `Ψ = Φ` on `abox n ℓ`, then `fsT … 0 (fibre n i Ψ x) = fsT … 0 (fibre n i Φ x)`. -/
lemma fsT_fibre_eq_of_eqOn_abox {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (i : Fin n)
    {Ψ Φ : Submission.BoseGases.X n → ℝ}
    (h : ∀ x ∈ Submission.BoseGases.abox n ℓ, Ψ x = Φ x)
    {x : Submission.BoseGases.X n} (hx : x ∈ Submission.BoseGases.abox n ℓ) :
    Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre n i Ψ x)
      = Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre n i Φ x) := by
  refine Work.BoseKinLoc.Sector.fsT_box_invariant (ℓ := ℓ) (d := d) (s := s) (εT := εT)
    (b := b) (u := 0) hℓ ?_
  intro z hz
  rw [lamBox_zero_eq_acube] at hz
  show Ψ (Function.update x i z) = Φ (Function.update x i z)
  exact h _ (update_mem_abox hx i hz)

/-! ## 3. The target -/

theorem integrableOn_fsT_fibre_smooth {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (i : Fin n) {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.indU ℓ 0 (x i) * Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre n i Φ x)) (Submission.BoseGases.abox n ℓ) := by
  classical
  -- a smooth compactly supported modification of `Φ` agreeing with it on the box
  obtain ⟨L, Ψ, -, hΨdiff, hΨsupp, hΨeq⟩ :=
    Work.BoseFixB2.Sector.exists_contDiff_cutoff_abox (ℓ := ℓ) (n := n) hℓ hΦ
  -- integrability of the compactly supported version (whole space)
  have hIntΨ : MeasureTheory.Integrable (fun x : Submission.BoseGases.X n =>
      Work.BoseKinLoc.indU ℓ 0 (x i) * Work.BoseKinLoc.fsT ℓ d s εT b 0
        (Work.BoseKinLoc.fibre n i Ψ x)) :=
    Work.BoseKinLoc.Sector.integrable_indU_mul_fsT_fibre_anyL hℓ hΨdiff hΨsupp i
  -- transfer to `Φ` by equality on the box
  refine (hIntΨ.integrableOn).congr_fun ?_ (Submission.BoseGases.abox_measurable n ℓ)
  intro x hx
  change Work.BoseKinLoc.indU ℓ 0 (x i) * Work.BoseKinLoc.fsT ℓ d s εT b 0
        (Work.BoseKinLoc.fibre n i Ψ x)
      = Work.BoseKinLoc.indU ℓ 0 (x i) * Work.BoseKinLoc.fsT ℓ d s εT b 0
        (Work.BoseKinLoc.fibre n i Φ x)
  rw [fsT_fibre_eq_of_eqOn_abox hℓ i hΨeq hx]

end Work.BoseFixB2.Sector
