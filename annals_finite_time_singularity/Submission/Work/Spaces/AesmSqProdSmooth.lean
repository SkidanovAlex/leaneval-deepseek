/-
Copyright: work module for the Elgindi finite-time singularity project.

# Almost everywhere strong measurability of `(A · B · W)²`

If `A` and `B` are smooth on an open neighbourhood of the closed quadrant
(`SmoothNbhd`), then `(A · B · Wᵅ)²` is almost everywhere strongly measurable both
for the product measure `(dz)|_{Iz} ⊗ (dθ)|_{Iθ}` and, for every fixed `z ∈ Iz`,
for the one-dimensional measure `(dθ)|_{Iθ}`.

The product statement is the case `j = i = 0` of `aesm_mixed_Wt_sq_prod` applied to
the (smooth) product `A · B`.  For the slice statement we use that on the *open*
interval `(0,π/2)` all three factors are continuous — `A z ·` and `B z ·` because
`z ∈ Iz ⊆ (-1,∞)` and the weight `Wᵅ = w(z)·sin(2θ)^{-γ/2}` because `sin(2θ) > 0`
there — and that `(0,π/2)` differs from `Iθ` by the null set `{0, π/2}`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.aesm_mixed_Wt_sq_prod

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false

/-- For `z ∈ Iz`, the `θ`-slice of a function smooth on an open neighbourhood of the
closed quadrant is continuous on the open interval `(0,π/2)`. -/
private lemma continuousOn_slice_smoothNbhd {f : ℝ → ℝ → ℝ} (hf : SmoothNbhd f) {z : ℝ}
    (hz : z ∈ Iz) :
    ContinuousOn (fun θ => f z θ) (Set.Ioo 0 (π / 2)) := by
  have hz' : (-1 : ℝ) < z := by
    rw [Iz, Set.mem_Ici] at hz; linarith
  have hcont : ContinuousOn (Function.uncurry f) nbhU := hf.continuousOn
  have hiota : ContinuousOn (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (π / 2)) :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hmap : MapsTo (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (π / 2)) nbhU := by
    intro θ hθ
    rw [nbhU, Set.mem_prod]
    exact ⟨by rw [Set.mem_Ioi]; exact hz',
      by rw [Set.mem_Ioo]; exact ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩⟩
  simpa only [Function.uncurry] using hcont.comp' hiota hmap

/-- The `θ`-slice of the weight `Wt α z · = w(z) · sin(2θ)^{-γ/2}` is continuous on
the open interval `(0,π/2)`, where `sin(2θ) > 0`. -/
private lemma continuousOn_slice_Wt (α z : ℝ) :
    ContinuousOn (fun θ => Wt α z θ) (Set.Ioo 0 (π / 2)) := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (π / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hne : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), Real.sin (2 * θ) ≠ 0 := by
    intro θ hθ
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos]))
  have hrp : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(gam α / 2)))
      (Set.Ioo 0 (π / 2)) :=
    hsin.rpow_const (fun θ hθ => Or.inl (hne θ hθ))
  simpa [Wt, wTheta] using hrp.const_mul (w z)

/-- The open interval `(0,π/2)` and the closed interval `Iθ` carry the same restriction
of Lebesgue measure, since they differ by the two null points `0` and `π/2`. -/
private lemma restrict_Ioo_eq_restrict_Iθ :
    volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) = volume.restrict Iθ :=
  Measure.restrict_congr_set (by rw [Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc)

theorem AesmSqProdSmooth (α : ℝ) {A B : ℝ → ℝ → ℝ}
    (hA : Work.Spaces.SmoothNbhd A) (hB : Work.Spaces.SmoothNbhd B) :
    MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => (A p.1 p.2 * B p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ))
      ∧ ∀ z ∈ Work.Spaces.Iz, MeasureTheory.AEStronglyMeasurable
        (fun θ : ℝ => (A z θ * B z θ * Work.Spaces.Wt α z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  refine ⟨?_, ?_⟩
  · -- The product `A · B` is again smooth on the neighbourhood, and `aesm_mixed_Wt_sq_prod`
    -- handles `(g · Wᵅ)²` for a smooth `g`.
    have hAB : SmoothNbhd (fun z θ => A z θ * B z θ) := by
      show ContDiffOn ℝ ⊤ (Function.uncurry (fun z θ => A z θ * B z θ)) nbhU
      exact hA.mul hB
    exact aesm_mixed_Wt_sq_prod α (fun z θ => A z θ * B z θ) hAB 0 0
  · intro z hz
    -- On the open interval `(0,π/2)` the integrand is continuous, and that interval is
    -- co-null in `Iθ`.
    have hcont : ContinuousOn (fun θ => (A z θ * B z θ * Wt α z θ) ^ 2) (Set.Ioo 0 (π / 2)) :=
      (((continuousOn_slice_smoothNbhd hA hz).mul
        (continuousOn_slice_smoothNbhd hB hz)).mul (continuousOn_slice_Wt α z)).pow 2
    rw [← restrict_Ioo_eq_restrict_Iθ]
    exact hcont.aestronglyMeasurable measurableSet_Ioo

end Work.Spaces
