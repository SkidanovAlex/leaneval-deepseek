/-
Work module for `annals_finite_time_singularity` (Elgindi, Annals 194(3) 2021): the
measure-theoretic conversion of the a.e. identity for the transported unknown `Vf α Ψ`.

The weak formulation lives on the strip `stripE = {0 < θ < π/2}` of the `(s,θ)`-coordinates
`s = (1/α) log z`, where the transported unknown `Vf α Ψ = wt α · Ψ ∘ chart` agrees a.e. there
with a function `Φt : E2 → ℂ`.  This file converts that statement back to the open quadrant
`Q0 = (0,∞) × (0,π/2)` in the `(z,θ)`-coordinates: the two functions

  `(z,θ) ↦ Ψ z θ`   and   `(z,θ) ↦ Φt (coords ((1/α) log z) θ) / wt α (coords ((1/α) log z) θ)`

agree a.e. on `Q0` with respect to `volume.restrict Q0`.

The argument is a null-set chase (`IR/NOTES_finalConvert.md`, Lemma B; the same pattern as
`IR/ae_eq_PhiPrime.lean` and `VT/ae_eq_PhiPrimeV`):

* the bad set `{x ∈ stripE | Vf α Ψ x ≠ Φt x}` is null (this is the hypothesis);
* it is pulled back to a null set of `ℝ × ℝ` along the measure-preserving coordinate map
  `q ↦ coords q.1 q.2` (`VT.coords_measurePreserving`);
* the exponential substitution `(s,θ) ↦ (e^{αs},θ)` is differentiable, hence maps that null set
  onto a null set (`MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`);
* finally, a point `p ∈ Q0` at which the two functions differ lies in that image: with
  `q = ((1/α) log p.1, p.2)` one has `e^{α·q.1} = p.1`, and if `coords q.1 q.2` were *not* bad
  then dividing the a.e. identity there (where the weight is non-zero,
  `Q0.wt_ne_zero`) would make `p` good.
-/
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.RingTheory.Finiteness.Prod
import Submission.Work.EllipticEst.InteriorRegularity.Q0.Defs
import Submission.Work.EllipticEst.InteriorRegularity.Strip
import Submission.Work.EllipticEst.InteriorRegularity.VT.Basic
import Submission.Work.EllipticEst.InteriorRegularity.VT.TransportDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.InteriorRegularity.Q0

open MeasureTheory Set Filter
open scoped Real Topology

/-- On the strip, the transported unknown is the product of the weight with `Ψ` evaluated at the
chart point. -/
theorem aeVf_Vf_coords (α : ℝ) (Ψ : ℝ → ℝ → ℝ) {σ θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Vf α Ψ (coords σ θ) = wt α (coords σ θ) * Ψ (Real.exp (α * σ)) θ := by
  have hmem : coords σ θ ∈ stripE := by
    rw [VT.mem_stripE, VT.coords_one]
    exact hθ
  rw [Vf, Set.indicator_of_mem hmem]
  simp only [VT.coords_zero, VT.coords_one]

/-- The exponential substitution is the inverse of the chart on the quadrant. -/
theorem aeVf_exp_log {α : ℝ} (hα : 0 < α) {z : ℝ} (hz : 0 < z) :
    Real.exp (α * ((1 / α) * Real.log z)) = z := by
  have h1 : α * ((1 / α) * Real.log z) = Real.log z := by
    rw [← mul_assoc, mul_one_div_cancel hα.ne', one_mul]
  rw [h1, Real.exp_log hz]

theorem ae_eq_of_ae_eq_Vf {α : ℝ} (hα : 0 < α) {Ψ : ℝ → ℝ → ℝ} {Φt : E2 → ℂ}
    (h : (fun x : E2 => (Work.EllipticEst.InteriorRegularity.Q0.Vf α Ψ x : ℂ))
      =ᵐ[MeasureTheory.volume.restrict Work.EllipticEst.InteriorRegularity.stripE] Φt) :
    (fun p : ℝ × ℝ => (Ψ p.1 p.2 : ℂ))
      =ᵐ[MeasureTheory.volume.restrict Work.FTS.EllipticEst.Q0]
        (fun p : ℝ × ℝ => Φt (Work.EllipticEst.InteriorRegularity.coords ((1 / α) * Real.log p.1) p.2)
          / (Work.EllipticEst.InteriorRegularity.Q0.wt α
              (Work.EllipticEst.InteriorRegularity.coords ((1 / α) * Real.log p.1) p.2) : ℂ)) := by
  -- the bad set of the strip is null
  have hbadE : volume ({x : E2 | (Vf α Ψ x : ℂ) ≠ Φt x} ∩ stripE) = 0 := by
    have h' := h
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff] at h'
    rwa [MeasureTheory.Measure.restrict_apply' VT.isOpen_stripE.measurableSet] at h'
  -- pull it back along the measure-preserving coordinate map `q ↦ coords q.1 q.2`
  have hB : volume ((fun p : ℝ × ℝ => coords p.1 p.2) ⁻¹'
      ({x : E2 | (Vf α Ψ x : ℂ) ≠ Φt x} ∩ stripE)) = 0 :=
    VT.coords_measurePreserving.quasiMeasurePreserving.preimage_null hbadE
  -- the differentiable exponential substitution maps it onto a null set
  have hT : volume (VT.TsubV α '' ((fun p : ℝ × ℝ => coords p.1 p.2) ⁻¹'
      ({x : E2 | (Vf α Ψ x : ℂ) ≠ Φt x} ∩ stripE))) = 0 :=
    MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (VT.differentiable_TsubV α).differentiableOn hB
  -- every bad point of the quadrant is the image of a bad point of the half-strip
  have hsub : {p : ℝ × ℝ | ¬ ((Ψ p.1 p.2 : ℂ)
        = Φt (coords ((1 / α) * Real.log p.1) p.2)
          / (wt α (coords ((1 / α) * Real.log p.1) p.2) : ℂ))}
      ∩ Work.FTS.EllipticEst.Q0 ⊆
      VT.TsubV α '' ((fun p : ℝ × ℝ => coords p.1 p.2) ⁻¹'
        ({x : E2 | (Vf α Ψ x : ℂ) ≠ Φt x} ∩ stripE)) := by
    rintro p ⟨hpb, hpQ⟩
    rw [Work.FTS.EllipticEst.mem_Q0] at hpQ
    obtain ⟨hz, hθ⟩ := hpQ
    have hstrip : coords ((1 / α) * Real.log p.1) p.2 ∈ stripE := by
      rw [VT.mem_stripE, VT.coords_one]
      exact hθ
    have hexp : Real.exp (α * ((1 / α) * Real.log p.1)) = p.1 := aeVf_exp_log hα hz
    have hTq : VT.TsubV α ((1 / α) * Real.log p.1, p.2) = p := by
      simp only [VT.TsubV]
      rw [hexp]
    refine ⟨((1 / α) * Real.log p.1, p.2), ⟨?_, hstrip⟩, hTq⟩
    intro hEq
    -- if `coords q.1 q.2` is not bad, dividing the identity by the non-vanishing weight
    -- gives back the definition of goodness at `p`
    have hEq' : (Vf α Ψ (coords ((1 / α) * Real.log p.1) p.2) : ℂ)
        = Φt (coords ((1 / α) * Real.log p.1) p.2) := hEq
    have hW := aeVf_Vf_coords α Ψ (σ := (1 / α) * Real.log p.1) hθ
    rw [hexp] at hW
    have hwt : (wt α (coords ((1 / α) * Real.log p.1) p.2) : ℂ) ≠ 0 := by
      have h0 : wt α (coords ((1 / α) * Real.log p.1) p.2) ≠ 0 := wt_ne_zero hα hstrip
      exact_mod_cast h0
    have hmul : (wt α (coords ((1 / α) * Real.log p.1) p.2) : ℂ) * (Ψ p.1 p.2 : ℂ)
        = Φt (coords ((1 / α) * Real.log p.1) p.2) := by
      rw [← hEq', hW, Complex.ofReal_mul]
    have hpb' : ¬ ((Ψ p.1 p.2 : ℂ)
        = Φt (coords ((1 / α) * Real.log p.1) p.2)
          / (wt α (coords ((1 / α) * Real.log p.1) p.2) : ℂ)) := hpb
    refine hpb' ?_
    rw [eq_div_iff hwt, mul_comm]
    exact hmul
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff,
    MeasureTheory.Measure.restrict_apply' Work.FTS.EllipticEst.isOpen_Q0.measurableSet]
  exact MeasureTheory.measure_mono_null hsub hT

end Work.EllipticEst.InteriorRegularity.Q0
