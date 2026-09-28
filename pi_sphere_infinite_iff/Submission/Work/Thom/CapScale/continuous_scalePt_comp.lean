import Mathlib
import Submission.Work.Thom.CapGeomDefs

set_option synthInstance.maxHeartbeats 400000

namespace Work.Thom.CapScale

/-- Continuity of the scaling family `Φ_λ` when both the scaling parameter and the base point
vary.  The non-vanishing hypothesis `hS` is used only to supply the proof argument of
`scalePt`; the value of `scalePt` does not depend on it, so the continuity is that of the
normalisation `v ↦ ‖scaleV n λ v‖⁻¹ • scaleV n λ v`. -/
theorem continuous_scalePt_comp (n : ℕ) {α : Type} [TopologicalSpace α] (lam : α → ℝ)
    (hlam : Continuous lam) (S : Set (MSph (n + 1)))
    (hS : ∀ (a : α) (v : ↥S), scaleV n (lam a) v.1.1 ≠ 0) :
    Continuous fun p : α × ↥S => scalePt n (lam p.1) p.2.1 (hS p.1 p.2) := by
  -- the two ingredients: `lam` varies continuously, and so does the base point
  have hlam' : Continuous fun p : α × ↥S => lam p.1 := hlam.comp continuous_fst
  have hpt : Continuous fun p : α × ↥S => p.2.1.1 :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
  have hlast : Continuous fun p : α × ↥S => lastC n p.2.1.1 :=
    (continuous_lastC n).comp hpt
  have hstrip : Continuous fun p : α × ↥S => Work.Morse.strip p.2.1.1 :=
    (Work.Cohomology.continuous_strip n).comp hpt
  -- the un-normalised vector `scaleV n (lam p.1) p.2.1.1` depends continuously on `p`
  have hscale : Continuous fun p : α × ↥S => scaleV n (lam p.1) p.2.1.1 := by
    have hfun : (fun p : α × ↥S => scaleV n (lam p.1) p.2.1.1)
        = (fun q : EuclideanSpace ℝ (Fin n) × ℝ => Work.Morse.snocLp q.1 q.2)
          ∘ (fun p : α × ↥S =>
              (Work.Morse.strip p.2.1.1, lam p.1 * lastC n p.2.1.1)) := rfl
    rw [hfun]
    exact Work.Morse.continuous_snocLp.comp (hstrip.prodMk (hlam'.mul hlast))
  -- unfold the definition of `scalePt`: it is a subtype constructor
  unfold scalePt
  apply Continuous.subtype_mk
  -- the normalised vector is continuous, since the norm never vanishes by `hS`
  exact (hscale.norm.inv₀ (fun p => norm_ne_zero_iff.mpr (hS p.1 p.2))).smul hscale

end Work.Thom.CapScale
