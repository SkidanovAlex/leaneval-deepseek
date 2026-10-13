import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.FTS.EllSol.SpecAux.FlipDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.SpecAux

open MeasureTheory Set

/-- The time reversal `(t, θ) ↦ (-t, θ)` preserves the restricted Lebesgue measure
`(dz ⊗ dθ)|_{univ ×ˢ Iθ}`: it is the product of the (measure preserving) negation on `ℝ`
with the identity on `Iθ`, and `univ ×ˢ Iθ` is invariant under it. -/
private theorem map_timFlip_restrict (t : Set ℝ) :
    Measure.map (Prod.map Neg.neg id)
        ((volume : Measure (ℝ × ℝ)).restrict ((univ : Set ℝ) ×ˢ t))
      = (volume : Measure (ℝ × ℝ)).restrict ((univ : Set ℝ) ×ˢ t) := by
  -- `univ ×ˢ t` with the product measure is `volume ⊗ (volume|_{t})`.
  have hkey : (volume : Measure ℝ).prod (volume.restrict t)
      = (volume : Measure (ℝ × ℝ)).restrict ((univ : Set ℝ) ×ˢ t) := by
    have h := Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        (univ : Set ℝ) t
    rwa [Measure.restrict_univ] at h
  -- the negation on `ℝ` and the identity on `Iθ` are measure preserving
  have hmap' : Measure.map (Prod.map Neg.neg id)
        ((volume : Measure ℝ).prod (volume.restrict t))
      = (volume : Measure ℝ).prod (volume.restrict t) := by
    have h := (MeasurePreserving.prod
      (Measure.measurePreserving_neg (volume : Measure ℝ))
      (MeasurePreserving.id (volume.restrict t)))
    simpa using h.map_eq
  rw [← hkey]
  exact hmap'

theorem timFlipIntegral (F : ℝ × ℝ → ℝ)
    (hF : MeasureTheory.IntegrableOn F ((Set.univ : Set ℝ) ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F (-p.1, p.2))
        ((Set.univ : Set ℝ) ×ˢ Work.Spaces.Iθ) ∧
      (∫ p in (Set.univ : Set ℝ) ×ˢ Work.Spaces.Iθ, F (-p.1, p.2))
        = ∫ p in (Set.univ : Set ℝ) ×ˢ Work.Spaces.Iθ, F p := by
  -- the flip is a measurable embedding
  have hemb : MeasurableEmbedding (Prod.map (Neg.neg : ℝ → ℝ) (id : ℝ → ℝ)) :=
    MeasurableEmbedding.prodMap (measurableEmbedding_neg)
      (MeasurableEmbedding.id : MeasurableEmbedding (id : ℝ → ℝ))
  have hmeas : Measurable (Prod.map (Neg.neg : ℝ → ℝ) (id : ℝ → ℝ)) := hemb.measurable
  -- it preserves the restricted measure
  have hmp : MeasurePreserving (Prod.map (Neg.neg : ℝ → ℝ) (id : ℝ → ℝ))
      ((volume : Measure (ℝ × ℝ)).restrict ((univ : Set ℝ) ×ˢ Work.Spaces.Iθ))
      ((volume : Measure (ℝ × ℝ)).restrict ((univ : Set ℝ) ×ˢ Work.Spaces.Iθ)) :=
    ⟨hmeas, map_timFlip_restrict Work.Spaces.Iθ⟩
  -- the flipped function, written as a composition
  have hfun : (fun p : ℝ × ℝ => F (Prod.map (Neg.neg : ℝ → ℝ) (id : ℝ → ℝ) p))
      = fun p : ℝ × ℝ => F (-p.1, p.2) := by
    funext p
    simp [Prod.map_apply', id_eq]
  constructor
  · have h := (hmp.integrable_comp_emb hemb).mpr hF
    have h' : Integrable (fun p : ℝ × ℝ => F (Prod.map (Neg.neg : ℝ → ℝ) (id : ℝ → ℝ) p))
        (volume.restrict ((univ : Set ℝ) ×ˢ Work.Spaces.Iθ)) := h
    rw [hfun] at h'
    exact h'
  · have h := hmp.integral_comp hemb F
    have h' : (∫ p in (univ : Set ℝ) ×ˢ Work.Spaces.Iθ,
          F (Prod.map (Neg.neg : ℝ → ℝ) (id : ℝ → ℝ) p))
        = ∫ p in (univ : Set ℝ) ×ˢ Work.Spaces.Iθ, F p := h
    rw [hfun] at h'
    exact h'

end Work.FTS.EllSol.SpecAux
