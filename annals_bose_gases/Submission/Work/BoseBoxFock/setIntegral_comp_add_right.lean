import Mathlib.MeasureTheory.Integral.Bochner.Set
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

/-- Change of variables for the right translation `x ↦ x + a` under a right-invariant measure:
the integral of the translated function over `s` equals the integral of `f` over the translate
`(· + a) '' s`.

This is `MeasureTheory.MeasurePreserving.setIntegral_image_emb` applied to the measure preserving
map `x ↦ x + a` (which is even a measurable embedding, being a bijection with measurable
inverse `x ↦ x - a`). -/
lemma setIntegral_comp_add_right {G E : Type*} [MeasurableSpace G] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {μ : MeasureTheory.Measure G} [AddGroup G] [MeasurableAdd G]
    [μ.IsAddRightInvariant] (f : G → E) (s : Set G) (a : G) :
    (∫ x in s, f (x + a) ∂μ) = ∫ x in (fun y => y + a) '' s, f x ∂μ :=
  (MeasureTheory.MeasurePreserving.setIntegral_image_emb
    (MeasureTheory.measurePreserving_add_right μ a) (measurableEmbedding_addRight a) f s).symm

end Work.BoseBoxFock
