import Mathlib
import Submission.Work.Stems.HurewiczSphere
import Submission.Work.Stems.SphereMinusPoint

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# A map of spheres that misses a point is based-null (general domain)

`Work.Stems.homotopicRel_const_of_misses` (`Stems/SphereMinusPoint.lean`) states this for self-maps
of `Sⁿ`; its proof only uses the *domain* through continuity, so it generalises verbatim to any
domain `X` with a base point `b`.  This is the last step of the general-position proof that a
continuous map `S^j → Sⁿ` with `j < n` is null-homotopic (`Stems/PLAN.md` §11).

If `g : X → Sⁿ` misses `y` and `g b = x₀`, then `y ≠ x₀` and the contraction of `Sⁿ ∖ {y}`
towards `x₀` (`sphereComplHomeo`, `sphereComplContraction`) gives a homotopy `g ≃ const x₀`
relative to `{b}`.
-/

open scoped Topology unitInterval
open Metric

namespace Work.Stems

noncomputable section

/-- **A map missing a point is based-null** (arbitrary domain): if `g : X → Sⁿ` misses `y` and
`g b = x₀`, then `g` is homotopic to the constant map at `x₀` relative to `{b}`. -/
theorem homotopicRel_const_of_misses' {X : Type} [TopologicalSpace X] (n : ℕ) {b : X}
    {x₀ y : sphere n} (g : C(X, sphere n)) (hg : ∀ z, g z ≠ y) (hgb : g b = x₀) :
    ContinuousMap.HomotopicRel g (ContinuousMap.const _ x₀) {b} := by
  have hne : x₀ ≠ y := by
    rw [← hgb]
    exact hg b
  refine ⟨{ toFun := fun p => sphereComplContraction n y x₀ hne (p.1, ⟨g p.2, hg p.2⟩)
            continuous_toFun := continuous_subtype_val.comp
              ((sphereComplContraction n y x₀ hne).continuous.comp
                (continuous_fst.prodMk
                  (Continuous.subtype_mk (g.continuous.comp continuous_snd) _)))
            map_zero_left := fun z =>
              congrArg Subtype.val (sphereComplContraction_zero n y x₀ hne ⟨g z, hg z⟩)
            map_one_left := fun z =>
              congrArg Subtype.val (sphereComplContraction_one n y x₀ hne ⟨g z, hg z⟩)
            prop' := fun t z hz => by
              rw [Set.mem_singleton_iff] at hz
              subst hz
              have hfix := congrArg Subtype.val (sphereComplContraction_self n y x₀ hne t)
              have hz' : (⟨g z, hg z⟩ : {w : sphere n // w ≠ y}) = ⟨x₀, hne⟩ := Subtype.ext hgb
              show (↑((sphereComplContraction n y x₀ hne)
                (t, (⟨g z, hg z⟩ : {w : sphere n // w ≠ y}))) : sphere n) = g z
              rw [hz', hfix, hgb] }⟩

end

end Work.Stems
