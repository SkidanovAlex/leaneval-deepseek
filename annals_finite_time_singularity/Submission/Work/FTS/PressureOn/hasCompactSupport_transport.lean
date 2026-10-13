import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.integral_div_eq_zero_of_hasFDerivAt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Compact support is preserved by the transport to the coordinate space

`transport G x = WithLp.ofLp (G (WithLp.toLp 2 x))` is `G` read through the linear isometry
`toLpCLE : (Fin 3 → ℝ) ≃L[ℝ] ℝ³` (`⇑toLpCLE = WithLp.toLp 2`, whose inverse is
`ofLpCLM = WithLp.ofLp`).  Consequently `transport G = toLpCLE.symm ∘ G ∘ toLpCLE`, i.e. `G`
conjugated by a homeomorphism which is a linear isometry onto its image, and

* `Function.support (transport G) = toLpCLE ⁻¹' Function.support G`
  (the inverse is injective and maps `0` to `0`), hence
* `tsupport (transport G) = toLpCLE ⁻¹' tsupport G`
  (a homeomorphism pulls closures back to closures),

so compactness of the support of `G` transfers to the support of `transport G`.

This is the bookkeeping step that lets the divergence theorem of
`Submission.Work.FTS.PressureOn.integral_div_eq_zero_of_hasFDerivAt` — which is stated for the
transported field on `Fin 3 → ℝ` — be fed with the compact support of the physical field on `ℝ³`.
-/

open FiniteTimeSingularity Set

namespace Work.FTS.PressureOn

/-- **The support of the transported field is the pull-back of the support of the field**: the
linear isometry `toLpCLE` is injective with inverse mapping `0` to `0`. -/
theorem support_transport (G : R3 → R3) :
    Function.support (transport G) = toLpCLE.toHomeomorph ⁻¹' Function.support G := by
  ext x
  simp only [Function.mem_support, Set.mem_preimage]
  rw [show transport G x = toLpCLE.symm (G (toLpCLE x)) from rfl,
    show toLpCLE.toHomeomorph x = toLpCLE x from rfl]
  simp only [ne_eq, ContinuousLinearEquiv.map_eq_zero_iff]

/-- **The (topological) support of the transported field is the pull-back of the (topological)
support of the field**: `tsupport = closure ∘ support`, and a homeomorphism commutes with
`closure` under pull-back. -/
theorem tsupport_transport (G : R3 → R3) :
    tsupport (transport G) = toLpCLE.toHomeomorph ⁻¹' tsupport G := by
  rw [tsupport, tsupport, Homeomorph.preimage_closure]
  congr 1
  exact support_transport G

/-- **`HasCompactSupport` is preserved by the transport to the coordinate space.** -/
theorem hasCompactSupport_transport {G : Work.FTS.PressureOn.R3 → Work.FTS.PressureOn.R3}
    (hG : HasCompactSupport G) : HasCompactSupport (Work.FTS.PressureOn.transport G) := by
  rw [HasCompactSupport, tsupport_transport G]
  exact toLpCLE.toHomeomorph.isCompact_preimage.mpr hG.isCompact

end Work.FTS.PressureOn
