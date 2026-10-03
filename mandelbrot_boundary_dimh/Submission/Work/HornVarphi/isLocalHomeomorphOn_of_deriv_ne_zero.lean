import Mathlib
import Submission.Work.Interfaces.HornParts

namespace Work.HornVarphi

open Set Topology

/-- On the open set `B`, a holomorphic function `f` with non-vanishing derivative (off a set `nc`
of "critical" points) is a local homeomorphism on the locus where the derivative is nonzero.

At a point `x ∈ B` with `x ∉ nc`, `f` is analytic at `x` (holomorphy on the open `B`), hence has a
strict derivative there; since `deriv f x ≠ 0` the linear map is invertible, and the inverse
function theorem (`HasStrictFDerivAt.toOpenPartialHomeomorph`) produces an ambient partial
homeomorphism equal to `f`.  Restricting to the open subtype `↥B` via
`OpenPartialHomeomorph.subtypeRestr` gives the required local homeomorphism of
`fun z : ↥B => f z`. -/
theorem isLocalHomeomorphOn_of_deriv_ne_zero {f : ℂ → ℂ} {B : Set ℂ} (hBopen : IsOpen B)
    (hdiff : DifferentiableOn ℂ f B) (nc : Set ℂ)
    (hd : ∀ z ∈ B, z ∉ nc → deriv f z ≠ 0) :
    IsLocalHomeomorphOn (fun z : ↥B => f z) {z : ↥B | (z : ℂ) ∉ nc} := by
  refine IsLocalHomeomorphOn.mk _ _ fun x hx => ?_
  have hxB : (x : ℂ) ∈ B := x.2
  have hxnc : (x : ℂ) ∉ nc := hx
  have hne : deriv f (x : ℂ) ≠ 0 := hd x hxB hxnc
  -- `f` is holomorphic on the open set `B`, hence analytic at `x`
  have hana : AnalyticAt ℂ f (x : ℂ) := hdiff.analyticAt (hBopen.mem_nhds hxB)
  -- hence it has a strict derivative there
  have hstrict : HasStrictDerivAt f (deriv f (x : ℂ)) (x : ℂ) := hana.hasStrictDerivAt
  -- whose linear map is invertible because the derivative is nonzero
  have hfd : HasStrictFDerivAt f
      (ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 (deriv f (x : ℂ)) hne) : ℂ →L[ℂ] ℂ)
      (x : ℂ) := hstrict.hasStrictFDerivAt_equiv hne
  -- the inverse function theorem gives an ambient partial homeomorphism equal to `f`
  let e₀ : OpenPartialHomeomorph ℂ ℂ := hfd.toOpenPartialHomeomorph f
  have hxe₀ : (x : ℂ) ∈ e₀.source := hfd.mem_toOpenPartialHomeomorph_source
  have hneB : Nonempty (⟨B, hBopen⟩ : TopologicalSpace.Opens ℂ) := ⟨⟨(x : ℂ), hxB⟩⟩
  refine ⟨e₀.subtypeRestr hneB, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact hxe₀
  · intro y _
    rfl

end Work.HornVarphi
