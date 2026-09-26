import Mathlib
import Submission.Work.Topology.SphereSlicing.Defs

/-!
# A region meeting the torus in finitely many points contains no essential loop

Let `F = P.carrier` be a parametrised torus and let `S ⊆ ℝ³` be a set with `S ∩ F` *finite*.
Then `S` contains no essential loop of `F`.

This is the degenerate case of Pardon's Lemma 4.2: a region of the ambient space whose trace on
the torus surface is finite (in particular, one whose trace on `F` is a finite set of points
rather than a union of curves) cannot carry a loop that is non-null-homotopic in `F`.

The argument is elementary.  If `γ : ClosedCurve P` has its image in `S`, then its image lies in
the finite set `S ∩ F`.  The image `Set.range γ` is the continuous image of the connected space
`ℝ`, hence preconnected, while `S ∩ P.carrier` is finite, so discrete in the `T1` space `ℝ³`
(`Set.Finite.isDiscrete`); a continuous map from a preconnected set into a discrete set is
constant (`IsPreconnected.constant_of_mapsTo`).  So `γ` is a constant curve, and the *constant*
lift of `γ` (possible because `γ 0 ∈ P.carrier`) has winding vector `(0, 0)`; by
`IsEssential.winding_ne` no lift of an essential curve can have vanishing winding, and neither
can a constant curve be essential.

This is the lemma that removes the "finite trace" case from the sphere-slicing chapter: a slice
region whose intersection with `P.carrier` is finite is vacuously fine.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Topology.SphereSlicing

/-- **A region whose trace on the torus surface is finite contains no essential loop of the
torus.**  The image of a closed curve of `P` is a continuous image of the connected space `ℝ`,
hence preconnected; if it lies in `S` it lies in the finite set `S ∩ P.carrier`, which is
discrete, so the curve is constant and has vanishing winding vector. -/
theorem not_containsEssentialLoop_of_finite_inter {P : Work.CoreTopology.ParamTorus}
    {S : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (h : (S ∩ P.carrier).Finite) : ¬ P.ContainsEssentialLoop S := by
  rintro ⟨γ, hess, hmem⟩
  -- `γ` maps the preconnected `ℝ` into the discrete set `S ∩ P.carrier`, so it is constant.
  have hconst : ∀ t s : ℝ, γ t = γ s := fun t s =>
    isPreconnected_univ.constant_of_mapsTo h.isDiscrete γ.cont.continuousOn
      (fun x _ => ⟨hmem x, γ.mem x⟩) trivial trivial
  -- The constant value of `γ` lies on the torus, so it has parameters `(x₀, y₀)`.
  obtain ⟨x₀, y₀, hxy⟩ := (P.mem_carrier_iff (γ 0)).mp (γ.mem 0)
  -- The constant lift of the constant curve `γ`, with both parameters constant.
  let L : Work.CoreTopology.LiftOf P γ :=
    { Θ := fun _ => x₀
      Φ := fun _ => y₀
      contΘ := continuous_const
      contΦ := continuous_const
      lifts := fun t => by rw [hconst t 0]; exact hxy }
  -- A lift with constant parameters has winding vector `(0, 0)`.
  have hw : L.winding = (0, 0) := by
    have h1 : (L.winding).1 = 0 := by
      have hspec := L.winding_spec.1
      have : (L.winding).1 * (2 * Real.pi) = 0 := by linarith [hspec]
      rcases mul_eq_zero.mp this with hh | hh
      · exact_mod_cast hh
      · exact absurd hh Work.CoreTopology.two_pi_ne_zero
    have h2 : (L.winding).2 = 0 := by
      have hspec := L.winding_spec.2
      have : (L.winding).2 * (2 * Real.pi) = 0 := by linarith [hspec]
      rcases mul_eq_zero.mp this with hh | hh
      · exact_mod_cast hh
      · exact absurd hh Work.CoreTopology.two_pi_ne_zero
    exact Prod.ext h1 h2
  exact (hess.winding_ne L) hw

end Work.Topology.SphereSlicing
