import Mathlib
import Submission.Work.Smooth.Morse.Defs

/-!
# The image of an open set of parameters is open in the surface

`Work.Smooth.Morse.param ψ : ℝ × ℝ → ℝ³` is the parametrisation of the surface
`F = ψ(standard torus)`.  The parametrisation is the universal covering of the torus
`F` (a local homeomorphism, indeed a covering map), so it is an *open map onto its
image*: the image of any open set of parameters is open in `F` for the subspace
topology.

This is the general fact `forgetful` lemma for a `ParamTorus`: the parametrisation
`psiMap P.psi : ℝ × ℝ → P.carrier` is `psiMapToRange P.psi` up to the identification
`P.carrier = Set.range (psiMap P.psi)`, and the latter is a covering map
(`Work.TorusCover.isCoveringMap_psiMapToRange_param`), hence a local homeomorphism,
hence an open map.
-/

open Set

namespace Work.Smooth.Morse.Surface

noncomputable section

/-- **The parametrisation of a `ParamTorus` is open onto its image.**  For any open set `U` of
parameters, `psiMap P.psi '' U` is open in the carrier `P.carrier` for the subspace topology. -/
theorem isOpenInCarrier_psiMap_image (P : Work.CoreTopology.ParamTorus)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) :
    Work.SurgeryInvariance.IsOpenInCarrier P (Work.TorusCover.psiMap P.psi '' U) := by
  -- the parametrisation, as a map onto its range, is a covering map, hence an open map
  have hmap : IsOpenMap (Work.TorusCover.psiMapToRange P.psi) :=
    (Work.TorusCover.isCoveringMap_psiMapToRange_param P).isLocalHomeomorph.isOpenMap
  rw [Work.SurgeryInvariance.IsOpenInCarrier]
  -- the preimage of the image of `U` under the range factorisation is that image
  have hEq : (Subtype.val ⁻¹' (Work.TorusCover.psiMap P.psi '' U) : Set P.carrier)
      = (Work.TorusCover.psiMapToRange P.psi '' U : Set P.carrier) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨p, hpU, hpy⟩
      exact ⟨p, hpU, Subtype.ext hpy⟩
    · rintro ⟨p, hpU, hpEq⟩
      exact ⟨p, hpU, by rw [← hpEq]; rfl⟩
  rw [hEq]
  exact hmap U hU

theorem isOpenInCarrier_image_of_isOpen (ψ : Submission.Diffeo) {U : Set (ℝ × ℝ)} (hU : IsOpen U) : Work.SurgeryInvariance.IsOpenInCarrier (Work.Smooth.Morse.torus ψ) (Work.Smooth.Morse.param ψ '' U) := by
  -- the parametrisation is `Work.TorusCover.psiMap (torus ψ).psi`
  have hset : Work.TorusCover.psiMap (Work.Smooth.Morse.torus ψ).psi = Work.Smooth.Morse.param ψ := by
    funext p
    simp [Work.TorusCover.psiMap, Work.Smooth.Morse.param, Work.Smooth.Morse.torus,
      Work.CoreTopology.ParamTorus.mapHomeomorph]
  have h := isOpenInCarrier_psiMap_image (Work.Smooth.Morse.torus ψ) (U := U) hU
  rwa [hset] at h

end

end Work.Smooth.Morse.Surface
