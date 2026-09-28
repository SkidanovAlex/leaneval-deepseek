import Mathlib
import Submission.Work.Thom.Cohomology
import Submission.Work.Projective.cpn_cohomology

set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

/-!
# `H²(ℂ³ ∖ {0}; ℤ) = 0`

The punctured complex `3`-space `ℂ³ ∖ {0}` is homotopy equivalent to the `5`-sphere `S⁵`, and
`H²(S⁵; ℤ) = 0`; equivalently the second cohomology of `ℂ³ ∖ {0}` is a subsingleton, which is
the statement `Work.Gen.PuncturedComplexThree`.

The vanishing is the case `m = 1` of the standard computation of the cohomology of the pieces of
the standard two-cover of `ℂP^{m+2}`: the chart at `0` identifies `cpU (m+2) ∩ cpV (m+2)` with
the punctured model space `ℂ^{m+2} ∖ {0}` (`Work.Projective.cpnUV_homeo`), and the cohomology of
that intersection vanishes off degrees `0` and `2m+3`
(`Work.Projective.cpnUV_cohomology_zero`).

The extra ingredient here is only that the workspace's `ℂ³` is the *Euclidean* space
`EuclideanSpace ℂ (Fin 3)` — the type `WithLp 2 (Fin 3 → ℂ)` — rather than the plain function type
`Fin 3 → ℂ` used by the projective-space chapter; the two are homeomorphic by the (linear)
identification `EuclideanSpace.equiv`.
-/

namespace Work.Gen

open CategoryTheory Limits

noncomputable section

/-- **`H²(ℂ³ ∖ {0}; ℤ) = 0` for the model space `ℂ³ = Fin 3 → ℂ`.**

`cpU 3 ∩ cpV 3 ⊆ ℂP³` is `ℂ³ ∖ {0}` under the chart at `0` (`Work.Projective.cpnUV_homeo 3`),
and its cohomology vanishes in degree `2` because `2 ∉ {0, 5}`
(`Work.Projective.cpnUV_cohomology_zero 2 2`). -/
theorem puncturedComplexModelH2Zero :
    IsZero (Work.Cohomology.singularCohomology ℤ 2 (TopCat.of {z : Fin 3 → ℂ // z ≠ 0})) := by
  obtain ⟨e⟩ := Work.Cohomology.cohomologyIso_of_homotopyEquiv
    (Work.Projective.cpnUV_homeo 3).toHomotopyEquiv 2
  have hz : IsZero (Work.Cohomology.singularCohomology ℤ 2
      (TopCat.of ↥(Work.Projective.cpU 3 ∩ Work.Projective.cpV 3))) :=
    Work.Projective.cpnUV_cohomology_zero 2 2 (by norm_num) (by norm_num)
  exact IsZero.of_iso hz e.symm

/-- **The punctured Euclidean complex space `EuclideanSpace ℂ (Fin 3) ∖ {0}` is homeomorphic to
the punctured model space `Fin 3 → ℂ` minus the origin.**  `EuclideanSpace ℂ (Fin 3)` is
`WithLp 2 (Fin 3 → ℂ)`, and `EuclideanSpace.equiv` is the (linear, hence zero-preserving)
identification with `Fin 3 → ℂ`. -/
noncomputable def puncturedComplexEuclideanHomeo :
    {w : EuclideanSpace ℂ (Fin 3) // w ≠ 0} ≃ₜ {z : Fin 3 → ℂ // z ≠ 0} :=
  Homeomorph.subtype (EuclideanSpace.equiv (Fin 3) ℂ).toHomeomorph (fun x => by
    show x ≠ 0 ↔ (EuclideanSpace.equiv (Fin 3) ℂ) x ≠ 0
    rw [show (EuclideanSpace.equiv (Fin 3) ℂ) x = x from rfl]
    exact ((WithLp.ofLp_eq_zero 2 (V := (Fin 3 → ℂ)) (x := x)).not).symm)

/-- **`H²(ℂ³ ∖ {0}; ℤ) = 0`.** -/
theorem PuncturedComplexThree :
    Subsingleton (Work.Thom.Coh ℤ 2 {w : EuclideanSpace ℂ (Fin 3) // w ≠ 0}) := by
  obtain ⟨e⟩ := Work.Cohomology.cohomologyIso_of_homotopyEquiv
    puncturedComplexEuclideanHomeo.toHomotopyEquiv 2
  haveI : IsZero (Work.Thom.Coh ℤ 2 {w : EuclideanSpace ℂ (Fin 3) // w ≠ 0}) :=
    IsZero.of_iso puncturedComplexModelH2Zero e
  exact ModuleCat.subsingleton_of_isZero ‹_›

end

end Work.Gen
