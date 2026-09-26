import Mathlib
import Submission.Work.SurgeryInvariance.Defs
import Submission.Work.InnermostDisk.not_isEssential_of_section
import Submission.Work.TorusCover.ParamTorus_exists_liftOf

/-!
# A loop lying in an embedded disc of the torus is inessential

`Work.SurgeryInvariance.DiscRegion P` records an embedded disc `D` of the surface
`F = P.carrier` of a parametrised torus: an injective continuous map `D.e` of the closed unit
disc of `ℂ` into `F`, whose interior is open in `F`.

A closed curve `γ` of `F` whose image lies in `D.carrier` is *inessential*: the disc is
contractible, so `γ` is null-homotopic in `F` and its winding vector vanishes.  This is the
statement used to check that the local model of a `2`-surgery of the sphere family
(`Work.SurgeryInvariance.SurgeryStep`) changes the winding span of the region in a controlled
way: none of the homology of the region is carried by the disc that the surgery adds or
removes.

The proof is the chart/section argument of `Work.InnermostDisk.not_isEssential_of_section`: the
parametrisation `psiMap P.psi : ℝ² → F` is a covering map
(`Work.TorusCover.isCoveringMap_psiMapToRange_param`), and `D.e`, viewed as a map of the
(contractible, hence simply connected) closed disc onto `F`, lifts through it
(`exists_lift_disc`); composing that lift with the inverse of `D.e` — continuous because `D.e`
is an injective continuous map from a compact space into a Hausdorff space — gives a continuous
section `σ` of `P.psi` over `D.carrier`.  Composing `σ` with `γ` yields a `2π`-periodic lift
of `γ`, so the winding vector of `γ` is zero.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.SurgeryInvariance.DiscRegion

/-- The closed unit disc of `ℂ`, on which the parametrisation `DiscRegion.e` is defined. -/
abbrev unitDisc : Set ℂ := Metric.closedBall (0 : ℂ) 1

/-- **A lift of the parametrisation of an embedded disc.**  The parametrisation of an embedded
disc of the torus lifts to the parameter plane: there is a continuous `Ξ : 𝔻 → ℝ²` with
`P.psi (Ξ z).1 (Ξ z).2 = D.e z` for all `z`.

This is the covering-space lifting theorem applied to the covering map `psiMapToRange P.psi`
and the simply connected, locally path connected closed disc (which is convex, hence
contractible). -/
theorem exists_lift_disc {P : Work.CoreTopology.ParamTorus}
    (D : Work.SurgeryInvariance.DiscRegion P) :
    ∃ Ξ : C(unitDisc, ℝ × ℝ), ∀ z : unitDisc,
      P.psi (Ξ z).1 (Ξ z).2 = D.e z := by
  have hcov : IsCoveringMap (Work.TorusCover.psiMapToRange P.psi) :=
    Work.TorusCover.isCoveringMap_psiMapToRange_param P
  have hcomp : CompactSpace unitDisc :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) 1)
  have hconv : Convex ℝ unitDisc := convex_closedBall (0 : ℂ) 1
  have hcontr : ContractibleSpace unitDisc :=
    hconv.contractibleSpace ⟨0, by simp [Metric.mem_closedBall]⟩
  have hsc : SimplyConnectedSpace unitDisc := inferInstance
  have hlpc : LocallyPathConnectedSpace unitDisc := hconv.locallyPathConnectedSpace
  -- a point of the parameter plane lying over the centre of the disc
  obtain ⟨p₀, hp₀⟩ : ∃ p₀ : ℝ × ℝ, Work.TorusCover.psiMap P.psi p₀ = D.e 0 := D.mem 0
  -- the disc, as a map into the surface `F = P.carrier`
  have hE : Continuous fun z : unitDisc =>
      (⟨D.e z, D.mem z⟩ : Set.range (Work.TorusCover.psiMap P.psi)) :=
    Continuous.subtype_mk D.e.continuous (fun z => D.mem z)
  obtain ⟨Ξ, ⟨-, hlift⟩, -⟩ := hcov.existsUnique_continuousMap_lifts
    (⟨fun z => ⟨D.e z, D.mem z⟩, hE⟩ :
      C(unitDisc, Set.range (Work.TorusCover.psiMap P.psi))) 0 p₀
    (Subtype.ext hp₀)
  refine ⟨Ξ, fun z => ?_⟩
  have h := congrArg Subtype.val (congr_fun hlift z)
  simpa [Work.TorusCover.psiMap] using h

/-- **A curve lying in an embedded disc of the torus is inessential.**

The image of the disc `D` in the surface `F = P.carrier` is contractible (it is homeomorphic to
the closed unit disc, because `D.e` is an injective continuous map from a compact space into a
Hausdorff space), so every closed curve of `F` contained in it is null-homotopic in `F` and
hence has vanishing winding vector. -/
theorem not_isEssential {P : Work.CoreTopology.ParamTorus}
    (D : Work.SurgeryInvariance.DiscRegion P) (γ : Work.CoreTopology.ClosedCurve P)
    (hγ : ∀ t : ℝ, γ t ∈ D.carrier) : ¬ Work.CoreTopology.IsEssential P γ := by
  obtain ⟨Ξ, hΞ⟩ := exists_lift_disc D
  -- the inverse of `D.e` on its range is continuous: `D.e` is an injective continuous map of
  -- the compact disc into the Hausdorff space `ℝ³`
  have hcomp : CompactSpace unitDisc :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) 1)
  have he : Continuous (Equiv.ofInjective D.e D.inj) :=
    Continuous.subtype_mk D.e.continuous (fun z => Set.mem_range_self z)
  let homeo : unitDisc ≃ₜ D.carrier :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofInjective D.e D.inj) he
  -- the lift of the disc, composed with the inverse of `D.e`, is a section of `P.psi` over
  -- the image of the disc
  have hcont : Continuous fun x : D.carrier => Ξ (homeo.symm x) :=
    Ξ.continuous.comp homeo.symm.continuous
  refine Work.InnermostDisk.not_isEssential_of_section
    (s := D.carrier) ⟨fun x => Ξ (homeo.symm x), hcont⟩ ?_ hγ
  intro x
  show P.psi (Ξ (homeo.symm x)).1 (Ξ (homeo.symm x)).2 =
    (x : LeanEval.KnotTheory.PardonDistortion.R3)
  rw [hΞ (homeo.symm x)]
  exact congrArg Subtype.val (homeo.apply_symm_apply x)

end Work.SurgeryInvariance.DiscRegion
