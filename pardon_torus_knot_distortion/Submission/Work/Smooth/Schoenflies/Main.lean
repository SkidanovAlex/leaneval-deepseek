import Submission.Work.Smooth.Schoenflies.Injectivity
import Submission.Work.Smooth.SphereJordan.Caratheodory.Assembly
import Submission.Work.Smooth.SphereJordan.Caratheodory.InverseAnalytic
import Submission.Work.Smooth.SphereJordan.planeHypothesis_of_caratheodoryJordan

/-!
# The planar Jordan–Schoenflies theorem from Carathéodory's extension theorem

This file is the headstone of the chapter `Submission/Work/Smooth/Schoenflies/`: it assembles the
boundary-correspondence theorem `Work.Smooth.Schoenflies.injOn_of_extension` (injectivity of the
boundary values of a Carathéodory extension of a biholomorphism `𝔻 → Ω`) with the classical
construction of the biholomorphism (`Caratheodory.exists_analytic_bijOn_ball_domain`, i.e. the
Riemann mapping theorem for a Jordan domain) into

> **the closure of a Jordan domain is homeomorphic to the closed unit disc**
> (`caratheodoryJordan_of_extension`, the hypothesis `H` of
> `Work.Smooth.SphereJordan.planeHypothesis_of_caratheodoryJordan`),

and hence into the planar Jordan–Schoenflies theorem

* `planeHypothesis_of_caratheodoryExtension` —
  `Work.Smooth.SphereJordan.PlaneHypothesis`;
* `classicalInput_of_caratheodoryExtension` — `Work.Smooth.Jordan.ClassicalInput` (the same
  statement, cf. `planeHypothesis_iff_classicalInput`);
* `schoenfliesInput_of_caratheodoryExtension` — `Work.Smooth.Jordan.SchoenfliesInput c` for every
  `C¹` simple closed plane curve `c`;
* `nonempty_planeSchoenflies_of_caratheodoryExtension` — `Nonempty (PlaneSchoenflies c)`.

The single input is the **Carathéodory extension theorem** (`CaratheodoryExtensionInput` below),
i.e. uniform continuity of a biholomorphism of the disc onto a Jordan domain, whose proof (by the
length–area/cap argument) lives in `Submission/Work/Smooth/SphereJordan/Caratheodory/`.
-/

open Set Metric
open scoped Topology

namespace Work.Smooth.Schoenflies

noncomputable section

/-- **Carathéodory's extension theorem (continuity part)**, as a `Prop`.

A biholomorphism of the unit disc onto a Jordan domain (a bounded simply connected domain whose
frontier is the trace of a simple closed curve) extends continuously to the closed disc, with
boundary values in the frontier.  This is exactly the statement proved by the length–area/cap
argument of `Submission/Work/Smooth/SphereJordan/Caratheodory/`; see
`Work.Smooth.SphereJordan.Caratheodory` and the file
`Submission/Work/Smooth/SphereJordan/caratheodory_extension_continuous.lean`. -/
def CaratheodoryExtensionInput : Prop :=
  ∀ {Ω : Set ℂ}, IsOpen Ω → Ω.Nonempty → Bornology.IsBounded Ω → SimplyConnectedSpace ↥Ω →
    ∀ {γ : ℝ → ℂ}, Continuous γ → Function.Periodic γ (2 * Real.pi) →
      Set.InjOn γ (Set.Ico 0 (2 * Real.pi)) → frontier Ω = Set.range γ →
      ∀ {f : ℂ → ℂ}, DifferentiableOn ℂ f unitBall → Set.InjOn f unitBall →
        f '' unitBall = Ω →
        ∃ G : ℂ → ℂ, ContinuousOn G unitClosedBall ∧
          (∀ z ∈ unitBall, G z = f z) ∧
          ∀ ζ : ℂ, ‖ζ‖ = 1 → G ζ ∈ frontier Ω

/-- **Carathéodory's boundary correspondence, closed-disc form.**  The closure of a Jordan domain is
homeomorphic to the closed unit disc.  This is the hypothesis `H` of
`Work.Smooth.SphereJordan.planeHypothesis_of_caratheodoryJordan`. -/
theorem caratheodoryJordan_of_extension (h : CaratheodoryExtensionInput) :
    ∀ {Ω : Set ℂ}, IsOpen Ω → Ω.Nonempty → Bornology.IsBounded Ω → SimplyConnectedSpace ↥Ω →
      ∀ {γ : ℝ → ℂ}, Continuous γ → Function.Periodic γ (2 * Real.pi) →
        Set.InjOn γ (Set.Ico 0 (2 * Real.pi)) → frontier Ω = Set.range γ →
        Nonempty (↥(closure Ω) ≃ₜ ↥(Metric.closedBall (0 : ℂ) 1)) := by
  intro Ω hΩo hΩne hΩb hΩsc γ hγc hγp hγi hfr
  obtain ⟨f, g, hf, hg, hfa, hga, hgf, hfg⟩ :=
    Work.Smooth.SphereJordan.Caratheodory.exists_analytic_bijOn_ball_domain hΩo hΩne hΩb hΩsc
  have hfsurj : f '' unitBall = Ω := hf.surjOn.image_eq_of_mapsTo hf.mapsTo
  obtain ⟨G, hGc, hGf, hGb⟩ :=
    h hΩo hΩne hΩb hΩsc hγc hγp hγi hfr hfa.differentiableOn hf.injOn hfsurj
  have hGinj : Set.InjOn G unitClosedBall :=
    injOn_of_extension hΩo hΩne hΩb hΩsc hγc hγp hγi hfr hfa.differentiableOn hf.injOn
      hfsurj hGc hGf hGb
  have himg : G '' unitBall = Ω := by
    rw [← hfsurj]
    exact Set.image_congr (fun z hz => hGf z hz)
  exact Work.Smooth.SphereJordan.Caratheodory.homeo_of_injective_extension hGc hGinj himg

/-- **The planar Jordan–Schoenflies theorem** (`Work.Smooth.SphereJordan.PlaneHypothesis`), from
Carathéodory's extension theorem. -/
theorem planeHypothesis_of_caratheodoryExtension (h : CaratheodoryExtensionInput) :
    Work.Smooth.SphereJordan.PlaneHypothesis :=
  Work.Smooth.SphereJordan.planeHypothesis_of_caratheodoryJordan
    (caratheodoryJordan_of_extension h)

/-- **The classical input of the Jordan chapter** (`Work.Smooth.Jordan.ClassicalInput`), from
Carathéodory's extension theorem. -/
theorem classicalInput_of_caratheodoryExtension (h : CaratheodoryExtensionInput) :
    Work.Smooth.Jordan.ClassicalInput :=
  Work.Smooth.SphereJordan.planeHypothesis_iff_classicalInput.mp
    (planeHypothesis_of_caratheodoryExtension h)

/-- **`SchoenfliesInput`** (`Work.Smooth.Jordan.SchoenfliesInput`) for a `C¹` simple closed plane
curve, from Carathéodory's extension theorem. -/
theorem schoenfliesInput_of_caratheodoryExtension (h : CaratheodoryExtensionInput)
    (c : Work.Smooth.Jordan.PlaneCurve) (_hdiff : ContDiff ℝ 1 c.γ) :
    Work.Smooth.Jordan.SchoenfliesInput c :=
  classicalInput_of_caratheodoryExtension h c

/-- **A spanning embedded disc** (`Nonempty (PlaneSchoenflies c)`) for a `C¹` simple closed plane
curve, from Carathéodory's extension theorem. -/
theorem nonempty_planeSchoenflies_of_caratheodoryExtension (h : CaratheodoryExtensionInput)
    (c : Work.Smooth.Jordan.PlaneCurve) (_hdiff : ContDiff ℝ 1 c.γ) (hs : c.IsSimple) :
    Nonempty (Work.Smooth.Jordan.PlaneSchoenflies c) :=
  classicalInput_of_caratheodoryExtension h c hs

end

end Work.Smooth.Schoenflies
