import Submission.Lib.Unif2.UnifDeps
import Submission.Lib.Unif2.GreenInterface
import Submission.Lib.Unif2.GreenModulus
import Submission.Lib.Unif2.Helpers

/-!
# The simply connected case of the uniformization theorem: interfaces

This module is the *interface layer* of the subproject
`Submission/Work/SimplyConnected/`.  Its deliverable is

> `Work.SC.uniformization_of_simplyConnected` — a connected, second countable, simply connected,
> non-compact Riemann surface is biholomorphic to `ℂ` or to the upper half plane
> (`Work.SimplyConnected.uniformization_of_simplyConnected` is an `alias` of the same theorem).

The chain of the shared library that is used is the **hyperbolic / parabolic dichotomy** of
`Submission.GreenInterface`:

* if `X` carries a *weak Green function* at `z₀` — `E > 0` off `z₀`, harmonic on `X \ {z₀}`, all
  superlevel sets `{ε ≤ E}` compact (`Submission.HasGreenFunctionWeak`) — then the hyperbolic
  endgame `Submission.uniformization_of_properInto_disc` (read off from a *holomorphic modulus*
  `Φ` of `E`, `Submission.HasLogPoleAt` + `‖Φ‖ = exp (-E)`) concludes the theorem;
* if `X` carries no weak Green function at all, then `X` is parabolic, and a simply connected
  parabolic surface is `ℂ`.

The three mathematical inputs of the reduction, each the deliverable of a parallel subproject, are
stated as explicit hypotheses of the theorems below, so that everything here is *proved*:

* `hA` : `Submission.HasGreenFunctionWeak z₀ E ⟹ ∃ E', Submission.HasGreenFunctionE z₀ E'`
  (normalisation of the logarithmic pole; `Work.Potential`, Bôcher + removable singularities);
* `hB` : `Submission.HasGreenFunctionE z₀ E ⟹ ∃ Φ, …` (the holomorphic modulus of a Green
  function; this is where the simple connectedness of `X` is used — the monodromy of the
  multivalued function `exp (-(E + iE*))` over the simply connected `X` is trivial;
  `Work.Modulus`);
* `hC` : `(∀ z₀ E, ¬ HasGreenFunctionWeak z₀ E) ⟹ Nonempty (X ≃ₘ⟮mℂ,mℂ⟯ ℂ)` (the parabolic case;
  `Work.Parabolic`).

Because these three are stated for a *weak/strong Green function* and for the parabolic case, and
the deliverable's hypothesis is the stronger `SimplyConnectedSpace X`, the reduction below is
genuine: `SimplyConnectedSpace X` implies the `Subsingleton (Additive (FundamentalGroup X x) →+ ℝ)`
used by the parallel subprojects (`subsingleton_hom_additive_fundamentalGroup_of_simplyConnected`).
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Work.SC

/-! ## The bridge: simple connectivity kills the additive characters of `π₁` -/

section Bridge

variable {X : Type*} [TopologicalSpace X]

/-- **A simply connected space has no non-trivial additive character of its fundamental group.**
This bridge lets every library lemma stated with the hypothesis
`Subsingleton (Additive (FundamentalGroup X x) →+ ℝ)` be applied to a simply connected `X`
(in particular `Submission.exists_holomorphicOnX_re_of_harmonic`, whose use is the only place
where the simple connectivity hypothesis enters the hyperbolic case). -/
theorem subsingleton_hom_additive_fundamentalGroup_of_simplyConnected
    [SimplyConnectedSpace X] (x : X) :
    Subsingleton (Additive (FundamentalGroup X x) →+ ℝ) := by
  haveI : Subsingleton (FundamentalGroup X x) := inferInstance
  infer_instance

end Bridge

/-! ## The hyperbolic endgame -/

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The holomorphic modulus of a (weak) Green function at `z₀`.**  There is `c > 0` and a
holomorphic `Φ : X → ℂ` with a *simple* zero at `z₀` (`Submission.HasLogPoleAt`) whose modulus is
`exp (-(c E))`.

The factor `c` is the (inverse of the) order of the logarithmic pole of `E`; allowing it means
that no normalisation of `E` is needed. -/
def GreenModulusAt (z₀ : X) (E : X → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ Φ : X → ℂ, Submission.HolomorphicOnX Φ Set.univ ∧
    Submission.HasLogPoleAt z₀ Φ ∧ ∀ y : X, y ≠ z₀ → ‖Φ y‖ = Real.exp (-(c * E y))

/-- **The hyperbolic endgame.**  A weak Green function together with a holomorphic modulus for it
gives the uniformization conclusion (indeed `X ≅ 𝔻`).

Every hypothesis of `Submission.uniformization_of_properInto_disc` is read off from `(E, Φ)`:
`Φ` maps into the disc because `E > 0` off `z₀`; `Φ ⁻¹' {0} = {z₀}` because `‖Φ‖ = exp (-E)` never
vanishes off `z₀`; `Φ` is proper into the disc because the superlevel sets of `E` are compact. -/
theorem uniformization_of_greenModulusAt (hX : ¬ CompactSpace X) {z₀ : X} {E : X → ℝ}
    (hE : Submission.HasGreenFunctionWeak z₀ E) (h : GreenModulusAt z₀ E) :
    Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ ℂ) ∨ Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ UpperHalfPlane) := by
  obtain ⟨c, hc, Φ, hΦ, hpole, hmod⟩ := h
  have hpos : ∀ x : X, x ≠ z₀ → 0 < (fun x : X => c * E x) x := fun x hx => mul_pos hc (hE.1 x hx)
  have hinf : ∀ ε : ℝ, 0 < ε → IsCompact {x : X | ε ≤ (fun x : X => c * E x) x} := by
    intro ε hε
    have hset : {x : X | ε ≤ c * E x} = {x : X | ε / c ≤ E x} := by
      ext x
      simp only [Set.mem_ofPred_eq]
      exact ⟨fun h => by rw [div_le_iff₀ hc]; linarith,
        fun h => by rw [div_le_iff₀ hc] at h; linarith⟩
    rw [hset]
    exact hE.2.2 (ε / c) (div_pos hε hc)
  have hzero : Φ z₀ = 0 := Submission.phi_zero_of_logPole hΦ hpole
  exact Submission.uniformization_of_properInto_disc (X := X) hX
    (Submission.phi_mem_ball hpos hmod hzero)
    (fun K hK hKsub =>
      Submission.isCompact_preimage_of_green hpos hmod hzero hinf hΦ.continuous hK hKsub)
    hΦ (Submission.phi_preimage_zero hpos hmod hzero)
    (Submission.phi_deriv_ne_zero_of_logPole hpole)

/-! ## Assembly of the two branches -/

/-- **The hyperbolic branch of uniformization.**  Given a weak Green function at `z₀`, the
normalisation of its pole (`hA`) and the existence of a holomorphic modulus for the resulting
strong Green function (`hB`), the uniformization conclusion holds. -/
theorem uniformization_of_hasGreenFunctionWeak (hX : ¬ CompactSpace X) {z₀ : X} {E : X → ℝ}
    (hE : Submission.HasGreenFunctionWeak z₀ E)
    (hA : ∀ {z₀ : X} {E : X → ℝ}, Submission.HasGreenFunctionWeak z₀ E →
      ∃ E' : X → ℝ, Submission.HasGreenFunctionE z₀ E')
    (hB : ∀ {z₀ : X} {E : X → ℝ}, Submission.HasGreenFunctionE z₀ E →
      ∃ Φ : X → ℂ, Submission.HolomorphicOnX Φ Set.univ ∧ Submission.HasLogPoleAt z₀ Φ ∧
        ∀ y : X, y ≠ z₀ → ‖Φ y‖ = Real.exp (-(E y))) :
    Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ ℂ) ∨ Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ UpperHalfPlane) := by
  obtain ⟨E', hE'⟩ := hA hE
  obtain ⟨Φ, hΦ, hpole, hmod⟩ := hB hE'
  refine uniformization_of_greenModulusAt hX hE'.1 ⟨1, one_pos, Φ, hΦ, hpole, ?_⟩
  intro y hy
  simpa using hmod y hy

/-- **The simply connected, non-compact case of uniformization, reduced to three explicit
inputs.**  The dichotomy `(∃ z₀ E, HasGreenFunctionWeak z₀ E) ∨ ¬(…)` is a tautology, so this is a
genuine reduction of the deliverable to

* `hA` : weak Green data ⟹ strong Green data (`Work.Potential`);
* `hB` : strong Green data ⟹ holomorphic modulus (`Work.Modulus`);
* `hC` : the parabolic branch, i.e. no weak Green function at all (`Work.Parabolic`). -/
theorem uniformization_of_simplyConnected_of_inputs [SimplyConnectedSpace X]
    (hX : ¬ CompactSpace X)
    (hA : ∀ {z₀ : X} {E : X → ℝ}, Submission.HasGreenFunctionWeak z₀ E →
      ∃ E' : X → ℝ, Submission.HasGreenFunctionE z₀ E')
    (hB : ∀ {z₀ : X} {E : X → ℝ}, Submission.HasGreenFunctionE z₀ E →
      ∃ Φ : X → ℂ, Submission.HolomorphicOnX Φ Set.univ ∧ Submission.HasLogPoleAt z₀ Φ ∧
        ∀ y : X, y ≠ z₀ → ‖Φ y‖ = Real.exp (-(E y)))
    (hC : (∀ (z₀ : X) (E : X → ℝ), ¬ Submission.HasGreenFunctionWeak z₀ E) →
      Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ ℂ)) :
    Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ ℂ) ∨ Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ UpperHalfPlane) := by
  by_cases h : ∃ z₀ : X, ∃ E : X → ℝ, Submission.HasGreenFunctionWeak z₀ E
  · obtain ⟨z₀, E, hE⟩ := h
    exact uniformization_of_hasGreenFunctionWeak hX hE hA hB
  · exact Or.inl (hC fun z₀ E hE => h ⟨z₀, E, hE⟩)

end Work.SC
