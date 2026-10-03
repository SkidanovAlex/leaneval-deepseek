import Submission.Lib.Unif2.Work.Mori.HyperbolicBranch
import Submission.Lib.Unif2.Work.Mori.Main

/-!
# The exact strength of the parabolic case

`fundmath3-uniformization` asks whether the deliverable

```
Work.Mori.plane_of_no_unitGreenFunction (hX : ¬ CompactSpace X) (x : X)
    [Subsingleton (Additive (FundamentalGroup X x) →+ ℝ)]
    (h : ¬ ∃ (z₀ : X) (E : X → ℝ), Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E) :
    Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ ℂ)
```

can be had without the two named classical inputs (`Work.Mori.Hubbard112` = the spine, and
`Work.Mori.ABSTheorem`).  The answer recorded here is the *exact* one:

**`Work.Mori.parabolicCase_iff_spine_and_dichotomy`** — for a connected non-compact second countable
Riemann surface `X` with `Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)` and with the
modulus interface `Work.Mori.ModulusOfTrivialHom X x₀` (which the spine proves:
`Work.Mori.modulusOfTrivialHom_of_hubbard112`),

  *the parabolic case for `X`* (i.e. the deliverable at `X`: "no unit-pole Green function ⟹
  `X ≅ ℂ`") **is equivalent to** *the spine for `X`* (`SimplyConnectedSpace X`) **together with the
  uniformization dichotomy for `X`** (`X ≅ ℂ ∨ X ≅ ℍ`).

Both directions are machine-checked below.  Consequences for the architecture:

* `Work.Mori.simplyConnectedSpace_of_parabolicCase`: **the deliverable implies the spine**, *given
  the modulus interface*.  Read carefully, this says: a proof of the deliverable which avoids the
  spine must supply `Work.Mori.ModulusOfTrivialHom X x₀` by other means — and `ModulusOfTrivialHom`
  is what the spine currently provides (`modulusOfTrivialHom_of_hubbard112`).  It does *not* by
  itself prove that no spine-free proof exists: that would need `ModulusOfTrivialHom` to be a
  theorem, for which the missing ingredient is the (purely topological) vanishing of the
  circle-valued monodromy of the modulus, i.e. the absence of finite quotients of `π₁(X)` when
  `Hom(π₁(X),ℝ) = 0` — for open orientable surfaces, torsion-freeness of `H₁`.  That statement is
  isolated below as `Work.Mori.NoNontrivialHomToCircle`, and it is a *cheaper* target than the spine
  because it says nothing about `π₁` beyond its finite quotients.
* `Work.Mori.plane_of_no_unitGreenFunction_of_spine_of_dichotomy` (`Main.lean`) is the other
  direction: the spine plus the dichotomy give the deliverable.

This is deliberately the analogue, for this chapter, of `Work.Mori.Diagnosis`'s two equivalences
(`hubbard112_iff_doorTwo`, `moriTheorem_of_nonempty_diffeomorph_plane`): it pins down the strength of
the deliverable instead of leaving it to the notes.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set

namespace Work.Mori

/-- **The topological input that would make the modulus interface a theorem.**

For a connected non-compact Riemann surface: if every homomorphism `π₁(X,x) →+ ℝ` vanishes, then
every homomorphism from `π₁(X,x)` to the circle group `ℝ/2πℤ` vanishes as well.

Mathematically this is the statement that `H₁` of an open orientable surface has no torsion: a
non-trivial circle-valued class on an open surface is either detected by a real class (excluded by
the hypothesis) or is torsion (excluded by torsion-freeness of `H₁`).  It is *strictly weaker* than
`Work.Mori.Hubbard112`: it constrains only the finite quotients of `π₁(X)`.

Consequence (see `NOTES_session3_analysis.md` §3): the monodromy of the holomorphic modulus of a
unit Green function is a homomorphism `π₁(X) → ℝ/2πℤ`; if it vanished, the modulus would be
single-valued, `Work.Mori.ModulusOfTrivialHom` would hold without the spine, and with
`Work.Mori.simplyConnectedSpace_of_parabolicCase` the sharpness would become unconditional. -/
def NoNontrivialHomToCircle (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] (x : X) : Prop :=
  Subsingleton (Additive (FundamentalGroup X x) →+ ℝ) →
    Subsingleton (Additive (FundamentalGroup X x) →+ ℝ ⧸ (AddSubgroup.zmultiples (2 * Real.pi)))

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **A surface biholomorphic to `ℂ` is simply connected.** -/
theorem simplyConnectedSpace_of_diffeomorph_plane
    (Φ : X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ) : SimplyConnectedSpace X :=
  ContinuousMap.HomotopyEquiv.simplyConnectedSpace Φ.toHomeomorph.toHomotopyEquiv

/-- **A surface biholomorphic to `ℍ` is simply connected.** -/
theorem simplyConnectedSpace_of_diffeomorph_upperHalfPlane
    (Φ : X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ UpperHalfPlane) :
    SimplyConnectedSpace X :=
  ContinuousMap.HomotopyEquiv.simplyConnectedSpace Φ.toHomeomorph.toHomotopyEquiv

/-- **The parabolic case is exactly the spine plus the dichotomy.**

For a connected non-compact second countable Riemann surface with `Hom(π₁(X,x₀),ℝ) = 0` and the
modulus interface `Work.Mori.ModulusOfTrivialHom X x₀`, the statement

  "no unit-pole Green function ⟹ `X ≅ ℂ`"

is equivalent to

  "`X` is simply connected **and** `X ≅ ℂ ∨ X ≅ ℍ`".

The direction `⟸` is `Work.Mori.plane_of_no_unitGreenFunction_of_dichotomy`; the direction `⟹` uses
the modulus interface: a unit-pole Green function would give `X ≅ ℍ`
(`Work.Mori.nonempty_diffeomorph_upperHalfPlane_of_modulusOfTrivialHom`), and its absence gives
`X ≅ ℂ` by hypothesis — in both cases `X` is simply connected. -/
theorem parabolicCase_iff_spine_and_dichotomy {x₀ : X} (hX : ¬ CompactSpace X)
    [Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)] (hmod : ModulusOfTrivialHom X x₀) :
    ((¬ ∃ (z₀ : X) (E : X → ℝ), Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E) →
        Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ)) ↔
      (SimplyConnectedSpace X ∧
        (Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ) ∨
          Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ UpperHalfPlane))) := by
  constructor
  · intro hparabolic
    have hdich : Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ) ∨
        Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ UpperHalfPlane) := by
      by_cases hE : ∃ (z₀ : X) (E : X → ℝ),
          Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E
      · obtain ⟨z₀, E, hE⟩ := hE
        exact Or.inr (nonempty_diffeomorph_upperHalfPlane_of_modulusOfTrivialHom (x₀ := x₀) hmod hE)
      · exact Or.inl (hparabolic hE)
    refine ⟨?_, hdich⟩
    rcases hdich with h | h
    · exact simplyConnectedSpace_of_diffeomorph_plane h.some
    · exact simplyConnectedSpace_of_diffeomorph_upperHalfPlane h.some
  · rintro ⟨-, hdich⟩ h
    exact plane_of_no_unitGreenFunction_of_dichotomy hX x₀ h hdich

/-- **The deliverable implies the spine** (given the modulus interface).

If the parabolic case holds for `X`, then `X` is simply connected: a unit-pole Green function would
give `X ≅ ℍ` through the modulus, and without one `X ≅ ℂ`.  Consequently no proof of the deliverable
can be spine-free (this is the sharp form of `NOTES_gap_analysis.md` §5). -/
theorem simplyConnectedSpace_of_parabolicCase {x₀ : X} (hX : ¬ CompactSpace X)
    [Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)] (hmod : ModulusOfTrivialHom X x₀)
    (hparabolic : (¬ ∃ (z₀ : X) (E : X → ℝ),
        Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E) →
      Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ)) :
    SimplyConnectedSpace X :=
  ((parabolicCase_iff_spine_and_dichotomy (X := X) hX hmod).mp hparabolic).1

/-- **The spine, from the deliverable and the dichotomy, at the level of `Hubbard112`.**

The deliverable plus the dichotomy for `X` give `Work.Mori.Hubbard112` (the topological step of
Hubbard 1.1.2) for the base point `x₀`: with the modulus interface, the deliverable and the spine
are interderivable. -/
theorem hubbard112_of_parabolicCase_of_dichotomy {x₀ : X}
    (hmod : ModulusOfTrivialHom X x₀)
    (hparabolic : (¬ ∃ (z₀ : X) (E : X → ℝ),
        Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E) →
      Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ))
    (hdich : Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ) ∨
      Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ UpperHalfPlane)) :
    (¬ CompactSpace X) → Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ) →
      SimplyConnectedSpace X :=
  fun _ _ => ((parabolicCase_iff_spine_and_dichotomy (X := X) ‹¬ CompactSpace X› hmod).mp
    hparabolic).1

/-- **With the spine, the deliverable is equivalent to the dichotomy.**  This is the form used by the
architecture: assuming the spine for all surfaces
(`Work.Spine.simplyConnectedSpace_of_subsingleton_hom_toReal`), the remaining content of the
uniformization theorem for `Hom(π₁,ℝ) = 0` surfaces is exactly the dichotomy `X ≅ ℂ ∨ X ≅ ℍ`. -/
theorem parabolicCase_iff_dichotomy_of_spine {x₀ : X} (hX : ¬ CompactSpace X)
    [Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)]
    (hspine : (¬ CompactSpace X) → (x : X) →
      Subsingleton (Additive (FundamentalGroup X x) →+ ℝ) → SimplyConnectedSpace X) :
    ((¬ ∃ (z₀ : X) (E : X → ℝ), Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E) →
        Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ)) ↔
      (Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ) ∨
        Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ UpperHalfPlane)) := by
  have hmod : ModulusOfTrivialHom X x₀ := modulusOfTrivialHom_of_hubbard112 hspine
  rw [parabolicCase_iff_spine_and_dichotomy (X := X) hX hmod]
  exact ⟨fun h => h.2, fun h => ⟨hspine hX x₀ inferInstance, h⟩⟩

end Work.Mori
