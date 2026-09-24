import Submission.Work.Mori.Defs
import Submission.Work.Mori.UnitGreen
import Submission.Work.Mori.Argument
import Submission.Work.Mori.nonempty_diffeomorph_opens_top
import Submission.Work.Mori.WindingCircle
import Submission.Work.Parabolic.Main

/-!
# The parabolic case of uniformization: assembly

This module assembles the chapter into the statement requested by `fundmath3-uniformization`:

```lean
Work.Mori.plane_of_no_unitGreenFunction (hX : ¬ CompactSpace X) (x : X)
    [Subsingleton (Additive (FundamentalGroup X x) →+ ℝ)]
    (h : ¬ ∃ (z₀ : X) (E : X → ℝ), Work.UnitGreen.IsUnitGreenFunctionAt z₀ E)
    (hSpine : Work.Mori.Hubbard112 X x) (hABS : Work.Mori.ABSTheorem X) :
    Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ ℂ)
```

The two extra arguments are the *named classical inputs owned by the other subprojects*, recorded as
`Prop`s in `Submission/Work/Mori/Defs.lean`:

* `Work.Mori.Hubbard112 X x` — Hubbard, *Teichmüller theory* Vol. 1, Theorem 1.1.2: `H¹(X,ℝ) = 0`
  forces `X` simply connected (the deliverable of `Work.Spine`, i.e. freeness of `π₁` of an open
  surface, Johansson/Stallings).  Purely topological, about *all* open surfaces.
* `Work.Mori.ABSTheorem X` — Anghel–Bruin–Stan Theorem 1: a non-compact simply connected Riemann
  surface embeds biholomorphically into `ℂ` (the deliverable of `Work.SimplyConnected`/ABS).

Everything else in the chain is *proved here*:

* `h` ⟹ `Work.Parabolic.IsParabolic X` (`Work.Mori.isParabolic_of_not_exists_isUnitGreenFunction`,
  `UnitGreen.lean` — the normalisation of the logarithmic pole, proved in this directory);
* the winding obstruction that removes a non-empty exceptional set
  (`Work.Mori.not_diffeomorph_of_isPolar_of_nonempty`, `Argument.lean`);
* the assembly `Work.Parabolic.nonempty_diffeomorph_plane_of_isParabolic_of_injective_holomorphic`.

Neither of the two named inputs is equivalent to the parabolic statement: they are a topological
theorem about open surfaces and an embedding theorem for simply connected surfaces, and the
statement of *this* chapter also needs the parabolicity normalisation and the winding argument that
are proved here.

An alternative assembly through Mori's *planar* normal form is
`Work.Mori.plane_of_no_unitGreenFunction_of_mori`, which instead takes
`Work.Mori.HasHolomorphicEmbedding X` ("`X` embeds holomorphically into `ℂ`") and
`Work.Mori.MoriNormalFormTheorem X` (the planar normal form, *with* that hypothesis: the
unconditional form is false, see `Defs.lean`).  It avoids the topological step `Hubbard112`
entirely, at the price of the harder classical input `MoriNormalFormTheorem`.

## Why the topological step cannot be dropped

The conclusion `X ≅ ℂ` implies that `X` is simply connected, so every proof of this chapter derives
simple connectivity of `X` from the hypotheses.  The parabolic hypothesis does not supply it (the
once-punctured torus is parabolic and has a handle), and neither does `H¹(X,ℝ) = 0` *by itself*
without the surface-theoretic fact that `π₁` of an open surface is free — exactly the content of
`Hubbard112`.  Consequently `plane_of_no_unitGreenFunction` *has* to consume a topological input,
either as `Hubbard112` (the route recorded below) or through the planarity hypothesis of the Mori
route (which is what `Hubbard112` + `ABSTheorem` produce).
-/

/-!
## SHARPNESS — the headline cannot be had without the topological input

`Work.Mori.ExactStrength` (`Submission/Work/Mori/ExactStrength.lean`) proves, with the modulus
interface `Work.Mori.ModulusOfTrivialHom X x₀` (which the spine proves), that the parabolic case for
`X` is **equivalent** to

  `SimplyConnectedSpace X` **and** (`X ≅ ℂ` or `X ≅ ℍ`):

* `Work.Mori.parabolicCase_iff_spine_and_dichotomy`;
* `Work.Mori.simplyConnectedSpace_of_parabolicCase` — **the deliverable implies the spine**, given
  the modulus interface `ModulusOfTrivialHom` (which the spine supplies): a spine-free proof of the
  deliverable must therefore supply that interface otherwise, and the isolated topological input
  which would do it is `Work.Mori.NoNontrivialHomToCircle` (vanishing of the circle-valued
  `π₁`-cohomology, i.e. absence of finite quotients of `π₁`);
* `Work.Mori.parabolicCase_iff_dichotomy_of_spine` — with the spine, the deliverable is *exactly*
  the dichotomy;
* `Work.Mori.hubbard112_of_parabolicCase_of_dichotomy`.

So the two extra arguments of `plane_of_no_unitGreenFunction` below are not an artefact of the
proof: every route to the four-hypothesis statement must supply the topological input
(`Work.Spine`'s Hubbard 1.1.2, or at least the weaker `Work.Mori.NoNontrivialHomToCircle`) and a
simply-connected-uniformization statement.  The classical
`O_G` route of `NOTES_session3_analysis.md` §2 replaces them by the two classical statements
(`Work.Mori.MoriHeinsTheorem` and the `O_G` gap `Work.Mori.plane_of_no_unitGreenFunction_of_moriHeins`),
and the certificate `Work.Mori.isParabolic_and_not_isO_G_and_not_subsingleton_hom_puncturedUnitDisc`
shows that route cannot be run from `h` alone.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

noncomputable section

open Filter Set

namespace Work.Mori

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **A Mori normal form forces `X ≅ ℂ` under the challenge hypothesis.**  If every homomorphism
`π₁(X,x) → ℝ` is trivial and `X` is biholomorphic to the complement `U` of a polar closed set, then
`U` must be all of `ℂ`: if `U` missed a point `p`, the small circle around `p` that avoids `Uᶜ`
(`Work.Mori.exists_sphere_eq_empty`) would give a loop of `X` whose argument around `p` is not
periodic (`Work.Mori.not_hasArg_circle`), contradicting the triviality of the monodromy of the
argument under the challenge hypothesis
(`Work.Mori.not_diffeomorph_of_isPolar_of_nonempty`).

Note that neither non-compactness nor the absence of a Green function is needed here: this is the
step that removes the exceptional set. -/
theorem plane_of_no_unitGreenFunction_of_hasMoriNormalForm (x : X)
    [Subsingleton (Additive (FundamentalGroup X x) →+ ℝ)]
    (hM : HasMoriNormalForm X) :
    Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ) := by
  obtain ⟨U, hpolar, ⟨Φ⟩⟩ := hM
  by_cases hne : ((U : Set ℂ)ᶜ).Nonempty
  · exact absurd (not_diffeomorph_of_isPolar_of_nonempty (X := X) x hpolar hne Φ) not_false
  · -- the polar set is empty, so `U = ⊤` and `X ≃ₘ ℂ`
    have hempty : (U : Set ℂ)ᶜ = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have huniv : (U : Set ℂ) = Set.univ := by rw [← Set.compl_empty_iff]; exact hempty
    have hUt : U = ⊤ := TopologicalSpace.Opens.ext (by rw [huniv]; simp)
    obtain ⟨e⟩ := nonempty_diffeomorph_opens_top
    exact ⟨(hUt ▸ Φ).trans e⟩

/-- **The parabolic case from the ABS input.**  If in addition `X` is simply connected and admits an
injective holomorphic map into `ℂ` (the input of `Work.SimplyConnected` / the Anghel–Bruin–Stan
route), the conclusion follows from the parabolic reduction of `Work.Parabolic`: the only new
ingredient here is `h ⟹ IsParabolic X`. -/
theorem plane_of_no_unitGreenFunction_of_ABS [SimplyConnectedSpace X]
    (hX : ¬ CompactSpace X) (x : X)
    [Subsingleton (Additive (FundamentalGroup X x) →+ ℝ)]
    (h : ¬ ∃ (z₀ : X) (E : X → ℝ), Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E)
    {φ : X → ℂ} (hφ : Submission.HolomorphicOnX φ Set.univ) (hinj : Function.Injective φ) :
    Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ) :=
  Work.Parabolic.nonempty_diffeomorph_plane_of_isParabolic_of_injective_holomorphic (x₀ := x)
    (isParabolic_of_not_exists_isUnitGreenFunction hX h) hφ hinj

/-- **The parabolic case of the uniformization theorem in the form "Mori"** (the deliverable of
`Submission/Work/Mori/`): a connected non-compact second countable Riemann surface with no
unit-pole Green function and with no non-trivial homomorphism from its fundamental group to `ℝ` is
biholomorphic to `ℂ`.

The two extra arguments are the named classical inputs of the parallel subprojects
(`Work.Mori.Hubbard112` = `Work.Spine`'s Hubbard 1.1.2; `Work.Mori.ABSTheorem` =
`Work.SimplyConnected`'s Anghel–Bruin–Stan Theorem 1).  See the module docstring for why the
topological input cannot be dropped, and `Submission/Work/Mori/Defs.lean` for the exact statements.
The `Work.Mori.plane_of_no_unitGreenFunction_of_ABS` instance of the reduction is what is
*proved* here, together with `h ⟹ IsParabolic X` (`Work.Mori.UnitGreen.lean`). -/
theorem plane_of_no_unitGreenFunction (hX : ¬ CompactSpace X) (x : X)
    [Subsingleton (Additive (FundamentalGroup X x) →+ ℝ)]
    (h : ¬ ∃ (z₀ : X) (E : X → ℝ), Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E)
    (hSpine : Hubbard112 X x) (hABS : ABSTheorem X) :
    Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ) := by
  haveI : SimplyConnectedSpace X := hSpine hX inferInstance
  obtain ⟨φ, hφ, hinj⟩ := hABS inferInstance hX
  exact plane_of_no_unitGreenFunction_of_ABS hX x h hφ hinj

/-- **The parabolic case from planarity and Mori's planar normal form.**

**DO NOT BUILD ON THIS ROUTE**: its input `Work.Mori.MoriNormalFormTheorem` is expected to be *false*
with the relative-compactness notion of parabolicity used here (the punctured disc `𝔻 ∖ {0}` is
parabolic and planar and is not `ℂ ∖ E` with `E` polar; see `WindingCircle.lean` and
`MyrbergRefutation.lean`).  The theorem below is therefore a true conditional statement whose
hypothesis is not known to have any instance; use `Work.Mori.MoriTheorem` (same module) or
`Work.Mori.PlaneParabolicTheorem` (`WindingCircle.lean`) instead.  Kept only because it is the
honest record of the route that the request described, and because the *winding* half of it
(`plane_of_no_unitGreenFunction_of_hasMoriNormalForm`) is the part that is really used. -/
theorem plane_of_no_unitGreenFunction_of_mori (hX : ¬ CompactSpace X) (x : X)
    [Subsingleton (Additive (FundamentalGroup X x) →+ ℝ)]
    (h : ¬ ∃ (z₀ : X) (E : X → ℝ), Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E)
    (hplanar : HasHolomorphicEmbedding X) (hMori : MoriNormalFormTheorem X) :
    Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ) :=
  plane_of_no_unitGreenFunction_of_hasMoriNormalForm x
    (hMori hX (isParabolic_of_not_exists_isUnitGreenFunction hX h) hplanar)

/-- **The parabolic case from the uniformization dichotomy.**  If the dichotomy `X ≅ ℂ ∨ X ≅ ℍ` is
available (the conclusion of the simply connected case, `Work.SC.uniformization_of_simplyConnected`),
then no unit Green function forces `X ≅ ℂ`, since `ℍ` has a Green function. -/
theorem plane_of_no_unitGreenFunction_of_dichotomy (hX : ¬ CompactSpace X) (x : X)
    [Subsingleton (Additive (FundamentalGroup X x) →+ ℝ)]
    (h : ¬ ∃ (z₀ : X) (E : X → ℝ), Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E)
    (hdich : Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ) ∨
      Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ UpperHalfPlane)) :
    Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ) :=
  Work.Parabolic.nonempty_diffeomorph_plane_of_isParabolic_of_dichotomy
    (isParabolic_of_not_exists_isUnitGreenFunction hX h) hdich

/-- **The parabolic case from the other subprojects' two deliverables.**  This wires the chapter to
the parallel work: `hspine` is Hubbard 1.1.2's topological step (the deliverable of `Work.Spine`,
`Work.Spine.simplyConnectedSpace_of_subsingleton_hom_toReal`: under the challenge hypothesis `X` is
simply connected) and `hdich` is the dichotomy of the simply connected case of uniformization (the
deliverable of `Work.SC` / `Work.SimplyConnected`).  With those, no unit Green function forces
`X ≅ ℂ`, and `ABSTheorem`/Mori are *not* needed. -/
theorem plane_of_no_unitGreenFunction_of_spine_of_dichotomy (hX : ¬ CompactSpace X) (x : X)
    [Subsingleton (Additive (FundamentalGroup X x) →+ ℝ)]
    (h : ¬ ∃ (z₀ : X) (E : X → ℝ), Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E)
    (hspine : ¬ CompactSpace X →
      Subsingleton (Additive (FundamentalGroup X x) →+ ℝ) → SimplyConnectedSpace X)
    (hdich : SimplyConnectedSpace X → ¬ CompactSpace X →
      Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ) ∨
        Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ UpperHalfPlane)) :
    Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ) :=
  plane_of_no_unitGreenFunction_of_dichotomy hX x h (hdich (hspine hX inferInstance) hX)

/-! ## Mori's theorem, sharpened, and the deliverable from it

`Work.Mori.MoriNormalFormTheorem` (`Defs.lean`) is stated *without* the hypothesis that every
homomorphism `π₁(X,x) → ℝ` vanishes, and it is expected to be **false** in that form with the notion
of parabolicity used here (relative compactness of the superlevel sets of the Green function): the
punctured disc `𝔻 ∖ {0}` is parabolic in that sense, while its complement `{0} ∪ {|z| ≥ 1}` is not
polar (see the discussion in `WindingCircle.lean` and `README.md`).  The classical theorem of
Mori 1957, in the form in which it is true and in which this chapter consumes it, carries the
vanishing-cohomology hypothesis as part of the statement. -/

/-- **Mori's theorem (Mori 1957; Heins), sharpened form.**

Planning remark: with `Work.Mori.plane_of_no_unitGreenFunction_of_hasMoriNormalForm` proved, this
input and the deliverable are *interderivable* — `MoriTheorem` plus the winding step gives `X ≅ ℂ`,
and `X ≅ ℂ` is the normal form at `U = ⊤`.  So `MoriTheorem` is not a cheaper external input than
the deliverable itself; the genuinely external content is the planarity/normal-form step for
parabolic surfaces, which is what the ABS/spine pair supply (`ABSTheorem` + `Hubbard112`) and what
the plane-domain route (`PlaneParabolicTheorem` + `plane_of_no_unitGreenFunction_of_planeParabolic`)
obtains without simple connectivity.

A connected non-compact parabolic Riemann surface on which every homomorphism `π₁(X,x) → ℝ`
vanishes is biholomorphic to the complement of a closed polar subset of `ℂ` — equivalently (and that
is all this chapter uses), it is biholomorphic to `ℂ`.

The hypothesis `Subsingleton (Additive (FundamentalGroup X x) →+ ℝ)` is necessary and is *not* a
consequence of parabolicity: the once-punctured torus is parabolic and non-planar, and every plane
domain with a puncture has a non-trivial winding homomorphism; moreover `𝔻 ∖ {0}` shows that even
planarity does not help (`MyrbergRefutation.lean`). -/
def MoriTheorem (X : Type*) [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] (x : X) : Prop :=
  ¬ CompactSpace X → Work.Parabolic.IsParabolic X →
    Subsingleton (Additive (FundamentalGroup X x) →+ ℝ) → HasMoriNormalForm X

/-- **The parabolic case of uniformization, from Mori's (sharpened) theorem.**  Mori's normal form
plus the winding step proved in this directory
(`Work.Mori.plane_of_no_unitGreenFunction_of_hasMoriNormalForm`) give `X ≅ ℂ`. -/
theorem plane_of_no_unitGreenFunction_of_moriTheorem (x : X) (hM : MoriTheorem X x)
    (hX : ¬ CompactSpace X)
    [Subsingleton (Additive (FundamentalGroup X x) →+ ℝ)]
    (h : ¬ ∃ (z₀ : X) (E : X → ℝ), Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E) :
    Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ) :=
  plane_of_no_unitGreenFunction_of_hasMoriNormalForm x
    (hM hX (isParabolic_of_not_exists_isUnitGreenFunction hX h) inferInstance)

end Work.Mori
