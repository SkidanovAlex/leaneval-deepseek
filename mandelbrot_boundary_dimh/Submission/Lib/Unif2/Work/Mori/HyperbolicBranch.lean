import Submission.Lib.Unif2.Work.Mori.Defs
import Submission.Lib.Unif2.Work.Mori.UnitGreen
import Submission.Lib.Unif2.Work.Mori.Interface
import Submission.Lib.Unif2.Work.Modulus.Main
import Submission.Lib.Unif2.Work.Parabolic.uniformization_of_greenFunctionAt
import Submission.Lib.Unif2.Work.Parabolic.isParabolic_complex

/-!
# The hyperbolic half of the dichotomy, from the holomorphic modulus

The parabolic case (`Work.Mori.plane_of_no_unitGreenFunction`, `Main.lean`) is one half of the
uniformization dichotomy: a surface with *no* Green function is `ℂ`.  This module supplies the
CHAPTER'S OTHER HALF, on the workspace's satisfiable predicates, and wires it to the modulus
chapter `Submission.Work.Modulus`:

* `Work.Mori.dichotomy_of_unitGreenFunction_of_hubbard112` — a connected non-compact Riemann
  surface which carries a unit-pole Green function and on which every homomorphism
  `π₁(X,x₀) →+ ℝ` vanishes is biholomorphic to `ℂ` or to `ℍ`.  The holomorphic modulus
  (`Work.Modulus.exists_holomorphic_modulus_of_unitGreenFunction_of_hubbard112`, which consumes the
  spine theorem as an explicit hypothesis) plus the *repaired* hyperbolic endgame
  (`Work.Parabolic.uniformization_of_greenFunctionAt`, whose properness hypothesis is the
  satisfiable relative-compactness one) give the conclusion.

* `Work.Mori.nonempty_diffeomorph_upperHalfPlane_of_unitGreenFunction_of_hubbard112` — the sharper
  form: such a surface is biholomorphic to `ℍ`.  The `ℂ` branch is excluded because `ℂ` is
  parabolic (`Work.Parabolic.isParabolic_complex`, a pure potential-theoretic fact) and parabolicity
  is a biholomorphic invariant (`Work.Mori.isParabolic_of_diffeomorph`).

Consequences for the assembly of the uniformization theorem:

* the **hyperbolic** half of the dichotomy needs only the spine (via the modulus chapter) and *no*
  ABS input (`Work.SC.HasDiscExhaustion`, `Work.SC.UniformBoundAt`), unlike the
  `Work.SC.uniformization_of_simplyConnected` route;
* the **parabolic** half is exactly the deliverable of this directory
  (`Work.Mori.plane_of_no_unitGreenFunction`), so with the spine the two halves together give the
  full dichotomy `X ≅ ℂ ∨ X ≅ ℍ` — except for surfaces that are parabolic *and* simply connected,
  which are precisely the content of the deliverable (see `README.md` §0ter).
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

noncomputable section

open Filter Set

namespace Work.Mori

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The dichotomy in the hyperbolic case, with the spine as an explicit hypothesis.**  A connected
non-compact Riemann surface carrying a unit-pole Green function, with no non-trivial homomorphism
`π₁(X,x₀) →+ ℝ`, is biholomorphic to `ℂ` or to `ℍ`.

The two inputs are proved elsewhere: the holomorphic modulus of the Green function
(`Work.Modulus.exists_holomorphic_modulus_of_unitGreenFunction_of_hubbard112`) and the hyperbolic
endgame (`Work.Parabolic.uniformization_of_greenFunctionAt`); `hSpine` is Hubbard 1.1.2
(`Work.Spine.simplyConnectedSpace_of_subsingleton_hom_toReal`), consumed by the modulus chapter. -/
theorem dichotomy_of_unitGreenFunction_of_hubbard112 {x₀ z₀ : X} {E : X → ℝ}
    (hE : Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E)
    (hSpine : (¬ CompactSpace X) → (x : X) →
      Subsingleton (Additive (FundamentalGroup X x) →+ ℝ) → SimplyConnectedSpace X)
    [Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)] :
    Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ) ∨
      Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ UpperHalfPlane) := by
  obtain ⟨Φ, hΦ, hpole, hmod⟩ :=
    Work.Modulus.exists_holomorphic_modulus_of_unitGreenFunction_of_hubbard112
      (z₀ := z₀) (x₀ := x₀) hE hSpine
  exact Work.Parabolic.uniformization_of_greenFunctionAt (Work.Modulus.greenNoncompact hE)
    hE.isGreenFunctionAt hΦ hmod hpole

/-- **The dichotomy in the hyperbolic case, from simple connectivity.**  Same statement with
`SimplyConnectedSpace X` in place of the spine hypothesis (this is the form provided by
`Work.Modulus.exists_holomorphic_modulus_of_unitGreenFunction_of_simplyConnected`). -/
theorem dichotomy_of_unitGreenFunction_of_simplyConnected {z₀ : X} {E : X → ℝ}
    (hE : Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E) [SimplyConnectedSpace X] :
    Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ) ∨
      Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ UpperHalfPlane) :=
  dichotomy_of_unitGreenFunction_of_hubbard112 (x₀ := z₀) hE
    (fun _ _ _ => inferInstance)

/-- **The `ℂ` branch of the dichotomy is impossible for a surface with a Green function.**  `ℂ` is
parabolic (`Work.Parabolic.isParabolic_complex`) and parabolicity is a biholomorphic invariant
(`Work.Mori.isParabolic_of_diffeomorph`), while the existence of a unit-pole Green function is the
negation of parabolicity. -/
theorem not_nonempty_diffeomorph_plane_of_unitGreenFunction {z₀ : X} {E : X → ℝ}
    (hX : ¬ CompactSpace X) (hE : Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E) :
    ¬ Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ) := by
  rintro ⟨Φ⟩
  have hpar : Work.Parabolic.IsParabolic X :=
    isParabolic_of_diffeomorph Φ.symm Work.Parabolic.isParabolic_complex
  exact ((isParabolic_iff_not_exists_isUnitGreenFunction hX).mp hpar) ⟨z₀, E, hE⟩

/-- **A surface with a Green function and no non-trivial homomorphism `π₁ →+ ℝ` is `ℍ`.**  This is
the hyperbolic half of the uniformization theorem in the analytic form: the dichotomy
(`Work.Mori.dichotomy_of_unitGreenFunction_of_hubbard112`) gives `ℂ` or `ℍ`, and the `ℂ` branch is
killed by `Work.Mori.not_nonempty_diffeomorph_plane_of_unitGreenFunction`. -/
theorem nonempty_diffeomorph_upperHalfPlane_of_unitGreenFunction_of_hubbard112 {x₀ z₀ : X}
    {E : X → ℝ} (hE : Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E)
    (hSpine : (¬ CompactSpace X) → (x : X) →
      Subsingleton (Additive (FundamentalGroup X x) →+ ℝ) → SimplyConnectedSpace X)
    [Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)] :
    Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ UpperHalfPlane) := by
  rcases dichotomy_of_unitGreenFunction_of_hubbard112 (x₀ := x₀) hE hSpine with h | h
  · exact absurd h (not_nonempty_diffeomorph_plane_of_unitGreenFunction
      (Work.Modulus.greenNoncompact hE) hE)
  · exact h

/-- **`ℍ` from simple connectivity** (the form that only needs
`Work.Modulus.exists_holomorphic_modulus_of_unitGreenFunction_of_simplyConnected`). -/
theorem nonempty_diffeomorph_upperHalfPlane_of_unitGreenFunction_of_simplyConnected {z₀ : X}
    {E : X → ℝ} (hE : Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E)
    [SimplyConnectedSpace X] :
    Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ UpperHalfPlane) :=
  nonempty_diffeomorph_upperHalfPlane_of_unitGreenFunction_of_hubbard112 (x₀ := z₀) hE
    (fun _ _ _ => inferInstance)

/-! ## The whole dichotomy from the spine and the parabolic case

If one already has the deliverable of this directory — the parabolic case — then the spine gives the
full dichotomy: either `X` carries a Green function (hyperbolic half, this module), or it does not
(parabolic half, `Work.Mori.plane_of_no_unitGreenFunction`).  This is recorded because it is exactly
the shape of route (ii) of `fundmath3-uniformization`. -/

/-- **The full dichotomy from the spine plus the parabolic case.** -/
theorem dichotomy_of_spine_and_parabolicCase {x₀ : X}
    (hSpine : (¬ CompactSpace X) → (x : X) →
      Subsingleton (Additive (FundamentalGroup X x) →+ ℝ) → SimplyConnectedSpace X)
    (hparabolic : (¬ CompactSpace X) → Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ) →
      (¬ ∃ (z₀ : X) (E : X → ℝ), Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E) →
      Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ)) :
    ¬ CompactSpace X → Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ) →
      Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ) ∨
        Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ UpperHalfPlane) := by
  intro hX hhom
  by_cases hE : ∃ (z₀ : X) (E : X → ℝ), Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E
  · obtain ⟨z₀, E, hE⟩ := hE
    exact Or.inr (nonempty_diffeomorph_upperHalfPlane_of_unitGreenFunction_of_hubbard112
      (x₀ := x₀) hE hSpine)
  · exact Or.inl (hparabolic hX hhom hE)

end Work.Mori


namespace Work.Mori

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-! ## The spine-free form of the hyperbolic branch, and the exact missing link

`Work.Modulus.exists_holomorphic_modulus_of_unitGreenFunction_of_hubbard112` reaches the holomorphic
modulus through the *spine theorem* (Hubbard 1.1.2), because single-valuedness of
`Φ = exp (-(E + iE*))` is proved there for simply connected `X` (or, equivalently, from the
loop-level statement `Work.Modulus.AllLoopsOfPuncturedTrivialInX`).

A *spine-free* hyperbolic branch needs only the following consequence, in which the topological input
is replaced by the cohomology hypothesis that is anyway part of the challenge statement.  It is
recorded as a named `Prop` so that a future session can attack it in isolation; it is *strictly
weaker* than the spine (the spine proves it:
`Work.Mori.modulusOfTrivialHom_of_hubbard112`), and the theorem below shows that it is exactly what
the hyperbolic branch of the dichotomy consumes. -/

/-- **The missing link of the spine-free hyperbolic branch**: every unit-pole Green function on a
surface on which every homomorphism `π₁(X,x₀) →+ ℝ` vanishes has a single-valued holomorphic modulus
`Φ` with `‖Φ x‖ = exp (-(E x))` off the pole and a logarithmic pole (`Submission.HasLogPoleAt`) at
it.

Equivalently: all periods of the conjugate differential are multiples of `2π`.  The spine theorem
gives this (see `Work.Mori.modulusOfTrivialHom_of_hubbard112`), by *simple connectivity* of `X`; the
question of whether the cohomology hypothesis alone suffices is the remaining gap of route (ii) of
`fundmath3-uniformization`.
See `NOTES_session3_analysis.md` §3 for the analysis: the monodromy of the modulus is a
homomorphism `π₁(X) → ℝ/2πℤ`, whose vanishing would follow from the cohomology hypothesis together
with the (purely topological) fact that `H₁` of an open orientable surface has no torsion. -/
def ModulusOfTrivialHom (X : Type*) [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] (x₀ : X) : Prop :=
  ∀ (z₀ : X) (E : X → ℝ), Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E →
    Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ) →
    ∃ Φ : X → ℂ, Submission.HolomorphicOnX Φ Set.univ ∧ Submission.HasLogPoleAt z₀ Φ ∧
      ∀ x, x ≠ z₀ → ‖Φ x‖ = Real.exp (-(E x))

/-- The spine theorem proves `Work.Mori.ModulusOfTrivialHom`. -/
theorem modulusOfTrivialHom_of_hubbard112 {x₀ : X}
    (hSpine : (¬ CompactSpace X) → (x : X) →
      Subsingleton (Additive (FundamentalGroup X x) →+ ℝ) → SimplyConnectedSpace X) :
    ModulusOfTrivialHom X x₀ :=
  fun _z₀ _E hE _ => Work.Modulus.exists_holomorphic_modulus_of_unitGreenFunction_of_hubbard112
    (z₀ := _z₀) (x₀ := x₀) hE hSpine

/-- **The hyperbolic branch of the dichotomy, from the cohomology hypothesis alone.**

With `Work.Mori.ModulusOfTrivialHom` in place of the spine, a connected non-compact Riemann surface
carrying a unit-pole Green function on which every `π₁(X,x) →+ ℝ` vanishes is biholomorphic to `ℍ`.
This is the shape in which route (ii) of `fundmath3-uniformization` needs the hyperbolic branch. -/
theorem nonempty_diffeomorph_upperHalfPlane_of_modulusOfTrivialHom {x₀ z₀ : X} {E : X → ℝ}
    (hmod : ModulusOfTrivialHom X x₀) (hE : Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E)
    [Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)] :
    Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ UpperHalfPlane) := by
  obtain ⟨Φ, hΦ, hpole, hmodE⟩ := hmod z₀ E hE inferInstance
  rcases Work.Parabolic.uniformization_of_greenFunctionAt (Work.Modulus.greenNoncompact hE)
      hE.isGreenFunctionAt hΦ hmodE hpole with h | h
  · exact absurd h (not_nonempty_diffeomorph_plane_of_unitGreenFunction
      (Work.Modulus.greenNoncompact hE) hE)
  · exact h

/-- **The `ℂ` branch of the dichotomy is excluded even with the polynomial-growth-free form**: a
surface with a unit Green function on which every `π₁(X,x) →+ ℝ` vanishes is *not* `ℂ`.  (Restated
here to record that `Work.Mori.ModulusOfTrivialHom` does not presuppose the conclusion.) -/
theorem not_nonempty_diffeomorph_plane_of_modulusOfTrivialHom {x₀ z₀ : X} {E : X → ℝ}
    (hE : Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E) :
    ¬ Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ) :=
  not_nonempty_diffeomorph_plane_of_unitGreenFunction (Work.Modulus.greenNoncompact hE) hE

end Work.Mori
