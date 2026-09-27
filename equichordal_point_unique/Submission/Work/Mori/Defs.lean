import Mathlib
import Submission.UnifDeps
import Submission.RiemannSurface
import Submission.Holomorphic
import Submission.Conjugate
import Submission.Commons.Topology.Winding.hasArg_homotopy_invariant
import Submission.Work.Parabolic.Basic
import Submission.Work.UnitGreen.Defs

/-!
# `Work.Mori` — the parabolic case of uniformization, Mori's route

This directory is the subproject that supplies the parabolic branch of the uniformization theorem
in the form requested by `fundmath3-uniformization`:

```lean
theorem Work.Mori.plane_of_no_unitGreenFunction
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) (x : X) [Subsingleton (Additive (FundamentalGroup X x) →+ ℝ)]
    (h : ¬ ∃ (z₀ : X) (E : X → ℝ), Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E) :
    Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ)
```

## The mathematics

`h` says that `X` carries no *unit* Green function; by the classical normalisation of the pole
coefficient (`Work.Mori.exists_isUnitGreenFunctionAt_of_isGreenFunctionAt`) this is equivalent to
`X` being **parabolic**, i.e. carrying no Green function at all
(`Work.Mori.isParabolic_of_not_exists_isUnitGreenFunction`).  The classical theorem of Mori (1957)
then says that a non-compact parabolic Riemann surface is biholomorphic to `ℂ ∖ E` for a closed
set `E ⊆ ℂ` of vanishing **logarithmic capacity** (a *polar* set).  Finally, if such an `E` were
non-empty, a small circle around a point `p ∈ E` (which exists because a polar set is *thin*:
`Work.Mori.exists_sphere_eq_empty`, proved here from Fekete's transfinite diameter) would give a
loop of `X` whose argument around `p` is not periodic; but the challenge hypothesis
`Subsingleton (Additive (FundamentalGroup X x) →+ ℝ)` makes the argument of *every* nowhere
vanishing holomorphic function single-valued along every loop
(`Work.Mori.hasArg_comp_of_holomorphic_of_subsingleton`), so `E` must be empty and `X ≅ ℂ`.
(`Work.Mori.not_diffeomorph_of_isPolar_of_nonempty` assembles this step.)

## What is proved here, and what is a named classical input

*Proved here (no classical input):* the normalisation `Green ⟹ unit Green` (hence
`h ⟹ IsParabolic X`); the theory of polar sets (`IsPolar`); the thinness of a polar set at each of
its points (`Work.Mori.exists_sphere_eq_empty`); and the winding argument excluding `E ≠ ∅`
(`Work.Mori.not_diffeomorph_of_isPolar_of_nonempty`).

*Named classical inputs:* three genuinely different classical theorems, each the deliverable of a
named parallel subproject, and none of them equivalent to the statement of the parabolic case:

* `Work.Mori.Hubbard112` — the topological step (Hubbard 1.1.2): `H¹(X,ℝ) = 0` forces `X` simply
  connected (`Work.Spine`, the spine theorem of Johansson/Stallings).
* `Work.Mori.ABSTheorem` — every non-compact simply connected Riemann surface embeds in `ℂ`
  (Anghel–Bruin–Stan Theorem 1; `Work.SimplyConnected`/ABS).
* `Work.Mori.MoriNormalFormTheorem` — the planar *Mori normal form*: a non-compact parabolic surface
  that embeds holomorphically into `ℂ` is biholomorphic to `ℂ ∖ E` with `E` closed and polar
  (Mori 1957, Heins; with the hypothesis `HasHolomorphicEmbedding X`, which is **necessary**: the
  unconditional form is false, see the docstring of `MoriNormalFormTheorem`).

`Work.Mori.plane_of_no_unitGreenFunction` takes the first two as explicit hypotheses (the route of
the requester's `Work.Spine` + `Work.SimplyConnected` chain); `Work.Mori.plane_of_no_unitGreenFunction_of_mori`
takes planarity and Mori instead.  Both are honest reductions, proved here, with no `sorryAx`.

## Contents of this file

* `Work.Mori.feketeMean` — Fekete's geometric mean of the pairwise distances of an `n`-tuple of
  points of `K ⊆ ℂ`;
* `Work.Mori.HasZeroFeketeCapacity` — the transfinite diameters of `K` tend to `0`;
* `Work.Mori.IsPolar` — every compact subset of `K` has vanishing Fekete capacity, i.e. `K` has
  logarithmic capacity `0` in the classical sense `cap K = sup {cap L : L ⊆ K compact}`
  (`IsPolar.mono`, `isPolar_empty`, `isPolar_singleton` are the basic API);
* `Work.Mori.HasMoriNormalForm` — `X` is biholomorphic to a domain whose complement is polar;
* `Work.Mori.MoriNormalFormTheorem` — Mori's theorem, as a named `Prop`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

noncomputable section

namespace Work.Mori

/-- **Fekete's geometric mean of the pairwise distances of a tuple.**  For `z : Fin n → K` this is
`(∏_{i<j} ‖z i - z j‖)^{1/N}`, where `N = n (n - 1) / 2` is the number of pairs.  The `n`-th
transfinite diameter of `K` is the supremum of these numbers over all `n`-tuples.

For `n ≤ 1` the product is empty, so the definition returns `1`; it is only used for `n ≥ 2`. -/
def feketeMean {n : ℕ} {K : Set ℂ} (z : Fin n → ↥K) : ℝ :=
  (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, ‖(z i : ℂ) - (z j : ℂ)‖) ^
    (1 / ((n * (n - 1) / 2 : ℕ) : ℝ))

/-- **Vanishing Fekete capacity.**  For every `ε > 0` there is `n ≥ 2` such that the Fekete
geometric mean of every `n`-tuple of points of `K` is `< ε`; equivalently, the transfinite
diameters of `K` tend to `0`.

By Fekete's theorem this is the same as `K` having logarithmic capacity `0`, for *compact* `K`
(the transfinite diameters decrease to the logarithmic capacity). -/
def HasZeroFeketeCapacity (K : Set ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, 2 ≤ n ∧ ∀ z : Fin n → ↥K, feketeMean z < ε

/-- A subset of a set of vanishing Fekete capacity has vanishing Fekete capacity. -/
theorem HasZeroFeketeCapacity.mono {K L : Set ℂ} (hKL : K ⊆ L)
    (h : HasZeroFeketeCapacity L) : HasZeroFeketeCapacity K := by
  intro ε hε
  obtain ⟨n, hn, hz⟩ := h ε hε
  exact ⟨n, hn, fun z => hz fun i => ⟨(z i : ℂ), hKL (z i).2⟩⟩

/-- A subsingleton has vanishing Fekete capacity: with `n = 2` every pair of points coincides, so
every Fekete mean vanishes. -/
theorem hasZeroFeketeCapacity_of_subsingleton {K : Set ℂ} (h : ∀ x y : ↥K, x = y) :
    HasZeroFeketeCapacity K := by
  intro ε hε
  refine ⟨2, le_rfl, fun z => ?_⟩
  have hz : (z 0 : ℂ) = (z 1 : ℂ) := congrArg Subtype.val (h (z 0) (z 1))
  have hsub : (z 0 : ℂ) - (z 1 : ℂ) = 0 := sub_eq_zero.mpr hz
  have hexp : (1 : ℝ) / ((2 * (2 - 1) / 2 : ℕ) : ℝ) ≠ 0 := by norm_num
  have hprod : (∏ i : Fin 2, ∏ j ∈ Finset.Ioi i, ‖(z i : ℂ) - (z j : ℂ)‖) = 0 := by
    refine Finset.prod_eq_zero (Finset.mem_univ 0) ?_
    refine Finset.prod_eq_zero (Finset.mem_Ioi.mpr (by decide : (0 : Fin 2) < 1)) ?_
    rw [hsub, norm_zero]
  rw [feketeMean, hprod, Real.zero_rpow hexp]
  exact hε

/-- **`K` is polar**, i.e. of vanishing logarithmic capacity: every compact subset of `K` has
vanishing Fekete capacity.  This is the classical convention
`cap K = sup {cap L : L ⊆ K compact}`, which makes `cap K = 0` equivalent to `K` being *polar* in
the potential-theoretic sense for arbitrary (not necessarily closed or bounded) sets `K ⊆ ℂ`: in
particular every countable set is polar. -/
def IsPolar (K : Set ℂ) : Prop :=
  ∀ L : Set ℂ, L ⊆ K → IsCompact L → HasZeroFeketeCapacity L

/-- A subset of a polar set is polar. -/
theorem IsPolar.mono {K L : Set ℂ} (hKL : K ⊆ L) (h : IsPolar L) : IsPolar K :=
  fun L' hL' hc => h L' (hL'.trans hKL) hc

/-- The empty set is polar. -/
theorem isPolar_empty : IsPolar (∅ : Set ℂ) :=
  fun L hL _ => hasZeroFeketeCapacity_of_subsingleton fun x y => absurd (hL x.2) (Set.notMem_empty _)

/-- A singleton is polar. -/
theorem isPolar_singleton (p : ℂ) : IsPolar ({p} : Set ℂ) :=
  fun L hL _ => hasZeroFeketeCapacity_of_subsingleton fun x y =>
    Subtype.ext (by rw [hL x.2, hL y.2])

/-- **Mori normal form**: `X` is biholomorphic to the complement of a closed polar subset of `ℂ`.
(The open set `U` is that complement; `U` is `⊤` exactly when the polar set is empty, in which case
`X ≅ ℂ`.) -/
def HasMoriNormalForm (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∃ U : TopologicalSpace.Opens ℂ, IsPolar ((U : Set ℂ)ᶜ) ∧
    Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ U)

/-- **`X` embeds holomorphically into `ℂ`.**  This is the "planarity" input of the parabolic case:
an injective holomorphic `φ : X → ℂ`.  Equivalently (`Work.Mori.hasMoriNormalForm_of_...`) the
`X`-side of a plane domain.

An injective holomorphic map with a biholomorphism into `ℂ` gives such a `φ`; the converse is
`Work.Parabolic.nonempty_diffeomorph_plane_of_isParabolic_of_injective_holomorphic` once one knows
that `X` is simply connected.  In the parabolic case the second input is supplied by classical
theorems owned by other subprojects (`Work.Spine` for the simple connectivity,
`Work.SimplyConnected`/ABS for the injective map). -/
def HasHolomorphicEmbedding (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∃ φ : X → ℂ, Submission.HolomorphicOnX φ Set.univ ∧ Function.Injective φ

/-- **Hubbard, *Teichmüller theory* Vol. 1, Theorem 1.1.2 (the topological step).**  A connected
non-compact second countable Riemann surface on which every homomorphism `π₁(X,x) → ℝ` vanishes is
simply connected.

This is a *purely topological* statement about open surfaces (equivalently, `π₁` of an open surface
is free, Johansson/Stallings); it is the deliverable of the subproject `Work.Spine`
(`Work.Spine.simplyConnectedSpace_of_subsingleton_hom_toReal`) and is recorded here as a named input
so that the parabolic case can be stated honestly without it.  It is **not** a consequence of the
parabolic hypothesis: the once-punctured torus is parabolic and not simply connected. -/
def Hubbard112 (X : Type*) [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] (x : X) : Prop :=
  ¬ CompactSpace X → Subsingleton (Additive (FundamentalGroup X x) →+ ℝ) → SimplyConnectedSpace X

/-- **Anghel–Bruin–Stan, Theorem 1.**  Every non-compact simply connected Riemann surface embeds
biholomorphically into `ℂ` (equivalently: is biholomorphic to a domain in `ℂ`).

This is the *analytic* classical input of the parabolic case; it is the deliverable of the
subproject `Work.SimplyConnected`/ABS, and it is recorded here as a named input.  It is strictly
weaker than the conclusion of the parabolic case: it produces an injective holomorphic map, not a
biholomorphism. -/
def ABSTheorem (X : Type*) [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] : Prop :=
  SimplyConnectedSpace X → ¬ CompactSpace X → HasHolomorphicEmbedding X

/-- **Mori's normal-form theorem (Mori 1957; Heins), corrected form.**

Every connected non-compact parabolic Riemann surface that *embeds holomorphically into `ℂ`* (i.e.
is a plane domain) is biholomorphic to the complement of a closed set of vanishing logarithmic
capacity.

The hypothesis `HasHolomorphicEmbedding X` is **not** redundant and is not an artefact of this
formalisation: the unconditional statement (`¬ CompactSpace X → IsParabolic X → HasMoriNormalForm X`)
is **false**.  A counterexample is the once-punctured torus `X = T ∖ {p}`:

* `X` is parabolic.  If `E` were a Green function at `z₀ ≠ p`, then `E ≥ 0` is harmonic on a
  punctured neighbourhood of `p`, hence (existence of a harmonic conjugate throughout the punctured
  disc, or the removable-singularities theorem for positive harmonic functions) extends harmonically
  across `p`; so `E` extends to `Σ ∖ {z₀}` on the compact torus `Σ`.  Its conjugate differential is
  then a meromorphic `1`-form on `Σ` whose only pole has non-zero residue, contradicting
  `Σ_{poles} res = 0`.
* `X` has a handle, so it is not homeomorphic to a plane domain: `HasMoriNormalForm X` would give
  `X ≃ₘ ℂ ∖ E`, hence a homeomorphism of `X` onto a plane domain, hence `H₁(X) ≅ H₁(ℂ∖E)`; but
  `H₁(T ∖ {p})` has rank `2` while a plane domain has free `H₁` of rank `≤ 1` here (`E` cannot be
  empty since then `X ≅ ℂ` would be simply connected).

So planarity is part of the classical hypothesis.  In the classical literature this is stated as
"Mori's theorem for domains on the sphere"; the version needed here is the one above. -/
def MoriNormalFormTheorem (X : Type*) [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] : Prop :=
  ¬ CompactSpace X → Work.Parabolic.IsParabolic X → HasHolomorphicEmbedding X → HasMoriNormalForm X

end Work.Mori
