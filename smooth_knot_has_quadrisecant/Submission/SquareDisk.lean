import Mathlib
import ChallengeDeps
import Submission.SecantDisk

open LeanEval.KnotTheory.Quadrisecant
open ContinuousMap
open scoped Real Topology unitInterval

/-!
# Layer A1/Layer B — square-disk transformations of the spanning square

The spanning-square predicate `PathsBoundDiskInteriorFree K γ δ` of
`SecantDisk.lean` is the interface through which the Layer-B Dehn-lemma
bridge and the Layer-C Fig.-3 disk surgery consume disk data.  The surgery
(replacing a disk locally near a trivial trisecant, Kuperberg Fig. 3a/3b)
will need to *relabel* and *reparametrise* the two boundary arcs of such a
square.  This module records the elementary symmetries of the square form
that make those manipulations possible:

1. **`PathsBoundDiskInteriorFree_swap_edges`** — reflecting a square disk
   across the horizontal axis swaps the two boundary arcs: if `γ` and `δ`
   bound a disk whose interior avoids `K`, then so do `δ` and `γ` (the
   reflected square `(s,t) ↦ D(s, 1−t)` has bottom edge `δ`, top edge `γ`,
   pinned sides and interior disjoint from `K`).  Together with the
   existing vertical reflection `PathsBoundDiskInteriorFree_rev`
   (`γ δ ↦ γ.symm δ.symm`) this gives all four relabellings of the pair of
   arcs.

2. **`PathsBoundDiskInteriorFree_reparam`** — simultaneous reparametrisation
   of both arcs by a continuous interval map `φ` that fixes the endpoints
   and maps the interior of `I` into itself: `γ∘φ` and `δ∘φ` again bound a
   disk off `K` (precompose the square with `(φ, id)`; the endpoint fix and
   the interior-preservation of `φ` are exactly what keeps the pinned sides
   pinned and the interior off `K`).

3. **`IsKnotArcPath_reparam`** — reparametrising a simple knot path `α` by
   an injective continuous `φ` fixing the endpoints keeps it a simple knot
   path (needed when the surgery reparametrises the knot arcs).

Everything here is elementary and verified (no axioms, no `sorry`).
-/

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-- The reparametrised path `γ ∘ φ` (for `φ : I → I` fixing the endpoints),
as a `Path` between the same endpoints as `γ`. -/
noncomputable def pathReparam {X : Type*} [TopologicalSpace X] {x y : X} (γ : Path x y)
    (φ : C(I, I)) (hφ0 : φ (0 : I) = (0 : I)) (hφ1 : φ (1 : I) = (1 : I)) : Path x y :=
  Path.mk (γ.toContinuousMap.comp φ)
    (by simp [hφ0])
    (by simp [hφ1])

/-- The reparametrised path evaluates as `γ (φ s)`. -/
lemma pathReparam_apply {X : Type*} [TopologicalSpace X] {x y : X} (γ : Path x y)
    (φ : C(I, I)) (hφ0 : φ (0 : I) = (0 : I)) (hφ1 : φ (1 : I) = (1 : I)) (s : I) :
    pathReparam γ φ hφ0 hφ1 s = γ (φ s) := by
  rfl

/-- **Swapping the two boundary arcs.**  Reflecting the square `(s,t) ↦
D(s, 1−t)` across the horizontal axis turns a disk bounded by `γ` and `δ`
(interior off `K`) into one bounded by `δ` and `γ`. -/
theorem PathsBoundDiskInteriorFree_swap_edges {X : Type*} [TopologicalSpace X] {K : Set X}
    {a b : X} (γ δ : Path a b) (hγδ : PathsBoundDiskInteriorFree K γ δ) :
    PathsBoundDiskInteriorFree K δ γ := by
  rcases hγδ with ⟨D, hbot, htop, hleft, hright, hint⟩
  let fl : I × I → I × I := fun p => (p.1, unitInterval.symm p.2)
  have hcont : Continuous fl := by
    dsimp [fl]
    fun_prop
  refine ⟨D.comp (ContinuousMap.mk fl hcont), ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    change D (s, unitInterval.symm (0 : I)) = δ s
    have hσ : unitInterval.symm (0 : I) = (1 : I) := by
      apply Subtype.ext
      simp
    rw [hσ, htop]
  · intro s
    change D (s, unitInterval.symm (1 : I)) = γ s
    have hσ : unitInterval.symm (1 : I) = (0 : I) := by
      apply Subtype.ext
      simp
    rw [hσ, hbot]
  · intro t
    change D ((0 : I), unitInterval.symm t) = a
    exact hleft (unitInterval.symm t)
  · intro t
    change D ((1 : I), unitInterval.symm t) = b
    exact hright (unitInterval.symm t)
  · intro u v hu0 hu1 hv0 hv1
    change D (u, unitInterval.symm v) ∉ K
    have hs0 : (unitInterval.symm v : ℝ) ≠ 0 := by
      have hσ : (unitInterval.symm v : ℝ) = 1 - (v : ℝ) := by simp
      intro hs
      apply hv1
      linarith
    have hs1 : (unitInterval.symm v : ℝ) ≠ 1 := by
      have hσ : (unitInterval.symm v : ℝ) = 1 - (v : ℝ) := by simp
      intro hs
      apply hv0
      linarith
    exact hint u (unitInterval.symm v) hu0 hu1 hs0 hs1

/-- **Simultaneous reparametrisation.**  If `γ` and `δ` bound a disk whose
interior avoids `K`, and `φ : I → I` is continuous, fixes the endpoints and
maps the interior of `I` into itself, then the reparametrised arcs `γ∘φ`
and `δ∘φ` bound a disk whose interior avoids `K` (precompose the square
with `(φ, id)` in the first coordinate). -/
theorem PathsBoundDiskInteriorFree_reparam {X : Type*} [TopologicalSpace X] {K : Set X}
    {a b : X} {γ δ : Path a b} (φ : C(I, I))
    (hφ0 : φ (0 : I) = (0 : I)) (hφ1 : φ (1 : I) = (1 : I))
    (hφint : ∀ u : I, (u : ℝ) ≠ 0 → (u : ℝ) ≠ 1 → (φ u : ℝ) ≠ 0 ∧ (φ u : ℝ) ≠ 1)
    (hγδ : PathsBoundDiskInteriorFree K γ δ) :
    PathsBoundDiskInteriorFree K (pathReparam γ φ hφ0 hφ1) (pathReparam δ φ hφ0 hφ1) := by
  rcases hγδ with ⟨D, hbot, htop, hleft, hright, hint⟩
  let ψ : I × I → I × I := fun p => (φ p.1, p.2)
  have hψ : Continuous ψ := by
    dsimp [ψ]
    fun_prop
  refine ⟨D.comp (ContinuousMap.mk ψ hψ), ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    change D (φ s, (0 : I)) = pathReparam γ φ hφ0 hφ1 s
    rw [pathReparam_apply, hbot]
  · intro s
    change D (φ s, (1 : I)) = pathReparam δ φ hφ0 hφ1 s
    rw [pathReparam_apply, htop]
  · intro t
    change D (φ (0 : I), t) = a
    rw [hφ0]
    exact hleft t
  · intro t
    change D (φ (1 : I), t) = b
    rw [hφ1]
    exact hright t
  · intro u v hu0 hu1 hv0 hv1
    change D (φ u, v) ∉ K
    rcases hφint u hu0 hu1 with ⟨hw0, hw1⟩
    exact hint (φ u) v hw0 hw1 hv0 hv1

/-- Reparametrising a simple knot path by an injective endpoint-fixing
interior-preserving map keeps it a simple knot path. -/
lemma IsKnotArcPath_reparam {r : ℝ → Space} {a b : AddCircle period}
    {α : Path (knotMap r a) (knotMap r b)} (φ : C(I, I))
    (hφ0 : φ (0 : I) = (0 : I)) (hφ1 : φ (1 : I) = (1 : I))
    (hφinj : Function.Injective φ)
    (hα : IsKnotArcPath r a b α) : IsKnotArcPath r a b (pathReparam α φ hφ0 hφ1) := by
  constructor
  · intro s t hst
    -- (α∘φ) s = (α∘φ) t ⇒ φ s = φ t (α injective) ⇒ s = t (φ injective)
    have hφs : φ s = φ t := hα.1 (pathReparam_apply α φ hφ0 hφ1 s ▸ hst ▸
      (pathReparam_apply α φ hφ0 hφ1 t).symm)
    exact hφinj hφs
  · intro s
    exact hα.2 (φ s)

