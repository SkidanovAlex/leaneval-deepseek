import Mathlib
import Submission.Work.Cohomology.Subdivision

/-!
# The mesh of affine chains: barycentres and nested vertex subsets

This file starts the **`ε`-smallness / mesh** chapter of the subdivision theory
(`Submission/NOTES.md`): the geometric input for the small-simplices theorem and hence for
Mayer–Vietoris.

The whole barycentric subdivision of `Δᴺ` is built (`Submission/Work/Cohomology/Subdivision.lean`)
from the `ℤ`-linear cone over the barycentre.  The two facts which make it *shrink* are

* **combinatorial**: every vertex family occurring in `sdLC k` is a *nested* family of uniform
  averages of the vertices of `Δᵏ` — this is `IsBaryNested`;
* **metric**: two uniform averages of nested subsets of a family of points have distance at most
  `(1 - |S|/|T|)` times the diameter of the family, hence at most `k/(k+1)` times it.

Since the standard simplex carries the `sup` metric (subtype of `Fin (N+1) → ℝ`), the second fact
is proved by the triangle inequality for convex combinations and holds in any normed space.

## Main definitions

* `baryOf S` — the uniform average (`barycentre`) of the vertices indexed by a nonempty `Finset`;
* `IsBaryNested w` — the vertex family `w` is, vertexwise, a nested chain of such barycentres of
  subsets of the standard vertices;
* `meshVF v` — the diameter of the vertex set of `v` (the *mesh* of the affine simplex);
* `affComp v u` — the vertex family `j ↦ affineSimplex v (u j)` (composition of affine simplices);
* `pushLC n k C` — the `ℤ`-linear "push a chain forward along each entry of `C`" operator;
* `sdIterLC n N` — the `N`-fold barycentric subdivision of the identity simplex of `Δⁿ`, as an
  affine chain.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-- **The barycentre of a nonempty finite set of vertices** of a standard simplex: the uniform
average of the corresponding vertices. -/
def baryOf {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset ι) (hS : S.Nonempty) :
    stdSimplex ℝ ι :=
  ⟨fun l => if l ∈ S then ((S.card : ℝ))⁻¹ else 0, by
    constructor
    · intro l
      by_cases h : l ∈ S
      · simp only [h, ↓reduceIte]; positivity
      · simp only [h, ↓reduceIte, le_refl]
    · rw [← Finset.sum_filter]
      have : Finset.univ.filter (· ∈ S) = S := by
        ext l; simp
      rw [this, Finset.sum_const, nsmul_eq_mul]
      have : (S.card : ℝ) ≠ 0 := by
        exact_mod_cast Finset.card_ne_zero.mpr hS
      field_simp⟩

@[simp]
theorem baryOf_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset ι) (hS : S.Nonempty)
    (l : ι) : (baryOf S hS) l = if l ∈ S then ((S.card : ℝ))⁻¹ else 0 := rfl

/-- The coordinates of `bary`. -/
theorem bary_apply {N k : ℕ} (v : Fin (k + 1) → stdSimplex ℝ (Fin (N + 1))) (i : Fin (N + 1)) :
    (bary v) i = ((k + 1 : ℝ))⁻¹ * ∑ j, v j i := rfl

/-- The cone point of the subdivision of `Δᵏ` is the barycentre of all its vertices. -/
theorem bary_eq_baryOf_univ (k : ℕ) :
    (bary (idVert k) : stdSimplex ℝ (Fin (k + 1))) = baryOf Finset.univ
      (Finset.univ_nonempty (α := Fin (k + 1))) := by
  ext l
  rw [baryOf_apply, bary_apply]
  simp only [Finset.mem_univ, ↓reduceIte, Finset.card_univ, Fintype.card_fin]
  have h1 : ∑ j : Fin (k + 1), (idVert k j : Fin (k + 1) → ℝ) l = 1 := by
    simp [idVert]
  rw [h1, mul_one]
  congr 1
  push_cast
  ring

/-- **Nested barycentre vertex family**: a vertex family `w : Fin (k+1) → Δᵏ` all of whose
vertices are uniform averages of (nonempty) subsets of the standard vertices of `Δᵏ`, the subsets
forming a chain under inclusion.

Note the direction of the chain: the subdivision `sdLC` puts the barycentre of the *whole* vertex
set first (`coneVF b v = Fin.cons b v`), and the vertex sets *decrease* with the index, so the
monotonicity is `i ≤ j → S j ⊆ S i`.  (Either direction is equally good for the metric estimate
`diam_affComp_le`.) -/
def IsBaryNested {k : ℕ} (w : Fin (k + 1) → stdSimplex ℝ (Fin (k + 1))) : Prop :=
  ∃ (S : Fin (k + 1) → Finset (Fin (k + 1))) (hS : ∀ j, (S j).Nonempty),
    (∀ i j : Fin (k + 1), i ≤ j → S j ⊆ S i) ∧ ∀ j, w j = baryOf (S j) (hS j)

/-- The **mesh** of an affine simplex: the diameter of its vertex family. -/
def meshVF {N k : ℕ} (v : Fin (k + 1) → stdSimplex ℝ (Fin (N + 1))) : ℝ :=
  Metric.diam (Set.range v)

/-- The vertex family obtained by *composing* the affine simplex with vertices `v` with the vertex
family `u`: `i ↦ affineSimplex v (u i)` (this is an affine simplex with the same vertices as `v`). -/
def affComp {N k j : ℕ} (v : Fin (k + 1) → stdSimplex ℝ (Fin (N + 1)))
    (u : Fin (j + 1) → stdSimplex ℝ (Fin (k + 1))) : Fin (j + 1) → stdSimplex ℝ (Fin (N + 1)) :=
  fun i => affineSimplex v (u i)

/-- **Push a chain forward along each of the affine simplices of another chain**: the `ℤ`-linear
map `C ↦ (c ↦ ∑ᵥ C v • v_*(c))`, where `v_*` composes with the affine simplex with vertices `v`.
This is the affine-chain avatar of `pushChain`. -/
def pushLC (n k : ℕ) : LinChain n n →ₗ[ℤ] (LinChain n k →ₗ[ℤ] LinChain n k) :=
  Finsupp.linearCombination ℤ fun v : Fin (n + 1) → stdSimplex ℝ (Fin (n + 1)) =>
    Finsupp.lmapDomain ℤ ℤ fun u : Fin (k + 1) → stdSimplex ℝ (Fin (n + 1)) => affComp v u

/-- **The `N`-fold barycentric subdivision of the identity simplex of `Δⁿ`**, as an affine chain of
`Δⁿ`.  `sdIterLC n 0` is the identity simplex and `sdIterLC n (N+1)` pushes `sdLC n` forward along
each simplex of `sdIterLC n N`. -/
def sdIterLC (n : ℕ) (N : ℕ) : LinChain n n :=
  match N with
  | 0 => Finsupp.single (idVert n) 1
  | (N + 1) => pushLC n n (sdIterLC n N) (sdLC n)

end

end Work.Cohomology
