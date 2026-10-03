import Mathlib
import Submission.Work.OROneRel.graded_hnn_coset
import Submission.Work.OROneRel.coset_lev

/-!
# The "line graph" of a pair `(H, t)` along a weight map

Let `G` be a group, `H ≤ G`, `t ∈ G`, and `φ : G →* Multiplicative ℤ` a weight map with
`H ≤ ker φ`.  Write `N = ker φ` and, for `m : ℤ`,

  `chainPiece H t φ hH m = (t ^ m * H * t ^ (-m)).subgroupOf N`,

the `m`-th **piece** of the chain of conjugates of `H`.

The **line graph** `lineGraph H t φ` is the graph
* whose vertices are the pairs `(m, x)` with `x` a coset of `chainPiece m` in `N`,
* in which two vertices are adjacent when one is at level `m`, the other at level `m + 1`, and the
  two cosets meet in `N` (i.e. some `n : N` represents both).

## Why this is the right object

The coset graph `GradedHNN.Coset H t` (vertices `G ⧸ H`, edges `{gH, gtH}`) is isomorphic to
`lineGraph H t φ`: the vertex `gH` at level `φ g = m` corresponds to the pair
`(m, (g * t ^ (-m)) · chainPiece m)`, and the edge `{gH, gtH}` corresponds to the pair of vertices
`(m, ·)`, `(m+1, ·)` with the *same* representative `g * t ^ (-m) : N` — exactly the `lineAdj`
relation.  This reduces `Work.OROneRel.band_cosetGraph_isTree` to a statement about the chain of
subgroups `t ^ m H t ^ (-m)` of `N = ker φ`.

For the two-letter band (with `H = winRho.range`, `t = tlLowTau p q`, `φ = cohom (tlW p q)`) the
line graph is precisely the **Bass--Serre tree of the line of band domains**: its vertices are the
lifts of the bands `τ ^ m D` to the universal cover and its edges are the lifts of the gates
`τ ^ m (D ∩ τ D)`, two consecutive lifts being adjacent exactly when they meet.  That this graph
*is* a tree is the one-dimensional case of Linton, *One-relator hierarchies*, arXiv 2202.11324,
Proposition `splitting` (with `2.2.19`) for the band `ℤ`-domain; the present file builds only the
interface (`Work.OROneRel.cosetGraph_lineGraph_iso`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.OROneRel

universe u

variable {G : Type u} [Group G] (H : Subgroup G) (t : G) (φ : G →* Multiplicative ℤ)

/-- **The conjugates of `H` lie in the kernel of the weight map**: if `H ≤ ker φ` then
`t ^ m * H * t ^ (-m) ≤ ker φ` for every `m : ℤ`. -/
theorem conj_zpow_le_ker (hH : H ≤ φ.ker) (m : ℤ) :
    H.map (MulAut.conj (t ^ m)) ≤ φ.ker := by
  have hH' : ∀ h ∈ H, φ h = 1 := fun h hh => MonoidHom.mem_ker.mp (hH hh)
  intro x hx
  obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hx
  show φ (MulAut.conj (t ^ m) h) = 1
  simp only [MulAut.conj_apply, map_mul, map_inv, hH' h hh, mul_one, mul_inv_cancel]

/-- **The `m`-th piece of the chain**: the conjugate `t ^ m * H * t ^ (-m)`, regarded as a subgroup
of the kernel `N = ker φ`. -/
def chainPiece (hH : H ≤ φ.ker) (m : ℤ) : Subgroup φ.ker :=
  (H.map (MulAut.conj (t ^ m))).subgroupOf φ.ker

/-- **The vertices of the line graph**: the disjoint union over `m : ℤ` of the coset spaces
`N ⧸ chainPiece m`. -/
abbrev lineVertex (hH : H ≤ φ.ker) : Type u :=
  Σ m : ℤ, (φ.ker ⧸ chainPiece H t φ hH m)

/-- The level of a vertex of the line graph. -/
def lineLev (hH : H ≤ φ.ker) (x : lineVertex H t φ hH) : ℤ := x.1

/-- **The adjacency of the line graph**: `(m, x)` is adjacent to `(m + 1, y)` (and conversely)
when the two cosets meet, i.e. when one element `n : N` represents both. -/
def lineAdj (hH : H ≤ φ.ker) : lineVertex H t φ hH → lineVertex H t φ hH → Prop :=
  fun x y =>
    (∃ (m : ℤ) (n : φ.ker),
      x = ⟨m, QuotientGroup.mk (s := chainPiece H t φ hH m) n⟩ ∧
      y = ⟨m + 1, QuotientGroup.mk (s := chainPiece H t φ hH (m + 1)) n⟩) ∨
    (∃ (m : ℤ) (n : φ.ker),
      y = ⟨m, QuotientGroup.mk (s := chainPiece H t φ hH m) n⟩ ∧
      x = ⟨m + 1, QuotientGroup.mk (s := chainPiece H t φ hH (m + 1)) n⟩)

theorem lineAdj_symm (hH : H ≤ φ.ker) {x y : lineVertex H t φ hH}
    (h : lineAdj H t φ hH x y) : lineAdj H t φ hH y x := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

theorem lineAdj_iff_levels (hH : H ≤ φ.ker) {x y : lineVertex H t φ hH}
    (h : lineAdj H t φ hH x y) :
    y.1 = x.1 + 1 ∨ x.1 = y.1 + 1 := by
  rcases h with ⟨m, n, hx, hy⟩ | ⟨m, n, hx, hy⟩
  · left; rw [hx, hy]
  · right; rw [hx, hy]

/-- The line graph as a quiver (proof-irrelevant labels, as for the coset graph). -/
@[reducible] instance instQuiverLine (hH : H ≤ φ.ker) : Quiver (lineVertex H t φ hH) :=
  ⟨fun x y => PLift (lineAdj H t φ hH x y)⟩

instance instSubsingletonHomLine (hH : H ≤ φ.ker) (x y : lineVertex H t φ hH) :
    Subsingleton (x ⟶ y) :=
  ⟨fun a b => Subsingleton.elim (α := PLift (lineAdj H t φ hH x y))
    (show PLift (lineAdj H t φ hH x y) from a) (show PLift (lineAdj H t φ hH x y) from b)⟩

instance instHasReverseLine (hH : H ≤ φ.ker) :
    Quiver.HasReverse (lineVertex H t φ hH) where
  reverse' := fun {_ _} e => ⟨lineAdj_symm H t φ hH e.down⟩

instance instHasInvolutiveReverseLine (hH : H ≤ φ.ker) :
    Quiver.HasInvolutiveReverse (lineVertex H t φ hH) where
  inv' := fun {_ _} e => Subsingleton.elim _ _

end Work.OROneRel
