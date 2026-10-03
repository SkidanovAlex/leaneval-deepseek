/-
# Howie's Case 1: the labelling of a presentation induced by a homomorphism to `ℤ`

Howie's proof (*A short proof of a theorem of Brodskii*, Publ. Mat. 44 (2000), Theorem 3.1) is by
contradiction on a *datum* in a staggered groupoid presentation `⟨Γ | R⟩`.  In **Case 1** the vertex
group `G_v` of the presented groupoid is *indicable*, i.e. there is a surjection
`φ : G_v ↠ ℤ`, and the proof passes to the *cyclic cover* of `Γ` defined by the induced labelling

`θ e = φ (d (e.left) · e · d (e.right)⁻¹)`,

where `d x : v → x` is a chosen path to every vertex of `Γ` (which exists when `Γ` is connected).
The properties of `θ` needed for the cover are proved here:

* `θ` is *balanced*: `θ (e⁻¹) = - θ e` (so that the lift of a reduced path is reduced, and so that
  `θ` defines a homomorphism `F(Γ)_v →* ℤ`); this is `isBalanced_labOf`;
* the level `pathSum θ p` of a *closed* path `p` at `x` is `φ` applied to the conjugate
  `d x · p · (d x)⁻¹` of `p` (`pathSum_labOf` below, via the multiplicativity `conjElem_comp` of the
  conjugation `conjElem d p = d a · p · (d b)⁻¹`);
* consequently `θ` *vanishes on the relators* of `P` — the conjugate of a relator lies in the normal
  closure of the relators, and `φ` factors through the presented groupoid — so that the relators
  lift to *closed* paths of the cover (`VanishOnRelators_of_pathSum_conj`).

The main result is `Work.ORLocInd.Howie.exists_labelling`: for every connected graph, presentation
`P` and surjection `φ` on the vertex group of `P` at `v`, there are `d`, a balanced labelling `L`
and a potential `τ` (with `τ (e⁻¹) = τ e - L e`, needed for the *code* of the edges of the cover)
such that the path sums of `L` compute `φ` on the conjugates.

## Contents

* `pathSum_labOf` — the path-sum formula for the labelling induced by a homomorphism `ψ`;
* `exists_labelling` — the case-1 data `(d, L, τ)`;
* `red_reverse`, `pmul_congr_right`, `conjElem_mem_relatorNormalClosure` and
  `VanishOnRelators_of_pathSum_conj` — the relator-conjugates lie in the normal closure, so `L`
  vanishes on the relators, together with the packaged form
  `exists_labelling_vanishOnRelators`.

The conjugation `conjElem`, the labelling `labOf` and the normal-form lemmas
`pmul_red_left`/`pmul_red_right` live in `Howie/LabellingAux.lean`; the multiplicativity
`conjElem_comp` and the balancedness `isBalanced_labOf` are in `Howie/conjElem_comp.lean` and
`Howie/isBalanced_labOf.lean`.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.LabellingAux
import Submission.Work.ORLocInd.Howie.conjElem_comp
import Submission.Work.ORLocInd.Howie.isBalanced_labOf
import Submission.Work.ORLocInd.Howie.Relator
import Submission.Work.ORLocInd.Howie.CoverGraph
import Submission.Work.ORLocInd.Howie.Cover
import Submission.Work.ORLocInd.Howie.CoverPresentation
import Submission.Work.ORLocInd.Howie.exists_tau

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd.Howie

/-- The path sums of the labelling `labOf d ψ` induced by a homomorphism `ψ : F(Γ)_v →* ℤ` compute
`ψ` on the conjugated loop: `pathSum (labOf d ψ) p = ψ (d a · p · (d b)⁻¹)`.

This is the formula which, for a *closed* path `p` at `x`, identifies the level of `p` in the cyclic
cover with `φ` of its conjugate `d x · p · (d x)⁻¹`.  It is proved by induction on the path using the
multiplicativity of the conjugation (`conjElem_comp`) and the fact that the empty path conjugates to
the trivial loop (`conjElem_nil`). -/
theorem pathSum_labOf {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V] {v : V}
    (d : ∀ x : V, Quiver.Path v x) (ψ : VertexGroup v →* Multiplicative ℤ) :
    ∀ {a b : V} (p : Quiver.Path a b),
      pathSum (labOf d ψ) p = Multiplicative.toAdd (ψ (conjElem d p)) := by
  intro a b p
  induction p with
  | nil => rw [pathSum_nil, conjElem_nil, map_one, toAdd_one]
  | cons q e ih =>
      rw [pathSum_cons, ih]
      show Multiplicative.toAdd (ψ (conjElem d q)) +
          Multiplicative.toAdd (ψ (conjElem d e.toPath)) =
        Multiplicative.toAdd (ψ (conjElem d (q.cons e)))
      rw [← toAdd_mul, ← map_mul, ← conjElem_comp d q e.toPath]
      rfl

theorem exists_labelling {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Work.ORLocInd.Howie.Presentation V) (v : V)
    (hconn : ∀ x : V, Nonempty (Quiver.Path v x))
    (φ : P.vertexGroup v →* Multiplicative ℤ) (hφ : Function.Surjective φ) :
    ∃ (d : ∀ x : V, Quiver.Path v x) (L : Work.ORLocInd.Howie.Labelling V)
      (τ : Quiver.Total V → ℤ),
      (∀ e : Quiver.Total V, τ (Quiver.totalReverse e) = τ e - L.toFun e) ∧
      (∀ (x : V) (p : Quiver.Path x x),
        Work.ORLocInd.Howie.pathSum L.toFun p =
          Multiplicative.toAdd
            (φ (P.toVertexGroup v
              ⟨Work.ORLocInd.Howie.pmul (Work.ORLocInd.Howie.pmul (d x) p) (d x).reverse,
                Work.ORLocInd.Howie.pmul_isReduced _ _⟩))) := by
  classical
  -- a chosen path to every vertex, and the labelling it induces
  obtain ⟨τ, hτ⟩ := exists_tau (⟨labOf (fun x => Classical.choice (hconn x))
      (φ.comp (P.toVertexGroup v)),
      isBalanced_labOf _ (φ.comp (P.toVertexGroup v))⟩ : Labelling V) P.noSelfLoop
  refine ⟨fun x => Classical.choice (hconn x),
    ⟨labOf (fun x => Classical.choice (hconn x)) (φ.comp (P.toVertexGroup v)),
      isBalanced_labOf _ (φ.comp (P.toVertexGroup v))⟩, τ, hτ, ?_⟩
  intro x p
  exact pathSum_labOf (fun x => Classical.choice (hconn x))
    (φ.comp (P.toVertexGroup v)) p

/-! ## The labelling vanishes on the relators

The labelling produced by `exists_labelling` sends every relator of `P` to level `0`: the level of
the conjugate `d x · r_i · (d x)⁻¹` of a relator is the `φ`-value of an element of the normal
closure of the relators, and `φ` factors through the presented groupoid.  Consequently the relators
lift to *closed* paths of the cyclic cover (`VanishOnRelators`, used by
`Howie/CoverPresentation.lean`). -/

/-- Reducing a path and then reversing is the same as reversing and then reducing. -/
theorem red_reverse {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V] {a b : V}
    (p : Quiver.Path a b) : red p.reverse = (red p).reverse :=
  red_eq_of_reducesTo_isReduced (Quiver.Path.ReducesTo.reverse (reducesTo_red p))
    (isReduced_red p).reverse

/-- The free-groupoid product is compatible with reducing the second factor. -/
theorem pmul_congr_right {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V] {a b c : V}
    (A : Quiver.Path a b) {Y Y' : Quiver.Path b c} (h : Y.ReducesTo Y') :
    pmul A Y = pmul A Y' :=
  red_eq_of_reducesTo_isReduced ((reducesTo_comp_left h A).trans (reducesTo_red (A.comp Y')))
    (isReduced_red (A.comp Y'))

/-- A conjugate of a relator lies in the normal closure of the relators: conjugating by an
arbitrary path `d x` gives the same element as conjugating by its reduced form. -/
theorem conjElem_mem_relatorNormalClosure {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]
    {v : V} (P : Presentation V) (d : ∀ x : V, Quiver.Path v x) (i : P.ι) :
    conjElem d (P.path i) ∈ P.relatorNormalClosure v := by
  refine Subgroup.subset_normalClosure ⟨i, red (d (P.base i)), isReduced_red _, ?_⟩
  apply Subtype.ext
  show pmul (pmul (d (P.base i)) (P.path i)) (d (P.base i)).reverse =
    pmul (red (d (P.base i))) (pmul (P.path i) (red (d (P.base i))).reverse)
  calc pmul (pmul (d (P.base i)) (P.path i)) (d (P.base i)).reverse
      = pmul (pmul (red (d (P.base i))) (P.path i)) (d (P.base i)).reverse :=
        congrArg (fun z => pmul z (d (P.base i)).reverse)
          (pmul_red_left (d (P.base i)) (P.path i)).symm
    _ = pmul (red (d (P.base i))) (pmul (P.path i) (d (P.base i)).reverse) := pmul_assoc _ _ _
    _ = pmul (red (d (P.base i))) (pmul (P.path i) (red (d (P.base i))).reverse) :=
        congrArg (fun z => pmul (red (d (P.base i))) z)
          (pmul_congr_right (P.path i)
            (Quiver.Path.ReducesTo.reverse (reducesTo_red (d (P.base i)))))

/-- If the path sums of a balanced labelling `L` compute `φ` on the conjugated loops, then `L`
vanishes on the relators of `P`: the relators lift to closed paths of the cyclic cover. -/
theorem VanishOnRelators_of_pathSum_conj {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]
    {v : V} (P : Presentation V) (d : ∀ x : V, Quiver.Path v x) (L : Labelling V)
    (φ : P.vertexGroup v →* Multiplicative ℤ)
    (hpath : ∀ (x : V) (p : Quiver.Path x x),
      pathSum L.toFun p =
        Multiplicative.toAdd (φ (P.toVertexGroup v (conjElem d p)))) :
    VanishOnRelators L P := by
  intro i
  rw [hpath (P.base i) (P.path i)]
  have h1 : P.toVertexGroup v (conjElem d (P.path i)) = 1 := by
    rw [P.toVertexGroup_apply]
    exact (QuotientGroup.eq_one_iff (conjElem d (P.path i))).mpr
      (conjElem_mem_relatorNormalClosure P d i)
  rw [h1, map_one, toAdd_one]

/-- **The case-1 data of Howie's proof, with the relators lifting to closed paths**: the labelling
produced by `exists_labelling` additionally vanishes on the relators of `P`. -/
theorem exists_labelling_vanishOnRelators {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Work.ORLocInd.Howie.Presentation V) (v : V)
    (hconn : ∀ x : V, Nonempty (Quiver.Path v x))
    (φ : P.vertexGroup v →* Multiplicative ℤ) (hφ : Function.Surjective φ) :
    ∃ (d : ∀ x : V, Quiver.Path v x) (L : Work.ORLocInd.Howie.Labelling V)
      (τ : Quiver.Total V → ℤ),
      (∀ e : Quiver.Total V, τ (Quiver.totalReverse e) = τ e - L.toFun e) ∧
      (∀ (x : V) (p : Quiver.Path x x),
        Work.ORLocInd.Howie.pathSum L.toFun p =
          Multiplicative.toAdd
            (φ (P.toVertexGroup v
              ⟨Work.ORLocInd.Howie.pmul (Work.ORLocInd.Howie.pmul (d x) p) (d x).reverse,
                Work.ORLocInd.Howie.pmul_isReduced _ _⟩))) ∧
      VanishOnRelators L P := by
  obtain ⟨d, L, τ, hτ, hpath⟩ := exists_labelling P v hconn φ hφ
  exact ⟨d, L, τ, hτ, hpath, VanishOnRelators_of_pathSum_conj P d L φ hpath⟩

end Work.ORLocInd.Howie
