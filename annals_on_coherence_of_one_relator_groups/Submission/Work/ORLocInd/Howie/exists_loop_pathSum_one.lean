/-
# A reduced loop of level `1` (Howie 2000, Case 1 of Theorem 3.1)

Howie's Case 1 is the *indicable* case: the vertex group `G_v` of the presented groupoid
`⟨Γ | R⟩` at the base vertex `v` admits a surjection `φ : G_v ↠ ℤ`, and one passes to the cyclic
cover of `Γ` given by the induced labelling `θ e = φ (d (e.left) · e · d (e.right)⁻¹)`.  For the
cover to be *usable* it must be non-trivial in the vertical direction: there has to be a closed path
at the base vertex of the base graph whose *level* `pathSum θ` is non-zero — otherwise the cover
would be disconnected and would add nothing.

This file proves the sharp form of that fact: `∃ β : Quiver.Path v v, β.IsReduced ∧
pathSum L β = 1`.  The witness is explicit.  Since `φ` is onto `ℤ` and the projection
`F(Γ)_v → π₁(⟨Γ | R⟩, v)` is onto, the composite `ψ = φ ∘ (P.toVertexGroup v)` is onto `ℤ`, so we
may choose `a ∈ F(Γ)_v` with `ψ a = 1`.  The loop

`β := (d v)⁻¹ · a · (d v)`

is reduced (as `a` is) and *conjugate* to `a`, and conjugation by the chosen path `d v` is exactly
the map `conjElem d` — both computable path identities, proved as `conjElem_conj_reverse` and used
to turn the hypothesis `hpath`

`pathSum L p = φ (P.toVertexGroup v (conjElem d p))`

at `p = β` into `pathSum L β = 1`.  Note that no property of the labelling (such as balancedness or
vanishing on relators) is needed: `hpath` already identifies the level with `φ`.

## Contents

* `conjElem_conj_reverse` — `conjElem d ((d v)⁻¹ · p · d v) = ⟨p, _⟩` for a reduced loop `p`;
* `exists_loop_pathSum_one` — the reduced loop of level `1`.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.exists_labelling
import Submission.Work.ORLocInd.Howie.LabellingAux

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORLocInd.Howie

variable {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
variable {v : V}

/-- **The conjugation by `d v` is undone by conjugating with its reverse.**  For a reduced loop
`p` at `v`, the reduced loop `(d v)⁻¹ · p · (d v)` has `conjElem` (i.e. `d v · – · (d v)⁻¹`)
equal to `p` itself.  In particular `conjElem d` hits every reduced loop at `v`.

The proof is the path computation

`d v · ((d v)⁻¹ · p · d v) · (d v)⁻¹ = ((d v · (d v)⁻¹) · p) · ((d v) · (d v)⁻¹) = p`,

where `pmul A A.reverse = nil` telescopes both occurrences of `d v`. -/
theorem conjElem_conj_reverse (d : ∀ x : V, Quiver.Path v x) (p : Quiver.Path v v)
    (hp : p.IsReduced) :
    conjElem d (pmul (pmul (d v).reverse p) (d v)) = (⟨p, hp⟩ : VertexGroup v) := by
  apply Subtype.ext
  show pmul (pmul (d v) (pmul (pmul (d v).reverse p) (d v))) (d v).reverse = p
  have hA : pmul (d v) (pmul (pmul (d v).reverse p) (d v)) = pmul p (d v) := by
    rw [← pmul_assoc (d v) (pmul (d v).reverse p) (d v)]
    rw [← pmul_assoc (d v) (d v).reverse p]
    rw [pmul_reverse (d v), pmul_nil_left p, red_eq_self hp]
  rw [hA, pmul_assoc p (d v) (d v).reverse, pmul_reverse (d v), pmul_nil_right p, red_eq_self hp]

/-- **Howie's Case 1, surjectivity of the level.**  If the path sums of a labelling `L` compute a
homomorphism `φ` out of `G_v` on the conjugated loops (`hpath`), and `φ` is onto `ℤ`, then some
*reduced* loop at `v` has level `1` — so that the cyclic cover of `Γ` defined by `L` is non-trivial
at the base vertex.

The witness is `β = (d v)⁻¹ · a · (d v)`, where `a` is a preimage of `1` under
`φ ∘ P.toVertexGroup v`; it is reduced by construction and conjugate to `a`, so
`pathSum L β = toAdd (φ (P.toVertexGroup v (conjElem d β))) = toAdd (φ (P.toVertexGroup v a))
= toAdd 1 = 1`. -/
theorem exists_loop_pathSum_one {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Work.ORLocInd.Howie.Presentation V) (v : V) (d : ∀ x : V, Quiver.Path v x)
    (L : Work.ORLocInd.Howie.Labelling V)
    (φ : P.vertexGroup v →* Multiplicative ℤ) (hφ : Function.Surjective φ)
    (hpath : ∀ (x : V) (p : Quiver.Path x x),
      Work.ORLocInd.Howie.pathSum L.toFun p =
        Multiplicative.toAdd (φ (P.toVertexGroup v (Work.ORLocInd.Howie.conjElem d p)))) :
    ∃ β : Quiver.Path v v, β.IsReduced ∧ Work.ORLocInd.Howie.pathSum L.toFun β = 1 := by
  -- the composite `φ ∘ (projection to the presented groupoid)` is onto `ℤ`
  obtain ⟨g, hg⟩ := hφ (Multiplicative.ofAdd 1)
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (P.relatorNormalClosure v) g
  have ha' : φ (P.toVertexGroup v a) = Multiplicative.ofAdd 1 := by
    rw [show P.toVertexGroup v a = g from ha, hg]
  -- the conjugate of `a` by `d v` is a reduced loop whose conjugate is `a` again
  refine ⟨pmul (pmul (d v).reverse a.1) (d v), pmul_isReduced _ _, ?_⟩
  rw [hpath v (pmul (pmul (d v).reverse a.1) (d v))]
  have hconj : φ (P.toVertexGroup v (conjElem d (pmul (pmul (d v).reverse a.1) (d v)))) =
      Multiplicative.ofAdd 1 := by
    rw [conjElem_conj_reverse d a.1 a.2]
    exact ha'
  rw [hconj]
  rfl

end Work.ORLocInd.Howie
