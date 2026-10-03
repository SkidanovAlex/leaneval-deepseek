import Mathlib
import Submission.Work.ORLocInd.Howie.Defs2
import Submission.Work.ORLocInd.Howie.indicable_of_labelling

namespace Work.ORLocInd.Howie

open Quiver

/-! ## Two self-contained preparations

The main theorem is the *contrapositive* of Howie's Case 1: if no vertex group is indicable (at the
base vertex `v`), then the presentation admits no indicable labelling.  The proof is the standard
one: a labelling which vanishes on the relators and has a closed path of non-zero level is
non-trivial on the presented vertex group, and a non-trivial homomorphism to `ℤ` can be corrected
to a surjective one.

The two auxiliary results below (`relatorNormalClosure_le_ker_pathSumHom_aux` and
`exists_surjective_of_labelling`) are the ingredients of `indicable_of_labelling`, reproved here so
that the present file depends only on `pathSum_of_reducesTo`, `pathSum_pmul` and
`exists_surjective_of_ne_one`. -/

/-- The level of a conjugate `δ · rᵢ · δ⁻¹` of a relator is `0`, because the labelling vanishes on
`rᵢ` and is balanced. -/
theorem pathSum_conj_relator {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Presentation V) (L : Labelling V) (hL : VanishOnRelators L P) (x : V)
    {i : P.ι} {δ : Quiver.Path x (P.base i)} :
    pathSum L.toFun (pmul δ (pmul (P.path i) δ.reverse)) = 0 := by
  rw [pathSum_pmul L.toFun L.isBalanced, pathSum_pmul L.toFun L.isBalanced,
    pathSum_reverse L.toFun L.isBalanced, hL i]
  ring

/-- The conjugates of the relators lie in the kernel of the labelling homomorphism, hence so does
the normal closure of the relators: the labelling descends to the presented vertex group. -/
theorem relatorNormalClosure_le_ker_pathSumHom_aux {V : Type*} [Quiver V]
    [Quiver.HasInvolutiveReverse V]
    (P : Presentation V) (L : Labelling V) (hL : VanishOnRelators L P) (x : V) :
    P.relatorNormalClosure x ≤ (pathSumHom L.toFun L.isBalanced x).ker := by
  refine Subgroup.normalClosure_le_normal ?_
  rintro y ⟨i, δ, hδ, rfl⟩
  change Multiplicative.ofAdd (pathSum L.toFun (pmul δ (pmul (P.path i) δ.reverse))) = 1
  rw [pathSum_conj_relator P L hL x, ofAdd_zero]

/-- A labelling which vanishes on the relators and has a closed path of non-zero level gives a
surjection of the presented vertex group at the base point of that path onto `ℤ`. -/
theorem exists_surjective_of_labelling {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Presentation V) (L : Labelling V) (hL : VanishOnRelators L P) {x : V}
    (p : Quiver.Path x x) (hp : pathSum L.toFun p ≠ 0) :
    ∃ φ : P.vertexGroup x →* Multiplicative ℤ, Function.Surjective φ := by
  classical
  -- the labelling homomorphism on the free groupoid, descended to the presented vertex group
  let ψ : VertexGroup x →* Multiplicative ℤ := pathSumHom L.toFun L.isBalanced x
  have hker : P.relatorNormalClosure x ≤ ψ.ker :=
    relatorNormalClosure_le_ker_pathSumHom_aux P L hL x
  let φ : P.vertexGroup x →* Multiplicative ℤ :=
    QuotientGroup.lift (P.relatorNormalClosure x) ψ hker
  have hφval : ∀ g : VertexGroup x,
      φ (QuotientGroup.mk g) = Multiplicative.ofAdd (pathSum L.toFun g.1) := by
    intro g
    change (QuotientGroup.lift (P.relatorNormalClosure x) ψ hker) (QuotientGroup.mk g) = _
    rw [QuotientGroup.lift_mk]
    rfl
  -- the reduced form of `p` has non-zero level, so `φ` is non-trivial
  have hp' : pathSum L.toFun (red p) ≠ 0 := by
    rwa [← pathSum_of_reducesTo L.toFun L.isBalanced (reducesTo_red p)]
  have hne : ∃ g : P.vertexGroup x, φ g ≠ 1 := by
    let g₀ : VertexGroup x := ⟨red p, isReduced_red p⟩
    refine ⟨QuotientGroup.mk g₀, ?_⟩
    rw [hφval g₀]
    exact fun h1 => hp' (ofAdd_eq_one.mp h1)
  -- a non-trivial homomorphism onto the infinite cyclic group can be corrected to a surjection
  exact exists_surjective_of_ne_one φ hne

/-- **The contrapositive of Howie's Case 1.**  If the vertex group of the presentation `⟨Γ | R⟩` at
`v` admits no surjection onto `ℤ`, and if `Γ` is connected with base point `v`, then `⟨Γ | R⟩`
admits no indicable labelling: a labelling which vanishes on the relators cannot have a closed path
of non-zero level.

Indeed, conjugating any closed path `p` at `x` into the vertex group at `v` by a path `δ : v → x`
preserves its level (`pathSum_pmul`, `pathSum_reverse`), so a labelling with a non-zero closed path
at *some* vertex produces a non-zero closed path at `v`; the descended labelling homomorphism is
then non-trivial, and `exists_surjective_of_ne_one` turns it into a surjection of `P.vertexGroup v`
onto `ℤ`, contradicting `hnon`. -/
theorem not_hasIndicableLabelling {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Work.ORLocInd.Howie.Presentation V) (v : V) (hconn : ∀ x : V, Nonempty (Quiver.Path v x))
    (hnon : ∀ f : P.vertexGroup v →* Multiplicative ℤ, ¬ Function.Surjective f) :
    ¬ P.HasIndicableLabelling := by
  rintro ⟨L, hL, x, p, hp⟩
  -- conjugating the closed path `p` at `x` into the vertex group at `v` preserves its level
  obtain ⟨δ⟩ := hconn x
  have hq : pathSum L.toFun (pmul (pmul δ p) δ.reverse) ≠ 0 := by
    have h : pathSum L.toFun (pmul (pmul δ p) δ.reverse) = pathSum L.toFun p := by
      rw [pathSum_pmul L.toFun L.isBalanced, pathSum_pmul L.toFun L.isBalanced,
        pathSum_reverse L.toFun L.isBalanced]
      ring
    rwa [h]
  -- the labelling vanishes on the relators and has a closed path of non-zero level at `v`,
  -- so the vertex group at `v` admits a surjection onto `ℤ`
  obtain ⟨φ, hφ⟩ := exists_surjective_of_labelling P L hL (pmul (pmul δ p) δ.reverse) hq
  exact hnon φ hφ

end Work.ORLocInd.Howie
