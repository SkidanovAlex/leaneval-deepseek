/-
# L4: the erasure of the substitution is the identity modulo the relators

For the Tietze data `D : TietzeData P` of Howie's Case 2 and every element `b` of the
free-groupoid vertex group `F(Γ)_x`, the erasure `delEraseVG D.K x` of the substitution
`D.pathSubst.vertexHom x` differs from the identity by an element of the normal closure of the
relators of `P`:

`delEraseVG D.K x (D.pathSubst.vertexHom x b) * b⁻¹ ∈ P.relatorNormalClosure x`.

This is the condition `hcong` of the abstract Tietze argument (`abstract_tietze`), one of the four
side conditions of the elimination step of Howie's Case 2 (see
`Submission/Work/ORLocInd/Howie/L4/SubstConditions.lean`).

The proof is by induction on the underlying path.  For *every* path `p : x → y` of `Γ` we show

`⟨erasePath (red (mapPath p)) · (red p)⁻¹, _⟩ ∈ P.relatorNormalClosure x`   (★)

* for the empty path both factors are empty, so the element is `1`;
* for `p = q.cons e` the substitution is multiplicative (`PathSubst.mapPath_cons`) and the erasure
  is multiplicative (`DelV.erasePath_pmul`), so with `α = erasePath (red (mapPath q))`, `β = red q`,
  `Ze = erasePath (red (substArrow e))` and `ε = e.toPath` the left hand side of (★) is
  `(α · Ze) · (β · ε)⁻¹`.  The induction hypothesis gives `α · β⁻¹ ∈ N_x`, while
  `Ze · ε⁻¹ ∈ N_{e.left}` is the single-arrow computation
  (`erasePath_red_substArrow_mul_reverse_mem`: for a *kept* arrow the erasure of the substitution is
  the arrow itself, so the defect is trivial; for a *deleted* arrow the defect is a conjugate of the
  deleted relator).  Conjugating the latter back along `α` by
  `conjPathHom_mem_relatorNormalClosure` and multiplying inside the subgroup finishes the step
  (`pmul_mem_relatorNormalClosure_of_mem`).
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.L4.SubstSupport
import Submission.Work.ORLocInd.Howie.conjPathHom_mem_relatorNormalClosure
import Submission.Work.ORLocInd.Howie.mem_relatorNormalClosure_substArrow_of_not_pred
import Submission.Work.ORLocInd.Howie.erasePath_substArrow_of_pred

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

namespace Work.L4

open Quiver
open Work.ORLocInd.Howie

variable {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-! ## Two elementary facts about `red` -/

/-- Reducing a path extended by an arrow: `red (p · e) = red p · e`. -/
theorem red_cons {a b c : V} (p : Quiver.Path a b) (e : b ⟶ c) :
    red (p.cons e) = pmul (red p) (Quiver.Hom.toPath e) := by
  refine red_eq_of_reducesTo_isReduced ?_ (pmul_isReduced _ _)
  exact (Quiver.Path.ReducesTo.comp_right (reducesTo_red p) (Quiver.Hom.toPath e)).trans
    (comp_reducesTo_pmul (red p) (Quiver.Hom.toPath e))

/-- The empty path of the arrow-deleted graph is reduced. -/
theorem red_dnil {K : Keep V} (a : V) : red (dnil K a) = dnil K a :=
  red_eq_self (Quiver.Path.IsReduced.nil _)

/-! ## The defect of a single arrow -/

/-- The defect of a single arrow `e`: the erasure of the reduced substitution of `e`, followed by
`e⁻¹`, lies in the normal closure of the relators.  For a kept arrow the substitution is the arrow
itself and the defect is trivial; for a deleted arrow it is a conjugate of the deleted relator. -/
theorem erasePath_red_substArrow_mul_reverse_mem (P : Presentation V) (D : TietzeData P)
    (e : Quiver.Total V) :
    (⟨pmul (DelV.erasePath D.K e.left (red (D.substArrow e))) (Quiver.Hom.toPath e.hom).reverse,
      pmul_isReduced _ _⟩ : VertexGroup e.left) ∈ P.relatorNormalClosure e.left := by
  by_cases h : D.K.pred e
  · -- a kept arrow: the erasure of its substitution is the arrow itself, so the defect is `1`
    have hE : DelV.erasePath D.K e.left (red (D.substArrow e)) = Quiver.Hom.toPath e.hom := by
      rw [← DelV.red_erasePath D.K (D.substArrow e), erasePath_substArrow_of_pred D h,
        red_eq_self (Quiver.Path.IsReduced.of_length_lt_two (p := Quiver.Hom.toPath e.hom)
          (by rw [Quiver.Path.length_toPath]; norm_num))]
    have hx : (⟨pmul (DelV.erasePath D.K e.left (red (D.substArrow e)))
          (Quiver.Hom.toPath e.hom).reverse, pmul_isReduced _ _⟩ : VertexGroup e.left)
        = (1 : VertexGroup e.left) := by
      apply Subtype.ext
      show pmul (DelV.erasePath D.K e.left (red (D.substArrow e)))
          (Quiver.Hom.toPath e.hom).reverse = (Quiver.Path.nil : Quiver.Path e.left e.left)
      rw [hE, pmul_reverse]
    rw [hx]
    exact Subgroup.one_mem (P.relatorNormalClosure e.left)
  · -- a deleted arrow: the goal element is the inverse of the element of
    -- `mem_relatorNormalClosure_substArrow_of_not_pred`
    have hinv : (⟨(pmul (Quiver.Hom.toPath e.hom)
          (DelV.erasePath D.K e.left (D.substArrow e)).reverse).reverse,
        (pmul_isReduced _ _).reverse⟩ : VertexGroup e.left) ∈ P.relatorNormalClosure e.left :=
      Subgroup.inv_mem (P.relatorNormalClosure e.left)
        (mem_relatorNormalClosure_substArrow_of_not_pred D h)
    have hx : (⟨pmul (DelV.erasePath D.K e.left (red (D.substArrow e)))
          (Quiver.Hom.toPath e.hom).reverse, pmul_isReduced _ _⟩ : VertexGroup e.left)
        = (⟨(pmul (Quiver.Hom.toPath e.hom)
              (DelV.erasePath D.K e.left (D.substArrow e)).reverse).reverse,
            (pmul_isReduced _ _).reverse⟩ : VertexGroup e.left) := by
      apply Subtype.ext
      show pmul (DelV.erasePath D.K e.left (red (D.substArrow e)))
          (Quiver.Hom.toPath e.hom).reverse
        = (pmul (Quiver.Hom.toPath e.hom)
            (DelV.erasePath D.K e.left (D.substArrow e)).reverse).reverse
      rw [pmul_reverse_comp, Quiver.Path.reverse_reverse,
        ← DelV.red_erasePath D.K (D.substArrow e), pmul_red_left]
    rw [hx]
    exact hinv

/-! ## Multiplying two defects -/

/-- If `α · β⁻¹ ∈ N_x` and `Ee · ε⁻¹ ∈ N_b`, then `(α · Ee) · (β · ε)⁻¹ ∈ N_x`: the relation "equal
modulo the relators" is compatible with the free-groupoid multiplication. -/
theorem pmul_mem_relatorNormalClosure_of_mem (P : Presentation V) {x b y : V}
    (α β : Quiver.Path x b) (Ee ε : Quiver.Path b y)
    (hαβ : (⟨pmul α β.reverse, pmul_isReduced _ _⟩ : VertexGroup x) ∈ P.relatorNormalClosure x)
    (hEe : (⟨pmul Ee ε.reverse, pmul_isReduced _ _⟩ : VertexGroup b) ∈ P.relatorNormalClosure b) :
    (⟨pmul (pmul α Ee) (pmul β ε).reverse, pmul_isReduced _ _⟩ : VertexGroup x)
      ∈ P.relatorNormalClosure x := by
  have hconj : conjPathHom α (⟨pmul Ee ε.reverse, pmul_isReduced _ _⟩ : VertexGroup b)
      ∈ P.relatorNormalClosure x := conjPathHom_mem_relatorNormalClosure P α hEe
  have hprod := Subgroup.mul_mem (P.relatorNormalClosure x) hconj hαβ
  have hW : (⟨pmul (pmul α Ee) (pmul β ε).reverse, pmul_isReduced _ _⟩ : VertexGroup x)
      = (⟨pmul (pmul (pmul α (pmul Ee ε.reverse)) α.reverse) (pmul α β.reverse),
          pmul_isReduced _ _⟩ : VertexGroup x) := by
    apply Subtype.ext
    show pmul (pmul α Ee) (pmul β ε).reverse
      = pmul (pmul (pmul α (pmul Ee ε.reverse)) α.reverse) (pmul α β.reverse)
    rw [pmul_reverse_comp β ε, pmul_assoc α Ee (pmul ε.reverse β.reverse),
      ← pmul_assoc Ee ε.reverse β.reverse, pmul_assoc (pmul α (pmul Ee ε.reverse)) α.reverse,
      ← pmul_assoc α.reverse α β.reverse, pmul_reverse_left α, pmul_nil_left (β.reverse),
      pmul_assoc α (pmul Ee ε.reverse) (red β.reverse),
      pmul_red_right (pmul Ee ε.reverse) β.reverse]
  rw [hW]
  exact hprod

/-! ## The induction -/

/-- (★): the erasure of the reduced substitution of any path differs from the reduced path itself
by an element of the normal closure of the relators. -/
theorem erasePath_red_pathSubst_mul_reverse_mem (P : Presentation V) (D : TietzeData P) {x y : V}
    (p : Quiver.Path x y) :
    (⟨pmul (DelV.erasePath D.K x (red (D.pathSubst.mapPath p))) (red p).reverse,
      pmul_isReduced _ _⟩ : VertexGroup x) ∈ P.relatorNormalClosure x := by
  induction p with
  | nil =>
      have hx : (⟨pmul (DelV.erasePath D.K x (red (D.pathSubst.mapPath
            (Quiver.Path.nil : Quiver.Path x x))))
          (red (Quiver.Path.nil : Quiver.Path x x)).reverse, pmul_isReduced _ _⟩ :
            VertexGroup x) = (1 : VertexGroup x) := by
        apply Subtype.ext
        show pmul (DelV.erasePath D.K x (red (D.pathSubst.mapPath
            (Quiver.Path.nil : Quiver.Path x x))))
          (red (Quiver.Path.nil : Quiver.Path x x)).reverse = (Quiver.Path.nil : Quiver.Path x x)
        rw [PathSubst.mapPath_nil, red_dnil, DelV.erasePath_nil]
        exact ((pmul_red_left (Quiver.Path.nil : Quiver.Path x x)
            ((red (Quiver.Path.nil : Quiver.Path x x)).reverse)).symm).trans
          (pmul_reverse (red (Quiver.Path.nil : Quiver.Path x x)))
      rw [hx]
      exact Subgroup.one_mem (P.relatorNormalClosure x)
  | cons q e ih =>
      have h2 : red (D.pathSubst.mapPath (q.cons e))
          = pmul (red (D.pathSubst.mapPath q)) (red (D.substArrow (Quiver.Total.mk _ _ e))) := by
        rw [PathSubst.mapPath_cons, TietzeData.pathSubst_mapArrow]
        exact red_comp _ _
      rw [h2, DelV.erasePath_pmul, red_cons q e]
      exact pmul_mem_relatorNormalClosure_of_mem P _ _ _ _ ih
        (erasePath_red_substArrow_mul_reverse_mem P D (Quiver.Total.mk _ _ e))

/-! ## The target -/

theorem delEraseVG_vertexHom_mul_inv_mem {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Work.ORLocInd.Howie.Presentation V) (D : Work.ORLocInd.Howie.TietzeData P) (x : V)
    (b : Work.ORLocInd.Howie.VertexGroup x) :
    Work.ORLocInd.Howie.delEraseVG D.K x (D.pathSubst.vertexHom x b) * b⁻¹ ∈ P.relatorNormalClosure x := by
  have h := erasePath_red_pathSubst_mul_reverse_mem P D b.1
  have hx : (⟨pmul (DelV.erasePath D.K x (red (D.pathSubst.mapPath b.1))) b.1.reverse,
        pmul_isReduced _ _⟩ : VertexGroup x)
      = (⟨pmul (DelV.erasePath D.K x (red (D.pathSubst.mapPath b.1))) (red b.1).reverse,
          pmul_isReduced _ _⟩ : VertexGroup x) := by
    apply Subtype.ext
    show pmul (DelV.erasePath D.K x (red (D.pathSubst.mapPath b.1))) b.1.reverse
      = pmul (DelV.erasePath D.K x (red (D.pathSubst.mapPath b.1))) (red b.1).reverse
    rw [red_eq_self b.2]
  have hmem : (⟨pmul (DelV.erasePath D.K x (red (D.pathSubst.mapPath b.1))) b.1.reverse,
      pmul_isReduced _ _⟩ : VertexGroup x) ∈ P.relatorNormalClosure x := by
    rw [hx]
    exact h
  have hgoal : (delEraseVG D.K x (D.pathSubst.vertexHom x b) * b⁻¹)
      = (⟨pmul (DelV.erasePath D.K x (red (D.pathSubst.mapPath b.1))) b.1.reverse,
          pmul_isReduced _ _⟩ : VertexGroup x) := by
    apply Subtype.ext
    show (delEraseVG D.K x (D.pathSubst.vertexHom x b) * b⁻¹).1
      = pmul (DelV.erasePath D.K x (red (D.pathSubst.mapPath b.1))) b.1.reverse
    rw [VertexGroup.coe_mul, VertexGroup.coe_inv, delEraseVG_apply, PathSubst.vertexHom_apply]
  rw [hgoal]
  exact hmem

end Work.L4
