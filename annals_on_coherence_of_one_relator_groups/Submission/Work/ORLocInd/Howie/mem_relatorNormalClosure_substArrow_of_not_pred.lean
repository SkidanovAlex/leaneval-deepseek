/-
# The non-kept arrows of the Tietze elimination lie in the relator normal closure

Given the Tietze data `D` of Howie's Case 2 (`TietzeData`, see `TietzeSupport.lean`), the deleted
arrow pair `{f, f⁻¹}` consists exactly of the distinguished arrow `g` of the relator `i₀` and its
reverse (`D.hK` and `D.hsep`).  The present file computes, for such an arrow `e` (`¬ D.K.pred e`),
the element of the free-groupoid vertex group

`⟨e · (substArrow e)⁻¹, _⟩ ∈ VertexGroup e.left`

(where `substArrow e` is the substitution of `e`, a path of the arrow-deleted graph, erased back to
`Γ`): it is a *conjugate of the relator `i₀` or of its inverse*, and hence lies in the normal closure
`P.relatorNormalClosure e.left` of the relators.

More precisely:

* if `e = D.g` then the element is `conjPathHom D.q₁.reverse` of the relator, i.e. the conjugate of
  `P.path i₀` by the path `q₁⁻¹` (the relator `i₀` is `q₁ · g · q₂` and `g = q₁⁻¹ · q₂⁻¹`);
* if `e = D.g⁻¹` then the element is `conjPathHom D.q₂` of the inverse relator, i.e. the conjugate
  of `(P.path i₀)⁻¹` by the path `q₂`.

This is the single-arrow case of `delEraseVG_substVG_cong` (`vertexGroup_eliminate.lean`), and the
path bookkeeping it needs (`DelV.erasePath_restrictPath`, the two evaluations `herase`, `hkey`,
`hkey2` below) is the content of the file.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.Delete
import Submission.Work.ORLocInd.Howie.TietzeSupport
import Submission.Work.ORLocInd.Howie.L4.SubstSupport
import Submission.Work.ORLocInd.Howie.conjPathHom_mem_relatorNormalClosure
import Submission.Work.ORLocInd.Howie.LoopAux

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORLocInd.Howie

open Quiver

variable {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-! ## Path bookkeeping for the erasure of a restricted path -/

/-- The erasure of the restriction of a path to the arrow-deleted graph is the path itself. -/
theorem DelV.erasePath_restrictPath (K : Keep V) (a : V) {b : V} (p : Quiver.Path a b)
    (h : ∀ f ∈ Quiver.Path.arrowList p, K.pred f) :
    DelV.erasePath K a (restrictPath K a p h) = p := by
  rw [← DelV.erasePath_eq_mapPath K (p := restrictPath K a p h)]
  exact inclPath_restrictPath K a p h

/-- `DelV.erasePath_reverse` with the two vertices explicit.

The implicit arguments of `DelV.erasePath_reverse` are inferred by unification against the target;
when the two vertices are known only up to definitional equality (`(Quiver.totalReverse e).left`
against `e.right`), the unifier may insert a cast in the vertex argument, which then prevents later
rewrites from firing.  Passing the vertices explicitly avoids this. -/
theorem DelV.erasePath_reverse_explicit (K : Keep V) (a b : V)
    (p : @Quiver.Path (DelV K) (instDelQuiver K) a b) :
    DelV.erasePath K b p.reverse = (DelV.erasePath K a p).reverse :=
  DelV.erasePath_reverse K p

/-! ## The lemma -/

theorem mem_relatorNormalClosure_substArrow_of_not_pred {V : Type*} [Quiver V]
    [Quiver.HasInvolutiveReverse V] {P : Work.ORLocInd.Howie.Presentation V}
    (D : Work.ORLocInd.Howie.TietzeData P) {e : Quiver.Total V} (h : ¬ D.K.pred e) :
    (⟨Work.ORLocInd.Howie.pmul (Quiver.Hom.toPath e.hom)
        (Work.ORLocInd.Howie.DelV.erasePath D.K e.left (D.substArrow e)).reverse,
      Work.ORLocInd.Howie.pmul_isReduced _ _⟩ :
      Work.ORLocInd.Howie.VertexGroup e.left) ∈ P.relatorNormalClosure e.left := by
  -- 1. `e` is the distinguished arrow `g` or its reverse.
  have hc : P.edgeOf e = P.edgeOf D.f := by
    by_contra hne
    exact h ((D.hK e).mpr hne)
  have hgs : P.edgeOf e = P.edgeOf D.g := hc.trans D.code.symm
  -- 2. The erasure of `D.phi = q₁⁻¹ · q₂⁻¹`.
  have herase : DelV.erasePath D.K D.g.left D.phi = pmul D.q₁.reverse D.q₂.reverse := by
    rw [show D.phi = pmul (dreverse (restrictPath D.K (P.base D.i₀) D.q₁ D.keep₁))
        (dreverse (restrictPath D.K D.g.right D.q₂ D.keep₂)) from rfl,
      DelV.erasePath_pmul, DelV.erasePath_reverse, DelV.erasePath_reverse,
      DelV.erasePath_restrictPath, DelV.erasePath_restrictPath]
  -- 3. The relator `i₀` itself lies in the normal closure.
  have hR : (⟨P.path D.i₀, P.reduced D.i₀⟩ : VertexGroup (P.base D.i₀))
      ∈ P.relatorNormalClosure (P.base D.i₀) := by
    have hnil : (Quiver.Path.nil : Quiver.Path (P.base D.i₀) (P.base D.i₀)).reverse
        = Quiver.Path.nil := rfl
    refine Subgroup.subset_normalClosure ⟨D.i₀, Quiver.Path.nil, ?_, ?_⟩
    · exact Quiver.Path.IsReduced.nil _
    · apply Subtype.ext
      show P.path D.i₀ = pmul (Quiver.Path.nil : Quiver.Path (P.base D.i₀) (P.base D.i₀))
          (pmul (P.path D.i₀) (Quiver.Path.nil : Quiver.Path (P.base D.i₀) (P.base D.i₀)).reverse)
      rw [hnil, pmul_nil_right, pmul_nil_left]
      exact ((red_eq_self (isReduced_red (P.path D.i₀))).trans (red_eq_self (P.reduced D.i₀))).symm
  rcases D.hsep e D.g hgs with heq | heq
  · -- Case `e = g`: the element is the conjugate of the relator by `q₁⁻¹`.
    subst heq
    rw [D.substArrow_g, herase]
    have hkey : pmul (Quiver.Hom.toPath D.g.hom) D.q₂ = pmul D.q₁.reverse (P.path D.i₀) := by
      rw [D.split]
      exact (pmul_rev_mul D.q₁ ((Quiver.Hom.toPath D.g.hom).comp D.q₂)).symm.trans
        (pmul_red_right D.q₁.reverse (D.q₁.comp ((Quiver.Hom.toPath D.g.hom).comp D.q₂)))
    have heqel : (⟨pmul (Quiver.Hom.toPath D.g.hom) (pmul D.q₁.reverse D.q₂.reverse).reverse,
        pmul_isReduced _ _⟩ : VertexGroup D.g.left)
        = conjPathHom D.q₁.reverse (⟨P.path D.i₀, P.reduced D.i₀⟩ : VertexGroup (P.base D.i₀)) := by
      apply Subtype.ext
      show pmul (Quiver.Hom.toPath D.g.hom) (pmul D.q₁.reverse D.q₂.reverse).reverse
        = pmul (pmul D.q₁.reverse (P.path D.i₀)) (D.q₁.reverse).reverse
      rw [Quiver.Path.reverse_reverse, pmul_reverse_comp,
        Quiver.Path.reverse_reverse, Quiver.Path.reverse_reverse, ← pmul_assoc]
      exact congrArg (fun z => pmul z D.q₁) hkey
    rw [heqel]
    exact conjPathHom_mem_relatorNormalClosure P D.q₁.reverse hR
  · -- Case `e = g⁻¹`: the element is the conjugate of the inverse relator by `q₂`.
    subst heq
    have h1 : D.substArrow (Quiver.totalReverse D.g) = D.phi.reverse := D.substArrow_reverse_g
    have h2 : DelV.erasePath D.K (Quiver.totalReverse D.g).left (D.phi.reverse)
        = (pmul D.q₁.reverse D.q₂.reverse).reverse :=
      (DelV.erasePath_reverse_explicit D.K D.g.left (Quiver.totalReverse D.g).left D.phi).trans
        (congrArg Quiver.Path.reverse herase)
    have hstep : (⟨pmul (Quiver.Hom.toPath (Quiver.totalReverse D.g).hom)
          (DelV.erasePath D.K (Quiver.totalReverse D.g).left
            (D.substArrow (Quiver.totalReverse D.g))).reverse,
        pmul_isReduced _ _⟩ : VertexGroup (Quiver.totalReverse D.g).left)
        = (⟨pmul (Quiver.Hom.toPath D.g.hom).reverse (pmul D.q₁.reverse D.q₂.reverse),
          pmul_isReduced _ _⟩ : VertexGroup (Quiver.totalReverse D.g).left) := by
      apply Subtype.ext
      show pmul (Quiver.Hom.toPath (Quiver.totalReverse D.g).hom)
          (DelV.erasePath D.K (Quiver.totalReverse D.g).left
            (D.substArrow (Quiver.totalReverse D.g))).reverse
        = pmul (Quiver.Hom.toPath D.g.hom).reverse (pmul D.q₁.reverse D.q₂.reverse)
      rw [h1, h2, Quiver.Path.reverse_reverse]
      rfl
    have hkey2 : pmul D.q₂ (P.path D.i₀).reverse
        = pmul (Quiver.Hom.toPath D.g.hom).reverse D.q₁.reverse := by
      rw [D.split, Quiver.Path.reverse_comp, Quiver.Path.reverse_comp, Quiver.Path.comp_assoc]
      refine (pmul_red_right D.q₂ (D.q₂.reverse.comp
        ((Quiver.Hom.toPath D.g.hom).reverse.comp D.q₁.reverse))).symm.trans ?_
      refine (pmul_assoc D.q₂ D.q₂.reverse
        ((Quiver.Hom.toPath D.g.hom).reverse.comp D.q₁.reverse)).symm.trans ?_
      exact (congrArg (fun z => pmul z ((Quiver.Hom.toPath D.g.hom).reverse.comp D.q₁.reverse))
        (pmul_reverse D.q₂)).trans (pmul_nil_left _)
    have hgoal : (⟨pmul (Quiver.Hom.toPath D.g.hom).reverse (pmul D.q₁.reverse D.q₂.reverse),
        pmul_isReduced _ _⟩ : VertexGroup (Quiver.totalReverse D.g).left)
        ∈ P.relatorNormalClosure (Quiver.totalReverse D.g).left := by
      have heqel : (⟨pmul (Quiver.Hom.toPath D.g.hom).reverse (pmul D.q₁.reverse D.q₂.reverse),
          pmul_isReduced _ _⟩ : VertexGroup (Quiver.totalReverse D.g).left)
          = conjPathHom D.q₂ (⟨P.path D.i₀, P.reduced D.i₀⟩ : VertexGroup (P.base D.i₀))⁻¹ := by
        apply Subtype.ext
        show pmul (Quiver.Hom.toPath D.g.hom).reverse (pmul D.q₁.reverse D.q₂.reverse)
          = pmul (pmul D.q₂ (P.path D.i₀).reverse) D.q₂.reverse
        rw [← pmul_assoc]
        exact congrArg (fun z => pmul z D.q₂.reverse) hkey2.symm
      rw [heqel]
      exact conjPathHom_mem_relatorNormalClosure P D.q₂
        (Subgroup.inv_mem (P.relatorNormalClosure (P.base D.i₀)) hR)
    exact hstep ▸ hgoal

end Work.ORLocInd.Howie
