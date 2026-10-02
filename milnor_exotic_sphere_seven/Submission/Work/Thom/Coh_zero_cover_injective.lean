import Mathlib
import Submission.Work.Thom.Cohomology
import Submission.Work.Thom.Pair
import Submission.Work.Thom.isOrientedOver_of_det_pos

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

/-!
# `H⁰` is detected on an open cover

For a topological space `X` and a family `V : Fin N → Set X` of subsets whose union is all of `X`,
a degree-zero cohomology class `x ∈ H⁰(X; ℤ)` which restricts to `0` on every `V j` is itself `0`.

In the singular model used throughout the Thom chapter, `H⁰(X;ℤ)` is the group of locally constant
functions (with values in `ℤ`) on `X`: a class is determined by its evaluations `h0Ev X s x` at the
`0`-simplices `s` of the singular simplicial set of `X`, i.e. by its values at the points of `X`.
If `x` restricts to `0` on each member `V j` of a cover, then all these values vanish — a point `p`
lies in some `V j`, and the `0`-simplex of `V j` sitting over `p` realises the evaluation of `x` at
`p` as the evaluation of `x|_{V j}`, which is `0`.  Since the evaluations jointly separate classes,
`x = 0`.

This is the elementary observation underlying the "Mayer–Vietoris/cover" arguments used when a class
of the chapter is shown to vanish after restriction to the pieces of a cover.
-/

namespace Work.Thom

open CategoryTheory

/-- The degree-zero evaluations `h0Ev` jointly separate cohomology classes: two classes of `H⁰(X;ℤ)`
which evaluate equally at every `0`-simplex of the singular simplicial set of `X` are equal. -/
theorem h0Ev_ext {X : Type} [TopologicalSpace X] {x y : Coh ℤ 0 X}
    (h : ∀ s : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk 0)),
      Work.Cohomology.h0Ev (TopCat.toSSet.obj (TopCat.of X)) s x
        = Work.Cohomology.h0Ev (TopCat.toSSet.obj (TopCat.of X)) s y) : x = y := by
  obtain ⟨α, hα, hx⟩ := Work.Cohomology.exists_cohomologyClassOf ℤ
    (TopCat.toSSet.obj (TopCat.of X)) 0 x
  obtain ⟨β, hβ, hy⟩ := Work.Cohomology.exists_cohomologyClassOf ℤ
    (TopCat.toSSet.obj (TopCat.of X)) 0 y
  rw [← hx, ← hy]
  apply Work.Cohomology.cohomologyClassOf_congr
  apply Work.Cohomology.genEval_ext
  intro s
  have hs := h s
  rw [← hx, ← hy, Work.Cohomology.h0Ev_classOf, Work.Cohomology.h0Ev_classOf] at hs
  simpa [Work.Cohomology.genEval, Work.Cohomology.h0Gen] using hs

/-- A degree-zero cohomology class all of whose evaluations at `0`-simplices vanish is zero. -/
theorem h0Ev_eq_zero {X : Type} [TopologicalSpace X] (y : Coh ℤ 0 X)
    (hy : ∀ s : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk 0)),
      Work.Cohomology.h0Ev (TopCat.toSSet.obj (TopCat.of X)) s y = 0) : y = 0 := by
  refine h0Ev_ext (y := 0) (fun s => ?_)
  rw [hy s]
  exact (map_zero (Work.Cohomology.h0Ev (TopCat.toSSet.obj (TopCat.of X)) s)).symm

/-- **A class of `H⁰` killed by restriction to the members of a cover is zero.** -/
theorem Coh_zero_cover_injective
    {X : Type} [TopologicalSpace X] {N : ℕ} (V : Fin N → Set X) (hV : ∀ j, IsOpen (V j))
    (hcov : ∀ x : X, ∃ j, x ∈ V j) (x : Work.Thom.Coh ℤ 0 X)
    (h : ∀ j, (Work.Thom.CohMap (Work.Thom.subtypeMap (V j)) ℤ 0).hom x = 0) : x = 0 := by
  refine h0Ev_eq_zero x (fun s => ?_)
  -- the point underlying the `0`-simplex `s`, and a member of the cover containing it
  set p : X := TopCat.toSSetObj₀Equiv s with hp
  obtain ⟨j, hpj⟩ := hcov p
  -- the `0`-simplex of `V j` lying over `p`
  set s' : (TopCat.toSSet.obj (TopCat.of ↥(V j))).obj (Opposite.op (SimplexCategory.mk 0)) :=
    TopCat.toSSetObj₀Equiv.symm (⟨p, hpj⟩ : ↥(V j)) with hs'
  -- it is mapped to `s` by the inclusion `V j ↪ X`
  have himg : (ConcreteCategory.hom ((TopCat.toSSet.map (TopCat.ofHom (subtypeMap (V j)))).app
      (Opposite.op (SimplexCategory.mk 0)))) s' = s := by
    apply TopCat.toSSetObj₀Equiv.injective
    rw [toSSetObj₀Equiv_map]
    rw [hs', Equiv.apply_symm_apply]
    exact hp
  -- naturality of the evaluation, and the hypothesis that `x` restricts to `0` on `V j`
  have hnat := h0Ev_pullback (subtypeMap (V j)) s' x
  rw [h j, map_zero] at hnat
  rw [himg] at hnat
  exact hnat.symm

end Work.Thom
