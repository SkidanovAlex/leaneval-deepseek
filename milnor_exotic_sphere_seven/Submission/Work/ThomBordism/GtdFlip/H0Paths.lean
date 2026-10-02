import Mathlib
import Submission.Work.Thom.chartCoeffAux
import Submission.Work.Cohomology.h0Evaluation
import Submission.Work.Cohomology.linSimplex_boundary

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false

/-!
# Degree-zero cohomology is constant along paths

In the singular cochain model, a class `c ∈ H⁰(Y;ℤ)` is a `0`-cocycle, i.e. a function on the
`0`-simplices of the singular simplicial set of `Y` which is constant on the faces of every
`1`-simplex.  A `1`-simplex of the singular simplicial set is a path, so `c` is constant along
paths: this file proves that the point evaluations `Work.Thom.ptEv · c` agree at the endpoints of
every path, and the underlying simplicial-cocycle statement.

* `Work.ThomBordism.GtdFlip.h0Ev_eq_of_edge` — a degree-zero cocycle is constant along edges;
* `Work.ThomBordism.GtdFlip.ptEv_eq_of_path` — the point evaluation of a class of `H⁰(Y;ℤ)` is
  constant along paths.
-/

namespace Work.ThomBordism.GtdFlip

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

noncomputable section

/-- **A degree-zero cocycle of the singular complex is constant along edges.**  If `α` is a
`0`-cocycle on the singular simplicial set of `Y` and `e` is an edge from the vertex `s` to the
vertex `t`, then `α` takes the same value at `s` and at `t`.  This is the cocycle condition for the
boundary `∂e = t - s` of the edge, computed with `Work.Cohomology.chainComplex_d_ι_apply`. -/
theorem h0Ev_eq_of_edge {Y : Type} [TopologicalSpace Y] (c : Work.Thom.Coh ℤ 0 Y)
    {s t : (TopCat.toSSet.obj (TopCat.of Y)).obj (Opposite.op (SimplexCategory.mk 0))}
    (e : SSet.Edge s t) :
    Work.Cohomology.h0Ev (TopCat.toSSet.obj (TopCat.of Y)) s c
      = Work.Cohomology.h0Ev (TopCat.toSSet.obj (TopCat.of Y)) t c := by
  obtain ⟨α, hα, hc⟩ := Work.Cohomology.exists_cohomologyClassOf ℤ
    (TopCat.toSSet.obj (TopCat.of Y)) 0 c
  rw [← hc, Work.Cohomology.h0Ev_classOf, Work.Cohomology.h0Ev_classOf]
  have h0 : α ((((TopCat.toSSet.obj (TopCat.of Y)).chainComplex (ModuleCat.of ℤ ℤ)).d 1 0)
      ((((TopCat.toSSet.obj (TopCat.of Y)).ιChainComplex (R := ModuleCat.of ℤ ℤ)) e.edge).hom 1))
      = 0 := by
    rw [← Work.Cohomology.cochainDiff_apply ℤ _ α e.edge, hα]
    rfl
  rw [Work.Cohomology.chainComplex_d_ι_apply] at h0
  rw [map_sum, Fin.sum_univ_two] at h0
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_one_zsmul] at h0
  rw [map_neg, e.tgt_eq, e.src_eq] at h0
  have h1 : α (((TopCat.toSSet.obj (TopCat.of Y)).ιChainComplex
        (R := ModuleCat.of ℤ ℤ) s).hom 1)
      = α (((TopCat.toSSet.obj (TopCat.of Y)).ιChainComplex
        (R := ModuleCat.of ℤ ℤ) t).hom 1) := by
    linarith
  exact h1

/-- **The point evaluation of a class of `H⁰(Y;ℤ)` is constant along paths.**  A path in `Y`
between `x` and `y` is an edge of the singular simplicial set between the corresponding vertices,
and a degree-zero class is constant along edges. -/
theorem ptEv_eq_of_path {Y : Type} [TopologicalSpace Y] (c : Work.Thom.Coh ℤ 0 Y)
    {x y : Y} (p : Path x y) : Work.Thom.ptEv x c = Work.Thom.ptEv y c := by
  have e : SSet.Edge ((TopCat.toSSetObj₀Equiv (X := TopCat.of Y)).symm x)
      ((TopCat.toSSetObj₀Equiv (X := TopCat.of Y)).symm y) :=
    TopCat.toSSetObjEdgeEquiv.symm (TopCat.pathEquiv (X := TopCat.of Y) |>.symm p)
  have h := h0Ev_eq_of_edge c e
  rw [Work.Thom.ptEv_apply, Work.Thom.ptEv_apply]
  exact h

end

end Work.ThomBordism.GtdFlip
