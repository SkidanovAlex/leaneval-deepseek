import Mathlib
import Submission.Work.Thom.chartCoeffAux
import Submission.Work.Cohomology.linSimplex_boundary

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The sign of a nowhere-vanishing degree-zero class

Let `W` be a topological space and `c ∈ H⁰(W; ℤ)` a degree-zero cohomology class whose evaluation
`Work.Thom.ptEv p c` at every point `p` is non-zero.  In the singular model, `H⁰(W;ℤ)` is the group
of locally constant `ℤ`-valued functions on `W` (`Work.Thom.ptEv` evaluates such a function at a
point, and `Work.Thom.ptEv_cup` says that the evaluation is multiplicative), so the *sign* of `c`
is again a degree-zero class: the function `p ↦ Int.sign (ptEv p c)` is locally constant because
`ptEv · c` is.

This module constructs that class explicitly on the singular cochains of `W`:

* `Work.ThomBordism.h0Sign_genEval_eq_of_edge` — a `0`-cocycle is constant along edges;
* `Work.ThomBordism.h0Sign_signFun` — the function on `π₀` given by the sign of the values of a
  `0`-cocycle (well defined by the previous point);
* `Work.ThomBordism.h0Sign_signMor` / `h0Sign_signCochain` — the `0`-cochain obtained by pulling
  the sign function back along `π₀` (it is a cocycle by construction,
  `h0Sign_signCochain_cocycle`);
* `Work.ThomBordism.h0Sign_h0Ev_signCochain` — its value at a point is the sign of the value of the
  original cocycle.

The main result `Work.ThomBordism.h0SignUnit` is the requested statement: for a nowhere-vanishing
`c` there is a degree-zero class `s` with `s ⌣ s = 1` pointwise and `s ⌣ c = |c|` pointwise.
-/

namespace Work.ThomBordism

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

noncomputable section

open Work.Cohomology

/-- **A `0`-cocycle is constant along edges.**  If `α` is a degree-zero cocycle on a simplicial set
`X` and `e` is an edge from `x` to `y`, then `α` takes the same value at `x` and at `y`: this is the
cocycle condition for the boundary `∂e = y - x` of the edge, computed with
`Work.Cohomology.chainComplex_d_ι_apply`. -/
theorem h0Sign_genEval_eq_of_edge {X : SSet} {α : Work.Cohomology.Cochain ℤ X 0}
    (hα : Work.Cohomology.cochainDiff ℤ X α = 0) {x y : X _⦋0⦌} (e : SSet.Edge x y) :
    Work.Cohomology.genEval ℤ X α x = Work.Cohomology.genEval ℤ X α y := by
  have h0 : α (((X.chainComplex (ModuleCat.of ℤ ℤ)).d 1 0)
      (((X.ιChainComplex (R := ModuleCat.of ℤ ℤ)) e.edge).hom 1)) = 0 := by
    rw [← Work.Cohomology.cochainDiff_apply ℤ X α e.edge, hα]
    rfl
  rw [Work.Cohomology.chainComplex_d_ι_apply] at h0
  rw [map_sum, Fin.sum_univ_two] at h0
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_one_zsmul] at h0
  rw [map_neg, e.tgt_eq, e.src_eq] at h0
  have h1 : α ((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) x).hom 1)
      = α ((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) y).hom 1) := by linarith
  exact h1

/-- **The sign of the values of a `0`-cocycle**, as a function on the connected components of `X`.
Well defined because the cocycle is constant along edges (`h0Sign_genEval_eq_of_edge`). -/
noncomputable def h0Sign_signFun (Y : SSet) (α : Work.Cohomology.Cochain ℤ Y 0)
    (hα : Work.Cohomology.cochainDiff ℤ Y α = 0) : SSet.π₀ Y → ℤ :=
  SSet.π₀.lift (fun x => Int.sign (Work.Cohomology.genEval ℤ Y α x))
    (fun x₀ x₁ e => by rw [h0Sign_genEval_eq_of_edge hα e])

/-- The defining property of `h0Sign_signFun` on the component of a `0`-simplex. -/
theorem h0Sign_signFun_mk (Y : SSet) (α : Work.Cohomology.Cochain ℤ Y 0)
    (hα : Work.Cohomology.cochainDiff ℤ Y α = 0) (σ : Y _⦋0⦌) :
    h0Sign_signFun Y α hα (SSet.π₀.mk σ)
      = Int.sign (Work.Cohomology.genEval ℤ Y α σ) := rfl

/-- The **sign cochain** of a `0`-cocycle `α`: the `0`-cochain which is `Int.sign (α σ)` on the
`0`-simplices of the component of `σ`.  It is defined by pulling the sign function back along
`π₀`, so that the cocycle condition is automatic. -/
noncomputable def h0Sign_signMor (Y : SSet) (α : Work.Cohomology.Cochain ℤ Y 0)
    (hα : Work.Cohomology.cochainDiff ℤ Y α = 0) :
    (Y.chainComplex (ModuleCat.of ℤ ℤ)).X 0 ⟶ ModuleCat.of ℤ ℤ :=
  SSet.π₀.fromChainComplexXZero Y (ModuleCat.of ℤ ℤ) ≫
    Sigma.desc
      (fun d => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ℤ (h0Sign_signFun Y α hα d)))

/-- The sign cochain, as an element of the degree-zero cochains. -/
noncomputable def h0Sign_signCochain (Y : SSet) (α : Work.Cohomology.Cochain ℤ Y 0)
    (hα : Work.Cohomology.cochainDiff ℤ Y α = 0) : Work.Cohomology.Cochain ℤ Y 0 :=
  (h0Sign_signMor Y α hα).hom

/-- **The sign cochain is a cocycle**, because it factors through `π₀` and the differential
`d₁` vanishes after `SSet.π₀.fromChainComplexXZero`. -/
theorem h0Sign_signCochain_cocycle (Y : SSet) (α : Work.Cohomology.Cochain ℤ Y 0)
    (hα : Work.Cohomology.cochainDiff ℤ Y α = 0) :
    Work.Cohomology.cochainDiff ℤ Y (h0Sign_signCochain Y α hα) = 0 := by
  have hd : (Y.chainComplex (ModuleCat.of ℤ ℤ)).d 1 0 ≫ h0Sign_signMor Y α hα = 0 := by
    rw [h0Sign_signMor, ← Category.assoc, SSet.π₀.d_fromChainComplexXZero, zero_comp]
  have h := congrArg ModuleCat.Hom.hom hd
  simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
  rw [← h]
  rfl

/-- The value of the sign cochain on a `0`-simplex is the sign of the value of `α`. -/
theorem h0Sign_signCochain_genEval (Y : SSet) (α : Work.Cohomology.Cochain ℤ Y 0)
    (hα : Work.Cohomology.cochainDiff ℤ Y α = 0) (σ : Y _⦋0⦌) :
    Work.Cohomology.genEval ℤ Y (h0Sign_signCochain Y α hα) σ
      = Int.sign (Work.Cohomology.genEval ℤ Y α σ) := by
  have key : Y.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ ≫ h0Sign_signMor Y α hα =
      ModuleCat.ofHom
        (LinearMap.toSpanSingleton ℤ ℤ (h0Sign_signFun Y α hα (SSet.π₀.mk σ))) := by
    rw [h0Sign_signMor, ← Category.assoc, SSet.π₀.comp_fromChainComplexXZero, Sigma.ι_desc]
  have h := congrArg ModuleCat.Hom.hom key
  rw [ModuleCat.hom_comp, ModuleCat.hom_ofHom] at h
  have h1 := LinearMap.congr_fun h 1
  rw [LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, smul_eq_mul, one_mul] at h1
  exact h1.trans (show h0Sign_signFun Y α hα (SSet.π₀.mk σ)
      = Int.sign (Work.Cohomology.genEval ℤ Y α σ) from rfl)

/-- **The signed class evaluates to the sign of the value of the class**: for a `0`-cocycle `α`,
the class of the sign cochain takes at every `0`-simplex the value `Int.sign (α σ)`. -/
theorem h0Sign_h0Ev_signCochain (Y : SSet) (α : Work.Cohomology.Cochain ℤ Y 0)
    (hα : Work.Cohomology.cochainDiff ℤ Y α = 0) (σ : Y _⦋0⦌) :
    Work.Cohomology.h0Ev Y σ
        (Work.Cohomology.cohomologyClassOf ℤ Y (h0Sign_signCochain Y α hα)
          (h0Sign_signCochain_cocycle Y α hα))
      = Int.sign (Work.Cohomology.h0Ev Y σ (Work.Cohomology.cohomologyClassOf ℤ Y α hα)) := by
  rw [Work.Cohomology.h0Ev_classOf, Work.Cohomology.h0Ev_classOf]
  show Work.Cohomology.genEval ℤ Y (h0Sign_signCochain Y α hα) σ
      = Int.sign (Work.Cohomology.genEval ℤ Y α σ)
  rw [h0Sign_signCochain_genEval]

/-- **A nowhere-vanishing degree-zero class admits a sign class.**  For `c ∈ H⁰(W;ℤ)` with
`ptEv p c ≠ 0` for every `p`, there is `s ∈ H⁰(W;ℤ)` with `ptEv p (s ⌣ s) = 1` and
`ptEv p (s ⌣ c) = |ptEv p c|` for every `p`. -/
theorem h0SignUnit {W : Type} [TopologicalSpace W] (c : Work.Thom.Coh ℤ 0 W)
    (hc : ∀ p : W, Work.Thom.ptEv p c ≠ 0) :
    ∃ s : Work.Thom.Coh ℤ 0 W,
      (∀ p : W, Work.Thom.ptEv p
        ((Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of W)) 0 0) s s) = 1) ∧
      (∀ p : W, Work.Thom.ptEv p
        ((Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of W)) 0 0) s c)
        = (Work.Thom.ptEv p c).natAbs) := by
  classical
  obtain ⟨α, hα, hcα⟩ := Work.Cohomology.exists_cohomologyClassOf ℤ
    (TopCat.toSSet.obj (TopCat.of W)) 0 c
  let s : Work.Thom.Coh ℤ 0 W := Work.Cohomology.cohomologyClassOf ℤ
    (TopCat.toSSet.obj (TopCat.of W)) (h0Sign_signCochain (TopCat.toSSet.obj (TopCat.of W)) α hα)
    (h0Sign_signCochain_cocycle (TopCat.toSSet.obj (TopCat.of W)) α hα)
  have hs_eq : s = (Work.Cohomology.cohomologyClassOf ℤ
      (TopCat.toSSet.obj (TopCat.of W))
      (h0Sign_signCochain (TopCat.toSSet.obj (TopCat.of W)) α hα)
      (h0Sign_signCochain_cocycle (TopCat.toSSet.obj (TopCat.of W)) α hα)
        : Work.Thom.Coh ℤ 0 W) := rfl
  have hval : ∀ p : W, Work.Thom.ptEv p s = Int.sign (Work.Thom.ptEv p c) := by
    intro p
    have e1 : Work.Thom.ptEv p s = Work.Cohomology.h0Ev (TopCat.toSSet.obj (TopCat.of W))
        ((TopCat.toSSetObj₀Equiv (X := TopCat.of W)).symm p)
        (Work.Cohomology.cohomologyClassOf ℤ (TopCat.toSSet.obj (TopCat.of W))
          (h0Sign_signCochain (TopCat.toSSet.obj (TopCat.of W)) α hα)
          (h0Sign_signCochain_cocycle (TopCat.toSSet.obj (TopCat.of W)) α hα)) :=
      (Work.Thom.ptEv_apply (X := W) p s).trans (congrArg _ hs_eq)
    have e2 : Work.Cohomology.h0Ev (TopCat.toSSet.obj (TopCat.of W))
        ((TopCat.toSSetObj₀Equiv (X := TopCat.of W)).symm p)
        (Work.Cohomology.cohomologyClassOf ℤ (TopCat.toSSet.obj (TopCat.of W))
          (h0Sign_signCochain (TopCat.toSSet.obj (TopCat.of W)) α hα)
          (h0Sign_signCochain_cocycle (TopCat.toSSet.obj (TopCat.of W)) α hα))
        = Int.sign (Work.Cohomology.h0Ev (TopCat.toSSet.obj (TopCat.of W))
            ((TopCat.toSSetObj₀Equiv (X := TopCat.of W)).symm p)
            (Work.Cohomology.cohomologyClassOf ℤ (TopCat.toSSet.obj (TopCat.of W)) α hα)) :=
      h0Sign_h0Ev_signCochain (TopCat.toSSet.obj (TopCat.of W)) α hα _
    have e3 : Work.Cohomology.h0Ev (TopCat.toSSet.obj (TopCat.of W))
        ((TopCat.toSSetObj₀Equiv (X := TopCat.of W)).symm p)
        (Work.Cohomology.cohomologyClassOf ℤ (TopCat.toSSet.obj (TopCat.of W)) α hα)
        = Work.Cohomology.h0Ev (TopCat.toSSet.obj (TopCat.of W))
            ((TopCat.toSSetObj₀Equiv (X := TopCat.of W)).symm p) c :=
      congrArg _ hcα
    have e4 : Work.Cohomology.h0Ev (TopCat.toSSet.obj (TopCat.of W))
        ((TopCat.toSSetObj₀Equiv (X := TopCat.of W)).symm p) c
        = Work.Thom.ptEv p c := (Work.Thom.ptEv_apply (X := W) p c).symm
    exact e1.trans (e2.trans ((congrArg Int.sign e3).trans (congrArg Int.sign e4)))
  refine ⟨s, ?_, ?_⟩
  · intro p
    rw [Work.Thom.ptEv_cup, hval p]
    rcases lt_trichotomy (Work.Thom.ptEv p c) 0 with h | h | h
    · rw [Int.sign_eq_neg_one_of_neg h]; norm_num
    · exact absurd h (hc p)
    · rw [Int.sign_eq_one_of_pos h]; norm_num
  · intro p
    rw [Work.Thom.ptEv_cup, hval p]
    exact Int.sign_mul_self (Work.Thom.ptEv p c)

end

end Work.ThomBordism
