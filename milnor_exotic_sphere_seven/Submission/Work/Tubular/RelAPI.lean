import Submission.Work.Tubular.relKronecker_chain
import Submission.Work.Cohomology.relCapH

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Two convenience lemmas for the relative Kronecker pairing

`Work.Tubular.relKronH` (`Submission/Work/Tubular/relKronecker_chain.lean`) computes its value on the
classes of a relative cocycle `α` and of a relative cycle `cc` by evaluating the underlying cochain
`α.1` on *any* chain `z` whose class in `C_*(X,A)` is the image of `cc` — the hypothesis of
`Work.Tubular.relKronH_apply` is phrased through the degreewise cokernel projection
`cokernel.π ((inclChains X A).f n)` and the comparison isomorphism `relChains_cokernelIso`.

In practice one produces such a lift `z` by lifting the *cycle* itself, i.e. by solving
`relDualProj X A n z = iCycles n cc` (`relDualProj_surjective`).  This module records the two
lemmas that make this usable:

* **`Work.Tubular.relKronH_apply_of_relDualProj`** — `relKronH_apply` with the hypothesis in the
  `relDualProj` form;
* **`Work.Tubular.relDualProj_d_eq_zero_of_cycle_lift`** — the boundary of such a lift is supported
  in `A`, i.e. the lift satisfies the hypothesis `hz` of
  `Work.Tubular.kronecker_cap_cup_comm_rel`.

Both were reviewed and found correctly stated (they are short corollaries of
`relDualProj_comm_lm`, `relChains_cokernelIso_canon_apply` and `HomologicalComplex.iCycles_d`, but
they are the two facts every local computation of the chapter starts from).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Tubular

noncomputable section

open Work.Cohomology

variable {X : TopCat} {A : Set X}

/-- **The boundary of a lift of a relative cycle is supported in `A`.**  If `z` lifts the relative
cycle `cc` (i.e. `relDualProj z = iCycles cc`), then `∂z` has trivial image in `C_{n}(X,A)`, i.e. is
supported in `A` — which is exactly the hypothesis under which
`Work.Tubular.kronecker_cap_cup_comm_rel` applies to `z`. -/
theorem relDualProj_d_eq_zero_of_cycle_lift (n : ℕ)
    (z : (singularChains ℤ X).X (n + 1)) (cc : (relChains X A).cycles (n + 1))
    (hz : relDualProj X A (n + 1) z = ((relChains X A).iCycles (n + 1)) cc) :
    relDualProj X A n (((singularChains ℤ X).d (n + 1) n).hom z) = 0 := by
  have hcomm := LinearMap.congr_fun (relDualProj_comm_lm X A n) z
  simp only [LinearMap.comp_apply] at hcomm
  rw [← hcomm, hz]
  have h := congrArg
    (fun (g : (relChains X A).cycles (n + 1) ⟶ (relChains X A).X n) => g.hom cc)
    (HomologicalComplex.iCycles_d (relChains X A) (n + 1) n)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] using h

/-- **`relKronH_apply` with the lift condition in the `relDualProj` form.**  If `z` lifts the relative
cycle `cc`, then the relative Kronecker pairing of the class of a relative cocycle `α` with the class
of `cc` is the evaluation of `α.1` on `z`. -/
theorem relKronH_apply_of_relDualProj (n : ℕ)
    (α : relKern ℤ X A n) (hα : relDiffLM ℤ X A n α = 0)
    (cc : (relChains X A).cycles n) (z : (singularChains ℤ X).X n)
    (hz : relDualProj X A n z = ((relChains X A).iCycles n) cc) :
    relKronH X A n (relClassOf ℤ X A α hα)
        ((HomologicalComplex.homologyπ (relChains X A) n).hom cc)
      = kronecker ℤ (TopCat.toSSet.obj X) α.1 z := by
  refine relKronH_apply X A n α hα cc z ?_
  have hstep := relChains_cokernelIso_canon_apply X A n z
  rw [← hstep]
  exact congrArg (fun (w : (relChains X A).X n) => (relChains_cokernelIso X A n).hom w) hz

end

end Work.Tubular
