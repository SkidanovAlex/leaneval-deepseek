import Mathlib
import Submission.Work.Whitney.TCMDefs
import Submission.Work.Whitney.tcmModelMul_of_point
import Submission.Work.Thom.naturalModelClass_punct
import Submission.Work.Whitney.Mn_one_eq_pairDelta
import Submission.Work.Whitney.tcmCup_step
import Submission.Work.Whitney.tcmPhiAux
import Submission.Work.Whitney.tcmModelMul_point_zero
import Submission.Work.Whitney.tcmStep_linear
import Submission.Work.Whitney.punctured_generated

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Whitney

open Work.Thom

/-!
# The point case of the signed model product formula, for all ranks `p`, `q`

This is `Work.Whitney.tcmModelMul_point_signed` (the statement is literally the same): over a
subsingleton base `Y`, the relative–relative cup of the two pulled-back model Thom classes of ranks
`p` and `q` is the model class of the sum, with the Koszul sign `(-1)^{p q}`:

  `tcmRelCup (pr₁^* Mpun p) (pr₂^* Mpun q) = (-1)^{p q} • tcmF^* (Mpun (p+q))`.

## The proof, and its single input

The proof is the induction on `q` proposed in the docstring of `Work.Whitney.tcmModelMul_point_signed`:

* **base** `q = 0`: the unit law, `Work.Whitney.tcmModelMul_point_zero` (proved);
* **step**: the recursion `Work.Whitney.tcmCup_step` (proved in `tcmCup_step.lean`), transported
  along the inverse coordinate identification `Fib.tcmF_inv` (the bookkeeping
  `Work.Whitney.phi_injective`, `Work.Whitney.phi_Mpun`, `Work.Whitney.phi_F_pullback` of
  `Submission/Work/Whitney/tcmPhiAux.lean`).

The recursion `tcmCup_step` is the *only* non-formal input: it is equivalent to the rank-one case
of the model product formula (`Work.Whitney.tcmPunctCore_signed`,
`Work.Whitney.tcmProd_rankOne_signed`), i.e. to the orientation sign of the cap map
`capMap n w = (w, √(1-‖w‖²))`; see `Submission/Work/Whitney/NOTES_rankOne_signed.md`,
`Submission/Work/Whitney/rankOne_cup_model_NOTES.md` and
`Submission/Work/Whitney/tcmProd_suspRule.NOTES.md`.
-/

theorem tcmModelMul_point_signed_full (Y : Type) [TopologicalSpace Y] [Subsingleton Y] (p q : ℕ) :
    Work.Whitney.tcmRelCup (Work.Whitney.tcmA Y p q) (Work.Whitney.tcmC Y p q)
        (Work.Whitney.isOpen_tcmA Y p q) (Work.Whitney.isOpen_tcmC Y p q) p q
      ((Work.Thom.relCohMap (Work.Whitney.tcmPr1 Y p q) (Work.Whitney.tcmA Y p q)
        (Work.Thom.Punct Y p) (fun x hx => hx) ℤ p).hom (Work.Thom.Mpun p Y))
      ((Work.Thom.relCohMap (Work.Whitney.tcmPr2 Y p q) (Work.Whitney.tcmC Y p q)
        (Work.Thom.Punct Y q) (fun x hx => hx) ℤ q).hom (Work.Thom.Mpun q Y))
    = ((-1 : ℤ) ^ (p * q)) •
      ((Work.Thom.relCohMap (Work.Whitney.tcmF Y p q)
        (Work.Whitney.tcmA Y p q ∪ Work.Whitney.tcmC Y p q) (Work.Thom.Punct Y (p + q))
        (Work.Whitney.tcmF_mem Y p q) ℤ (p + q)).hom (Work.Thom.Mpun (p + q) Y)) := by
  induction q with
  | zero => exact Work.Whitney.tcmModelMul_point_zero Y p
  | succ q ih =>
      refine Work.Whitney.phi_injective (Y := Y) p (q + 1) (p + (q + 1)) ?_
      rw [map_zsmul]
      rw [Work.Whitney.tcmCup_step Y p q]
      rw [ih]
      rw [map_zsmul]
      rw [Work.Whitney.phi_Mpun (Y := Y) p q]
      rw [Work.Whitney.step_zsmul]
      rw [show Work.Thom.step Y (p + q) (Work.Thom.Mn (p + q) Y)
          = Work.Thom.Mn (p + q + 1) Y from rfl]
      rw [smul_smul]
      congr 1
      · rw [Nat.mul_succ, pow_add]
        exact mul_comm _ _
      · exact (Work.Whitney.phi_Mpun (Y := Y) p (q + 1)).symm

end Work.Whitney
