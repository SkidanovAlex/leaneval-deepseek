/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GLUE area (fundmath3-gorenstein_walter)
-/
import Submission.Work.GLUE.Bridge
import Submission.Work.GLUE.ThompsonJ
import Submission.Work.GLUE.PStable

set_option autoImplicit false

open scoped MatrixGroups
open Subgroup

/-!
# GLUE: Glauberman's `Z(J)`-theorem (Theorem A), in the contract's vocabulary

**Deliverable of the GLUE area.**

`Work.GW2.ZJAProp` is the contract's statement of Glauberman's `Z(J)`-theorem (Theorem A):
if `X` is a finite group, `p ≠ 2` a prime, `X` has dihedral or cyclic Sylow 2-subgroups,
`C_X(O_p(X)) ≤ O_p(X)`, and `P ∈ Syl_p(X)`, then `Z(J(P)) = J(P) ∩ C_X(J(P))` is normal in `X`.

The odd-order library proves this as `Subgroup.zCenter_thompsonJAbelian_normal`, stated with
the library's `opCore`/`thompsonJAbelian` and with *p*-stability (`Subgroup.IsPStableOp`) as an
explicit hypothesis.  Here:

* `pCore_eq_opCore` and `ZJ_eq_thompsonJAbelian` (from `Bridge.lean`/`ThompsonJ.lean`)
  translate the statement;
* `PStableProp`, the `PSTAB` area's deliverable, supplies `p`-stability for every group of
  the class (`isPStableOp_of_pStableProp` in `PStable.lean`).

The main results are `zjA : PStableProp → ZJAProp` (the contract's shape) and the applied
forms `zJ_normal_of_pStableProp`, `zJ_normal_of_isPStableOp`.
-/

namespace Work.GW2

/-- `Z(J(P))` is normal in `X`, from `p`-stability in the library's own shape
(`Subgroup.IsPStableOp`).  This is Glauberman's Theorem A with the translation of the
vocabulary performed by hand. -/
theorem zJ_normal_of_isPStableOp {X : Type*} [Group X] [Finite X] (p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hstab : Subgroup.IsPStableOp p X)
    (hconstr : Subgroup.centralizer (pCore p X : Set X) ≤ pCore p X) (P : Sylow p X) :
    (ZJ (P : Subgroup X)).Normal := by
  have hconstr' : Subgroup.centralizer
      ((OddOrder.Isaacs.Ch01.opCore p X : Subgroup X) : Set X)
      ≤ OddOrder.Isaacs.Ch01.opCore p X := by
    rw [← pCore_eq_opCore]
    exact hconstr
  have h := Subgroup.zCenter_thompsonJAbelian_normal (p := p) hp2 hstab hconstr' P
  simpa only [ZJ_eq_thompsonJAbelian] using h

/-- **Glauberman's `Z(J)`-theorem, Theorem A, in the contract's shape.** -/
theorem zjA (hPS : PStableProp) : ZJAProp := by
  intro X instG instF p instP hp2 hdih hconstr P
  exact zJ_normal_of_isPStableOp (X := X) p hp2
    (isPStableOp_of_pStableProp hPS X p hp2 hdih) hconstr P

/-- The per-group form of `zjA`, for callers working with one group at a time. -/
theorem zJ_normal_of_pStableProp (hPS : PStableProp) (X : Type) [Group X] [Finite X]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hdih : DihOrCycSylow X)
    (hconstr : Subgroup.centralizer (pCore p X : Set X) ≤ pCore p X) (P : Sylow p X) :
    (ZJ (P : Subgroup X)).Normal :=
  zjA hPS X p hp2 hdih hconstr P

end Work.GW2
