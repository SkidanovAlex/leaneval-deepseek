import Mathlib
import Submission.Work.ORHomAlg.Dual
import Submission.Work.ORHomAlg.JL52.DiagTensorDefs
import Submission.Work.ORBridgeTor.DiagDualDefs
import Submission.Work.ORBridgeTor.diagTensorCongr

namespace Work.ORBridgeTor

/-!
Both tensor products carry the diagonal action `Work.ORHomAlg.JL52.instDiagModule`; on the second
factor the two `K[G]`-module structures (`Work.ORHomAlg.DualMod.instModuleOfRight` on
`DualMod (DualMod C)`, and the given one on `C`) agree pointwise (see
`Work.ORHomAlg.DualMod.instModuleOfRight_smul` and
`Work.ORHomAlg.DualMod.instModuleOppositeOfLeft_smul`).  So the identity map works: for
`map_smul'`, compare the two diagonal actions on pure tensors
(`Work.ORHomAlg.JL52.diag_smul_single_tmul` for both structures) and conclude by
`MonoidAlgebra.induction_on` on the scalar.  `TensorProduct.congr` of two `LinearEquiv.refl`s
already typechecks against this goal.

The proof below is organised differently, but follows exactly this route: the pointwise agreement
of the two `K[G]`-structures on `DualMod (DualMod C)` is `diagDual_smul_eq_smul`, and the two
`K`-linear identity maps `dualDualToCLin`, `dualDualToXLin` (whose codomains are the *given* copy
of `C`, resp. the double dual, so that `•` on their values resolves to the intended structure) are
shown to be `K[G]`-linear in `dualDualToCLin_smul` and `dualDualToXLin_smul`, using only the
DualMod API.  The general functoriality statement `Work.ORBridgeTor.diagTensorCongr` then turns
these two maps into the required `K[G]`-linear equivalence of the diagonal tensor products.

Note the use of *term-mode* (`Eq.trans`) rather than `rw` for the comparison: the two spellings
`DualMod (DualMod C)` and `C` of the same type are only definitionally equal, and term elaboration
checks definitional equality at the default transparency, whereas the rewriting tactics work at a
lower one at which the plain `def DualMod` does not unfold.
-/
open TensorProduct MulOpposite

universe u

section DiagDual

variable (K : Type u) [Field K] (G : Type u) [Group G]
    (C : Type u) [AddCommGroup C] [Module K C] [Module (MonoidAlgebra K G) C]
    [SMulCommClass K (MonoidAlgebra K G) C]

/-- **The two `K[G]`-module structures on `DualMod (DualMod C)` agree pointwise**: the action of
`r : K[G]` for the dual-dual structure equals the given action of `r` on `C`.

Both sides of the equation are elements of `DualMod (DualMod C)`, but the right hand side is
written with `dualDualToCLin K C x` (a term of type `C`) so that the instance resolved for `•`
is the given structure on `C`. -/
theorem diagDual_smul_eq_smul (r : MonoidAlgebra K G)
    (x : Work.ORHomAlg.DualMod (Work.ORHomAlg.DualMod C)) :
    r • x = r • (dualDualToCLin K C x) :=
  (Work.ORHomAlg.DualMod.instModuleOfRight_smul K G (Work.ORHomAlg.DualMod C) r x).trans
    ((Work.ORHomAlg.DualMod.instModuleOppositeOfLeft_smul K G C
        (Work.ORHomAlg.antipodeEquiv K G r) x).trans
      (by rw [RingEquiv.symm_apply_apply]; rfl))

/-- The identity `K`-linear map `dualDualToCLin` is `K[G]`-linear, where the source carries the
dual-dual structure and the target the given structure on `C`. -/
theorem dualDualToCLin_smul (r : MonoidAlgebra K G)
    (x : Work.ORHomAlg.DualMod (Work.ORHomAlg.DualMod C)) :
    dualDualToCLin K C (r • x) = r • dualDualToCLin K C x :=
  (dualDualToCLin_apply K C (r • x)).trans (diagDual_smul_eq_smul K G C r x)

/-- The identity `K`-linear map `dualDualToXLin` is `K[G]`-linear, where the source carries the
given structure on `C` and the target the dual-dual structure. -/
theorem dualDualToXLin_smul (r : MonoidAlgebra K G) (y : C) :
    dualDualToXLin K C (r • y) = r • dualDualToXLin K C y := by
  rw [dualDualToXLin_apply]
  refine (diagDual_smul_eq_smul K G C r (dualDualToXLin K C y)).symm.trans ?_
  rfl

end DiagDual

theorem diagDualDualEquiv (K : Type u) [Field K] (G : Type u) [Group G]
    (S : Type u) [Ring S] [Algebra K S] [Module (MonoidAlgebra K G) S]
    [SMulCommClass K (MonoidAlgebra K G) S]
    (C : Type u) [AddCommGroup C] [Module K C] [Module (MonoidAlgebra K G) C]
    [SMulCommClass K (MonoidAlgebra K G) C] :
    Nonempty (TensorProduct K S (Work.ORHomAlg.DualMod (Work.ORHomAlg.DualMod C)) ≃ₗ[MonoidAlgebra K G]
      TensorProduct K S C) :=
  diagTensorCongr K G S (Work.ORHomAlg.DualMod (Work.ORHomAlg.DualMod C)) C
    (dualDualToCLin K C) (dualDualToXLin K C)
    (fun r x => dualDualToCLin_smul K G C r x)
    (fun r y => dualDualToXLin_smul K G C r y)
    (fun x => rfl) (fun y => rfl)

end Work.ORBridgeTor
