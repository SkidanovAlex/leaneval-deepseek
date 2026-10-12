import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseB7.FockDefs
import Submission.Work.BoseB7.bAdjoint
import Submission.Work.BoseB7.bCCR
import Submission.Work.BoseB7.bComm
import Submission.Work.BoseB7.l2Form_posDef
import Submission.Work.BoseB7.l2Form_symm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7.boseModel` — the honest bosonic Fock space as a `FockData`

`Work.BoseB7.boseFockData Mode` is the free bosonic Fock space over the mode set
`Mode` (occupation-number representation, `Work.BoseB7.boseDefs`), with

* `a i = bAnn i` the annihilation operator of the mode `i`,
* `aDag i = bCre i` the creation operator of the mode `i`,
* `bp = l2Form (occIdx Mode)` the ℓ² (Fock) inner product,
* `ccrK i j = if i = j then 1 else 0` the **non-zero** commutator kernel
  (`[a_i, a_j†] = δ_{ij}`).

This is a genuine (non-degenerate) instantiation of the `B4` interface
`Work.BoseB7.FockData`: the operators are the standard bosonic ladder operators
on states of finite particle number, the creation operator is the adjoint of the
annihilation operator (`Work.BoseB7.bAdjoint`) and the canonical commutation
relations hold (`Work.BoseB7.bCCR`, `Work.BoseB7.bComm`).

The carrier is `boseH.{0,v} Mode = occIdx.{0,v} Mode →₀ ℝ`, a type in
`Type (max 0 v)` — that is `Type v` after the level normalisation `max 0 v = v`.
The structure is built with `FockData.mk`, the ladder operators being ascribed to
the carrier universe `v` so that no universe metavariable is left open; the
universe-polymorphic lemmas of `boseDefs` are then instantiated at that same
universe.

The momentum assignment `kmom` is taken to be identically zero: the parity axiom
of `FockData` forces `kmom i = 0` whenever `-i = i`
(`Work.BoseB7.kmom_eq_zero_of_neg_eq_self` in `fockModel_nonempty.lean`), in
particular for `ZMod 2`, so nothing is lost for the instantiation used there.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7

universe v

/-- **The free bosonic Fock space as a `FockData`**: annihilation/creation
operators in the occupation-number representation, the ℓ² Fock form and the
canonical commutation relations `[a_i, a_j†] = δ_{ij}`. -/
def boseFockData (Mode : Type) [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode] :
    FockData.{0, max 0 v} Mode :=
  FockData.mk (boseH.{0, v} Mode) 0 (by intro i; simp)
    (fun i => (bAnn i : boseH.{0, v} Mode →ₗ[ℝ] boseH.{0, v} Mode))
    (fun i => (bCre i : boseH.{0, v} Mode →ₗ[ℝ] boseH.{0, v} Mode))
    (by intro i j; exact (@bComm.{0, v, v} Mode i j).1)
    (by intro i j; exact (@bComm.{0, v, v} Mode i j).2)
    (fun i j => if i = j then 1 else 0)
    (by intro i j; exact bCCR i j)
    (l2Form (occIdx.{0, v} Mode))
    (by intro f g; exact l2Form_symm (occIdx.{0, v} Mode) f g)
    (by intro f; exact (l2Form_posDef (occIdx.{0, v} Mode) f).1)
    (by intro f hf; exact (l2Form_posDef (occIdx.{0, v} Mode) f).2 hf)
    (by intro i f g; exact bAdjoint i f g)

/-- The genuine model has a **non-zero** commutator kernel: `[a₀, a₀†] = 1`.  This
certifies that the `FockData` interface is instantiated non-degenerately (unlike
the all-zero model of `fockModel_nonempty`). -/
theorem boseFockData_ccrK :
    (boseFockData (ZMod 2)).ccrK 0 0 = 1 := by
  simp [boseFockData]

/-- The interface is instantiated with a **non-zero** commutator kernel on
`ZMod 2`: the free bosonic Fock space realises `[a₀, a₀†] = 1`. -/
theorem fockModel_ccrK_nonzero :
    ∃ F : FockData.{0, max 0 v} (ZMod 2), F.ccrK 0 0 = 1 :=
  ⟨boseFockData (ZMod 2), by simp [boseFockData]⟩

end Work.BoseB7
