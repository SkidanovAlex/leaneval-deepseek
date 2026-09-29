import Mathlib
import Submission.Work.ConvR.listProdBDefs
import Submission.Work.ConvR.listProdBWork

/-!
# The list-product word (`Work.ConvR.listProdB`)

A word that replaces the value `intList ts` (a list of naturals on top of the value stack) by the
single value `int ts.prod`, at cost quadratic in the encoding size of the list.

The program and its cost functions are defined in `Submission/Work/ConvR/listProdBDefs.lean`;
the proof (the two runs of one iteration, the walk over the list with its per-iteration cost sum,
and the quadratic cost bound) is in `Submission/Work/ConvR/listProdBWork.lean`.
-/

set_option autoImplicit false

namespace Work.ConvR

theorem listProdB (hK : HvdH.KernelLib) (hI : HvdH.IntLib) (hL : HvdH.LayoutLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (ts : List ℕ) (rest : List HvdH.Val),
      HvdH.WordR main prog (fun vs => vs = HvdH.intList ts :: rest)
        (fun _ out => out = HvdH.Val.int ((ts.prod : ℕ) : ℤ) :: rest)
        (fun vs => K * ((HvdH.vsz (vs.headD HvdH.Val.nil)) + 1) ^ 2) :=
  listProdB_aux hK hI hL

end Work.ConvR
