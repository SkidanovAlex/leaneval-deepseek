import Submission.Work.PTCert.KernelCert

/-!
# PTCert — extra kernel checks (added after the main data build; kept separate so that the data
modules need not be rebuilt)
-/

set_option autoImplicit false

noncomputable section

namespace Submission.PTCert

/-- Every code of the chunk has an N-representative number `< 611`. -/
def eBoundOK (eM : NT) (l : List ℕ) : Bool := allL l (fun z => Nat.blt ((eG eM z - 1) / 32) 611)

/-- Every member entry `4096 z + s` of the group lists uses a stabiliser index `s < ns`. -/
def memIdxOK (gl : List (List ℕ)) (ns : ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun l _ ih => allL l (fun v => Nat.blt (v % 4096) ns) && ih) gl

/-- A packed table of signed target coefficients agrees with `q` on the pairs `ps`. -/
def qTabOK (qT : NT) (q : ℕ → ℤ) (ps : List ℕ) : Bool := allL ps (fun p => decide (sv (p8 qT p) = q p))

end Submission.PTCert

end
