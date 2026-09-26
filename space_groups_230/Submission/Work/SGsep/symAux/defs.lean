import Mathlib
import Submission.Work.SG.SGsepDefs
import Submission.Work.SGsep.sym_prep
import Submission.Work.SGsep.table_facts

/-!
# Shared vocabulary for the soundness of the `sym` certificate (`symChk_yes`)

The `sym` certificate of representative `k` (`Data.SymCert`, checked by `Data.SymCert.chk`)
certifies the order of `[τ_k] ∈ H¹(P, ℝ³/ℤ³)`, `τ_k = sgTau k`.  The *yes* half of its
soundness is that `o · τ_k` is a coboundary for `o = a.o`.

This file fixes the notation used by the delegated lemmas (`symDef`, `symSig`, `eK`, `GK`,
`nK`, `kK`, `geni`, `mulg`, `zK`) and nothing else; every entry is an `abbrev`, so it is
definitionally the corresponding accessor of `Data.repArith k`.

Nothing here is `sorry`ed.
-/

namespace Work.SGsep

open Work.SG

/-- The certified arithmetic-class table of representative `k`. -/
abbrev Dk (k : Fin 230) : Data.ArithData := Data.repArith k.val

/-- The `i`-th element of the arithmetic class of `k` (identity off the table). -/
abbrev eK (k : Fin 230) (i : ℕ) : IMat := ((Dk k).elems.getD i Data.M3.one).toIMat

/-- The `g`-th generator matrix of the arithmetic class of `k` (identity off the list). -/
abbrev GK (k : Fin 230) (g : ℕ) : IMat := ((Dk k).gens.getD g Data.M3.one).toIMat

/-- The order of the arithmetic class of `k`. -/
abbrev nK (k : Fin 230) : ℕ := (Dk k).n

/-- The number of generators of the arithmetic class of `k`. -/
abbrev kK (k : Fin 230) : ℕ := (Dk k).gens.length

/-- The index of the `g`-th generator in the element table of `k`. -/
abbrev geni (k : Fin 230) (g : ℕ) : ℕ := (Dk k).genIdx.getD g 0

/-- The index of `generator g · element i` in the element table of `k`. -/
abbrev mulg (k : Fin 230) (g i : ℕ) : ℕ := ((Dk k).mulGen.getD g []).getD i 0

/-- The BFS generator index of the parent of element `i+1`. -/
abbrev par1 (k : Fin 230) (i : ℕ) : ℕ := ((Dk k).par.getD i (0, 0)).1

/-- The BFS element index of the parent of element `i+1`. -/
abbrev par2 (k : Fin 230) (i : ℕ) : ℕ := ((Dk k).par.getD i (0, 0)).2

/-- The tabulated integer numerator vector of the `i`-th element of the class of `k`. -/
abbrev zK (k : Fin 230) (i : ℕ) : Data.V3 := (Data.repZ.getD k.val []).getD i Data.V3.zero

/-- The coboundary potential attached to a symmorphy certificate: `σ = a.sig / n²`. -/
noncomputable def symSig (k : Fin 230) (a : Data.SymCert) : Fin 3 → ℝ :=
  fun c => (a.sig.toFun c : ℝ) / ((nK k : ℝ) ^ 2)

/-- The defect of `a.o · τ_k` for the potential `symSig k a`, at the matrix `A`. -/
noncomputable def symDef (k : Fin 230) (a : Data.SymCert) (A : IMat) : Fin 3 → ℝ :=
  (a.o : ℝ) • sgTau k A - (symSig k a - (toRMat A).mulVec (symSig k a))

theorem symDef_eq_defect (k : Fin 230) (a : Data.SymCert) (A : IMat) :
    symDef k a A = defect (fun A => (a.o : ℝ) • sgTau k A) (symSig k a) A := rfl

@[simp] theorem symSig_apply (k : Fin 230) (a : Data.SymCert) (c : Fin 3) :
    symSig k a c = (a.sig.toFun c : ℝ) / ((nK k : ℝ) ^ 2) := rfl

end Work.SGsep
