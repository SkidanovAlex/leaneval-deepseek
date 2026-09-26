import Mathlib
import Submission.Work.SG.SGsepDefs
import Submission.Work.SGsep.sym_prep
import Submission.Work.SGsep.table_facts
import Submission.Work.SGsep.symChk_defs
import Submission.Work.SGsep.symChk_kern
import Submission.Work.SGsep.symChk_dot
import Submission.Work.SGsep.symChk_data
import Submission.Work.SGsep.symChk_extract

/-!
# `Work.SGsep.symChk_no`

The `no` half of the `sym` separation certificate: if `Data.SymCert.chk k a` holds with
`a.o ≤ 48`, then for every prime `p ∣ a.o` the multiple `(a.o / p) • sgTau k` of the
representative cocycle is *not* an integral coboundary on `arithRep (sgArith k)`.

The certificate provides, for each prime `p ∣ a.o`, an integer left-kernel vector `u` of the
stacked `(1 - A_g)` (over the generators `A_g` of the class) with
`∑_g u_g · (a.o/p) z_g ≢ 0 (mod n)`, where `z_g = n · τ(A_g)`.  A potential `σ` with
`(a.o/p) τ (A_g) - (σ - A_g σ) ∈ ℤ³` for the generators would force
`n ∣ ∑_g u_g · (a.o/p) z_g`, a contradiction (`Work.SGsep.not_isCob_of_leftKernel`).
-/

namespace Work.SGsep

open Work.SG
open scoped BigOperators

/-- `TauOnTable` read at the generators of the class table: `sgTau k` at the generator `A_g` is
`z_g / n` with `z_g = repZ[k][genIdx g]`; this is `TauOnTable` at the index `genIdx g`, using that
`elems` has the generator at that index (`Work.SGsep.symChk_data`). -/
theorem tau_gens (k : Fin 230) (hk : TauOnTable k) (g : ℕ)
    (hg : g < (Data.repArith k.val).gens.length) :
    sgTau k (((Data.repArith k.val).gens.getD g Data.M3.one).toIMat) =
      fun c => (((Data.repZ.getD k.val []).getD ((Data.repArith k.val).genIdx.getD g 0)
        Data.V3.zero).toFun c : ℝ) / ((Data.repArith k.val).n : ℝ) := by
  obtain ⟨-, hfacts⟩ := symChk_data k
  rw [← (hfacts g hg).2.2]
  exact hk _ (hfacts g hg).2.1

/-- The `no` half of the symmorphy certificate: for every prime `p ∣ a.o`, `(a.o / p) • sgTau k`
is not an integral coboundary on `arithRep (sgArith k)`. -/
theorem symChk_no (k : Fin 230) (a : Data.SymCert) (hk : TauOnTable k)
    (ha : Data.SymCert.chk k.val a = true) (hao : a.o ≤ 48)
    (p : ℕ) (hp : p.Prime) (hpd : p ∣ a.o) :
    ¬ IsCob (arithRep (sgArith k)) (fun A => ((a.o / p : ℕ) : ℝ) • sgTau k A) := by
  obtain ⟨-, u, -, hkern, hdot⟩ := symChk_extract k a ha p hp hpd hao
  obtain ⟨hnpos, hfacts⟩ := symChk_data k
  have h1 := symChk_kern (Data.repArith k.val) u hkern
  have h2 := symChk_dot (Data.repArith k.val) a.o p
    (fun g => (Data.repZ.getD k.val []).getD ((Data.repArith k.val).genIdx.getD g 0)
      Data.V3.zero) u hdot
  refine not_isCob_of_leftKernel (P := arithRep (sgArith k)) (τ := sgTau k) (a.o / p)
    (Data.repArith k.val).n (Data.repArith k.val).gens.length hnpos
    (fun g => ((Data.repArith k.val).gens.getD g Data.M3.one).toIMat)
    (fun g => ((Data.repZ.getD k.val []).getD ((Data.repArith k.val).genIdx.getD g 0)
      Data.V3.zero).toFun)
    (fun g => ublk u g) ?_ ?_ h1 h2
  · intro g hg
    exact (hfacts g hg).1
  · intro g hg
    exact tau_gens k hk g hg

end Work.SGsep
