import Mathlib
import Submission.Work.SG.SGsepDefs
import Submission.Work.SGsep.sym_prep
import Submission.Work.SGsep.symChk_yes
import Submission.Work.SGsep.symChk_no

namespace Work.SGsep

open Work.SG

/-- `1 ≤ a.o` is part of the certificate check. -/
theorem symChk_pos (k : Fin 230) (a : Data.SymCert) (ha : Data.SymCert.chk k.val a = true) :
    1 ≤ a.o := by
  have h1 : decide (1 ≤ a.o) = true := by
    have := ha
    unfold Data.SymCert.chk at this
    simp only [Bool.and_eq_true] at this
    exact this.1.1.1
  exact of_decide_eq_true h1

/-- A certificate `a` that checks for the representative `k` certifies the symmorphy order of
`τ_k` on its arithmetic class: `o τ_k` is a coboundary (`symChk_yes`) and `(o/p) τ_k` is not
for every prime `p ∣ o` (`symChk_no`, which needs `o ≤ 48` for `primesOf` completeness). -/
theorem symChk_SymOrd (k : Fin 230) (a : Data.SymCert) (hk : TauOnTable k)
    (ha : Data.SymCert.chk k.val a = true) (hao : a.o ≤ 48) :
    SymOrd (arithRep (sgArith k)) (sgTau k) a.o :=
  ⟨symChk_pos k a ha, symChk_yes k a hk ha, symChk_no k a hk ha hao⟩

/-- The `sym` invariant separates: two certificates `Data.SymCert.chk k a` and
`Data.SymCert.chk l b` with different orders `a.o ≠ b.o` of `[τ]` in `H¹` rule out an integral
equivalence.  Meaning of the check (`Data/SepCheck.lean`): `(1 - g) (σ/n²) ≡ o τ(g) (mod ℤ³)`
for all generators (so `o τ` is a coboundary), and for each prime `p ∣ o` a left-kernel vector
`u` of the stacked `(1 - g)` with `∑_g u_g · (o/p) z_g ≢ 0 (mod n)` (so `(o/p) τ` is *not* a
coboundary).  The hypotheses `a.o ≤ 48`, `b.o ≤ 48` ensure that `Data.primesOf o` (primes
`≤ 47`) really lists all prime divisors of `o`, making the check sound.  Transport a coboundary
by `x ↦ U x + s` (use `σ' = (toRMat U).mulVec σ + o • s`), in both directions (with `invMat U`),
and use that the set of `o` with `o τ` a coboundary is closed under `gcd` (Bézout), so it has a
unique positive generator. -/
theorem sym_separates (k l : Fin 230) (a b : Data.SymCert)
    (hk : TauOnTable k) (hl : TauOnTable l)
    (ha : Data.SymCert.chk k a = true) (hb : Data.SymCert.chk l b = true)
    (hao : a.o ≤ 48) (hbo : b.o ≤ 48) (hne : a.o ≠ b.o) :
    ¬ ∃ U : IMat, IsUnit U.det ∧ ∃ s : Fin 3 → ℝ,
        IntEquiv (arithRep (sgArith k)) (sgTau k) (arithRep (sgArith l)) (sgTau l) U s := by
  rintro ⟨U, hU, s, hIE⟩
  have haS : SymOrd (arithRep (sgArith k)) (sgTau k) a.o := symChk_SymOrd k a hk ha hao
  have hbS : SymOrd (arithRep (sgArith l)) (sgTau l) b.o := symChk_SymOrd l b hl hb hbo
  have h2 : SymOrd (arithRep (sgArith k)) (sgTau k) b.o :=
    (SymOrd_nat hU hIE b.o).mpr hbS
  exact hne (SymOrd_unique haS h2)

end Work.SGsep
