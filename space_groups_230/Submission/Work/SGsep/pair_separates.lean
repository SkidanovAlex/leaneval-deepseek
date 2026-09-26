import Mathlib
import Submission.Work.SG.SGsepDefs
import Submission.Work.SGsep.PairAux
import Submission.Work.SGsep.PairAux2
import Submission.Work.SGsep.PairAux3
import Submission.Work.SGsep.table_facts
import Submission.Work.SGsep.elem_separates
import Submission.Work.SGsep.keyE_conj
import Submission.Work.SGsep.pairsep_bits
import Submission.Work.SGsep.PairAux4

namespace Work.SGsep

open Work.SG
open Work.SGsep.PSep

/-- The `pair` invariant separates: if the number of ordered pairs of table elements with keys
`(dA,tA,oA)`, `(dB,tB,oB)` and the six-bit pattern `bits` differs (`some ca ≠ some cb`, as in
`Data.Sep.chk`; `Data.pairCount` is `none` for an invalid certificate list, hence both sides
are required to be `some`), then there is no integral equivalence.
The bits (`Data.PairCert.chk`, `Data/SepCheck.lean`) are
`(B-1)v_A ∈ (B-1)N_A ℤ³`, `(B+1)v_A ∈ (B+1)N_A ℤ³` (checked by `SpanCert` membership in the
column span, i.e. the image of the matrix) and the `τ`-free
`(A∓1)ℤ³ ⊆ (B∓1)ℤ³` in the order `(A-1,B-1), (A+1,B+1), (A-1,B+1), (A+1,B-1)`.
Naturality: `conj_sub_one`, `conj_add_one`, `latImg_conj_eq_map`, `latImg_le_conj_iff` are in
`SGsepDefs` (`vA_conj`, `NZ_conj`, `det_trace_conj`, `IsOrdOf_conj`, `table_facts` are sibling
files that may also be imported); `TauOnTable` identifies `sgTau` with `repZ/n`. -/
theorem pair_separates (k l : Fin 230) (dA tA : ℤ) (oA : ℕ) (dB tB : ℤ) (oB : ℕ)
    (bits : List Bool) (la lb : List Data.PairCert) (ca cb : ℕ)
    (hk : TauOnTable k) (hl : TauOnTable l)
    (ha : Data.pairCount k (dA, tA, oA) (dB, tB, oB) bits la = some ca)
    (hb : Data.pairCount l (dA, tA, oA) (dB, tB, oB) bits lb = some cb)
    (hne : ca ≠ cb) :
    ¬ ∃ U : IMat, IsUnit U.det ∧ ∃ s : Fin 3 → ℝ,
        IntEquiv (arithRep (sgArith k)) (sgTau k) (arithRep (sgArith l)) (sgTau l) U s := by
  rintro ⟨U, hU, s, hie⟩
  -- the `U⁻¹` of `IntEquiv` is `invMat U`
  have hinv : (U⁻¹ : IMat) = invMat U := Matrix_inv_eq_invMat hU
  -- the semantic keys of the table elements
  have hkeyk : ∀ i, i < pn k → ekeyK k i = keyE k (elI k i) := fun i hi =>
    (ElemTbl.keyE_table k i hi hk (elemTab_chk_at k i hi)).symm
  have hkeyl : ∀ i, i < pn l → ekeyK l i = keyE l (elI l i) := fun i hi =>
    (ElemTbl.keyE_table l i hi hl (elemTab_chk_at l i hi)).symm
  -- the certificate bits are the semantic bits
  have hbitk : ∀ p : Data.PairCert, p.i < pn k → p.j < pn k → Data.PairCert.chk k p = true →
      p.bits = pairBits k (elI k p.i) (elI k p.j) := fun p hi hj hp =>
    pairsep_bits k p hk hi hj hp (elM_ord_ne_zero k hi) (vOfK_eq_vA k p.i hk hi) tfCert_bit
  have hbitl : ∀ p : Data.PairCert, p.i < pn l → p.j < pn l → Data.PairCert.chk l p = true →
      p.bits = pairBits l (elI l p.i) (elI l p.j) := fun p hi hj hp =>
    pairsep_bits l p hl hi hj hp (elM_ord_ne_zero l hi) (vOfK_eq_vA l p.i hl hi) tfCert_bit
  -- both counts are the invariant
  have hca : ca = PInv k (dA, tA, oA) (dB, tB, oB) bits :=
    pairCount_eq_PInv k _ _ _ _ _ hkeyk hbitk (Tk_eq_range k) (elI_injOn k) ha
  have hcb : cb = PInv l (dA, tA, oA) (dB, tB, oB) bits :=
    pairCount_eq_PInv l _ _ _ _ _ hkeyl hbitl (Tk_eq_range l) (elI_injOn l) hb
  -- conjugation bijects the tables
  have hbij : ∀ A, A ∈ Tk l ↔ ∃ B ∈ Tk k, A = U * B * invMat U := fun A => by
    rw [mem_Tk_iff l A, hie.1 A]
    constructor
    · rintro ⟨B, hB, rfl⟩
      exact ⟨B, (mem_Tk_iff k B).mpr hB, by rw [hinv]⟩
    · rintro ⟨B, hB, rfl⟩
      exact ⟨B, (mem_Tk_iff k B).mp hB, by rw [hinv]⟩
  -- the cocycle equation, in `invMat` form
  have hcoc : ∀ A ∈ Tk k, ∃ n : Fin 3 → ℤ,
      sgTau l (U * A * invMat U) = (toRMat U).mulVec (sgTau k A) + s
        - (toRMat (U * A * invMat U)).mulVec s + toRVec n := by
    intro A hA
    obtain ⟨n, hn⟩ := hie.2 A ((mem_Tk_iff k A).mp hA)
    rw [hinv] at hn
    exact ⟨n, hn⟩
  -- the key and the bits are preserved
  have hkp : ∀ A ∈ Tk k, keyE l (U * A * invMat U) = keyE k A := fun A hA =>
    keyE_conj k l U s hU (hcoc A hA)
  have hbp : ∀ A ∈ Tk k, ∀ B ∈ Tk k, pairBits l (U * A * invMat U) (U * B * invMat U)
      = pairBits k A B := fun A hA B hB => by
    rw [pairBits_eq_pairBitsG l (U * A * invMat U) (U * B * invMat U),
      pairBits_eq_pairBitsG k A B]
    exact pairBitsG_conj hU (sgTau k) (sgTau l) s A B (hcoc A hA)
  -- hence the invariants agree, contradicting `ca ≠ cb`
  have hP : PInv k (dA, tA, oA) (dB, tB, oB) bits
      = PInv l (dA, tA, oA) (dB, tB, oB) bits :=
    pairsep_pinv k l U hU _ _ bits hbij hkp hbp
  exact hne (by rw [hca, hP, hcb])

end Work.SGsep
