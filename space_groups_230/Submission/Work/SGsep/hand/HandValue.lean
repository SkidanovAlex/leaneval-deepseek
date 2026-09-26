import Submission.Work.SGsep.hand.HandCore
import Submission.Work.SGsep.hand.gcd_v3
import Submission.Work.SGsep.hand.misc_bridges
import Submission.Work.SGsep.hand.rankOne_eq_conj_V3
import Submission.Work.SGsep.vA_conj
import Submission.Work.SGsep.NZ_conj

/-!
# Comparing the handedness values of corresponding certificates

If two table elements correspond under the integral equivalence `A_l j = U A_k i U⁻¹` with
`det U = 1`, then any hand certificate of `k` at `i` and any hand certificate of `l` at `j`
have the same handedness value `(ord, h, j mod h)`.
-/

namespace Work.SGsep.Hand

open Work.SG
open Work.SG.Data
open Work.SGsep.Hand.Data
open Work.SGsep.hand
open scoped Matrix

theorem toIMat_conj_of {k l : Fin 230} {i j : Nat} {U : IMat}
    (hij : Ah l j = U * Ah k i * invMat U) :
    (A3n l.val j).toIMat = U * (A3n k.val i).toIMat * invMat U := by
  show (A3 l j).toIMat = U * (A3 k i).toIMat * invMat U
  simpa only [Ah] using hij

theorem NZ_normSum_of {k : Fin 230} {i ord : Nat}
    (hord : (A3n k.val i).ord = ord) (h3 : 3 ≤ ord) :
    (M3.normSum (A3n k.val i) ord).toIMat = NZ (Ah k i) := by
  have hne : (A3n k.val i).ord ≠ 0 := by omega
  have h1 : (Data.normOf (A3n k.val i)).toIMat = NZ (Ah k i) := by
    show (Data.normOf (A3n k.val i)).toIMat = NZ ((A3n k.val i).toIMat)
    exact PSep.normOf_toIMat _ hne
  have h2 : (Data.normOf (A3n k.val i)).toIMat = (M3.normSum (A3n k.val i) ord).toIMat := by
    show (M3.normSum (A3n k.val i) (A3n k.val i).ord).toIMat
      = (M3.normSum (A3n k.val i) ord).toIMat
    rw [hord]
  rw [← h1, h2]

/-- Corresponding elements have certificates with the same handedness value. -/
theorem handVal_eq_of_corresponds {k l : Fin 230} (U : IMat) (s : Fin 3 → ℝ)
    (hU : IsUnit U.det) (hUdet : U.det = 1)
    (hIE : IntEquiv (arithRep (sgArith k)) (sgTau k) (arithRep (sgArith l)) (sgTau l) U s)
    (hk : TauOnTable k) (hl : TauOnTable l)
    {i j : Nat} (hi : i < (repArith k.val).n) (hj : j < (repArith l.val).n)
    (hij : Ah l j = U * Ah k i * invMat U)
    (o : Option HandCert) (hoc : HandCert.chk k.val i o = true)
    (o' : Option HandCert) (ho'c : HandCert.chk l.val j o' = true) :
    handVal o = handVal o' := by
  have hB := toIMat_conj_of (U := U) hij
  have hdetB : (A3n l.val j).det = (A3n k.val i).det := (ord_bridges.2.2 hU hB).2
  have hordB : (A3n l.val j).ord = (A3n k.val i).ord := (ord_bridges.2.2 hU hB).1
  cases o with
  | none =>
    cases o' with
    | none => rfl
    | some cb =>
      exfalso
      have hn : ¬ ((A3n k.val i).det = 1 ∧ 3 ≤ (A3n k.val i).ord) := by
        rcases chk_none hoc with h | h
        · intro hc; exact h hc.1
        · intro hc; omega
      obtain ⟨h1, h2, h3, -, -, -, -, -, -, -, -⟩ := chk_some ho'c
      exact hn ⟨by rw [← hdetB]; exact h1, by rw [← hordB, h2]; omega⟩
  | some ca =>
    cases o' with
    | none =>
      exfalso
      have hn : ¬ ((A3n l.val j).det = 1 ∧ 3 ≤ (A3n l.val j).ord) := by
        rcases chk_none ho'c with h | h
        · intro hc; exact h hc.1
        · intro hc; omega
      obtain ⟨h1, h2, h3, -, -, -, -, -, -, -, -⟩ := chk_some hoc
      exact hn ⟨by rw [hdetB]; exact h1, by rw [hordB, h2]; omega⟩
    | some cb =>
      obtain ⟨hdetk, hordk, h3k, hmulVk, hdotk, -, hcolsk, hhk, hdvdk, hbeta2k, hvofk⟩ :=
        chk_some hoc
      obtain ⟨hdetl, hordl, h3l, hmulVl, hdotl, -, hcolsl, hhl, hdvdl, hbeta2l, hvofl⟩ :=
        chk_some ho'c
      -- the conjugated axis
      have hcc := cert_conj_axis U hU hUdet hi hj hij hoc ho'c
      have hcc' : cb.c.toFun = Matrix.mulVec U ca.c.toFun := by
        rw [hcc, toFun_toV3]
      -- the `w` relation
      have hNA : NZ (Ah k i) = rankOne ca.c.toFun ca.w.toFun := by
        rw [← NZ_normSum_of (k := k) (i := i) (ord := ca.ord) hordk h3k]
        exact cols_rankOne hcolsk
      have hNB : NZ (Ah l j) = rankOne cb.c.toFun cb.w.toFun := by
        rw [← NZ_normSum_of (k := l) (i := j) (ord := cb.ord) hordl h3l]
        exact cols_rankOne hcolsl
      have hconj : rankOne cb.c.toFun cb.w.toFun
          = U * rankOne ca.c.toFun ca.w.toFun * invMat U := by
        rw [← hNB, hij, NZ_conj hU, hNA]
      have hcne : ca.c ≠ V3.zero := by
        intro hc0
        rw [hc0] at hdotk
        simp [V3.dot, V3.zero] at hdotk
      have hwrel : cb.w.toFun = (invMat U).transpose.mulVec ca.w.toFun :=
        rankOne_eq_conj_V3 hU hcne hcc' hconj
      -- the gcd data
      have hgcdk : V3.gcdV ca.w = ca.h := gcd_v3.1 hhk hdvdk ⟨ca.beta2, hbeta2k⟩
      have hgcdl : V3.gcdV cb.w = cb.h := gcd_v3.1 hhl hdvdl ⟨cb.beta2, hbeta2l⟩
      have hgcdEq : gcdIVec cb.w.toFun = gcdIVec ca.w.toFun := by
        rw [hwrel]
        refine gcdIVec_mulVec_unimodular (B := (invMat U).transpose) ?_ ca.w.toFun
        rw [Matrix.det_transpose, det_invMat hU]
        exact hU
      have hh : cb.h = ca.h := by
        rw [← hgcdl, ← hgcdk, ← gcdV_toFun, ← gcdV_toFun, hgcdEq]
      have hordEq : cb.ord = ca.ord := by
        rw [← hordl, hordB, hordk]
      -- the intrinsic translations
      have hvofK : toRealV (vOf k.val i) = vA (sgTau k) (Ah k i) := by
        show PSep.toRV (PSep.vOfK k i) = vA (sgTau k) (PSep.elI k i)
        exact (PSep.vOfK_eq_vA k i hk hi).symm
      have hvofL : toRealV (vOf l.val j) = vA (sgTau l) (Ah l j) := by
        show PSep.toRV (PSep.vOfK l j) = vA (sgTau l) (PSep.elI l j)
        exact (PSep.vOfK_eq_vA l j hl hj).symm
      have hvak : vA (sgTau k) (Ah k i) = (ca.j : ℝ) • toRealV ca.c := by
        rw [← hvofK, hvofk, toRealV_smul_eq]
      have hval : vA (sgTau l) (Ah l j) = (cb.j : ℝ) • toRealV cb.c := by
        rw [← hvofL, hvofl, toRealV_smul_eq]
      -- the conjugation of the cocycle
      have hAik : Ah k i ∈ arithRep (sgArith k) := Ah_mem hi
      obtain ⟨n1, hn1⟩ := hIE.2 (Ah k i) hAik
      have hinv : (U⁻¹ : IMat) = invMat U := (misc_bridges.1 hU).symm
      have hn1' : sgTau l (U * Ah k i * invMat U)
          = (toRMat U).mulVec (sgTau k (Ah k i)) + s
            - (toRMat (U * Ah k i * invMat U)).mulVec s + toRVec n1 := by
        rw [hinv] at hn1
        exact hn1
      obtain ⟨m, hmem, hmeq⟩ := vA_conj hU (sgTau k) (sgTau l) s (Ah k i) ⟨n1, hn1'⟩
      have hmeq' : vA (sgTau l) (Ah l j) = (toRMat U).mulVec (vA (sgTau k) (Ah k i)) + m := by
        rw [← hij] at hmeq
        exact hmeq
      -- `m` is an integral multiple of `cb.h • cb.c`
      have hNZconj : NZ (Ah l j) = U * NZ (Ah k i) * invMat U := by
        rw [hij, NZ_conj hU]
      have hmem' : m ∈ latImg (rankOne cb.c.toFun cb.w.toFun) := by
        rw [← hNB, hNZconj]
        exact hmem
      have hcbl : cb.c ≠ V3.zero := by
        intro hc0
        rw [hc0] at hdotl
        simp [V3.dot, V3.zero] at hdotl
      have hcbl_ne : cb.c.toFun ≠ 0 := by
        intro h0
        have hz : toRealV cb.c = 0 := by
          funext i
          have := congrFun h0 i
          simpa [toRealV, toRVec, V3.toFun] using this
        exact toRealV_ne_zero' hcbl hz
      obtain ⟨x, hx⟩ := mem_latImg.mp hmem'
      obtain ⟨t, ht⟩ := latImg_rankOne (c := cb.c.toFun) (w := cb.w.toFun) hcbl_ne
        (v := (rankOne cb.c.toFun cb.w.toFun).mulVec x) ⟨x, mulVec_toRVec _ x⟩
      have hgh : (gcdIVec cb.w.toFun : Int) = (cb.h : Int) := by
        have := hgcdl
        rw [← gcdV_toFun] at this
        exact_mod_cast this
      have hmval : m = ((t : ℝ) * ((cb.h : Int) : ℝ)) • toRealV cb.c := by
        rw [← hx, mulVec_toRVec, ht, toRVec_smul, hgh]
        congr 1
        push_cast
        ring
      have hX : toRealV cb.c = (toRMat U).mulVec (toRealV ca.c) := by
        rw [hcc, toRealV_toV3]
        exact (mulVec_toRVec U ca.c.toFun).symm
      have hXeq : (cb.j : ℝ) • toRealV cb.c
          = (ca.j : ℝ) • toRealV cb.c + ((t : ℝ) * ((cb.h : Int) : ℝ)) • toRealV cb.c := by
        rw [← hval, hmeq', hvak, Matrix.mulVec_smul, ← hX, hmval]
      -- cancel the nonzero vector
      obtain ⟨i0, hi0⟩ := Function.ne_iff.mp (toRealV_ne_zero' hcbl)
      have hcoord := congrFun hXeq i0
      simp only [Pi.add_apply, Pi.smul_apply] at hcoord
      have hscal : (cb.j : ℝ) = (ca.j : ℝ) + (t : ℝ) * ((cb.h : Int) : ℝ) := by
        have h1 : ((cb.j : ℝ) - ((ca.j : ℝ) + (t : ℝ) * ((cb.h : Int) : ℝ)))
            * (toRealV cb.c i0) = 0 := by
          linear_combination hcoord
        have h2 := (mul_eq_zero.mp h1).resolve_right hi0
        linarith
      have hjint : cb.j = ca.j + t * (cb.h : Int) := by
        exact_mod_cast hscal
      have hdvdj : (cb.h : Int) ∣ cb.j - ca.j := by
        refine ⟨t, ?_⟩
        rw [hjint]; ring
      -- the value
      show some (ca.ord, ca.h, ca.j % (ca.h : Int)) = some (cb.ord, cb.h, cb.j % (cb.h : Int))
      have h3' : ca.j % (ca.h : Int) = cb.j % (cb.h : Int) := by
        rw [hh]
        exact misc_bridges.2 (by rw [← hh]; exact hhl) (by rw [← hh]; exact hdvdj)
      rw [h3', hordEq.symm, hh.symm]

end Work.SGsep.Hand
