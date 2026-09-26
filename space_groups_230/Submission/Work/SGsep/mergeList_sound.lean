import Mathlib
import Submission.Work.SG.SGsepDefs
import Submission.Work.SGsep.table_facts
import Submission.Work.SGsep.bmats_dvd

namespace Work.SGsep

open Work.SG
open Work.SG.Data

set_option maxHeartbeats 1600000
set_option maxRecDepth 1000000

/-! ## Auxiliary algebra used by `mergeList_sound` -/

namespace MergeAux

lemma divfun_eq_smul (n : ℝ) (v : Data.V3) :
    (fun t => ((v.toFun t : ℤ) : ℝ) / n) = n⁻¹ • toRVec v.toFun := by
  funext t
  simp [toRVec, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]

lemma mulVec_map_cast (A : IMat) (v : IVec) :
    (A.map (Int.cast : ℤ → ℝ)).mulVec (toRVec v) = toRVec (A.mulVec v) :=
  mulVec_toRVec A v

lemma smul_sq_inv_smul (n : ℝ) (hn : n ≠ 0) (X : Fin 3 → ℝ) :
    n^2 • (n⁻¹ • X) = n • X := by
  rw [smul_smul]
  congr 1
  rw [sq, mul_assoc, mul_inv_cancel₀ hn, mul_one]

lemma smul_sq_inv_smul_self (n : ℝ) (hn : n ≠ 0) (X : Fin 3 → ℝ) :
    n^2 • (n^2)⁻¹ • X = X := by
  rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero 2 hn), one_smul]

lemma mulV_sub (A : Data.M3) (u v : Data.V3) :
    A.mulV (Data.V3.sub u v) = Data.V3.sub (A.mulV u) (A.mulV v) := by
  apply Data.V3.toFun_injective
  rw [← Data.M3.toIMat_mulV, Data.V3.toFun_sub, Matrix.mulVec_sub,
    Data.M3.toIMat_mulV, Data.M3.toIMat_mulV, Data.V3.toFun_sub]

/-- Divisibility extraction: a `V3` all of whose coordinates are divisible by `m` is a
scalar multiple of an integer vector. -/
lemma v3_dvd_toFun {m : ℤ} {v : Data.V3} (h : Data.V3.dvd m v = true) :
    ∃ w : Fin 3 → ℤ, v.toFun = m • w := by
  simp only [Data.V3.dvd, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hx, hy⟩, hz⟩ := h
  have key : ∀ a : ℤ, a % m = 0 → a = m * (a / m) := fun a ha => by
    rw [mul_comm, Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero ha)]
  have ht : ∀ t : Fin 3, v.toFun t % m = 0 := by
    intro t
    fin_cases t <;> simp only [Data.V3.toFun]
    · exact hx
    · exact hy
    · exact hz
  refine ⟨fun t => v.toFun t / m, ?_⟩
  funext t
  simp only [Pi.smul_apply, smul_eq_mul]
  exact key (v.toFun t) (ht t)

/-- Unpacking of `Data.ConjCert.chk`. -/
theorem chk_elim {D : Data.ArithData} {y : List ℤ} {c : Data.ConjCert}
    (h : Data.ConjCert.chk D y c = true) :
    (Data.M3.mul c.U c.Uinv = Data.M3.one ∧ c.img.length = D.n) ∧
    ∀ i, i < D.n →
      c.img.getD i 0 < D.n ∧
      Data.M3.mul (Data.M3.mul c.U (D.elems.getD i Data.M3.one)) c.Uinv
        = D.elems.getD (c.img.getD i 0) Data.M3.one ∧
      Data.V3.dvd (D.n * D.n)
        (Data.V3.add (Data.V3.sub (Data.V3.sub
          (Data.V3.smul D.n ((Data.repZ.getD c.k []).getD (c.img.getD i 0) Data.V3.zero))
          (Data.V3.smul D.n (Data.M3.mulV c.U (Data.applyB ((Data.bmats D).getD i []) y))))
          c.sig)
          (Data.M3.mulV (D.elems.getD (c.img.getD i 0) Data.M3.one) c.sig)) := by
  simp only [Data.ConjCert.chk, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, beq_iff_eq] at h
  refine ⟨h.1, fun i hi => ?_⟩
  have h2 := h.2 i (List.mem_range.mpr hi)
  exact ⟨h2.1.1, h2.1.2, h2.2⟩

theorem repArith_elems_nodup (k : Fin 230) : (Data.repArith k.val).elems.Nodup := by
  obtain ⟨h1, _⟩ := of_decide_eq_true (List.all_eq_true.mp arithData_elems_nodup_len
    (Data.repClass k.val) (List.mem_range.mpr (repClass_lt k)))
  simpa [Data.repArith] using h1

theorem repArith_elems_length (k : Fin 230) :
    (Data.repArith k.val).elems.length = (Data.repArith k.val).n := by
  obtain ⟨_, h2⟩ := of_decide_eq_true (List.all_eq_true.mp arithData_elems_nodup_len
    (Data.repClass k.val) (List.mem_range.mpr (repClass_lt k)))
  simpa [Data.repArith] using h2

end MergeAux

/-- The element set encoded by an arithmetic-class table. -/
def ElSet (D : Data.ArithData) : Set IMat := {A | ∃ e ∈ D.elems, A = e.toIMat}

/-- Extraction of the normaliser data from a `Data.ConjCert` check. -/
theorem conjCert_facts {D : Data.ArithData} {c : Data.ConjCert} {y : List ℤ}
    (hnd : D.elems.Nodup) (hlen : D.elems.length = D.n)
    (hchk : Data.ConjCert.chk D y c = true) :
    (Data.M3.toIMat c.U * Data.M3.toIMat c.Uinv = 1) ∧
    ((Data.M3.toIMat c.U)⁻¹ = Data.M3.toIMat c.Uinv) ∧
    (Data.M3.toIMat c.Uinv * Data.M3.toIMat c.U = 1) ∧
    (∀ i, i < D.n →
      c.img.getD i 0 < D.n ∧
      Data.M3.toIMat c.U * (D.elems.getD i Data.M3.one).toIMat * Data.M3.toIMat c.Uinv
        = (D.elems.getD (c.img.getD i 0) Data.M3.one).toIMat) ∧
    (∀ j, j < D.n → ∃ i, i < D.n ∧ c.img.getD i 0 = j) := by
  obtain ⟨⟨hmul, hlenimg⟩, hall⟩ := MergeAux.chk_elim hchk
  have hUU : Data.M3.toIMat c.U * Data.M3.toIMat c.Uinv = 1 := by
    have h := congrArg Data.M3.toIMat hmul
    rwa [Data.M3.toIMat_mul, Data.M3.toIMat_one] at h
  have hdet : IsUnit (Data.M3.toIMat c.U).det := by
    have h1 : (Data.M3.toIMat c.U).det * (Data.M3.toIMat c.Uinv).det = 1 := by
      rw [← Matrix.det_mul, hUU, Matrix.det_one]
    exact isUnit_iff_exists.mpr ⟨_, h1, by rw [mul_comm]; exact h1⟩
  have hUinv_eq : Data.M3.toIMat c.Uinv = invMat (Data.M3.toIMat c.U) := by
    calc Data.M3.toIMat c.Uinv
        = 1 * Data.M3.toIMat c.Uinv := (one_mul _).symm
      _ = (invMat (Data.M3.toIMat c.U) * Data.M3.toIMat c.U) * Data.M3.toIMat c.Uinv := by
            rw [invMat_mul hdet]
      _ = invMat (Data.M3.toIMat c.U) * (Data.M3.toIMat c.U * Data.M3.toIMat c.Uinv) := by
            rw [Matrix.mul_assoc]
      _ = invMat (Data.M3.toIMat c.U) * 1 := by rw [hUU]
      _ = invMat (Data.M3.toIMat c.U) := mul_one _
  have hUinvU : Data.M3.toIMat c.Uinv * Data.M3.toIMat c.U = 1 := by
    rw [hUinv_eq, invMat_mul hdet]
  have hinv : (Data.M3.toIMat c.U)⁻¹ = Data.M3.toIMat c.Uinv :=
    Matrix.inv_eq_right_inv hUU
  have hstep : ∀ i, i < D.n →
      c.img.getD i 0 < D.n ∧
      Data.M3.toIMat c.U * (D.elems.getD i Data.M3.one).toIMat * Data.M3.toIMat c.Uinv
        = (D.elems.getD (c.img.getD i 0) Data.M3.one).toIMat := by
    intro i hi
    obtain ⟨hlt, heq, _⟩ := hall i hi
    refine ⟨hlt, ?_⟩
    have h := congrArg Data.M3.toIMat heq
    rwa [Data.M3.toIMat_mul, Data.M3.toIMat_mul] at h
  have cancel1 : ∀ X : IMat, Data.M3.toIMat c.Uinv * (Data.M3.toIMat c.U * X) = X := by
    intro X
    rw [← Matrix.mul_assoc, hUinvU, Matrix.one_mul]
  have key : ∀ A : IMat, Data.M3.toIMat c.Uinv
      * (Data.M3.toIMat c.U * A * Data.M3.toIMat c.Uinv) * Data.M3.toIMat c.U = A := by
    intro A
    rw [← Matrix.mul_assoc (Data.M3.toIMat c.Uinv) (Data.M3.toIMat c.U * A)
      (Data.M3.toIMat c.Uinv), cancel1 A, Matrix.mul_assoc A (Data.M3.toIMat c.Uinv)
      (Data.M3.toIMat c.U), hUinvU, Matrix.mul_one]
  have hinj : Function.Injective (fun i : Fin D.n => c.img.getD i.val 0) := by
    intro i i' h
    have hi := i.isLt
    have hi' := i'.isLt
    have hAi := (hstep i.val hi).2
    have hAi' := (hstep i'.val hi').2
    have h' : c.img.getD i.val 0 = c.img.getD i'.val 0 := h
    have hmid : Data.M3.toIMat c.U * (D.elems.getD i.val Data.M3.one).toIMat
          * Data.M3.toIMat c.Uinv
        = Data.M3.toIMat c.U * (D.elems.getD i'.val Data.M3.one).toIMat
          * Data.M3.toIMat c.Uinv := by
      rw [hAi, hAi', h']
    have hA : (D.elems.getD i.val Data.M3.one).toIMat
        = (D.elems.getD i'.val Data.M3.one).toIMat := by
      rw [← key ((D.elems.getD i.val Data.M3.one).toIMat), hmid,
        key ((D.elems.getD i'.val Data.M3.one).toIMat)]
    have hget := Data.M3.toIMat_injective hA
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hi),
        List.getD_eq_getElem _ _ (by rw [hlen]; exact hi')] at hget
    exact Fin.ext ((hnd.getElem_inj_iff).mp hget)
  have hsurj : ∀ j, j < D.n → ∃ i, i < D.n ∧ c.img.getD i 0 = j := by
    let f : Fin D.n → Fin D.n := fun i => ⟨c.img.getD i.val 0, (hstep i.val i.isLt).1⟩
    have hfinj : Function.Injective f := by
      intro a b hab
      exact hinj (by simpa [f] using congrArg Fin.val hab)
    intro j hj
    obtain ⟨i, hi⟩ := (Finite.injective_iff_surjective (f := f)).mp hfinj ⟨j, hj⟩
    exact ⟨i.val, i.isLt, by simpa [f] using congrArg Fin.val hi⟩
  exact ⟨hUU, hinv, hUinvU, hstep, hsurj⟩

/-- The set-membership half of `IntEquiv` for a conjugation certificate. -/
theorem set_part {D : Data.ArithData} {c : Data.ConjCert} {y : List ℤ}
    (hnd : D.elems.Nodup) (hlen : D.elems.length = D.n)
    (hchk : Data.ConjCert.chk D y c = true) :
    ∀ A : IMat, A ∈ ElSet D ↔ ∃ B ∈ ElSet D,
      A = Data.M3.toIMat c.U * B * (Data.M3.toIMat c.U)⁻¹ := by
  obtain ⟨hUU, hinv, hUinvU, hstep, hsurj⟩ := conjCert_facts hnd hlen hchk
  intro A
  simp only [ElSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨e, he, rfl⟩
    obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.mp he
    have hidn : i < D.n := by rw [← hlen]; exact hi
    have hgeti : D.elems.getD i Data.M3.one = e := by
      rw [List.getD_eq_getElem _ _ hi, hie]
    obtain ⟨i', hi', himg⟩ := hsurj i hidn
    refine ⟨(D.elems.getD i' Data.M3.one).toIMat, ⟨D.elems.getD i' Data.M3.one, ?_, rfl⟩, ?_⟩
    · rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hi')]
      exact List.getElem_mem _
    · rw [hinv, (hstep i' hi').2, himg, hgeti]
  · rintro ⟨B, ⟨e, he, rfl⟩, hA⟩
    obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.mp he
    have hidn : i < D.n := by rw [← hlen]; exact hi
    have hgeti : D.elems.getD i Data.M3.one = e := by
      rw [List.getD_eq_getElem _ _ hi, hie]
    refine ⟨D.elems.getD (c.img.getD i 0) Data.M3.one, ?_, ?_⟩
    · rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact (hstep i hidn).1)]
      exact List.getElem_mem _
    · rw [hA, ← hgeti, hinv, ← (hstep i hidn).2]

/-- The cocycle half of `IntEquiv` for a conjugation certificate, given the `bmats`
propagation of the certified cocycle. -/
theorem cocycle_part {D : Data.ArithData} {c : Data.ConjCert} {k l : Fin 230} {y : List ℤ}
    (hchk : Data.ConjCert.chk D y c = true)
    (hlen : D.elems.length = D.n)
    (hinv : (Data.M3.toIMat c.U)⁻¹ = Data.M3.toIMat c.Uinv)
    (hstep : ∀ i, i < D.n →
      Data.M3.toIMat c.U * (D.elems.getD i Data.M3.one).toIMat * Data.M3.toIMat c.Uinv
        = (D.elems.getD (c.img.getD i 0) Data.M3.one).toIMat)
    (hk : ∀ i, i < D.n →
      sgTau k (D.elems.getD i Data.M3.one).toIMat
        = fun t => (((Data.repZ.getD k.val []).getD i Data.V3.zero).toFun t : ℝ) / (D.n : ℝ))
    (hl : ∀ i, i < D.n →
      sgTau l (D.elems.getD i Data.M3.one).toIMat
        = fun t => (((Data.repZ.getD l.val []).getD i Data.V3.zero).toFun t : ℝ) / (D.n : ℝ))
    (hck : l.val = c.k)
    (hbm : ∀ i, i < D.n →
      Data.V3.dvd (D.n : ℤ)
        (Data.V3.sub (Data.applyB ((Data.bmats D).getD i []) y)
          ((Data.repZ.getD k.val []).getD i Data.V3.zero)) = true)
    (hpos : 0 < D.n) :
    ∀ A : IMat, (∃ e ∈ D.elems, A = e.toIMat) → ∃ m : Fin 3 → ℤ,
      sgTau l (Data.M3.toIMat c.U * A * (Data.M3.toIMat c.U)⁻¹)
        = ((Data.M3.toIMat c.U).map (Int.cast : ℤ → ℝ)).mulVec (sgTau k A)
          + (fun t => ((c.sig.toFun t : ℤ) : ℝ) / (D.n : ℝ) ^ 2)
          - ((Data.M3.toIMat c.U * A * (Data.M3.toIMat c.U)⁻¹).map (Int.cast : ℤ → ℝ)).mulVec
              (fun t => ((c.sig.toFun t : ℤ) : ℝ) / (D.n : ℝ) ^ 2)
          + intVec m := by
  intro A hA
  obtain ⟨e, he, rfl⟩ := hA
  obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.mp he
  have hidn : i < D.n := by rw [← hlen]; exact hi
  have hgeti : D.elems.getD i Data.M3.one = e := by
    rw [List.getD_eq_getElem _ _ hi, hie]
  obtain ⟨_, hall⟩ := MergeAux.chk_elim hchk
  obtain ⟨hjlt, hnode, hdvd⟩ := hall i hidn
  rw [← hck] at hdvd
  obtain ⟨w, hw⟩ := MergeAux.v3_dvd_toFun hdvd
  obtain ⟨u, hu⟩ := MergeAux.v3_dvd_toFun (hbm i hidn)
  refine ⟨w + (Data.M3.toIMat c.U).mulVec u, ?_⟩
  rw [← hgeti, hinv, hstep i hidn, hk i hidn, hl (c.img.getD i 0) hjlt]
  have hn0 : (D.n : ℝ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    exact ne_of_gt hpos
  have hn2 : (D.n : ℝ)^2 ≠ 0 := pow_ne_zero 2 hn0
  have hUrel : (Data.M3.mulV c.U (Data.applyB ((Data.bmats D).getD i []) y)).toFun
        - (Data.M3.mulV c.U ((Data.repZ.getD k.val []).getD i Data.V3.zero)).toFun
      = (D.n : ℤ) • ((Data.M3.toIMat c.U).mulVec u) := by
    rw [← Data.V3.toFun_sub, ← MergeAux.mulV_sub, ← Data.M3.toIMat_mulV, hu,
      Matrix.mulVec_smul]
  have hAB : toRVec ((Data.M3.mulV c.U (Data.applyB ((Data.bmats D).getD i []) y)).toFun)
        - toRVec ((Data.M3.mulV c.U ((Data.repZ.getD k.val []).getD i Data.V3.zero)).toFun)
      = (D.n : ℝ) • toRVec ((Data.M3.toIMat c.U).mulVec u) := by
    simp only [← toRVec_sub, hUrel, toRVec_smul, Int.cast_natCast]
  have hVc : toRVec ((Data.V3.add (Data.V3.sub (Data.V3.sub
        (Data.V3.smul (D.n : ℤ) ((Data.repZ.getD l.val []).getD (c.img.getD i 0) Data.V3.zero))
        (Data.V3.smul (D.n : ℤ) (Data.M3.mulV c.U (Data.applyB ((Data.bmats D).getD i []) y))))
        c.sig) (Data.M3.mulV (D.elems.getD (c.img.getD i 0) Data.M3.one) c.sig)).toFun)
      = (D.n : ℝ) • toRVec ((Data.repZ.getD l.val []).getD (c.img.getD i 0) Data.V3.zero).toFun
        - (D.n : ℝ) • toRVec ((Data.M3.mulV c.U (Data.applyB ((Data.bmats D).getD i []) y)).toFun)
        - toRVec c.sig.toFun
        + toRVec ((Data.M3.mulV (D.elems.getD (c.img.getD i 0) Data.M3.one) c.sig).toFun) := by
    simp only [Data.V3.toFun_add, Data.V3.toFun_sub, Data.V3.toFun_smul,
      toRVec_add, toRVec_sub, toRVec_smul, Int.cast_natCast]
  have t1 : (D.n : ℝ)^2 • toRVec w
      = (D.n : ℝ) • toRVec ((Data.repZ.getD l.val []).getD (c.img.getD i 0) Data.V3.zero).toFun
        - (D.n : ℝ) • toRVec ((Data.M3.mulV c.U (Data.applyB ((Data.bmats D).getD i []) y)).toFun)
        - toRVec c.sig.toFun
        + toRVec ((Data.M3.mulV (D.elems.getD (c.img.getD i 0) Data.M3.one) c.sig).toFun) := by
    have hcast : (((D.n : ℤ) * (D.n : ℤ) : ℤ) : ℝ) = (D.n : ℝ)^2 := by
      push_cast; ring
    have hA2 : (D.n : ℝ)^2 • toRVec w = toRVec ((Data.V3.add (Data.V3.sub (Data.V3.sub
        (Data.V3.smul (D.n : ℤ) ((Data.repZ.getD l.val []).getD (c.img.getD i 0) Data.V3.zero))
        (Data.V3.smul (D.n : ℤ) (Data.M3.mulV c.U (Data.applyB ((Data.bmats D).getD i []) y))))
        c.sig) (Data.M3.mulV (D.elems.getD (c.img.getD i 0) Data.M3.one) c.sig)).toFun) := by
      rw [hw, toRVec_smul, hcast]
    rw [hA2, hVc]
  have t2 : (D.n : ℝ)^2 • toRVec ((Data.M3.toIMat c.U).mulVec u)
      = (D.n : ℝ) • toRVec ((Data.M3.mulV c.U (Data.applyB ((Data.bmats D).getD i []) y)).toFun)
        - (D.n : ℝ) • toRVec ((Data.M3.mulV c.U ((Data.repZ.getD k.val []).getD i Data.V3.zero)).toFun) := by
    have h1 : (D.n : ℝ)^2 • toRVec ((Data.M3.toIMat c.U).mulVec u)
        = (D.n : ℝ) • ((D.n : ℝ) • toRVec ((Data.M3.toIMat c.U).mulVec u)) := by
      rw [smul_smul]; congr 1; ring
    rw [h1, ← hAB, smul_sub]
  have hE : (D.n : ℝ)^2 • toRVec (w + (Data.M3.toIMat c.U).mulVec u)
      = (D.n : ℝ) • toRVec ((Data.repZ.getD l.val []).getD (c.img.getD i 0) Data.V3.zero).toFun
        - (D.n : ℝ) • toRVec ((Data.M3.mulV c.U ((Data.repZ.getD k.val []).getD i Data.V3.zero)).toFun)
        - toRVec c.sig.toFun
        + toRVec ((Data.M3.mulV (D.elems.getD (c.img.getD i 0) Data.M3.one) c.sig).toFun) := by
    rw [toRVec_add, smul_add, t1, t2]
    abel
  have hZa := MergeAux.divfun_eq_smul (D.n : ℝ) ((Data.repZ.getD k.val []).getD i Data.V3.zero)
  have hZb := MergeAux.divfun_eq_smul (D.n : ℝ) ((Data.repZ.getD l.val []).getD (c.img.getD i 0) Data.V3.zero)
  have hs := MergeAux.divfun_eq_smul ((D.n : ℝ)^2) c.sig
  have hvec : intVec (w + (Data.M3.toIMat c.U).mulVec u)
      = toRVec (w + (Data.M3.toIMat c.U).mulVec u) := rfl
  apply (smul_right_injective (Fin 3 → ℝ) hn2)
  simp only []
  simp only [hZb, hZa, hs, hvec, smul_add, smul_sub, Matrix.mulVec_smul,
    MergeAux.smul_sq_inv_smul (D.n : ℝ) hn0, MergeAux.smul_sq_inv_smul_self (D.n : ℝ) hn0,
    MergeAux.mulVec_map_cast, Data.M3.toIMat_mulV, hE]
  abel

/-! ## Reading the list of merges -/

/-- Membership in `Data.sameClassPairs` forces equal arithmetic-class index. -/
theorem mem_sameClassPairs {a b : ℕ} (h : (a, b) ∈ Data.sameClassPairs) :
    Data.repClass a = Data.repClass b := by
  simp only [Data.sameClassPairs] at h
  obtain ⟨x, hx, h2⟩ := List.mem_flatMap.mp h
  obtain ⟨l, hl, hlab⟩ := List.mem_map.mp h2
  rw [List.mem_filter] at hl
  have hcon := hl.2
  simp only [Bool.and_eq_true, beq_iff_eq] at hcon
  obtain ⟨hx1, hx2⟩ := (Prod.mk.injEq x l a b).mp hlab
  rw [hx1, hx2] at hcon
  exact hcon.2

/-- Positivity of the order of an arithmetic-class table (finite kernel check). -/
theorem repArith_n_pos (k : Fin 230) : 0 < (Data.repArith k.val).n := by
  have h : (List.range 230).all (fun k => decide (0 < (Data.repArith k).n)) = true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp h k.val (List.mem_range.mpr k.isLt))

end Work.SGsep

namespace Work.SGsep

open Work.SG
open Work.SG.Data

theorem mergeList_sound (k l : Fin 230) (c : Data.ConjCert)
    (hk : TauOnTable k) (hl : TauOnTable l)
    (hc : ((k : ℕ), c) ∈ Data.mergeList) (hck : l.val = c.k) :
    ∃ s : Fin 3 → ℝ, IntEquiv (arithRep (sgArith k)) (sgTau k)
      (arithRep (sgArith l)) (sgTau l) (Data.M3.toIMat c.U) s := by
  obtain ⟨hmap, hall⟩ := Data.mergeList_chk
  have hmem : ((k.val, c) : ℕ × Data.ConjCert) ∈ Data.mergeList := hc
  have hall' := List.all_eq_true.mp hall (k.val, c) hmem
  simp only [Bool.and_eq_true, beq_iff_eq] at hall'
  obtain ⟨hdet, hchk⟩ := hall'
  have hfilt : (k.val, c.k) ∈
      List.filter (fun p : ℕ × ℕ => Data.affIdx p.1 == Data.affIdx p.2) Data.sameClassPairs := by
    rw [← hmap]
    exact List.mem_map.mpr ⟨(k.val, c), hc, rfl⟩
  have hmemSC : (k.val, c.k) ∈ Data.sameClassPairs := (List.mem_filter.mp hfilt).1
  have hclass0 : Data.repClass k.val = Data.repClass c.k := mem_sameClassPairs hmemSC
  have hDl : Data.repArith l.val = Data.repArith k.val := by
    simp only [Data.repArith, hck]
    rw [← hclass0]
  have hlen := MergeAux.repArith_elems_length k
  have hnd := MergeAux.repArith_elems_nodup k
  obtain ⟨hUU, hinv, hUinvU, hstep, hsurj⟩ := conjCert_facts hnd hlen hchk
  have hkk : ∀ i, i < (Data.repArith k.val).n →
      sgTau k ((Data.repArith k.val).elems.getD i Data.M3.one).toIMat
        = fun t => (((Data.repZ.getD k.val []).getD i Data.V3.zero).toFun t : ℝ)
            / ((Data.repArith k.val).n : ℝ) :=
    fun i hi => hk i hi
  have hll : ∀ i, i < (Data.repArith k.val).n →
      sgTau l ((Data.repArith k.val).elems.getD i Data.M3.one).toIMat
        = fun t => (((Data.repZ.getD l.val []).getD i Data.V3.zero).toFun t : ℝ)
            / ((Data.repArith k.val).n : ℝ) := by
    rw [← hDl]
    exact hl
  have harith_k : arithRep (sgArith k) = ElSet (Data.repArith k.val) := by
    simp only [ElSet]
    rw [arithRep_eq_data (sgArith k), ← repArith_eq_data_getD k]
  have harith_l : arithRep (sgArith l) = ElSet (Data.repArith k.val) := by
    simp only [ElSet]
    rw [arithRep_eq_data (sgArith l), ← repArith_eq_data_getD l, hDl]
  refine ⟨fun t => ((c.sig.toFun t : ℤ) : ℝ) / ((Data.repArith k.val).n : ℝ)^2, ?_, ?_⟩
  · rw [harith_l, harith_k]
    exact set_part hnd hlen hchk
  · intro B hB
    rw [harith_k] at hB
    exact cocycle_part hchk hlen hinv (fun i hi => (hstep i hi).2) hkk hll hck
      (bmats_dvd k) (repArith_n_pos k) B hB

end Work.SGsep
