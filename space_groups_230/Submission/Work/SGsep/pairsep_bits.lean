import Mathlib
import Submission.Work.SGsep.PairAux
import Submission.Work.SGsep.PairAux2
import Submission.Work.SGsep.elem_separates

namespace Work.SGsep

open Work.SG
open Work.SGsep.PSep
open Classical

/-- For a `Bool` `b` and a proposition `P`: if `b = true` is equivalent to `P`, then
`b` is the explicit `Bool` encoding `if P then true else false` of `P`. -/
theorem bool_eq_ite_true_false {b : Bool} {P : Prop} (h : (b = true) ↔ P) :
    b = (if P then true else false) := by
  by_cases hP : P
  · rw [if_pos hP]; exact h.mpr hP
  · rw [if_neg hP]
    cases b with
    | true => exact absurd (h.mp rfl) hP
    | false => rfl

theorem sub_one_toIMat (k : Fin 230) (i : ℕ) :
    (Data.M3.sub (elM k i) Data.M3.one).toIMat = elI k i - 1 := by
  rw [PSep.toIMat_sub, Data.M3.toIMat_one]; rfl

theorem add_one_toIMat (k : Fin 230) (i : ℕ) :
    (Data.M3.add (elM k i) Data.M3.one).toIMat = elI k i + 1 := by
  rw [PSep.toIMat_add, Data.M3.toIMat_one]; rfl

/-- Soundness of the pair certificate `Data.PairCert.chk k p`: the stored six-bit pattern
`p.bits = [p.fix.bit, p.afix.bit] ++ p.tf.map Data.TfCert.bit` is the semantic pattern
`pairBits k (elI k p.i) (elI k p.j)`. -/
theorem pairsep_bits (k : Fin 230) (p : Data.PairCert) (hk : TauOnTable k) (hi : p.i < pn k)
    (hj : p.j < pn k) (h : Data.PairCert.chk k p = true) (hordi : (elM k p.i).ord ≠ 0)
    (hvofi : vA (sgTau k) (elI k p.i) = toRV (vOfK k p.i))
    (htf : ∀ (CX CY : Data.M3) (c : Data.TfCert), Data.TfCert.chk CX.cols CY.cols c = true →
      (c.bit = true ↔ latImg CX.toIMat ≤ latImg CY.toIMat)) :
    p.bits = pairBits k (elI k p.i) (elI k p.j) := by
  simp only [Data.PairCert.chk] at h
  simp only [← elM_def] at h
  generalize hBm1 : (elM k p.j).sub Data.M3.one = Bm1 at h
  generalize hBp1 : (elM k p.j).add Data.M3.one = Bp1 at h
  generalize hAm1 : (elM k p.i).sub Data.M3.one = Am1 at h
  generalize hAp1 : (elM k p.i).add Data.M3.one = Ap1 at h
  generalize hN3 : Data.normOf (elM k p.i) = N3 at h
  generalize hv0 : Data.vOf (↑k) p.i = v0 at h
  obtain ⟨h6, ht3b⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨h5, ht2b⟩ := Bool.and_eq_true_iff.mp h6
  obtain ⟨h4, ht1b⟩ := Bool.and_eq_true_iff.mp h5
  obtain ⟨h3, ht0b⟩ := Bool.and_eq_true_iff.mp h4
  obtain ⟨h2, hlenb⟩ := Bool.and_eq_true_iff.mp h3
  obtain ⟨hfixb, hafixb⟩ := Bool.and_eq_true_iff.mp h2
  have hlen4 : p.tf.length = 4 := beq_iff_eq.mp hlenb
  have hBm1I : Bm1.toIMat = elI k p.j - 1 := by rw [← hBm1]; exact sub_one_toIMat k p.j
  have hBp1I : Bp1.toIMat = elI k p.j + 1 := by rw [← hBp1]; exact add_one_toIMat k p.j
  have hAm1I : Am1.toIMat = elI k p.i - 1 := by rw [← hAm1]; exact sub_one_toIMat k p.i
  have hAp1I : Ap1.toIMat = elI k p.i + 1 := by rw [← hAp1]; exact add_one_toIMat k p.i
  have hN3I : N3.toIMat = NZ (elI k p.i) := by
    rw [← hN3, PSep.normOf_toIMat (elM k p.i) hordi]; rfl
  have hv0' : toRV v0 = vA (sgTau k) (elI k p.i) := by
    rw [← hv0]; exact hvofi.symm
  -- the `fix` bit
  have hfixl : p.fix.bit =
      (if fixBit k (elI k p.i) (elI k p.j) then true else false) := by
    apply bool_eq_ite_true_false
    have hfix' : Data.SpanCert.chk ((Bm1.mul N3).cols) (Bm1.mulV v0) p.fix = true := by
      rw [PSep.cols_mulV]; exact hfixb
    have hsp := PSep.spanCert_bit (Bm1.mul N3) (Bm1.mulV v0) p.fix hfix'
    have hmv : toRV (Bm1.mulV v0) =
        (toRMat (elI k p.j) - 1).mulVec (vA (sgTau k) (elI k p.i)) := by
      rw [PSep.mulV_toRV, hBm1I, PSep.toRMat_sub, PSep.toRMat_one, hv0']
    have hlat : (Bm1.mul N3).toIMat = (elI k p.j - 1) * NZ (elI k p.i) := by
      rw [Data.M3.toIMat_mul, hBm1I, hN3I]
    unfold fixBit
    rw [← hmv, ← hlat]
    exact hsp
  -- the `afix` bit
  have hafixl : p.afix.bit =
      (if afixBit k (elI k p.i) (elI k p.j) then true else false) := by
    apply bool_eq_ite_true_false
    have hafix' : Data.SpanCert.chk ((Bp1.mul N3).cols) (Bp1.mulV v0) p.afix = true := by
      rw [PSep.cols_mulV]; exact hafixb
    have hsp := PSep.spanCert_bit (Bp1.mul N3) (Bp1.mulV v0) p.afix hafix'
    have hmv : toRV (Bp1.mulV v0) =
        (toRMat (elI k p.j) + 1).mulVec (vA (sgTau k) (elI k p.i)) := by
      rw [PSep.mulV_toRV, hBp1I, PSep.toRMat_add, PSep.toRMat_one, hv0']
    have hlat : (Bp1.mul N3).toIMat = (elI k p.j + 1) * NZ (elI k p.i) := by
      rw [Data.M3.toIMat_mul, hBp1I, hN3I]
    unfold afixBit
    rw [← hmv, ← hlat]
    exact hsp
  -- the four `tf` bits
  have ht0l : (p.tf.getD 0 default).bit =
      (if latImg (elI k p.i - 1) ≤ latImg (elI k p.j - 1) then true else false) := by
    apply bool_eq_ite_true_false
    have hh := htf Am1 Bm1 (p.tf.getD 0 default) ht0b
    rw [hAm1I, hBm1I] at hh
    exact hh
  have ht1l : (p.tf.getD 1 default).bit =
      (if latImg (elI k p.i + 1) ≤ latImg (elI k p.j + 1) then true else false) := by
    apply bool_eq_ite_true_false
    have hh := htf Ap1 Bp1 (p.tf.getD 1 default) ht1b
    rw [hAp1I, hBp1I] at hh
    exact hh
  have ht2l : (p.tf.getD 2 default).bit =
      (if latImg (elI k p.i - 1) ≤ latImg (elI k p.j + 1) then true else false) := by
    apply bool_eq_ite_true_false
    have hh := htf Am1 Bp1 (p.tf.getD 2 default) ht2b
    rw [hAm1I, hBp1I] at hh
    exact hh
  have ht3l : (p.tf.getD 3 default).bit =
      (if latImg (elI k p.i + 1) ≤ latImg (elI k p.j - 1) then true else false) := by
    apply bool_eq_ite_true_false
    have hh := htf Ap1 Bm1 (p.tf.getD 3 default) ht3b
    rw [hAp1I, hBm1I] at hh
    exact hh
  -- assemble
  have hbits : p.bits = [p.fix.bit, p.afix.bit, (p.tf.getD 0 default).bit,
      (p.tf.getD 1 default).bit, (p.tf.getD 2 default).bit, (p.tf.getD 3 default).bit] := by
    simp only [Data.PairCert.bits]
    rw [PSep.map_eq_map_getD p.tf Data.TfCert.bit default, hlen4]
    rfl
  rw [hbits]
  simp only [pairBits]
  rw [hfixl, hafixl, ht0l, ht1l, ht2l, ht3l]

end Work.SGsep
