import Mathlib
import Submission.Work.Idx.WPenBlk
import Submission.Work.Idx.WPenPsi
import Submission.Work.Idx.WPenRes
import Submission.Work.Idx.blkPenProjDefs
import Submission.Work.Idx.matPenProj_eval
import Submission.Work.Idx.wPsi_preSeq

/-!
# `Work.Idx.blkPenProj_preSeq_blocks` — the structural comparison of the two companion pencils

This file contains the proof of `Work.Idx.blkPenProj_preSeq_blocks`, the prepend step of Hatcher's
formula (2) at the level of the Riesz projections:

`(wInc n d)ᵀ * P(preSeq b) * wInc n d = P(b) + wUpdate n d b (wPsi X n d b)`,

where `P(c)` is the Riesz projection `(2πi)⁻¹ ∮_{|z|=1} (z·wBA n D + wBB n D c)⁻¹ · wBA n D dz` of
the companion pencil of the coefficient sequence `c`, `wInc n d` is the block inclusion of the first
`d+1` blocks into the first `d+2`, and the correction `wUpdate n d b (wPsi X n d b)` is the block
matrix with block `(k,i)` equal to `Ψ_{k-1} * b_i` (`Ψ = wPsi X n d b` the Fourier data of `b`).

The proof is self-contained and follows the route sketched in the file header of the original
statement:

* `BlkPen.sandwich_apply` — the sandwich `(wInc n d)ᵀ * M * wInc n d` is the restriction of `M` to
  the first `d+1` block indices, and `BlkPen.blkOf_mul_wBA_sandwich`, `BlkPen.blkOf_mul_wBA_last`
  compute the two sides blockwise after multiplying by `wBA`.
* `BlkPen.wd_preSeq`/`wde_preSeq` — the shift identity `wd'ᵢ = bᵢ + z · wdᵢ` for the tail sums of
  `preSeq X b` and of `b`.
* `BlkPen.bInv_preSeq` — the block comparison of the explicit inverses `wInv` (`Work.Idx.WPenRes`)
  of the `(d+2)`-pencil of `preSeq X b` and the `(d+1)`-pencil of `b`; this needs the shift
  `Ring.inverse (wQ (preSeq b) z) = z⁻¹ • Ring.inverse (wQ b z)` (`wQ_preSeq`, `ringInverse_smul`).
* `BlkPen.pointwise` — the pointwise (on the unit circle) identity
  `(wInc n d)ᵀ * pResA(big) z * wInc n d = pResA(small) z + wCorr z`, where `wCorr z` is the block
  matrix with block `(k,i)` equal to `z^{k-1} • (Ring.inverse (wQ b z) * b_i)`
  (`Work.Idx.wCorr`); it is proved by rewriting both factors with `wInv_eq_ringInverse` and
  comparing blocks.
* `BlkPen.circleIntegral_wCorr` — `∮_{|z|=1} wCorr z = 2πi • wUpdate n d b (wPsi X n d b)`, the
  entrywise computation of the integral of the correction, using
  `BlkPen.circleIntegral_apply` (the circle integral of a matrix-valued function is entrywise) and
  the definition of `wPsi`.
* `BlkPen.assembly` — the assembly: the circle integral commutes with the sandwich
  (`BlkPen.circleIntegral_sandwich`), the pointwise identity is integrated
  (`circleIntegral.integral_congr`, `circleIntegral.integral_add`), and the scalar `(2πi)⁻¹` is
  cancelled.

Matrix norms on `Matrix ι ι C(X, ℂ)` are the `L∞` operator norms (`Matrix.Norms.Operator`), the
structure used by `blkPenProj` (`Work.Idx.blkPenProj_eq`, inside `Work.Idx.blkPenProjDefs`), `wPsi`
and `Work.KT.Idx.penProj`.
-/

namespace Work.Idx
open Matrix MeasureTheory intervalIntegral
open scoped Topology Interval Matrix.Norms.Operator
noncomputable section
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
variable {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]

namespace BlkPen

/-! ## 1. The block inclusion `wInc` -/

lemma wInc_castSucc_left (n d : ℕ) (p : Fin (d + 1) × Fin n) :
    wInc (X := X) n d (Fin.castSucc p.1, p.2) p = 1 := by
  simp [wInc]

lemma wInc_eq_zero_of_ne (n d : ℕ) {p : Fin (d + 2) × Fin n} {q : Fin (d + 1) × Fin n}
    (h : p ≠ (Fin.castSucc q.1, q.2)) : wInc (X := X) n d p q = 0 := by
  simp only [wInc]
  split_ifs with hc
  · exact absurd (Prod.ext (Fin.ext (by simpa using hc.1)) hc.2) h
  · rfl

lemma sandwich_apply (n d : ℕ) (M : Matrix (Fin (d + 2) × Fin n) (Fin (d + 2) × Fin n) C(X, ℂ))
    (p q : Fin (d + 1) × Fin n) :
    (Matrix.transpose (wInc (X := X) n d) * M * wInc (X := X) n d) p q
      = M (Fin.castSucc p.1, p.2) (Fin.castSucc q.1, q.2) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.castSucc q.1, q.2)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.castSucc p.1, p.2)]
    · rw [Matrix.transpose_apply, wInc_castSucc_left, one_mul, wInc_castSucc_left, mul_one]
    · intro b _ hb
      rw [Matrix.transpose_apply, wInc_eq_zero_of_ne (n := n) (d := d) hb, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro b _ hb
    rw [wInc_eq_zero_of_ne (n := n) (d := d) hb, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma blkOf_sandwich (n d : ℕ) (M : Matrix (Fin (d + 2) × Fin n) (Fin (d + 2) × Fin n) C(X, ℂ))
    (k i : Fin (d + 1)) :
    blkOf (Matrix.transpose (wInc (X := X) n d) * M * wInc (X := X) n d) k i
      = blkOf M (Fin.castSucc k) (Fin.castSucc i) := by
  apply Matrix.ext
  intro a b
  exact sandwich_apply n d M (k, a) (i, b)

lemma blkOf_mul_wBA_sandwich (n d : ℕ)
    (M : Matrix (Fin (d + 2) × Fin n) (Fin (d + 2) × Fin n) C(X, ℂ)) (k i : Fin (d + 1)) :
    blkOf (Matrix.transpose (wInc (X := X) n d) * (M * wBA (A := C(X, ℂ)) n (d + 1))
        * wInc (X := X) n d) k i
      = blkOf M (Fin.castSucc k) (Fin.castSucc i) := by
  rw [blkOf_sandwich n d (M * wBA (A := C(X, ℂ)) n (d + 1)) k i, blkOf_mul,
    Finset.sum_eq_single (Fin.castSucc i)]
  · rw [blkOf_wBA, bA, if_pos rfl,
      if_neg (by have := (Fin.castSucc i).isLt; simp only [Fin.val_castSucc] at this ⊢; omega),
      mul_one]
  · intro j _ hj
    rw [blkOf_wBA, bA, if_neg hj, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma blkOf_mul_wBA_last (n D : ℕ)
    (N : Matrix (Fin (D + 1) × Fin n) (Fin (D + 1) × Fin n) C(X, ℂ)) (k i : Fin (D + 1)) :
    blkOf (N * wBA (A := C(X, ℂ)) n D) k i = if (i : ℕ) = D then 0 else blkOf N k i := by
  rw [blkOf_mul, Finset.sum_eq_single i]
  · rw [blkOf_wBA, bA, if_pos rfl]
    by_cases hi : (i : ℕ) = D
    · rw [if_pos hi, if_pos hi, mul_zero]
    · rw [if_neg hi, if_neg hi, mul_one]
  · intro j _ hj
    rw [blkOf_wBA, bA, if_neg hj, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ## 2. the shift of `wd` under prepending a zero coefficient -/

lemma preSeq_succ' (n d : ℕ) (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ))
    (s : Fin (d + 1)) : Work.KT.Idx.preSeq X b (Fin.succ s) = b s := by
  rw [Work.KT.Idx.preSeq_apply, dif_pos (by simp : 0 < ((Fin.succ s : Fin (d + 2)) : ℕ))]
  exact congrArg b (Fin.ext (by simp))

lemma wd_preSeq (n d : ℕ) (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) (z : ℂ)
    (i : Fin (d + 1)) :
    wd n (d + 1) (Work.KT.Idx.preSeq X b) z (Fin.castSucc i) = b i + z • wd n d b z i := by
  have hc : ∀ s : Fin (d + 1), (Fin.castSucc i : Fin (d + 2)) < Fin.succ s ↔ i ≤ s := by
    intro s; simp only [Fin.lt_def, Fin.le_def, Fin.val_castSucc, Fin.val_succ]; omega
  have hexp : ∀ s : Fin (d + 1), ((Fin.succ s : Fin (d + 2)) : ℕ) - 1 - (i : ℕ)
      = (s : ℕ) - (i : ℕ) := by
    intro s; simp only [Fin.val_succ]; omega
  have hL : wd n (d + 1) (Work.KT.Idx.preSeq X b) z (Fin.castSucc i)
      = ∑ s : Fin (d + 1), (if i ≤ s then z ^ ((s : ℕ) - (i : ℕ)) • b s else 0) := by
    rw [wd, Finset.sum_filter]
    simp only [Fin.val_castSucc]
    conv_lhs => rw [Fin.sum_univ_succ]
    rw [if_neg (Fin.not_lt_zero _), zero_add]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [hc s, hexp s, preSeq_succ' (X := X) n d b s]
  have hR : b i + z • wd n d b z i
      = b i + ∑ s : Fin (d + 1), (if i < s then z ^ ((s : ℕ) - (i : ℕ)) • b s else 0) := by
    congr 1
    rw [wd, Finset.sum_filter, Finset.smul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases h : i < s
    · rw [if_pos h, if_pos h, smul_smul, ← pow_succ',
        show ((s : ℕ) - 1 - (i : ℕ)) + 1 = (s : ℕ) - (i : ℕ) by omega]
    · rw [if_neg h, if_neg h, smul_zero]
  have hsplit : ∀ s : Fin (d + 1),
      (if i ≤ s then z ^ ((s : ℕ) - (i : ℕ)) • b s else 0)
        = (if s = i then b i else 0)
          + (if i < s then z ^ ((s : ℕ) - (i : ℕ)) • b s else 0) := by
    intro s
    rcases lt_trichotomy s i with h | h | h
    · rw [if_neg (not_le.mpr h), if_neg (ne_of_lt h), if_neg (not_lt.mpr (le_of_lt h)), zero_add]
    · subst h; simp
    · rw [if_pos (le_of_lt h), if_neg (ne_of_gt h), if_pos h, zero_add]
  have hbi : b i = ∑ s : Fin (d + 1), (if s = i then b i else 0) := by
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ i)]
  have hsum1 : (∑ s : Fin (d + 1), (if i ≤ s then z ^ ((s : ℕ) - (i : ℕ)) • b s else 0))
      = ∑ s : Fin (d + 1), ((if s = i then b i else 0)
          + (if i < s then z ^ ((s : ℕ) - (i : ℕ)) • b s else 0)) :=
    Finset.sum_congr rfl fun s _ => hsplit s
  rw [hL, hR, hbi, hsum1, Finset.sum_add_distrib]

lemma wde_preSeq (n d : ℕ) (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) (z : ℂ)
    (i : Fin (d + 1)) :
    wde n (d + 1) (Work.KT.Idx.preSeq X b) z (Fin.castSucc i) = b i + z • wd n d b z i := by
  rw [wde, if_neg (by simp only [Fin.val_castSucc]; exact ne_of_lt i.isLt), wd_preSeq]


/-! ## 3. the block comparison of the explicit inverses -/

lemma bInv_preSeq (n d : ℕ) (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) (z : ℂ)
    (hz0 : z ≠ 0) (E : Matrix (Fin n) (Fin n) C(X, ℂ)) (k i : Fin (d + 1)) :
    bInv n (d + 1) (Work.KT.Idx.preSeq X b) z (z⁻¹ • E) (Fin.castSucc k) (Fin.castSucc i)
      = (if (i : ℕ) = d then 0 else bInv n d b z E k i)
        + z ^ ((k : ℤ) - 1) • (E * b i) := by
  have hzpow : z ^ ((k : ℤ) - 1) = (z : ℂ) ^ (k : ℕ) * z⁻¹ := by
    rw [show ((k : ℤ) - 1) = ((k : ℕ) : ℤ) + (-1 : ℤ) by ring,
      zpow_add₀ hz0, zpow_natCast, _root_.zpow_neg_one]
  rw [bInv, bInv]
  simp only [Fin.val_castSucc]
  rw [BlkPen.wde_preSeq]
  have h1 : (z⁻¹ • E) * (b i + z • wd n d b z i)
      = z⁻¹ • (E * b i) + (E * wd n d b z i) := by
    rw [mul_add, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul,
      inv_mul_cancel₀ hz0, one_smul]
  have hterm : (z : ℂ) ^ (k : ℕ) • ((z⁻¹ • E) * (b i + z • wd n d b z i))
      = z ^ ((k : ℤ) - 1) • (E * b i) + (z : ℂ) ^ (k : ℕ) • (E * wd n d b z i) := by
    rw [h1, smul_add, smul_smul, ← hzpow]
  rw [hterm]
  by_cases hi : (i : ℕ) = d
  · have hil : i = Fin.last d := Fin.ext (by rw [Fin.val_last]; exact hi)
    have hwd : wd n d b z i = 0 := by rw [hil]; exact wd_last n d b z
    have hik : ¬ (i : ℕ) < (k : ℕ) := by
      rw [hi]; exact not_lt.mpr (by have := k.isLt; omega)
    rw [if_pos hi, if_neg hik, sub_zero, hwd, mul_zero, smul_zero, add_zero, zero_add]
  · rw [if_neg hi, wde, if_neg hi]
    by_cases hik : (i : ℕ) < (k : ℕ)
    · rw [if_pos hik]
      abel
    · rw [if_neg hik]
      abel

/-! ## 4. The pointwise identity on the circle -/

lemma pointwise (n d : ℕ) (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ))
    (hQ : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (wQ (A := C(X, ℂ)) n d b z))
    (hQ' : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (wQ (A := C(X, ℂ)) n (d + 1) (Work.KT.Idx.preSeq X b) z))
    (z : ℂ) (hz : ‖z‖ = 1) :
    Matrix.transpose (wInc (X := X) n d) *
        Work.KT.Idx.pResA (wBA (A := C(X, ℂ)) n (d + 1)) (wBB n (d + 1) (Work.KT.Idx.preSeq X b)) z *
        wInc (X := X) n d
      = Work.KT.Idx.pResA (wBA (A := C(X, ℂ)) n d) (wBB n d b) z
        + wCorr (A := C(X, ℂ)) n d b z := by
  have hz0 : z ≠ 0 := by intro h0; rw [h0] at hz; simp at hz
  have hbig : Ring.inverse (z • wBA (A := C(X, ℂ)) n (d + 1)
        + wBB n (d + 1) (Work.KT.Idx.preSeq X b))
      = wInv n (d + 1) (Work.KT.Idx.preSeq X b) z
          (z⁻¹ • Ring.inverse (wQ (A := C(X, ℂ)) n d b z)) := by
    rw [wInv_eq_ringInverse n (d + 1) (Work.KT.Idx.preSeq X b) z (hQ' z hz),
      wQ_preSeq X n d b z, ringInverse_smul]
  have hsmall : Ring.inverse (z • wBA (A := C(X, ℂ)) n d + wBB n d b)
      = wInv n d b z (Ring.inverse (wQ (A := C(X, ℂ)) n d b z)) :=
    wInv_eq_ringInverse n d b z (hQ z hz)
  simp only [Work.KT.Idx.pResA, Work.KT.Idx.pRes]
  rw [hbig, hsmall]
  apply Matrix.ext
  intro p q
  have hL : (Matrix.transpose (wInc (X := X) n d) *
        (wInv n (d + 1) (Work.KT.Idx.preSeq X b) z (z⁻¹ • Ring.inverse (wQ (A := C(X, ℂ)) n d b z))
          * wBA (A := C(X, ℂ)) n (d + 1)) * wInc (X := X) n d) p q
      = (bInv n (d + 1) (Work.KT.Idx.preSeq X b) z (z⁻¹ • Ring.inverse (wQ (A := C(X, ℂ)) n d b z))
          (Fin.castSucc p.1) (Fin.castSucc q.1)) p.2 q.2 := by
    rw [show (Matrix.transpose (wInc (X := X) n d) *
        (wInv n (d + 1) (Work.KT.Idx.preSeq X b) z
            (z⁻¹ • Ring.inverse (wQ (A := C(X, ℂ)) n d b z))
          * wBA (A := C(X, ℂ)) n (d + 1)) * wInc (X := X) n d) p q
        = (blkOf (Matrix.transpose (wInc (X := X) n d) *
            (wInv n (d + 1) (Work.KT.Idx.preSeq X b) z
                (z⁻¹ • Ring.inverse (wQ (A := C(X, ℂ)) n d b z))
              * wBA (A := C(X, ℂ)) n (d + 1)) * wInc (X := X) n d) p.1 q.1) p.2 q.2
        from rfl,
      blkOf_mul_wBA_sandwich, blkOf_wInv]
  have hR : ((wInv n d b z (Ring.inverse (wQ (A := C(X, ℂ)) n d b z)) * wBA (A := C(X, ℂ)) n d)
        + wCorr (A := C(X, ℂ)) n d b z) p q
      = ((if (q.1 : ℕ) = d then 0
            else bInv n d b z (Ring.inverse (wQ (A := C(X, ℂ)) n d b z)) p.1 q.1)) p.2 q.2
        + (z ^ ((p.1 : ℤ) - 1) • (Ring.inverse (wQ (A := C(X, ℂ)) n d b z) * b q.1)) p.2 q.2 := by
    rw [Matrix.add_apply,
      show (wInv n d b z (Ring.inverse (wQ (A := C(X, ℂ)) n d b z)) * wBA (A := C(X, ℂ)) n d) p q
        = (blkOf (wInv n d b z (Ring.inverse (wQ (A := C(X, ℂ)) n d b z))
            * wBA (A := C(X, ℂ)) n d) p.1 q.1) p.2 q.2 from rfl,
      blkOf_mul_wBA_last, blkOf_wInv, wCorr_apply]
  rw [hL, hR,
    bInv_preSeq n d b z hz0 (Ring.inverse (wQ (A := C(X, ℂ)) n d b z)) p.1 q.1,
    Matrix.add_apply]

/-! ## 5. Integrability -/

lemma circleIntegrable_pResA {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι C(X, ℂ)) (hunit : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (z • A + B)) :
    CircleIntegrable (fun z : ℂ => Work.KT.Idx.pResA A B z) 0 1 := by
  have hcomp : CompleteSpace (Matrix ι ι C(X, ℂ)) := Matrix.instCompleteSpace ι ι C(X, ℂ)
  exact (@continuousOn_res (Matrix ι ι C(X, ℂ)) _ _ hcomp A B hunit).circleIntegrable
    (by norm_num)

/-! ## 6. The circle integral of the sandwich -/

lemma circleIntegral_sandwich (n d : ℕ)
    (F : ℂ → Matrix (Fin (d + 2) × Fin n) (Fin (d + 2) × Fin n) C(X, ℂ))
    (hF : ContinuousOn F (Metric.sphere 0 1)) :
    Matrix.transpose (wInc (X := X) n d) * (∮ z in C(0, 1), F z) * wInc (X := X) n d
      = ∮ z in C(0, 1), Matrix.transpose (wInc (X := X) n d) * F z * wInc (X := X) n d := by
  have hFint : CircleIntegrable F 0 1 := hF.circleIntegrable (by norm_num)
  have hcM : Continuous (fun M : Matrix (Fin (d + 2) × Fin n) (Fin (d + 2) × Fin n) C(X, ℂ) =>
      Matrix.transpose (wInc (X := X) n d) * M) :=
    continuous_const.matrix_mul continuous_id
  have hcMd : Continuous (fun M : Matrix (Fin (d + 2) × Fin n) (Fin (d + 2) × Fin n) C(X, ℂ) =>
      Matrix.transpose (wInc (X := X) n d) * M * wInc (X := X) n d) :=
    hcM.matrix_mul continuous_const
  have hcont : ContinuousOn
      (fun z : ℂ => Matrix.transpose (wInc (X := X) n d) * F z * wInc (X := X) n d)
      (Metric.sphere 0 1) := hcMd.comp_continuousOn hF
  have hGint : CircleIntegrable
      (fun z : ℂ => Matrix.transpose (wInc (X := X) n d) * F z * wInc (X := X) n d) 0 1 :=
    hcont.circleIntegrable (by norm_num)
  apply Matrix.ext
  intro p q
  rw [sandwich_apply,
    BlkPen.circleIntegral_apply (X := X) F 0 1 (Fin.castSucc p.1, p.2) (Fin.castSucc q.1, q.2) hFint,
    BlkPen.circleIntegral_apply (X := X)
      (fun z : ℂ => Matrix.transpose (wInc (X := X) n d) * F z * wInc (X := X) n d) 0 1 p q hGint]
  refine circleIntegral.integral_congr (by norm_num) fun z hz => ?_
  rw [sandwich_apply]

/-! ## 7. The correction integral -/

lemma continuousOn_wCorr (n d : ℕ) (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ))
    (hQ : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (wQ (A := C(X, ℂ)) n d b z)) :
    ContinuousOn (fun z : ℂ => wCorr (A := C(X, ℂ)) n d b z) (Metric.sphere 0 1) := by
  have hcomp : CompleteSpace (Matrix (Fin n) (Fin n) C(X, ℂ)) := Matrix.instCompleteSpace _ _ _
  have hE : ContinuousOn (fun z : ℂ => Ring.inverse (wQ (A := C(X, ℂ)) n d b z))
      (Metric.sphere 0 1) :=
    @continuousOn_ringInverse_of (Matrix (Fin n) (Fin n) C(X, ℂ)) _ _ hcomp
      (fun z => wQ (A := C(X, ℂ)) n d b z) (continuous_wQ X n d b).continuousOn hQ
  rw [continuousOn_iff_continuous_domRestrict]
  refine continuous_matrix fun p q => ?_
  have h1 : Continuous (fun z : Metric.sphere (0 : ℂ) 1 => (z : ℂ) ^ ((p.1 : ℤ) - 1)) :=
    continuousOn_iff_continuous_domRestrict.mp (continuousOn_zpow_sphere ((p.1 : ℤ) - 1))
  have h2 : Continuous (fun z : Metric.sphere (0 : ℂ) 1 =>
      Ring.inverse (wQ (A := C(X, ℂ)) n d b (z : ℂ)) * b q.1) :=
    (continuousOn_iff_continuous_domRestrict.mp hE).matrix_mul continuous_const
  exact ((h1.smul h2).matrix_elem p.2 q.2).congr
    (fun z => (wCorr_apply n d b (z : ℂ) p q).symm)

lemma circleIntegrable_wCorr (n d : ℕ) (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ))
    (hQ : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (wQ (A := C(X, ℂ)) n d b z)) :
    CircleIntegrable (fun z : ℂ => wCorr (A := C(X, ℂ)) n d b z) 0 1 :=
  (continuousOn_wCorr n d b hQ).circleIntegrable (by norm_num)

lemma circleIntegral_wCorr (n d : ℕ) (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ))
    (hQ : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (wQ (A := C(X, ℂ)) n d b z)) :
    (∮ z in C(0, 1), wCorr (A := C(X, ℂ)) n d b z)
      = (2 * Real.pi * Complex.I) • wUpdate n d b (wPsi X n d b) := by
  have hcomp : CompleteSpace (Matrix (Fin n) (Fin n) C(X, ℂ)) := Matrix.instCompleteSpace _ _ _
  have hE : ContinuousOn (fun z : ℂ => Ring.inverse (wQ (A := C(X, ℂ)) n d b z))
      (Metric.sphere 0 1) :=
    @continuousOn_ringInverse_of (Matrix (Fin n) (Fin n) C(X, ℂ)) _ _ hcomp
      (fun z => wQ (A := C(X, ℂ)) n d b z) (continuous_wQ X n d b).continuousOn hQ
  have hW : ∀ m : ℤ, (∮ z in C(0, 1), (z ^ m) • Ring.inverse (wQ (A := C(X, ℂ)) n d b z))
      = (2 * Real.pi * Complex.I) • wPsi X n d b m := by
    intro m
    rw [wPsi, smul_smul, mul_inv_cancel₀ Complex.two_pi_I_ne_zero, one_smul]
  have hmatInt : ∀ m : ℤ, CircleIntegrable
      (fun z : ℂ => (z ^ m) • Ring.inverse (wQ (A := C(X, ℂ)) n d b z)) 0 1 := by
    intro m
    refine ContinuousOn.circleIntegrable (by norm_num) ?_
    have h1 : Continuous (fun z : Metric.sphere (0 : ℂ) 1 => (z : ℂ) ^ m) :=
      continuousOn_iff_continuous_domRestrict.mp (continuousOn_zpow_sphere m)
    have h2 : Continuous (fun z : Metric.sphere (0 : ℂ) 1 =>
        Ring.inverse (wQ (A := C(X, ℂ)) n d b (z : ℂ))) :=
      continuousOn_iff_continuous_domRestrict.mp hE
    exact continuousOn_iff_continuous_domRestrict.mpr (h1.smul h2)
  have hcInt : ∀ (m : ℤ) (a c : Fin n), CircleIntegrable
      (fun z : ℂ => ((z ^ m) • Ring.inverse (wQ (A := C(X, ℂ)) n d b z)) a c) 0 1 := by
    intro m a c
    refine ContinuousOn.circleIntegrable (by norm_num) ?_
    exact continuousOn_iff_continuous_domRestrict.mpr
      (((continuousOn_iff_continuous_domRestrict.mp (continuousOn_zpow_sphere m)).smul
        (continuousOn_iff_continuous_domRestrict.mp hE)).matrix_elem a c)
  apply Matrix.ext
  intro p q
  have hcongr : ∀ z ∈ Metric.sphere (0 : ℂ) 1,
      wCorr (A := C(X, ℂ)) n d b z p q
        = ∑ x : Fin n, ((z ^ ((p.1 : ℤ) - 1)) • Ring.inverse (wQ (A := C(X, ℂ)) n d b z)) p.2 x
            * (b q.1) x q.2 := by
    intro z hz
    rw [wCorr_apply, ← smul_mul_assoc, Matrix.mul_apply]
  have hcInt2 : ∀ x : Fin n, CircleIntegrable
      (fun z : ℂ => ((z ^ ((p.1 : ℤ) - 1)) • Ring.inverse (wQ (A := C(X, ℂ)) n d b z)) p.2 x
        * (b q.1) x q.2) 0 1 := by
    intro x
    have h1 : ContinuousOn (fun z : ℂ => ((z ^ ((p.1 : ℤ) - 1)) •
        Ring.inverse (wQ (A := C(X, ℂ)) n d b z)) p.2 x) (Metric.sphere 0 1) :=
      continuousOn_iff_continuous_domRestrict.mpr
        (((continuousOn_iff_continuous_domRestrict.mp
            (continuousOn_zpow_sphere ((p.1 : ℤ) - 1))).smul
          (continuousOn_iff_continuous_domRestrict.mp hE)).matrix_elem p.2 x)
    exact (h1.mul continuousOn_const).circleIntegrable (by norm_num)
  rw [BlkPen.circleIntegral_apply (X := X) (fun z : ℂ => wCorr (A := C(X, ℂ)) n d b z) 0 1
    p q (circleIntegrable_wCorr n d b hQ)]
  calc (∮ z in C(0, 1), wCorr (A := C(X, ℂ)) n d b z p q)
      = ∮ z in C(0, 1), ∑ x : Fin n,
          ((z ^ ((p.1 : ℤ) - 1)) • Ring.inverse (wQ (A := C(X, ℂ)) n d b z)) p.2 x
            * (b q.1) x q.2 :=
        circleIntegral.integral_congr (by norm_num) hcongr
    _ = ∑ x : Fin n, ∮ z in C(0, 1),
          ((z ^ ((p.1 : ℤ) - 1)) • Ring.inverse (wQ (A := C(X, ℂ)) n d b z)) p.2 x
            * (b q.1) x q.2 :=
        circleIntegral.integral_fun_sum (s := Finset.univ) (c := 0) (R := 1)
          (fun x _ => hcInt2 x)
    _ = ∑ x : Fin n, ((2 * Real.pi * Complex.I) •
          (wPsi X n d b ((p.1 : ℤ) - 1)) p.2 x) * (b q.1) x q.2 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        have hca := BlkPen.circleIntegral_apply (X := X)
          (f := fun z : ℂ => (z ^ ((p.1 : ℤ) - 1)) • Ring.inverse (wQ (A := C(X, ℂ)) n d b z))
          0 1 p.2 x (hmatInt ((p.1 : ℤ) - 1))
        rw [Work.KT.Fund.circleIntegral_mul_const ((b q.1) x q.2)
            (fun z : ℂ => ((z ^ ((p.1 : ℤ) - 1)) • Ring.inverse (wQ (A := C(X, ℂ)) n d b z)) p.2 x)
            0 1 (hcInt ((p.1 : ℤ) - 1) p.2 x),
          ← hca, hW, Matrix.smul_apply]
    _ = ((2 * Real.pi * Complex.I) • wUpdate n d b (wPsi X n d b)) p q := by
        rw [Matrix.smul_apply, wUpdate, Matrix.mul_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [smul_mul_assoc]

/-! ## 8b. The pencil is a unit when `wQ` is -/

lemma isUnit_wBlk {A : Type*} [CommRing A] [Algebra ℂ A] (n D : ℕ)
    (c : Fin (D + 1) → Matrix (Fin n) (Fin n) A) (z : ℂ) (hQ : IsUnit (wQ n D c z)) :
    IsUnit (z • wBA (A := A) n D + wBB n D c) := by
  have hQE : wQ n D c z * Ring.inverse (wQ n D c z) = 1 := Ring.mul_inverse_cancel _ hQ
  have hmul := wBlk_mul_wInv n D c z hQE
  have hdet : (z • wBA (A := A) n D + wBB n D c).det *
      (wInv n D c z (Ring.inverse (wQ n D c z))).det = 1 := by
    rw [← Matrix.det_mul, hmul, Matrix.det_one]
  rw [Matrix.isUnit_iff_isUnit_det]
  exact ⟨⟨_, _, hdet, by rw [mul_comm, hdet]⟩, rfl⟩


/-! ## 8. The final assembly -/

lemma continuousOn_pResA {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι C(X, ℂ)) (hunit : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (z • A + B)) :
    ContinuousOn (fun z : ℂ => Work.KT.Idx.pResA A B z) (Metric.sphere 0 1) := by
  have hcomp : CompleteSpace (Matrix ι ι C(X, ℂ)) := Matrix.instCompleteSpace ι ι C(X, ℂ)
  exact @continuousOn_res (Matrix ι ι C(X, ℂ)) _ _ hcomp A B hunit

lemma assembly (n d : ℕ) (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ))
    (hQ : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (wQ (A := C(X, ℂ)) n d b z))
    (hQ' : ∀ z : ℂ, ‖z‖ = 1 →
      IsUnit (wQ (A := C(X, ℂ)) n (d + 1) (Work.KT.Idx.preSeq X b) z)) :
    Matrix.transpose (wInc (X := X) n d) *
        blkPenProj X (wBA (A := C(X, ℂ)) n (d + 1)) (wBB n (d + 1) (Work.KT.Idx.preSeq X b)) *
        wInc (X := X) n d
      = blkPenProj X (wBA (A := C(X, ℂ)) n d) (wBB n d b)
        + wUpdate n d b (wPsi X n d b) := by
  have hcontbig : ContinuousOn (fun z : ℂ =>
      Work.KT.Idx.pResA (wBA (A := C(X, ℂ)) n (d + 1))
        (wBB n (d + 1) (Work.KT.Idx.preSeq X b)) z) (Metric.sphere 0 1) :=
    continuousOn_pResA _ _ (fun z hz => isUnit_wBlk n (d + 1) (Work.KT.Idx.preSeq X b) z (hQ' z hz))
  have hint_s : CircleIntegrable (fun z : ℂ =>
      Work.KT.Idx.pResA (wBA (A := C(X, ℂ)) n d) (wBB n d b) z) 0 1 :=
    circleIntegrable_pResA _ _ (fun z hz => isUnit_wBlk n d b z (hQ z hz))
  rw [blkPenProj_eq (X := X) (A := wBA (A := C(X, ℂ)) n (d + 1))
      (B := wBB n (d + 1) (Work.KT.Idx.preSeq X b)),
    blkPenProj_eq (X := X) (A := wBA (A := C(X, ℂ)) n d) (B := wBB n d b)]
  have hsc : Matrix.transpose (wInc (X := X) n d) *
        ((2 * Real.pi * Complex.I)⁻¹ •
          (∮ z in C(0, 1), Work.KT.Idx.pResA (wBA (A := C(X, ℂ)) n (d + 1))
            (wBB n (d + 1) (Work.KT.Idx.preSeq X b)) z)) * wInc (X := X) n d
      = (2 * Real.pi * Complex.I)⁻¹ • (Matrix.transpose (wInc (X := X) n d) *
          (∮ z in C(0, 1), Work.KT.Idx.pResA (wBA (A := C(X, ℂ)) n (d + 1))
            (wBB n (d + 1) (Work.KT.Idx.preSeq X b)) z) * wInc (X := X) n d) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [hsc]
  rw [circleIntegral_sandwich n d _ hcontbig]
  rw [show (∮ z in C(0, 1), Matrix.transpose (wInc (X := X) n d) *
        Work.KT.Idx.pResA (wBA (A := C(X, ℂ)) n (d + 1))
          (wBB n (d + 1) (Work.KT.Idx.preSeq X b)) z * wInc (X := X) n d)
      = ∮ z in C(0, 1), (Work.KT.Idx.pResA (wBA (A := C(X, ℂ)) n d) (wBB n d b) z
          + wCorr (A := C(X, ℂ)) n d b z) from
    circleIntegral.integral_congr (by norm_num) (fun z hz =>
      pointwise n d b hQ hQ' z (by simpa [Metric.mem_sphere, dist_eq_norm] using hz))]
  rw [circleIntegral.integral_add hint_s (circleIntegrable_wCorr n d b hQ),
    circleIntegral_wCorr n d b hQ]
  have hsmall : (∮ z in C(0, 1), Work.KT.Idx.pResA (wBA (A := C(X, ℂ)) n d) (wBB n d b) z)
      = (2 * Real.pi * Complex.I) • blkPenProj X (wBA (A := C(X, ℂ)) n d) (wBB n d b) := by
    rw [blkPenProj_eq, smul_smul, mul_inv_cancel₀ Complex.two_pi_I_ne_zero, one_smul]
  rw [hsmall, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ Complex.two_pi_I_ne_zero,
    one_smul, one_smul]

end BlkPen

/-- **The structural comparison of the two companion pencils (the prepend step).**

`wInc n d` is the "block inclusion" `Matrix (Fin (d+2) × Fin n) (Fin (d+1) × Fin n)` (identity in
the first `d+1` blocks, zero in the last), so `Matrix.transpose (wInc n d)` restricts a `(d+2)`-block
matrix to its first `d+1` blocks and `wInc n d` includes such a matrix back.  `blkPenProj X A B` is
the Riesz projection `(2πi)⁻¹ ∮_{|z|=1} (zA+B)⁻¹ A dz` of a pencil over `C(X, ℂ)` on an arbitrary
finite index type (the `ι = Fin N` case is `Work.KT.Idx.matPenProj`), `wBA`/`wBB` are the W
linearisation (`Work.KT.Idx.wPenA`/`wPenB` before reindexing), `wQ n D c z = ∑_j z^j • c_j`,
`wPsi X n D c m` is the Fourier data `(2πi)⁻¹ ∮ z^m • (wQ n D c z)⁻¹ dz`, and `wUpdate n d b Ψ` is
the block matrix with block `(k,i)` equal to `Ψ_{k-1} * b_i`.

Claim: the restriction of the projection of the `(d+2)`-block pencil of `preSeq X b = (0,b₀,…,b_d)`
to the first `d+1` blocks equals the projection of the `(d+1)`-block pencil of `b`, plus the
correction `wUpdate n d b (wPsi X n d b)`.  This is Hatcher's formula (2) at the level of the
projections; it is the heart of `Work.Idx.wPen_prepend` and is combined there with the idempotency
of the projections (`Work.Idx.penProj_idem`) and the Murray–von Neumann equivalence `1 ~ wUpdate`
coming from the Fourier relation `Work.Idx.wRow_wPsi`.

The proof is `BlkPen.assembly`; see the module docstring for the route and for the intermediate
lemmas. -/
theorem blkPenProj_preSeq_blocks {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n d : ℕ) (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ))
    (hQ : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (wQ (A := C(X, ℂ)) n d b z))
    (hQ' : ∀ z : ℂ, ‖z‖ = 1 →
      IsUnit (wQ (A := C(X, ℂ)) n (d + 1) (Work.KT.Idx.preSeq X b) z)) :
    Matrix.transpose (wInc (X := X) n d) *
        blkPenProj X (wBA (A := C(X, ℂ)) n (d + 1)) (wBB n (d + 1) (Work.KT.Idx.preSeq X b)) *
        wInc (X := X) n d
      = blkPenProj X (wBA (A := C(X, ℂ)) n d) (wBB n d b)
        + wUpdate n d b (wPsi X n d b) :=
  BlkPen.assembly n d b hQ hQ'

end

end Work.Idx
