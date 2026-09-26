import Submission.Work.SGsep.hand.HandPrep
import Submission.Work.SGsep.hand.two_row_kernel
import Submission.Work.SGsep.hand.eq_pm_of_rat_smul
import Submission.Work.SGsep.hand.gcd_v3
import Submission.Work.SGsep.hand.form_psd
import Submission.Work.SGsep.hand.detCols_conj
import Submission.Work.SGsep.hand.misc_bridges
import Submission.Work.SGsep.hand.chk_some
import Submission.Work.SGsep.hand.chk_none
import Submission.Work.SGsep.hand.ord_bridges
import Submission.Work.SGsep.hand.conj_pow_invMat

/-!
# The handedness certificate of a table element

The certificate conditions of `Data.HandCert.chk` pin down the handedness value of a table
element: the axis is the primitive oriented kernel vector of `A - 1` (kernel checked through the
generated axis table `axisAt`), and a conjugation by a unimodular `U` transports the certificate
data of `k` to that of `l`.
-/

namespace Work.SGsep.Hand

open Work.SG
open Work.SG.Data
open Work.SGsep.Hand.Data
open Work.SGsep.hand
open scoped Matrix

/-- `M3.mulV` commutes with the real embedding. -/
theorem mulV_toRealV (A : M3) (v : V3) :
    toRealV (A.mulV v) = (toRMat (M3.toIMat A)).mulVec (toRealV v) :=
  PSep.mulV_toRV A v

/-! ## The axis of a certificate -/

/-- The axis vector of a certificate for element `i` of representative `k` is, up to sign, the
tabulated primitive kernel vector. -/
theorem cert_axis_pm {k : Fin 230} {i : Nat} (hi : i < (repArith k.val).n)
    {ca : HandCert} (h : HandCert.chk k.val i (some ca) = true) :
    ∃ w : AxisW, axisAt k i = some w ∧ w.chkCore (A3n k.val i) = true ∧
      (ca.c = w.z ∨ ca.c = V3.negate w.z) := by
  obtain ⟨hdet, hord, h3, hmulV, hdot, hdetq, hcols, hh, hdvd, hbeta2, hvof⟩ := chk_some h
  have hrot : (A3n k.val i).det = 1 ∧ 3 ≤ (A3n k.val i).ord := ⟨hdet, by omega⟩
  obtain ⟨w, hw, hcore⟩ := axisAt_rot hi hrot
  refine ⟨w, hw, hcore, ?_⟩
  obtain ⟨hm0, hzB, hgcd, hcross, heps, hsymm, hpsd⟩ := chkCore_facts hcore
  have hz : (M3.sub (A3n k.val i) M3.one).mulV ca.c = V3.zero := mulV_sub_one hmulV
  have hzn : w.z ≠ V3.zero := by
    intro hc
    rw [hc] at hgcd
    simp [V3.gcdV, V3.zero] at hgcd
  have hr : V3.dot (M3.row (M3.sub (A3n k.val i) M3.one) w.p) ca.c = 0 :=
    dot_row_of_mulV_zero _ _ _ hz
  have hs : V3.dot (M3.row (M3.sub (A3n k.val i) M3.one) w.q) ca.c = 0 :=
    dot_row_of_mulV_zero _ _ _ hz
  obtain ⟨q, hq⟩ := two_row_kernel hm0 hzn hcross hr hs
  exact eq_pm_of_rat_smul (prim_of_gcdV_eq_one hgcd) ⟨ca.beta, hdot⟩ hq

/-- The conjugated axis vector `U c` of a certificate for element `i` of representative `k` is,
up to sign, the tabulated primitive kernel vector of the element `j` of representative `l` with
`A_l j = U A_k i U⁻¹`. -/
theorem conj_axis_pm {k l : Fin 230} (U : IMat) (hU : IsUnit U.det)
    {i j : Nat} (hi : i < (repArith k.val).n) (hj : j < (repArith l.val).n)
    (hij : Ah l j = U * Ah k i * invMat U)
    {ca : HandCert} (h : HandCert.chk k.val i (some ca) = true) :
    ∃ w' : AxisW, axisAt l j = some w' ∧ w'.chkCore (A3n l.val j) = true ∧
      (toV3 (Matrix.mulVec U ca.c.toFun) = w'.z ∨ toV3 (Matrix.mulVec U ca.c.toFun) = V3.negate w'.z) := by
  obtain ⟨hdet, hord, h3, hmulV, hdot, hdetq, hcols, hh, hdvd, hbeta2, hvof⟩ := chk_some h
  have hB : (A3n l.val j).toIMat = U * (A3n k.val i).toIMat * invMat U := by
    show (A3 l j).toIMat = U * (A3 k i).toIMat * invMat U
    simpa only [Ah] using hij
  have hordB : (A3n l.val j).ord = (A3n k.val i).ord := (ord_bridges.2.2 hU hB).1
  have hdetB : (A3n l.val j).det = (A3n k.val i).det := (ord_bridges.2.2 hU hB).2
  have hrot : (A3n l.val j).det = 1 ∧ 3 ≤ (A3n l.val j).ord :=
    ⟨by rw [hdetB, hdet], by rw [hordB]; omega⟩
  obtain ⟨w', hw', hcore'⟩ := axisAt_rot hj hrot
  refine ⟨w', hw', hcore', ?_⟩
  obtain ⟨hm0, hzB', hgcd', hcross', heps', hsymm', hpsd'⟩ := chkCore_facts hcore'
  -- `A c = c` at the matrix level
  have hAc : Matrix.mulVec (M3.toIMat (A3n k.val i)) ca.c.toFun = ca.c.toFun := by
    rw [← mulV_toFun (A3n k.val i) ca.c, hmulV]
  have hUc : Matrix.mulVec (M3.toIMat (A3n l.val j)) (Matrix.mulVec U ca.c.toFun)
      = Matrix.mulVec U ca.c.toFun := by
    rw [hB]
    calc Matrix.mulVec (U * M3.toIMat (A3n k.val i) * invMat U) (Matrix.mulVec U ca.c.toFun)
        = Matrix.mulVec U (Matrix.mulVec (M3.toIMat (A3n k.val i))
            (Matrix.mulVec (invMat U * U) ca.c.toFun)) := by
          simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = Matrix.mulVec U (Matrix.mulVec (M3.toIMat (A3n k.val i)) ca.c.toFun) := by
          rw [invMat_mul hU, Matrix.one_mulVec]
      _ = Matrix.mulVec U ca.c.toFun := by rw [hAc]
  -- transport to `M3`
  have hzB : M3.mulV (M3.sub (A3n l.val j) M3.one) (toV3 (Matrix.mulVec U ca.c.toFun))
      = V3.zero := by
    rw [mulV_eq_zero_iff, PSep.toIMat_sub, Matrix.sub_mulVec, M3.toIMat_one,
      Matrix.one_mulVec, toFun_toV3, hUc]
    simp
  have hdotIVec : ca.beta.toFun ⬝ᵥ ca.c.toFun = 1 := by
    rw [← dot_toFun]; exact hdot
  have hprimIVec : PrimIVec (Matrix.mulVec U ca.c.toFun) :=
    primIVec_mulVec_unimodular hU ⟨ca.beta.toFun, hdotIVec⟩
  have hprim : V3.Prim (toV3 (Matrix.mulVec U ca.c.toFun)) := prim_toV3 hprimIVec
  have huc_ne : Matrix.mulVec U ca.c.toFun ≠ 0 := by
    obtain ⟨β, hβ⟩ := hprim
    have hβ' : β.toFun ⬝ᵥ Matrix.mulVec U ca.c.toFun = 1 := by
      rw [← dot_toV3, toV3_toFun]
      exact hβ
    intro hc0
    rw [hc0] at hβ'
    simp at hβ'
  have hzn : w'.z ≠ V3.zero := by
    intro hc
    rw [hc] at hgcd'
    simp [V3.gcdV, V3.zero] at hgcd'
  have hr : V3.dot (M3.row (M3.sub (A3n l.val j) M3.one) w'.p)
      (toV3 (Matrix.mulVec U ca.c.toFun)) = 0 :=
    dot_row_of_mulV_zero _ _ _ hzB
  have hs : V3.dot (M3.row (M3.sub (A3n l.val j) M3.one) w'.q)
      (toV3 (Matrix.mulVec U ca.c.toFun)) = 0 :=
    dot_row_of_mulV_zero _ _ _ hzB
  obtain ⟨q, hq⟩ := two_row_kernel hm0 hzn hcross' hr hs
  exact eq_pm_of_rat_smul (prim_of_gcdV_eq_one hgcd') hprim hq


/-! ## Small sign lemmas for `V3.negate` -/

@[simp] theorem V3.negate_negate (v : V3) : V3.negate (V3.negate v) = v := by
  cases v; simp [V3.negate]

/-! ## The sign of the orientation form from the axis table -/

/-- For a checked axis datum, the quadratic form `y ↦ det(y, A y, c)` has a constant sign, for
`c` either the tabulated axis or its negative. -/
theorem axis_psd_sign {A : M3} {w : AxisW} (hcore : w.chkCore A = true)
    {c : V3} (hc : c = w.z ∨ c = V3.negate w.z) :
    ∃ κ : ℝ, (κ = 1 ∨ κ = -1) ∧
      ∀ y : Fin 3 → ℝ, 0 ≤ κ * detCols y ((toRMat (M3.toIMat A)).mulVec y) (toRealV c) := by
  have hpsd := form_psd (chkCore_eps hcore) (chkCore_psd hcore)
  rcases hc with hc | hc
  · refine ⟨(w.eps : ℝ), ?_, ?_⟩
    · rcases chkCore_eps hcore with h | h <;> rw [h] <;> norm_num
    · intro y; rw [hc]; exact hpsd y
  · refine ⟨-(w.eps : ℝ), ?_, ?_⟩
    · rcases chkCore_eps hcore with h | h <;> rw [h] <;> norm_num
    · intro y
      have h1 : detCols y ((toRMat (M3.toIMat A)).mulVec y) (toRealV (V3.negate w.z))
          = -detCols y ((toRMat (M3.toIMat A)).mulVec y) (toRealV w.z) := by
        rw [toRealV_negate, detCols_neg3]
      rw [hc, h1]
      have h2 : -(w.eps : ℝ) * (-(detCols y ((toRMat (M3.toIMat A)).mulVec y) (toRealV w.z)))
          = (w.eps : ℝ) * detCols y ((toRMat (M3.toIMat A)).mulVec y) (toRealV w.z) := by ring
      rw [h2]
      exact hpsd y

/-- `detCols_conj`, with the conjugated vector in the third slot and an arbitrary first column. -/
theorem detCols_conj' {U A B : IMat} (hU : IsUnit U.det)
    (hB : (toRMat B) * (toRMat U) = (toRMat U) * (toRMat A))
    {c c' y : Fin 3 → ℝ} (hc : c' = (toRMat U).mulVec c) :
    detCols y ((toRMat B).mulVec y) c'
      = (U.det : ℝ) * detCols ((toRMat (invMat U)).mulVec y)
          ((toRMat A).mulVec ((toRMat (invMat U)).mulVec y)) c := by
  have hMM' : (toRMat U) * (toRMat (invMat U)) = 1 := by
    rw [← toRMat_mul, mul_invMat hU, toRMat_one]
  have hMA : (toRMat U) * (toRMat A) = (toRMat B) * (toRMat U) := hB.symm
  have key := detCols_mulVec (toRMat U) ((toRMat (invMat U)).mulVec y)
    ((toRMat A).mulVec ((toRMat (invMat U)).mulVec y)) c
  rw [toRMat_det] at key
  have h1 : (toRMat U).mulVec ((toRMat (invMat U)).mulVec y) = y := by
    rw [Matrix.mulVec_mulVec y (toRMat U) (toRMat (invMat U)), hMM', Matrix.one_mulVec]
  have h2 : (toRMat U).mulVec ((toRMat A).mulVec ((toRMat (invMat U)).mulVec y))
      = (toRMat B).mulVec y := by
    rw [Matrix.mulVec_mulVec ((toRMat (invMat U)).mulVec y) (toRMat U) (toRMat A), hMA,
      ← Matrix.mulVec_mulVec ((toRMat (invMat U)).mulVec y) (toRMat B) (toRMat U), h1]
  rw [h1, h2, hc.symm] at key
  exact key

/-! ## The conjugated certificate -/

/-- The certificate of the conjugated element carries the conjugated axis: for `det U = 1` the
orientation condition of the certificate selects the same sign on both sides. -/
theorem cert_conj_axis {k l : Fin 230} (U : IMat) (hU : IsUnit U.det) (hUdet : U.det = 1)
    {i j : Nat} (hi : i < (repArith k.val).n) (hj : j < (repArith l.val).n)
    (hij : Ah l j = U * Ah k i * invMat U)
    {ca cb : HandCert} (hca : HandCert.chk k.val i (some ca) = true)
    (hcb : HandCert.chk l.val j (some cb) = true) :
    cb.c = toV3 (Matrix.mulVec U ca.c.toFun) := by
  obtain ⟨wk, hwk, hcorek, hcak⟩ := cert_axis_pm hi hca
  obtain ⟨wl, hwl, hcorel, hcbl⟩ := cert_axis_pm hj hcb
  obtain ⟨wl', hwl', hcorel', hucl⟩ := conj_axis_pm U hU hi hj hij hca
  have hwl_eq : wl' = wl := Option.some.inj (hwl'.symm.trans hwl)
  subst hwl_eq
  have hcases : cb.c = toV3 (Matrix.mulVec U ca.c.toFun) ∨
      cb.c = V3.negate (toV3 (Matrix.mulVec U ca.c.toFun)) := by
    rcases hcbl with h | h <;> rcases hucl with h' | h'
    · exact Or.inl (h.trans h'.symm)
    · exact Or.inr (h.trans (by rw [h', V3.negate_negate]))
    · exact Or.inr (by rw [h, h'])
    · exact Or.inl (h.trans h'.symm)
  rcases hcases with h | h
  · exact h
  · exfalso
    obtain ⟨hdetk, hordk, h3k, hmulVk, hdotk, hdetqk, hcolsk, hhk, hdvdk, hbeta2k, hvofk⟩ :=
      chk_some hca
    obtain ⟨hdetl, hordl, h3l, hmulVl, hdotl, hdetql, hcolsl, hhl, hdvdl, hbeta2l, hvofl⟩ :=
      chk_some hcb
    -- the PSD sign on the `k` side, pinned by the orientation condition
    obtain ⟨κ, hκpm, hκ⟩ := axis_psd_sign (A := A3n k.val i) hcorek hcak
    have horientk : 0 < detCols (toRealV (e3 ca.q))
        ((toRMat (M3.toIMat (A3n k.val i))).mulVec (toRealV (e3 ca.q))) (toRealV ca.c) := by
      rw [← mulV_toRealV, ← detCols_ofCols]
      exact_mod_cast hdetqk
    have hκ1 : κ = 1 := by
      rcases hκpm with h' | h'
      · exact h'
      · exfalso
        have hD := hκ (toRealV (e3 ca.q))
        rw [h'] at hD
        linarith [horientk, hD]
    have hk_nonneg : ∀ y : Fin 3 → ℝ,
        0 ≤ detCols y ((toRMat (M3.toIMat (A3n k.val i))).mulVec y) (toRealV ca.c) := by
      intro y
      have hy := hκ y
      rw [hκ1, one_mul] at hy
      exact hy
    -- the orientation condition on the `l` side, with the negated axis
    have horientl : 0 < detCols (toRealV (e3 cb.q))
        ((toRMat (M3.toIMat (A3n l.val j))).mulVec (toRealV (e3 cb.q))) (toRealV cb.c) := by
      rw [← mulV_toRealV, ← detCols_ofCols]
      exact_mod_cast hdetql
    have hDl : detCols (toRealV (e3 cb.q))
        ((toRMat (M3.toIMat (A3n l.val j))).mulVec (toRealV (e3 cb.q)))
        (toRealV (toV3 (Matrix.mulVec U ca.c.toFun))) < 0 := by
      have h1 : toRealV cb.c = fun i => -(toRealV (toV3 (Matrix.mulVec U ca.c.toFun)) i) := by
        rw [h, toRealV_negate]
      rw [h1, detCols_neg3] at horientl
      linarith
    -- naturality of the determinant
    have hBU : (toRMat (M3.toIMat (A3n l.val j))) * (toRMat U)
        = (toRMat U) * (toRMat (M3.toIMat (A3n k.val i))) := by
      have hB : M3.toIMat (A3n l.val j) = U * M3.toIMat (A3n k.val i) * invMat U := by
        show (A3 l j).toIMat = U * (A3 k i).toIMat * invMat U
        simpa only [Ah] using hij
      rw [← toRMat_mul, hB]
      simp only [Matrix.mul_assoc, invMat_mul hU, mul_one, toRMat_mul]
    have hUc_eq : toRealV (toV3 (Matrix.mulVec U ca.c.toFun))
        = (toRMat U).mulVec (toRealV ca.c) := by
      rw [toRealV_toV3]
      exact (Work.SG.mulVec_toRVec U ca.c.toFun).symm
    have hrel := detCols_conj' (A := M3.toIMat (A3n k.val i)) (B := M3.toIMat (A3n l.val j))
      hU hBU (c := toRealV ca.c) (c' := toRealV (toV3 (Matrix.mulVec U ca.c.toFun)))
      (y := toRealV (e3 cb.q)) hUc_eq
    rw [hUdet] at hrel
    norm_num at hrel
    have hrel' : detCols (toRealV (e3 cb.q))
        ((toRMat (M3.toIMat (A3n l.val j))).mulVec (toRealV (e3 cb.q)))
        (toRealV (toV3 (Matrix.mulVec U ca.c.toFun)))
        = detCols ((toRMat (invMat U)).mulVec (toRealV (e3 cb.q)))
          ((toRMat (M3.toIMat (A3n k.val i))).mulVec
            ((toRMat (invMat U)).mulVec (toRealV (e3 cb.q)))) (toRealV ca.c) := by
      simpa [toRealV_eq_toRVec] using hrel
    rw [hrel'] at hDl
    exact absurd (hk_nonneg ((toRMat (invMat U)).mulVec (toRealV (e3 cb.q)))) (not_le.mpr hDl)

end Work.SGsep.Hand
