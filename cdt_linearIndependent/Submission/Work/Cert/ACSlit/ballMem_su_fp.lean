import Mathlib
import Submission.Work.Cert.ACSlit.Shadow
import Submission.Work.Cert.ball_ops
import Submission.Work.APsi.slit_facts
import Submission.Work.ANum2.slit_second_deriv_bound
import Submission.Work.ANum2.Der2
import Submission.Work.Cert.ACBall.LuneChain

namespace Work.Cert.ACSlit
open Work.Cert Complex Submission.CDTPlan
open Work.Cert.ACBall
open Work.ANum2

/-- `cx x y` is contained in the ball `⟨x, y, 0⟩`. -/
lemma ballMem_cx' (x y : ℤ) : BallMem (⟨x, y, 0⟩ : Bl) (cx x y) := by
  rw [BallMem]; simp

/-- `cx (x - S) y = cx x y - 1`. -/
lemma cx_sub_one (x y : ℤ) : cx (x - S) y = cx x y - 1 := by
  have h1 : cx S 0 = (1 : ℂ) := by
    rw [cx_zero_y, div_self (ne_of_gt S_posR), Complex.ofReal_one]
  have hcomp : cx (x - S) y = cx (x - S) (y - 0) := by rw [Int.sub_zero]
  rw [hcomp, ← cx_sub x y S 0, h1]

/-- reading a mantissa equation `k = S·v` as `mS k = v`. -/
lemma mS_of_eq {k : ℤ} {v : ℝ} (h : (k : ℝ) = (S : ℝ) * v) : mS k = v := by
  rw [mS, h, div_eq_iff (ne_of_gt S_posR)]
  ring

lemma ballMem_sC' (A B2 E C1 G8 A2 ror roi : ℤ) (st : St) (w : SlitW) :
    BallMem (sC A B2 E C1 G8 A2 ror roi st w) (cIn st) :=
  ballMem_cx' st.cr st.ci

lemma ballMem_sc2' (A B2 E C1 G8 A2 ror roi : ℤ) (st : St) (w : SlitW) :
    BallMem (sc2 A B2 E C1 G8 A2 ror roi st w) (cIn st * cIn st) :=
  bmul_mem (ballMem_sC' A B2 E C1 G8 A2 ror roi st w)
    (ballMem_sC' A B2 E C1 G8 A2 ror roi st w)

lemma ballMem_sQ' (A B2 E C1 G8 A2 ror roi : ℤ) (st : St) (w : SlitW) {r : ℝ}
    (hA : (A : ℝ) = (S : ℝ) * (1 + r) ^ 2)
    (hB2 : (B2 : ℝ) = (S : ℝ) * (2 * (1 - 6 * r + r ^ 2))) :
    BallMem (sQ A B2 E C1 G8 A2 ror roi st w) (Qf r (cIn st)) := by
  have hsC := ballMem_sC' A B2 E C1 G8 A2 ror roi st w
  have hsc2 := ballMem_sc2' A B2 E C1 G8 A2 ror roi st w
  have h := ballMem_badd (ballMem_bsub (bmul_mem (ballMem_bK_mS A) hsc2)
      (bmul_mem (ballMem_bK_mS B2) hsC)) (ballMem_bK_mS A)
  rw [mS_of_eq hA, mS_of_eq hB2] at h
  convert h <;> try rfl
  rw [Qf_apply]
  push_cast
  ring

lemma ballMem_ss' (A B2 E C1 G8 A2 ror roi : ℤ) (st : St) (w : SlitW) {r : ℝ}
    (hok : bsqrtOK (sQ A B2 E C1 G8 A2 ror roi st w) w.sr = true)
    (hQ : BallMem (sQ A B2 E C1 G8 A2 ror roi st w) (Qf r (cIn st))) :
    BallMem (ss A B2 E C1 G8 A2 ror roi st w) (Sf r (cIn st)) := by
  have h := bsqrt_mem (si := w.si) hok hQ
  rw [Sf_apply]
  exact h

lemma ballMem_scm1' (A B2 E C1 G8 A2 ror roi : ℤ) (st : St) (w : SlitW) :
    BallMem (scm1 A B2 E C1 G8 A2 ror roi st w) (cIn st - 1) := by
  have h := ballMem_cx' (st.cr - S) st.ci
  rw [cx_sub_one] at h
  exact h

lemma ballMem_sN' (A B2 E C1 G8 A2 ror roi : ℤ) (st : St) (w : SlitW) {r : ℝ}
    (hA : (A : ℝ) = (S : ℝ) * (1 + r) ^ 2)
    (hE : (E : ℝ) = (S : ℝ) * (2 * (r - 1) ^ 2))
    (hC1 : (C1 : ℝ) = (S : ℝ) * (1 + r))
    (hss : BallMem (ss A B2 E C1 G8 A2 ror roi st w) (Sf r (cIn st)))
    (hsc2 : BallMem (sc2 A B2 E C1 G8 A2 ror roi st w) (cIn st * cIn st))
    (hscm1 : BallMem (scm1 A B2 E C1 G8 A2 ror roi st w) (cIn st - 1)) :
    BallMem (sN A B2 E C1 G8 A2 ror roi st w) (Nf r (cIn st)) := by
  have hsC := ballMem_sC' A B2 E C1 G8 A2 ror roi st w
  have h := ballMem_badd (ballMem_badd
      (ballMem_bsub (ballMem_bK_mS A) (bmul_mem (ballMem_bK_mS E) hsC))
      (bmul_mem (ballMem_bK_mS A) hsc2))
    (bmul_mem (ballMem_bK_mS C1) (bmul_mem hscm1 hss))
  rw [mS_of_eq hA, mS_of_eq hE, mS_of_eq hC1] at h
  convert h <;> try rfl
  rw [Nf_apply, Sf_apply]
  push_cast
  ring

lemma ballMem_sden' (A B2 E C1 G8 A2 ror roi : ℤ) (st : St) (w : SlitW) {r : ℝ}
    (hG8 : (G8 : ℝ) = (S : ℝ) * (8 * r)) :
    BallMem (sden A B2 E C1 G8 A2 ror roi st w) (8 * (r : ℂ) * cIn st) := by
  have h := bmul_mem (ballMem_bK_mS G8) (ballMem_sC' A B2 E C1 G8 A2 ror roi st w)
  rw [mS_of_eq hG8] at h
  convert h <;> try rfl
  push_cast
  ring

lemma ballMem_sinv1' (A B2 E C1 G8 A2 ror roi : ℤ) (st : St) (w : SlitW) {r : ℝ}
    (hok : binvOK (sden A B2 E C1 G8 A2 ror roi st w) w.L1 = true)
    (hden : BallMem (sden A B2 E C1 G8 A2 ror roi st w) (8 * (r : ℂ) * cIn st)) :
    BallMem (sinv1 A B2 E C1 G8 A2 ror roi st w) ((8 * (r : ℂ) * cIn st)⁻¹) :=
  binv_mem hok hden

lemma ballMem_sv' (A B2 E C1 G8 A2 ror roi : ℤ) (st : St) (w : SlitW) {r : ℝ}
    (hN : BallMem (sN A B2 E C1 G8 A2 ror roi st w) (Nf r (cIn st)))
    (hi : BallMem (sinv1 A B2 E C1 G8 A2 ror roi st w) ((8 * (r : ℂ) * cIn st)⁻¹)) :
    BallMem (sv A B2 E C1 G8 A2 ror roi st w) (slit r (cIn st)) := by
  have h := bmul_mem hN hi
  convert h <;> try rfl
  rw [slit_eq_Nf r]
  beta_reduce
  rw [div_eq_mul_inv]

lemma ballMem_sRO' (A B2 E C1 G8 A2 ror roi : ℤ) (st : St) (w : SlitW) {t : ℝ}
    (hrot : ‖cx ror roi - rot t‖ ≤ 2 / (S : ℝ)) :
    BallMem (sRO A B2 E C1 G8 A2 ror roi st w) (rot t) := by
  rw [BallMem]
  show ‖rot t - cx ror roi‖ ≤ ((2 : ℤ) : ℝ) / (S : ℝ)
  rw [norm_sub_rev]
  convert hrot using 1
  all_goals first | rfl | (push_cast; ring) | push_cast

lemma ballMem_sQp' (A B2 E C1 G8 A2 ror roi : ℤ) (st : St) (w : SlitW) {r : ℝ}
    (hA2 : (A2 : ℝ) = (S : ℝ) * (2 * (1 + r) ^ 2))
    (hB2 : (B2 : ℝ) = (S : ℝ) * (2 * (1 - 6 * r + r ^ 2))) :
    BallMem (sQp A B2 E C1 G8 A2 ror roi st w) (Qd r (cIn st)) := by
  have h := ballMem_bsub
    (bmul_mem (ballMem_bK_mS A2) (ballMem_sC' A B2 E C1 G8 A2 ror roi st w))
    (ballMem_bK_mS B2)
  rw [mS_of_eq hA2, mS_of_eq hB2] at h
  convert h <;> try rfl
  rw [Qd_apply]
  push_cast
  ring

lemma ballMem_sinvs' (A B2 E C1 G8 A2 ror roi : ℤ) (st : St) (w : SlitW) {r : ℝ}
    (hok : binvOK (ss A B2 E C1 G8 A2 ror roi st w) w.Ls = true)
    (hss : BallMem (ss A B2 E C1 G8 A2 ror roi st w) (Sf r (cIn st))) :
    BallMem (sinvs A B2 E C1 G8 A2 ror roi st w) ((Sf r (cIn st))⁻¹) :=
  binv_mem hok hss

lemma ballMem_sqos' (A B2 E C1 G8 A2 ror roi : ℤ) (st : St) (w : SlitW) {r : ℝ}
    (hQp : BallMem (sQp A B2 E C1 G8 A2 ror roi st w) (Qd r (cIn st)))
    (hinvs : BallMem (sinvs A B2 E C1 G8 A2 ror roi st w) ((Sf r (cIn st))⁻¹)) :
    BallMem (sqos A B2 E C1 G8 A2 ror roi st w) (Qd r (cIn st) / (2 * Sf r (cIn st))) := by
  have hhalf : BallMem (bK (fdiv S 2)) (((1 / 2 : ℝ)) : ℂ) := by
    have h := ballMem_bK_mS (fdiv S 2)
    rw [mS_fdiv_S_two] at h
    exact h
  have h := bmul_mem (bmul_mem hQp hinvs) hhalf
  convert h <;> try rfl
  rw [div_eq_mul_inv, mul_inv]
  have h2 : ((1 / 2 : ℝ) : ℂ) = (2 : ℂ)⁻¹ := by norm_num
  rw [h2]
  ring

lemma ballMem_sNp' (A B2 E C1 G8 A2 ror roi : ℤ) (st : St) (w : SlitW) {r : ℝ}
    (hA2 : (A2 : ℝ) = (S : ℝ) * (2 * (1 + r) ^ 2))
    (hE : (E : ℝ) = (S : ℝ) * (2 * (r - 1) ^ 2))
    (hC1 : (C1 : ℝ) = (S : ℝ) * (1 + r))
    (hss : BallMem (ss A B2 E C1 G8 A2 ror roi st w) (Sf r (cIn st)))
    (hqos : BallMem (sqos A B2 E C1 G8 A2 ror roi st w) (Qd r (cIn st) / (2 * Sf r (cIn st))))
    (hscm1 : BallMem (scm1 A B2 E C1 G8 A2 ror roi st w) (cIn st - 1)) :
    BallMem (sNp A B2 E C1 G8 A2 ror roi st w) (Nd r (cIn st)) := by
  have h := ballMem_badd (ballMem_badd
      (ballMem_bsub (bmul_mem (ballMem_bK_mS A2) (ballMem_sC' A B2 E C1 G8 A2 ror roi st w))
        (ballMem_bK_mS E))
      (bmul_mem (ballMem_bK_mS C1) hss))
    (bmul_mem (ballMem_bK_mS C1) (bmul_mem hscm1 hqos))
  rw [mS_of_eq hA2, mS_of_eq hE, mS_of_eq hC1] at h
  convert h <;> try rfl
  rw [Nd_apply]
  push_cast
  ring

lemma ballMem_sdn' (A B2 E C1 G8 A2 ror roi : ℤ) (st : St) (w : SlitW) {r : ℝ}
    (hNp : BallMem (sNp A B2 E C1 G8 A2 ror roi st w) (Nd r (cIn st)))
    (hN : BallMem (sN A B2 E C1 G8 A2 ror roi st w) (Nf r (cIn st))) :
    BallMem (sdn A B2 E C1 G8 A2 ror roi st w) (Nd r (cIn st) * cIn st - Nf r (cIn st)) :=
  ballMem_bsub (bmul_mem hNp (ballMem_sC' A B2 E C1 G8 A2 ror roi st w)) hN

lemma ballMem_sinvc' (A B2 E C1 G8 A2 ror roi : ℤ) (st : St) (w : SlitW)
    (hok : binvOK (sC A B2 E C1 G8 A2 ror roi st w) w.cL = true) :
    BallMem (sinvc A B2 E C1 G8 A2 ror roi st w) ((cIn st)⁻¹) :=
  binv_mem hok (ballMem_sC' A B2 E C1 G8 A2 ror roi st w)

/-- the derivative of the slit map at `c` in the `N`-normalisation. -/
lemma deriv_slit_eq (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) {c : ℂ} (hc : c ≠ 0) (hclt : ‖c‖ < 1) :
    deriv (slit r) c = (Nd r c * c - Nf r c) / (8 * (r : ℂ) * c ^ 2) := by
  rw [slit_eq_Gfun r]
  exact ((slit_hasDerivAt_Gfun r hr0 hr1 hclt hc).deriv).trans (Hd_apply r c)

/-- Ball semantics of the value and derivative of a slit stage at the centre: `su ∋ rot t · slit r c`
and `sfp ∋ rot t · deriv (slit r) c`, `c = cIn st`. Uses `ball_ops` for every `badd/bsub/bmul/binv/bsqrt`,
`Work.APsi.slit_eq_formula` (valid because `binvOK (sC st) w.cL` forces `c ≠ 0` — `ball_ops.2.1`),
`Work.APsi.cpow_half_sq`, `Work.ANum2.slit_eq_Gfun` + `Work.ANum2.slit_hasDerivAt_Gfun` +
`Work.ANum2.Hd_apply` for `deriv (slit r) c = (N'(c)·c − N(c))/(8 r c²)`, and `ring`.
(`slit_hasDerivAt_Gfun` lives in `Submission.Work.ANum2.slit_second_deriv_bound`; the fact
`(fdiv S 2)/S = 1/2` is `Work.Cert.ACBall.mS_fdiv_S_two` in `ACBall.LuneChain`.)
Namespace of this declaration: `Work.Cert.ACSlit`. -/
theorem ballMem_su_fp (A B2 E C1 G8 A2 ror roi : ℤ) (st : Work.Cert.St) (w : Work.Cert.SlitW)
    {r t : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hA : (A : ℝ) = (Work.Cert.S : ℝ) * (1 + r) ^ 2)
    (hB2 : (B2 : ℝ) = (Work.Cert.S : ℝ) * (2 * (1 - 6 * r + r ^ 2)))
    (hE : (E : ℝ) = (Work.Cert.S : ℝ) * (2 * (r - 1) ^ 2))
    (hC1 : (C1 : ℝ) = (Work.Cert.S : ℝ) * (1 + r))
    (hG8 : (G8 : ℝ) = (Work.Cert.S : ℝ) * (8 * r))
    (hA2 : (A2 : ℝ) = (Work.Cert.S : ℝ) * (2 * (1 + r) ^ 2))
    (hrot : ‖Work.Cert.cx ror roi - Submission.CDTPlan.rot t‖ ≤ 2 / (Work.Cert.S : ℝ))
    (hokB : Work.Cert.ACSlit.sokB A B2 E C1 G8 A2 ror roi st w = true)
    (hc0 : Work.Cert.ACSlit.cIn st ≠ 0) (hclt : ‖Work.Cert.ACSlit.cIn st‖ < 1) :
    Work.Cert.ACBall.BallMem (Work.Cert.ACSlit.su A B2 E C1 G8 A2 ror roi st w)
        (Submission.CDTPlan.rot t * Submission.CDTPlan.slit r (Work.Cert.ACSlit.cIn st)) ∧
      Work.Cert.ACBall.BallMem (Work.Cert.ACSlit.sfp A B2 E C1 G8 A2 ror roi st w)
        (Submission.CDTPlan.rot t * deriv (Submission.CDTPlan.slit r) (Work.Cert.ACSlit.cIn st)) := by
  simp only [sokB, Bool.and_eq_true] at hokB
  obtain ⟨⟨⟨hbs, hL1⟩, hLs⟩, hcL⟩ := hokB
  have hsC := ballMem_sC' A B2 E C1 G8 A2 ror roi st w
  have hsc2 := ballMem_sc2' A B2 E C1 G8 A2 ror roi st w
  have hQ := ballMem_sQ' A B2 E C1 G8 A2 ror roi st w hA hB2
  have hss := ballMem_ss' A B2 E C1 G8 A2 ror roi st w hbs hQ
  have hscm1 := ballMem_scm1' A B2 E C1 G8 A2 ror roi st w
  have hN := ballMem_sN' A B2 E C1 G8 A2 ror roi st w hA hE hC1 hss hsc2 hscm1
  have hden := ballMem_sden' A B2 E C1 G8 A2 ror roi st w hG8
  have hinv1 := ballMem_sinv1' A B2 E C1 G8 A2 ror roi st w hL1 hden
  have hsv := ballMem_sv' A B2 E C1 G8 A2 ror roi st w hN hinv1
  have hRO := ballMem_sRO' A B2 E C1 G8 A2 ror roi st w hrot
  have hsu : BallMem (su A B2 E C1 G8 A2 ror roi st w) (rot t * slit r (cIn st)) :=
    bmul_mem hRO hsv
  have hQp := ballMem_sQp' A B2 E C1 G8 A2 ror roi st w hA2 hB2
  have hinvs := ballMem_sinvs' A B2 E C1 G8 A2 ror roi st w hLs hss
  have hqos := ballMem_sqos' A B2 E C1 G8 A2 ror roi st w hQp hinvs
  have hNp := ballMem_sNp' A B2 E C1 G8 A2 ror roi st w hA2 hE hC1 hss hqos hscm1
  have hdn := ballMem_sdn' A B2 E C1 G8 A2 ror roi st w hNp hN
  have hinvc := ballMem_sinvc' A B2 E C1 G8 A2 ror roi st w hcL
  have hd1 : BallMem (bmul (sdn A B2 E C1 G8 A2 ror roi st w)
        (sinv1 A B2 E C1 G8 A2 ror roi st w))
      ((Nd r (cIn st) * cIn st - Nf r (cIn st)) * (8 * (r : ℂ) * cIn st)⁻¹) :=
    bmul_mem hdn hinv1
  have hd2 : BallMem (bmul (bmul (sdn A B2 E C1 G8 A2 ror roi st w)
        (sinv1 A B2 E C1 G8 A2 ror roi st w)) (sinvc A B2 E C1 G8 A2 ror roi st w))
      (((Nd r (cIn st) * cIn st - Nf r (cIn st)) * (8 * (r : ℂ) * cIn st)⁻¹)
        * (cIn st)⁻¹) :=
    bmul_mem hd1 hinvc
  have hd3 : BallMem (bmul (bmul (sdn A B2 E C1 G8 A2 ror roi st w)
        (sinv1 A B2 E C1 G8 A2 ror roi st w)) (sinvc A B2 E C1 G8 A2 ror roi st w))
      (deriv (slit r) (cIn st)) := by
    rw [deriv_slit_eq r hr0 hr1 hc0 hclt]
    convert hd2 using 1
    rw [div_eq_mul_inv]
    rw [show (8 * (r : ℂ) * (cIn st) ^ 2 : ℂ) = (8 * (r : ℂ) * cIn st) * cIn st by ring,
      mul_inv]
    ring
  exact ⟨hsu, bmul_mem hRO hd3⟩

end Work.Cert.ACSlit
