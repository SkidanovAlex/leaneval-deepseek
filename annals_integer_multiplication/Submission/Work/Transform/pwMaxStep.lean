import Mathlib
import Submission.Work.Transform.pwMaxDefs
import Submission.Work.Transform.pwScanBv
import Submission.Work.Transform.pwMaxWin
import Submission.Work.Transform.pwMaxLose

/-!
# `Work.Transform.pwMaxStep`: one element of the parameter-word max phase

`elemProg src mx sp spc ds tmp sA bA bB` handles one element `t > 0` of the list: store its
magnitude (most significant first) on `sp`, copy and reverse it onto `sA` (least significant first),
compare it with the running maximum `M` on `mx` by the *buffered* lockstep scan (`pwScanBv`, cost
`O (min (size t) (size M) + 1)`), and then either move the element's bits onto `mx` (`pwMaxWin`) or
push the consumed prefix of the maximum back (`pwMaxLose`); finally the element's sign is discarded.

The cost of the whole word is `O (t.size + 1)`: it never pays for the length of the running maximum,
because either the maximum is not longer than the element (`gGt` branch) or only its consumed prefix
(which the scan paid for) has to be pushed back.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.Transform.Pw

open HvdH
open Work.Kernel

theorem pwMaxStep (src mx : HvdH.Stk) (hsm : src ≠ mx) (S : Scr src mx) :
    ∃ (elem : HvdH.Cmd) (Ke : ℕ), ElemSpec src mx elem Ke := by
  obtain ⟨Ks, hscan⟩ := pwScanBv S.sA mx S.bA S.bB S.ne_sA_mx (S.ne_sA_bA).symm S.ne_bA_mx
    (S.ne_sA_bB).symm S.ne_bB_mx S.ne_bA_bB
  obtain ⟨Kw, hwin⟩ := pwMaxWin S.sp S.sA S.bA S.bB mx S.nodup5
  obtain ⟨Kl, hlose⟩ := pwMaxLose S.sp S.sA S.bA S.bB mx S.nodup5
  refine ⟨elemProg src mx S.sp S.spc S.ds S.tmp S.sA S.bA S.bB,
    2 * (Ks + Kw + Kl + 130), ?_⟩
  intro main t M tail mxTail s ht0 hsrc hmx
  set B := Computability.encodeNat t with hB
  set MB := Computability.encodeNat M with hMB
  have hBl : B.length = t.size := by rw [hB]; exact mx_encodeNat_length t
  have hMBl : MB.length = M.size := by rw [hMB]; exact mx_encodeNat_length M
  -- ## step 1: storeMag
  have hsrc2 : s.stk src = HvdH.Glyph.pos :: (B.map HvdH.Glyph.bit ++ HvdH.Glyph.iend :: tail) := by
    rw [hsrc, hB, mx_enc_int_nat]
    simp only [List.cons_append, List.append_assoc, List.nil_append]
  obtain ⟨s1, n1, e1, hn1, hs1src, hs1sp, hs1ds, hs1fr⟩ :=
    storeMag_eval main src S.sp S.ds mA mB S.ne_sp_src S.ne_ds_src (Ne.symm S.ne_sp_ds)
      HvdH.Glyph.pos B tail s hsrc2
  -- ## step 2: copyMarked2
  obtain ⟨s2, n2, e2, hn2, hs2sp, hs2spc, hs2tmp, hs2fr⟩ :=
    copyMarked2_eval main S.sp S.spc S.tmp mA mB (Ne.symm S.ne_sp_spc) (Ne.symm S.ne_sp_tmp)
      (Ne.symm S.ne_spc_tmp) S.ne_sp_spc (B.reverse.map HvdH.Glyph.bit) (s.stk S.sp)
      (map_bit_ne_gM B.reverse) (map_bit_ne_gM2 B.reverse) s1 hs1sp
  -- ## step 3: revMarked
  have hs2spc' : s2.stk S.spc = B.reverse.map HvdH.Glyph.bit ++ gM :: s.stk S.spc := by
    rw [hs2spc, hs1fr S.spc S.ne_spc_src (S.ne_sp_spc).symm S.ne_spc_ds]
  obtain ⟨s3, n3, e3, hn3, hs3spc, hs3sA, hs3fr⟩ :=
    revMarked_eval main S.spc S.sA mA mB (S.ne_spc_sA).symm (B.reverse.map HvdH.Glyph.bit)
      (s.stk S.spc) (map_bit_ne_gM B.reverse) s2 hs2spc'
  have hs3sA' : s3.stk S.sA = B.map HvdH.Glyph.bit ++ gM :: s.stk S.sA := by
    rw [hs3sA, ← List.map_reverse, List.reverse_reverse]
    rw [hs2fr S.sA (S.ne_sp_sA).symm (S.ne_spc_sA).symm (S.ne_tmp_sA).symm,
      hs1fr S.sA S.ne_sA_src (S.ne_sp_sA).symm (S.ne_ds_sA).symm]
  -- the running maximum is untouched up to the scan
  have hs1mx : s1.stk mx = (Computability.encodeNat M).map HvdH.Glyph.bit ++ gM :: mxTail :=
    (hs1fr mx hsm.symm (S.ne_sp_mx).symm (S.ne_ds_mx).symm).trans hmx
  have hs3mx : s3.stk mx = MB.map HvdH.Glyph.bit ++ gM :: mxTail := by
    rw [hs3fr mx (S.ne_spc_mx).symm (S.ne_sA_mx).symm,
      hs2fr mx (S.ne_sp_mx).symm (S.ne_spc_mx).symm (S.ne_tmp_mx).symm, hs1mx, hMB]
  -- the buffers are untouched up to the scan
  have hs3bA : s3.stk S.bA = s.stk S.bA := by
    rw [hs3fr S.bA (S.ne_spc_bA).symm (S.ne_sA_bA).symm,
      hs2fr S.bA (S.ne_sp_bA).symm (S.ne_spc_bA).symm (S.ne_tmp_bA).symm,
      hs1fr S.bA S.ne_bA_src (S.ne_sp_bA).symm (S.ne_ds_bA).symm]
  have hs3bB : s3.stk S.bB = s.stk S.bB := by
    rw [hs3fr S.bB (S.ne_spc_bB).symm (S.ne_sA_bB).symm,
      hs2fr S.bB (S.ne_sp_bB).symm (S.ne_spc_bB).symm (S.ne_tmp_bB).symm,
      hs1fr S.bB S.ne_bB_src (S.ne_sp_bB).symm (S.ne_ds_bB).symm]
  -- ## step 4: the buffered scan
  obtain ⟨s4, ns, e4, hns, _h4cont, h4flag, h4sA, h4mx, h4bA, h4bB, h4fr⟩ :=
    hscan main B MB (s.stk S.sA) mxTail s3 (by rw [hB]; exact mx_isBits_encodeNat t)
      (by rw [hMB]; exact mx_isBits_encodeNat M) hs3sA' hs3mx
  have hs4sp : s4.stk S.sp = B.reverse.map HvdH.Glyph.bit ++ gM :: s.stk S.sp := by
    rw [h4fr S.sp S.ne_sp_sA S.ne_sp_mx S.ne_sp_bA S.ne_sp_bB,
      hs3fr S.sp S.ne_sp_spc S.ne_sp_sA]
    exact hs2sp
  have hs4sA : s4.stk S.sA = (B.drop (min B.length MB.length)).map HvdH.Glyph.bit
      ++ gM :: s.stk S.sA := h4sA
  have hs4bA : s4.stk S.bA = ((B.take (min B.length MB.length)).map HvdH.Glyph.bit).reverse
      ++ gM :: s.stk S.bA := by rw [h4bA, hs3bA]
  have hs4bB : s4.stk S.bB = ((MB.take (min B.length MB.length)).map HvdH.Glyph.bit).reverse
      ++ gM :: s.stk S.bB := by rw [h4bB, hs3bB]
  have hs4mx : s4.stk mx = (MB.drop (min B.length MB.length)).map HvdH.Glyph.bit
      ++ gM :: mxTail := h4mx
  -- ## step 5: the branch
  have hflag' : NatFlag (s4.reg rFlag) t M := by
    rw [hB, hMB] at h4flag
    simpa only [mx_ofBits_encodeNat] using h4flag
  have hbranch : ∃ (s5 : HvdH.State) (nb : ℕ),
      HvdH.Eval main (.ite rFlag gGt (winProg S.sp S.sA S.bA S.bB mx)
        (loseProg S.sp S.sA S.bA S.bB mx)) s4 s5 (nb + 1) ∧
      nb ≤ (Kw + Kl) * (t.size + 1) ∧
      s5.stk mx = (Computability.encodeNat (max M t)).map HvdH.Glyph.bit ++ gM :: mxTail ∧
      s5.stk S.sp = s.stk S.sp ∧ s5.stk S.sA = s.stk S.sA ∧ s5.stk S.bA = s.stk S.bA ∧
      s5.stk S.bB = s.stk S.bB ∧
      (∀ j : HvdH.Stk, j ≠ S.sp → j ≠ S.sA → j ≠ S.bA → j ≠ S.bB → j ≠ mx →
        s5.stk j = s4.stk j) := by
    by_cases hf : s4.reg rFlag = gGt
    · have hMt : M < t := by
        rcases hflag' with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h2⟩
        · exact absurd (h1.symm.trans hf) (by decide)
        · exact absurd (h1.symm.trans hf) (by decide)
        · exact h2
      have hlen : MB.length ≤ B.length := by rw [hMBl, hBl]; exact mx_size_le_of_lt hMt
      obtain ⟨s5, nb, eb, hnb, h5mx, h5sp, h5sA, h5bA, h5bB, h5fr⟩ :=
        hwin main B MB (min B.length MB.length) (s.stk S.sp) (s.stk S.sA) (s.stk S.bA)
          (s.stk S.bB) mxTail s4 hs4sp hs4sA hs4bA hs4bB hs4mx hlen
      refine ⟨s5, nb, Eval.iteT hf eb, ?_, ?_, h5sp, h5sA, h5bA, h5bB, h5fr⟩
      · have hnb' : nb ≤ Kw * (t.size + 1) := by rw [hBl] at hnb; exact hnb
        exact le_trans hnb' (Nat.mul_le_mul_right (t.size + 1) (by omega))
      · rw [h5mx, hB, mx_max_eq_right hMt]
    · have htM : t ≤ M := by
        rcases hflag' with ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨h1, -⟩
        · exact le_of_lt h2
        · exact le_of_eq h2
        · exact absurd h1 hf
      have hkA : min B.length MB.length ≤ B.length := Nat.min_le_left _ _
      obtain ⟨s5, nb, eb, hnb, h5mx, h5sp, h5sA, h5bA, h5bB, h5fr⟩ :=
        hlose main B MB (min B.length MB.length) (s.stk S.sp) (s.stk S.sA) (s.stk S.bA)
          (s.stk S.bB) mxTail s4 hs4sp hs4sA hs4bA hs4bB hs4mx hkA
      refine ⟨s5, nb, Eval.iteF hf eb, ?_, ?_, h5sp, h5sA, h5bA, h5bB, h5fr⟩
      · have hnb' : nb ≤ Kl * (t.size + 1) := by rw [hBl] at hnb; exact hnb
        exact le_trans hnb' (Nat.mul_le_mul_right (t.size + 1) (by omega))
      · rw [h5mx, hMB, mx_max_eq_left htM]
  obtain ⟨s5, nb, eb, hnb, h5mx, h5sp, h5sA, h5bA, h5bB, h5fr⟩ := hbranch
  -- ## step 6: discard the element's sign
  set s6 : HvdH.State := HvdH.State.tPop s5 S.ds mA with hs6
  have e6 : HvdH.Eval main (.pop S.ds mA) s5 s6 1 := by rw [hs6]; exact eval_pop main S.ds mA s5
  -- ds was restored up to the sign by the toolkit, and the branch leaves it alone
  have hds5 : s5.stk S.ds = HvdH.Glyph.pos :: s.stk S.ds := by
    rw [h5fr S.ds (S.ne_sp_ds).symm S.ne_ds_sA S.ne_ds_bA S.ne_ds_bB S.ne_ds_mx]
    rw [h4fr S.ds S.ne_ds_sA S.ne_ds_mx S.ne_ds_bA S.ne_ds_bB]
    rw [hs3fr S.ds (S.ne_spc_ds).symm S.ne_ds_sA]
    rw [hs2fr S.ds (S.ne_sp_ds).symm (S.ne_spc_ds).symm S.ne_ds_tmp]
    exact hs1ds
  have hspc5 : s5.stk S.spc = s.stk S.spc := by
    rw [h5fr S.spc (S.ne_sp_spc).symm S.ne_spc_sA S.ne_spc_bA S.ne_spc_bB S.ne_spc_mx]
    rw [h4fr S.spc S.ne_spc_sA S.ne_spc_mx S.ne_spc_bA S.ne_spc_bB]
    exact hs3spc
  have htmp5 : s5.stk S.tmp = s.stk S.tmp := by
    rw [h5fr S.tmp (S.ne_sp_tmp).symm S.ne_tmp_sA S.ne_tmp_bA S.ne_tmp_bB S.ne_tmp_mx]
    rw [h4fr S.tmp S.ne_tmp_sA S.ne_tmp_mx S.ne_tmp_bA S.ne_tmp_bB]
    rw [hs3fr S.tmp (S.ne_spc_tmp).symm S.ne_tmp_sA, hs2tmp]
    exact hs1fr S.tmp S.ne_tmp_src (S.ne_sp_tmp).symm (S.ne_ds_tmp).symm
  -- ## the result
  refine ⟨s6, n1 + (n2 + (n3 + (ns + ((nb + 1) + 1)))), ?_, ?_, ?_, ?_, ?_⟩
  · exact Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq eb e6))))
  · -- cost
    have h1' : n1 ≤ 5 * t.size + 14 := by rw [hBl] at hn1; exact hn1
    have h2' : n2 ≤ 12 * t.size + 24 := by
      rw [List.length_map, List.length_reverse, hBl] at hn2; exact hn2
    have h3' : n3 ≤ 5 * t.size + 13 := by
      rw [List.length_map, List.length_reverse, hBl] at hn3; exact hn3
    have h4' : ns ≤ Ks * (t.size + 1) := by
      refine le_trans hns (Nat.mul_le_mul_left Ks ?_)
      have := Nat.min_le_left B.length MB.length
      omega
    nlinarith [h1', h2', h3', h4', hnb, Nat.zero_le t.size]
  · rw [hs6, tPop_stk, if_neg S.ne_ds_src.symm]
    rw [h5fr src S.ne_sp_src.symm S.ne_sA_src.symm S.ne_bA_src.symm S.ne_bB_src.symm hsm]
    rw [h4fr src S.ne_sA_src.symm hsm S.ne_bA_src.symm S.ne_bB_src.symm]
    rw [hs3fr src S.ne_spc_src.symm S.ne_sA_src.symm]
    rw [hs2fr src S.ne_sp_src.symm S.ne_spc_src.symm S.ne_tmp_src.symm]
    exact hs1src
  · rw [hs6, tPop_stk, if_neg S.ne_ds_mx.symm]; exact h5mx
  · intro j hj1 hj2
    by_cases hd : j = S.ds
    · rw [hd, hs6, tPop_stk, if_pos rfl, hds5]; simp
    · rw [hs6, tPop_stk, if_neg hd]
      by_cases hsp : j = S.sp
      · rw [hsp]; exact h5sp
      by_cases hsA : j = S.sA
      · rw [hsA]; exact h5sA
      by_cases hbA : j = S.bA
      · rw [hbA]; exact h5bA
      by_cases hbB : j = S.bB
      · rw [hbB]; exact h5bB
      by_cases hspc : j = S.spc
      · rw [hspc]; exact hspc5
      by_cases htmp : j = S.tmp
      · rw [htmp]; exact htmp5
      · rw [h5fr j hsp hsA hbA hbB hj2, h4fr j hsA hj2 hbA hbB, hs3fr j hspc hsA,
          hs2fr j hsp hspc htmp, hs1fr j hj1 hsp hd]

end Work.Transform.Pw
