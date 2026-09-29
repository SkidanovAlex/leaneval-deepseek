import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Resample.pbDefs
import Submission.Work.Resample.auLoopDefs
import Submission.Work.Resample.auConvDefs
import Submission.Work.Resample.auDefs
import Submission.Work.Resample.auWinSlice
import Submission.Work.Resample.auElemsElem
import Submission.Work.Resample.auKSum
import Submission.Work.Resample.auSizes
import Submission.Work.Resample.auKArith
import Submission.Work.Resample.auStreamSz
import Submission.Work.Resample.auJoin
import Submission.Work.Resample.auLoopWord
import Submission.Work.Resample.auSetupRun
import Submission.Work.Resample.auWinRecAll
import Submission.Work.Resample.auSplit
import Submission.Work.Resample.wmLoopSent
import Submission.Work.Resample.auRoundAux
import Submission.Work.Resample.auSetupSz
import Submission.Work.Resample.auLoopHyp
import Submission.Work.Resample.auCostArith
import Submission.Work.ConvR.basic
import Submission.Work.Kernel.Raw

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.Resample

open HvdH

/-!
# The setup word of the resampling word (`Work.Resample.auSetup`)

Paper Lemma 4.9 / Theorem 4.1, assembly of the one-dimensional resampling word `q`: the four
words `auSetupRun` (build the extended array, the window and the three runs), `auLoopWord` (the
`t`-round sliding-window loop), `auClearStack` (clean up the temporaries) and `auJoin` (collect
the chunk run into the stream) are composed; the hypotheses of the loop are discharged from
`auLoopHyp`, `auSetupSz` and `auWinRecAll`, and the costs are summed with `auCostArith`.
-/

/-! ## Helpers -/

/-- `WordM.seq` for programs whose costs are constants. -/
theorem WordM.seqK {main p q : Cmd}
    {Pre₁ : List Val → (Stk → List Val) → Prop}
    {Post₁ : List Val → (Stk → List Val) → List Val → (Stk → List Val) → Prop}
    {Pre₂ : List Val → (Stk → List Val) → Prop}
    {Post₂ : List Val → (Stk → List Val) → List Val → (Stk → List Val) → Prop}
    {C₁ C₂ : ℕ} (h₁ : WordM main p Pre₁ Post₁ (fun _ _ => C₁))
    (h₂ : WordM main q Pre₂ Post₂ (fun _ _ => C₂))
    (hpre : ∀ vs a mid a', Post₁ vs a mid a' → Pre₂ mid a') :
    WordM main (.seq p q) Pre₁
      (fun vs a out b => ∃ mid a', Post₁ vs a mid a' ∧ Post₂ mid a' out b)
      (fun _ _ => C₁ + C₂) :=
  WordM.seq h₁ h₂ hpre (fun _ _ _ _ _ => le_rfl)

/-- The last window centre is `s`: `auK s t t = s` for `t > 0`. -/
theorem auK_self {s t : ℕ} (ht : 0 < t) : auK s t t = s := by
  have h2t : 0 < 2 * t := by omega
  rw [auK]
  refine le_antisymm ?_ ?_
  · rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul h2t]
    nlinarith
  · rw [Nat.le_div_iff_mul_le h2t]
    nlinarith

/-- The raw chunk list of the window loop is the stream `auStream`. -/
theorem auStream_map_chunks (p α s t : ℕ) (u : List (ℤ × ℤ)) :
    (List.range t).map (fun k => Val.cons (ofList (auWts p α s t k)) (ofList (auWinV p α s t u k)))
      = auStream p α s t u := by
  simp only [auStream, auChunk, auWinV]

/-- The `getD` of the re-encoded record table, at an in-range index. -/
theorem auRecsF_getD (p α s t k : ℕ) (hk : k < t) :
    (auRecsF p α s t).getD k Val.nil =
      Val.cons (auSeqFlg (auK s t (k + 1) - auK s t k))
        (Val.cons (.int (((auK s t (k + 1) - auK s t k : ℕ) : ℤ))) (ofList (auWts p α s t k))) := by
  have hmono : auK s t k ≤ auK s t (k + 1) := auKArith_mono s t (Nat.le_succ k)
  have hcast : ((auK s t (k + 1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)
      = ((auK s t (k + 1) - auK s t k : ℕ) : ℤ) := (Nat.cast_sub hmono).symm
  have hsome : (List.range t)[k]? = some k := List.getElem?_range hk
  simp only [auRecsF, List.getD_eq_getElem?_getD, List.getElem?_map, hsome, Option.map_some,
    Option.getD_some, auRecF, hcast]

/-- Every entry of the element run is a `cons`-value, so its head glyph is not the sentinel. -/
theorem auElems_enc_ne_nil (p α s : ℕ) (u : List (ℤ × ℤ)) (v : Val) (hv : v ∈ auElems p α s u) :
    (Val.enc v).headD Glyph.eos ≠ Glyph.nil := by
  obtain ⟨z, -, rfl⟩ := List.mem_map.mp hv
  rw [show Val.enc (cfxVal z)
      = Glyph.cons :: (Val.enc (Val.int z.1) ++ Val.enc (Val.int z.2)) from rfl, List.headD_cons]
  decide

/-- The empty value stack encodes to the empty word. -/
theorem encs_nil_au : encs ([] : List Val) = [] := rfl

/-- The element run is short: at most `2s` entries. -/
theorem auElems_length_le (p α s : ℕ) (u : List (ℤ × ℤ)) (hu : u.length = s) :
    (auElems p α s u).length ≤ 2 * s := by
  have h1 : auCop p α s * s ≤ auOff p α s + 2 * s + 2 * auM p α := by
    simp only [auCop]
    exact Nat.div_mul_le_self _ _
  rw [auElems, List.length_map, List.length_drop, auExt_length, hu]
  simp only [auL]
  omega

/-- Clearing a run of values above the `Val.nil` sentinel from a non-zero stack: the sentinel loop
of `wmLoopSent` pops one value at a time (moving it onto the value stack, where the `drop` word of
`KernelLib` destroys it) until the sentinel is on top, and one final `pop` removes the sentinel
glyph.  This is the cleanup used at the end of `auSetup`. -/
theorem auClearAux (hk : HvdH.KernelLib) (k : HvdH.Stk) (hk0 : k ≠ 0) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (L : List HvdH.Val) (B : ℕ)
      (rest : List HvdH.Val),
      (∀ v ∈ L, (HvdH.Val.enc v).headD HvdH.Glyph.eos ≠ HvdH.Glyph.nil) →
      (∀ v ∈ L, HvdH.vsz v ≤ B) →
      WordM main prog
        (fun vs a => vs = rest ∧ a k = L ++ [Val.nil])
        (fun vs a out b => out = rest ∧ b k = [] ∧ (∀ j, j ≠ 0 → j ≠ k → b j = a j))
        (fun _ _ => K * ((L.length + 1) * (B + 1) + 1)) := by
  obtain ⟨popP, Kc, hpop⟩ := auRoundPop k hk0
  obtain ⟨dropP, Kd, hdrop⟩ := hk.drop
  obtain ⟨comb, KL, hloop⟩ := wmLoopSent k hk0
  refine ⟨Cmd.seq (comb (Cmd.seq popP dropP)) (Cmd.pop k 0), Kc + Kd + KL + 1, ?_⟩
  intro main L B rest hhead hsz vs a hpre s0 R Bg h0 hks
  obtain ⟨hvs, ha⟩ := hpre
  let I : ℕ → List Val → (Stk → List Val) → Prop :=
    fun i w b => w = rest ∧ b k = L.drop i ++ [Val.nil] ∧ (∀ j, j ≠ 0 → j ≠ k → b j = a j)
  let F : List Val → (Stk → List Val) → Prop :=
    fun w b => w = rest ∧ b k = [Val.nil] ∧ (∀ j, j ≠ 0 → j ≠ k → b j = a j)
  have hI0 : I 0 vs a := by
    refine ⟨hvs, ?_, fun j _ _ => rfl⟩
    rw [ha, List.drop_zero]
  have hbody : ∀ i w b, I i w b → i < L.length →
      WordM main (Cmd.seq popP dropP) (fun w' b' => w' = w ∧ b' = b)
        (fun _ _ out b' => I (i + 1) out b') (fun _ _ => (Kc + Kd) * (B + 1)) := by
    intro i w b hi hilt
    obtain ⟨hw, hbk, hfr⟩ := hi
    have hdropi : L.drop i = L[i] :: L.drop (i + 1) := List.drop_eq_getElem_cons hilt
    have hsz_i : vsz (L[i]) ≤ B := hsz _ (List.getElem_mem hilt)
    have hb : b k = L[i] :: (L.drop (i + 1) ++ [Val.nil]) := by
      rw [hbk, hdropi]
      rfl
    have h1 := hpop main (L[i]) (L.drop (i + 1) ++ [Val.nil]) w
    have h2 := WordM.ofWordR (hdrop main)
    have hseq := WordM.seq (B := fun _ _ => Kd * (B + 1)) h1 h2
      (fun vs' a' mid a'' h => by
        obtain ⟨hout, -, -⟩ := h
        rw [hout]
        exact List.cons_ne_nil _ _)
      (fun vs' a' mid a'' h => by
        obtain ⟨hout, -, -⟩ := h
        rw [hout]
        exact Nat.mul_le_mul_left Kd (by rw [List.headD_cons]; omega))
    refine WordM.conseq hseq ?_ ?_ ?_
    · intro vs' a' hpre'
      obtain ⟨hw', hb'⟩ := hpre'
      exact ⟨hw', by rw [hb', hb]⟩
    · intro vs' a' out b' hpre' hpost'
      obtain ⟨hw', hb'⟩ := hpre'
      obtain ⟨mid, a'', hP1, hP2⟩ := hpost'
      obtain ⟨hout1, hb1k, hfr1⟩ := hP1
      obtain ⟨⟨v0, r0, hv0, hout2⟩, hfr2⟩ := hP2
      have hr0 : r0 = w := by
        rw [hout1, hw'] at hv0
        injection hv0 with _ hr
        exact hr.symm
      refine ⟨?_, ?_, ?_⟩
      · rw [hout2, hr0, hw]
      · rw [hfr2, hb1k]
      · intro j hj0 hjk
        rw [hfr2, hfr1 j hj0 hjk, hb']
        exact hfr j hj0 hjk
    · intro vs' a' _
      show Kc * (vsz (L[i]) + 1) + Kd * (B + 1) ≤ (Kc + Kd) * (B + 1)
      nlinarith [hsz_i]
  have hcont : ∀ i w b, I i w b → i < L.length →
      b k ≠ [] ∧ (encs (b k)).headD Glyph.eos ≠ Glyph.nil := by
    intro i w b hi hilt
    obtain ⟨hw, hbk, hfr⟩ := hi
    have hdropi : L.drop i = L[i] :: L.drop (i + 1) := List.drop_eq_getElem_cons hilt
    have hhead_i : (Val.enc (L[i])).headD Glyph.eos ≠ Glyph.nil := hhead _ (List.getElem_mem hilt)
    constructor
    · rw [hbk, hdropi]
      exact List.cons_ne_nil _ _
    · rw [hbk, hdropi, List.cons_append, Work.Kernel.encs_cons,
        wmLoopSent_headD_append (Val.enc (L[i]))
          (encs (L.drop (i + 1) ++ [Val.nil])) Glyph.eos (wmLoopSent_enc_ne_nil _)]
      exact hhead_i
  have hexit : ∀ w b, I L.length w b → (encs (b k)).headD Glyph.eos = Glyph.nil := by
    intro w b hi
    obtain ⟨hw, hbk, hfr⟩ := hi
    rw [hbk, List.drop_length, List.nil_append]
    rfl
  have hF : ∀ w b, I L.length w b → F w b := by
    intro w b hi
    obtain ⟨hw, hbk, hfr⟩ := hi
    exact ⟨hw, by rw [hbk, List.drop_length, List.nil_append], hfr⟩
  obtain ⟨outL, bL, sL, nL, hFL, hevL, hcL, h0L, hkL⟩ :=
    hloop main (Cmd.seq popP dropP) I F ((Kc + Kd) * (B + 1)) L.length hbody hcont hexit hF
      vs a hI0 s0 R Bg h0 hks
  obtain ⟨houtL, hbkL, hfrL⟩ := hFL
  have hstk : sL.stk k = Glyph.nil :: Bg k := by
    rw [hkL k hk0, hbkL]
    rfl
  refine ⟨outL, Function.update bL k [], ⟨Function.update sL.reg 0 ((sL.stk k).headD Glyph.eos),
    Function.update sL.stk k (sL.stk k).tail⟩, nL + 1, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨houtL, Function.update_self k [] bL, ?_⟩
    intro j hj0 hjk
    rw [Function.update_of_ne hjk]
    exact hfrL j hj0 hjk
  · exact Eval.seq hevL (Eval.pop k 0 sL)
  · show nL + 1 ≤ (Kc + Kd + KL + 1) * ((L.length + 1) * (B + 1) + 1)
    have hc : nL ≤ (L.length + 1) * ((Kc + Kd) * (B + 1) + KL) + KL := hcL
    have h4 : (L.length + 1) * KL ≤ KL * ((L.length + 1) * (B + 1)) := by
      calc (L.length + 1) * KL = KL * (L.length + 1) := by ring
        _ ≤ KL * (L.length + 1) * (B + 1) := Nat.le_mul_of_pos_right _ (by omega)
        _ = KL * ((L.length + 1) * (B + 1)) := by ring
    have hkey : (L.length + 1) * ((Kc + Kd) * (B + 1) + KL) + KL + 1
        ≤ (Kc + Kd + KL + 1) * ((L.length + 1) * (B + 1) + 1) := by
      nlinarith [h4, Nat.zero_le Kc, Nat.zero_le Kd, Nat.zero_le (L.length), Nat.zero_le B]
    omega
  · show (Function.update sL.stk k (sL.stk k).tail) 0 = encs outL ++ R
    rw [Function.update_of_ne (Ne.symm hk0)]
    exact h0L
  · intro j hj0
    show (Function.update sL.stk k (sL.stk k).tail) j = encs (Function.update bL k [] j) ++ Bg j
    by_cases hjk : j = k
    · rw [hjk]
      rw [Function.update_self, Function.update_self, hstk]
      show Bg k = encs ([] : List Val) ++ Bg k
      rw [encs_nil_au, List.nil_append]
    · rw [Function.update_of_ne hjk, Function.update_of_ne hjk, hkL j hj0]

/-! ## The assembly -/

theorem auSetupAux (hk : HvdH.KernelLib) (hi : HvdH.IntLib) (hl : HvdH.LayoutLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p α s t : ℕ) (u : List (ℤ × ℤ))
      (rest : List HvdH.Val),
      u.length = s → (∀ z ∈ u, HvdH.inDisc p z) → 2 ≤ s → 2 ≤ α → 100 ≤ p → α ^ 2 < p → s < t →
      WordM main prog
        (fun vs a => vs = ofList (u.map cfxVal) :: auPvals p α s t ++ rest ∧ (∀ k, k ≠ 0 → a k = []))
        (fun vs a out b => out = auStreamV p α s t u :: auPvals p α s t ++ rest ∧
          (∀ k, k ≠ 0 → b k = []))
        (fun _ _ => K * ((s + t * auL p α + auCop p α s * s + 1) * (p + 1))) := by
  obtain ⟨prep, K1, hprep⟩ := auSetupRun hk hi hl
  obtain ⟨loop, K2, hloop⟩ := auLoopWord hk hl
  obtain ⟨cl1, Kc1, hcl1⟩ := auClearAux hk (1 : Stk) (by decide)
  obtain ⟨cl2, Kc2, hcl2⟩ := auClearAux hk (2 : Stk) (by decide)
  obtain ⟨cl3, Kc3, hcl3⟩ := auClearAux hk (3 : Stk) (by decide)
  obtain ⟨jn, K3, hjoin⟩ := auJoin hk
  refine ⟨Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq prep loop) cl1) cl2) jn) cl3,
    K1 + 88 * K2 + 2 * Kc1 + 44 * Kc2 + 26 * K3 + 2 * Kc3, ?_⟩
  intro main p α s t u rest hu hd hs hα hp hαp hst
  -- the hypotheses of the loop
  obtain ⟨hSlide, -, hWlen, -, -, hWTSlen, hREClen, hsum, -, -, -, -⟩ :=
    auLoopHyp p α s t u hs hd hα hp hαp hst hu
  obtain ⟨-, hstreamSz, hwtSz, hwin0Sz, helemsSz⟩ := auSetupSz p α s t u hs hst hα hp hαp hu hd
  have hWrec : ∀ k < t, auWinV p α s t u (k + 1) =
      ((auWinV p α s t u k).drop (auK s t (k + 1) - auK s t k) ++
        [(auElems p α s u).getD
          (((List.range k).map (fun j => auK s t (j + 1) - auK s t j)).sum) Val.nil]).take
            (auL p α) :=
    auWinRecAll p α s t u hs hst hu
  have hRECget : ∀ k < t, (auRecsF p α s t).getD k Val.nil =
      Val.cons (auSeqFlg (auK s t (k + 1) - auK s t k))
        (Val.cons (.int (((auK s t (k + 1) - auK s t k : ℕ) : ℤ))) (ofList (auWts p α s t k))) :=
    fun k hk => auRecsF_getD p α s t k hk
  have hW0sz : ∀ v ∈ auWinV p α s t u 0, vsz v ≤ 2 * p + 8 := hwin0Sz
  have hWTSsz : ∀ k < t, ∀ v ∈ auWts p α s t k, vsz v ≤ 2 * p + 8 :=
    fun k hk v hv => le_trans (hwtSz k hk v hv) (by omega)
  have hELEMsz : ∀ v ∈ auElems p α s u, vsz v ≤ 2 * p + 8 := helemsSz
  have hnilSz : vsz (Val.nil) ≤ 2 * p + 8 := by
    have h : vsz (Val.nil) = 1 := by simp [vsz, Val.enc]
    omega
  have hsum_s : ((List.range t).map (fun k => auK s t (k + 1) - auK s t k)).sum = s :=
    (auKSum s t t).trans (auK_self (by omega : 0 < t))
  have hElemlen : (auElems p α s u).length ≤ 2 * s := auElems_length_le p α s u hu
  have hEdrop : ((auElems p α s u).drop s).length ≤ s := by
    rw [List.length_drop]
    omega
  -- the six pieces
  have P1 : WordM main prep
      (fun vs a => vs = ofList (u.map cfxVal) :: auPvals p α s t ++ rest ∧ (∀ k, k ≠ 0 → a k = []))
      (fun vs a out b => out = ofList (auWinV p α s t u 0) :: auPvals p α s t ++ rest ∧
        b 1 = auRecsF p α s t ++ [Val.nil] ∧ b 2 = auElems p α s u ++ [Val.nil] ∧
        b 3 = [Val.nil] ∧ (∀ k, k ≠ 0 → k ≠ 1 → k ≠ 2 → k ≠ 3 → b k = a k))
      (fun _ _ => K1 * ((s + t * auL p α + auCop p α s * s + 1) * (p + 1))) :=
    hprep main p α s t u rest hu hd hs hα hp hαp hst
  have P2 : WordM main loop
      (fun vs a => vs = ofList (auWinV p α s t u 0) :: auPvals p α s t ++ rest ∧
        a 1 = auRecsF p α s t ++ [Val.nil] ∧ a 2 = auElems p α s u ++ [Val.nil] ∧
        a 3 = [Val.nil])
      (fun vs a out b => out = auPvals p α s t ++ rest ∧ b 1 = [Val.nil] ∧
        b 2 = (auElems p α s u).drop
          (((List.range t).map (fun k => auK s t (k + 1) - auK s t k)).sum) ++ [Val.nil] ∧
        b 3 = ((List.range t).map (fun k => Val.cons (ofList (auWts p α s t k))
          (ofList (auWinV p α s t u k)))).reverse ++ [Val.nil] ∧
        (∀ k, k ≠ 0 → k ≠ 1 → k ≠ 2 → k ≠ 3 → b k = a k))
      (fun _ _ => K2 * (t + 1) * ((auL p α + 1) * (2 * p + 8 + 1) + 1)) :=
    hloop main (auL p α) (2 * p + 8) t (fun k => auK s t (k + 1) - auK s t k) (auWts p α s t)
      (auElems p α s u) (auRecsF p α s t) (auPvals p α s t ++ rest) (auWinV p α s t u)
      Val.nil Val.nil Val.nil rfl hSlide hREClen hRECget hWlen hWrec hWTSlen hW0sz hWTSsz hELEMsz
      hnilSz hsum
  have P3 : WordM main cl1
      (fun vs a => vs = auPvals p α s t ++ rest ∧ a 1 = ([] : List Val) ++ [Val.nil])
      (fun vs a out b => out = auPvals p α s t ++ rest ∧ b 1 = [] ∧
        (∀ j, j ≠ 0 → j ≠ 1 → b j = a j))
      (fun _ _ => Kc1 * ((([] : List Val).length + 1) * (0 + 1) + 1)) :=
    hcl1 main ([] : List Val) 0 (auPvals p α s t ++ rest) (by simp) (by simp)
  have P4 : WordM main cl2
      (fun vs a => vs = auPvals p α s t ++ rest ∧ a 2 = (auElems p α s u).drop s ++ [Val.nil])
      (fun vs a out b => out = auPvals p α s t ++ rest ∧ b 2 = [] ∧
        (∀ j, j ≠ 0 → j ≠ 2 → b j = a j))
      (fun _ _ => Kc2 * ((((auElems p α s u).drop s).length + 1) * (2 * p + 8 + 1) + 1)) :=
    hcl2 main ((auElems p α s u).drop s) (2 * p + 8) (auPvals p α s t ++ rest)
      (fun v hv => auElems_enc_ne_nil p α s u v (List.mem_of_mem_drop hv))
      (fun v hv => hELEMsz v (List.mem_of_mem_drop hv))
  have P5 : WordM main jn
      (fun vs a => vs = auPvals p α s t ++ rest ∧
        a 3 = ((List.range t).map (fun k => Val.cons (ofList (auWts p α s t k))
          (ofList (auWinV p α s t u k)))).reverse ++ [Val.nil])
      (fun vs a out b => out = ofList (((List.range t).map (fun k => Val.cons (ofList (auWts p α s t k))
          (ofList (auWinV p α s t u k)))).reverse).reverse :: auPvals p α s t ++ rest ∧
        b 3 = [Val.nil] ∧ (∀ k, k ≠ 0 → k ≠ 3 → b k = a k))
      (fun _ _ => K3 * (vsz (ofList (((List.range t).map (fun k => Val.cons (ofList (auWts p α s t k))
          (ofList (auWinV p α s t u k)))).reverse)) + 1)) :=
    hjoin main _ _
      (fun v hv => by
        obtain ⟨k, -, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hv)
        exact ⟨ofList (auWts p α s t k), ofList (auWinV p α s t u k), rfl⟩)
  have P6 : WordM main cl3
      (fun vs a => vs = ofList (((List.range t).map (fun k => Val.cons (ofList (auWts p α s t k))
          (ofList (auWinV p α s t u k)))).reverse).reverse :: auPvals p α s t ++ rest ∧
        a 3 = ([] : List Val) ++ [Val.nil])
      (fun vs a out b => out = ofList (((List.range t).map (fun k => Val.cons (ofList (auWts p α s t k))
          (ofList (auWinV p α s t u k)))).reverse).reverse :: auPvals p α s t ++ rest ∧
        b 3 = [] ∧ (∀ j, j ≠ 0 → j ≠ 3 → b j = a j))
      (fun _ _ => Kc3 * ((([] : List Val).length + 1) * (0 + 1) + 1)) :=
    hcl3 main ([] : List Val) 0 _ (by simp) (by simp)
  -- the chain
  have h12 := WordM.seqK P1 P2 (fun vs a mid a' h => by
    obtain ⟨hout, hb1, hb2, hb3, _⟩ := h
    exact ⟨hout, hb1, hb2, hb3⟩)
  have h123 := WordM.seqK h12 P3 (fun vs a mid a' h => by
    obtain ⟨m, a2, _, hP2⟩ := h
    obtain ⟨hout, hb1, _⟩ := hP2
    exact ⟨hout, hb1⟩)
  have h1234 := WordM.seqK h123 P4 (fun vs a mid a' h => by
    obtain ⟨m, a2, h12p, hP3⟩ := h
    obtain ⟨hout3, _, hfr3⟩ := hP3
    obtain ⟨m2, a3, _, hP2⟩ := h12p
    obtain ⟨_, _, hb2b, _, _⟩ := hP2
    refine ⟨hout3, ?_⟩
    rw [hfr3 2 (by decide) (by decide), hb2b, hsum_s])
  have h12345 := WordM.seqK h1234 P5 (fun vs a mid a' h => by
    obtain ⟨m, a2, h1234p, hP4⟩ := h
    obtain ⟨hout4, _, hfr4⟩ := hP4
    obtain ⟨m2, a3, h123p, hP3⟩ := h1234p
    obtain ⟨_, _, hfr3⟩ := hP3
    obtain ⟨m3, a4, _, hP2⟩ := h123p
    obtain ⟨_, _, _, hb2c, _⟩ := hP2
    refine ⟨hout4, ?_⟩
    rw [hfr4 3 (by decide) (by decide), hfr3 3 (by decide) (by decide), hb2c])
  have hAll := WordM.seqK h12345 P6 (fun vs a mid a' h => by
    obtain ⟨m, a2, _, hP5⟩ := h
    obtain ⟨hout5, hb5, _⟩ := hP5
    exact ⟨hout5, hb5⟩)
  refine WordM.conseq hAll (fun vs a h => h) ?_ ?_
  · -- the postcondition
    intro vs a out b hpre hpost
    obtain ⟨m1, a1, h12345p, hP6⟩ := hpost
    obtain ⟨m2, a2, h1234p, hP5⟩ := h12345p
    obtain ⟨m3, a3, h123p, hP4⟩ := h1234p
    obtain ⟨m4, a4, h12p, hP3⟩ := h123p
    obtain ⟨m5, a5, hP1, hP2⟩ := h12p
    obtain ⟨hout6, hb6, hfr6⟩ := hP6
    obtain ⟨hout5, hb5, hfr5⟩ := hP5
    obtain ⟨hout4, hb4, hfr4⟩ := hP4
    obtain ⟨hout3, hb3, hfr3⟩ := hP3
    obtain ⟨hout2, hb2a, hb2b, hb2c, hfr2⟩ := hP2
    obtain ⟨hout1, hb1a, hb1b, hb1c, hfr1⟩ := hP1
    refine ⟨?_, ?_⟩
    · rw [hout6, List.reverse_reverse, auStream_map_chunks]
      rfl
    · intro k hk0
      by_cases hk3 : k = 3
      · rw [hk3]; exact hb6
      · rw [hfr6 k hk0 hk3]
        by_cases hk1 : k = 1
        · rw [hk1]
          rw [hfr5 1 (by decide) (by decide), hfr4 1 (by decide) (by decide)]
          exact hb3
        · by_cases hk2 : k = 2
          · rw [hk2]
            rw [hfr5 2 (by decide) (by decide)]
            exact hb4
          · rw [hfr5 k hk0 hk3, hfr4 k hk0 hk2, hfr3 k hk0 hk1,
              hfr2 k hk0 hk1 hk2 hk3, hfr1 k hk0 hk1 hk2 hk3]
            exact hpre.2 k hk0
  · -- the cost
    intro vs a _
    have hL1 : 1 ≤ auL p α := Nat.le_add_left 1 (2 * auM p α)
    have hArith := auCostArith K1 K2 K3 Kc1 Kc2 Kc3 s t (auL p α) (auCop p α s) p
      (((auElems p α s u).drop s).length) (by omega) (by omega) hL1 (by omega) hEdrop
    have hCj : K3 * (vsz (ofList (((List.range t).map (fun k => Val.cons (ofList (auWts p α s t k))
        (ofList (auWinV p α s t u k)))).reverse)) + 1)
        ≤ K3 * (t * (auL p α * (3 * p + 16) + 4) + t + 2) :=
      Nat.mul_le_mul_left K3 (by
        have h1 : vsz (ofList (((List.range t).map (fun k => Val.cons (ofList (auWts p α s t k))
            (ofList (auWinV p α s t u k)))).reverse)) = vsz (auStreamV p α s t u) := by
          rw [vsz_ofList_reverse, auStream_map_chunks]
          rfl
        rw [h1]
        omega)
    simp only [List.length_nil, Nat.zero_add, Nat.mul_one] at *
    nlinarith [hArith, hCj]

theorem auSetup (hk : HvdH.KernelLib) (hi : HvdH.IntLib) (hl : HvdH.LayoutLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p α s t : ℕ) (u : List (ℤ × ℤ)) (rest : List HvdH.Val),
      u.length = s → (∀ z ∈ u, HvdH.inDisc p z) → 2 ≤ s → 2 ≤ α → 100 ≤ p → α ^ 2 < p → s < t →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.ofList (u.map HvdH.cfxVal) :: Work.Resample.auPvals p α s t ++ rest)
        (fun _ out => out = Work.Resample.auStreamV p α s t u :: Work.Resample.auPvals p α s t ++ rest)
        (fun _ => K * ((s + t * Work.Resample.auL p α + Work.Resample.auCop p α s * s + 1) * (p + 1))) := by
  obtain ⟨prog, K, hprog⟩ := auSetupAux hk hi hl
  refine ⟨prog, K, ?_⟩
  intro main p α s t u rest hu hd hs hα hp hαp hst vs hpre s0 R h0
  obtain ⟨out, b, s', n, hPost, hev, hc, h0', hk'⟩ :=
    hprog main p α s t u rest hu hd hs hα hp hαp hst vs (fun _ => []) ⟨hpre, fun k _ => rfl⟩ s0 R
      (fun k => s0.stk k) h0 (fun k _ => by
        show s0.stk k = encs ([] : List Val) ++ s0.stk k
        rw [encs_nil_au, List.nil_append])
  exact ⟨out, s', n, hPost.1, hev, hc, h0', fun k hk0 => by
    rw [hk' k hk0, hPost.2 k hk0, encs_nil_au, List.nil_append]⟩

end Work.Resample
