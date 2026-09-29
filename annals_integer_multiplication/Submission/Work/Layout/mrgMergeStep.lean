import Mathlib
import Submission.Work.Layout.MergeDefs
import Submission.Work.Layout.dupInt_ev
import Submission.Work.Layout.mvVal_ev_full
import Submission.Work.Layout.Move
import Submission.Work.Layout.merge_readFlag
import Submission.Work.Layout.merge_updSizeSkip
import Submission.Work.Layout.mrgDefs
import Submission.Work.Layout.mrgMergeStepPrefix
import Submission.Work.Layout.mrgMergeCmp
import Submission.Work.Layout.mrgMergeMoveQ2
import Submission.Work.Layout.mrgMergeMoveP3

set_option maxHeartbeats 8000000

namespace Work.Layout

open HvdH Work.Layout

/-- arithmetic helpers for the `mrgStep` budget -/
theorem mrgStep_eq_of_lt {KLt KSz k l : ℕ} {v' w' : Val} {ps qs : List Val} (h : l < k) :
    mrgStep KLt KSz (Val.cons (Val.int (k : ℤ)) v') ps (Val.cons (Val.int (l : ℤ)) w') qs
      = cCmp KLt * ((k.size).size + (l.size).size + 4)
        + cMov KLt * (vsz (Val.cons (Val.int (l : ℤ)) w') + 1)
        + cExp KSz * (vsz (if qs = [] then Val.nil else qs.headD Val.nil) + 2) + cK := by
  unfold mrgStep
  rw [keyOf_record, keyOf_record]
  simp only [ite_eq_left h]

theorem mrgStep_eq_of_ge {KLt KSz k l : ℕ} {v' w' : Val} {ps qs : List Val} (h : ¬ l < k) :
    mrgStep KLt KSz (Val.cons (Val.int (k : ℤ)) v') ps (Val.cons (Val.int (l : ℤ)) w') qs
      = cCmp KLt * ((k.size).size + (l.size).size + 4)
        + cMov KLt * (vsz (Val.cons (Val.int (k : ℤ)) v') + 1)
        + cExp KSz * (vsz (if ps = [] then Val.nil else ps.headD Val.nil) + 2) + cK := by
  unfold mrgStep
  rw [keyOf_record, keyOf_record]
  simp only [ite_eq_right h]

/-- the `cExp` term of the budget covers the cost of the (size) update or of the skip -/
theorem updSize_or_skip_le_cExp (KSz : ℕ) (qs : List Val)
    (hqs : ∀ v ∈ qs, ∃ (k' : ℕ) (v'' : Val), v = Val.cons (Val.int (k' : ℤ)) v'') :
    (if qs = [] then 4 else updSizeCost KSz (keyOf (qs.headD Val.nil)))
      ≤ cExp KSz * (vsz (if qs = [] then Val.nil else qs.headD Val.nil) + 2) := by
  by_cases hq : qs = []
  · rw [ite_eq_left hq, ite_eq_left hq]
    exact four_le_cExp_nil KSz
  · obtain ⟨k', v'', hv, hkey⟩ := headD_record hqs hq
    rw [ite_eq_right hq, ite_eq_right hq]
    rw [hkey, hv]
    exact updSizeCost_le_cExp KSz k' v''

/-- pushing `cons` twice (restoring the two records) -/
theorem pushConst_pair {main : Cmd} {SX SY T SA SB F1 F2 t d : Stk}
    (hdis : ([SX, SY, T, SA, SB, F1, F2, t, d, 0] : List Stk).Nodup) {g : Reg → Glyph}
    {X : Stk → List Glyph} :
    ∃ s' n, Ev main (seqs [pushConst SX Glyph.cons, pushConst SY Glyph.cons]) ⟨g, X⟩ s' n ∧
      n ≤ 4 ∧ s'.stk SX = Glyph.cons :: X SX ∧ s'.stk SY = Glyph.cons :: X SY ∧
      s'.stk T = X T ∧ s'.stk SA = X SA ∧ s'.stk SB = X SB ∧ s'.stk F1 = X F1 ∧
      s'.stk F2 = X F2 ∧ s'.stk t = X t ∧ s'.stk d = X d ∧ s'.stk 0 = X 0 ∧
      (∀ k', k' ∉ ({SX, SY, SA, SB, T, F1, F2, t, d, 0} : Finset Stk) → s'.stk k' = X k') := by
  have nSX : ∀ x ∈ ([SY, T, SA, SB, F1, F2, t, d, 0] : List Stk), x ≠ SX := by
    intro x hx h
    subst h
    exact (List.nodup_cons.mp hdis).1 hx
  have nSY : ∀ x ∈ ([T, SA, SB, F1, F2, t, d, 0] : List Stk), x ≠ SY := by
    intro x hx h
    subst h
    exact (List.nodup_cons.mp (List.nodup_cons.mp hdis).2).1 hx
  have hSXSY : SX ≠ SY := (nSX SY (by simp)).symm
  obtain ⟨s₁, n₁, h₁, hn₁, hSX₁, hfr₁, -, -⟩ :=
    pushConst_ev (main := main) (k := SX) (cst := Glyph.cons) (g := g) (X := X)
  obtain ⟨s₂, n₂, h₂, hn₂, hSY₂, hfr₂, -, -⟩ :=
    pushConst_ev (main := main) (k := SY) (cst := Glyph.cons) (g := s₁.reg) (X := s₁.stk)
  refine ⟨s₂, n₁ + n₂, Ev.seq' h₁ h₂ (by omega), by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfr₂ SX hSXSY, hSX₁]
  · rw [hSY₂, hfr₁ SY hSXSY.symm]
  · rw [hfr₂ T (nSY T (by simp)), hfr₁ T (nSX T (by simp))]
  · rw [hfr₂ SA (nSY SA (by simp)), hfr₁ SA (nSX SA (by simp))]
  · rw [hfr₂ SB (nSY SB (by simp)), hfr₁ SB (nSX SB (by simp))]
  · rw [hfr₂ F1 (nSY F1 (by simp)), hfr₁ F1 (nSX F1 (by simp))]
  · rw [hfr₂ F2 (nSY F2 (by simp)), hfr₁ F2 (nSX F2 (by simp))]
  · rw [hfr₂ t (nSY t (by simp)), hfr₁ t (nSX t (by simp))]
  · rw [hfr₂ d (nSY d (by simp)), hfr₁ d (nSX d (by simp))]
  · rw [hfr₂ 0 (nSY 0 (by simp)), hfr₁ 0 (nSX 0 (by simp))]
  · intro k' hk
    have hkSY : k' ≠ SY := fun hh => hk (by simp [hh])
    have hkSX : k' ≠ SX := fun hh => hk (by simp [hh])
    rw [hfr₂ k' hkSY, hfr₁ k' hkSX]

private theorem mrgMergeStep_mk {main pLt pSize : Cmd} {KLt KSz : ℕ}
    {SX SY T SA SB F1 F2 t d : Stk} {g : Reg → Glyph} {X : Stk → List Glyph}
    {k l : ℕ} {v' w' : Val} {ps qs : List Val} {A B' Tc R Sc Sc' : List Glyph}
    : ∀ (s' : State) (n : ℕ),
      Ev main (Sk.mergeStep pLt pSize SX SY SA SB T F1 F2 t d) ⟨g, X⟩ s' n →
      n ≤ mrgStepCore KLt KSz (Val.cons (Val.int (k : ℤ)) v') ps (Val.cons (Val.int (l : ℤ)) w') qs →
      s'.stk 0 = R →
      s'.stk T = (if l < k then (Val.cons (Val.int (l : ℤ)) w').enc ++ Tc else (Val.cons (Val.int (k : ℤ)) v').enc ++ Tc) →
      s'.stk SX = (if l < k then (Val.cons (Val.int (k : ℤ)) v').enc ++ encs ps ++ gMark :: A else encs ps ++ gMark :: A) →
      s'.stk SY = (if l < k then encs qs ++ gMark :: B' else (Val.cons (Val.int (l : ℤ)) w').enc ++ encs qs ++ gMark :: B') →
      s'.stk SA = (if l < k then X SA else if ps = [] then X SA else (Val.int ((keyOf (ps.headD Val.nil)).size : ℤ)).enc ++ (Val.int (k.size : ℤ)).enc ++ Sc) →
      s'.stk SB = (if l < k then (if qs = [] then X SB else (Val.int ((keyOf (qs.headD Val.nil)).size : ℤ)).enc ++ (Val.int (l.size : ℤ)).enc ++ Sc') else X SB) →
      s'.stk F1 = X F1 → s'.stk F2 = X F2 → s'.stk t = X t → s'.stk d = X d →
      (∀ k' : Stk, k' ∉ ({SX, SY, SA, SB, T, F1, F2, t, d, 0} : Finset Stk) → s'.stk k' = X k') →
      ∃ s' n, Ev main (Sk.mergeStep pLt pSize SX SY SA SB T F1 F2 t d) ⟨g, X⟩ s' n ∧
        n ≤ mrgStepCore KLt KSz (Val.cons (Val.int (k : ℤ)) v') ps (Val.cons (Val.int (l : ℤ)) w') qs ∧
        s'.stk 0 = R ∧
        s'.stk T = (if l < k then (Val.cons (Val.int (l : ℤ)) w').enc ++ Tc else (Val.cons (Val.int (k : ℤ)) v').enc ++ Tc) ∧
        s'.stk SX = (if l < k then (Val.cons (Val.int (k : ℤ)) v').enc ++ encs ps ++ gMark :: A else encs ps ++ gMark :: A) ∧
        s'.stk SY = (if l < k then encs qs ++ gMark :: B' else (Val.cons (Val.int (l : ℤ)) w').enc ++ encs qs ++ gMark :: B') ∧
        s'.stk SA = (if l < k then X SA else if ps = [] then X SA else (Val.int ((keyOf (ps.headD Val.nil)).size : ℤ)).enc ++ (Val.int (k.size : ℤ)).enc ++ Sc) ∧
        s'.stk SB = (if l < k then (if qs = [] then X SB else (Val.int ((keyOf (qs.headD Val.nil)).size : ℤ)).enc ++ (Val.int (l.size : ℤ)).enc ++ Sc') else X SB) ∧
        s'.stk F1 = X F1 ∧ s'.stk F2 = X F2 ∧ s'.stk t = X t ∧ s'.stk d = X d ∧
        (∀ k' : Stk, k' ∉ ({SX, SY, SA, SB, T, F1, F2, t, d, 0} : Finset Stk) → s'.stk k' = X k') := by
    intro s' n hev hc h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    exact ⟨s', n, hev, hc, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

private theorem mrgMergeStep_A1 {main pLt pSize : Cmd} {KLt KSz : ℕ}
    (hLt : ∀ main : Cmd, BinOp main pLt (fun _ _ => True) (fun a b => if a < b then 1 else 0)
      (fun a b => KLt * (isz a + isz b)))
    (hSz : ∀ main : Cmd, UnOp main pSize (fun _ => True) (fun a => (a.natAbs.size : ℤ))
      (fun a => KSz * isz a))
    {SX SY T SA SB F1 F2 t d : Stk}
    (hdis : ([SX, SY, T, SA, SB, F1, F2, t, d, 0] : List Stk).Nodup)
    {g : Reg → Glyph} {X : Stk → List Glyph} {k l : ℕ} {v' w' : Val} {ps qs : List Val}
    {A B' Tc R Sc Sc' : List Glyph}
    (hps : ∀ v ∈ ps, ∃ (k' : ℕ) (v'' : Val), v = Val.cons (Val.int (k' : ℤ)) v'')
    (hqs : ∀ v ∈ qs, ∃ (k' : ℕ) (v'' : Val), v = Val.cons (Val.int (k' : ℤ)) v'')
    (hSX : X SX = (Val.cons (Val.int (k : ℤ)) v').enc ++ encs ps ++ gMark :: A)
    (hSY : X SY = (Val.cons (Val.int (l : ℤ)) w').enc ++ encs qs ++ gMark :: B')
    (hSA : X SA = (Val.int (k.size : ℤ)).enc ++ Sc)
    (hSB : X SB = (Val.int (l.size : ℤ)).enc ++ Sc')
    (hT : X T = Tc) (h0 : X 0 = R)  (h1 : l.size < k.size) :
    ∃ s' n, Ev main (Sk.mergeStep pLt pSize SX SY SA SB T F1 F2 t d) ⟨g, X⟩ s' n ∧
      n ≤ mrgStepCore KLt KSz (Val.cons (Val.int (k : ℤ)) v') ps (Val.cons (Val.int (l : ℤ)) w') qs ∧
      s'.stk 0 = R ∧
      s'.stk T = (if l < k then (Val.cons (Val.int (l : ℤ)) w').enc ++ Tc else (Val.cons (Val.int (k : ℤ)) v').enc ++ Tc) ∧
      s'.stk SX = (if l < k then (Val.cons (Val.int (k : ℤ)) v').enc ++ encs ps ++ gMark :: A else encs ps ++ gMark :: A) ∧
      s'.stk SY = (if l < k then encs qs ++ gMark :: B' else (Val.cons (Val.int (l : ℤ)) w').enc ++ encs qs ++ gMark :: B') ∧
      s'.stk SA = (if l < k then X SA else if ps = [] then X SA else (Val.int ((keyOf (ps.headD Val.nil)).size : ℤ)).enc ++ (Val.int (k.size : ℤ)).enc ++ Sc) ∧
      s'.stk SB = (if l < k then (if qs = [] then X SB else (Val.int ((keyOf (qs.headD Val.nil)).size : ℤ)).enc ++ (Val.int (l.size : ℤ)).enc ++ Sc') else X SB) ∧
      s'.stk F1 = X F1 ∧ s'.stk F2 = X F2 ∧ s'.stk t = X t ∧ s'.stk d = X d ∧
      (∀ k' : Stk, k' ∉ ({SX, SY, SA, SB, T, F1, F2, t, d, 0} : Finset Stk) → s'.stk k' = X k') := by
  have hdis' := hdis
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.mem_singleton, not_or] at hdis'
  obtain ⟨s₁, n₁, hev₁, hn₁, h0₁, hSX₁, hSY₁, hT₁, hSA₁, hSB₁, hF1₁, hF2₁, ht₁, hd₁, hrH₁, hrG₁, hfr₁⟩ :=
    mrgMergeStepPrefix (main := main) (pLt := pLt) (g := g) (X := X) hLt hdis hSX hSY hSA hSB h0
  have hlt : l < k := lt_of_size_lt h1
  have hrH : s₁.reg Sk.rH = Glyph.bit true := by rw [hrH₁, ite_eq_left h1]
  obtain ⟨sb, npc, hpc, hnpc, hSXp, hSYp, hTp, hSAp, hSBp, hF1p, hF2p, htp, hdp, h0p, hfrp⟩ :=
    pushConst_pair (main := main) (SX := SX) (SY := SY) (T := T) (SA := SA) (SB := SB)
      (F1 := F1) (F2 := F2) (t := t) (d := d) hdis (g := s₁.reg) (X := s₁.stk)
  have hSXsb : sb.stk SX = (Val.cons (Val.int (k : ℤ)) v').enc ++ encs ps ++ gMark :: A := by
    rw [hSXp, hSX₁]
    exact record_cons_recomp k v' ps A
  have hSYsb : sb.stk SY = (Val.cons (Val.int (l : ℤ)) w').enc ++ encs qs ++ gMark :: B' := by
    rw [hSYp, hSY₁]
    exact record_cons_recomp l w' qs B'
  have hTsb : sb.stk T = Tc := by rw [hTp, hT₁, hT]
  have h0sb : sb.stk 0 = R := by rw [h0p, h0₁]
  obtain ⟨s', nc, hevc, hnc, hSXc, hSYc, hTc, h0c, hSAc, hSBc, hF1c, hF2c, htc, hdc, hfrc⟩ :=
    mrgMergeMoveQ2 (main := main) (pSize := pSize) hSz hdis hqs (g := sb.reg) (X := sb.stk)
      hSXsb hSYsb hTsb h0sb
  have hA1 : Ev main (seqs [pushConst SX Glyph.cons, pushConst SY Glyph.cons, mvVal SY T t d,
      Sk.updSize pSize SY SB t d]) s₁ s' (npc + nc) := Ev.seqs_append hpc hevc
  have htail : Ev main (mrgTail pLt pSize SX SY SA SB T F1 F2 t d) s₁ s' (npc + nc + 1) :=
    Ev.iteT hrH hA1
  have hwhole : Ev main (Sk.mergeStep pLt pSize SX SY SA SB T F1 F2 t d) ⟨g, X⟩ s'
      (n₁ + (npc + nc + 1)) := by
    rw [mergeStep_eq]
    exact Ev.seqs_append (by simpa only [mrgPreL] using hev₁) htail
  have hcost : n₁ + (npc + nc + 1) ≤ mrgStepCore KLt KSz (Val.cons (Val.int (k : ℤ)) v') ps
      (Val.cons (Val.int (l : ℤ)) w') qs := by
    have h1' : n₁ ≤ 2 * KLt * ((k.size).size + (l.size).size + 4)
        + 80 * ((k.size).size + (l.size).size) + 622 := by
      have h := hn₁
      simp only [isz_ksv] at h
      nlinarith [h]
    have h2' : nc ≤ 16 * (vsz (Val.cons (Val.int (l : ℤ)) w') + 1)
        + cExp KSz * (vsz (if qs = [] then Val.nil else qs.headD Val.nil) + 2) := by
      have h := hnc
      have hq := updSize_or_skip_le_cExp KSz qs hqs
      linarith [h, hq]
    have h2'' : nc ≤ 16 * (vsz (Val.cons (Val.int (l : ℤ)) w') + 1)
        + (60 + KSz) * (vsz (if qs = [] then Val.nil else qs.headD Val.nil) + 2) := by
      simpa only [cExp] using h2'
    have hmain : n₁ + (npc + nc + 1) + 20 ≤ mrgStep KLt KSz (Val.cons (Val.int (k : ℤ)) v') ps
        (Val.cons (Val.int (l : ℤ)) w') qs := by
      rw [mrgStep_eq_of_lt hlt]
      have hVQ : 1 ≤ vsz (Val.cons (Val.int (l : ℤ)) w') := one_le_vsz _
      simp only [cCmp, cMov, cExp, cK]
      nlinarith [h1', h2'', hnpc, hVQ]
    rw [mrgStepCore]
    omega
  have h0' : s'.stk 0 = R := h0c
  have hT' : s'.stk T = (if l < k then (Val.cons (Val.int (l : ℤ)) w').enc ++ Tc
      else (Val.cons (Val.int (k : ℤ)) v').enc ++ Tc) := by
    rw [ite_eq_left hlt, hTc]
  have hSX' : s'.stk SX = (if l < k then (Val.cons (Val.int (k : ℤ)) v').enc ++ encs ps ++ gMark :: A
      else encs ps ++ gMark :: A) := by
    rw [ite_eq_left hlt, hSXc, hSXsb]
  have hSY' : s'.stk SY = (if l < k then encs qs ++ gMark :: B'
      else (Val.cons (Val.int (l : ℤ)) w').enc ++ encs qs ++ gMark :: B') := by
    rw [ite_eq_left hlt]
    exact hSYc
  have hSA' : s'.stk SA = (if l < k then X SA else if ps = [] then X SA
      else (Val.int ((keyOf (ps.headD Val.nil)).size : ℤ)).enc ++ (Val.int (k.size : ℤ)).enc ++ Sc) := by
    rw [ite_eq_left hlt, hSAc, hSAp, hSA₁]
  have hSB' : s'.stk SB = (if l < k then (if qs = [] then X SB
      else (Val.int ((keyOf (qs.headD Val.nil)).size : ℤ)).enc ++ (Val.int (l.size : ℤ)).enc ++ Sc')
      else X SB) := by
    rw [ite_eq_left hlt, hSBc, hSBp, hSB₁]
    by_cases hq : qs = []
    · rw [ite_eq_left hq, ite_eq_left hq]
    · rw [ite_eq_right hq, ite_eq_right hq, hSB, List.append_assoc]
  have hF1' : s'.stk F1 = X F1 := by rw [hF1c, hF1p, hF1₁]
  have hF2' : s'.stk F2 = X F2 := by rw [hF2c, hF2p, hF2₁]
  have ht' : s'.stk t = X t := by rw [htc, htp, ht₁]
  have hd' : s'.stk d = X d := by rw [hdc, hdp, hd₁]
  have hfr' : ∀ k' : Stk, k' ∉ ({SX, SY, SA, SB, T, F1, F2, t, d, 0} : Finset Stk) →
      s'.stk k' = X k' := by
    intro k' hk
    have hk9 : k' ∉ ({SX, SY, SA, SB, F1, F2, t, d, 0} : Finset Stk) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk ⊢
      tauto
    have hkSY : k' ≠ SY := fun h => hk (by simp [h])
    have hkSX : k' ≠ SX := fun h => hk (by simp [h])
    rw [hfrc k' hk, hfrp k' hk, hfr₁ k' hk9]
  exact mrgMergeStep_mk s' (n₁ + (npc + nc + 1)) hwhole hcost h0' hT' hSX' hSY' hSA' hSB' hF1' hF2' ht' hd' hfr'

private theorem mrgMergeStep_A2 {main pLt pSize : Cmd} {KLt KSz : ℕ}
    (hLt : ∀ main : Cmd, BinOp main pLt (fun _ _ => True) (fun a b => if a < b then 1 else 0)
      (fun a b => KLt * (isz a + isz b)))
    (hSz : ∀ main : Cmd, UnOp main pSize (fun _ => True) (fun a => (a.natAbs.size : ℤ))
      (fun a => KSz * isz a))
    {SX SY T SA SB F1 F2 t d : Stk}
    (hdis : ([SX, SY, T, SA, SB, F1, F2, t, d, 0] : List Stk).Nodup)
    {g : Reg → Glyph} {X : Stk → List Glyph} {k l : ℕ} {v' w' : Val} {ps qs : List Val}
    {A B' Tc R Sc Sc' : List Glyph}
    (hps : ∀ v ∈ ps, ∃ (k' : ℕ) (v'' : Val), v = Val.cons (Val.int (k' : ℤ)) v'')
    (hqs : ∀ v ∈ qs, ∃ (k' : ℕ) (v'' : Val), v = Val.cons (Val.int (k' : ℤ)) v'')
    (hSX : X SX = (Val.cons (Val.int (k : ℤ)) v').enc ++ encs ps ++ gMark :: A)
    (hSY : X SY = (Val.cons (Val.int (l : ℤ)) w').enc ++ encs qs ++ gMark :: B')
    (hSA : X SA = (Val.int (k.size : ℤ)).enc ++ Sc)
    (hSB : X SB = (Val.int (l.size : ℤ)).enc ++ Sc')
    (hT : X T = Tc) (h0 : X 0 = R)  (h1 : ¬ l.size < k.size) (h2 : k.size < l.size) :
    ∃ s' n, Ev main (Sk.mergeStep pLt pSize SX SY SA SB T F1 F2 t d) ⟨g, X⟩ s' n ∧
      n ≤ mrgStepCore KLt KSz (Val.cons (Val.int (k : ℤ)) v') ps (Val.cons (Val.int (l : ℤ)) w') qs ∧
      s'.stk 0 = R ∧
      s'.stk T = (if l < k then (Val.cons (Val.int (l : ℤ)) w').enc ++ Tc else (Val.cons (Val.int (k : ℤ)) v').enc ++ Tc) ∧
      s'.stk SX = (if l < k then (Val.cons (Val.int (k : ℤ)) v').enc ++ encs ps ++ gMark :: A else encs ps ++ gMark :: A) ∧
      s'.stk SY = (if l < k then encs qs ++ gMark :: B' else (Val.cons (Val.int (l : ℤ)) w').enc ++ encs qs ++ gMark :: B') ∧
      s'.stk SA = (if l < k then X SA else if ps = [] then X SA else (Val.int ((keyOf (ps.headD Val.nil)).size : ℤ)).enc ++ (Val.int (k.size : ℤ)).enc ++ Sc) ∧
      s'.stk SB = (if l < k then (if qs = [] then X SB else (Val.int ((keyOf (qs.headD Val.nil)).size : ℤ)).enc ++ (Val.int (l.size : ℤ)).enc ++ Sc') else X SB) ∧
      s'.stk F1 = X F1 ∧ s'.stk F2 = X F2 ∧ s'.stk t = X t ∧ s'.stk d = X d ∧
      (∀ k' : Stk, k' ∉ ({SX, SY, SA, SB, T, F1, F2, t, d, 0} : Finset Stk) → s'.stk k' = X k') := by
  have hdis' := hdis
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.mem_singleton, not_or] at hdis'
  obtain ⟨s₁, n₁, hev₁, hn₁, h0₁, hSX₁, hSY₁, hT₁, hSA₁, hSB₁, hF1₁, hF2₁, ht₁, hd₁, hrH₁, hrG₁, hfr₁⟩ :=
    mrgMergeStepPrefix (main := main) (pLt := pLt) (g := g) (X := X) hLt hdis hSX hSY hSA hSB h0
  have hlt2 : k < l := lt_of_size_lt h2
  have hge : ¬ l < k := by omega
  have hrHne : s₁.reg Sk.rH ≠ Glyph.bit true := by rw [hrH₁, ite_eq_right h1]; decide
  have hrG : s₁.reg Sk.rG = Glyph.bit true := by rw [hrG₁, ite_eq_left h2]
  obtain ⟨sb, npc, hpc, hnpc, hSXp, hSYp, hTp, hSAp, hSBp, hF1p, hF2p, htp, hdp, h0p, hfrp⟩ :=
    pushConst_pair (main := main) (SX := SX) (SY := SY) (T := T) (SA := SA) (SB := SB)
      (F1 := F1) (F2 := F2) (t := t) (d := d) hdis (g := s₁.reg) (X := s₁.stk)
  have hSXsb : sb.stk SX = (Val.cons (Val.int (k : ℤ)) v').enc ++ encs ps ++ gMark :: A := by
    rw [hSXp, hSX₁]
    exact record_cons_recomp k v' ps A
  have hSYsb : sb.stk SY = (Val.cons (Val.int (l : ℤ)) w').enc ++ encs qs ++ gMark :: B' := by
    rw [hSYp, hSY₁]
    exact record_cons_recomp l w' qs B'
  have hTsb : sb.stk T = Tc := by rw [hTp, hT₁, hT]
  have h0sb : sb.stk 0 = R := by rw [h0p, h0₁]
  obtain ⟨s', nc, hevc, hnc, hSXc, hSYc, hTc, h0c, hSAc, hSBc, hF1c, hF2c, htc, hdc, hfrc⟩ :=
    mrgMergeMoveP3 (main := main) (pSize := pSize) hSz hdis hps (g := sb.reg) (X := sb.stk)
      hSXsb hTsb h0sb
  have hA2 : Ev main (seqs [pushConst SX Glyph.cons, pushConst SY Glyph.cons, mvVal SX T t d,
      Sk.updSize pSize SX SA t d]) s₁ s' (npc + nc) := Ev.seqs_append hpc hevc
  have htail : Ev main (mrgTail pLt pSize SX SY SA SB T F1 F2 t d) s₁ s' (npc + nc + 2) :=
    Ev.iteF hrHne (Ev.iteT hrG hA2)
  have hwhole : Ev main (Sk.mergeStep pLt pSize SX SY SA SB T F1 F2 t d) ⟨g, X⟩ s'
      (n₁ + (npc + nc + 2)) := by
    rw [mergeStep_eq]
    exact Ev.seqs_append (by simpa only [mrgPreL] using hev₁) htail
  have hcost : n₁ + (npc + nc + 2) ≤ mrgStepCore KLt KSz (Val.cons (Val.int (k : ℤ)) v') ps
      (Val.cons (Val.int (l : ℤ)) w') qs := by
    have h1' : n₁ ≤ 2 * KLt * ((k.size).size + (l.size).size + 4)
        + 80 * ((k.size).size + (l.size).size) + 622 := by
      have h := hn₁
      simp only [isz_ksv] at h
      nlinarith [h]
    have h2' : nc ≤ 16 * (vsz (Val.cons (Val.int (k : ℤ)) v') + 1)
        + cExp KSz * (vsz (if ps = [] then Val.nil else ps.headD Val.nil) + 2) := by
      have h := hnc
      have hq := updSize_or_skip_le_cExp KSz ps hps
      linarith [h, hq]
    have h2'' : nc ≤ 16 * (vsz (Val.cons (Val.int (k : ℤ)) v') + 1)
        + (60 + KSz) * (vsz (if ps = [] then Val.nil else ps.headD Val.nil) + 2) := by
      simpa only [cExp] using h2'
    have hmain : n₁ + (npc + nc + 2) + 20 ≤ mrgStep KLt KSz (Val.cons (Val.int (k : ℤ)) v') ps
        (Val.cons (Val.int (l : ℤ)) w') qs := by
      rw [mrgStep_eq_of_ge hge]
      have hVP : 1 ≤ vsz (Val.cons (Val.int (k : ℤ)) v') := one_le_vsz _
      simp only [cCmp, cMov, cExp, cK]
      nlinarith [h1', h2'', hnpc, hVP]
    rw [mrgStepCore]
    omega
  have h0' : s'.stk 0 = R := h0c
  have hT' : s'.stk T = (if l < k then (Val.cons (Val.int (l : ℤ)) w').enc ++ Tc
      else (Val.cons (Val.int (k : ℤ)) v').enc ++ Tc) := by
    rw [ite_eq_right hge, hTc]
  have hSX' : s'.stk SX = (if l < k then (Val.cons (Val.int (k : ℤ)) v').enc ++ encs ps ++ gMark :: A
      else encs ps ++ gMark :: A) := by
    rw [ite_eq_right hge]
    exact hSXc
  have hSY' : s'.stk SY = (if l < k then encs qs ++ gMark :: B'
      else (Val.cons (Val.int (l : ℤ)) w').enc ++ encs qs ++ gMark :: B') := by
    rw [ite_eq_right hge, hSYc, hSYp, hSY₁]
    exact record_cons_recomp l w' qs B'
  have hSA' : s'.stk SA = (if l < k then X SA else if ps = [] then X SA
      else (Val.int ((keyOf (ps.headD Val.nil)).size : ℤ)).enc ++ (Val.int (k.size : ℤ)).enc ++ Sc) := by
    rw [ite_eq_right hge, hSAc, hSAp, hSA₁]
    by_cases hp : ps = []
    · rw [ite_eq_left hp, ite_eq_left hp]
    · rw [ite_eq_right hp, ite_eq_right hp, hSA, List.append_assoc]
  have hSB' : s'.stk SB = (if l < k then (if qs = [] then X SB
      else (Val.int ((keyOf (qs.headD Val.nil)).size : ℤ)).enc ++ (Val.int (l.size : ℤ)).enc ++ Sc')
      else X SB) := by
    rw [ite_eq_right hge, hSBc, hSBp, hSB₁]
  have hF1' : s'.stk F1 = X F1 := by rw [hF1c, hF1p, hF1₁]
  have hF2' : s'.stk F2 = X F2 := by rw [hF2c, hF2p, hF2₁]
  have ht' : s'.stk t = X t := by rw [htc, htp, ht₁]
  have hd' : s'.stk d = X d := by rw [hdc, hdp, hd₁]
  have hfr' : ∀ k' : Stk, k' ∉ ({SX, SY, SA, SB, T, F1, F2, t, d, 0} : Finset Stk) →
      s'.stk k' = X k' := by
    intro k' hk
    have hk9 : k' ∉ ({SX, SY, SA, SB, F1, F2, t, d, 0} : Finset Stk) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk ⊢
      tauto
    have hkSY : k' ≠ SY := fun h => hk (by simp [h])
    have hkSX : k' ≠ SX := fun h => hk (by simp [h])
    rw [hfrc k' hk, hfrp k' hk, hfr₁ k' hk9]
  exact mrgMergeStep_mk s' (n₁ + (npc + nc + 2)) hwhole hcost h0' hT' hSX' hSY' hSA' hSB' hF1' hF2' ht' hd' hfr'

private theorem mrgMergeStep_A3Q {main pLt pSize : Cmd} {KLt KSz : ℕ}
    (hLt : ∀ main : Cmd, BinOp main pLt (fun _ _ => True) (fun a b => if a < b then 1 else 0)
      (fun a b => KLt * (isz a + isz b)))
    (hSz : ∀ main : Cmd, UnOp main pSize (fun _ => True) (fun a => (a.natAbs.size : ℤ))
      (fun a => KSz * isz a))
    {SX SY T SA SB F1 F2 t d : Stk}
    (hdis : ([SX, SY, T, SA, SB, F1, F2, t, d, 0] : List Stk).Nodup)
    {g : Reg → Glyph} {X : Stk → List Glyph} {k l : ℕ} {v' w' : Val} {ps qs : List Val}
    {A B' Tc R Sc Sc' : List Glyph}
    (hps : ∀ v ∈ ps, ∃ (k' : ℕ) (v'' : Val), v = Val.cons (Val.int (k' : ℤ)) v'')
    (hqs : ∀ v ∈ qs, ∃ (k' : ℕ) (v'' : Val), v = Val.cons (Val.int (k' : ℤ)) v'')
    (hSX : X SX = (Val.cons (Val.int (k : ℤ)) v').enc ++ encs ps ++ gMark :: A)
    (hSY : X SY = (Val.cons (Val.int (l : ℤ)) w').enc ++ encs qs ++ gMark :: B')
    (hSA : X SA = (Val.int (k.size : ℤ)).enc ++ Sc)
    (hSB : X SB = (Val.int (l.size : ℤ)).enc ++ Sc')
    (hT : X T = Tc) (h0 : X 0 = R)  (h1 : ¬ l.size < k.size) (h2 : ¬ k.size < l.size) (h3 : l < k) :
    ∃ s' n, Ev main (Sk.mergeStep pLt pSize SX SY SA SB T F1 F2 t d) ⟨g, X⟩ s' n ∧
      n ≤ mrgStepCore KLt KSz (Val.cons (Val.int (k : ℤ)) v') ps (Val.cons (Val.int (l : ℤ)) w') qs ∧
      s'.stk 0 = R ∧
      s'.stk T = (if l < k then (Val.cons (Val.int (l : ℤ)) w').enc ++ Tc else (Val.cons (Val.int (k : ℤ)) v').enc ++ Tc) ∧
      s'.stk SX = (if l < k then (Val.cons (Val.int (k : ℤ)) v').enc ++ encs ps ++ gMark :: A else encs ps ++ gMark :: A) ∧
      s'.stk SY = (if l < k then encs qs ++ gMark :: B' else (Val.cons (Val.int (l : ℤ)) w').enc ++ encs qs ++ gMark :: B') ∧
      s'.stk SA = (if l < k then X SA else if ps = [] then X SA else (Val.int ((keyOf (ps.headD Val.nil)).size : ℤ)).enc ++ (Val.int (k.size : ℤ)).enc ++ Sc) ∧
      s'.stk SB = (if l < k then (if qs = [] then X SB else (Val.int ((keyOf (qs.headD Val.nil)).size : ℤ)).enc ++ (Val.int (l.size : ℤ)).enc ++ Sc') else X SB) ∧
      s'.stk F1 = X F1 ∧ s'.stk F2 = X F2 ∧ s'.stk t = X t ∧ s'.stk d = X d ∧
      (∀ k' : Stk, k' ∉ ({SX, SY, SA, SB, T, F1, F2, t, d, 0} : Finset Stk) → s'.stk k' = X k') := by
  have hdis' := hdis
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.mem_singleton, not_or] at hdis'
  obtain ⟨s₁, n₁, hev₁, hn₁, h0₁, hSX₁, hSY₁, hT₁, hSA₁, hSB₁, hF1₁, hF2₁, ht₁, hd₁, hrH₁, hrG₁, hfr₁⟩ :=
    mrgMergeStepPrefix (main := main) (pLt := pLt) (g := g) (X := X) hLt hdis hSX hSY hSA hSB h0
  have hsz : k.size = l.size := by omega
  have hrHne : s₁.reg Sk.rH ≠ Glyph.bit true := by rw [hrH₁, ite_eq_right h1]; decide
  have hrGne : s₁.reg Sk.rG ≠ Glyph.bit true := by rw [hrG₁, ite_eq_right h2]; decide
  obtain ⟨s₂, n₂, hev₂, hn₂, hSX₂, hSY₂, h0₂, hT₂, hSA₂, hSB₂, hF1₂, hF2₂, ht₂, hd₂, hrG₂, hfr₂⟩ :=
    mrgMergeCmp (main := main) (pLt := pLt) hLt hdis (g := s₁.reg) (X := s₁.stk)
      (k := k) (l := l) (v' := v') (w' := w') (ps := ps) (qs := qs) (A := A) (B' := B') (R := R)
      hSX₁ hSY₁ h0₁
  have hT₂' : s₂.stk T = Tc := by rw [hT₂, hT₁, hT]
  have h0₂' : s₂.stk 0 = R := h0₂
  have hrG₃ : s₂.reg Sk.rG = Glyph.bit true := by rw [hrG₂, ite_eq_left h3]
  obtain ⟨s', nc, hevc, hnc, hSXc, hSYc, hTc, h0c, hSAc, hSBc, hF1c, hF2c, htc, hdc, hfrc⟩ :=
    mrgMergeMoveQ2 (main := main) (pSize := pSize) hSz hdis hqs (g := s₂.reg) (X := s₂.stk)
      hSX₂ hSY₂ hT₂' h0₂'
  have hinner : Ev main (.ite Sk.rG (Glyph.bit true) (seqs [mvVal SY T t d, Sk.updSize pSize SY SB t d])
      (seqs [mvVal SX T t d, Sk.updSize pSize SX SA t d])) s₂ s' (nc + 1) :=
    Ev.iteT hrG₃ hevc
  have hA3 : Ev main (seqs ([Sk.dupInt SX 0 t d, Sk.dupInt SY 0 t d, pLt, mvVal 0 F2 t d,
      Sk.readFlag F2 Sk.rG, pushConst SX Glyph.cons, pushConst SY Glyph.cons]
      ++ [.ite Sk.rG (Glyph.bit true) (seqs [mvVal SY T t d, Sk.updSize pSize SY SB t d])
           (seqs [mvVal SX T t d, Sk.updSize pSize SX SA t d])])) s₁ s' (n₂ + (nc + 1)) :=
    Ev.seqs_append hev₂ hinner
  have htail : Ev main (mrgTail pLt pSize SX SY SA SB T F1 F2 t d) s₁ s' (n₂ + (nc + 1) + 2) :=
    Ev.iteF hrHne (Ev.iteF hrGne hA3)
  have hwhole : Ev main (Sk.mergeStep pLt pSize SX SY SA SB T F1 F2 t d) ⟨g, X⟩ s'
      (n₁ + (n₂ + (nc + 1) + 2)) := by
    rw [mergeStep_eq]
    exact Ev.seqs_append (by simpa only [mrgPreL] using hev₁) htail
  have hcost : n₁ + (n₂ + (nc + 1) + 2) ≤ mrgStepCore KLt KSz (Val.cons (Val.int (k : ℤ)) v') ps
      (Val.cons (Val.int (l : ℤ)) w') qs := by
    have h1' : n₁ ≤ 2 * KLt * ((k.size).size + (l.size).size + 4)
        + 80 * ((k.size).size + (l.size).size) + 622 := by
      have h := hn₁
      simp only [isz_ksv] at h
      nlinarith [h]
    have h2' : n₂ ≤ 40 * ((k.size) + 3) + 40 * ((l.size) + 3)
        + KLt * ((l.size) + (k.size) + 4) + 74 := by
      have h := hn₂
      rw [isz_natCast, isz_natCast] at h
      nlinarith [h]
    have h3' : nc ≤ 16 * (vsz (Val.cons (Val.int (l : ℤ)) w') + 1)
        + cExp KSz * (vsz (if qs = [] then Val.nil else qs.headD Val.nil) + 2) := by
      have h := hnc
      have hq := updSize_or_skip_le_cExp KSz qs hqs
      linarith [h, hq]
    have h3'' : nc ≤ 16 * (vsz (Val.cons (Val.int (l : ℤ)) w') + 1)
        + (60 + KSz) * (vsz (if qs = [] then Val.nil else qs.headD Val.nil) + 2) := by
      simpa only [cExp] using h3'
    have hVQ : vsz (Val.cons (Val.int (l : ℤ)) w') = (l.size) + 3 + vsz w' := vsz_record l w'
    have hVw : 1 ≤ vsz w' := one_le_vsz w'
    have hmain : n₁ + (n₂ + (nc + 1) + 2) + 20 ≤ mrgStep KLt KSz (Val.cons (Val.int (k : ℤ)) v') ps
        (Val.cons (Val.int (l : ℤ)) w') qs := by
      rw [mrgStep_eq_of_lt h3]
      simp only [cCmp, cMov, cExp, cK]
      nlinarith [h1', h2', h3'', hsz, hVQ, hVw]
    rw [mrgStepCore]
    omega
  have h0' : s'.stk 0 = R := h0c
  have hT' : s'.stk T = (if l < k then (Val.cons (Val.int (l : ℤ)) w').enc ++ Tc
      else (Val.cons (Val.int (k : ℤ)) v').enc ++ Tc) := by
    rw [ite_eq_left h3, hTc]
  have hSX' : s'.stk SX = (if l < k then (Val.cons (Val.int (k : ℤ)) v').enc ++ encs ps ++ gMark :: A
      else encs ps ++ gMark :: A) := by
    rw [ite_eq_left h3, hSXc, hSX₂]
  have hSY' : s'.stk SY = (if l < k then encs qs ++ gMark :: B'
      else (Val.cons (Val.int (l : ℤ)) w').enc ++ encs qs ++ gMark :: B') := by
    rw [ite_eq_left h3]
    exact hSYc
  have hSA' : s'.stk SA = (if l < k then X SA else if ps = [] then X SA
      else (Val.int ((keyOf (ps.headD Val.nil)).size : ℤ)).enc ++ (Val.int (k.size : ℤ)).enc ++ Sc) := by
    rw [ite_eq_left h3, hSAc, hSA₂, hSA₁]
  have hSB' : s'.stk SB = (if l < k then (if qs = [] then X SB
      else (Val.int ((keyOf (qs.headD Val.nil)).size : ℤ)).enc ++ (Val.int (l.size : ℤ)).enc ++ Sc')
      else X SB) := by
    rw [ite_eq_left h3, hSBc, hSB₂, hSB₁]
    by_cases hq : qs = []
    · rw [ite_eq_left hq, ite_eq_left hq]
    · rw [ite_eq_right hq, ite_eq_right hq, hSB, List.append_assoc]
  have hF1' : s'.stk F1 = X F1 := by rw [hF1c, hF1₂, hF1₁]
  have hF2' : s'.stk F2 = X F2 := by rw [hF2c, hF2₂, hF2₁]
  have ht' : s'.stk t = X t := by rw [htc, ht₂, ht₁]
  have hd' : s'.stk d = X d := by rw [hdc, hd₂, hd₁]
  have hfr' : ∀ k' : Stk, k' ∉ ({SX, SY, SA, SB, T, F1, F2, t, d, 0} : Finset Stk) →
      s'.stk k' = X k' := by
    intro k' hk
    have hk9 : k' ∉ ({SX, SY, SA, SB, F1, F2, t, d, 0} : Finset Stk) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk ⊢
      tauto
    rw [hfrc k' hk, hfr₂ k' hk, hfr₁ k' hk9]
  exact mrgMergeStep_mk s' (n₁ + (n₂ + (nc + 1) + 2)) hwhole hcost h0' hT' hSX' hSY' hSA' hSB' hF1' hF2' ht' hd' hfr'

private theorem mrgMergeStep_A3P {main pLt pSize : Cmd} {KLt KSz : ℕ}
    (hLt : ∀ main : Cmd, BinOp main pLt (fun _ _ => True) (fun a b => if a < b then 1 else 0)
      (fun a b => KLt * (isz a + isz b)))
    (hSz : ∀ main : Cmd, UnOp main pSize (fun _ => True) (fun a => (a.natAbs.size : ℤ))
      (fun a => KSz * isz a))
    {SX SY T SA SB F1 F2 t d : Stk}
    (hdis : ([SX, SY, T, SA, SB, F1, F2, t, d, 0] : List Stk).Nodup)
    {g : Reg → Glyph} {X : Stk → List Glyph} {k l : ℕ} {v' w' : Val} {ps qs : List Val}
    {A B' Tc R Sc Sc' : List Glyph}
    (hps : ∀ v ∈ ps, ∃ (k' : ℕ) (v'' : Val), v = Val.cons (Val.int (k' : ℤ)) v'')
    (hqs : ∀ v ∈ qs, ∃ (k' : ℕ) (v'' : Val), v = Val.cons (Val.int (k' : ℤ)) v'')
    (hSX : X SX = (Val.cons (Val.int (k : ℤ)) v').enc ++ encs ps ++ gMark :: A)
    (hSY : X SY = (Val.cons (Val.int (l : ℤ)) w').enc ++ encs qs ++ gMark :: B')
    (hSA : X SA = (Val.int (k.size : ℤ)).enc ++ Sc)
    (hSB : X SB = (Val.int (l.size : ℤ)).enc ++ Sc')
    (hT : X T = Tc) (h0 : X 0 = R)  (h1 : ¬ l.size < k.size) (h2 : ¬ k.size < l.size) (h3 : ¬ l < k) :
    ∃ s' n, Ev main (Sk.mergeStep pLt pSize SX SY SA SB T F1 F2 t d) ⟨g, X⟩ s' n ∧
      n ≤ mrgStepCore KLt KSz (Val.cons (Val.int (k : ℤ)) v') ps (Val.cons (Val.int (l : ℤ)) w') qs ∧
      s'.stk 0 = R ∧
      s'.stk T = (if l < k then (Val.cons (Val.int (l : ℤ)) w').enc ++ Tc else (Val.cons (Val.int (k : ℤ)) v').enc ++ Tc) ∧
      s'.stk SX = (if l < k then (Val.cons (Val.int (k : ℤ)) v').enc ++ encs ps ++ gMark :: A else encs ps ++ gMark :: A) ∧
      s'.stk SY = (if l < k then encs qs ++ gMark :: B' else (Val.cons (Val.int (l : ℤ)) w').enc ++ encs qs ++ gMark :: B') ∧
      s'.stk SA = (if l < k then X SA else if ps = [] then X SA else (Val.int ((keyOf (ps.headD Val.nil)).size : ℤ)).enc ++ (Val.int (k.size : ℤ)).enc ++ Sc) ∧
      s'.stk SB = (if l < k then (if qs = [] then X SB else (Val.int ((keyOf (qs.headD Val.nil)).size : ℤ)).enc ++ (Val.int (l.size : ℤ)).enc ++ Sc') else X SB) ∧
      s'.stk F1 = X F1 ∧ s'.stk F2 = X F2 ∧ s'.stk t = X t ∧ s'.stk d = X d ∧
      (∀ k' : Stk, k' ∉ ({SX, SY, SA, SB, T, F1, F2, t, d, 0} : Finset Stk) → s'.stk k' = X k') := by
  have hdis' := hdis
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.mem_singleton, not_or] at hdis'
  obtain ⟨s₁, n₁, hev₁, hn₁, h0₁, hSX₁, hSY₁, hT₁, hSA₁, hSB₁, hF1₁, hF2₁, ht₁, hd₁, hrH₁, hrG₁, hfr₁⟩ :=
    mrgMergeStepPrefix (main := main) (pLt := pLt) (g := g) (X := X) hLt hdis hSX hSY hSA hSB h0
  have hsz : k.size = l.size := by omega
  have hrHne : s₁.reg Sk.rH ≠ Glyph.bit true := by rw [hrH₁, ite_eq_right h1]; decide
  have hrGne : s₁.reg Sk.rG ≠ Glyph.bit true := by rw [hrG₁, ite_eq_right h2]; decide
  obtain ⟨s₂, n₂, hev₂, hn₂, hSX₂, hSY₂, h0₂, hT₂, hSA₂, hSB₂, hF1₂, hF2₂, ht₂, hd₂, hrG₂, hfr₂⟩ :=
    mrgMergeCmp (main := main) (pLt := pLt) hLt hdis (g := s₁.reg) (X := s₁.stk)
      (k := k) (l := l) (v' := v') (w' := w') (ps := ps) (qs := qs) (A := A) (B' := B') (R := R)
      hSX₁ hSY₁ h0₁
  have hT₂' : s₂.stk T = Tc := by rw [hT₂, hT₁, hT]
  have h0₂' : s₂.stk 0 = R := h0₂
  have hge : ¬ l < k := h3
  have hrG₃ : s₂.reg Sk.rG ≠ Glyph.bit true := by rw [hrG₂, ite_eq_right h3]; decide
  obtain ⟨s', nc, hevc, hnc, hSXc, hSYc, hTc, h0c, hSAc, hSBc, hF1c, hF2c, htc, hdc, hfrc⟩ :=
    mrgMergeMoveP3 (main := main) (pSize := pSize) hSz hdis hps (g := s₂.reg) (X := s₂.stk)
      hSX₂ hT₂' h0₂'
  have hinner : Ev main (.ite Sk.rG (Glyph.bit true) (seqs [mvVal SY T t d, Sk.updSize pSize SY SB t d])
      (seqs [mvVal SX T t d, Sk.updSize pSize SX SA t d])) s₂ s' (nc + 1) :=
    Ev.iteF hrG₃ hevc
  have hA3 : Ev main (seqs ([Sk.dupInt SX 0 t d, Sk.dupInt SY 0 t d, pLt, mvVal 0 F2 t d,
      Sk.readFlag F2 Sk.rG, pushConst SX Glyph.cons, pushConst SY Glyph.cons]
      ++ [.ite Sk.rG (Glyph.bit true) (seqs [mvVal SY T t d, Sk.updSize pSize SY SB t d])
           (seqs [mvVal SX T t d, Sk.updSize pSize SX SA t d])])) s₁ s' (n₂ + (nc + 1)) :=
    Ev.seqs_append hev₂ hinner
  have htail : Ev main (mrgTail pLt pSize SX SY SA SB T F1 F2 t d) s₁ s' (n₂ + (nc + 1) + 2) :=
    Ev.iteF hrHne (Ev.iteF hrGne hA3)
  have hwhole : Ev main (Sk.mergeStep pLt pSize SX SY SA SB T F1 F2 t d) ⟨g, X⟩ s'
      (n₁ + (n₂ + (nc + 1) + 2)) := by
    rw [mergeStep_eq]
    exact Ev.seqs_append (by simpa only [mrgPreL] using hev₁) htail
  have hcost : n₁ + (n₂ + (nc + 1) + 2) ≤ mrgStepCore KLt KSz (Val.cons (Val.int (k : ℤ)) v') ps
      (Val.cons (Val.int (l : ℤ)) w') qs := by
    have h1' : n₁ ≤ 2 * KLt * ((k.size).size + (l.size).size + 4)
        + 80 * ((k.size).size + (l.size).size) + 622 := by
      have h := hn₁
      simp only [isz_ksv] at h
      nlinarith [h]
    have h2' : n₂ ≤ 40 * ((k.size) + 3) + 40 * ((l.size) + 3)
        + KLt * ((l.size) + (k.size) + 4) + 74 := by
      have h := hn₂
      rw [isz_natCast, isz_natCast] at h
      nlinarith [h]
    have h3' : nc ≤ 16 * (vsz (Val.cons (Val.int (k : ℤ)) v') + 1)
        + cExp KSz * (vsz (if ps = [] then Val.nil else ps.headD Val.nil) + 2) := by
      have h := hnc
      have hq := updSize_or_skip_le_cExp KSz ps hps
      linarith [h, hq]
    have h3'' : nc ≤ 16 * (vsz (Val.cons (Val.int (k : ℤ)) v') + 1)
        + (60 + KSz) * (vsz (if ps = [] then Val.nil else ps.headD Val.nil) + 2) := by
      simpa only [cExp] using h3'
    have hVP : vsz (Val.cons (Val.int (k : ℤ)) v') = (k.size) + 3 + vsz v' := vsz_record k v'
    have hVv : 1 ≤ vsz v' := one_le_vsz v'
    have hmain : n₁ + (n₂ + (nc + 1) + 2) + 20 ≤ mrgStep KLt KSz (Val.cons (Val.int (k : ℤ)) v') ps
        (Val.cons (Val.int (l : ℤ)) w') qs := by
      rw [mrgStep_eq_of_ge hge]
      simp only [cCmp, cMov, cExp, cK]
      nlinarith [h1', h2', h3'', hsz, hVP, hVv]
    rw [mrgStepCore]
    omega
  have h0' : s'.stk 0 = R := h0c
  have hT' : s'.stk T = (if l < k then (Val.cons (Val.int (l : ℤ)) w').enc ++ Tc
      else (Val.cons (Val.int (k : ℤ)) v').enc ++ Tc) := by
    rw [ite_eq_right hge, hTc]
  have hSX' : s'.stk SX = (if l < k then (Val.cons (Val.int (k : ℤ)) v').enc ++ encs ps ++ gMark :: A
      else encs ps ++ gMark :: A) := by
    rw [ite_eq_right hge]
    exact hSXc
  have hSY' : s'.stk SY = (if l < k then encs qs ++ gMark :: B'
      else (Val.cons (Val.int (l : ℤ)) w').enc ++ encs qs ++ gMark :: B') := by
    rw [ite_eq_right hge, hSYc, hSY₂]
  have hSA' : s'.stk SA = (if l < k then X SA else if ps = [] then X SA
      else (Val.int ((keyOf (ps.headD Val.nil)).size : ℤ)).enc ++ (Val.int (k.size : ℤ)).enc ++ Sc) := by
    rw [ite_eq_right hge, hSAc, hSA₂, hSA₁]
    by_cases hp : ps = []
    · rw [ite_eq_left hp, ite_eq_left hp]
    · rw [ite_eq_right hp, ite_eq_right hp, hSA, List.append_assoc]
  have hSB' : s'.stk SB = (if l < k then (if qs = [] then X SB
      else (Val.int ((keyOf (qs.headD Val.nil)).size : ℤ)).enc ++ (Val.int (l.size : ℤ)).enc ++ Sc')
      else X SB) := by
    rw [ite_eq_right hge, hSBc, hSB₂, hSB₁]
  have hF1' : s'.stk F1 = X F1 := by rw [hF1c, hF1₂, hF1₁]
  have hF2' : s'.stk F2 = X F2 := by rw [hF2c, hF2₂, hF2₁]
  have ht' : s'.stk t = X t := by rw [htc, ht₂, ht₁]
  have hd' : s'.stk d = X d := by rw [hdc, hd₂, hd₁]
  have hfr' : ∀ k' : Stk, k' ∉ ({SX, SY, SA, SB, T, F1, F2, t, d, 0} : Finset Stk) →
      s'.stk k' = X k' := by
    intro k' hk
    have hk9 : k' ∉ ({SX, SY, SA, SB, F1, F2, t, d, 0} : Finset Stk) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk ⊢
      tauto
    rw [hfrc k' hk, hfr₂ k' hk, hfr₁ k' hk9]
  exact mrgMergeStep_mk s' (n₁ + (n₂ + (nc + 1) + 2)) hwhole hcost h0' hT' hSX' hSY' hSA' hSB' hF1' hF2' ht' hd' hfr'

theorem mrgMergeStep {main pLt pSize : Cmd} {KLt KSz : ℕ}
    (hLt : ∀ main : Cmd, BinOp main pLt (fun _ _ => True) (fun a b => if a < b then 1 else 0)
      (fun a b => KLt * (isz a + isz b)))
    (hSz : ∀ main : Cmd, UnOp main pSize (fun _ => True) (fun a => (a.natAbs.size : ℤ))
      (fun a => KSz * isz a))
    {SX SY T SA SB F1 F2 t d : Stk}
    (hdis : ([SX, SY, T, SA, SB, F1, F2, t, d, 0] : List Stk).Nodup)
    {g : Reg → Glyph} {X : Stk → List Glyph} {k l : ℕ} {v' w' : Val} {ps qs : List Val}
    {A B' Tc R Sc Sc' : List Glyph}
    (hps : ∀ v ∈ ps, ∃ (k' : ℕ) (v'' : Val), v = Val.cons (Val.int (k' : ℤ)) v'')
    (hqs : ∀ v ∈ qs, ∃ (k' : ℕ) (v'' : Val), v = Val.cons (Val.int (k' : ℤ)) v'')
    (hSX : X SX = (Val.cons (Val.int (k : ℤ)) v').enc ++ encs ps ++ gMark :: A)
    (hSY : X SY = (Val.cons (Val.int (l : ℤ)) w').enc ++ encs qs ++ gMark :: B')
    (hSA : X SA = (Val.int (k.size : ℤ)).enc ++ Sc)
    (hSB : X SB = (Val.int (l.size : ℤ)).enc ++ Sc')
    (hT : X T = Tc) (h0 : X 0 = R) :
    ∃ s' n, Ev main (Sk.mergeStep pLt pSize SX SY SA SB T F1 F2 t d) ⟨g, X⟩ s' n ∧
      n ≤ mrgStepCore KLt KSz (Val.cons (Val.int (k : ℤ)) v') ps (Val.cons (Val.int (l : ℤ)) w') qs ∧
      s'.stk 0 = R ∧
      s'.stk T = (if l < k then (Val.cons (Val.int (l : ℤ)) w').enc ++ Tc else (Val.cons (Val.int (k : ℤ)) v').enc ++ Tc) ∧
      s'.stk SX = (if l < k then (Val.cons (Val.int (k : ℤ)) v').enc ++ encs ps ++ gMark :: A else encs ps ++ gMark :: A) ∧
      s'.stk SY = (if l < k then encs qs ++ gMark :: B' else (Val.cons (Val.int (l : ℤ)) w').enc ++ encs qs ++ gMark :: B') ∧
      s'.stk SA = (if l < k then X SA else if ps = [] then X SA else (Val.int ((keyOf (ps.headD Val.nil)).size : ℤ)).enc ++ (Val.int (k.size : ℤ)).enc ++ Sc) ∧
      s'.stk SB = (if l < k then (if qs = [] then X SB else (Val.int ((keyOf (qs.headD Val.nil)).size : ℤ)).enc ++ (Val.int (l.size : ℤ)).enc ++ Sc') else X SB) ∧
      s'.stk F1 = X F1 ∧ s'.stk F2 = X F2 ∧ s'.stk t = X t ∧ s'.stk d = X d ∧
      (∀ k' : Stk, k' ∉ ({SX, SY, SA, SB, T, F1, F2, t, d, 0} : Finset Stk) → s'.stk k' = X k') := by
  by_cases h1 : l.size < k.size
  · exact mrgMergeStep_A1 hLt hSz hdis hps hqs hSX hSY hSA hSB hT h0 h1
  · by_cases h2 : k.size < l.size
    · exact mrgMergeStep_A2 hLt hSz hdis hps hqs hSX hSY hSA hSB hT h0 h1 h2
    · by_cases h3 : l < k
      · exact mrgMergeStep_A3Q hLt hSz hdis hps hqs hSX hSY hSA hSB hT h0 h1 h2 h3
      · exact mrgMergeStep_A3P hLt hSz hdis hps hqs hSX hSY hSA hSB hT h0 h1 h2 h3

end Work.Layout
