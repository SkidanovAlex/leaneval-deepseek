import Mathlib
import Submission.Work.Layout.chunksOfDefs
import Submission.Work.Layout.chunksProof
import Submission.Work.Layout.buildDefs
import Submission.Work.Layout.chunksArith
import Submission.Work.Layout.groupStop_ev
import Submission.Work.Layout.innerFrame_ev
import Submission.Work.Layout.mem_getD_length

namespace Work.Layout

open HvdH

theorem gEos_ne_gCont : Glyph.eos ≠ Work.Layout.gCont := by decide

/-! ## Elementary list arithmetic -/

/-- the per-chunk cost bound of one iteration of the outer loop -/
def gCost (m : ℕ) (c : List Val) : ℕ := 40 * ((c.map vsz).sum) + 80 * m + 129

/-- arithmetic padding: the cost bound of `buildProg` is dominated by the target bound. -/
theorem buildCost_le' (ch : List (List Val)) (m : ℕ) (hlen : ∀ c ∈ ch, c.length = m) :
    (ch.map (gCost m)).sum + 8 ≤
      100 * (vsz (ofList (ch.map ofList)) + ch.length + 1) := by
  induction ch with
  | nil => simp [gCost, ofList, vsz, Val.enc]
  | cons c ch ih =>
      have hc : c.length = m := hlen c (List.mem_cons_self ..)
      have hlen' : ∀ c' ∈ ch, c'.length = m := fun c' hc' => hlen c' (List.mem_cons_of_mem c hc')
      have ih' := ih hlen'
      have hv : vsz (ofList c) = (c.map vsz).sum + m + 1 := by
        rw [vsz_ofList_eq, sum_map_vsz_succ, hc]
      have hgc : gCost m c = 40 * (c.map vsz).sum + 80 * m + 129 := rfl
      have hmap2 : List.map ofList (c :: ch) = ofList c :: List.map ofList ch := rfl
      rw [List.map_cons, List.sum_cons, hmap2, vsz_ofList_cons, hv, List.length_cons, hgc]
      omega

/-! ## One non-final iteration of the outer loop -/

theorem hAcc_cons (v : Val) (B : List Val) (R : List Glyph) :
    Glyph.cons :: (v.enc ++ ((ofList B).enc ++ R)) = (ofList (v :: B)).enc ++ R := by
  rw [enc_ofList_cons, List.cons_append, List.append_assoc]

theorem groupBody_cont {main : Cmd} {g : Reg → Glyph} {X : Stk → List Glyph}
    {c : List Val} {A : List (List Val)} {m : ℕ} {B : List Val}
    {A0 T0 M0 W0 T20 B0 C0 : List Glyph}
    (hm : 1 ≤ m) (hc : c.length = m)
    (hT : X sT = EncSeq (c :: A) ++ gSent :: T0)
    (hM : X sM = List.replicate m gPend ++ gSent :: M0)
    (hW : X sW = W0) (hT2 : X sT2 = T20) (hB : X sB = B0) (hC : X sC = C0)
    (h0 : X 0 = (ofList B).enc ++ A0) :
    ∃ s', Ev main groupBody ⟨g, X⟩ s' (40 * ((c.map vsz).sum) + 80 * m + 128) ∧
      s'.stk 0 = (ofList (ofList c :: B)).enc ++ A0 ∧
      s'.stk sT = EncSeq A ++ gSent :: T0 ∧
      s'.stk sM = List.replicate m gPend ++ gSent :: M0 ∧
      s'.stk sW = W0 ∧ s'.stk sT2 = T20 ∧ s'.stk sB = B0 ∧ s'.stk sC = C0 ∧
      s'.reg rLoopG = gCont ∧
      (∀ j : Stk, j ≠ 0 → j ≠ sT → j ≠ sM → j ≠ sW → j ≠ sT2 → j ≠ sB → j ≠ sC →
        s'.stk j = X j) := by
  have hcne : c ≠ [] := by intro h; rw [h] at hc; simp at hc; omega
  have hheadX : (X sT).headD Glyph.eos ≠ gSent := by
    rw [hT]; exact EncSeq_headD_ne_gSent hcne A (gSent :: T0)
  have hpeek : Ev main (.peek sT rE) ⟨g, X⟩
      ⟨Function.update g rE ((X sT).headD Glyph.eos), X⟩ 1 := ev_peek' main sT rE g X
  obtain ⟨s₂, hev₂, hs₂0, hs₂f, -, -⟩ :=
    step_pushK (main := main) (k := 0) (c := Glyph.nil)
      (g := Function.update g rE ((X sT).headD Glyph.eos)) (X := X)
  have hM₂ : s₂.stk sM = List.replicate m gPend ++ gSent :: M0 := by
    rw [hs₂f sM (by decide)]; exact hM
  have hT2₂ : s₂.stk sT2 = T20 := by rw [hs₂f sT2 (by decide)]; exact hT2
  have hW₂ : s₂.stk sW = W0 := by rw [hs₂f sW (by decide)]; exact hW
  obtain ⟨s₃, n₃, hev₃, hle₃, hs₃M, hs₃W, hs₃T2, hs₃f⟩ :=
    copy_ev (main := main) (g := s₂.reg) (X := s₂.stk) (G := List.replicate m gPend)
      (M0 := M0) (W0 := W0) (T20 := T20)
      (gMark_notMem_replicate m) (gSent_notMem_replicate m) hM₂ hT2₂ hW₂
  have hs₃T : s₃.stk sT = (c.reverse.map Val.enc).flatten ++ (EncSeq A ++ gSent :: T0) := by
    rw [hs₃f sT (by decide) (by decide) (by decide), hs₂f sT (by decide), hT, EncSeq_cons,
      List.append_assoc]
  have hs₃0 : s₃.stk 0 = Glyph.nil :: ((ofList B).enc ++ A0) := by
    rw [hs₃f 0 (by decide) (by decide) (by decide), hs₂0, h0]
  obtain ⟨s₄, n₄, hev₄, hle₄, hs₄0, hs₄T, hs₄W, hs₄B, hs₄C, hs₄f⟩ :=
    innerFrame_ev (main := main) (g := s₃.reg) (X := s₃.stk) (ys := c.reverse) (k := m)
      (A0 := Glyph.nil :: ((ofList B).enc ++ A0)) (T0 := EncSeq A ++ gSent :: T0) (W0 := W0)
      (by rw [List.length_reverse]; exact hc) hs₃W hs₃T hs₃0
  have hs₄0' : s₄.stk 0 = (ofList c).enc ++ ((ofList B).enc ++ A0) := by
    have h1 : twist c.reverse ++ (Glyph.nil :: ((ofList B).enc ++ A0))
        = (twist c.reverse ++ [Glyph.nil]) ++ ((ofList B).enc ++ A0) := by
      rw [List.append_assoc, List.singleton_append]
    rw [hs₄0, h1, twist_reverse_enc]
  obtain ⟨s₅, hev₅, hs₅W, _, hs₅f, -⟩ :=
    step_pop (main := main) (k := sW) (r := rE) (g := s₄.reg) (X := s₄.stk) hs₄W
  obtain ⟨s₆, hev₆, hs₆0, hs₆f, -, -⟩ :=
    step_pushK (main := main) (k := 0) (c := Glyph.cons) (g := s₅.reg) (X := s₅.stk)
  obtain ⟨s₇, hev₇, hs₇r, -, hs₇f⟩ :=
    step_set (main := main) (r := rLoopG) (c := gCont) (g := s₆.reg) (X := s₆.stk)
  have hcost : n₃ + n₄ + 8 ≤ 40 * ((c.map vsz).sum) + 80 * m + 128 := by
    have h3 : n₃ ≤ 40 * (m + 1) + 40 := by
      have h := hle₃; rw [List.length_replicate] at h; exact h
    have h4 : n₄ ≤ 40 * (((c.reverse).map vsz).sum + m + 1) := hle₄
    rw [List.map_reverse, List.sum_reverse] at h4
    omega
  have h01 : Ev main (seqs [.set rLoopG gCont]) s₆ s₇ 1 := hev₇
  have h12 : Ev main (seqs [pushK 0 Glyph.cons, .set rLoopG gCont]) s₅ s₇ 3 :=
    Ev.seq' hev₆ h01 (by omega)
  have h23 : Ev main (seqs [.pop sW rE, pushK 0 Glyph.cons, .set rLoopG gCont]) s₄ s₇ 4 :=
    Ev.seq' hev₅ h12 (by omega)
  have h34 : Ev main (seqs [innerProg, .pop sW rE, pushK 0 Glyph.cons, .set rLoopG gCont])
      ⟨s₃.reg, s₃.stk⟩ s₇ (n₄ + 4) := Ev.seq' hev₄ h23 (by omega)
  have h45 : Ev main (seqs [copyProg, innerProg, .pop sW rE, pushK 0 Glyph.cons,
      .set rLoopG gCont]) ⟨s₂.reg, s₂.stk⟩ s₇ (n₃ + n₄ + 4) := Ev.seq' hev₃ h34 (by omega)
  have hA : Ev main (seqs [pushK 0 Glyph.nil, copyProg, innerProg, .pop sW rE,
      pushK 0 Glyph.cons, .set rLoopG gCont])
      ⟨Function.update g rE ((X sT).headD Glyph.eos), X⟩ s₇ (n₃ + n₄ + 6) :=
    Ev.seq' hev₂ h45 (by omega)
  have hite : Ev main (.ite rE gSent (.set rLoopG Glyph.eos)
      (seqs [pushK 0 Glyph.nil, copyProg, innerProg, .pop sW rE, pushK 0 Glyph.cons,
        .set rLoopG gCont]))
      ⟨Function.update g rE ((X sT).headD Glyph.eos), X⟩ s₇ (n₃ + n₄ + 7) :=
    (Ev.iteF (by simpa using hheadX) hA).mono (by omega)
  have hmain : Ev main groupBody ⟨g, X⟩ s₇ (n₃ + n₄ + 8) := by
    have hseq : Ev main (seqs [.peek sT rE, .ite rE gSent (.set rLoopG Glyph.eos)
        (seqs [pushK 0 Glyph.nil, copyProg, innerProg, .pop sW rE, pushK 0 Glyph.cons,
          .set rLoopG gCont])]) ⟨g, X⟩ s₇ (1 + (n₃ + n₄ + 7)) :=
      Ev.seq' hpeek hite (by omega)
    exact hseq.mono (by omega)
  refine ⟨s₇, hmain.mono (by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_, hs₇r, ?_⟩
  · rw [hs₇f 0, hs₆0, hs₅f 0 (by decide), hs₄0', hAcc_cons (ofList c) B A0]
  · rw [hs₇f sT, hs₆f sT (by decide), hs₅f sT (by decide), hs₄T]
  · rw [hs₇f sM, hs₆f sM (by decide), hs₅f sM (by decide),
      hs₄f sM (by decide) (by decide) (by decide) (by decide) (by decide), hs₃M]
  · rw [hs₇f sW, hs₆f sW (by decide), hs₅W]
  · rw [hs₇f sT2, hs₆f sT2 (by decide), hs₅f sT2 (by decide),
      hs₄f sT2 (by decide) (by decide) (by decide) (by decide) (by decide), hs₃T2]
  · rw [hs₇f sB, hs₆f sB (by decide), hs₅f sB (by decide), hs₄B,
      hs₃f sB (by decide) (by decide) (by decide), hs₂f sB (by decide)]
    exact hB
  · rw [hs₇f sC, hs₆f sC (by decide), hs₅f sC (by decide), hs₄C,
      hs₃f sC (by decide) (by decide) (by decide), hs₂f sC (by decide)]
    exact hC
  · intro j hj0 hjT hjM hjW hjT2 hjB hjC
    rw [hs₇f j, hs₆f j hj0, hs₅f j hjW,
      hs₄f j hj0 hjT hjW hjB hjC, hs₃f j hjM hjW hjT2, hs₂f j hj0]

/-! ## The whole outer loop -/

theorem buildLoop {main : Cmd} {m : ℕ} (hm : 1 ≤ m) :
    ∀ (A : List (List Val)) (g : Reg → Glyph) (X : Stk → List Glyph) (B : List Val)
      (A0 T0 M0 W0 T20 B0 C0 : List Glyph),
      (∀ c ∈ A, c.length = m) →
      X sT = EncSeq A ++ gSent :: T0 →
      X sM = List.replicate m gPend ++ gSent :: M0 →
      X sW = W0 → X sT2 = T20 → X sB = B0 → X sC = C0 →
      X 0 = (ofList B).enc ++ A0 →
      g rLoopG = gCont →
      ∃ s' Cst, loopRuns main rLoopG gCont groupBody (A.length + 1) ⟨g, X⟩ s' Cst ∧
        Cst ≤ (A.map (gCost m)).sum + 4 ∧
        s'.stk 0 = (ofList (A.reverse.map ofList ++ B)).enc ++ A0 ∧
        s'.stk sT = gSent :: T0 ∧
        s'.stk sM = List.replicate m gPend ++ gSent :: M0 ∧
        s'.stk sW = W0 ∧ s'.stk sT2 = T20 ∧ s'.stk sB = B0 ∧ s'.stk sC = C0 ∧
        s'.reg rLoopG = Glyph.eos ∧
        (∀ j : Stk, j ≠ 0 → j ≠ sT → j ≠ sM → j ≠ sW → j ≠ sT2 → j ≠ sB → j ≠ sC →
          s'.stk j = X j) := by
  intro A
  induction A with
  | nil =>
      intro g X B A0 T0 M0 W0 T20 B0 C0 hlen hT hM hW hT2 hB hC h0 hreg
      obtain ⟨s', hev, hreg', hfr⟩ := groupStop_ev (main := main) (g := g) (X := X) (T0 := T0) hT
      refine ⟨s', ((([] : List (List Val)).map (gCost m)).sum + 4),
        loopRuns.mono (by simp) (loopRuns.one hreg hev) (by simp), le_rfl, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, hreg', ?_⟩
      · rw [hfr 0, h0]; simp
      · rw [hfr sT]; simpa using hT
      · rw [hfr sM, hM]
      · rw [hfr sW, hW]
      · rw [hfr sT2, hT2]
      · rw [hfr sB, hB]
      · rw [hfr sC, hC]
      · intro j h1 h2 h3 h4 h5 h6 h7
        exact hfr j
  | cons c A' ih =>
      intro g X B A0 T0 M0 W0 T20 B0 C0 hlen hT hM hW hT2 hB hC h0 hreg
      have hc : c.length = m := hlen c (List.mem_cons_self ..)
      have hlen' : ∀ c' ∈ A', c'.length = m :=
        fun c' hc' => hlen c' (List.mem_cons_of_mem c hc')
      obtain ⟨s₁, hev₁, hs₁0, hs₁T, hs₁M, hs₁W, hs₁T2, hs₁B, hs₁C, hs₁r, hs₁f⟩ :=
        groupBody_cont (main := main) (g := g) (X := X) (c := c) (A := A') (m := m) (B := B)
          (A0 := A0) (T0 := T0) (M0 := M0) (W0 := W0) (T20 := T20) (B0 := B0) (C0 := C0)
          hm hc hT hM hW hT2 hB hC h0
      obtain ⟨s₂, Cst, hrun, hcost, hs₂0, hs₂T, hs₂M, hs₂W, hs₂T2, hs₂B, hs₂C, hs₂r, hs₂f⟩ :=
        ih s₁.reg s₁.stk (ofList c :: B) A0 T0 M0 W0 T20 B0 C0 hlen'
          (by rw [hs₁T]) (by rw [hs₁M]) (by rw [hs₁W]) (by rw [hs₁T2])
          (by rw [hs₁B]) (by rw [hs₁C]) (by rw [hs₁0]) (by rw [hs₁r])
      have hgc : gCost m c = 40 * (c.map vsz).sum + 80 * m + 129 := rfl
      have hmap : ((c :: A').map (gCost m)).sum = gCost m c + (A'.map (gCost m)).sum := by
        rw [List.map_cons, List.sum_cons]
      refine ⟨s₂, ((c :: A').map (gCost m)).sum + 4,
        loopRuns.succ' hreg hev₁ hrun (by rw [hmap, hgc]; omega),
        le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hs₂r, ?_⟩
      · rw [hs₂0, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
          List.append_assoc, List.cons_append, List.nil_append]
      · exact hs₂T
      · exact hs₂M
      · exact hs₂W
      · exact hs₂T2
      · exact hs₂B
      · exact hs₂C
      · intro j hj0 hjT hjM hjW hjT2 hjB hjC
        rw [hs₂f j hj0 hjT hjM hjW hjT2 hjB hjC,
          hs₁f j hj0 hjT hjM hjW hjT2 hjB hjC]

/-- Requires the imports of `Submission.Work.Layout.chunksOfDefs` and
`Submission.Work.Layout.chunksProof` (the latter contains `copy_ev` and `inner_ev`).

STRENGTHENING of `Work.Layout.build_ev` (`Submission/Work/Layout/build_ev.lean`): `buildProg` also
restores the two `mvVal` scratch stacks `sB` and `sC` (used inside `Work.Layout.innerProg`), and the
scratch stack `sT2`.  This is needed because the frame clause of `build_ev` deliberately excludes
them. -/
theorem buildFrame {main : HvdH.Cmd} {g : HvdH.Reg → HvdH.Glyph}
    {X : HvdH.Stk → List HvdH.Glyph} {ch : List (List HvdH.Val)} {m : ℕ}
    {A0 T0 M0 W0 : List HvdH.Glyph} (hm : 1 ≤ m)
    (hlen : ∀ i, i < ch.length → (ch.getD i []).length = m)
    (hT : X Work.Layout.sT = ((Work.Layout.elemOrder ch).map HvdH.Val.enc).flatten ++
      Work.Layout.gSent :: T0)
    (hM : X Work.Layout.sM = List.replicate m Work.Layout.gPend ++ Work.Layout.gSent :: M0)
    (hW : X Work.Layout.sW = W0) (h0 : X 0 = A0) :
    ∃ s' n, Work.Layout.Ev main Work.Layout.buildProg ⟨g, X⟩ s' n ∧
      n ≤ 100 * (HvdH.vsz (HvdH.ofList (ch.map HvdH.ofList)) + ch.length + 1) ∧
      s'.stk 0 = (HvdH.ofList (ch.map HvdH.ofList)).enc ++ A0 ∧
      s'.stk Work.Layout.sT = Work.Layout.gSent :: T0 ∧
      s'.stk Work.Layout.sM = List.replicate m Work.Layout.gPend ++ Work.Layout.gSent :: M0 ∧
      s'.stk Work.Layout.sW = W0 ∧
      s'.stk Work.Layout.sB = X Work.Layout.sB ∧
      s'.stk Work.Layout.sC = X Work.Layout.sC ∧
      s'.stk Work.Layout.sT2 = X Work.Layout.sT2 ∧
      (∀ j : HvdH.Stk, j ≠ 0 → j ≠ Work.Layout.sT → j ≠ Work.Layout.sM →
        j ≠ Work.Layout.sW → j ≠ Work.Layout.sB → j ≠ Work.Layout.sC → s'.stk j = X j) := by
  have hlenMem : ∀ c ∈ ch, c.length = m := mem_getD_length hlen
  have hlenRev : ∀ c ∈ ch.reverse, c.length = m :=
    fun c hc => hlenMem c (List.mem_reverse.mp hc)
  obtain ⟨s₁, hev₁, hs₁0, hs₁f, -, -⟩ :=
    step_pushK (main := main) (k := 0) (c := Glyph.nil) (g := g) (X := X)
  obtain ⟨s₂, hev₂, hs₂r, -, hs₂f⟩ :=
    step_set (main := main) (r := rLoopG) (c := gCont) (g := s₁.reg) (X := s₁.stk)
  have hT₂ : s₂.stk sT = EncSeq ch.reverse ++ gSent :: T0 := by
    rw [hs₂f sT, hs₁f sT (by decide), hT]
    rfl
  have hM₂ : s₂.stk sM = List.replicate m gPend ++ gSent :: M0 := by
    rw [hs₂f sM, hs₁f sM (by decide), hM]
  have hW₂ : s₂.stk sW = W0 := by rw [hs₂f sW, hs₁f sW (by decide), hW]
  have hT2₂ : s₂.stk sT2 = X sT2 := by rw [hs₂f sT2, hs₁f sT2 (by decide)]
  have hB₂ : s₂.stk sB = X sB := by rw [hs₂f sB, hs₁f sB (by decide)]
  have hC₂ : s₂.stk sC = X sC := by rw [hs₂f sC, hs₁f sC (by decide)]
  have h0₂ : s₂.stk 0 = (ofList ([] : List Val)).enc ++ A0 := by
    rw [hs₂f 0, hs₁0, h0]; simp [ofList, Val.enc]
  obtain ⟨s', Cst, hrun, hcost, hs'0, hs'T, hs'M, hs'W, hs'T2, hs'B, hs'C, hs'r, hs'f⟩ :=
    buildLoop (main := main) (m := m) hm (ch.reverse) s₂.reg s₂.stk ([] : List Val)
      A0 T0 M0 W0 (X sT2) (X sB) (X sC) hlenRev hT₂ hM₂ hW₂ hT2₂ hB₂ hC₂ h0₂ hs₂r
  have hloop : Ev main (.loop rLoopG gCont groupBody) s₂ s' (Cst + 1) :=
    loopRuns.eval hrun (by rw [hs'r]; exact gEos_ne_gCont)
  have hprog : Ev main buildProg ⟨g, X⟩ s' (2 + 1 + (Cst + 1)) := by
    have h23 : Ev main (seqs [.set rLoopG gCont, .loop rLoopG gCont groupBody]) s₁ s'
        (1 + (Cst + 1)) := Ev.seq' hev₂ hloop (by omega)
    have h123 : Ev main (seqs [pushK 0 Glyph.nil, .set rLoopG gCont,
        .loop rLoopG gCont groupBody]) ⟨g, X⟩ s' (2 + (1 + (Cst + 1))) :=
      Ev.seq' hev₁ h23 (by omega)
    exact h123.mono (by omega)
  have hfin : (2 + 1 + (Cst + 1))
      ≤ 100 * (vsz (ofList (ch.map ofList)) + ch.length + 1) := by
    have h1 : Cst ≤ (ch.reverse.map (gCost m)).sum + 4 := hcost
    rw [List.map_reverse, List.sum_reverse] at h1
    have h2 := buildCost_le' ch m hlenMem
    omega
  refine ⟨s', _, hprog.mono hfin, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs'0, List.reverse_reverse, List.append_nil]
  · rw [hs'T]
  · rw [hs'M]
  · rw [hs'W]
  · rw [hs'B]
  · rw [hs'C]
  · rw [hs'T2]
  · intro j hj0 hjT hjM hjW hjB hjC
    by_cases hjT2 : j = sT2
    · subst hjT2; rw [hs'T2]
    · rw [hs'f j hj0 hjT hjM hjW hjT2 hjB hjC, hs₂f j, hs₁f j hj0]

end Work.Layout
