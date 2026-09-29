-- PRIVATE COPY (own namespace, Resample/PB dialect) of `Submission/Work/Resample/buildFrameT.lean`.
-- The declarations have been moved from `Work.Layout`/`Work.Resample` into the
-- dedicated namespace `Work.Resample.PBChunk` (with `buildFrameT`/`chunksOfWordT`
-- renamed to `buildFramePB`/`chunksOfWordPB`) so that this module coexists with
-- every other module of the workspace (in particular with `Layout.Take.*` and with
-- `Work.Layout.AA.Defs`).  The proofs are unchanged.
import Mathlib
import Submission.Work.Resample.PBChunk.chunksOfDefs
import Submission.Work.Resample.PBChunk.buildDefs
import Submission.Work.Resample.PBChunk.chunksProof
import Submission.Work.Resample.PBChunk.inner_ev_tight
import Submission.Work.Resample.PBChunk.innerFrame_ev
import Submission.Work.Resample.PBChunk.groupStop_ev
import Submission.Work.Resample.PBChunk.chunksArith
import Submission.Work.Resample.PBChunk.chunk_len_mul_le_sum_vsz
import Submission.Work.Resample.PBChunk.buildCost_le
namespace Work.Resample.PBChunk

open Work.Layout
open HvdH Work.Layout

/-!
# `Work.Resample.buildFrameT`

This is the `buildProg` phase of `Work.Layout.chunksOf` (`Submission/Work/Layout/chunksOfDefs.lean`)
for a chunk list given as a `List (List Val)` together with the hypothesis that every member has
length `m` (the form used by the `Resample` area, as opposed to the `getD`-form hypothesis of
`Work.Layout.buildFrame`).

The proof follows that of `Work.Layout.buildFrame`; the strengthened frame, which also restores the
`mvVal` scratch stacks `sB`, `sC` and the scratch stack `sT2`, is obtained from the *proved*
`Work.Resample.PBChunk.innerFrame_ev` (`Submission/Work/Layout/innerFrame_ev.lean`).
-/

/-- `eos ≠ gCont` -/
theorem bf_gEos_ne_gCont : Glyph.eos ≠ gCont := by decide

/-- Prepending the `cons` of one element to a list encoding. -/
theorem bf_hAcc_cons (v : Val) (B : List Val) (R : List Glyph) :
    Glyph.cons :: (v.enc ++ ((ofList B).enc ++ R)) = (ofList (v :: B)).enc ++ R := by
  rw [enc_ofList_cons, List.cons_append, List.append_assoc]

/-- Summing over a reversed list. -/
theorem bf_sum_map_reverse {α : Type} (l : List α) (f : α → ℕ) :
    (l.reverse.map f).sum = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons c l ih =>
      simp only [List.reverse_cons, List.map_append, List.map_cons, List.sum_append,
        List.sum_cons, List.map_nil, List.sum_nil, ih]
      omega

/-- Cost arithmetic for `buildProg`: `Σ_c groupCost m c + #ch + 8` is dominated by the target
bound `100 * (vsz + #ch + 1)`. -/
theorem bf_cost_le (ch : List (List Val)) (m : ℕ) (hlen : ∀ c ∈ ch, c.length = m) :
    (ch.map (groupCost m)).sum + ch.length + 8 ≤
      100 * (vsz (ofList (ch.map ofList)) + ch.length + 1) := by
  induction ch with
  | nil => simp [ofList, vsz, Val.enc]
  | cons c ch ih =>
      have hc : c.length = m := hlen c (List.mem_cons_self ..)
      have hlen' : ∀ c' ∈ ch, c'.length = m := fun c' hc' => hlen c' (List.mem_cons_of_mem c hc')
      have ih' := ih hlen'
      have hv : vsz (ofList c) = (c.map vsz).sum + m + 1 := by
        rw [vsz_ofList_eq, sum_map_vsz_succ, hc]
      have hgc : groupCost m c = 40 * (c.map vsz).sum + 80 * m + 128 := rfl
      simp only [List.map_cons, List.sum_cons, List.length_cons, vsz_ofList_cons, hv, hgc]
      omega

/-! ## One non-final iteration of the outer loop -/

/-- One iteration of the outer loop `groupBody` on a chunk `c` of length `m`: push `nil`, copy the
master counter `sM` into `sW`, move the `m` elements of `c` onto stack 0, pop the working counter's
sentinel, push `cons`.  Restores every stack except `0`, `sT`, `sM`, `sW`, `sT2`, `sB`, `sC` (the
`mvVal` scratch stacks are restored, thanks to `Work.Resample.PBChunk.innerFrame_ev`). -/
theorem bf_groupBody {main : Cmd} {g : Reg → Glyph} {X : Stk → List Glyph}
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
  · rw [hs₇f 0, hs₆0, hs₅f 0 (by decide), hs₄0', bf_hAcc_cons (ofList c) B A0]
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

/-- `A.length + 1` iterations of the loop body `groupBody`, with the cost bound `loopCost m A`. -/
theorem bf_buildLoop {main : Cmd} {m : ℕ} (hm : 1 ≤ m) :
    ∀ (A : List (List Val)) (g : Reg → Glyph) (X : Stk → List Glyph) (B : List Val)
      (A0 T0 M0 W0 T20 B0 C0 : List Glyph),
      (∀ c ∈ A, c.length = m) →
      X sT = EncSeq A ++ gSent :: T0 →
      X sM = List.replicate m gPend ++ gSent :: M0 →
      X sW = W0 → X sT2 = T20 → X sB = B0 → X sC = C0 →
      X 0 = (ofList B).enc ++ A0 →
      g rLoopG = gCont →
      ∃ s' Cst, loopRuns main rLoopG gCont groupBody (A.length + 1) ⟨g, X⟩ s' Cst ∧
        Cst ≤ loopCost m A ∧
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
      refine ⟨s', loopCost m [], loopRuns.mono (by simp) (loopRuns.one hreg hev)
        (by simp [loopCost]), le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hreg', ?_⟩
      · rw [hfr 0, h0]
        simp
      · rw [hfr sT, hT]
        rfl
      · rw [hfr sM, hM]
      · rw [hfr sW, hW]
      · rw [hfr sT2, hT2]
      · rw [hfr sB, hB]
      · rw [hfr sC, hC]
      · intro j _ _ _ _ _ _ _
        exact hfr j
  | cons c A' ih =>
      intro g X B A0 T0 M0 W0 T20 B0 C0 hlen hT hM hW hT2 hB hC h0 hreg
      have hc : c.length = m := hlen c (List.mem_cons_self ..)
      have hlen' : ∀ c' ∈ A', c'.length = m :=
        fun c' hc' => hlen c' (List.mem_cons_of_mem c hc')
      obtain ⟨s₁, hev₁, hs₁0, hs₁T, hs₁M, hs₁W, hs₁T2, hs₁B, hs₁C, hs₁r, hs₁f⟩ :=
        bf_groupBody (main := main) (g := g) (X := X) (c := c) (A := A') (m := m) (B := B)
          (A0 := A0) (T0 := T0) (M0 := M0) (W0 := W0) (T20 := T20) (B0 := B0) (C0 := C0)
          hm hc hT hM hW hT2 hB hC h0
      obtain ⟨s₂, Cst, hrun, hcost, hs₂0, hs₂T, hs₂M, hs₂W, hs₂T2, hs₂B, hs₂C, hs₂r, hs₂f⟩ :=
        ih s₁.reg s₁.stk (ofList c :: B) A0 T0 M0 W0 T20 B0 C0 hlen'
          (by rw [hs₁T]) (by rw [hs₁M]) (by rw [hs₁W]) (by rw [hs₁T2])
          (by rw [hs₁B]) (by rw [hs₁C]) (by rw [hs₁0]) (by rw [hs₁r])
      have hgc : groupCost m c = 40 * (c.map vsz).sum + 80 * m + 128 := rfl
      refine ⟨s₂, groupCost m c + Cst + 1,
        loopRuns.succ' hreg hev₁ hrun (by rw [hgc]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        hs₂r, ?_⟩
      · rw [loopCost_cons]
        omega
      · rw [hs₂0, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
          List.append_assoc, List.cons_append, List.nil_append]
      · exact hs₂T
      · exact hs₂M
      · exact hs₂W
      · exact hs₂T2
      · exact hs₂B
      · exact hs₂C
      · intro j hj0 hjT hjM hjW hjT2 hjB hjC
        rw [hs₂f j hj0 hjT hjM hjW hjT2 hjB hjC, hs₁f j hj0 hjT hjM hjW hjT2 hjB hjC]

/-! ## `buildProg` -/

theorem buildFramePB {main : HvdH.Cmd} {g : HvdH.Reg → HvdH.Glyph}
    {X : HvdH.Stk → List HvdH.Glyph} {ch : List (List HvdH.Val)} {m : ℕ}
    {A0 T0 M0 W0 : List HvdH.Glyph} (hm : 1 ≤ m)
    (hlen : ∀ c ∈ ch, c.length = m)
    (hT : X Work.Resample.PBChunk.sT = ((Work.Resample.PBChunk.elemOrder ch).map HvdH.Val.enc).flatten ++
      Work.Layout.gSent :: T0)
    (hM : X Work.Resample.PBChunk.sM = List.replicate m Work.Layout.gPend ++ Work.Layout.gSent :: M0)
    (hW : X Work.Resample.PBChunk.sW = W0) (h0 : X 0 = A0) :
    ∃ s' n, Work.Layout.Ev main Work.Resample.PBChunk.buildProg ⟨g, X⟩ s' n ∧
      n ≤ 100 * (HvdH.vsz (HvdH.ofList (ch.map HvdH.ofList)) + ch.length + 1) ∧
      s'.stk 0 = (HvdH.ofList (ch.map HvdH.ofList)).enc ++ A0 ∧
      s'.stk Work.Resample.PBChunk.sT = Work.Layout.gSent :: T0 ∧
      s'.stk Work.Resample.PBChunk.sM = List.replicate m Work.Layout.gPend ++ Work.Layout.gSent :: M0 ∧
      s'.stk Work.Resample.PBChunk.sW = W0 ∧
      s'.stk Work.Resample.PBChunk.sB = X Work.Resample.PBChunk.sB ∧
      s'.stk Work.Resample.PBChunk.sC = X Work.Resample.PBChunk.sC ∧
      s'.stk Work.Resample.PBChunk.sT2 = X Work.Resample.PBChunk.sT2 ∧
      (∀ j : HvdH.Stk, j ≠ 0 → j ≠ Work.Resample.PBChunk.sT → j ≠ Work.Resample.PBChunk.sM →
        j ≠ Work.Resample.PBChunk.sW → j ≠ Work.Resample.PBChunk.sB → j ≠ Work.Resample.PBChunk.sC → s'.stk j = X j) := by
  have hlenRev : ∀ c ∈ ch.reverse, c.length = m :=
    fun c hc => hlen c (List.mem_reverse.mp hc)
  -- push the outer `nil`
  obtain ⟨s₁, hev₁, hs₁0, hs₁f, -, -⟩ :=
    step_pushK (main := main) (k := 0) (c := Glyph.nil) (g := g) (X := X)
  -- set the loop register
  obtain ⟨s₂, hev₂, hs₂r, -, hs₂f⟩ :=
    step_set (main := main) (r := rLoopG) (c := gCont) (g := s₁.reg) (X := s₁.stk)
  have hT₂ : s₂.stk sT = EncSeq ch.reverse ++ gSent :: T0 := by
    rw [hs₂f sT, hs₁f sT (by decide), EncSeq_reverse_eq, hT]
  have hM₂ : s₂.stk sM = List.replicate m gPend ++ gSent :: M0 := by
    rw [hs₂f sM, hs₁f sM (by decide), hM]
  have hW₂ : s₂.stk sW = W0 := by rw [hs₂f sW, hs₁f sW (by decide), hW]
  have hT2₂ : s₂.stk sT2 = X sT2 := by rw [hs₂f sT2, hs₁f sT2 (by decide)]
  have hB₂ : s₂.stk sB = X sB := by rw [hs₂f sB, hs₁f sB (by decide)]
  have hC₂ : s₂.stk sC = X sC := by rw [hs₂f sC, hs₁f sC (by decide)]
  have h0₂ : s₂.stk 0 = (ofList ([] : List Val)).enc ++ A0 := by
    rw [hs₂f 0, hs₁0, h0]; simp [ofList, Val.enc]
  -- the outer loop
  obtain ⟨s₃, n₃, hrun₃, hcost₃, hs₃0, hs₃T, hs₃M, hs₃W, hs₃T2, hs₃B, hs₃C, hs₃r, hs₃f⟩ :=
    bf_buildLoop (main := main) (m := m) hm (ch.reverse) s₂.reg s₂.stk ([] : List Val)
      A0 T0 M0 W0 (X sT2) (X sB) (X sC) hlenRev hT₂ hM₂ hW₂ hT2₂ hB₂ hC₂ h0₂ hs₂r
  have hloop : Ev main (.loop rLoopG gCont groupBody) s₂ s₃ (n₃ + 1) :=
    loopRuns.eval hrun₃ (by rw [hs₃r]; exact bf_gEos_ne_gCont)
  -- assemble
  have hprog : Ev main buildProg ⟨g, X⟩ s₃ (2 + 1 + (n₃ + 1)) := by
    have h23 : Ev main (seqs [.set rLoopG gCont, .loop rLoopG gCont groupBody]) s₁ s₃
        (1 + (n₃ + 1)) := Ev.seq' hev₂ hloop (by omega)
    have h123 : Ev main (seqs [pushK 0 Glyph.nil, .set rLoopG gCont,
        .loop rLoopG gCont groupBody]) ⟨g, X⟩ s₃ (2 + (1 + (n₃ + 1))) :=
      Ev.seq' hev₁ h23 (by omega)
    exact h123.mono (by omega)
  have hfin : (2 + 1 + (n₃ + 1)) ≤ 100 * (vsz (ofList (ch.map ofList)) + ch.length + 1) := by
    have h1 : n₃ ≤ (ch.reverse.map (groupCost m)).sum + ch.length + 4 := by
      have h := hcost₃
      simp only [loopCost, List.length_reverse] at h
      exact h
    have h2 : (ch.reverse.map (groupCost m)).sum = (ch.map (groupCost m)).sum :=
      bf_sum_map_reverse ch (groupCost m)
    have h3 := bf_cost_le ch m hlen
    omega
  have hs₃0' : s₃.stk 0 = (ofList (ch.map ofList)).enc ++ A0 := by
    rw [hs₃0]
    simp
  refine ⟨s₃, 100 * (vsz (ofList (ch.map ofList)) + ch.length + 1), hprog.mono hfin, le_rfl,
    hs₃0', hs₃T, hs₃M, hs₃W, hs₃B, hs₃C, hs₃T2, ?_⟩
  intro j hj0 hjT hjM hjW hjB hjC
  by_cases hjT2 : j = sT2
  · subst hjT2; rw [hs₃T2]
  · rw [hs₃f j hj0 hjT hjM hjW hjT2 hjB hjC, hs₂f j, hs₁f j hj0]

end Work.Resample.PBChunk