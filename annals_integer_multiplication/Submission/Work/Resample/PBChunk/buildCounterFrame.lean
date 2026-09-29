-- PRIVATE COPY (own namespace, Resample/PB dialect) of `Submission/Work/Layout/buildCounterFrame.lean`.
-- The declarations have been moved from `Work.Layout`/`Work.Resample` into the
-- dedicated namespace `Work.Resample.PBChunk` (with `buildFrameT`/`chunksOfWordT`
-- renamed to `buildFramePB`/`chunksOfWordPB`) so that this module coexists with
-- every other module of the workspace (in particular with `Layout.Take.*` and with
-- `Work.Layout.AA.Defs`).  The proofs are unchanged.
import Mathlib
import Submission.Work.Resample.PBChunk.chunksOfDefs
import Submission.Work.Resample.PBChunk.chunksProof
namespace Work.Resample.PBChunk

open Work.Layout
open HvdH

/-! ## Frame-preserving phase lemmas for `buildCounterProg`

`buildCounterProg = pushK sM gSent ;; loop (rLoopG = gCont) buildCounterBody ;; pop sBits rE`,
where the body reads the bits of the counter from `sBits` (most significant first, above the `gMark`
sentinel), doubling the unary counter on `sM` and adding one unit per `true` bit.

The point of this file (compared with `buildCounter_ev`) is that the scratch stack `sT2` used by
`doubleProg` is tracked through the whole program and shown to be *restored*. -/

/-! ### The `ite` that adds a bit -/

/-- `ite rE (bit true) (pushK sM gPend) skip` with `rE` holding the bit `b`: adds `b.toNat` units to
the unary counter on `sM` (i.e. pushes one `gPend` when `b = true`). -/
private theorem bcF_ite {main : Cmd} {g : Reg → Glyph} {X : Stk → List Glyph} {b : Bool}
    {k : ℕ} {M0 : List Glyph} (hr : g rE = Glyph.bit b)
    (hM : X sM = List.replicate k gPend ++ gSent :: M0) :
    ∃ s', Ev main (.ite rE (Glyph.bit true) (pushK sM gPend) .skip) ⟨g, X⟩ s' 3 ∧
      s'.stk sM = List.replicate (k + b.toNat) gPend ++ gSent :: M0 ∧
      (∀ j : Stk, j ≠ sM → s'.stk j = X j) := by
  cases b with
  | false =>
      have hneq : g rE ≠ Glyph.bit true := by rw [hr]; decide
      refine ⟨⟨g, X⟩, ?_, ?_, ?_⟩
      · exact (Ev.iteF hneq (ev_skip' main g X)).mono (by omega)
      · show X sM = List.replicate (k + false.toNat) gPend ++ gSent :: M0
        rw [hM, show false.toNat = 0 from rfl, Nat.add_zero]
      · intro j _
        rfl
  | true =>
      obtain ⟨s₁, hev₁, hs₁M, hs₁f, -⟩ :=
        step_pushK (main := main) (g := g) (X := X) (k := sM) (c := gPend)
      refine ⟨s₁, Ev.iteT hr hev₁, ?_, ?_⟩
      · rw [hs₁M, hM, show true.toNat = 1 from rfl, List.replicate_succ]
        rfl
      · intro j hj
        rw [hs₁f j hj]

/-! ### The two cases of `buildCounterBody` -/

/-- The `gMark` case of `buildCounterBody`: nothing happens, the loop is stopped. -/
private theorem bcF_body_stop {main : Cmd} {g : Reg → Glyph} {X : Stk → List Glyph}
    {B6 : List Glyph} (hh : X sBits = gMark :: B6) :
    ∃ s', Ev main buildCounterBody ⟨g, X⟩ s' 3 ∧ s'.stk sBits = X sBits ∧
      s'.reg rLoopG = Glyph.eos ∧ (∀ j : Stk, s'.stk j = X j) := by
  obtain ⟨s₁, hev₁, hs₁B, hs₁r, hs₁f, -⟩ :=
    step_peek (main := main) (g := g) (X := X) (k := sBits) (r := rE) hh
  obtain ⟨s₂, hev₂, hs₂r, -, hs₂f⟩ :=
    step_set (main := main) (r := rLoopG) (c := Glyph.eos) (g := s₁.reg) (X := s₁.stk)
  have hs₁X : s₁.stk sBits = X sBits := hs₁B.trans hh.symm
  have hit : Ev main (.ite rE gMark (.set rLoopG Glyph.eos)
      (seqs [.pop sBits rE, .push sFl rE, doubleProg, .peek sFl rE,
        .ite rE (Glyph.bit true) (pushK sM gPend) .skip, .pop sFl rE,
        .set rLoopG gCont])) s₁ s₂ 2 := Ev.iteT hs₁r hev₂
  have hbody : Ev main buildCounterBody ⟨g, X⟩ s₂ 3 := Ev.seq' hev₁ hit (by omega)
  refine ⟨s₂, hbody, ?_, hs₂r, ?_⟩
  · rw [hs₂f sBits]
    exact hs₁X
  · intro j
    rw [hs₂f j]
    rcases eq_or_ne j sBits with rfl | hj
    · exact hs₁X
    · exact hs₁f j hj

/-- The "continue" case of `buildCounterBody`: pop the bit `b` from `sBits`, push it on the scratch
stack `sFl`, double the unary counter on `sM` and add `b.toNat`; `sFl` and `sT2` are restored. -/
private theorem bcF_body_go {main : Cmd} {g : Reg → Glyph} {X : Stk → List Glyph}
    {L : List Glyph} {b : Bool} {k : ℕ} {M0 F0 T0 : List Glyph}
    (hB : X sBits = Glyph.bit b :: L)
    (hM : X sM = List.replicate k gPend ++ gSent :: M0)
    (hF : X sFl = F0) (hT : X sT2 = T0) :
    ∃ s', Ev main buildCounterBody ⟨g, X⟩ s' (20 + 14 * (k + 1)) ∧
      s'.stk sBits = L ∧
      s'.stk sM = List.replicate (2 * k + b.toNat) gPend ++ gSent :: M0 ∧
      s'.stk sFl = F0 ∧ s'.stk sT2 = T0 ∧ s'.reg rLoopG = gCont ∧
      (∀ j : Stk, j ≠ sBits → j ≠ sFl → j ≠ sM → j ≠ sT2 → s'.stk j = X j) := by
  obtain ⟨s₁, hev₁, hs₁B, hs₁r, hs₁f, -⟩ :=
    step_peek (main := main) (g := g) (X := X) (k := sBits) (r := rE) hB
  obtain ⟨s₂, hev₂, hs₂B, hs₂r, hs₂f, -⟩ :=
    step_pop (main := main) (k := sBits) (r := rE) (g := s₁.reg) (X := s₁.stk) hs₁B
  obtain ⟨s₃, hev₃, hs₃F, hs₃f, -⟩ :=
    step_push (main := main) (k := sFl) (r := rE) (g := s₂.reg) (X := s₂.stk)
      (v := Glyph.bit b) hs₂r
  have hs₃M : s₃.stk sM = List.replicate k gPend ++ gSent :: M0 := by
    rw [hs₃f sM (by decide : sM ≠ sFl), hs₂f sM (by decide : sM ≠ sBits),
      hs₁f sM (by decide : sM ≠ sBits), hM]
  have hs₃T : s₃.stk sT2 = T0 := by
    rw [hs₃f sT2 (by decide : sT2 ≠ sFl), hs₂f sT2 (by decide : sT2 ≠ sBits),
      hs₁f sT2 (by decide : sT2 ≠ sBits), hT]
  obtain ⟨s₄, n₄, hev₄, hn₄, hs₄M, hs₄T, hfr₄⟩ :=
    double_ev (main := main) (g := s₃.reg) (X := s₃.stk) (k := k) (M0 := M0) (T0 := T0) hs₃M hs₃T
  have h4 : Ev main doubleProg ⟨s₃.reg, s₃.stk⟩ s₄ (14 * (k + 1) + 10) := hev₄.mono hn₄
  have hs₄F : s₄.stk sFl = Glyph.bit b :: F0 := by
    rw [hfr₄ sFl (by decide : sFl ≠ sM) (by decide : sFl ≠ sT2), hs₃F,
      hs₂f sFl (by decide : sFl ≠ sBits), hs₁f sFl (by decide : sFl ≠ sBits), hF]
  obtain ⟨s₅, hev₅, hs₅F, hs₅r, hs₅f, -⟩ :=
    step_peek (main := main) (g := s₄.reg) (X := s₄.stk) (k := sFl) (r := rE) hs₄F
  have hs₅M : s₅.stk sM = List.replicate (2 * k) gPend ++ gSent :: M0 := by
    rw [hs₅f sM (by decide : sM ≠ sFl), hs₄M]
  obtain ⟨s₆, hev₆, hs₆M, hs₆f⟩ :=
    bcF_ite (main := main) (g := s₅.reg) (X := s₅.stk) (b := b) (k := 2 * k) (M0 := M0) hs₅r hs₅M
  have hs₆F : s₆.stk sFl = Glyph.bit b :: F0 := by
    rw [hs₆f sFl (by decide : sFl ≠ sM), hs₅F]
  obtain ⟨s₇, hev₇, hs₇F, -, hs₇f, -⟩ :=
    step_pop (main := main) (k := sFl) (r := rE) (g := s₆.reg) (X := s₆.stk) hs₆F
  obtain ⟨s₈, hev₈, hs₈r, -, hs₈f⟩ :=
    step_set (main := main) (r := rLoopG) (c := gCont) (g := s₇.reg) (X := s₇.stk)
  have hcond : ¬ (s₁.reg rE = gMark) := by
    intro h
    rw [hs₁r] at h
    exact gMark_ne_bit b h.symm
  have h56 : Ev main (seqs [.peek sFl rE, .ite rE (Glyph.bit true) (pushK sM gPend) .skip])
      s₄ s₆ (1 + 3) := Ev.seq' hev₅ hev₆ (by omega)
  have h78 : Ev main (seqs [.pop sFl rE, .set rLoopG gCont]) s₆ s₈ (1 + 1) :=
    Ev.seq' hev₇ hev₈ (by omega)
  have h678 : Ev main (seqs [.ite rE (Glyph.bit true) (pushK sM gPend) .skip,
      .pop sFl rE, .set rLoopG gCont]) s₅ s₈ (3 + (1 + 1)) := Ev.seq' hev₆ h78 (by omega)
  have hRest : Ev main (seqs [.peek sFl rE, .ite rE (Glyph.bit true) (pushK sM gPend) .skip,
      .pop sFl rE, .set rLoopG gCont]) s₄ s₈ (1 + (3 + (1 + 1))) :=
    Ev.seq' hev₅ h678 (by omega)
  have hFrom3 : Ev main (seqs [doubleProg, .peek sFl rE,
      .ite rE (Glyph.bit true) (pushK sM gPend) .skip, .pop sFl rE, .set rLoopG gCont])
      s₃ s₈ ((14 * (k + 1) + 10) + (1 + (3 + (1 + 1)))) := Ev.seq' h4 hRest (by omega)
  have hFrom2 : Ev main (seqs [.push sFl rE, doubleProg, .peek sFl rE,
      .ite rE (Glyph.bit true) (pushK sM gPend) .skip, .pop sFl rE, .set rLoopG gCont])
      s₂ s₈ (1 + ((14 * (k + 1) + 10) + (1 + (3 + (1 + 1))))) := Ev.seq' hev₃ hFrom3 (by omega)
  have hFrom1 : Ev main (seqs [.pop sBits rE, .push sFl rE, doubleProg, .peek sFl rE,
      .ite rE (Glyph.bit true) (pushK sM gPend) .skip, .pop sFl rE, .set rLoopG gCont])
      s₁ s₈ (1 + (1 + ((14 * (k + 1) + 10) + (1 + (3 + (1 + 1)))))) :=
    Ev.seq' hev₂ hFrom2 (by omega)
  have hit : Ev main (.ite rE gMark (.set rLoopG Glyph.eos)
      (seqs [.pop sBits rE, .push sFl rE, doubleProg, .peek sFl rE,
        .ite rE (Glyph.bit true) (pushK sM gPend) .skip, .pop sFl rE,
        .set rLoopG gCont])) s₁ s₈
      ((1 + (1 + ((14 * (k + 1) + 10) + (1 + (3 + (1 + 1)))))) + 1) :=
    Ev.iteF hcond hFrom1
  have hbody0 : Ev main buildCounterBody ⟨g, X⟩ s₈
      (1 + ((1 + (1 + ((14 * (k + 1) + 10) + (1 + (3 + (1 + 1)))))) + 1)) :=
    Ev.seq' hev₁ hit (by omega)
  have hbody : Ev main buildCounterBody ⟨g, X⟩ s₈ (20 + 14 * (k + 1)) := hbody0.mono (by omega)
  refine ⟨s₈, hbody, ?_, ?_, ?_, ?_, hs₈r, ?_⟩
  · rw [hs₈f sBits, hs₇f sBits (by decide : sBits ≠ sFl), hs₆f sBits (by decide : sBits ≠ sM),
      hs₅f sBits (by decide : sBits ≠ sFl), hfr₄ sBits (by decide : sBits ≠ sM)
        (by decide : sBits ≠ sT2),
      hs₃f sBits (by decide : sBits ≠ sFl), hs₂B]
  · rw [hs₈f sM, hs₇f sM (by decide : sM ≠ sFl), hs₆M]
  · rw [hs₈f sFl, hs₇F]
  · rw [hs₈f sT2, hs₇f sT2 (by decide : sT2 ≠ sFl), hs₆f sT2 (by decide : sT2 ≠ sM),
      hs₅f sT2 (by decide : sT2 ≠ sFl), hs₄T]
  · intro j hjB hjF hjM hjT
    rw [hs₈f j, hs₇f j hjF, hs₆f j hjM, hs₅f j hjF, hfr₄ j hjM hjT, hs₃f j hjF,
      hs₂f j hjB, hs₁f j hjB]

/-! ### The bit-builder loop -/

/-- The `buildCounterBody` loop: processes the bits of `L` (most significant first) on `sBits`,
turning the unary counter on `sM` into `gPend^(valBits L k) ++ [gSent]`; `sFl` and `sT2` are
restored and everything outside `{sBits, sFl, sM, sT2}` is untouched. -/
private theorem bcF_loop {main : Cmd} {B6 M0 F0 T0 : List Glyph} :
    ∀ (L : List Bool) (g : Reg → Glyph) (X : Stk → List Glyph) (k : ℕ),
      g rLoopG = gCont → X sBits = bitsG L ++ gMark :: B6 →
      X sM = List.replicate k gPend ++ gSent :: M0 → X sFl = F0 → X sT2 = T0 →
      ∃ s', loopRuns main rLoopG gCont buildCounterBody (L.length + 1) ⟨g, X⟩ s'
          (40 * (Ssum L k + L.length + 1)) ∧
        s'.stk sBits = gMark :: B6 ∧
        s'.stk sM = List.replicate (valBits L k) gPend ++ gSent :: M0 ∧
        s'.stk sFl = F0 ∧ s'.stk sT2 = T0 ∧ s'.reg rLoopG = Glyph.eos ∧
        (∀ j : Stk, j ≠ sBits → j ≠ sFl → j ≠ sM → j ≠ sT2 → s'.stk j = X j) := by
  intro L
  induction L with
  | nil =>
      intro g X k hreg hB hM hF hT
      obtain ⟨s₁, hev₁, hs₁B, hs₁r, hfr₁⟩ :=
        bcF_body_stop (main := main) (g := g) (X := X) (B6 := B6) (by simpa using hB)
      have hloop : loopRuns main rLoopG gCont buildCounterBody 1 ⟨g, X⟩ s₁ (3 + 1) :=
        loopRuns.one (show (⟨g, X⟩ : State).reg rLoopG = gCont from hreg) hev₁
      have hC : (3 + 1 : ℕ) ≤ 40 * (Ssum ([] : List Bool) k + ([] : List Bool).length + 1) := by
        simp [Ssum]
      have hrun : loopRuns main rLoopG gCont buildCounterBody
          ((([] : List Bool).length) + 1) ⟨g, X⟩ s₁
          (40 * (Ssum ([] : List Bool) k + ([] : List Bool).length + 1)) :=
        loopRuns.mono (k := 1) (by omega) hloop hC
      refine ⟨s₁, hrun, ?_, ?_, ?_, ?_, hs₁r, ?_⟩
      · rw [hs₁B]
        simpa using hB
      · rw [hfr₁ sM, hM]
        rfl
      · rw [hfr₁ sFl, hF]
      · rw [hfr₁ sT2, hT]
      · intro j hj1 hj2 hj3 hj4
        rw [hfr₁ j]
  | cons b t ih =>
      intro g X k hreg hB hM hF hT
      have hB' : X sBits = Glyph.bit b :: (bitsG t ++ gMark :: B6) := by rw [hB]; rfl
      obtain ⟨s₁, hev₁, hs₁B, hs₁M, hs₁F, hs₁T, hs₁r, hfr₁⟩ :=
        bcF_body_go (main := main) (g := g) (X := X) (L := bitsG t ++ gMark :: B6) (b := b)
          (k := k) (M0 := M0) (F0 := F0) (T0 := T0) hB' hM hF hT
      obtain ⟨s₂, hrun₂, hs₂B, hs₂M, hs₂F, hs₂T, hs₂r, hfr₂⟩ :=
        ih s₁.reg s₁.stk (2 * k + b.toNat) hs₁r hs₁B hs₁M hs₁F hs₁T
      refine ⟨s₂, loopRuns.succ' (show (⟨g, X⟩ : State).reg rLoopG = gCont from hreg) hev₁
        hrun₂ ?_, ?_, ?_, ?_, ?_, hs₂r, ?_⟩
      · rw [show (b :: t).length = t.length + 1 from rfl, Ssum_cons]
        omega
      · rw [hs₂B]
      · rw [hs₂M, valBits_cons]
      · exact hs₂F
      · exact hs₂T
      · intro j hj1 hj2 hj3 hj4
        rw [hfr₂ j hj1 hj2 hj3 hj4, hfr₁ j hj1 hj2 hj3 hj4]

/-! ### The whole program -/

/-- Requires the import of `Submission.Work.Layout.chunksOfDefs` (and it may import
`Submission.Work.Layout.chunksProof` for `Work.Resample.PBChunk.double_ev`).

STRENGTHENING of `Work.Layout.buildCounter_ev`: `buildCounterProg` also restores the scratch stack
`sT2` (which `Work.Resample.PBChunk.doubleProg` uses and restores, see `Work.Resample.PBChunk.double_ev`).  Needed for
the frame bookkeeping of the `LayoutLib.chunksOf` assembly. -/
theorem buildCounterFrame {main : HvdH.Cmd} {g : HvdH.Reg → HvdH.Glyph}
    {X : HvdH.Stk → List HvdH.Glyph} {L : List Bool} {B6 M0 : List HvdH.Glyph}
    (h6 : X Work.Resample.PBChunk.sBits = Work.Resample.PBChunk.bitsG L ++ Work.Layout.gMark :: B6)
    (hM : X Work.Resample.PBChunk.sM = M0) :
    ∃ s' n, Work.Layout.Ev main Work.Resample.PBChunk.buildCounterProg ⟨g, X⟩ s' n ∧
      n ≤ 100 * (Work.Resample.PBChunk.valBits L 0 + L.length + 1) ∧
      s'.stk Work.Resample.PBChunk.sM =
        List.replicate (Work.Resample.PBChunk.valBits L 0) Work.Layout.gPend ++
          Work.Layout.gSent :: M0 ∧
      s'.stk Work.Resample.PBChunk.sBits = B6 ∧
      s'.stk Work.Resample.PBChunk.sT2 = X Work.Resample.PBChunk.sT2 ∧
      (∀ j : HvdH.Stk, j ≠ Work.Resample.PBChunk.sM → j ≠ Work.Resample.PBChunk.sBits →
        j ≠ Work.Resample.PBChunk.sT2 → s'.stk j = X j) := by
  obtain ⟨s₀, hev₀, hs₀M, hs₀f, -, -⟩ :=
    step_pushK (main := main) (g := g) (X := X) (k := sM) (c := gSent)
  obtain ⟨s₁, hev₁, hs₁r, -, hs₁f⟩ :=
    step_set (main := main) (r := rLoopG) (c := gCont) (g := s₀.reg) (X := s₀.stk)
  have hM₁ : s₁.stk sM = List.replicate 0 gPend ++ gSent :: M0 := by
    rw [hs₁f sM, hs₀M, hM]
    rfl
  have hB₁ : s₁.stk sBits = bitsG L ++ gMark :: B6 := by
    rw [hs₁f sBits, hs₀f sBits (by decide : sBits ≠ sM), h6]
  have hF₁ : s₁.stk sFl = X sFl := by
    rw [hs₁f sFl, hs₀f sFl (by decide : sFl ≠ sM)]
  have hT₁ : s₁.stk sT2 = X sT2 := by
    rw [hs₁f sT2, hs₀f sT2 (by decide : sT2 ≠ sM)]
  obtain ⟨s₂, hrun₂, hs₂B, hs₂M, hs₂F, hs₂T, hs₂r, hfr₂⟩ :=
    bcF_loop (main := main) (B6 := B6) (M0 := M0) (F0 := X sFl) (T0 := X sT2)
      L s₁.reg s₁.stk 0 (by rw [hs₁r]) hB₁ hM₁ hF₁ hT₁
  obtain ⟨s₃, hev₃, hs₃B, -, hs₃f, -⟩ :=
    step_pop (main := main) (k := sBits) (r := rE) (g := s₂.reg) (X := s₂.stk) hs₂B
  have hloop : Ev main (.loop rLoopG gCont buildCounterBody) s₁ s₂
      (40 * (Ssum L 0 + L.length + 1) + 1) :=
    loopRuns.eval hrun₂ (by rw [hs₂r]; decide)
  have htail : Ev main (seqs [.loop rLoopG gCont buildCounterBody, .pop sBits rE]) s₁ s₃
      ((40 * (Ssum L 0 + L.length + 1) + 1) + 1) := Ev.seq' hloop hev₃ (by omega)
  have hmiddle : Ev main (seqs [.set rLoopG gCont, .loop rLoopG gCont buildCounterBody,
      .pop sBits rE]) s₀ s₃ (1 + ((40 * (Ssum L 0 + L.length + 1) + 1) + 1)) :=
    Ev.seq' hev₁ htail (by omega)
  have hcompose : Ev main (seqs [pushK sM gSent, .set rLoopG gCont,
      .loop rLoopG gCont buildCounterBody, .pop sBits rE]) ⟨g, X⟩ s₃
      (2 + (1 + ((40 * (Ssum L 0 + L.length + 1) + 1) + 1))) :=
    Ev.seq' hev₀ hmiddle (by omega)
  have hmain : Ev main buildCounterProg ⟨g, X⟩ s₃ (40 * (Ssum L 0 + L.length + 1) + 5) :=
    hcompose.mono (by omega)
  refine ⟨s₃, 40 * (Ssum L 0 + L.length + 1) + 5, hmain, ?_, ?_, ?_, ?_, ?_⟩
  · have hS := Ssum_zero_le L
    omega
  · rw [hs₃f sM (by decide : sM ≠ sBits), hs₂M]
  · exact hs₃B
  · rw [hs₃f sT2 (by decide : sT2 ≠ sBits), hs₂T]
  · intro j hjM hjB hjT
    rw [hs₃f j hjB]
    by_cases hjF : j = sFl
    · subst hjF
      exact hs₂F
    · rw [hfr₂ j hjB hjF hjM hjT, hs₁f j, hs₀f j hjM]

end Work.Resample.PBChunk