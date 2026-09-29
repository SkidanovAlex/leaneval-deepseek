import Mathlib
import Submission.Work.SynFFT.mrgLvDefs

/-!
# `Work.SynFFT.foldLoopEv`

`foldLoop` (defined in `Submission/Work/SynFFT/mrgLvDefs.lean`) folds a raw `cons`-chain of values
sitting on stack 0 above the boundary marker `gMark` into a list *value* on stack `lvOut`:

* stack 0 starts as `encs acc ++ gMark :: T0` (the values `acc`, head first, above the marker);
* `lvOut` starts as `(ofList L).enc ++ gMark :: B`;
* each iteration moves the top value `v` of stack 0 onto the front of the list value of `lvOut`
  (via `Work.Layout.prependTo`), wrapping it in a fresh `cons` cell;
* the loop stops when the marker `gMark` surfaces on stack 0.

The result is `lvOut = (ofList (acc.reverse ++ L)).enc ++ gMark :: B`, stack 0 back to
`gMark :: T0`, and every other stack (in particular the two scratch stacks `lvS1`, `lvS2`) restored.
The cost is `O(Σᵥ (vsz v + 1))`, i.e. linear in the size of the raw chain.

The proof is an induction on `acc`; the scratch-stack restoration is obtained from a strengthened
version of `Work.Layout.AA.prependTo_ev` (`prependToS` below), which exposes the fact that `mvVal`
restores its two scratch stacks as well.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.SynFFT

open HvdH

/-- The head of a nonempty value encoding is never the boundary marker `gMark`. -/
theorem headD_enc_ne_gMark (v : Val) (A : List Glyph) :
    (v.enc ++ A).headD Glyph.eos ≠ Work.Layout.gMark := by
  intro h
  cases v with
  | int z =>
      simp only [Val.enc, List.cons_append, List.headD_cons] at h
      by_cases hz : z < 0
      · rw [if_pos hz] at h; exact Work.Layout.gMark_ne_neg h.symm
      · rw [if_neg hz] at h; exact Work.Layout.gMark_ne_pos h.symm
  | nil =>
      simp only [Val.enc, List.singleton_append, List.headD_cons] at h
      exact Work.Layout.gMark_ne_nil h.symm
  | cons a b =>
      simp only [Val.enc, List.cons_append, List.headD_cons] at h
      exact Work.Layout.gMark_ne_cons h.symm

/-- `Work.Layout.prependTo` moves the top value `v` of stack `a` onto the front of the value list of
stack `b` (replacing `ofList L` by `ofList (v :: L)`), and in addition restores the two scratch
stacks `c`, `d` (this is the strengthening of `Work.Layout.AA.prependTo_ev` used below: the loop
`foldLoop` must leave *all* stacks other than 0 and `lvOut` untouched, and `lvS1`/`lvS2` are its
scratch stacks). -/
theorem prependToS (main : Cmd) (a b c d : Stk) (rr : Reg)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (g : Reg → Glyph) (X : Stk → List Glyph) (v : Val) (L : List Val) (A B : List Glyph)
    (ha : X a = v.enc ++ A) (hb : X b = (ofList L).enc ++ B) :
    ∃ s' n, Work.Layout.Ev main (Work.Layout.prependTo a b c d rr) ⟨g, X⟩ s' n ∧
      n ≤ 20 * (vsz v + 1) + 4 ∧ s'.stk a = A ∧
      s'.stk b = (ofList (v :: L)).enc ++ B ∧
      s'.stk c = X c ∧ s'.stk d = X d ∧
      (∀ j, j ≠ a → j ≠ b → s'.stk j = X j) := by
  obtain ⟨s₁, n₁, h1, hn₁, ha₁, hc₁, hd₁, hf₁⟩ :=
    Work.Layout.mvA_ev (main := main) hac had hcd v A (X c) (X d) g X ha rfl rfl
  have hb₁ : s₁.stk b = (ofList L).enc ++ B := by
    rw [hf₁ b hab.symm hbc hbd]; exact hb
  obtain ⟨s₂, n₂, h2, hn₂, hc₂, hb₂, hf₂⟩ :=
    Work.Layout.mvB_ev (main := main) hbc (G := v.enc.reverse) (C := X c)
      (B := (ofList L).enc ++ B) (Work.Layout.gMark_not_mem_enc_rev v) hc₁ hb₁
  have hlen : (v.enc.reverse).length = vsz v := by simp [vsz]
  have hn₂' : n₂ ≤ 4 * (vsz v + 1) + 3 := by rw [← hlen]; exact hn₂
  have hd₂ : s₂.stk d = X d := by rw [hf₂ d hcd.symm hbd.symm]; exact hd₁
  have hcost : n₁ + n₂ ≤ 16 * (vsz v + 1) := by
    have hv := Work.Layout.one_le_vsz v; omega
  have hp : Work.Layout.Ev main (Work.Kernel.pushGlyphs [Glyph.cons] b rr) s₂
      (Work.Kernel.pushGlyphsState [Glyph.cons] b rr s₂) 3 :=
    ⟨_, Work.Kernel.eval_pushGlyphs main [Glyph.cons] b rr s₂, by decide⟩
  have hmv : Work.Layout.Ev main (Work.Layout.mvVal a b c d) ⟨g, X⟩ s₂ (n₁ + n₂) :=
    Work.Layout.Ev.seq h1 h2
  have hmain : Work.Layout.Ev main (Work.Layout.prependTo a b c d rr) ⟨g, X⟩
      (Work.Kernel.pushGlyphsState [Glyph.cons] b rr s₂) (n₁ + n₂ + 3) :=
    Work.Layout.Ev.seq hmv hp
  refine ⟨_, _, hmain, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Work.Kernel.pushGlyphsState_stk, if_neg hab, hf₂ a hac hab]; exact ha₁
  · rw [Work.Kernel.pushGlyphsState_stk, if_pos rfl, hb₂,
      show (ofList (v :: L)).enc = Glyph.cons :: (v.enc ++ (ofList L).enc) from rfl]
    simp [List.append_assoc]
  · rw [Work.Kernel.pushGlyphsState_stk, if_neg (hbc.symm)]; exact hc₂
  · rw [Work.Kernel.pushGlyphsState_stk, if_neg (hbd.symm)]; exact hd₂
  · intro j hja hjb
    by_cases hjc : j = c
    · subst hjc
      rw [Work.Kernel.pushGlyphsState_stk, if_neg hbc.symm]
      exact hc₂
    · by_cases hjd : j = d
      · subst hjd
        rw [Work.Kernel.pushGlyphsState_stk, if_neg hbd.symm]
        exact hd₂
      · rw [Work.Kernel.pushGlyphsState_stk, if_neg hjb, hf₂ j hjc hjb, hf₁ j hja hjc hjd]

/-! ## One iteration of the fold -/

/-- One *continuing* iteration of `foldLoop`: the top value `v` of stack 0 is moved onto the front of
the list value of `lvOut`, ``lvF`` is set back to `cons`, and all stacks other than `0` and `lvOut`
(including the scratch stacks `lvS1`, `lvS2`) are restored. -/
theorem foldStep_cont {main : Cmd} {v : Val} {A : List Glyph} {L : List Val} {B : List Glyph}
    {g : Reg → Glyph} {X : Stk → List Glyph}
    (hX0 : X 0 = v.enc ++ A) (hXO : X lvOut = (ofList L).enc ++ B) :
    ∃ s' n, Work.Layout.Ev main foldStep_xmrgLvDefs ⟨g, X⟩ s' n ∧ n ≤ 20 * (vsz v + 1) + 8 ∧
      s'.stk 0 = A ∧ s'.stk lvOut = (ofList (v :: L)).enc ++ B ∧
      s'.stk lvS1 = X lvS1 ∧ s'.stk lvS2 = X lvS2 ∧
      s'.reg lvF = Glyph.cons ∧
      (∀ j, j ≠ 0 → j ≠ lvOut → s'.stk j = X j) := by
  have hhead : (X 0).headD Glyph.eos ≠ Work.Layout.gMark := by
    rw [hX0]; exact headD_enc_ne_gMark v A
  have hpk : Work.Layout.Ev main (.peek 0 lvP) ⟨g, X⟩
      ⟨Function.update g lvP ((X 0).headD Glyph.eos), X⟩ 1 :=
    Work.Layout.ev_peek' main 0 lvP g X
  obtain ⟨s₁, n₁, h1, hn₁, ha₁, hb₁, hc₁, hd₁, hf₁⟩ :=
    prependToS main 0 lvOut lvS1 lvS2 lvP (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (Function.update g lvP ((X 0).headD Glyph.eos)) X v L A B hX0 hXO
  have hset : Work.Layout.Ev main (.set lvF Glyph.cons) s₁
      ⟨Function.update s₁.reg lvF Glyph.cons, s₁.stk⟩ 1 :=
    Work.Layout.ev_set' main lvF Glyph.cons s₁.reg s₁.stk
  have hbody : Work.Layout.Ev main
      (.seq (Work.Layout.prependTo 0 lvOut lvS1 lvS2 lvP) (.set lvF Glyph.cons))
      ⟨Function.update g lvP ((X 0).headD Glyph.eos), X⟩
      ⟨Function.update s₁.reg lvF Glyph.cons, s₁.stk⟩ (n₁ + 1) :=
    Work.Layout.Ev.seq h1 hset
  have hite : Work.Layout.Ev main
      (.ite lvP Work.Layout.gMark (.set lvF Glyph.eos)
        (.seq (Work.Layout.prependTo 0 lvOut lvS1 lvS2 lvP) (.set lvF Glyph.cons)))
      ⟨Function.update g lvP ((X 0).headD Glyph.eos), X⟩
      ⟨Function.update s₁.reg lvF Glyph.cons, s₁.stk⟩ (n₁ + 1 + 1) :=
    Work.Layout.Ev.iteF (by
      change (Function.update g lvP ((X 0).headD Glyph.eos)) lvP ≠ Work.Layout.gMark
      rw [Function.update_self]; exact hhead) hbody
  have hmain : Work.Layout.Ev main foldStep_xmrgLvDefs ⟨g, X⟩
      ⟨Function.update s₁.reg lvF Glyph.cons, s₁.stk⟩ (1 + (n₁ + 1 + 1)) :=
    Work.Layout.Ev.seq hpk hite
  refine ⟨_, _, hmain, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ha₁
  · exact hb₁
  · exact hc₁
  · exact hd₁
  · simp
  · intro j hj0 hjO; exact hf₁ j hj0 hjO

/-- One *stopping* iteration of `foldLoop`: the boundary marker has surfaced on stack 0, so the flag
is set to `eos` and nothing else changes. -/
theorem foldStep_stop {main : Cmd} {T0 : List Glyph} {g : Reg → Glyph} {X : Stk → List Glyph}
    (hX0 : X 0 = Work.Layout.gMark :: T0) :
    ∃ s' n, Work.Layout.Ev main foldStep_xmrgLvDefs ⟨g, X⟩ s' n ∧ n ≤ 4 ∧
      s'.stk = X ∧ s'.reg lvF = Glyph.eos := by
  have hpk : Work.Layout.Ev main (.peek 0 lvP) ⟨g, X⟩
      ⟨Function.update g lvP ((X 0).headD Glyph.eos), X⟩ 1 :=
    Work.Layout.ev_peek' main 0 lvP g X
  have hpkv : (Function.update g lvP ((X 0).headD Glyph.eos)) lvP = Work.Layout.gMark := by
    rw [Function.update_self, hX0, List.headD_cons]
  have hset : Work.Layout.Ev main (.set lvF Glyph.eos)
      ⟨Function.update g lvP ((X 0).headD Glyph.eos), X⟩
      ⟨Function.update (Function.update g lvP ((X 0).headD Glyph.eos)) lvF Glyph.eos, X⟩ 1 :=
    Work.Layout.ev_set' main lvF Glyph.eos _ X
  have hite : Work.Layout.Ev main
      (.ite lvP Work.Layout.gMark (.set lvF Glyph.eos)
        (.seq (Work.Layout.prependTo 0 lvOut lvS1 lvS2 lvP) (.set lvF Glyph.cons)))
      ⟨Function.update g lvP ((X 0).headD Glyph.eos), X⟩
      ⟨Function.update (Function.update g lvP ((X 0).headD Glyph.eos)) lvF Glyph.eos, X⟩
      (1 + 1) :=
    Work.Layout.Ev.iteT hpkv hset
  have hmain : Work.Layout.Ev main foldStep_xmrgLvDefs ⟨g, X⟩
      ⟨Function.update (Function.update g lvP ((X 0).headD Glyph.eos)) lvF Glyph.eos, X⟩
      (1 + (1 + 1)) :=
    Work.Layout.Ev.seq hpk hite
  exact ⟨_, _, hmain, by omega, rfl, by simp⟩

/-! ## The whole loop -/

/-- The loop `lvF`-`cons`-`foldStep_xmrgLvDefs` starting with a clean flag: it performs `acc.length` continuing
iterations (moving the values of `acc`, head first, onto `lvOut`) and one stopping iteration. -/
theorem foldLoopRun (main : Cmd) : ∀ (acc : List Val),
    ∀ (L : List Val) (T0 B : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph),
      g lvF = Glyph.cons →
      X 0 = encs acc ++ Work.Layout.gMark :: T0 →
      X lvOut = (ofList L).enc ++ Work.Layout.gMark :: B →
      ∃ s' C, Work.Layout.loopRuns main lvF Glyph.cons foldStep_xmrgLvDefs (acc.length + 1) ⟨g, X⟩ s' C ∧
        C ≤ 40 * ((acc.map (fun v => vsz v + 1)).sum + 1) ∧
        s'.stk 0 = Work.Layout.gMark :: T0 ∧
        s'.stk lvOut = (ofList (acc.reverse ++ L)).enc ++ Work.Layout.gMark :: B ∧
        s'.reg lvF = Glyph.eos ∧
        (∀ j, j ≠ 0 → j ≠ lvOut → s'.stk j = X j) := by
  intro acc
  induction acc with
  | nil =>
      intro L T0 B g X hg hX0 hXO
      obtain ⟨s', n, he, hn, hstk, hreg⟩ :=
        foldStep_stop (main := main) (T0 := T0) (g := g) (X := X) hX0
      refine ⟨s', n + 1, Work.Layout.loopRuns.succ' hg he Work.Layout.loopRuns.zero (by omega),
        by omega, ?_, ?_, ?_, ?_⟩
      · rw [hstk, hX0]; simp only [Work.Kernel.encs_nil, List.nil_append]
      · rw [hstk, hXO]; simp only [List.reverse_nil, List.nil_append]
      · exact hreg
      · exact fun j _ _ => congrFun hstk j
  | cons v acc' ih =>
      intro L T0 B g X hg hX0 hXO
      have hX0' : X 0 = v.enc ++ (encs acc' ++ Work.Layout.gMark :: T0) := by
        rw [hX0, Work.Kernel.encs_cons, List.append_assoc]
      obtain ⟨s₁, n₁, he₁, hn₁, h0₁, hO₁, hS1₁, hS2₁, hreg₁, hfr₁⟩ :=
        foldStep_cont (main := main) (v := v) (A := encs acc' ++ Work.Layout.gMark :: T0)
          (L := L) (B := Work.Layout.gMark :: B) (g := g) (X := X) hX0' hXO
      obtain ⟨s₂, C₂, hrun₂, hC₂, h0₂, hO₂, hreg₂, hfr₂⟩ :=
        ih (v :: L) T0 B s₁.reg s₁.stk hreg₁ h0₁ hO₁
      refine ⟨s₂, n₁ + C₂ + 1,
        Work.Layout.loopRuns.succ' hg he₁ hrun₂ (by omega), ?_, h0₂, ?_, hreg₂, ?_⟩
      · have hv := Work.Layout.one_le_vsz v
        have h1 := hn₁; have h2 := hC₂
        simp only [List.map_cons, List.sum_cons] at h1 h2 ⊢
        omega
      · rw [hO₂]
        simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
      · intro j hj0 hjO
        rw [hfr₂ j hj0 hjO, hfr₁ j hj0 hjO]

/-! ## The target -/

theorem foldLoopEv (main : HvdH.Cmd) :
    ∀ (acc : List HvdH.Val) (L : List HvdH.Val) (T0 B : List HvdH.Glyph)
      (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph),
      g Work.SynFFT.lvF = HvdH.Glyph.cons →
      X 0 = HvdH.encs acc ++ Work.Layout.gMark :: T0 →
      X Work.SynFFT.lvOut = (HvdH.ofList L).enc ++ Work.Layout.gMark :: B →
      ∃ s' n, Work.Layout.Ev main Work.SynFFT.foldLoop ⟨g, X⟩ s' n ∧
        n ≤ 40 * ((acc.map (fun v => HvdH.vsz v + 1)).sum + 1) + 40 ∧
        s'.stk 0 = Work.Layout.gMark :: T0 ∧
        s'.stk Work.SynFFT.lvOut = (HvdH.ofList (acc.reverse ++ L)).enc ++ Work.Layout.gMark :: B ∧
        s'.reg Work.SynFFT.lvF = HvdH.Glyph.eos ∧
        (∀ j, j ≠ 0 → j ≠ Work.SynFFT.lvOut → s'.stk j = X j) := by
  intro acc L T0 B g X hg hX0 hXO
  have hset : Work.Layout.Ev main (.set lvF Glyph.cons) ⟨g, X⟩
      ⟨Function.update g lvF Glyph.cons, X⟩ 1 :=
    Work.Layout.ev_set' main lvF Glyph.cons g X
  obtain ⟨s', C, hrun, hC, h0, hO, hreg, hfr⟩ :=
    foldLoopRun main acc L T0 B (Function.update g lvF Glyph.cons) X (by simp) hX0 hXO
  have hloop : Work.Layout.Ev main (.loop lvF Glyph.cons foldStep_xmrgLvDefs)
      ⟨Function.update g lvF Glyph.cons, X⟩ s' (C + 1) :=
    Work.Layout.loopRuns.eval hrun (by rw [hreg]; decide)
  have hmain : Work.Layout.Ev main foldLoop ⟨g, X⟩ s' (1 + (C + 1)) :=
    Work.Layout.Ev.seq hset hloop
  exact ⟨s', _, hmain, by omega, h0, hO, hreg, hfr⟩

end Work.SynFFT
