import Mathlib
import Submission.Work.Layout.Take.Defs

/-!
# take/drop: the fixed-frame phases

`initProg` pushes the frame marker on the five scratch stacks, and `drainProg b` discards
everything on stack `b` down to and including that frame marker.

These two are worked out in detail; they are the template for the loop phases
(the `Eval` of each program is given with an *explicit* result state, obtained by chaining
`Ev.seq'` of `ev_pop'`, `ev_peek'`, `ev_push'`, `ev_set'`, and the loop lemmas `loopRuns.*`
of `Submission/Work/Layout/Base.lean`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.Layout

open HvdH

/-! ## Pushing the frame markers -/

theorem markPush_ev (main : Cmd) (b : Stk) (g : Reg → Glyph) (X : Stk → List Glyph) :
    Ev main (markPush b) ⟨g, X⟩
      ⟨Function.update g rE_x gMark, Function.update X b (gMark :: X b)⟩ 2 := by
  have h1 : Ev main (.set rE_x gMark) ⟨g, X⟩ ⟨Function.update g rE_x gMark, X⟩ 1 :=
    ev_set' main rE_x gMark g X
  have h2 : Ev main (.push b rE_x) ⟨Function.update g rE_x gMark, X⟩
      ⟨Function.update g rE_x gMark, Function.update X b (gMark :: X b)⟩ 1 := by
    have h := ev_push' main b rE_x (Function.update g rE_x gMark) X
    convert h using 2
    simp
  unfold markPush
  simp only [seqs]
  exact Ev.seq' h1 h2 (by omega)

/-- pushing the frame marker on a list of stacks, in order -/
theorem markPushList_ev (main : Cmd) :
    ∀ (L : List Stk), L.Nodup → ∀ (g : Reg → Glyph) (X : Stk → List Glyph),
      ∃ s' n, Ev main (seqs (L.map markPush)) ⟨g, X⟩ s' n ∧ n ≤ 2 * L.length + 1 ∧
        (∀ b ∈ L, s'.stk b = gMark :: X b) ∧ (∀ b, b ∉ L → s'.stk b = X b) := by
  intro L
  induction L with
  | nil =>
      intro _ g X
      exact ⟨_, 1, Ev.seqs_nil, by simp, by intro b hb; simp at hb, by intro b _; rfl⟩
  | cons b L ih =>
      intro hL g X
      have hbL : b ∉ L := (List.nodup_cons.mp hL).1
      have hL' : L.Nodup := (List.nodup_cons.mp hL).2
      obtain ⟨s₁, n₁, he₁, hn₁, hb₁, ho₁⟩ : ∃ s' n, Ev main (markPush b) ⟨g, X⟩ s' n ∧ n ≤ 2 ∧
          s'.stk b = gMark :: X b ∧ (∀ k, k ≠ b → s'.stk k = X k) :=
        ⟨_, 2, markPush_ev main b g X, le_rfl, by simp, by intro k hk; simp [hk]⟩
      obtain ⟨s₂, n₂, he₂, hn₂, hb₂, ho₂⟩ := ih hL' s₁.reg s₁.stk
      refine ⟨_, n₁ + n₂, Ev.seqs_cons he₁ he₂, ?_, ?_, ?_⟩
      · simp only [List.length_map, List.length_cons]; omega
      · intro c hc
        rcases List.mem_cons.mp hc with hcb | hc
        · rw [hcb, ho₂ b hbL]; exact hb₁
        · have hcb : c ≠ b := fun h => hbL (h ▸ hc)
          rw [hb₂ c hc, ho₁ c hcb]
      · intro c hc
        rw [ho₂ c (fun hcL => hc (List.mem_cons_of_mem b hcL)),
          ho₁ c (fun hcb => hc (hcb ▸ List.mem_cons_self ..))]

theorem init_ev (main : Cmd) (g : Reg → Glyph) (X : Stk → List Glyph) :
    ∃ s' n, Ev main initProg ⟨g, X⟩ s' n ∧ n ≤ 11 ∧
      s'.stk sS = gMark :: X sS ∧ s'.stk sT_x = gMark :: X sT_x ∧
      s'.stk sD = gMark :: X sD ∧ s'.stk sDp = gMark :: X sDp ∧
      s'.stk sBit = gMark :: X sBit ∧
      (∀ k, k ≠ sS → k ≠ sT_x → k ≠ sD → k ≠ sDp → k ≠ sBit → s'.stk k = X k) := by
  obtain ⟨s', n, he, hn, hmem, hout⟩ :=
    markPushList_ev main [sS, sT_x, sD, sDp, sBit] (by decide) g X
  have hn' : n ≤ 11 := by simpa using hn
  refine ⟨s', n, ?_, hn', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact he
  · exact hmem sS (by simp)
  · exact hmem sT_x (by simp)
  · exact hmem sD (by simp)
  · exact hmem sDp (by simp)
  · exact hmem sBit (by simp)
  · intro k h1 h2 h3 h4 h5
    exact hout k (by simp [h1, h2, h3, h4, h5])

theorem gMark_notMem_encs (vs : List Val) : gMark ∉ encs vs := by
  intro h
  obtain ⟨l, hl, hml⟩ := List.mem_flatten.mp h
  obtain ⟨v, -, rfl⟩ := List.mem_map.mp hl
  exact gMark_not_mem_enc v hml

theorem gMark_notMem_replicate_gU (n : ℕ) : gMark ∉ List.replicate n gU := by
  intro h
  exact gMark_ne_gU (List.eq_of_mem_replicate h)

/-! ## Draining a stack down to its frame marker -/

/-- one iteration of the drain loop: it pops one glyph and stops exactly when the popped glyph is
the frame marker -/
theorem drainBody_ev (main : Cmd) {b : Stk} (g : Reg → Glyph) (X : Stk → List Glyph) :
    Ev main (drainBody_x b) ⟨g, X⟩
      ⟨Function.update (Function.update g rE_x ((X b).headD Glyph.eos)) rG
          (if (X b).headD Glyph.eos = gMark then Glyph.eos else gCont_x),
        Function.update X b (X b).tail⟩ 3 := by
  have h1 : Ev main (.pop b rE_x) ⟨g, X⟩
      ⟨Function.update g rE_x ((X b).headD Glyph.eos), Function.update X b (X b).tail⟩ 1 :=
    ev_pop' main b rE_x g X
  have h2 : Ev main (.ite rE_x gMark (.set rG Glyph.eos) (.set rG gCont_x))
      ⟨Function.update g rE_x ((X b).headD Glyph.eos), Function.update X b (X b).tail⟩
      ⟨Function.update (Function.update g rE_x ((X b).headD Glyph.eos)) rG
          (if (X b).headD Glyph.eos = gMark then Glyph.eos else gCont_x),
        Function.update X b (X b).tail⟩ 2 := by
    by_cases h : (X b).headD Glyph.eos = gMark
    · refine Ev.iteT h ?_
      rw [if_pos h]
      exact ev_set' main rG Glyph.eos _ _
    · refine Ev.iteF h ?_
      rw [if_neg h]
      exact ev_set' main rG gCont_x _ _
  unfold drainBody_x
  simp only [seqs]
  exact Ev.seq' h1 h2 (by omega)

/-- the drain loop: `G` is the content above the frame marker (it must not contain `gMark`) -/
theorem drainLoop (main : Cmd) {b : Stk} (G : List Glyph) :
    ∀ (B : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph), gMark ∉ G →
      X b = G ++ gMark :: B → g rG = gCont_x →
      ∃ s', loopRuns main rG gCont_x (drainBody_x b) (G.length + 1) ⟨g, X⟩ s' (4 * (G.length + 1)) ∧
        s'.stk b = B ∧ s'.reg rG = Glyph.eos ∧ (∀ k, k ≠ b → s'.stk k = X k) := by
  induction G with
  | nil =>
      intro B g X hG hX hg
      have hhead : (X b).headD Glyph.eos = gMark := by simp [hX]
      refine ⟨_, loopRuns.one hg (drainBody_ev main g X), ?_, ?_, ?_⟩
      · show Function.update X b (X b).tail b = B
        simp only [Function.update_self, hX, List.nil_append, List.tail_cons]
      · show Function.update (Function.update g rE_x ((X b).headD Glyph.eos)) rG
          (if (X b).headD Glyph.eos = gMark then Glyph.eos else gCont_x) rG = Glyph.eos
        rw [Function.update_self, if_pos hhead]
      · intro k hk
        show Function.update X b (X b).tail k = X k
        simp [hk]
  | cons hd tl ih =>
      intro B g X hG hX hg
      have hhd : hd ≠ gMark := fun h => hG (h ▸ List.mem_cons_self ..)
      have htl : gMark ∉ tl := fun h => hG (List.mem_cons_of_mem hd h)
      have hhead : (X b).headD Glyph.eos = hd := by simp [hX]
      have hreg : (⟨Function.update (Function.update g rE_x ((X b).headD Glyph.eos)) rG
            (if (X b).headD Glyph.eos = gMark then Glyph.eos else gCont_x),
          Function.update X b (X b).tail⟩ : State).reg rG = gCont_x := by
        show Function.update (Function.update g rE_x ((X b).headD Glyph.eos)) rG
          (if (X b).headD Glyph.eos = gMark then Glyph.eos else gCont_x) rG = gCont_x
        rw [Function.update_self, if_neg (by rw [hhead]; exact hhd)]
      have hX' : (⟨Function.update (Function.update g rE_x ((X b).headD Glyph.eos)) rG
            (if (X b).headD Glyph.eos = gMark then Glyph.eos else gCont_x),
          Function.update X b (X b).tail⟩ : State).stk b = tl ++ gMark :: B := by
        show Function.update X b (X b).tail b = tl ++ gMark :: B
        simp [hX]
      obtain ⟨s₂, hrun, hb₂, hr₂, ho₂⟩ := ih B _ _ htl hX' hreg
      refine ⟨s₂, loopRuns.succ' (C := 4 * ((hd :: tl).length + 1)) hg
        (drainBody_ev main g X) hrun (by simp; omega), hb₂, hr₂, ?_⟩
      intro k hk
      rw [ho₂ k hk]
      show Function.update X b (X b).tail k = X k
      simp [hk]

theorem drain_ev (main : Cmd) {b : Stk} {G B : List Glyph} {g : Reg → Glyph} {X : Stk → List Glyph}
    (hG : gMark ∉ G) (hX : X b = G ++ gMark :: B) :
    ∃ s' n, Ev main (drainProg b) ⟨g, X⟩ s' n ∧ n ≤ 4 * (G.length + 1) + 2 ∧
      s'.stk b = B ∧ (∀ k, k ≠ b → s'.stk k = X k) := by
  obtain ⟨s₁, hrun, hb₁, hr₁, ho₁⟩ :=
    drainLoop main G B (Function.update g rG gCont_x) X hG hX (Function.update_self rG gCont_x g)
  have hset : Ev main (.set rG gCont_x) ⟨g, X⟩ ⟨Function.update g rG gCont_x, X⟩ 1 :=
    ev_set' main rG gCont_x g X
  have hloop : Ev main (.loop rG gCont_x (drainBody_x b))
      ⟨Function.update g rG gCont_x, X⟩ s₁ (4 * (G.length + 1) + 1) :=
    (loopRuns.eval hrun (by rw [hr₁]; decide)).mono (by omega)
  refine ⟨s₁, 1 + (4 * (G.length + 1) + 1), ?_, by omega, hb₁, ?_⟩
  · unfold drainProg
    simp only [seqs]
    exact Ev.seq' hset hloop (by omega)
  · intro k hk
    rw [ho₁ k hk]

end Work.Layout
