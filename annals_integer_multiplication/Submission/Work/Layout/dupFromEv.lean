import Mathlib
import Submission.Work.Layout.ReplicateDefs

set_option linter.unusedSimpArgs false

namespace Work.Layout

open HvdH

/-- The stacks `drain2` touches: the source and the two destinations. -/
theorem cmdTouches_drain2 (c b1 b2 : Stk) : cmdTouches (drain2 c b1 b2) = {c, b1, b2} := by
  simp only [drain2, drain2Body, seqs, cmdTouches]
  ext k
  simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]
  tauto

/-- Push the content of register `rA` on both `b1` and `b2`. -/
theorem pushBoth_ev {main : Cmd} {b1 b2 : Stk} (hb : b1 ≠ b2) (s : State) :
    ∃ s' n, Ev main (seqs [Cmd.push b1 rA, Cmd.push b2 rA]) s s' n ∧ n ≤ 2 ∧
      s'.stk b1 = s.reg rA :: s.stk b1 ∧ s'.stk b2 = s.reg rA :: s.stk b2 ∧
      (∀ k, k ≠ b1 → k ≠ b2 → s'.stk k = s.stk k) ∧ s'.reg = s.reg := by
  refine ⟨⟨s.reg, Function.update (Function.update s.stk b1 (s.reg rA :: s.stk b1)) b2
      (s.reg rA :: Function.update s.stk b1 (s.reg rA :: s.stk b1) b2)⟩, 2, ?_, by omega,
    ?_, ?_, ?_, rfl⟩
  · simp only [seqs]
    exact Ev.seq (ev_push main b1 rA s) (ev_push main b2 rA _)
  · simp [Function.update_of_ne hb, Function.update_of_ne (Ne.symm hb)]
  · simp [Function.update_of_ne hb, Function.update_of_ne (Ne.symm hb)]
  · intro k hk1 hk2
    simp only [Function.update_of_ne hk2, Function.update_of_ne hk1]

/-- `drain2Body` with the boundary marker on top: consume it and stop. -/
private theorem drain2Body_hit {main : Cmd} {c b1 b2 : Stk} {g : Reg → Glyph} {X : Stk → List Glyph}
    {C B1 B2 : List Glyph} (hc : X c = gMark :: C) (hb1 : X b1 = B1) (hb2 : X b2 = B2)
    (hb1c : b1 ≠ c) (hb2c : b2 ≠ c) :
    ∃ s' n, Ev main (drain2Body c b1 b2) ⟨g, X⟩ s' n ∧ n ≤ 3 ∧
      s'.stk c = C ∧ s'.stk b1 = B1 ∧ s'.stk b2 = B2 ∧ s'.reg rLoopG = Glyph.eos := by
  have h1 : Ev main (.pop c rA) ⟨g, X⟩
      ⟨Function.update g rA ((X c).headD Glyph.eos), Function.update X c (X c).tail⟩ 1 :=
    ev_pop' main c rA g X
  have h2 : Ev main (.ite rA gMark (.set rLoopG Glyph.eos)
        (seqs [Cmd.push b1 rA, Cmd.push b2 rA]))
      ⟨Function.update g rA ((X c).headD Glyph.eos), Function.update X c (X c).tail⟩
      ⟨Function.update (Function.update g rA ((X c).headD Glyph.eos)) rLoopG Glyph.eos,
        Function.update X c (X c).tail⟩ 2 :=
    Ev.iteT (by simp [hc]) (ev_set' main rLoopG Glyph.eos _ _)
  have hbody : Ev main (drain2Body c b1 b2) ⟨g, X⟩
      ⟨Function.update (Function.update g rA ((X c).headD Glyph.eos)) rLoopG Glyph.eos,
        Function.update X c (X c).tail⟩ 3 := by
    unfold drain2Body
    simp only [seqs]
    exact Ev.seq' h1 h2 (by omega)
  refine ⟨_, 3, hbody, by omega, ?_, ?_, ?_, ?_⟩
  · simp [hc]
  · simp [hb1, Function.update_of_ne hb1c]
  · simp [hb2, Function.update_of_ne hb2c]
  · simp

/-- `drain2Body` on a non-marker glyph: move it to both destinations and continue. -/
private theorem drain2Body_miss {main : Cmd} {c b1 b2 : Stk} (hb1c : b1 ≠ c) (hb2c : b2 ≠ c)
    (hb1b2 : b1 ≠ b2) {g : Reg → Glyph} {X : Stk → List Glyph} {h : Glyph}
    {G C B1 B2 : List Glyph} (hh : h ≠ gMark) (hc : X c = h :: G ++ gMark :: C)
    (hb1 : X b1 = B1) (hb2 : X b2 = B2) (hreg : g rLoopG = Glyph.cons) :
    ∃ s' n, Ev main (drain2Body c b1 b2) ⟨g, X⟩ s' n ∧ n ≤ 4 ∧
      s'.stk c = G ++ gMark :: C ∧ s'.stk b1 = h :: B1 ∧ s'.stk b2 = h :: B2 ∧
      s'.reg rLoopG = Glyph.cons := by
  have h1 : Ev main (.pop c rA) ⟨g, X⟩
      ⟨Function.update g rA ((X c).headD Glyph.eos), Function.update X c (X c).tail⟩ 1 :=
    ev_pop' main c rA g X
  obtain ⟨s₂, n₂, h2, hn₂, hs₂b1, hs₂b2, hs₂o, hs₂r⟩ :=
    pushBoth_ev (main := main) (b1 := b1) (b2 := b2) hb1b2
      (⟨Function.update g rA ((X c).headD Glyph.eos), Function.update X c (X c).tail⟩ : State)
  have hite : Ev main (.ite rA gMark (.set rLoopG Glyph.eos)
        (seqs [Cmd.push b1 rA, Cmd.push b2 rA]))
      ⟨Function.update g rA ((X c).headD Glyph.eos), Function.update X c (X c).tail⟩ s₂ 3 :=
    Ev.iteF (by simp [hc, hh]) (h2.mono (show n₂ ≤ 2 by omega))
  have hbody : Ev main (drain2Body c b1 b2) ⟨g, X⟩ s₂ 4 := by
    unfold drain2Body
    simp only [seqs]
    exact Ev.seq' h1 hite (by omega)
  refine ⟨s₂, _, hbody, by omega, ?_, ?_, ?_, ?_⟩
  · rw [hs₂o c (Ne.symm hb1c) (Ne.symm hb2c)]
    simp [hc]
  · rw [hs₂b1]
    simp [hc, hb1, Function.update_of_ne hb1c]
  · rw [hs₂b2]
    simp [hc, hb2, Function.update_of_ne hb2c]
  · rw [hs₂r]
    simp only [Function.update_of_ne (by decide : rLoopG ≠ rA)]
    exact hreg

/-- The `drain2` loop: consume `G` then the boundary marker, pushing `G.reverse` on both
destination stacks. -/
theorem drain2_loop {main : Cmd} {c b1 b2 : Stk} (hb1c : b1 ≠ c) (hb2c : b2 ≠ c)
    (hb1b2 : b1 ≠ b2) :
    ∀ (G : List Glyph) (C B1 B2 : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph),
      gMark ∉ G → g rLoopG = Glyph.cons → X c = G ++ gMark :: C → X b1 = B1 → X b2 = B2 →
      ∃ s', loopRuns main rLoopG Glyph.cons (drain2Body c b1 b2) (G.length + 1) ⟨g, X⟩ s'
          (5 * (G.length + 1)) ∧
        s'.stk c = C ∧ s'.stk b1 = G.reverse ++ B1 ∧ s'.stk b2 = G.reverse ++ B2 ∧
        s'.reg rLoopG = Glyph.eos := by
  intro G
  induction G with
  | nil =>
      intro C B1 B2 g X _ hreg hc hb1 hb2
      obtain ⟨s', n, hev, hn, hsc, hsb1, hsb2, hsr⟩ :=
        drain2Body_hit (main := main) (c := c) (b1 := b1) (b2 := b2) (g := g) (X := X)
          (C := C) (B1 := B1) (B2 := B2) hc hb1 hb2 hb1c hb2c
      refine ⟨s', loopRuns.one hreg (hev.mono (show n ≤ 4 by omega)), ?_, ?_, ?_, hsr⟩
      · simpa using hsc
      · simpa using hsb1
      · simpa using hsb2
  | cons h G' ih =>
      intro C B1 B2 g X hmem hreg hc hb1 hb2
      have hh : h ≠ gMark := fun hh => hmem (hh ▸ List.mem_cons_self ..)
      have hmem' : gMark ∉ G' := fun hx => hmem (List.mem_cons_of_mem h hx)
      obtain ⟨s₁, n₁, hev₁, hn₁, hc₁, hb1₁, hb2₁, hr₁⟩ :=
        drain2Body_miss (main := main) (c := c) (b1 := b1) (b2 := b2) (g := g) (X := X)
          (h := h) (G := G') (C := C) (B1 := B1) (B2 := B2) hb1c hb2c hb1b2 hh hc hb1 hb2 hreg
      obtain ⟨s₂, hrun₂, hc₂, hb1₂, hb2₂, hr₂⟩ :=
        ih C (h :: B1) (h :: B2) s₁.reg s₁.stk hmem' hr₁ hc₁ hb1₁ hb2₁
      have hcat := loopRuns.concat (G'.length + 1)
        (loopRuns.one hreg (hev₁.mono (show n₁ ≤ 4 by omega))) hrun₂
      refine ⟨s₂, ?_, hc₂, ?_, ?_, hr₂⟩
      · have hk1 : 1 ≤ (h :: G').length + 1 := by simp only [List.length_cons]; omega
        have hcost : 5 + 5 * (G'.length + 1) ≤ 5 * ((h :: G').length + 1) := by
          simp only [List.length_cons]; omega
        exact loopRuns.mono hk1
          (loopRuns.cast (by simp only [List.length_cons]; omega) hcat) hcost
      · rw [hb1₂]; simp
      · rw [hb2₂]; simp

/-- `drain2 c b1 b2` as a whole: the glyph list `G` sitting above the boundary marker `gMark` of
stack `c` is popped and pushed (reversed, hence in the original order) on both `b1` and `b2`;
the marker is consumed, so stack `c` is left holding `C` (what was below the marker). -/
theorem drain2_ev {main : Cmd} {c b1 b2 : Stk} (hb1c : b1 ≠ c) (hb2c : b2 ≠ c)
    (hb1b2 : b1 ≠ b2) {G C B1 B2 : List Glyph} {g : Reg → Glyph} {X : Stk → List Glyph}
    (hgM : gMark ∉ G) (hc : X c = G ++ gMark :: C) (hb1 : X b1 = B1) (hb2 : X b2 = B2) :
    ∃ s' n, Ev main (drain2 c b1 b2) ⟨g, X⟩ s' n ∧ n ≤ 5 * (G.length + 1) + 2 ∧
      s'.stk c = C ∧ s'.stk b1 = G.reverse ++ B1 ∧ s'.stk b2 = G.reverse ++ B2 ∧
      (∀ k, k ≠ c → k ≠ b1 → k ≠ b2 → s'.stk k = X k) := by
  have hset : Ev main (.set rLoopG Glyph.cons) ⟨g, X⟩
      ⟨Function.update g rLoopG Glyph.cons, X⟩ 1 := ev_set' main rLoopG Glyph.cons g X
  obtain ⟨s₁, hrun, hc₁, hb1₁, hb2₁, hr₁⟩ :=
    drain2_loop (main := main) (c := c) (b1 := b1) (b2 := b2) hb1c hb2c hb1b2 G C B1 B2
      (Function.update g rLoopG Glyph.cons) X hgM (by simp) hc hb1 hb2
  have hloop : Ev main (.loop rLoopG Glyph.cons (drain2Body c b1 b2))
      ⟨Function.update g rLoopG Glyph.cons, X⟩ s₁ (5 * (G.length + 1) + 1) :=
    loopRuns.eval hrun (by rw [hr₁]; decide)
  have hmain : Ev main (drain2 c b1 b2) ⟨g, X⟩ s₁ (5 * (G.length + 1) + 2) := by
    unfold drain2
    simp only [seqs]
    exact Ev.seq' hset hloop (by omega)
  refine ⟨s₁, _, hmain, by omega, hc₁, hb1₁, hb2₁, ?_⟩
  intro k hkc hkb1 hkb2
  have hfr : s₁.stk k = (⟨g, X⟩ : State).stk k :=
    Ev.frame hmain (S := {c, b1, b2}) (by rw [cmdTouches_drain2]) (by simp [hkc, hkb1, hkb2])
  simpa using hfr

/-- Work in `Submission/Work/Layout/dupFromEv.lean`.

`Work.Layout.dupFrom a` copies the top value of stack `a` onto the top of stack 0, leaving stack `a`
unchanged (and every stack outside `{0, a}` untouched).  Definition (in
`Submission/Work/Layout/ReplicateDefs.lean`):
`dupFrom a = seqs [mvA a 5 6, drain2 5 0 a]`, where `drain2 c b1 b2` is the loop that pops the glyphs
above the boundary marker `gMark` of stack `c` and pushes each of them on `b1` *and* on `b2`
(`seqs [Cmd.set rLoopG Glyph.cons, Cmd.loop rLoopG Glyph.cons (drain2Body c b1 b2)]`).
Route: `mvA_ev` writes `v.enc.reverse` above the marker `gMark` on stack 5, then the `drain2` loop
pushes the reversed list on stack 0 and on stack `a`, so both get `v.enc` back in the original order.
Ingredients available: `mvA_ev`, `mvB_ev`, `gMark_not_mem_enc_rev`, `Ev`, `loopRuns`, `loopRuns.one`,
`loopRuns.concat`, `loopRuns.eval` (all in `Submission/Work/Layout/Move.lean`); the loop fact for
`drain2` can be proved in this file following the pattern of `mvB_loop` (induction on the glyph list
`G`, with one-step facts for the marker case `mvBBody_hit` and the non-marker case `mvBBody_miss`). -/
theorem dupFromEv {main : HvdH.Cmd} {a : HvdH.Stk} (ha0 : a ≠ 0) (ha5 : a ≠ 5) (ha6 : a ≠ 6) :
    ∀ (v : HvdH.Val) (A B : List HvdH.Glyph) (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph),
      X a = v.enc ++ A → X 0 = B →
      ∃ s' n, Work.Layout.Ev main (Work.Layout.dupFrom a) ⟨g, X⟩ s' n ∧ n ≤ 16 * (HvdH.vsz v + 1) ∧
        s'.stk 0 = v.enc ++ B ∧ s'.stk a = v.enc ++ A ∧
        (∀ k : HvdH.Stk, k ≠ 0 → k ≠ a → s'.stk k = X k) := by
  intro v A B g X ha hb
  obtain ⟨s₁, n₁, h1, hn₁, ha₁, h5₁, h6₁, hf₁⟩ :=
    mvA_ev (main := main) (a := a) (c := 5) (d := 6) ha5 ha6
      (show (5 : Stk) ≠ 6 from by decide) v A (X 5) (X 6) g X ha rfl rfl
  have hb₁ : s₁.stk 0 = B := by
    rw [hf₁ 0 (Ne.symm ha0) (by decide) (by decide), hb]
  obtain ⟨s₂, n₂, h2, hn₂, h5₂, h0₂, ha₂, hf₂⟩ :=
    drain2_ev (main := main) (c := 5) (b1 := 0) (b2 := a) (G := v.enc.reverse)
      (C := X 5) (B1 := B) (B2 := A) (show (0 : Stk) ≠ 5 from by decide) ha5 (Ne.symm ha0)
      (gMark_not_mem_enc_rev v) h5₁ hb₁ ha₁
  have hn₂' : n₂ ≤ 5 * (vsz v + 1) + 2 := by
    have h := hn₂
    simp only [List.length_reverse] at h
    simpa [vsz] using h
  refine ⟨s₂, n₁ + n₂, ?_, ?_, ?_, ?_, ?_⟩
  · unfold dupFrom
    simp only [seqs]
    exact Ev.seq h1 h2
  · have hv := one_le_vsz v
    omega
  · rw [h0₂, List.reverse_reverse]
  · rw [ha₂, List.reverse_reverse]
  · intro k hk0 hka
    by_cases hk5 : k = 5
    · rw [hk5]; exact h5₂
    · by_cases hk6 : k = 6
      · rw [hk6, hf₂ 6 (by decide) (by decide) (fun h => ha6 h.symm), h6₁]
      · rw [hf₂ k hk5 hk0 hka, hf₁ k hka hk5 hk6]

end Work.Layout
