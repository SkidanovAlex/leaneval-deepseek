import Mathlib
import Submission.Work.Layout.ReplicateDefs
import Submission.Work.Layout.mvVal_ev_full
import Submission.Work.Kernel.dropValue
import Submission.Work.Layout.pushListEv
import Submission.Work.Layout.dupFromEv
import Submission.Work.Layout.repBodyEv

/-!
# Layout area: `LayoutLib.replicate`

`int k :: v :: rest ↦ ofList (replicate k v) :: rest` in cost `O((k+1) * (vsz v + 1) + isz k)`.

The program is assembled from

* `Work.Layout.pushList` (`Submission/Work/Layout/pushListEv.lean`) — push the constants
  `int 1`, `int 0` in front of `int k :: v :: rest`;
* `IntLib.chunk` with `x = 0`, `b = 1` — turn `int 0 :: int 1 :: int k` into the `k`-element list
  `intList (replicate k 0)` of zeros, which serves as a *unary counter*;
* `Work.Layout.mvVal` — move the counter to stack 1 and the source `v` to stack 3;
* the main loop `Work.Layout.repBody` (`Submission/Work/Layout/repBodyEv.lean`,
  `Work.Layout.repLoop`): one iteration consumes one `.int 0` of the counter (three glyphs
  `cons`,`pos`,`iend`), copies `v` from stack 3 onto stack 0 (`Work.Layout.dupFrom`,
  `Submission/Work/Layout/dupFromEv.lean`) and prefixes a `cons` glyph, so that the accumulator on
  stack 0 becomes `.cons v acc`;
* finally the counter's terminating `nil` is popped, `v` is moved back on top of the accumulator and
  dropped with the Kernel word `Work.Kernel.dropValue`.

The `(k+1) * (vsz v + 1)` term also covers `k = 0`, where no iteration runs but `v` must still be
moved out of the way and dropped.  No value is ever read "from below": the counter is scanned only
through its own glyphs, and every scratch stack is restored.
-/

set_option autoImplicit false

namespace Work.Layout

open HvdH

/-- **`LayoutLib.replicate`** (v2 cost): `int k :: v :: rest ↦ ofList (replicate k v) :: rest`.  Route:
`IntLib.chunk` with `x = 0, b = 1` gives `intList (replicate k 0)` in cost `O(k + isz k)`, then replace
each `.int 0` by a copy of `v` (a raw copy loop, since `hI` has no `dup`).  The `(k+1)*(vsz v+1)` term
also covers `k = 0`, where `v` must still be removed from the stack. -/
theorem replicateWord (hI : HvdH.IntLib) : ∃ (p : Cmd) (K : ℕ), ∀ (main : Cmd) (k : ℕ) (v : Val),
    WordR main p
    (fun vs => ∃ rest, vs = .int k :: v :: rest)
    (fun vs out => ∃ rest, vs = .int k :: v :: rest ∧ out = ofList (List.replicate k v) :: rest)
    (fun _ => K * ((k + 1) * (vsz v + 1) + isz k + 1)) := by
  obtain ⟨chunkP, Kc, hchunk⟩ := hI.chunk
  obtain ⟨dropP, Kd, hdrop⟩ := Work.Kernel.dropValue
  refine ⟨seqs [pushList (Val.enc (.int 1)), pushList (Val.enc (.int 0)), chunkP,
      mvVal 0 1 4 5, mvVal 0 3 4 5, pushConst 0 Glyph.nil,
      Cmd.peek 1 rLoopG, Cmd.loop rLoopG Glyph.cons repBody,
      Cmd.pop 1 rB, mvVal 3 0 4 5, dropP], 100 * (Kc + Kd + 10), ?_⟩
  intro main k v vs hpre s R hs
  obtain ⟨rest, rfl⟩ := hpre
  have hs0 : s.stk 0 = (Val.int k).enc ++ (v.enc ++ (encs rest ++ R)) := by
    rw [hs]
    simp only [encs_cons'_rp, List.append_assoc]
  -- stage 1: push `int 1`
  obtain ⟨s₁, n₁, hev₁, hn₁, h1a, h1o⟩ := pushListEv (main := main) (Val.enc (.int 1)) s.reg s.stk
  have hs1 : s₁.stk 0 = (Val.int 1).enc ++ ((Val.int k).enc ++ (v.enc ++ (encs rest ++ R))) := by
    rw [h1a, hs0]
  -- stage 2: push `int 0`
  obtain ⟨s₂, n₂, hev₂, hn₂, h2a, h2o⟩ := pushListEv (main := main) (Val.enc (.int 0)) s₁.reg s₁.stk
  have hs2 : s₂.stk 0 = encs (.int 0 :: .int 1 :: .int k :: v :: rest) ++ R := by
    rw [h2a, hs1]
    simp only [encs_cons'_rp, List.append_assoc]
  -- stage 3: `chunk 0 1 k`
  have hch := hchunk main 0 1 k (by omega) (by positivity)
  obtain ⟨out₃, s₃, n₃, hpost₃, hev₃, hn₃, h3a, h3o⟩ :=
    hch (.int 0 :: .int 1 :: .int k :: v :: rest) ⟨v :: rest, rfl⟩ s₂ R hs2
  obtain ⟨rest₃, hvs₃, hout₃⟩ := hpost₃
  have hrest₃ : rest₃ = v :: rest := by
    have := congrArg (List.drop 3) hvs₃
    simpa using this.symm
  have hout₃' : out₃ = ofList (List.replicate k (.int 0)) :: v :: rest := by
    rw [hout₃, hrest₃, chunks_zero_one, intList_replicate]
  have h3a' : s₃.stk 0 =
      (ofList (List.replicate k (.int 0))).enc ++ (v.enc ++ (encs rest ++ R)) := by
    rw [h3a, hout₃']
    simp only [encs_cons'_rp, List.append_assoc]
  -- stage 4: move the counter to stack 1
  obtain ⟨s₄, n₄, hev₄, hn₄, h4a, h4b, h4c, h4d, h4o⟩ :=
    mvVal_ev_full (main := main) (a := 0) (b := 1) (c := 4) (d := 5)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s₃.reg) (X := s₃.stk) (v := ofList (List.replicate k (.int 0)))
      (A := v.enc ++ (encs rest ++ R)) (B := s₃.stk 1) h3a' rfl
  -- stage 5: move `v` to stack 3
  obtain ⟨s₅, n₅, hev₅, hn₅, h5a, h5b, h5c, h5d, h5o⟩ :=
    mvVal_ev_full (main := main) (a := 0) (b := 3) (c := 4) (d := 5)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s₄.reg) (X := s₄.stk) (v := v) (A := encs rest ++ R) (B := s₄.stk 3)
      h4a rfl
  -- stage 6: accumulator `nil` on stack 0
  obtain ⟨s₆, n₆, hev₆, hn₆, h6a, h6o, -, -⟩ :=
    pushConst_ev (main := main) (k := 0) (cst := Glyph.nil) (g := s₅.reg) (X := s₅.stk)
  have h6a' : s₆.stk 0 = (ofList ([] : List Val)).enc ++ (encs rest ++ R) := by
    rw [h6a, h5a]
    rfl
  -- stack 1 at that point is the counter
  have h6c : s₆.stk 1 = (ofList (List.replicate k (.int 0))).enc ++ s₃.stk 1 := by
    rw [h6o 1 (by decide), h5o 1 (by decide) (by decide) (by decide) (by decide), h4b]
  have h6v : s₆.stk 3 = v.enc ++ s₄.stk 3 := by
    rw [h6o 3 (by decide), h5b]
  -- stage 7: read the counter's top glyph into `rLoopG`
  obtain ⟨s₇, hs₇⟩ : ∃ s₇ : State,
      s₇ = ⟨Function.update s₆.reg rLoopG ((s₆.stk 1).headD Glyph.eos), s₆.stk⟩ := ⟨_, rfl⟩
  have hev₇ : Ev main (Cmd.peek 1 rLoopG) s₆ s₇ 1 := by
    rw [hs₇]; exact ev_peek' main 1 rLoopG s₆.reg s₆.stk
  have h7s : ∀ k' : Stk, s₇.stk k' = s₆.stk k' := by intro k'; rw [hs₇]
  have h7r : s₇.reg rLoopG = (s₆.stk 1).headD Glyph.eos := by simp [hs₇]
  -- stage 8: the loop
  have hstep := fun (v' : Val) (acc : Val) (L' : Val) (F S1 S3 : List Glyph)
      (g : Reg → Glyph) (X : Stk → List Glyph)
      (h0 : X 0 = acc.enc ++ F) (h1 : X 1 = (Val.cons (.int 0) L').enc ++ S1)
      (h3 : X 3 = v'.enc ++ S3) =>
    repBodyEv (main := main) (Cd := fun n => 16 * (n + 1))
      (fun v0 S3' B g0 X0 h3' h0' =>
        dupFromEv (main := main) (a := 3) (by decide) (by decide) (by decide) v0 S3' B g0 X0 h3' h0')
      v' acc L' F S1 S3 g X h0 h1 h3
  have h7counter : s₇.stk 1 = (ofList (List.replicate k (.int 0))).enc ++ s₃.stk 1 := by
    rw [h7s 1, h6c]
  have h7v : s₇.stk 3 = v.enc ++ s₄.stk 3 := by rw [h7s 3, h6v]
  have h7r' : s₇.reg rLoopG = (ofList (List.replicate k (.int 0))).enc.headD Glyph.eos := by
    rw [h7r, h6c]
    exact headD_append_of_ne _ _ (enc_ofList_rep_ne_nil k) _
  obtain ⟨s₈, hrun₈, h8a, h8b, h8c, h8r, h8o⟩ :=
    repLoop (main := main) (body := repBody) (Cd := fun n => 16 * (n + 1)) hstep
      k [] v (encs rest ++ R) (s₃.stk 1) (s₄.stk 3) s₇.reg s₇.stk
      (by rw [h7s 0]; exact h6a') h7counter h7v h7r'
  have hev₈ : Ev main (Cmd.loop rLoopG Glyph.cons repBody) s₇ s₈
      (k * (16 * (vsz v + 1) + 7) + 1) := by
    have hnil : s₈.reg rLoopG = Glyph.nil := by
      rw [h8r, headD_enc_ofList_rep_zero]
    refine loopRuns.eval (C := k * (16 * (vsz v + 1) + 7)) hrun₈ ?_
    rw [hnil]; decide
  -- stage 9: drop the counter's terminating `nil`
  obtain ⟨s₉, hs₉⟩ : ∃ s₉ : State,
      s₉ = ⟨Function.update s₈.reg rB ((s₈.stk 1).headD Glyph.eos),
        Function.update s₈.stk 1 (s₈.stk 1).tail⟩ := ⟨_, rfl⟩
  have hev₉ : Ev main (Cmd.pop 1 rB) s₈ s₉ 1 := by
    rw [hs₉]; exact ev_pop' main 1 rB s₈.reg s₈.stk
  have h9s : ∀ k' : Stk, k' ≠ 1 → s₉.stk k' = s₈.stk k' := by
    intro k' hk'
    simp only [hs₉]
    exact Function.update_of_ne hk' _ _
  have h9one : s₉.stk 1 = s₃.stk 1 := by
    simp only [hs₉, Function.update_self]
    rw [h8b, enc_ofList_rep_zero]
    rfl
  -- stage 10: `v` back on top of the accumulator
  have h8a' : s₈.stk 0 = (ofList (List.replicate k v)).enc ++ (encs rest ++ R) := by
    rw [h8a, List.append_nil]
  have h9a : s₉.stk 0 = (ofList (List.replicate k v)).enc ++ (encs rest ++ R) := by
    rw [h9s 0 (by decide), h8a']
  have h9v : s₉.stk 3 = v.enc ++ s₄.stk 3 := by rw [h9s 3 (by decide), h8c]
  obtain ⟨s₁₀, n₁₀, hev₁₀, hn₁₀, h10a, h10b, h10c, h10d, h10o⟩ :=
    mvVal_ev_full (main := main) (a := 3) (b := 0) (c := 4) (d := 5)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s₉.reg) (X := s₉.stk) (v := v) (A := s₄.stk 3) (B := s₉.stk 0)
      h9v rfl
  have h10b' : s₁₀.stk 0 = encs (v :: ofList (List.replicate k v) :: rest) ++ R := by
    rw [h10b, h9a]
    simp only [encs_cons'_rp, List.append_assoc]
  -- stage 11: drop `v`
  obtain ⟨out₁₁, s₁₁, n₁₁, hpost₁₁, hev₁₁, hn₁₁, h11a, h11o⟩ :=
    hdrop main (v :: ofList (List.replicate k v) :: rest) (by simp) s₁₀ R h10b'
  obtain ⟨v₁₁, rest₁₁, hvs₁₁, hout₁₁⟩ := hpost₁₁
  have hrest₁₁ : rest₁₁ = ofList (List.replicate k v) :: rest := by
    have := congrArg (List.drop 1) hvs₁₁
    simpa using this.symm
  have hout₁₁' : out₁₁ = ofList (List.replicate k v) :: rest := by rw [hout₁₁, hrest₁₁]
  -- total evaluation
  have htotal : Ev main (seqs [pushList (Val.enc (.int 1)), pushList (Val.enc (.int 0)), chunkP,
      mvVal 0 1 4 5, mvVal 0 3 4 5, pushConst 0 Glyph.nil,
      Cmd.peek 1 rLoopG, Cmd.loop rLoopG Glyph.cons repBody,
      Cmd.pop 1 rB, mvVal 3 0 4 5, dropP]) s s₁₁
      (n₁ + (n₂ + (n₃ + (n₄ + (n₅ + (n₆ + (1 +
        ((k * (16 * (vsz v + 1) + 7) + 1) + (1 + (n₁₀ + n₁₁)))))))))) := by
    refine Ev.seqs_cons hev₁ (Ev.seqs_cons hev₂ (Ev.seqs_cons ⟨_, hev₃, le_rfl⟩ (Ev.seqs_cons hev₄
      (Ev.seqs_cons hev₅ (Ev.seqs_cons hev₆ (Ev.seqs_cons hev₇ (Ev.seqs_cons hev₈
      (Ev.seqs_cons hev₉ (Ev.seqs_cons hev₁₀ ⟨_, hev₁₁, le_rfl⟩)))))))))
  -- cost bound
  have hn₃' : n₃ ≤ Kc * (2 * k + isz k + 5) := by
    have h := hn₃
    have hle : isz (↑(0:ℕ) : ℤ) + k * (1 + 1) + isz (↑(1:ℕ) : ℤ) + isz (↑k : ℤ)
        ≤ 2 * k + isz (↑k : ℤ) + 5 := by
      have h0 : isz (↑(0:ℕ) : ℤ) = 2 := by simp [isz, Nat.size_zero]
      have h1 : isz (↑(1:ℕ) : ℤ) = 3 := by simp [isz]
      rw [h0, h1]; omega
    exact le_trans h (Nat.mul_le_mul_left Kc hle)
  have hn₁' : n₁ ≤ 7 := by
    have h := hn₁
    rw [enc_int_one_length] at h
    omega
  have hn₂' : n₂ ≤ 5 := by
    have h := hn₂
    rw [enc_int_zero_length] at h
    omega
  have hn₄' : n₄ ≤ 48 * k + 32 := by
    have := hn₄
    rw [vsz_ofList_rep] at this
    omega
  have hn₁₁' : n₁₁ ≤ Kd * (vsz v + 1) := by
    have := hn₁₁
    simp only [List.headD_cons] at this
    exact this
  have hflat : n₁ + (n₂ + (n₃ + (n₄ + (n₅ + (n₆ + (1 +
        ((k * (16 * (vsz v + 1) + 7) + 1) + (1 + (n₁₀ + n₁₁)))))))))
      ≤ 7 + 5 + Kc * (2 * k + isz k + 5) + (48 * k + 32) + 16 * (vsz v + 1) + 2 + 1 +
        (k * (16 * (vsz v + 1) + 7) + 1) + 1 + 16 * (vsz v + 1) + Kd * (vsz v + 1) := by
    have hn₅' : n₅ ≤ 16 * (vsz v + 1) := hn₅
    have hn₁₀' : n₁₀ ≤ 16 * (vsz v + 1) := hn₁₀
    omega
  have hV : 2 ≤ vsz v + 1 := by have := one_le_vsz v; omega
  have hcost : (n₁ + (n₂ + (n₃ + (n₄ + (n₅ + (n₆ + (1 +
        ((k * (16 * (vsz v + 1) + 7) + 1) + (1 + (n₁₀ + n₁₁))))))))))
      ≤ 100 * (Kc + Kd + 10) * ((k + 1) * (vsz v + 1) + isz k + 1) :=
    le_trans hflat (replicateCostBound Kc Kd k (vsz v + 1) (isz k) hV)
  -- frame
  have hframe : ∀ k' : Stk, k' ≠ 0 → s₁₁.stk k' = s.stk k' := by
    intro k' hk'
    have e₁ : s₁.stk k' = s.stk k' := h1o k' hk'
    have e₂ : s₂.stk k' = s₁.stk k' := h2o k' hk'
    have e₃ : s₃.stk k' = s₂.stk k' := h3o k' hk'
    have e₆ : s₆.stk k' = s₅.stk k' := h6o k' hk'
    have e₁₁ : s₁₁.stk k' = s₁₀.stk k' := h11o k' hk'
    by_cases hk1 : k' = 1
    · subst hk1
      rw [e₁₁, h10o 1 (by decide) (by decide) (by decide) (by decide), h9one, e₃, e₂, e₁]
    by_cases hk3 : k' = 3
    · subst hk3
      rw [e₁₁, h10a, h4o 3 (by decide) (by decide) (by decide) (by decide), e₃, e₂, e₁]
    by_cases hk4 : k' = 4
    · subst hk4
      rw [e₁₁, h10c, h9s 4 (by decide), h8o 4 (by decide) (by decide) (by decide),
        h7s 4, e₆, h5c, h4c, e₃, e₂, e₁]
    by_cases hk5 : k' = 5
    · subst hk5
      rw [e₁₁, h10d, h9s 5 (by decide), h8o 5 (by decide) (by decide) (by decide),
        h7s 5, e₆, h5d, h4d, e₃, e₂, e₁]
    rw [e₁₁, h10o k' hk3 hk' hk4 hk5, h9s k' hk1,
      h8o k' hk' hk1 hk3, h7s k', e₆,
      h5o k' hk' hk3 hk4 hk5, h4o k' hk' hk1 hk4 hk5, e₃, e₂, e₁]
  obtain ⟨ntot, hevTot, hleTot⟩ := htotal
  refine ⟨ofList (List.replicate k v) :: rest, s₁₁, ntot,
    ⟨rest, rfl, rfl⟩, hevTot, le_trans hleTot hcost, ?_, hframe⟩
  rw [h11a, hout₁₁']
