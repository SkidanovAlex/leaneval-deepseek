import Mathlib
import Submission.Work.Layout.enumDefs
import Submission.Work.Layout.Move
import Submission.Work.Layout.mvVal_ev_full
import Submission.Work.IntLib.encodeNatBridge

/-!
# Layout area: the counter step `incDup` of `LayoutLib.enumerate`

`incDup addP` walks the top value `int i` of stack `0`: it copies it onto stack `4` (`dupVal`, the
copy program of `Submission/Work/Layout/enumDefs.lean`), moves the counter aside on stack `9`, pushes
`int 1`, brings the counter back on top of it and runs `addP` (`IntLib.add`).  At the end stack `0`
carries `int (i+1)` and stack `4` carries the label `int i` above its original content.

This file builds, bottom-up,

* `popRA_ev`, `pushBoth_ev_inc` — the two primitive steps of the copy program `dupB`;
* `dupBBody_hit`, `dupBBody_miss` — one iteration of the copy loop (the twin of
  `Work.Layout.mvBBody_hit`/`mvBBody_miss` of `Move.lean`);
* `dupB_loop`, `dupB_ev` — the whole copy program, cost `5 * (G.length + 1) + 2`;
* `dupVal_ev_full` — `dupVal` copies a value with a full frame, cost `16 * (vsz v + 1)`;
* `incDup_ev` — the counter step, cost `≤ (64 + Kadd) * (isz i + 4)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Layout

open HvdH

/-! ## Primitive steps -/

/-- `pop c rA`: pop the top glyph of `c` into register `rA`, exposing the tail on `c`.  Register
`rA` holds the popped glyph, all other registers and stacks are untouched. -/
theorem popRA_ev {main : Cmd} {c : Stk} {g : Reg → Glyph} {X : Stk → List Glyph} (v : Glyph)
    (C' : List Glyph) (hc : X c = v :: C') :
    ∃ s' n, Ev main (.pop c rA) ⟨g, X⟩ s' n ∧ n ≤ 1 ∧ s'.reg rA = v ∧
      (∀ r : Reg, r ≠ rA → s'.reg r = g r) ∧ s'.stk c = C' ∧
      (∀ k : Stk, k ≠ c → s'.stk k = X k) := by
  refine ⟨⟨Function.update g rA ((X c).headD Glyph.eos), Function.update X c (X c).tail⟩, 1,
    ev_pop' main c rA g X, le_rfl, ?_, ?_, ?_, ?_⟩
  · simp [hc]
  · intro r hr; simp [Function.update_of_ne hr]
  · simp [hc]
  · intro k hk; simp [Function.update_of_ne hk]

/-- push the glyph held in register `rA` onto both `a` and `b` (distinct stacks). -/
theorem pushBoth_ev_inc {main : Cmd} {a b : Stk} (hab : a ≠ b) {g : Reg → Glyph}
    {X : Stk → List Glyph} :
    ∃ s' n, Ev main (seqs [.push a rA, .push b rA]) ⟨g, X⟩ s' n ∧ n ≤ 2 ∧
      s'.stk a = g rA :: X a ∧ s'.stk b = g rA :: X b ∧ s'.reg = g ∧
      (∀ k : Stk, k ≠ a → k ≠ b → s'.stk k = X k) := by
  refine ⟨⟨g, Function.update (Function.update X a (g rA :: X a)) b
      (g rA :: Function.update X a (g rA :: X a) b)⟩, 2, ?_, le_rfl, ?_, ?_, rfl, ?_⟩
  · simp only [seqs]
    exact Ev.seq' (ev_push' main a rA g X)
      (ev_push' main b rA g (Function.update X a (g rA :: X a))) le_rfl
  · simp only [stk_mk]; rw [Function.update_of_ne hab]; simp
  · simp only [stk_mk]
    rw [Function.update_of_ne hab.symm, Function.update_self]
  · intro k hka hkb
    simp only [stk_mk]
    rw [Function.update_of_ne hkb, Function.update_of_ne hka]

/-! ## One iteration of the `dupB` loop -/

/-- an iteration of the `dupBBody` loop that pops the boundary marker: stop. -/
theorem dupBBody_hit {main : Cmd} {c a b : Stk} {g : Reg → Glyph} {X : Stk → List Glyph}
    {C A B : List Glyph} (hac : a ≠ c) (hbc : b ≠ c) (hc : X c = gMark :: C) (ha : X a = A)
    (hb : X b = B) :
    ∃ s' n, Ev main (dupBBody c a b) ⟨g, X⟩ s' n ∧ n ≤ 3 ∧
      s'.stk c = C ∧ s'.stk a = A ∧ s'.stk b = B ∧ s'.reg rLoopG = Glyph.eos := by
  obtain ⟨s₁, n₁, h₁, hn₁, hrA₁, -, hc₁, hf₁⟩ :=
    popRA_ev (main := main) (c := c) (g := g) (X := X) gMark C hc
  have hset : Ev main (.set rLoopG Glyph.eos) s₁
      ⟨Function.update s₁.reg rLoopG Glyph.eos, s₁.stk⟩ 1 :=
    ev_set' main rLoopG Glyph.eos s₁.reg s₁.stk
  have hite : Ev main (.ite rA gMark (.set rLoopG Glyph.eos) (seqs [.push a rA, .push b rA]))
      s₁ ⟨Function.update s₁.reg rLoopG Glyph.eos, s₁.stk⟩ 2 :=
    Ev.iteT hrA₁ hset
  have hbody : Ev main (dupBBody c a b) ⟨g, X⟩
      ⟨Function.update s₁.reg rLoopG Glyph.eos, s₁.stk⟩ (n₁ + 2) := h₁.seq hite
  refine ⟨⟨Function.update s₁.reg rLoopG Glyph.eos, s₁.stk⟩, n₁ + 2, hbody,
    by omega, ?_, ?_, ?_, ?_⟩
  · rw [hc₁]
  · rw [hf₁ a hac, ha]
  · rw [hf₁ b hbc, hb]
  · simp

/-- an iteration of the `dupBBody` loop on a non-marker glyph: move it to both `a` and `b`. -/
theorem dupBBody_miss {main : Cmd} {c a b : Stk} (hac : a ≠ c) (hbc : b ≠ c) (hab : a ≠ b)
    {g : Reg → Glyph} {X : Stk → List Glyph} {v : Glyph} {G C A B : List Glyph}
    (hv : v ≠ gMark) (hc : X c = v :: G ++ gMark :: C) (ha : X a = A) (hb : X b = B)
    (hreg : g rLoopG = Glyph.cons) :
    ∃ s' n, Ev main (dupBBody c a b) ⟨g, X⟩ s' n ∧ n ≤ 4 ∧
      s'.stk c = G ++ gMark :: C ∧ s'.stk a = v :: A ∧ s'.stk b = v :: B ∧
      s'.reg rLoopG = Glyph.cons := by
  obtain ⟨s₁, n₁, h₁, hn₁, hrA₁, hreg₁, hc₁, hf₁⟩ :=
    popRA_ev (main := main) (c := c) (g := g) (X := X) v (G ++ gMark :: C) hc
  obtain ⟨s₂, n₂, h₂, hn₂, ha₂, hb₂, hreg₂, hf₂⟩ :=
    pushBoth_ev_inc (main := main) (a := a) (b := b) hab (g := s₁.reg) (X := s₁.stk)
  have hrl₁ : s₁.reg rLoopG = Glyph.cons := by
    rw [hreg₁ rLoopG (by decide : rLoopG ≠ rA)]; exact hreg
  have hite : Ev main (.ite rA gMark (.set rLoopG Glyph.eos) (seqs [.push a rA, .push b rA]))
      s₁ s₂ (n₂ + 1) := Ev.iteF (by rw [hrA₁]; exact hv) h₂
  have hbody : Ev main (dupBBody c a b) ⟨g, X⟩ s₂ (n₁ + (n₂ + 1)) := h₁.seq hite
  refine ⟨s₂, n₁ + (n₂ + 1), hbody, by omega, ?_, ?_, ?_, ?_⟩
  · rw [hf₂ c hac.symm hbc.symm, hc₁]
  · rw [ha₂, hrA₁, hf₁ a hac, ha]
  · rw [hb₂, hrA₁, hf₁ b hbc, hb]
  · rw [hreg₂]; exact hrl₁

/-! ## The whole `dupB` loop -/

/-- The `dupB` loop: pop the glyphs of `G` from `c`, pushing each of them onto both `a` and `b`,
until the boundary marker is consumed.  Cost `5 * (G.length + 1)`: `4` per iteration plus one
loop test per iteration, the final test included. -/
theorem dupB_loop {main : Cmd} {c a b : Stk} (hac : a ≠ c) (hbc : b ≠ c) (hab : a ≠ b) :
    ∀ (G : List Glyph) (C A B : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph),
      gMark ∉ G → g rLoopG = Glyph.cons → X c = G ++ gMark :: C → X a = A → X b = B →
      ∃ s', loopRuns main rLoopG Glyph.cons (dupBBody c a b) (G.length + 1) ⟨g, X⟩ s'
          (5 * (G.length + 1)) ∧
        s'.stk c = C ∧ s'.stk a = G.reverse ++ A ∧ s'.stk b = G.reverse ++ B ∧
        s'.reg rLoopG = Glyph.eos := by
  intro G
  induction G with
  | nil =>
      intro C A B g X _ hreg hc ha hb
      obtain ⟨s', n, hev, hn, hsc, hsa, hsb, hsr⟩ :=
        dupBBody_hit (main := main) (c := c) (a := a) (b := b) (g := g) (X := X)
          (C := C) (A := A) (B := B) hac hbc hc ha hb
      refine ⟨s', loopRuns.one hreg (hev.mono (by omega : n ≤ 4)), ?_, ?_, ?_, hsr⟩
      · simpa using hsc
      · simpa using hsa
      · simpa using hsb
  | cons h G' ih =>
      intro C A B g X hmem hreg hc ha hb
      have hh : h ≠ gMark := fun hh => hmem (hh ▸ List.mem_cons_self ..)
      have hmem' : gMark ∉ G' := fun hx => hmem (List.mem_cons_of_mem h hx)
      obtain ⟨s₁, n₁, hev₁, hn₁, hc₁, ha₁, hb₁, hr₁⟩ :=
        dupBBody_miss (main := main) (c := c) (a := a) (b := b) (hac := hac) (hbc := hbc)
          (hab := hab) (g := g) (X := X) (v := h) (G := G') (C := C) (A := A) (B := B)
          hh hc ha hb hreg
      obtain ⟨s₂, hrun₂, hc₂, ha₂, hb₂, hr₂⟩ :=
        ih C (h :: A) (h :: B) s₁.reg s₁.stk hmem' hr₁ hc₁ ha₁ hb₁
      have hcat := loopRuns.concat (G'.length + 1)
        (loopRuns.one hreg (hev₁.mono hn₁)) hrun₂
      refine ⟨s₂, loopRuns.congr ?_ ?_ hcat, hc₂, ?_, ?_, hr₂⟩
      · simp only [List.length_cons]; omega
      · simp only [List.length_cons]; omega
      · rw [ha₂]; simp
      · rw [hb₂]; simp

/-- the stacks `dupB` touches. -/
theorem cmdTouches_dupB (c a b : Stk) : cmdTouches (dupB c a b) ⊆ {c, a, b} := by
  intro k hk
  simp only [dupB, dupBBody, seqs, cmdTouches] at hk ⊢
  simp at hk ⊢
  tauto

/-- `dupB` as a whole. -/
theorem dupB_ev {main : Cmd} {c a b : Stk} (hac : a ≠ c) (hbc : b ≠ c) (hab : a ≠ b)
    {G C A B : List Glyph} {g : Reg → Glyph} {X : Stk → List Glyph}
    (hgM : gMark ∉ G) (hc : X c = G ++ gMark :: C) (ha : X a = A) (hb : X b = B) :
    ∃ s' n, Ev main (dupB c a b) ⟨g, X⟩ s' n ∧ n ≤ 5 * (G.length + 1) + 2 ∧
      s'.stk c = C ∧ s'.stk a = G.reverse ++ A ∧ s'.stk b = G.reverse ++ B ∧
      (∀ k : Stk, k ≠ a → k ≠ b → k ≠ c → s'.stk k = X k) := by
  have hinit : Ev main (.set rLoopG Glyph.cons) ⟨g, X⟩
      ⟨Function.update g rLoopG Glyph.cons, X⟩ 1 := ev_set' main rLoopG Glyph.cons g X
  obtain ⟨s₁, hrun, hc₁, ha₁, hb₁, hr₁⟩ :=
    dupB_loop (main := main) hac hbc hab G C A B (Function.update g rLoopG Glyph.cons) X
      hgM (by simp) hc ha hb
  have hloop : Ev main (.loop rLoopG Glyph.cons (dupBBody c a b))
      ⟨Function.update g rLoopG Glyph.cons, X⟩ s₁ (5 * (G.length + 1) + 1) :=
    loopRuns.eval hrun (by rw [hr₁]; decide)
  have hmain : Ev main (dupB c a b) ⟨g, X⟩ s₁ (5 * (G.length + 1) + 2) := by
    unfold dupB
    simp only [seqs]
    exact Ev.seq' hinit hloop (by omega)
  refine ⟨s₁, 5 * (G.length + 1) + 2, hmain, le_rfl, hc₁, ha₁, hb₁, ?_⟩
  intro k hka hkb hkc
  have hfr : s₁.stk k = (⟨g, X⟩ : State).stk k :=
    Ev.frame hmain (S := {c, a, b}) (cmdTouches_dupB c a b) (by simp [hka, hkb, hkc])
  simpa using hfr

/-! ## `dupVal`: copy a value, with a full frame -/

/-- Full-strength `dupVal`: `dupVal a b c d` copies the top value of `a` onto `b`, keeping it on `a`;
the scratch stacks `c` and `d` and everything else are restored.  Cost `16 * (vsz v + 1)`. -/
theorem dupVal_ev_full {main : Cmd} {a b c d : Stk} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) {g : Reg → Glyph} {X : Stk → List Glyph}
    {v : Val} {A B : List Glyph} (ha : X a = v.enc ++ A) (hb : X b = B) :
    ∃ s' n, Ev main (dupVal a b c d) ⟨g, X⟩ s' n ∧ n ≤ 16 * (vsz v + 1) ∧
      s'.stk a = v.enc ++ A ∧ s'.stk b = v.enc ++ B ∧ s'.stk c = X c ∧ s'.stk d = X d ∧
      (∀ k : Stk, k ≠ a → k ≠ b → k ≠ c → k ≠ d → s'.stk k = X k) := by
  obtain ⟨s₁, n₁, h₁, hn₁, ha₁, hc₁, hd₁, hf₁⟩ :=
    mvA_ev (main := main) hac had hcd v A (X c) (X d) g X ha rfl rfl
  have hb₁ : s₁.stk b = B := by rw [hf₁ b hab.symm hbc hbd, hb]
  obtain ⟨s₂, n₂, h₂, hn₂, hc₂, ha₂, hb₂, hf₂⟩ :=
    dupB_ev (main := main) (c := c) (a := a) (b := b) hac hbc hab
      (G := v.enc.reverse) (C := X c) (A := A) (B := B) (g := s₁.reg) (X := s₁.stk)
      (gMark_not_mem_enc_rev v) hc₁ ha₁ hb₁
  have hlen : (v.enc.reverse).length = vsz v := by simp [vsz]
  have hm : Ev main (dupVal a b c d) ⟨g, X⟩ s₂ (n₁ + n₂) := by
    unfold dupVal
    exact Ev.seq h₁ h₂
  refine ⟨s₂, n₁ + n₂, hm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h₂' : n₂ ≤ 5 * (vsz v + 1) + 2 := by rw [← hlen]; exact hn₂
    have hv := one_le_vsz v
    omega
  · rw [ha₂, List.reverse_reverse]
  · rw [hb₂, List.reverse_reverse]
  · exact hc₂
  · rw [hf₂ d had.symm hbd.symm hcd.symm]; exact hd₁
  · intro k hka hkb hkc hkd
    rw [hf₂ k hka hkb hkc]
    exact hf₁ k hka hkc hkd

/-! ## The counter step -/

/-- **The counter step of `LayoutLib.enumerate`.** `incDup addP` walks the top of the value stack 0
(`int i` above the rest of the value list) and: copies `int i` to stack 4 (with `dupVal`, the copy
program defined in `Submission/Work/Layout/enumDefs.lean`), moves the counter aside, pushes `int 1`,
brings the counter back and runs `addP` (`IntLib.add`), so that stack 0 now carries `int (i+1)` and
stack 4 carries the label `int i` above its original content `L`. Cost `O(isz i)`, i.e.
`≤ (64+Kadd)*(isz i + 4)`. Build `dupVal_ev_full` (copy a value with full frame, cost
`16*(vsz+1)`) as a helper in the same file, on top of `Work.Layout.mvA_ev` and the `mvB` pattern. -/
theorem incDup_ev {addP : HvdH.Cmd} {Kadd : ℕ}
    (hadd : ∀ main : HvdH.Cmd, HvdH.BinOp main addP (fun _ _ => True) (· + ·)
      (fun a b => Kadd * (HvdH.isz a + HvdH.isz b))) :
    ∀ (main : HvdH.Cmd) (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph) (i : ℕ)
      (rest : List HvdH.Val) (R L : List HvdH.Glyph),
      X 0 = HvdH.encs (HvdH.Val.int (i : ℤ) :: rest) ++ R → X 4 = L →
      ∃ s' n, Work.Layout.Ev main (Work.Layout.incDup addP) ⟨g, X⟩ s' n ∧
        n ≤ (64 + Kadd) * (HvdH.isz (i : ℤ) + 4) ∧
        s'.stk 0 = HvdH.encs (HvdH.Val.int ((i + 1 : ℕ) : ℤ) :: rest) ++ R ∧
        s'.stk 4 = (HvdH.Val.int (i : ℤ)).enc ++ L ∧
        s'.stk 6 = X 6 ∧ s'.stk 7 = X 7 ∧ s'.stk 9 = X 9 ∧ s'.stk 10 = X 10 ∧
        s'.stk 11 = X 11 ∧
        (∀ k : HvdH.Stk, k ≠ 0 → k ≠ 4 → k ≠ 6 → k ≠ 7 → k ≠ 9 → k ≠ 10 → k ≠ 11 →
          s'.stk k = X k) := by
  intro main g X i rest R L hX0 hX4
  -- the counter `int i` leaves stack 0, keeping the rest of the value list below it
  have hX0' : X 0 = (Val.int (i : ℤ)).enc ++ (encs rest ++ R) := by
    rw [hX0, encs_cons, List.append_assoc]
  -- 1. copy `int i` from stack 0 onto stack 4 (the label)
  obtain ⟨s₁, n₁, h₁, hn₁, h01, h41, h61, h71, hf1⟩ :=
    dupVal_ev_full (main := main) (a := 0) (b := 4) (c := 6) (d := 7)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := g) (X := X) (v := Val.int (i : ℤ)) (A := encs rest ++ R) (B := L) hX0' hX4
  -- 2. move the counter to the scratch stack 9
  obtain ⟨s₂, n₂, h₂, hn₂, h02, h92, h102, h112, hf2⟩ :=
    mvVal_ev_full (main := main) (a := 0) (b := 9) (c := 10) (d := 11)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s₁.reg) (X := s₁.stk) (v := Val.int (i : ℤ)) (A := encs rest ++ R)
      (B := s₁.stk 9) h01 rfl
  -- 3. push `int 1`
  obtain ⟨s₃, n₃, h₃, hn₃, h03, hf3⟩ :=
    pushIntOne_ev (main := main) (g := s₂.reg) (X := s₂.stk)
  -- 4. bring the counter back on top of `int 1`
  have h₉₃ : s₃.stk 9 = (Val.int (i : ℤ)).enc ++ X 9 := by
    rw [hf3 9 (by decide), h92, hf1 9 (by decide) (by decide) (by decide) (by decide)]
  obtain ⟨s₄, n₄, h₄, hn₄, h94, h04, h104, h114, hf4⟩ :=
    mvVal_ev_full (main := main) (a := 9) (b := 0) (c := 10) (d := 11)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s₃.reg) (X := s₃.stk) (v := Val.int (i : ℤ)) (A := X 9) (B := s₃.stk 0) h₉₃ rfl
  -- 5. `addP` adds `int 1` to the counter
  have h₄0 : s₄.stk 0 = encs (Val.int (i : ℤ) :: Val.int (1 : ℤ) :: rest) ++ R := by
    rw [h04, h03, h02]
    simp only [encs_cons, List.append_assoc]
  obtain ⟨s₅, n₅, h₅, hn₅, h05, hf5⟩ :=
    binOp_ev (h := hadd main) (a := (i : ℤ)) (b := (1 : ℤ)) (rest := rest) (R := R)
      (s := s₄) trivial h₄0
  have h5' : Ev main addP s₄ s₅ n₅ := ⟨n₅, h₅, le_rfl⟩
  have hinc : Ev main (incDup addP) ⟨g, X⟩ s₅ (n₁ + (n₂ + (n₃ + (n₄ + n₅)))) := by
    unfold incDup
    simp only [seqs]
    exact Ev.seq h₁ (Ev.seq h₂ (Ev.seq h₃ (Ev.seq h₄ h5')))
  refine ⟨s₅, (64 + Kadd) * (isz (i : ℤ) + 4), hinc.mono ?_, le_rfl,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- cost
    have hv : vsz (Val.int (i : ℤ)) = isz (i : ℤ) := Work.IntLib.vsz_int (i : ℤ)
    have hb1 : n₁ ≤ 16 * (isz (i : ℤ) + 1) := by rw [← hv]; exact hn₁
    have hb2 : n₂ ≤ 16 * (isz (i : ℤ) + 1) := by rw [← hv]; exact hn₂
    have hb4 : n₄ ≤ 16 * (isz (i : ℤ) + 1) := by rw [← hv]; exact hn₄
    have hb5 : n₅ ≤ Kadd * (isz (i : ℤ) + 4) := by
      have hle : isz (i : ℤ) + isz (1 : ℤ) ≤ isz (i : ℤ) + 4 := by
        rw [show isz (1 : ℤ) = 3 from rfl]; omega
      exact le_trans hn₅ (mul_le_mul_right hle Kadd)
    have h1234 : n₁ + (n₂ + (n₃ + n₄)) ≤
        16 * (isz (i : ℤ) + 1) + 16 * (isz (i : ℤ) + 1) + 6 + 16 * (isz (i : ℤ) + 1) := by
      omega
    have hI : 16 * (isz (i : ℤ) + 1) + 16 * (isz (i : ℤ) + 1) + 6 + 16 * (isz (i : ℤ) + 1) ≤
        64 * (isz (i : ℤ) + 4) := by omega
    have hassoc : n₁ + (n₂ + (n₃ + (n₄ + n₅))) = (n₁ + (n₂ + (n₃ + n₄))) + n₅ := by omega
    rw [hassoc]
    calc (n₁ + (n₂ + (n₃ + n₄))) + n₅
        ≤ (16 * (isz (i : ℤ) + 1) + 16 * (isz (i : ℤ) + 1) + 6 + 16 * (isz (i : ℤ) + 1)) +
            Kadd * (isz (i : ℤ) + 4) := add_le_add h1234 hb5
      _ ≤ 64 * (isz (i : ℤ) + 4) + Kadd * (isz (i : ℤ) + 4) := add_le_add hI le_rfl
      _ = (64 + Kadd) * (isz (i : ℤ) + 4) := by ring
  · -- stack 0: the incremented counter
    rw [h05]
    rw [show ((i : ℤ) + 1) = ((i + 1 : ℕ) : ℤ) by push_cast; ring]
  · -- stack 4: the label
    rw [hf5 4 (by decide), hf4 4 (by decide) (by decide) (by decide) (by decide),
      hf3 4 (by decide), hf2 4 (by decide) (by decide) (by decide) (by decide)]
    exact h41
  · -- stack 6
    rw [hf5 6 (by decide), hf4 6 (by decide) (by decide) (by decide) (by decide),
      hf3 6 (by decide), hf2 6 (by decide) (by decide) (by decide) (by decide)]
    exact h61
  · -- stack 7
    rw [hf5 7 (by decide), hf4 7 (by decide) (by decide) (by decide) (by decide),
      hf3 7 (by decide), hf2 7 (by decide) (by decide) (by decide) (by decide)]
    exact h71
  · -- stack 9
    rw [hf5 9 (by decide)]
    exact h94
  · -- stack 10
    rw [hf5 10 (by decide), h104, hf3 10 (by decide), h102,
      hf1 10 (by decide) (by decide) (by decide) (by decide)]
  · -- stack 11
    rw [hf5 11 (by decide), h114, hf3 11 (by decide), h112,
      hf1 11 (by decide) (by decide) (by decide) (by decide)]
  · -- everything else
    intro k h0 h4 h6 h7 h9 h10 h11
    rw [hf5 k h0, hf4 k h9 h0 h10 h11, hf3 k h0, hf2 k h0 h9 h10 h11,
      hf1 k h0 h4 h6 h7]

end Work.Layout
