import Mathlib
import Submission.Work.Kernel.mapListDefs
import Submission.Work.Kernel.mapListPhaseA
import Submission.Work.Kernel.mapListBodyBMiss

namespace Work.Kernel

open HvdH
open Work.Layout

/-- One `mapList_bodyB q` iteration when the top glyph of stack 2 **is** the marker `gMark`:
`peek` reads `gMark` into `rA`, the `ite` takes the stop branch, and `set rLoopG eos` clears the
loop flag.  Nothing else changes (cost `3`: `peek` + `ite` test + `set`). -/
theorem mapList_bodyB_hit {main q : Cmd} {X2 : List Glyph} {s : State}
    (h2 : s.stk 2 = gMark :: X2) :
    ∃ (s' : State) (C : ℕ),
      Ev main (mapList_bodyB q) s s' C ∧ C ≤ 3 ∧
      s'.stk 2 = gMark :: X2 ∧ s'.stk 0 = s.stk 0 ∧ s'.stk 3 = s.stk 3 ∧
      s'.reg rLoopG = Glyph.eos ∧
      (∀ k : Stk, k ≠ 0 → k ≠ 2 → k ≠ 3 → s'.stk k = s.stk k) := by
  have hhead : (s.stk 2).headD Glyph.eos = gMark := by rw [h2]; rfl
  set sp : State := ⟨Function.update s.reg rA ((s.stk 2).headD Glyph.eos), s.stk⟩ with hsp
  have hpeek : Ev main (.peek (2 : Stk) rA) s sp 1 := by rw [hsp]; exact ev_peek main 2 rA s
  have hsp_reg : sp.reg rA = gMark := by
    rw [hsp]; simpa only [Function.update_self] using hhead
  set sr : State := ⟨Function.update sp.reg rLoopG Glyph.eos, sp.stk⟩ with hsr
  have hset : Ev main (.set rLoopG Glyph.eos) sp sr 1 := by
    rw [hsr]; exact ev_set main rLoopG Glyph.eos sp
  have hite : Ev main (.ite rA gMark (.set rLoopG Glyph.eos)
      (.seq (mvVal 2 0 4 5) (.seq q (.seq (mvVal 0 3 4 5) (.set rLoopG Glyph.cons))))) sp sr 2 :=
    Ev.iteT hsp_reg (hset.mono (by omega))
  have hbody : Ev main (mapList_bodyB q) s sr 3 := by
    unfold mapList_bodyB
    exact Ev.seq' hpeek hite (by omega)
  refine ⟨sr, 3, hbody, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · show sr.stk 2 = gMark :: X2; rw [hsr, hsp]; exact h2
  · show sr.stk 0 = s.stk 0; rw [hsr, hsp]
  · show sr.stk 3 = s.stk 3; rw [hsr, hsp]
  · show sr.reg rLoopG = Glyph.eos; rw [hsr]; simp
  · intro k _ _ _; show sr.stk k = s.stk k; rw [hsr, hsp]

/-- `mapList` phase C: `Work.Kernel.mapList_bodyB q` (defined in `Submission/Work/Kernel/mapListDefs.lean`), run as `Cmd.loop Work.Layout.rLoopG Glyph.cons (mapList_bodyB q)`.  The state has stack 2 = `encs bs ++ gMark :: X2` (the elements `bs`, head on top) and stack 0 = `encs rest ++ R`.  While the top glyph of stack 2 is not `gMark`, the body moves the top value `x` of stack 2 to stack 0 (so that the value stack is exactly `x :: rest`, as `hq` requires), runs `q`, and moves the result `y` to stack 3; it stops at the marker, leaving stack 2 = `gMark :: X2`, stack 0 = `encs rest ++ R`, and stack 3 = `encs zs.reverse ++ s.stk 3` where `zs` are the results in processing order, with `List.Forall₂ Q bs zs`.  `Work.Layout.mvVal_ev_full` (bounded `Ev`/`Eval`, cost `≤ 16 * (vsz v + 1)`, restores its buffer/counter stacks 4,5 exactly) is the tool.  Template: `Work.Kernel.mapList_phaseA` in `Submission/Work/Kernel/mapListPhaseA.lean`.  To be placed in namespace `Work.Kernel`. -/
theorem mapListPhaseB (main q : HvdH.Cmd) (bs rest : List HvdH.Val) (R : List HvdH.Glyph)
    (P : HvdH.Val → Prop) (Q : HvdH.Val → HvdH.Val → Prop) (c L : ℕ) (s : HvdH.State)
    (X2 : List HvdH.Glyph)
    (hr : s.reg Work.Layout.rLoopG = HvdH.Glyph.cons)
    (hq : ∀ x, P x → HvdH.WordR main q (fun vs => vs = x :: rest)
      (fun _ out => ∃ y, out = y :: rest ∧ Q x y ∧ HvdH.vsz y ≤ L) (fun _ => c))
    (hsz : ∀ x ∈ bs, P x ∧ HvdH.vsz x ≤ L)
    (h2 : s.stk 2 = HvdH.encs bs ++ Work.Layout.gMark :: X2)
    (h0 : s.stk 0 = HvdH.encs rest ++ R) :
    ∃ (s' : HvdH.State) (zs : List HvdH.Val) (C : ℕ),
      Work.Layout.loopRuns main Work.Layout.rLoopG HvdH.Glyph.cons (Work.Kernel.mapList_bodyB q)
        (bs.length + 1) s s' C ∧
      C ≤ bs.length * (c + 32 * (L + 1) + 5) + 5 ∧
      List.Forall₂ Q bs zs ∧
      s'.stk 2 = Work.Layout.gMark :: X2 ∧
      s'.stk 0 = HvdH.encs rest ++ R ∧
      s'.stk 3 = HvdH.encs zs.reverse ++ s.stk 3 ∧
      (∀ y ∈ zs, HvdH.vsz y ≤ L) ∧
      s'.reg Work.Layout.rLoopG = HvdH.Glyph.eos ∧
      (∀ k : HvdH.Stk, k ≠ 0 → k ≠ 2 → k ≠ 3 → s'.stk k = s.stk k) := by
  induction bs generalizing s with
  | nil =>
    have h2' : s.stk 2 = gMark :: X2 := by rw [h2, encs_nil, List.nil_append]
    obtain ⟨s', C, hev, _hC, hs'2, hs'0, hs'3, hs'r, hfr⟩ :=
      mapList_bodyB_hit (main := main) (q := q) h2'
    refine ⟨s', [], C + 1, loopRuns.one hr hev, ?_, List.Forall₂.nil, hs'2, ?_, ?_, ?_, hs'r, ?_⟩
    · simp only [List.length_nil, Nat.zero_mul, Nat.zero_add]; omega
    · rw [hs'0, h0]
    · rw [hs'3, List.reverse_nil, encs_nil, List.nil_append]
    · intro y hy; exact absurd hy List.not_mem_nil
    · intro k hk0 hk2 hk3; exact hfr k hk0 hk2 hk3
  | cons x xs ih =>
    have h2' : s.stk 2 = x.enc ++ (encs xs ++ gMark :: X2) := by
      rw [h2, encs_cons, List.append_assoc]
    obtain ⟨hxP, hxL⟩ := hsz x (by simp)
    obtain ⟨s₁, y, C₁, hev₁, hC₁, hQxy, hyL, hs₁2, hs₁0, hs₁3, hs₁r, hfr₁⟩ :=
      mapListBodyBMiss (main := main) (q := q) (x := x) (bs' := xs) (rest := rest) (R := R)
        (X2 := X2) (Q := Q) (c := c) (L := L) (s := s) hxL (hq x hxP) h2' h0
    obtain ⟨s₂, zs', C₂, hrun₂, hC₂, hForall₂', hs₂2, hs₂0, hs₂3, hs₂vsz, hs₂r, hfr₂⟩ :=
      ih (s := s₁) hs₁r (fun y hy => hsz y (List.mem_cons_of_mem x hy)) hs₁2 hs₁0
    refine ⟨s₂, y :: zs', C₁ + C₂ + 1, ?_, ?_, List.Forall₂.cons hQxy hForall₂', hs₂2, hs₂0,
      ?_, ?_, hs₂r, ?_⟩
    · refine loopRuns.cast (by simp [List.length_cons]) (loopRuns.succ' hr hev₁ hrun₂ (by omega))
    · have h1 := hC₁; have h2c := hC₂
      simp only [List.length_cons]
      rw [Nat.add_mul, Nat.one_mul]
      omega
    · rw [hs₂3, hs₁3]
      simp [List.reverse_cons, encs_append, List.append_assoc]
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hyL
      · exact hs₂vsz z hz
    · intro k hk0 hk2 hk3
      rw [hfr₂ k hk0 hk2 hk3, hfr₁ k hk0 hk2 hk3]

end Work.Kernel
