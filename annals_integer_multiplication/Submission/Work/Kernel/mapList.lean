import Mathlib
import Submission.Work.Kernel.mapListDefs
import Submission.Work.Kernel.mapListPhaseA
import Submission.Work.Kernel.mapListPhaseRev
import Submission.Work.Kernel.mapListPhaseB
import Submission.Work.Kernel.mapListRebuild

set_option autoImplicit false
set_option maxHeartbeats 6400000

namespace Work.Kernel

open HvdH
open Work.Layout

@[simp] theorem mapList_tSet_stk (s : State) (r : Reg) (g : Glyph) : (State.tSet s r g).stk = s.stk :=
  rfl

@[simp] theorem mapList_tSet_reg (s : State) (r : Reg) (g : Glyph) (r' : Reg) :
    (State.tSet s r g).reg r' = if r' = r then g else s.reg r' := by
  rw [State.tSet]; exact State.updReg_apply s r r' g

@[simp] theorem mapList_tPush_stk (s : State) (k : Stk) (r : Reg) (k' : Stk) :
    (State.tPush s k r).stk k' = if k' = k then s.reg r :: s.stk k else s.stk k' := by
  show Function.update s.stk k (s.reg r :: s.stk k) k'
      = if k' = k then s.reg r :: s.stk k else s.stk k'
  exact Function.update_apply s.stk k (s.reg r :: s.stk k) k'

@[simp] theorem mapList_tPush_reg (s : State) (k : Stk) (r : Reg) (r' : Reg) :
    (State.tPush s k r).reg r' = s.reg r' := rfl

@[simp] theorem mapList_tPop_stk (s : State) (k : Stk) (r : Reg) (k' : Stk) :
    (State.tPop s k r).stk k' = if k' = k then (s.stk k).tail else s.stk k' := by
  rw [State.tPop, State.updReg_stk]
  exact State.updStk_apply s k k' (s.stk k).tail

/-- Arithmetic core of the `mapList` cost bound (the constant `15` is the number of primitive steps
of the straight-line parts of `mapList_prog`). -/
theorem mapList_cost_arith (n c L x1 x2 x3 x4 : ℕ)
    (h1 : x1 ≤ n * (16 * (L + 1) + 5) + 7) (h2 : x2 ≤ n * (16 * (L + 1) + 4) + 6)
    (h3 : x3 ≤ n * (c + 32 * (L + 1) + 5) + 6) (h4 : x4 ≤ n * (16 * (L + 1) + 6) + 6) :
    1 + (2 + (x1 + (2 + (1 + (x2 + (1 + (2 + (1 + (x3 + (1 + (2 + (1 + (x4 + 1)))))))))))))
      ≤ n * (c + 128 * (L + 1)) + 128 := by
  have hsum : 1 + (2 + (x1 + (2 + (1 + (x2 + (1 + (2 + (1 + (x3 + (1 + (2 + (1 + (x4 + 1)))))))))))))
      = x1 + x2 + x3 + x4 + 15 := by ring
  rw [hsum]
  refine le_trans (b := (n * (16 * (L + 1) + 5) + 7) + (n * (16 * (L + 1) + 4) + 6)
        + (n * (c + 32 * (L + 1) + 5) + 6) + (n * (16 * (L + 1) + 6) + 6) + 15) ?_ ?_
  · omega
  have hkey : (n * (16 * (L + 1) + 5) + 7) + (n * (16 * (L + 1) + 4) + 6)
        + (n * (c + 32 * (L + 1) + 5) + 6) + (n * (16 * (L + 1) + 6) + 6) + 15
      = n * (c + 80 * (L + 1) + 20) + 40 := by ring
  rw [hkey]
  have hc : c + 80 * (L + 1) + 20 ≤ c + 128 * (L + 1) := by omega
  calc n * (c + 80 * (L + 1) + 20) + 40 ≤ n * (c + 128 * (L + 1)) + 40 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left n hc) 40
    _ ≤ n * (c + 128 * (L + 1)) + 128 := by omega

/-- `mapList` field of `HvdH.KernelLib` (v2/v3).  Imports: `Submission.Work.Kernel.Raw`, `Submission.Work.Kernel.Pend`, plus the already-proved marker movers `Submission.Work.Layout.Move` (`Work.Layout.Ev` = bounded `Eval`; `mvVal_ev` moves one value between two stacks at cost `≤ 16*(vsz v+1)`) — using them saves hours.  Key facts: `encs (ofList xs :: rest) = cons :: (encs xs ++ rest)` and `encs (x :: xs') = x.enc ++ encs xs'`, so popping one `cons` glyph from the top of the value stack exposes the first element `x` on top of `ofList xs' :: rest`; conversely `ofList [] = .nil`.  Plan: if the top value is `nil`, drop it and stop (output `.nil`, cost ≤ K — this is what makes the bound work at `xs = []`).  Otherwise move the elements aside one at a time onto a scratch stack (marker before each); then for each element, move it back so that the value stack is exactly `x :: rest` (the `rest` of the statement!), run `q` via its `WordR` hypothesis, and move the result `y` aside to a second scratch stack (marker first); finally rebuild `ofList ys` on top of `rest` and restore all scratch stacks.  `List.Forall₂` follows by induction.  Helpers must be named with the prefix `mapList_`. -/
theorem mapList : ∃ (comb : HvdH.Cmd → HvdH.Cmd) (K : ℕ), ∀ (main q : HvdH.Cmd) (rest : List HvdH.Val) (P : HvdH.Val → Prop)
    (Q : HvdH.Val → HvdH.Val → Prop) (c L : ℕ),
    (∀ x, P x → HvdH.WordR main q (fun vs => vs = x :: rest)
      (fun _ out => ∃ y, out = y :: rest ∧ Q x y ∧ HvdH.vsz y ≤ L) (fun _ => c)) →
    ∀ xs : List HvdH.Val, (∀ x ∈ xs, P x ∧ HvdH.vsz x ≤ L) →
    HvdH.WordR main (comb q) (fun vs => vs = HvdH.ofList xs :: rest)
      (fun _ out => ∃ ys, out = HvdH.ofList ys :: rest ∧ List.Forall₂ Q xs ys)
      (fun _ => xs.length * (c + K * (L + 1)) + K) := by
  have hRev : ∀ (main : Cmd) (bs : List Val) (s : State) (L : ℕ) (X1 : List Glyph),
      s.reg rLoopG = Glyph.cons → (∀ x ∈ bs, vsz x ≤ L) →
      s.stk 1 = encs bs ++ gMark :: X1 →
      ∃ (s' : State) (C : ℕ),
        loopRuns main rLoopG Glyph.cons mapList_bodyRev (bs.length + 1) s s' C ∧
        C ≤ bs.length * (16 * (L + 1) + 4) + 5 ∧
        s'.stk 1 = gMark :: X1 ∧ s'.stk 2 = encs bs.reverse ++ s.stk 2 ∧
        s'.reg rLoopG = Glyph.eos ∧ (∀ k : Stk, k ≠ 1 → k ≠ 2 → s'.stk k = s.stk k) := mapListPhaseRev
  have hB : ∀ (main q : Cmd) (bs rest : List Val) (R : List Glyph) (P : Val → Prop)
      (Q : Val → Val → Prop) (c L : ℕ) (s : State) (X2 : List Glyph),
      s.reg rLoopG = Glyph.cons →
      (∀ x, P x → WordR main q (fun vs => vs = x :: rest)
        (fun _ out => ∃ y, out = y :: rest ∧ Q x y ∧ vsz y ≤ L) (fun _ => c)) →
      (∀ x ∈ bs, P x ∧ vsz x ≤ L) → s.stk 2 = encs bs ++ gMark :: X2 →
      s.stk 0 = encs rest ++ R →
      ∃ (s' : State) (zs : List Val) (C : ℕ),
        loopRuns main rLoopG Glyph.cons (mapList_bodyB q) (bs.length + 1) s s' C ∧
        C ≤ bs.length * (c + 32 * (L + 1) + 5) + 5 ∧ List.Forall₂ Q bs zs ∧
        s'.stk 2 = gMark :: X2 ∧ s'.stk 0 = encs rest ++ R ∧
        s'.stk 3 = encs zs.reverse ++ s.stk 3 ∧ (∀ y ∈ zs, vsz y ≤ L) ∧
        s'.reg rLoopG = Glyph.eos ∧ (∀ k : Stk, k ≠ 0 → k ≠ 2 → k ≠ 3 → s'.stk k = s.stk k) := mapListPhaseB
  have hR : ∀ (main : Cmd) (bs cs rest : List Val) (R : List Glyph) (s : State) (L : ℕ)
      (X3 : List Glyph),
      s.reg rLoopG = Glyph.cons → (∀ x ∈ bs, vsz x ≤ L) →
      s.stk 3 = encs bs ++ gMark :: X3 → s.stk 0 = encs (ofList cs :: rest) ++ R →
      ∃ (s' : State) (C : ℕ),
        loopRuns main rLoopG Glyph.cons mapList_bodyR (bs.length + 1) s s' C ∧
        C ≤ bs.length * (16 * (L + 1) + 6) + 5 ∧ s'.stk 3 = gMark :: X3 ∧
        s'.stk 0 = encs (ofList (bs.reverse ++ cs) :: rest) ++ R ∧
        s'.reg rLoopG = Glyph.eos ∧ (∀ k : Stk, k ≠ 0 → k ≠ 3 → s'.stk k = s.stk k) := mapListRebuild
  refine ⟨mapList_prog, 128, ?_⟩
  intro main q rest P Q c L hq xs hxs vs hvs s R hR0
  subst hvs
  set A1 : ℕ := xs.length * (16 * (L + 1) + 5) + 7 with hA1
  set A2 : ℕ := xs.length * (16 * (L + 1) + 4) + 6 with hA2
  set A3 : ℕ := xs.length * (c + 32 * (L + 1) + 5) + 6 with hA3
  set A4 : ℕ := xs.length * (16 * (L + 1) + 6) + 6 with hA4
  -- ================= step 1: set rLoopG cons =================
  set s1 : State := State.tSet s rLoopG Glyph.cons with hs1
  have h1stk : ∀ k : Stk, s1.stk k = s.stk k := fun k => by rw [hs1]; rfl
  have h1ev : Ev main (.set rLoopG Glyph.cons) s s1 1 := by
    rw [hs1]; exact ev_set main rLoopG Glyph.cons s
  -- ================= step 2: pushConst 1 gMark =================
  set s2 : State := State.tPush (State.tSet s1 rB gMark) 1 rB with hs2
  have h2ev : Ev main (pushConst 1 gMark) s1 s2 2 := by
    change Ev main (.seq (.set rB gMark) (.push 1 rB)) s1 s2 2
    exact Ev.seq (ev_set main rB gMark s1) (ev_push main 1 rB _)
  have h20 : s2.stk 0 = encs (ofList xs :: rest) ++ R := by
    rw [hs2, hs1]; simpa using hR0
  have h21 : s2.stk 1 = gMark :: s.stk 1 := by rw [hs2, hs1]; simp
  have h2stk : ∀ k : Stk, k ≠ 1 → s2.stk k = s.stk k := by
    intro k hk; rw [hs2, hs1]; simp [hk]
  have h2r : s2.reg rLoopG = Glyph.cons := by
    rw [hs2, hs1, mapList_tPush_reg, mapList_tSet_reg,
      if_neg (by decide : ¬(rLoopG = rB)), mapList_tSet_reg, if_pos rfl]
  -- ================= phase A =================
  obtain ⟨s3, C3, hrun3, hC3, h30, h31, h3r, h3fr⟩ :=
    mapList_phaseA main xs rest R s2 L h2r (fun x hx => (hxs x hx).2) h20
  have hAev : Ev main (.loop rLoopG Glyph.cons mapList_bodyA) s2 s3 A1 :=
    (loopRuns.eval hrun3 (by rw [h3r]; decide)).mono (by rw [hA1]; omega)
  have h31' : s3.stk 1 = encs xs.reverse ++ gMark :: s.stk 1 := by rw [h31, h21]
  -- ================= step 4: pushConst 2 gMark =================
  set s4 : State := State.tPush (State.tSet s3 rB gMark) 2 rB with hs4
  have h4ev : Ev main (pushConst 2 gMark) s3 s4 2 := by
    change Ev main (.seq (.set rB gMark) (.push 2 rB)) s3 s4 2
    exact Ev.seq (ev_set main rB gMark s3) (ev_push main 2 rB _)
  have h42 : s4.stk 2 = gMark :: s3.stk 2 := by rw [hs4]; simp
  have h4stk : ∀ k : Stk, k ≠ 2 → s4.stk k = s3.stk k := by
    intro k hk; rw [hs4]; simp [hk]
  -- ================= step 5: set rLoopG cons =================
  set s5 : State := State.tSet s4 rLoopG Glyph.cons with hs5
  have h5ev : Ev main (.set rLoopG Glyph.cons) s4 s5 1 := by
    rw [hs5]; exact ev_set main rLoopG Glyph.cons s4
  have h5r : s5.reg rLoopG = Glyph.cons := by rw [hs5]; simp
  have h5stk : ∀ k : Stk, s5.stk k = s4.stk k := fun k => by rw [hs5]; rfl
  have h51 : s5.stk 1 = encs xs.reverse ++ gMark :: s.stk 1 := by
    rw [h5stk 1, h4stk 1 (by decide)]; exact h31'
  -- ================= phase Rev =================
  obtain ⟨s6, C6, hrun6, hC6, h61, h62, h6r, h6fr⟩ :=
    hRev main xs.reverse s5 L (s.stk 1) h5r
      (fun x hx => (hxs x (List.mem_reverse.mp hx)).2) h51
  have hRvev : Ev main (.loop rLoopG Glyph.cons mapList_bodyRev) s5 s6 A2 :=
    (loopRuns.eval hrun6 (by rw [h6r]; decide)).mono (by
      rw [hA2]
      have hlen : xs.reverse.length = xs.length := List.length_reverse
      rw [← hlen]
      omega)
  have h62' : s6.stk 2 = encs xs ++ gMark :: s.stk 2 := by
    rw [h62, List.reverse_reverse, h5stk 2, h42, h3fr 2 (by decide) (by decide),
      h2stk 2 (by decide)]
  -- ================= step 7: pop 1 rA =================
  set s7 : State := State.tPop s6 1 rA with hs7
  have h7ev : Ev main (.pop 1 rA) s6 s7 1 := by rw [hs7]; exact ev_pop main 1 rA s6
  have h71 : s7.stk 1 = s.stk 1 := by rw [hs7]; simp [h61]
  have h7stk : ∀ k : Stk, k ≠ 1 → s7.stk k = s6.stk k := by
    intro k hk; rw [hs7]; simp [hk]
  -- ================= step 8: pushConst 3 gMark =================
  set s8 : State := State.tPush (State.tSet s7 rB gMark) 3 rB with hs8
  have h8ev : Ev main (pushConst 3 gMark) s7 s8 2 := by
    change Ev main (.seq (.set rB gMark) (.push 3 rB)) s7 s8 2
    exact Ev.seq (ev_set main rB gMark s7) (ev_push main 3 rB _)
  have h83 : s8.stk 3 = gMark :: s7.stk 3 := by rw [hs8]; simp
  have h83' : s8.stk 3 = gMark :: s.stk 3 := by
    rw [h83, h7stk 3 (by decide), h6fr 3 (by decide) (by decide), h5stk 3, h4stk 3 (by decide),
      h3fr 3 (by decide) (by decide), h2stk 3 (by decide)]
  have h8stk : ∀ k : Stk, k ≠ 3 → s8.stk k = s7.stk k := by
    intro k hk; rw [hs8]; simp [hk]
  -- ================= step 9: set rLoopG cons =================
  set s9 : State := State.tSet s8 rLoopG Glyph.cons with hs9
  have h9ev : Ev main (.set rLoopG Glyph.cons) s8 s9 1 := by
    rw [hs9]; exact ev_set main rLoopG Glyph.cons s8
  have h9r : s9.reg rLoopG = Glyph.cons := by rw [hs9]; simp
  have h9stk : ∀ k : Stk, s9.stk k = s8.stk k := fun k => by rw [hs9]; rfl
  have h92 : s9.stk 2 = encs xs ++ gMark :: s.stk 2 := by
    rw [h9stk 2, h8stk 2 (by decide), h7stk 2 (by decide)]; exact h62'
  have h90 : s9.stk 0 = encs rest ++ R := by
    rw [h9stk 0, h8stk 0 (by decide), h7stk 0 (by decide), h6fr 0 (by decide) (by decide),
      h5stk 0, h4stk 0 (by decide)]
    exact h30
  -- ================= phase B =================
  obtain ⟨s10, zs, C10, hrun10, hC10, hF, h10_2, h10_0, h10_3, h10sz, h10r, h10fr⟩ :=
    hB main q xs rest R P Q c L s9 (s.stk 2) h9r hq (fun x hx => hxs x hx) h92 h90
  have hBev : Ev main (.loop rLoopG Glyph.cons (mapList_bodyB q)) s9 s10 A3 :=
    (loopRuns.eval hrun10 (by rw [h10r]; decide)).mono (by rw [hA3]; omega)
  have h10_3' : s10.stk 3 = encs zs.reverse ++ gMark :: s.stk 3 := by
    rw [h10_3, h9stk 3, h83']
  -- ================= step 11: pop 2 rA =================
  set s11 : State := State.tPop s10 2 rA with hs11
  have h11ev : Ev main (.pop 2 rA) s10 s11 1 := by rw [hs11]; exact ev_pop main 2 rA s10
  have h11_2 : s11.stk 2 = s.stk 2 := by rw [hs11]; simp [h10_2]
  have h11stk : ∀ k : Stk, k ≠ 2 → s11.stk k = s10.stk k := by
    intro k hk; rw [hs11]; simp [hk]
  -- ================= step 12: pushConst 0 nil =================
  set s12 : State := State.tPush (State.tSet s11 rB Glyph.nil) 0 rB with hs12
  have h12ev : Ev main (pushConst 0 Glyph.nil) s11 s12 2 := by
    change Ev main (.seq (.set rB Glyph.nil) (.push 0 rB)) s11 s12 2
    exact Ev.seq (ev_set main rB Glyph.nil s11) (ev_push main 0 rB _)
  have h120 : s12.stk 0 = encs (ofList ([] : List Val) :: rest) ++ R := by
    rw [hs12]
    show Glyph.nil :: s11.stk 0 = encs (ofList ([] : List Val) :: rest) ++ R
    rw [h11stk 0 (by decide), h10_0, mapList_encs_ofList_nil, List.cons_append]
  have h12stk : ∀ k : Stk, k ≠ 0 → s12.stk k = s11.stk k := by
    intro k hk; rw [hs12]; simp [hk]
  -- ================= step 13: set rLoopG cons =================
  set s13 : State := State.tSet s12 rLoopG Glyph.cons with hs13
  have h13ev : Ev main (.set rLoopG Glyph.cons) s12 s13 1 := by
    rw [hs13]; exact ev_set main rLoopG Glyph.cons s12
  have h13r : s13.reg rLoopG = Glyph.cons := by rw [hs13]; simp
  have h13stk : ∀ k : Stk, s13.stk k = s12.stk k := fun k => by rw [hs13]; rfl
  have h133 : s13.stk 3 = encs zs.reverse ++ gMark :: s.stk 3 := by
    rw [h13stk 3, h12stk 3 (by decide), h11stk 3 (by decide)]
    exact h10_3'
  have h130 : s13.stk 0 = encs (ofList ([] : List Val) :: rest) ++ R := by
    rw [h13stk 0]; exact h120
  -- ================= phase rebuild =================
  obtain ⟨s14, C14, hrun14, hC14, h14_3, h14_0, h14r, h14fr⟩ :=
    hR main zs.reverse [] rest R s13 L (s.stk 3) h13r
      (fun x hx => h10sz x (List.mem_reverse.mp hx)) h133 h130
  have hRebev : Ev main (.loop rLoopG Glyph.cons mapList_bodyR) s13 s14 A4 :=
    (loopRuns.eval hrun14 (by rw [h14r]; decide)).mono (by
      rw [hA4]
      have hlen : zs.reverse.length = zs.length := List.length_reverse
      have hlen2 : xs.length = zs.length := hF.length_eq
      rw [hlen2, ← hlen]
      omega)
  have h14_0' : s14.stk 0 = encs (ofList zs :: rest) ++ R := by
    rw [h14_0]; simp only [List.reverse_reverse, List.append_nil]
  -- ================= step 15: pop 3 rA =================
  set s15 : State := State.tPop s14 3 rA with hs15
  have h15ev : Ev main (.pop 3 rA) s14 s15 1 := by rw [hs15]; exact ev_pop main 3 rA s14
  have h15_0 : s15.stk 0 = encs (ofList zs :: rest) ++ R := by
    rw [hs15]; simp [h14_0']
  have h15_3 : s15.stk 3 = s.stk 3 := by rw [hs15]; simp [h14_3]
  have h15stk : ∀ k : Stk, k ≠ 3 → s15.stk k = s14.stk k := by
    intro k hk; rw [hs15]; simp [hk]
  have h15_1 : s15.stk 1 = s.stk 1 := by
    rw [h15stk 1 (by decide), h14fr 1 (by decide) (by decide), h13stk 1, h12stk 1 (by decide),
      h11stk 1 (by decide), h10fr 1 (by decide) (by decide) (by decide), h9stk 1,
      h8stk 1 (by decide)]
    exact h71
  have h15_2 : s15.stk 2 = s.stk 2 := by
    rw [h15stk 2 (by decide), h14fr 2 (by decide) (by decide), h13stk 2, h12stk 2 (by decide)]
    exact h11_2
  have hoth : ∀ k : Stk, k ≠ 0 → k ≠ 1 → k ≠ 2 → k ≠ 3 → s15.stk k = s.stk k := by
    intro k hk0 hk1 hk2 hk3
    rw [h15stk k hk3, h14fr k hk0 hk3, h13stk k, h12stk k hk0, h11stk k hk2,
      h10fr k hk0 hk2 hk3, h9stk k, h8stk k hk3, h7stk k hk1, h6fr k hk1 hk2,
      h5stk k, h4stk k hk2, h3fr k hk0 hk1, h2stk k hk1]
  -- ================= the `Ev` chain =================
  set BDG : ℕ := 1 + (2 + (A1 + (2 + (1 + (A2 + (1 + (2 + (1 + (A3 + (1 + (2 + (1 + (A4 + 1)))))))))))))
    with hBDG
  have hbdg : BDG ≤ xs.length * (c + 128 * (L + 1)) + 128 := by
    rw [hBDG]
    exact mapList_cost_arith xs.length c L A1 A2 A3 A4 (by rw [hA1]) (by rw [hA2])
      (by rw [hA3]) (by rw [hA4])
  have hchain : Ev main (mapList_prog q) s s15 BDG := by
    change Ev main (seqs [ .set rLoopG Glyph.cons, pushConst 1 gMark,
        .loop rLoopG Glyph.cons mapList_bodyA, pushConst 2 gMark, .set rLoopG Glyph.cons,
        .loop rLoopG Glyph.cons mapList_bodyRev, .pop 1 rA, pushConst 3 gMark,
        .set rLoopG Glyph.cons, .loop rLoopG Glyph.cons (mapList_bodyB q), .pop 2 rA,
        pushConst 0 Glyph.nil, .set rLoopG Glyph.cons,
        .loop rLoopG Glyph.cons mapList_bodyR, .pop 3 rA ]) s s15 BDG
    refine Ev.seqs_cons h1ev ?_
    refine Ev.seqs_cons h2ev ?_
    refine Ev.seqs_cons hAev ?_
    refine Ev.seqs_cons h4ev ?_
    refine Ev.seqs_cons h5ev ?_
    refine Ev.seqs_cons hRvev ?_
    refine Ev.seqs_cons h7ev ?_
    refine Ev.seqs_cons h8ev ?_
    refine Ev.seqs_cons h9ev ?_
    refine Ev.seqs_cons hBev ?_
    refine Ev.seqs_cons h11ev ?_
    refine Ev.seqs_cons h12ev ?_
    refine Ev.seqs_cons h13ev ?_
    refine Ev.seqs_cons hRebev ?_
    exact h15ev
  obtain ⟨n15, hEval15, hLe15⟩ := hchain
  refine ⟨ofList zs :: rest, s15, n15, ⟨zs, rfl, hF⟩, hEval15, le_trans hLe15 hbdg, h15_0, ?_⟩
  intro k hk0
  rcases eq_or_ne k 1 with h1 | h1
  · subst h1; exact h15_1
  rcases eq_or_ne k 2 with h2 | h2
  · subst h2; exact h15_2
  rcases eq_or_ne k 3 with h3 | h3
  · subst h3; exact h15_3
  · exact hoth k hk0 h1 h2 h3

end Work.Kernel
