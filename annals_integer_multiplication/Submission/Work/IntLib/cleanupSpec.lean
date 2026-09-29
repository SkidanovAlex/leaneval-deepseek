import Mathlib
import Submission.Work.IntLib.divCore
import Submission.Work.IntLib.divRaw
import Submission.Work.IntLib.eval_dropRgn
import Submission.Work.Kernel.Raw

/-!
# `Work.IntLib.cleanupSpec`: the nine-region cleanup of the division core

`Work.IntLib.Div.cleanup` is `seqs [dropRgn stP gP rgT, …, dropRgn stY gY rgT]`: it drops the nine
regions of stacks 1–9 down to their markers and then pops the markers, so that every stack other
than stack 0 is restored to its entry content `b0`.

The generic `eval_dropRgn` bounds one `dropRgn` by `6 * (l.length + 1) + 9`, which is too weak for
the nine-fold bound `5 * (sum of lengths) + 117` (it would give `6 * sum + 135`).  Here we prove the
sharp bound: `consume` with a `skip` handler costs exactly `5 * l.length + 7`
(`consumeLoop_skip_le` plus the initial `set r eos`), so one `dropRgn` costs at most
`5 * l.length + 8`.  This is proved by a direct induction on the region, without going through the
general (slack) `consume` machinery.

The assembly lemma `dropRegions_le` iterates this over an arbitrary list of
(stack, marker, region) triples with pairwise distinct stacks.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib

open HvdH
open Work.IntLib.Div

/-! ## Sharp bounds for one region -/

/-- `consumeLoop k T r .skip` with the marker `T` of stack `k` as terminator: the glyphs of the
region `l` are popped one by one (the `skip` handler does nothing), then `T` is pushed back and the
register `r` is set to `Glyph.mk 0`, which stops the loop.  Cost: at most `5 * l.length + 6`. -/
theorem consumeLoop_skip_le (main : Cmd) (k : Stk) (T : Glyph) (r : Reg)
    (l bk : List Glyph) (s : State) (hT : ∀ g ∈ l, g ≠ T)
    (hk : s.stk k = l ++ T :: bk) (hr : s.reg r = Glyph.eos) :
    ∃ (s' : State) (n : ℕ), Eval main (consumeLoop k T r (Cmd.skip : Cmd)) s s' n ∧
      n ≤ 5 * l.length + 6 ∧ s'.stk k = T :: bk ∧ s'.reg r = Glyph.mk 0 ∧
      (∀ j : Stk, j ≠ k → s'.stk j = s.stk j) := by
  induction l generalizing s with
  | nil =>
    have hsk : s.stk k = T :: bk := by simpa using hk
    let s1 : State := ⟨Function.update s.reg r T, Function.update s.stk k bk⟩
    have h1 : Eval main (.pop k r) s s1 1 := by
      have h := Eval.pop_cons (main := main) (k := k) (r := r) hsk
      simpa [s1] using h
    have hs1reg : s1.reg r = T := by simp [s1]
    let s2 : State := ⟨s1.reg, Function.update s1.stk k (s1.reg r :: s1.stk k)⟩
    have h2 : Eval main (.push k r) s1 s2 1 := by
      have h := Eval.push (main := main) k r s1
      simpa [s2] using h
    let s3 : State := ⟨Function.update s2.reg r (Glyph.mk 0), s2.stk⟩
    have h3 : Eval main (.set r (Glyph.mk 0)) s2 s3 1 := by
      have h := Eval.set (main := main) r (Glyph.mk 0) s2
      simpa [s3] using h
    have h23 : Eval main (.seq (.push k r) (.set r (Glyph.mk 0))) s1 s3 2 := Eval.seq h2 h3
    have hite : Eval main (.ite r T (.seq (.push k r) (.set r (Glyph.mk 0)))
        (.seq (Cmd.skip : Cmd) (.set r Glyph.eos))) s1 s3 3 := Eval.iteT hs1reg h23
    have hbody : Eval main (consumeStep k T r (Cmd.skip : Cmd)) s s3 4 := Eval.seq h1 hite
    have hs3reg : s3.reg r = Glyph.mk 0 := by simp [s3, s2]
    have hne : s3.reg r ≠ Glyph.eos := by rw [hs3reg]; decide
    have hloopF : Eval main (.loop r Glyph.eos (consumeStep k T r (Cmd.skip : Cmd))) s3 s3 1 :=
      Eval.loopF hne
    have hloop : Eval main (consumeLoop k T r (Cmd.skip : Cmd)) s s3 (4 + 1 + 1) :=
      Eval.loopT hr hbody hloopF
    refine ⟨s3, 4 + 1 + 1, hloop, by simp, ?_, hs3reg, ?_⟩
    · simp [s3, s2, s1]
    · intro j hj
      simp [s3, s2, s1, hj]
  | cons g rest ih =>
    have hgT : g ≠ T := hT g (by simp)
    have hsk : s.stk k = g :: (rest ++ T :: bk) := by simpa using hk
    let s1 : State := ⟨Function.update s.reg r g, Function.update s.stk k (rest ++ T :: bk)⟩
    have h1 : Eval main (.pop k r) s s1 1 := by
      have h := Eval.pop_cons (main := main) (k := k) (r := r) hsk
      simpa [s1] using h
    have hs1reg : s1.reg r = g := by simp [s1]
    let s3 : State := ⟨Function.update s1.reg r Glyph.eos, s1.stk⟩
    have h2 : Eval main (Cmd.skip : Cmd) s1 s1 1 := Eval.skip s1
    have h3 : Eval main (.set r Glyph.eos) s1 s3 1 := by
      have h := Eval.set (main := main) r Glyph.eos s1
      simpa [s3] using h
    have h23 : Eval main (.seq (Cmd.skip : Cmd) (.set r Glyph.eos)) s1 s3 2 := Eval.seq h2 h3
    have hite : Eval main (.ite r T (.seq (.push k r) (.set r (Glyph.mk 0)))
        (.seq (Cmd.skip : Cmd) (.set r Glyph.eos))) s1 s3 3 :=
      Eval.iteF (by rw [hs1reg]; exact hgT) h23
    have hbody : Eval main (consumeStep k T r (Cmd.skip : Cmd)) s s3 4 := Eval.seq h1 hite
    have hs3stk : s3.stk k = rest ++ T :: bk := by simp [s3, s1]
    have hs3reg : s3.reg r = Glyph.eos := by simp [s3]
    have hT' : ∀ g' ∈ rest, g' ≠ T := fun g' hg' => hT g' (List.mem_cons_of_mem g hg')
    obtain ⟨s4, n4, hev4, hn4, hstk4, hreg4, hoth4⟩ := ih s3 hT' hs3stk hs3reg
    have hloop : Eval main (consumeLoop k T r (Cmd.skip : Cmd)) s s4 (4 + n4 + 1) :=
      Eval.loopT hr hbody hev4
    refine ⟨s4, 4 + n4 + 1, hloop, ?_, hstk4, hreg4, ?_⟩
    · have hl : 4 + n4 + 1 ≤ 5 * (g :: rest).length + 6 := by
        simp only [List.length_cons]
        omega
      exact hl
    · intro j hj
      rw [hoth4 j hj]
      simp [s3, s1, hj]

/-- `consume k T r .skip`: same as `consumeLoop_skip_le` with the initial `set r eos`.
Cost: at most `5 * l.length + 7`. -/
theorem consume_skip_le (main : Cmd) (k : Stk) (T : Glyph) (r : Reg)
    (l bk : List Glyph) (s : State) (hT : ∀ g ∈ l, g ≠ T)
    (hk : s.stk k = l ++ T :: bk) :
    ∃ (s' : State) (n : ℕ), Eval main (consume k T r (Cmd.skip : Cmd)) s s' n ∧
      n ≤ 5 * l.length + 7 ∧ s'.stk k = T :: bk ∧ s'.reg r = Glyph.mk 0 ∧
      (∀ j : Stk, j ≠ k → s'.stk j = s.stk j) := by
  let s0 : State := ⟨Function.update s.reg r Glyph.eos, s.stk⟩
  have h1 : Eval main (.set r Glyph.eos) s s0 1 := by
    have h := Eval.set (main := main) r Glyph.eos s
    simpa [s0] using h
  have hs0stk : s0.stk k = l ++ T :: bk := by simp [s0, hk]
  have hs0reg : s0.reg r = Glyph.eos := by simp [s0]
  obtain ⟨s', n, hev, hn, hstk, hreg, hoth⟩ :=
    consumeLoop_skip_le main k T r l bk s0 hT hs0stk hs0reg
  refine ⟨s', 1 + n, ?_, by omega, hstk, hreg, ?_⟩
  · have h := Eval.seq h1 hev
    simpa [consume] using h
  · intro j hj
    rw [hoth j hj]

/-- `dropRgn k T r` costs at most `5 * l.length + 8` (instead of the generic
`6 * (l.length + 1) + 9`), and leaves `bk` behind. -/
theorem dropRgn_le (main : Cmd) (k : Stk) (T : Glyph) (r : Reg)
    (l bk : List Glyph) (s : State) (hT : ∀ g ∈ l, g ≠ T)
    (hk : s.stk k = l ++ T :: bk) :
    ∃ (s' : State) (n : ℕ), Eval main (dropRgn k T r) s s' n ∧ n ≤ 5 * l.length + 8 ∧
      s'.stk k = bk ∧ (∀ j : Stk, j ≠ k → s'.stk j = s.stk j) := by
  obtain ⟨s1, n, hev, hn, hstk, hreg, hoth⟩ := consume_skip_le main k T r l bk s hT hk
  refine ⟨⟨Function.update s1.reg r T, Function.update s1.stk k bk⟩, n + 1, ?_, by omega, ?_, ?_⟩
  · have hpop : Eval main (.pop k r) s1
        ⟨Function.update s1.reg r T, Function.update s1.stk k bk⟩ 1 := Eval.pop_cons hstk
    have h := Eval.seq hev hpop
    simpa [dropRgn] using h
  · simp
  · intro j hj
    show (Function.update s1.stk k bk) j = s.stk j
    rw [Function.update_of_ne hj, hoth j hj]

/-! ## The nine parts of `cleanup` -/

/-- The nine (stack, marker, region) triples of `Div.cleanup`. -/
def cleanupParts (lP lB lR lQ lS lC lD lX lY : List Glyph) : List (Stk × Glyph × List Glyph) :=
  [(stP, gP, lP), (stB, gB, lB), (stR, gR, lR), (stQ, gQ, lQ), (stS, gS, lS),
   (stC, gC, lC), (stD, gD, lD), (stX, gX, lX), (stY, gY, lY)]

/-- `cleanup` is the sequential composition of the drops prescribed by `cleanupParts`. -/
theorem cleanup_eq_seqs (lP lB lR lQ lS lC lD lX lY : List Glyph) :
    seqs ((cleanupParts lP lB lR lQ lS lC lD lX lY).map fun p => dropRgn p.1 p.2.1 rgT) =
      Div.cleanup := rfl

/-- Iterating `dropRgn_le` over a list of parts with pairwise distinct stacks. -/
theorem dropRegions_le (main : Cmd) (b0 : State) :
    ∀ (ps : List (Stk × Glyph × List Glyph)) (s : State),
      (ps.map (fun p => p.1)).Nodup →
      (∀ p ∈ ps, s.stk p.1 = p.2.2 ++ p.2.1 :: b0.stk p.1) →
      (∀ p ∈ ps, ∀ g ∈ p.2.2, g ≠ p.2.1) →
      ∃ (s' : State) (n : ℕ),
        Eval main (seqs (ps.map fun p => dropRgn p.1 p.2.1 rgT)) s s' n ∧
        n ≤ 5 * (ps.map (fun p => p.2.2.length)).sum + 12 * ps.length + 1 ∧
        (∀ p ∈ ps, s'.stk p.1 = b0.stk p.1) ∧
        (∀ j : Stk, (∀ p ∈ ps, j ≠ p.1) → s'.stk j = s.stk j) := by
  intro ps
  induction ps with
  | nil =>
    intro s _ _ _
    refine ⟨s, 1, ?_, by simp, by simp, by simp⟩
    simpa using (Eval.skip s : Eval main Cmd.skip s s 1)
  | cons p ps ih =>
    intro s hnd hreg hglyph
    have hnd0 : (p.1 :: ps.map (fun p => p.1)).Nodup := by simpa using hnd
    obtain ⟨hnotin, hnd'⟩ := List.nodup_cons.mp hnd0
    have hstep : ∀ q ∈ ps, q.1 ≠ p.1 := by
      intro q hq heq
      have hmem : q.1 ∈ ps.map (fun p => p.1) := List.mem_map.mpr ⟨q, hq, rfl⟩
      rw [heq] at hmem
      exact hnotin hmem
    obtain ⟨s1, n1, hev1, hn1, hstk1, hoth1⟩ :=
      dropRgn_le main p.1 p.2.1 rgT p.2.2 (b0.stk p.1) s
        (hglyph p (by simp)) (hreg p (by simp))
    obtain ⟨s2, n2, hev2, hn2, hstk2, hoth2⟩ := ih s1 hnd'
      (fun q hq => by rw [hoth1 q.1 (hstep q hq)]; exact hreg q (List.mem_cons_of_mem p hq))
      (fun q hq g hg => hglyph q (List.mem_cons_of_mem p hq) g hg)
    refine ⟨s2, n1 + n2, ?_, ?_, ?_, ?_⟩
    · have h := Eval.seq hev1 hev2
      simpa using h
    · simp only [List.map_cons, List.sum_cons, List.length_cons] at hn1 hn2 ⊢
      omega
    · intro q hq
      rcases List.mem_cons.mp hq with heq | hq'
      · rw [heq]
        exact (hoth2 p.1 (fun r hr h => hstep r hr h.symm)).trans hstk1
      · exact hstk2 q hq'
    · intro j hj
      rw [hoth2 j (fun r hr => hj r (List.mem_cons_of_mem p hr))]
      exact hoth1 j (hj p (by simp))

theorem cleanupSpec (main : HvdH.Cmd) (b0 : HvdH.State) (s : HvdH.State)
    (lP lB lR lQ lS lC lD lX lY : List HvdH.Glyph)
    (hP : s.stk Work.IntLib.Div.stP = lP ++ [Work.IntLib.gP] ++ b0.stk Work.IntLib.Div.stP)
    (hB : s.stk Work.IntLib.Div.stB = lB ++ [Work.IntLib.gB] ++ b0.stk Work.IntLib.Div.stB)
    (hR : s.stk Work.IntLib.Div.stR = lR ++ [Work.IntLib.gR] ++ b0.stk Work.IntLib.Div.stR)
    (hQ : s.stk Work.IntLib.Div.stQ = lQ ++ [Work.IntLib.gQ] ++ b0.stk Work.IntLib.Div.stQ)
    (hS : s.stk Work.IntLib.Div.stS = lS ++ [Work.IntLib.gS] ++ b0.stk Work.IntLib.Div.stS)
    (hC : s.stk Work.IntLib.Div.stC = lC ++ [Work.IntLib.gC] ++ b0.stk Work.IntLib.Div.stC)
    (hD : s.stk Work.IntLib.Div.stD = lD ++ [Work.IntLib.gD] ++ b0.stk Work.IntLib.Div.stD)
    (hX : s.stk Work.IntLib.Div.stX = lX ++ [Work.IntLib.gX] ++ b0.stk Work.IntLib.Div.stX)
    (hY : s.stk Work.IntLib.Div.stY = lY ++ [Work.IntLib.gY] ++ b0.stk Work.IntLib.Div.stY)
    (nP : ∀ g ∈ lP, g ≠ Work.IntLib.gP) (nB : ∀ g ∈ lB, g ≠ Work.IntLib.gB)
    (nR : ∀ g ∈ lR, g ≠ Work.IntLib.gR) (nQ : ∀ g ∈ lQ, g ≠ Work.IntLib.gQ)
    (nS : ∀ g ∈ lS, g ≠ Work.IntLib.gS) (nC : ∀ g ∈ lC, g ≠ Work.IntLib.gC)
    (nD : ∀ g ∈ lD, g ≠ Work.IntLib.gD) (nX : ∀ g ∈ lX, g ≠ Work.IntLib.gX)
    (nY : ∀ g ∈ lY, g ≠ Work.IntLib.gY)
    (hoth : ∀ k : HvdH.Stk, 10 ≤ k.val → s.stk k = b0.stk k) :
    ∃ s' n, HvdH.Eval main Work.IntLib.Div.cleanup s s' n ∧
      n ≤ 5 * (lP.length + lB.length + lR.length + lQ.length + lS.length + lC.length +
        lD.length + lX.length + lY.length) + 117 ∧
      (∀ k : HvdH.Stk, k ≠ 0 → s'.stk k = b0.stk k) := by
  have hnodup : ((cleanupParts lP lB lR lQ lS lC lD lX lY).map (fun p => p.1)).Nodup := by
    simp only [cleanupParts, List.map_cons, List.map_nil]
    decide
  obtain ⟨s', n, hev, hn, hstk, hoth'⟩ :=
    dropRegions_le main b0 (cleanupParts lP lB lR lQ lS lC lD lX lY) s hnodup
      (by
        intro p hp
        simp only [cleanupParts, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · simpa [List.append_assoc] using hP
        · simpa [List.append_assoc] using hB
        · simpa [List.append_assoc] using hR
        · simpa [List.append_assoc] using hQ
        · simpa [List.append_assoc] using hS
        · simpa [List.append_assoc] using hC
        · simpa [List.append_assoc] using hD
        · simpa [List.append_assoc] using hX
        · simpa [List.append_assoc] using hY)
      (by
        intro p hp g hg
        simp only [cleanupParts, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact nP g hg
        · exact nB g hg
        · exact nR g hg
        · exact nQ g hg
        · exact nS g hg
        · exact nC g hg
        · exact nD g hg
        · exact nX g hg
        · exact nY g hg)
  have hev' : HvdH.Eval main Work.IntLib.Div.cleanup s s' n := by
    rw [← cleanup_eq_seqs lP lB lR lQ lS lC lD lX lY]
    exact hev
  refine ⟨s', n, hev', ?_, ?_⟩
  · simp only [cleanupParts, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.length_cons, List.length_nil] at hn
    omega
  · have hge10 : ∀ p ∈ cleanupParts lP lB lR lQ lS lC lD lX lY, ∀ j : Stk,
        10 ≤ j.val → j ≠ p.1 := by
      intro p hp j hj hjp
      have hm : p.1 ∈ [stP, stB, stR, stQ, stS, stC, stD, stX, stY] := by
        simpa [cleanupParts] using List.mem_map.mpr ⟨p, hp, rfl⟩
      have hlt : p.1.val < 10 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with h | h | h | h | h | h | h | h | h <;> (rw [h]; decide)
      have hjv : j.val = p.1.val := by rw [hjp]
      omega
    intro k hk
    fin_cases k
    · exact absurd rfl hk
    · exact hstk (stP, gP, lP) (by simp [cleanupParts])
    · exact hstk (stB, gB, lB) (by simp [cleanupParts])
    · exact hstk (stR, gR, lR) (by simp [cleanupParts])
    · exact hstk (stQ, gQ, lQ) (by simp [cleanupParts])
    · exact hstk (stS, gS, lS) (by simp [cleanupParts])
    · exact hstk (stC, gC, lC) (by simp [cleanupParts])
    · exact hstk (stD, gD, lD) (by simp [cleanupParts])
    · exact hstk (stX, gX, lX) (by simp [cleanupParts])
    · exact hstk (stY, gY, lY) (by simp [cleanupParts])
    · exact (hoth' 10 (fun p hp => hge10 p hp 10 (by decide))).trans (hoth 10 (by decide))
    · exact (hoth' 11 (fun p hp => hge10 p hp 11 (by decide))).trans (hoth 11 (by decide))
    · exact (hoth' 12 (fun p hp => hge10 p hp 12 (by decide))).trans (hoth 12 (by decide))
    · exact (hoth' 13 (fun p hp => hge10 p hp 13 (by decide))).trans (hoth 13 (by decide))
    · exact (hoth' 14 (fun p hp => hge10 p hp 14 (by decide))).trans (hoth 14 (by decide))
    · exact (hoth' 15 (fun p hp => hge10 p hp 15 (by decide))).trans (hoth 15 (by decide))

end Work.IntLib
