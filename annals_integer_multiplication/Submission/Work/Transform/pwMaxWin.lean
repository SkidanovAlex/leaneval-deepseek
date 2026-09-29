import Mathlib
import Submission.Work.Transform.pwMaxDefs

namespace Work.Transform

open HvdH

/-- A `Nodup` list of five elements is pairwise distinct. -/
theorem nodup5 {α : Type*} [DecidableEq α] {a b c d e : α} (h : [a, b, c, d, e].Nodup) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ c ≠ d ∧ c ≠ e ∧ d ≠ e := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or,
    List.nodup_nil, and_true] at h
  tauto

namespace Pw

/-- `dropMarked` with an explicit resulting state (the bare `dLoop` + `pop` run). -/
theorem dropMarked_ev (main : Cmd) (src : Stk) (rA rB : Reg)
    (gs below : List Glyph) (hgs : ∀ g ∈ gs, g ≠ gM) (s : State)
    (hstk : s.stk src = gs ++ gM :: below) :
    Eval main (dropMarked src rA rB) s (State.tPop (dSt src gM rB below s) src rA)
      ((4 * gs.length + 7) + 1) :=
  Eval.seq (dLoop_eval main src gM rB gM_ne_eos gs below s hstk hgs)
    (Work.Kernel.eval_pop main src rA (dSt src gM rB below s))

/-- `dropMarked src rA rB` leaves `below` on `src`. -/
theorem tPop_dSt_stk (k : Stk) (tg : Glyph) (rA rB : Reg) (below : List Glyph) (s : State) :
    (State.tPop (dSt k tg rB below s) k rA).stk k = below := by
  rw [tPop_stk, if_pos rfl, dSt_stk_k]
  rfl

end Pw

/-- The `gGt` branch of the max phase, run by the already-defined program
`Work.Transform.Pw.winProg sp sA bA bB mx` (`Submission.Work.Transform.pwMaxDefs`, itself a
composition of the toolkit words `Pw.dropMarked`, `Pw.dLoop` and `Pw.tLoop`).

This is the state left by the buffered scan (`pwScanBv`): `sp` holds the bits of the current
element most significant first above a marker, `sA` resp. `mx` hold the unconsumed parts of the two
bit strings, and `bA` resp. `bB` the consumed prefixes of the element resp. of the running maximum
(reversed, above the marker that the scan pushed on the buffer).  The five stacks `sp, sA, bA, bB,
mx` are pairwise distinct.  Since the element is strictly larger than the running maximum the latter
has at most as many bits (`B.length ≤ A.length`), and the branch drains `mx`, moves the bits from
`sp` onto `mx` (they arrive least significant first), and empties `sp`, `sA`, `bA`, `bB` down to
their markers.  The cost is bounded by `K * (A.length + 1)`. -/
theorem pwMaxWin (sp sA bA bB mx : HvdH.Stk) (hnd : [sp, sA, bA, bB, mx].Nodup) :
    ∃ (K : ℕ),
    ∀ (main : HvdH.Cmd) (A B : List Bool) (k : ℕ) (Osp OsA ObA ObB R : List HvdH.Glyph)
      (s : HvdH.State),
      s.stk sp = A.reverse.map HvdH.Glyph.bit ++ Work.Transform.Pw.gM :: Osp →
      s.stk sA = (A.drop k).map HvdH.Glyph.bit ++ Work.Transform.Pw.gM :: OsA →
      s.stk bA = ((A.take k).map HvdH.Glyph.bit).reverse ++ Work.Transform.Pw.gM :: ObA →
      s.stk bB = ((B.take k).map HvdH.Glyph.bit).reverse ++ Work.Transform.Pw.gM :: ObB →
      s.stk mx = (B.drop k).map HvdH.Glyph.bit ++ Work.Transform.Pw.gM :: R →
      B.length ≤ A.length →
      ∃ s' n, HvdH.Eval main (Work.Transform.Pw.winProg sp sA bA bB mx) s s' n ∧
        n ≤ K * (A.length + 1) ∧
        s'.stk mx = A.map HvdH.Glyph.bit ++ Work.Transform.Pw.gM :: R ∧
        s'.stk sp = Osp ∧ s'.stk sA = OsA ∧ s'.stk bA = ObA ∧ s'.stk bB = ObB ∧
        (∀ j : HvdH.Stk, j ≠ sp → j ≠ sA → j ≠ bA → j ≠ bB → j ≠ mx →
          s'.stk j = s.stk j) := by
  refine ⟨60, ?_⟩
  intro main A B k Osp OsA ObA ObB R s hsp hsA hbA hbB hmx hlen
  obtain ⟨hsp_sA, hsp_bA, hsp_bB, hsp_mx, hsA_bA, hsA_bB, hsA_mx, hbA_bB, hbA_mx, hbB_mx⟩ :=
    nodup5 hnd
  -- the intermediate states of the six steps of `winProg`
  let s1 : State := State.tPop (Pw.dSt sA Pw.gM Pw.mB OsA s) sA Pw.mA
  let s2 : State := State.tPop (Pw.dSt bA Pw.gM Pw.mB ObA s1) bA Pw.mA
  let s3 : State := Pw.dSt mx Pw.gM Pw.mB R s2
  let s4 : State := Pw.tSt sp Pw.gM mx Pw.mB (A.reverse.map Glyph.bit) Osp s3
  let s5 : State := State.tPop (Pw.dSt sp Pw.gM Pw.mB Osp s4) sp Pw.mA
  let s6 : State := State.tPop (Pw.dSt bB Pw.gM Pw.mB ObB s5) bB Pw.mA
  -- what each step leaves alone
  have hs1 : ∀ j : Stk, j ≠ sA → s1.stk j = s.stk j := by
    intro j hj
    dsimp only [s1]
    rw [Pw.tPop_stk, if_neg hj, Pw.dSt_stk_ne' sA Pw.gM Pw.mB OsA s hj]
  have hs2 : ∀ j : Stk, j ≠ bA → s2.stk j = s1.stk j := by
    intro j hj
    dsimp only [s2]
    rw [Pw.tPop_stk, if_neg hj, Pw.dSt_stk_ne' bA Pw.gM Pw.mB ObA s1 hj]
  have hs3 : ∀ j : Stk, j ≠ mx → s3.stk j = s2.stk j := by
    intro j hj
    dsimp only [s3]
    rw [Pw.dSt_stk_ne' mx Pw.gM Pw.mB R s2 hj]
  have hs4 : ∀ j : Stk, j ≠ sp → j ≠ mx → s4.stk j = s3.stk j := by
    intro j h1 h2
    dsimp only [s4]
    rw [Pw.tSt_stk_ne' sp Pw.gM mx Pw.mB (A.reverse.map Glyph.bit) Osp s3 h1 h2]
  have hs5 : ∀ j : Stk, j ≠ sp → s5.stk j = s4.stk j := by
    intro j hj
    dsimp only [s5]
    rw [Pw.tPop_stk, if_neg hj, Pw.dSt_stk_ne' sp Pw.gM Pw.mB Osp s4 hj]
  have hs6 : ∀ j : Stk, j ≠ bB → s6.stk j = s5.stk j := by
    intro j hj
    dsimp only [s6]
    rw [Pw.tPop_stk, if_neg hj, Pw.dSt_stk_ne' bB Pw.gM Pw.mB ObB s5 hj]
  -- the preconditions of the intermediate steps, transported along the frames
  have hbA_s1 : s1.stk bA = ((A.take k).map Glyph.bit).reverse ++ Pw.gM :: ObA := by
    rw [hs1 bA (Ne.symm hsA_bA)]
    exact hbA
  have hmx_s2 : s2.stk mx = (B.drop k).map Glyph.bit ++ Pw.gM :: R := by
    rw [hs2 mx (Ne.symm hbA_mx), hs1 mx (Ne.symm hsA_mx)]
    exact hmx
  have hsp_s3 : s3.stk sp = A.reverse.map Glyph.bit ++ Pw.gM :: Osp := by
    rw [hs3 sp hsp_mx, hs2 sp hsp_bA, hs1 sp hsp_sA]
    exact hsp
  have hsp_s4 : s4.stk sp = Pw.gM :: Osp := by
    dsimp only [s4]
    rw [Pw.tSt_stk_k sp Pw.gM mx Pw.mB (A.reverse.map Glyph.bit) Osp s3 (Ne.symm hsp_mx)]
  have hbB_s5 : s5.stk bB = ((B.take k).map Glyph.bit).reverse ++ Pw.gM :: ObB := by
    rw [hs5 bB (Ne.symm hsp_bB), hs4 bB (Ne.symm hsp_bB) hbB_mx,
        hs3 bB hbB_mx, hs2 bB (Ne.symm hbA_bB), hs1 bB (Ne.symm hsA_bB)]
    exact hbB
  -- the six steps
  have e1 : Eval main (Pw.dropMarked sA Pw.mA Pw.mB) s s1 ((4 * (A.drop k).length + 7) + 1) := by
    have h := Pw.dropMarked_ev main sA Pw.mA Pw.mB ((A.drop k).map Glyph.bit) OsA
      (Pw.map_bit_ne_gM (A.drop k)) s hsA
    simpa only [List.length_map] using h
  have e2 : Eval main (Pw.dropMarked bA Pw.mA Pw.mB) s1 s2
      ((4 * (A.take k).length + 7) + 1) := by
    have h := Pw.dropMarked_ev main bA Pw.mA Pw.mB (((A.take k).map Glyph.bit).reverse) ObA
      (fun g hg => Pw.map_bit_ne_gM (A.take k) g (List.mem_reverse.mp hg)) s1 hbA_s1
    simpa only [List.length_map, List.length_reverse] using h
  have e3 : Eval main (Pw.dLoop mx Pw.gM Pw.mB) s2 s3 (4 * (B.drop k).length + 7) := by
    have h := Pw.dLoop_eval main mx Pw.gM Pw.mB Pw.gM_ne_eos ((B.drop k).map Glyph.bit) R s2
      hmx_s2 (Pw.map_bit_ne_gM (B.drop k))
    simpa only [List.length_map] using h
  have e4 : Eval main (Pw.tLoop sp Pw.gM mx Pw.mB) s3 s4 (5 * A.length + 7) := by
    have h := Pw.tLoop_eval main sp Pw.gM mx Pw.mB (Ne.symm hsp_mx) Pw.gM_ne_eos
      (A.reverse.map Glyph.bit) Osp s3 hsp_s3 (Pw.map_bit_ne_gM A.reverse)
    simpa only [List.length_map, List.length_reverse] using h
  have e5 : Eval main (Pw.dropMarked sp Pw.mA Pw.mB) s4 s5 8 := by
    have h := Pw.dropMarked_ev main sp Pw.mA Pw.mB ([] : List Glyph) Osp (by simp) s4 hsp_s4
    simpa using h
  have e6 : Eval main (Pw.dropMarked bB Pw.mA Pw.mB) s5 s6
      ((4 * (B.take k).length + 7) + 1) := by
    have h := Pw.dropMarked_ev main bB Pw.mA Pw.mB (((B.take k).map Glyph.bit).reverse) ObB
      (fun g hg => Pw.map_bit_ne_gM (B.take k) g (List.mem_reverse.mp hg)) s5 hbB_s5
    simpa only [List.length_map, List.length_reverse] using h
  refine ⟨s6, ((4 * (A.drop k).length + 7) + 1) + (((4 * (A.take k).length + 7) + 1)
      + ((4 * (B.drop k).length + 7) + ((5 * A.length + 7)
      + (8 + ((4 * (B.take k).length + 7) + 1))))), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 e6))))
  · have hA1 : (A.drop k).length ≤ A.length := by rw [List.length_drop]; omega
    have hA2 : (A.take k).length ≤ A.length := by rw [List.length_take]; omega
    have hB1 : (B.drop k).length ≤ B.length := by rw [List.length_drop]; omega
    have hB2 : (B.take k).length ≤ B.length := by rw [List.length_take]; omega
    omega
  · rw [hs6 mx (Ne.symm hbB_mx), hs5 mx (Ne.symm hsp_mx)]
    dsimp only [s4, s3]
    rw [Pw.tSt_stk_dst, Pw.dSt_stk_k, List.map_reverse, List.reverse_reverse]
  · rw [hs6 sp hsp_bB]
    show (State.tPop (Pw.dSt sp Pw.gM Pw.mB Osp s4) sp Pw.mA).stk sp = Osp
    exact Pw.tPop_dSt_stk sp Pw.gM Pw.mA Pw.mB Osp s4
  · rw [hs6 sA hsA_bB, hs5 sA (Ne.symm hsp_sA),
        hs4 sA (Ne.symm hsp_sA) hsA_mx, hs3 sA hsA_mx, hs2 sA hsA_bA]
    show (State.tPop (Pw.dSt sA Pw.gM Pw.mB OsA s) sA Pw.mA).stk sA = OsA
    exact Pw.tPop_dSt_stk sA Pw.gM Pw.mA Pw.mB OsA s
  · rw [hs6 bA hbA_bB, hs5 bA (Ne.symm hsp_bA),
        hs4 bA (Ne.symm hsp_bA) hbA_mx, hs3 bA hbA_mx]
    show (State.tPop (Pw.dSt bA Pw.gM Pw.mB ObA s1) bA Pw.mA).stk bA = ObA
    exact Pw.tPop_dSt_stk bA Pw.gM Pw.mA Pw.mB ObA s1
  · show (State.tPop (Pw.dSt bB Pw.gM Pw.mB ObB s5) bB Pw.mA).stk bB = ObB
    exact Pw.tPop_dSt_stk bB Pw.gM Pw.mA Pw.mB ObB s5
  · intro j hjsp hjsA hjbA hjbB hjmx
    rw [hs6 j hjbB, hs5 j hjsp, hs4 j hjsp hjmx,
        hs3 j hjmx, hs2 j hjbA, hs1 j hjsA]

end Work.Transform
