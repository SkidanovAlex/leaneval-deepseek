import Mathlib
import Submission.Work.Transform.pwMaxDefs

namespace Work.Transform

/-- The "running maximum survives" branch of the max phase, run by the already-defined program
`Work.Transform.Pw.loseProg sp sA bA bB mx` (`Submission.Work.Transform.pwMaxDefs`).

This is the state left by the buffered scan (`pwScanBv`): `sp` holds the bits of the current
element most significant first above a marker, `sA` resp. `mx` hold the unconsumed parts of the two
bit strings, and `bA` resp. `bB` the consumed prefixes of the element resp. of the running maximum
(reversed, above the marker the scan pushed on the buffer).  The five stacks `sp, sA, bA, bB, mx`
are pairwise distinct.  The branch pushes the consumed prefix of the maximum from `bB` back onto
`mx` (restoring `mx` exactly, since `B.take k ++ B.drop k = B`), drops the buffer's marker, and
empties `sA`, `bA`, `sp` down to their markers.  The cost is bounded by `K * (A.length + 1)`
(`k ≤ A.length` and `|B.take k| ≤ k`). -/
theorem pwMaxLose (sp sA bA bB mx : HvdH.Stk) (hnd : [sp, sA, bA, bB, mx].Nodup) :
    ∃ (K : ℕ),
    ∀ (main : HvdH.Cmd) (A B : List Bool) (k : ℕ) (Osp OsA ObA ObB R : List HvdH.Glyph)
      (s : HvdH.State),
      s.stk sp = A.reverse.map HvdH.Glyph.bit ++ Work.Transform.Pw.gM :: Osp →
      s.stk sA = (A.drop k).map HvdH.Glyph.bit ++ Work.Transform.Pw.gM :: OsA →
      s.stk bA = ((A.take k).map HvdH.Glyph.bit).reverse ++ Work.Transform.Pw.gM :: ObA →
      s.stk bB = ((B.take k).map HvdH.Glyph.bit).reverse ++ Work.Transform.Pw.gM :: ObB →
      s.stk mx = (B.drop k).map HvdH.Glyph.bit ++ Work.Transform.Pw.gM :: R →
      k ≤ A.length →
      ∃ s' n, HvdH.Eval main (Work.Transform.Pw.loseProg sp sA bA bB mx) s s' n ∧
        n ≤ K * (A.length + 1) ∧
        s'.stk mx = B.map HvdH.Glyph.bit ++ Work.Transform.Pw.gM :: R ∧
        s'.stk sp = Osp ∧ s'.stk sA = OsA ∧ s'.stk bA = ObA ∧ s'.stk bB = ObB ∧
        (∀ j : HvdH.Stk, j ≠ sp → j ≠ sA → j ≠ bA → j ≠ bB → j ≠ mx →
          s'.stk j = s.stk j) := by
  -- The constant only has to absorb the constant overheads `5 * |B.take k| ≤ 5 * k`,
  -- `3 * (4 * |A| + 9)` and the four primitive steps.
  refine ⟨40, ?_⟩
  intro main A B k Osp OsA ObA ObB R s hsp hsA hbA hbB hmx hk
  -- pairwise distinctness of the five stacks
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_true, not_or] at hnd
  obtain ⟨⟨h_sp_sA, h_sp_bA, h_sp_bB, h_sp_mx⟩, ⟨h_sA_bA, h_sA_bB, h_sA_mx⟩,
    ⟨h_bA_bB, h_bA_mx⟩, h_bB_mx⟩ := hnd
  have hmx_bB : mx ≠ bB := Ne.symm h_bB_mx
  have hmx_sp : mx ≠ sp := Ne.symm h_sp_mx
  have hmx_bA : mx ≠ bA := Ne.symm h_bA_mx
  have hmx_sA : mx ≠ sA := Ne.symm h_sA_mx
  have hsA_sp : sA ≠ sp := Ne.symm h_sp_sA
  have hbA_sp : bA ≠ sp := Ne.symm h_sp_bA
  have hbB_sp : bB ≠ sp := Ne.symm h_sp_bB
  have hbA_sA : bA ≠ sA := Ne.symm h_sA_bA
  have hbB_bA : bB ≠ bA := Ne.symm h_bA_bB
  have hbB_sA : bB ≠ sA := Ne.symm h_sA_bB
  -- `B.take k ++ B.drop k = B`, pushed through `map`
  have hBsplit : (B.take k).map HvdH.Glyph.bit ++ (B.drop k).map HvdH.Glyph.bit
      = B.map HvdH.Glyph.bit := by rw [← List.map_append, List.take_append_drop]
  -- ## Step 1: `tLoop bB gM mx mB` moves the consumed prefix of the maximum back onto `mx`
  let gs : List HvdH.Glyph := ((B.take k).map HvdH.Glyph.bit).reverse
  have hgs : ∀ g ∈ gs, g ≠ Work.Transform.Pw.gM := by
    intro g hg
    have hg' : g ∈ (B.take k).map HvdH.Glyph.bit := by simpa [gs] using hg
    obtain ⟨b, _, hb⟩ := List.mem_map.mp hg'
    rw [← hb]; exact Work.Transform.Pw.bit_ne_gM b
  let s1 : HvdH.State :=
    Work.Transform.Pw.tSt bB Work.Transform.Pw.gM mx Work.Transform.Pw.mB gs ObB s
  have e1 : HvdH.Eval main
      (Work.Transform.Pw.tLoop bB Work.Transform.Pw.gM mx Work.Transform.Pw.mB) s s1
      (5 * gs.length + 7) := by
    show HvdH.Eval main
      (Work.Transform.Pw.tLoop bB Work.Transform.Pw.gM mx Work.Transform.Pw.mB) s
      (Work.Transform.Pw.tSt bB Work.Transform.Pw.gM mx Work.Transform.Pw.mB gs ObB s)
      (5 * gs.length + 7)
    exact Work.Transform.Pw.tLoop_eval main bB Work.Transform.Pw.gM mx Work.Transform.Pw.mB
      hmx_bB Work.Transform.Pw.gM_ne_eos gs ObB s hbB hgs
  have hs1bB : s1.stk bB = Work.Transform.Pw.gM :: ObB := by
    show (Work.Transform.Pw.tSt bB Work.Transform.Pw.gM mx Work.Transform.Pw.mB gs ObB s).stk bB
      = _
    rw [Work.Transform.Pw.tSt_stk_k _ _ _ _ _ _ _ hmx_bB]
  have hs1mx : s1.stk mx = B.map HvdH.Glyph.bit ++ Work.Transform.Pw.gM :: R := by
    show (Work.Transform.Pw.tSt bB Work.Transform.Pw.gM mx Work.Transform.Pw.mB gs ObB s).stk mx
      = _
    rw [Work.Transform.Pw.tSt_stk_dst,
      show gs.reverse = (B.take k).map HvdH.Glyph.bit from by simp [gs], hmx,
      ← List.append_assoc, hBsplit]
  have hs1o : ∀ j, j ≠ bB → j ≠ mx → s1.stk j = s.stk j := by
    intro j hj1 hj2
    show (Work.Transform.Pw.tSt bB Work.Transform.Pw.gM mx Work.Transform.Pw.mB gs ObB s).stk j
      = s.stk j
    exact Work.Transform.Pw.tSt_stk_ne' bB Work.Transform.Pw.gM mx Work.Transform.Pw.mB gs ObB s
      hj1 hj2
  -- ## Step 2: drop the buffer marker
  let s2 : HvdH.State := HvdH.State.tPop s1 bB Work.Transform.Pw.mA
  have e2 : HvdH.Eval main (.pop bB Work.Transform.Pw.mA) s1 s2 1 := by
    show HvdH.Eval main (.pop bB Work.Transform.Pw.mA) s1
      (HvdH.State.tPop s1 bB Work.Transform.Pw.mA) 1
    exact Work.Kernel.eval_pop main bB Work.Transform.Pw.mA s1
  have hs2bB : s2.stk bB = ObB := by
    show (HvdH.State.tPop s1 bB Work.Transform.Pw.mA).stk bB = ObB
    rw [Work.Transform.Pw.tPop_stk, if_pos rfl, hs1bB]
    rfl
  have hs2o : ∀ j, j ≠ bB → s2.stk j = s1.stk j := by
    intro j hj
    show (HvdH.State.tPop s1 bB Work.Transform.Pw.mA).stk j = s1.stk j
    rw [Work.Transform.Pw.tPop_stk, if_neg hj]
  -- ## Step 3: empty `sA` (the unconsumed part of the element) down to its marker
  have hgs3 : ∀ g ∈ (A.drop k).map HvdH.Glyph.bit, g ≠ Work.Transform.Pw.gM := by
    intro g hg
    obtain ⟨b, _, hb⟩ := List.mem_map.mp hg
    rw [← hb]; exact Work.Transform.Pw.bit_ne_gM b
  have hs2sA : s2.stk sA = (A.drop k).map HvdH.Glyph.bit ++ Work.Transform.Pw.gM :: OsA := by
    rw [hs2o sA h_sA_bB, hs1o sA h_sA_bB h_sA_mx]
    exact hsA
  obtain ⟨s3, n3, e3, hn3, hs3sA, hs3o, _⟩ :=
    Work.Transform.Pw.dropMarked_eval main sA Work.Transform.Pw.mA Work.Transform.Pw.mB
      ((A.drop k).map HvdH.Glyph.bit) OsA hgs3 s2 hs2sA
  -- ## Step 4: empty the element's buffer `bA`
  have hgs4 : ∀ g ∈ ((A.take k).map HvdH.Glyph.bit).reverse, g ≠ Work.Transform.Pw.gM := by
    intro g hg
    have hg' : g ∈ (A.take k).map HvdH.Glyph.bit := by simpa using hg
    obtain ⟨b, _, hb⟩ := List.mem_map.mp hg'
    rw [← hb]; exact Work.Transform.Pw.bit_ne_gM b
  have hs3bA : s3.stk bA
      = ((A.take k).map HvdH.Glyph.bit).reverse ++ Work.Transform.Pw.gM :: ObA := by
    rw [hs3o bA hbA_sA, hs2o bA h_bA_bB, hs1o bA h_bA_bB h_bA_mx]
    exact hbA
  obtain ⟨s4, n4, e4, hn4, hs4bA, hs4o, _⟩ :=
    Work.Transform.Pw.dropMarked_eval main bA Work.Transform.Pw.mA Work.Transform.Pw.mB
      (((A.take k).map HvdH.Glyph.bit).reverse) ObA hgs4 s3 hs3bA
  -- ## Step 5: empty the element's bits `sp`
  have hgs5 : ∀ g ∈ A.reverse.map HvdH.Glyph.bit, g ≠ Work.Transform.Pw.gM := by
    intro g hg
    have hg' : g ∈ A.map HvdH.Glyph.bit := by simpa using hg
    obtain ⟨b, _, hb⟩ := List.mem_map.mp hg'
    rw [← hb]; exact Work.Transform.Pw.bit_ne_gM b
  have hs4sp : s4.stk sp = A.reverse.map HvdH.Glyph.bit ++ Work.Transform.Pw.gM :: Osp := by
    rw [hs4o sp h_sp_bA, hs3o sp h_sp_sA, hs2o sp h_sp_bB, hs1o sp h_sp_bB h_sp_mx]
    exact hsp
  obtain ⟨s5, n5, e5, hn5, hs5sp, hs5o, _⟩ :=
    Work.Transform.Pw.dropMarked_eval main sp Work.Transform.Pw.mA Work.Transform.Pw.mB
      (A.reverse.map HvdH.Glyph.bit) Osp hgs5 s4 hs4sp
  -- ## Assembly
  have eall : HvdH.Eval main (Work.Transform.Pw.loseProg sp sA bA bB mx) s s5
      ((5 * gs.length + 7) + (1 + (n3 + (n4 + n5)))) :=
    HvdH.Eval.seq e1 (HvdH.Eval.seq e2 (HvdH.Eval.seq e3 (HvdH.Eval.seq e4 e5)))
  have hmx5 : s5.stk mx = B.map HvdH.Glyph.bit ++ Work.Transform.Pw.gM :: R := by
    rw [hs5o mx hmx_sp, hs4o mx hmx_bA, hs3o mx hmx_sA, hs2o mx hmx_bB, hs1mx]
  have hsA5 : s5.stk sA = OsA := by
    rw [hs5o sA hsA_sp, hs4o sA h_sA_bA]
    exact hs3sA
  have hbA5 : s5.stk bA = ObA := by
    rw [hs5o bA hbA_sp]
    exact hs4bA
  have hbB5 : s5.stk bB = ObB := by
    rw [hs5o bB hbB_sp, hs4o bB hbB_bA, hs3o bB hbB_sA]
    exact hs2bB
  have hfr : ∀ j : HvdH.Stk, j ≠ sp → j ≠ sA → j ≠ bA → j ≠ bB → j ≠ mx →
      s5.stk j = s.stk j := by
    intro j hj_sp hj_sA hj_bA hj_bB hj_mx
    rw [hs5o j hj_sp, hs4o j hj_bA, hs3o j hj_sA, hs2o j hj_bB, hs1o j hj_bB hj_mx]
  refine ⟨s5, (5 * gs.length + 7) + (1 + (n3 + (n4 + n5))), eall, ?_, hmx5, hs5sp, hsA5,
    hbA5, hbB5, hfr⟩
  -- ## Cost
  have hlen1 : gs.length ≤ A.length := by
    simp only [gs, List.length_reverse, List.length_map]
    exact le_trans (List.length_take_le k B) hk
  have hn3' : n3 ≤ 4 * A.length + 9 := by
    refine le_trans hn3 ?_
    simp only [List.length_map, List.length_drop]
    omega
  have hn4' : n4 ≤ 4 * A.length + 9 := by
    refine le_trans hn4 ?_
    simp only [List.length_reverse, List.length_map]
    have := List.length_take_le k A
    omega
  have hn5' : n5 ≤ 4 * A.length + 9 := by
    refine le_trans hn5 ?_
    simp only [List.length_map, List.length_reverse]
    omega
  omega

end Work.Transform
