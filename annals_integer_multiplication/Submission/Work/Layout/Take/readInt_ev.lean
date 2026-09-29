import Mathlib
import Submission.Work.Layout.Take.Basic

/-!
# Reading the bits of the integer on top of stack `0`

`readIntProg` pushes a frame marker `gMark` on `sTmp`, discards the sign glyph of the integer on
top of stack `0`, then reads its bits one by one (pushing each on `sTmp`), stops at `iend`, and
finally moves the buffered bits down to `sBit` with `mvB` (which reverses them again, restoring
the least-significant-bit-first order).

`readInt_ev` states the resulting `Ev` with its cost: the loop makes `|G| + 1` iterations for a
bit string `G`, each of cost at most `5` in the `loopRuns` accounting.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.Layout

open HvdH

/-- every glyph of a bit string differs from `iend` -/
theorem ne_iend_of_mem_bitsG_x {l : List Bool} {h : Glyph} (hh : h ∈ bitsG_x l) : h ≠ Glyph.iend := by
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hh
  intro hc
  cases hc

/-- one iteration of the bit-reading loop, on the `iend` terminator: stop -/
theorem riBody_iend (main : Cmd) {g : Reg → Glyph} {X : Stk → List Glyph} {A : List Glyph}
    (h0 : X 0 = Glyph.iend :: A) :
    ∃ s' n, Ev main readIntBody ⟨g, X⟩ s' n ∧ n ≤ 3 ∧
      s'.stk 0 = A ∧ s'.stk sTmp = X sTmp ∧ s'.reg rG = Glyph.eos := by
  have h1 : Ev main (.pop 0 rE_x) ⟨g, X⟩
      ⟨Function.update g rE_x Glyph.iend, Function.update X 0 A⟩ 1 := by
    simpa [h0] using ev_pop' main 0 rE_x g X
  have h2 : Ev main (.ite rE_x Glyph.iend (.set rG Glyph.eos) (seqs [.push sTmp rE_x, .set rG gCont_x]))
      ⟨Function.update g rE_x Glyph.iend, Function.update X 0 A⟩
      ⟨Function.update (Function.update g rE_x Glyph.iend) rG Glyph.eos, Function.update X 0 A⟩ 2 :=
    Ev.iteT rfl (ev_set' main rG Glyph.eos _ _)
  have hmain : Ev main readIntBody ⟨g, X⟩
      ⟨Function.update (Function.update g rE_x Glyph.iend) rG Glyph.eos, Function.update X 0 A⟩ 3 := by
    unfold readIntBody
    simp only [seqs]
    exact Ev.seq' h1 h2 (C := 3) (by omega)
  refine ⟨_, _, hmain, by omega, ?_, ?_, ?_⟩
  · simp
  · simp [Function.update_of_ne (show sTmp ≠ (0 : Stk) by decide)]
  · simp

/-- one iteration of the bit-reading loop, on a bit glyph: buffer it on `sTmp` -/
theorem riBody_miss (main : Cmd) {g : Reg → Glyph} {X : Stk → List Glyph} {h : Glyph}
    {A : List Glyph} (hh : h ≠ Glyph.iend) (h0 : X 0 = h :: A) :
    ∃ s' n, Ev main readIntBody ⟨g, X⟩ s' n ∧ n ≤ 4 ∧
      s'.stk 0 = A ∧ s'.stk sTmp = h :: X sTmp ∧ s'.reg rG = gCont_x := by
  have h1 : Ev main (.pop 0 rE_x) ⟨g, X⟩
      ⟨Function.update g rE_x h, Function.update X 0 A⟩ 1 := by
    simpa [h0] using ev_pop' main 0 rE_x g X
  have hpush : Ev main (.push sTmp rE_x) ⟨Function.update g rE_x h, Function.update X 0 A⟩
      ⟨Function.update g rE_x h, Function.update (Function.update X 0 A) sTmp (h :: X sTmp)⟩ 1 := by
    simpa [Function.update_of_ne (show sTmp ≠ (0 : Stk) by decide)]
      using ev_push' main sTmp rE_x (Function.update g rE_x h) (Function.update X 0 A)
  have hset : Ev main (.set rG gCont_x)
      ⟨Function.update g rE_x h, Function.update (Function.update X 0 A) sTmp (h :: X sTmp)⟩
      ⟨Function.update (Function.update g rE_x h) rG gCont_x,
        Function.update (Function.update X 0 A) sTmp (h :: X sTmp)⟩ 1 :=
    ev_set' main rG gCont_x _ _
  have h2 : Ev main (seqs [.push sTmp rE_x, .set rG gCont_x])
      ⟨Function.update g rE_x h, Function.update X 0 A⟩
      ⟨Function.update (Function.update g rE_x h) rG gCont_x,
        Function.update (Function.update X 0 A) sTmp (h :: X sTmp)⟩ 2 :=
    Ev.seq' hpush hset (C := 2) (by omega)
  have h3 : Ev main (.ite rE_x Glyph.iend (.set rG Glyph.eos) (seqs [.push sTmp rE_x, .set rG gCont_x]))
      ⟨Function.update g rE_x h, Function.update X 0 A⟩
      ⟨Function.update (Function.update g rE_x h) rG gCont_x,
        Function.update (Function.update X 0 A) sTmp (h :: X sTmp)⟩ 3 :=
    Ev.iteF (by simp [hh]) h2
  have hmain : Ev main readIntBody ⟨g, X⟩
      ⟨Function.update (Function.update g rE_x h) rG gCont_x,
        Function.update (Function.update X 0 A) sTmp (h :: X sTmp)⟩ 4 := by
    unfold readIntBody
    simp only [seqs]
    exact Ev.seq' h1 h3 (C := 4) (by omega)
  refine ⟨_, _, hmain, by omega, ?_, ?_, ?_⟩
  · simp [Function.update_of_ne (show (0 : Stk) ≠ sTmp by decide)]
  · simp
  · simp

/-- the bit-reading loop: from `G ++ iend :: A` on stack `0` it reads `|G| + 1` glyphs, buffering
`G` in reverse on `sTmp` above the frame marker, and stops with the driver register `rG` at `eos` -/
theorem riLoop (main : Cmd) :
    ∀ (G : List Glyph) (A : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph),
      (∀ h ∈ G, h ≠ Glyph.iend) → g rG = gCont_x → X 0 = G ++ Glyph.iend :: A →
      ∃ s', loopRuns main rG gCont_x readIntBody (G.length + 1) ⟨g, X⟩ s' (5 * (G.length + 1)) ∧
        s'.stk 0 = A ∧ s'.stk sTmp = G.reverse ++ X sTmp ∧ s'.reg rG = Glyph.eos := by
  intro G
  induction G with
  | nil =>
      intro A g X _ hg h0
      obtain ⟨s', n, hev, hn, hA, hT, hr⟩ :=
        riBody_iend main (g := g) (X := X) (A := A) (by simpa using h0)
      refine ⟨s', loopRuns.mono (by omega) (loopRuns.one hg (hev.mono hn)) (by simp), ?_, ?_, hr⟩
      · simpa using hA
      · simpa using hT
  | cons hd tl ih =>
      intro A g X hG hg h0
      have hhd : hd ≠ Glyph.iend := hG hd (List.mem_cons_self ..)
      have htl : ∀ x ∈ tl, x ≠ Glyph.iend := fun x hx => hG x (List.mem_cons_of_mem hd hx)
      have h0' : X 0 = hd :: (tl ++ Glyph.iend :: A) := by simpa using h0
      obtain ⟨s₁, n₁, hev₁, hn₁, hA₁, hT₁, hr₁⟩ :=
        riBody_miss main (g := g) (X := X) (h := hd) (A := tl ++ Glyph.iend :: A) hhd h0'
      obtain ⟨s₂, hrun₂, hA₂, hT₂, hr₂⟩ := ih A s₁.reg s₁.stk htl hr₁ hA₁
      have hcat := loopRuns.concat (tl.length + 1) (loopRuns.one hg (hev₁.mono hn₁)) hrun₂
      refine ⟨s₂, loopRuns.cast ?_ (loopRuns.mono (by omega) hcat ?_), hA₂, ?_, hr₂⟩
      · simp only [List.length_cons] <;> omega
      · simp only [List.length_cons] <;> omega
      · rw [hT₂, hT₁]
        simp [List.reverse_cons, List.append_assoc]

end Work.Layout

namespace Work.Layout.Take

open HvdH
open Work.Layout

/-- `readIntProg` (`Submission/Work/Layout/Take/Defs.lean`) reads the bits of the integer value on
top of stack `0`.  For an input `Val.int k` with `k : ℕ` (sign glyph `pos`, then the bits of `k`
least significant first, then `iend`) it discards the sign and the `iend` and leaves the bits
(LSB first, as `bit` glyphs) on top of stack `sBit`; stack `0` loses the value.  `sTmp` and every
stack other than `0` and `sBit` are restored.

Useful: `Work.Layout.enc_int_nat_x : (Val.int (k:ℤ)).enc = Glyph.pos :: (bitsG_x k.bits ++ [Glyph.iend])`,
`Work.Layout.bitsG_append`, `Work.Layout.gMark_notMem_bitsG_x`, `Work.Layout.mvB_ev` (in
`Submission/Work/Layout/Move.lean`), `Work.Layout.ev_pop'`, `Work.Layout.ev_peek'`,
`Work.Layout.ev_push'`, `Work.Layout.ev_set'`, `Work.Layout.ev_iteT`, `Work.Layout.ev_iteF`,
`Work.Layout.Ev.seq'` (in `Submission/Work/Layout/Base.lean`) and `Work.Layout.loopRuns.*`. -/
theorem readInt_ev (main : HvdH.Cmd) (k : ℕ) (L : List HvdH.Glyph) (g : HvdH.Reg → HvdH.Glyph)
    (X : HvdH.Stk → List HvdH.Glyph)
    (h0 : X 0 = (HvdH.Val.int (k : ℤ)).enc ++ L) :
    ∃ s' n, Work.Layout.Ev main Work.Layout.readIntProg ⟨g, X⟩ s' n ∧ n ≤ 20 * (k.size + 2) ∧
      s'.stk 0 = L ∧ s'.stk Work.Layout.sTmp = X Work.Layout.sTmp ∧
      s'.stk Work.Layout.sBit = Work.Layout.bitsG_x k.bits ++ X Work.Layout.sBit ∧
      (∀ j, j ≠ 0 → j ≠ Work.Layout.sTmp → j ≠ Work.Layout.sBit → s'.stk j = X j) := by
  have h0' : X 0 = Glyph.pos :: (bitsG_x k.bits ++ [Glyph.iend] ++ L) := by
    rw [h0, enc_int_nat_x]; simp
  -- the four commands before the loop: set the marker, buffer it, drop the sign, start the loop
  have ha : Ev main (.set rE_x gMark) ⟨g, X⟩ ⟨Function.update g rE_x gMark, X⟩ 1 :=
    ev_set' main rE_x gMark g X
  have hb : Ev main (.push sTmp rE_x) ⟨Function.update g rE_x gMark, X⟩
      ⟨Function.update g rE_x gMark, Function.update X sTmp (gMark :: X sTmp)⟩ 1 := by
    simpa using ev_push' main sTmp rE_x (Function.update g rE_x gMark) X
  have hc : Ev main (.pop 0 rE_x)
      ⟨Function.update g rE_x gMark, Function.update X sTmp (gMark :: X sTmp)⟩
      ⟨Function.update g rE_x Glyph.pos,
        Function.update (Function.update X sTmp (gMark :: X sTmp)) 0
          (bitsG_x k.bits ++ [Glyph.iend] ++ L)⟩ 1 := by
    have h := ev_pop' main 0 rE_x (Function.update g rE_x gMark) (Function.update X sTmp (gMark :: X sTmp))
    have hhead : (Function.update X sTmp (gMark :: X sTmp) 0).headD Glyph.eos = Glyph.pos := by
      rw [Function.update_of_ne (show (0 : Stk) ≠ sTmp by decide), h0']; rfl
    have htail : (Function.update X sTmp (gMark :: X sTmp) 0).tail =
        bitsG_x k.bits ++ [Glyph.iend] ++ L := by
      rw [Function.update_of_ne (show (0 : Stk) ≠ sTmp by decide), h0']; rfl
    rw [hhead, htail] at h
    convert h using 2
    exact (Function.update_idem gMark Glyph.pos g).symm
  have hd : Ev main (.set rG gCont_x)
      ⟨Function.update g rE_x Glyph.pos,
        Function.update (Function.update X sTmp (gMark :: X sTmp)) 0
          (bitsG_x k.bits ++ [Glyph.iend] ++ L)⟩
      ⟨Function.update (Function.update g rE_x Glyph.pos) rG gCont_x,
        Function.update (Function.update X sTmp (gMark :: X sTmp)) 0
          (bitsG_x k.bits ++ [Glyph.iend] ++ L)⟩ 1 :=
    ev_set' main rG gCont_x _ _
  -- state after `set rG gCont_x`
  have hdrv : (Function.update (Function.update g rE_x Glyph.pos) rG gCont_x) rG = gCont_x := by
    simp
  have hstk0 : Function.update (Function.update X sTmp (gMark :: X sTmp)) 0
        (bitsG_x k.bits ++ [Glyph.iend] ++ L) 0 = bitsG_x k.bits ++ Glyph.iend :: L := by
    rw [Function.update_self, List.append_assoc]; simp
  -- the bit-reading loop
  obtain ⟨s5, hrun, hA5, hT5, hr5⟩ :=
    riLoop main (bitsG_x k.bits) L (Function.update (Function.update g rE_x Glyph.pos) rG gCont_x)
      (Function.update (Function.update X sTmp (gMark :: X sTmp)) 0
        (bitsG_x k.bits ++ [Glyph.iend] ++ L))
      (fun h hh => ne_iend_of_mem_bitsG_x hh) hdrv hstk0
  have hevLoop : Ev main (.loop rG gCont_x readIntBody) _ s5
      (5 * ((bitsG_x k.bits).length + 1) + 1) :=
    loopRuns.eval hrun (by rw [hr5]; decide)
  -- nothing before `mvB` touches `sBit`
  have hpre5 : Ev main (seqs [.set rE_x gMark, .push sTmp rE_x, .pop 0 rE_x, .set rG gCont_x,
      .loop rG gCont_x readIntBody]) ⟨g, X⟩ s5 _ :=
    Ev.seqs_cons ha (Ev.seqs_cons hb (Ev.seqs_cons hc (Ev.seqs_cons hd hevLoop)))
  have hsBit5 : s5.stk sBit = X sBit :=
    Ev.frame hpre5 (S := ({0, sTmp} : Finset Stk)) (by decide) (k := sBit) (by decide)
  -- move the buffered bits from `sTmp` to `sBit`
  have hsTmp4 : Function.update (Function.update X sTmp (gMark :: X sTmp)) 0
        (bitsG_x k.bits ++ [Glyph.iend] ++ L) sTmp = gMark :: X sTmp := by
    rw [Function.update_of_ne (show sTmp ≠ (0 : Stk) by decide), Function.update_self]
  have hmvBc : s5.stk sTmp = (bitsG_x k.bits).reverse ++ gMark :: X sTmp := by
    rw [hT5, hsTmp4]
  have hgm : gMark ∉ (bitsG_x k.bits).reverse := by
    rw [List.mem_reverse]; exact gMark_notMem_bitsG_x k.bits
  obtain ⟨s6, n6, hev6, hn6, hc6, hb6, hf6⟩ :=
    mvB_ev (main := main) (c := sTmp) (b := sBit) (by decide)
      (G := (bitsG_x k.bits).reverse) (C := X sTmp) (B := s5.stk sBit)
      (g := s5.reg) (X := s5.stk) hgm hmvBc rfl
  have hmvB : Ev main (mvB sTmp sBit) ⟨s5.reg, s5.stk⟩ s6
      (4 * (((bitsG_x k.bits).reverse).length + 1) + 3) :=
    hev6.mono hn6
  have hmain : Ev main readIntProg ⟨g, X⟩ s6 _ :=
    Ev.seqs_cons ha (Ev.seqs_cons hb (Ev.seqs_cons hc (Ev.seqs_cons hd (Ev.seqs_cons hevLoop hmvB))))
  have hmainEv := hmain
  obtain ⟨n, he, hnC⟩ := hmain
  have hbound : n ≤ 20 * (k.size + 2) := by
    refine le_trans hnC ?_
    simp only [bitsG_length_x, List.length_reverse, Nat.size_eq_bits_len]
    omega
  refine ⟨s6, n, ⟨n, he, le_rfl⟩, hbound, ?_, ?_, ?_, ?_⟩
  · rw [hf6 0 (by decide) (by decide), hA5]
  · exact hc6
  · rw [hb6, hsBit5]; simp
  · intro j hj0 hjT hjB
    exact Ev.frame hmainEv (S := ({0, sTmp, sBit} : Finset Stk)) (by decide) (by simp [hj0, hjT, hjB])

end Work.Layout.Take
