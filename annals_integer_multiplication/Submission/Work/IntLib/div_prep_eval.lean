import Mathlib
import Submission.Work.IntLib.divCore
import Submission.Work.IntLib.eval_mvRevOnto
import Submission.Work.IntLib.mvRevOntoTight
import Submission.Work.IntLib.eval_stripZeros
import Submission.Work.IntLib.stripZeros_range_eval

/-!
# `div_prep_eval`: the `prep` fix-up of the division core

`Work.IntLib.Div.prep src msrc` is the fix-up used by the division routines (`tdiv`, `tmod`, `fdiv`,
`fmod`) to turn the raw result region of a cache stack into a value region on stack `8`
(`Div.stX`):

1. `mvRevOnto src msrc stX rgT` moves the glyphs of stack `src` above its frame marker `msrc` onto
   stack `stX`, reversing them (and drops the marker);
2. `stripZeros stX gX rgT` drops the leading `false` bits of that reversed region (the trailing
   zeros of the value, i.e. the padding inserted by the core);
3. `mkG src msrc` restores the empty region marker on `src`.

This file proves the raw `Eval` specification, with the exact post-state and the linear cost bound
`7 * l.length + 19` (the three parts cost `5 * L + 9`, `2 * L + 6` and `2`, plus the final `skip`),
where `L = l.length` and the stack `src` initially holds `bitsG l ++ msrc :: bk`.
-/

set_option autoImplicit false

namespace Work.IntLib

open HvdH

theorem div_prep_eval (main : HvdH.Cmd) (src : HvdH.Stk) (msrc : HvdH.Glyph) (l : List Bool)
    (bk bkX : List HvdH.Glyph) (s : HvdH.State) (hbit : ∀ b : Bool, HvdH.Glyph.bit b ≠ msrc)
    (hsrc : s.stk src = Work.IntLib.bitsG l ++ msrc :: bk)
    (hX : s.stk Work.IntLib.Div.stX = [Work.IntLib.gX] ++ bkX)
    (hne : src ≠ Work.IntLib.Div.stX) :
    ∃ s' n, HvdH.Eval main (Work.IntLib.Div.prep src msrc) s s' n ∧
      n ≤ 7 * l.length + 19 ∧
      s'.stk src = msrc :: bk ∧
      s'.stk Work.IntLib.Div.stX =
        ((Work.IntLib.bitsG l).reverse).dropWhile (fun g => g = HvdH.Glyph.bit false) ++
          [Work.IntLib.gX] ++ bkX ∧
      ∀ j : HvdH.Stk, j ≠ src → j ≠ Work.IntLib.Div.stX → s'.stk j = s.stk j := by
  have hTsrc : ∀ g ∈ Work.IntLib.bitsG l, g ≠ msrc := by
    intro g hg hgm
    obtain ⟨b, -, hb⟩ := List.mem_map.mp hg
    exact hbit b (hb.trans hgm)
  obtain ⟨s₁, n₁, hev₁, hn₁, hs₁src, hs₁X, hfr₁⟩ :=
    Work.IntLib.mvRevOntoTight main src msrc Work.IntLib.Div.stX Work.IntLib.Div.rgT
      (Work.IntLib.bitsG l) bk ([Work.IntLib.gX] ++ bkX) s hTsrc hsrc hX hne
  set p : HvdH.Glyph → Bool := fun g => g = HvdH.Glyph.bit false with hp
  set e : List HvdH.Glyph := ((Work.IntLib.bitsG l).reverse).takeWhile p with he
  set rest : List HvdH.Glyph :=
    ((Work.IntLib.bitsG l).reverse).dropWhile p ++ [Work.IntLib.gX] ++ bkX with hrest
  have hlen : (Work.IntLib.bitsG l).length = l.length := by simp [Work.IntLib.bitsG]
  -- the stripped prefix consists of `false` bits
  have heall : ∀ x ∈ e, x = HvdH.Glyph.bit false := by
    intro x hx
    rw [he] at hx
    have h := List.mem_takeWhile_imp hx
    simpa [hp] using h
  -- the glyph that stops the stripping loop is neither a `false` bit nor `eos`
  have hhead1 : rest.headD HvdH.Glyph.eos ≠ HvdH.Glyph.bit false := by
    rcases hgs : ((Work.IntLib.bitsG l).reverse).dropWhile p with _ | ⟨g, gs⟩
    · have hnil : rest.headD HvdH.Glyph.eos = Work.IntLib.gX := by rw [hrest, hgs]; rfl
      rw [hnil]; intro hcon; cases hcon
    · have hnot : ¬ (p g = true) := Work.IntLib.dropWhile_eq_cons_not _ hgs
      have hcon : rest.headD HvdH.Glyph.eos = g := by rw [hrest, hgs]; rfl
      rw [hcon]; intro hg
      exact hnot (by simp [hp, hg])
  have hhead2 : rest.headD HvdH.Glyph.eos ≠ HvdH.Glyph.eos := by
    rcases hgs : ((Work.IntLib.bitsG l).reverse).dropWhile p with _ | ⟨g, gs⟩
    · have hnil : rest.headD HvdH.Glyph.eos = Work.IntLib.gX := by rw [hrest, hgs]; rfl
      rw [hnil]; intro hcon; cases hcon
    · have hcon : rest.headD HvdH.Glyph.eos = g := by rw [hrest, hgs]; rfl
      rw [hcon]; intro hg
      have hgmem : g ∈ ((Work.IntLib.bitsG l).reverse).dropWhile p := by
        rw [hgs]; exact List.mem_cons_self ..
      have hgin : g ∈ (Work.IntLib.bitsG l).reverse :=
        List.Sublist.mem hgmem (List.dropWhile_sublist p)
      have hgin' : g ∈ Work.IntLib.bitsG l := List.mem_reverse.mp hgin
      obtain ⟨b, -, hb⟩ := List.mem_map.mp hgin'
      rw [← hb] at hg
      cases hg
  have hstkrest : s₁.stk Work.IntLib.Div.stX = e ++ rest := by
    calc s₁.stk Work.IntLib.Div.stX = (Work.IntLib.bitsG l).reverse ++ ([Work.IntLib.gX] ++ bkX) :=
          hs₁X
      _ = ((Work.IntLib.bitsG l).reverse ++ [Work.IntLib.gX]) ++ bkX := (List.append_assoc ..).symm
      _ = ((((Work.IntLib.bitsG l).reverse).takeWhile p ++
              ((Work.IntLib.bitsG l).reverse).dropWhile p)
              ++ [Work.IntLib.gX]) ++ bkX := by rw [List.takeWhile_append_dropWhile]
      _ = e ++ rest := by simp only [he, hrest, List.append_assoc]
  have hev₂ := Work.IntLib.stripZeros_range_eval main Work.IntLib.Div.stX Work.IntLib.gX
    Work.IntLib.Div.rgT e rest s₁ heall hhead1 hhead2 hstkrest
  set s₂ : HvdH.State := ⟨Function.update s₁.reg Work.IntLib.Div.rgT (rest.headD HvdH.Glyph.eos),
    Function.update s₁.stk Work.IntLib.Div.stX rest⟩ with hs₂
  have hs₂X : s₂.stk Work.IntLib.Div.stX = rest := by rw [hs₂]; rfl
  have hfr₂ : ∀ j : HvdH.Stk, j ≠ Work.IntLib.Div.stX → s₂.stk j = s₁.stk j := by
    intro j hj
    rw [hs₂]
    exact Function.update_of_ne hj _ _
  set s₃ : HvdH.State := ⟨Function.update s₂.reg Work.IntLib.Div.rgT msrc, s₂.stk⟩ with hs₃
  set s₄ : HvdH.State := ⟨s₃.reg, Function.update s₃.stk src (msrc :: s₃.stk src)⟩ with hs₄
  have hs₄src : s₄.stk src = msrc :: bk := by
    have h2 : s₂.stk src = bk := by rw [hfr₂ src hne, hs₁src]
    rw [hs₄, hs₃]
    simp [h2]
  have hs₄X : s₄.stk Work.IntLib.Div.stX =
      ((Work.IntLib.bitsG l).reverse).dropWhile (fun g => g = HvdH.Glyph.bit false) ++
        [Work.IntLib.gX] ++ bkX := by
    have h1 : s₄.stk Work.IntLib.Div.stX = s₂.stk Work.IntLib.Div.stX := by
      simp only [hs₄, hs₃, Function.update_of_ne (Ne.symm hne)]
    rw [h1, hs₂X, ← hrest]
  have hframe : ∀ j : HvdH.Stk, j ≠ src → j ≠ Work.IntLib.Div.stX → s₄.stk j = s.stk j := by
    intro j hj1 hj2
    have h1 : s₄.stk j = s₃.stk j := by simp only [hs₄, Function.update_of_ne hj1]
    have h2 : s₃.stk j = s₂.stk j := by simp only [hs₃]
    rw [h1, h2, hfr₂ j hj2, hfr₁ j hj1 hj2]
  have hevset : HvdH.Eval main (HvdH.Cmd.set Work.IntLib.Div.rgT msrc) s₂ s₃ 1 :=
    Work.IntLib.Eval.set_eq
  have hevpush : HvdH.Eval main (HvdH.Cmd.push src Work.IntLib.Div.rgT) s₃ s₄ 1 := by
    rw [hs₄]
    apply Work.IntLib.Eval.push_eq
    rw [hs₃]
    rfl
  have hevmk : HvdH.Eval main (Work.IntLib.Div.mkG src msrc) s₂ s₄ 2 := by
    show HvdH.Eval main (HvdH.Cmd.seq (HvdH.Cmd.set Work.IntLib.Div.rgT msrc)
      (HvdH.Cmd.push src Work.IntLib.Div.rgT)) s₂ s₄ 2
    exact HvdH.Eval.seq hevset hevpush
  have hwhole : HvdH.Eval main
      (HvdH.Cmd.seq (Work.IntLib.mvRevOnto src msrc Work.IntLib.Div.stX Work.IntLib.Div.rgT)
        (HvdH.Cmd.seq (Work.IntLib.stripZeros Work.IntLib.Div.stX Work.IntLib.gX Work.IntLib.Div.rgT)
          (HvdH.Cmd.seq (HvdH.Cmd.seq (HvdH.Cmd.set Work.IntLib.Div.rgT msrc)
            (HvdH.Cmd.push src Work.IntLib.Div.rgT)) HvdH.Cmd.skip)))
      s s₄ (n₁ + (2 * e.length + 6 + 3)) :=
    HvdH.Eval.seq hev₁ (HvdH.Eval.seq hev₂ (HvdH.Eval.seq hevmk (HvdH.Eval.skip s₄)))
  have hevprep : HvdH.Eval main (Work.IntLib.Div.prep src msrc) s s₄
      (n₁ + (2 * e.length + 6 + 3)) := by
    simp only [Work.IntLib.Div.prep, Work.IntLib.Div.seqs_cons, Work.IntLib.Div.seqs_nil,
      Work.IntLib.Div.mkG]
    exact hwhole
  have hcost : n₁ + (2 * e.length + 6 + 3) ≤ 7 * l.length + 19 := by
    have hele : e.length ≤ l.length := by
      rw [he]
      calc (List.takeWhile p ((Work.IntLib.bitsG l).reverse)).length
          ≤ ((Work.IntLib.bitsG l).reverse).length :=
            List.Sublist.length_le
              (List.takeWhile_sublist (p := p) (l := (Work.IntLib.bitsG l).reverse))
        _ = (Work.IntLib.bitsG l).length := List.length_reverse ..
        _ = l.length := hlen
    rw [hlen] at hn₁
    omega
  exact ⟨s₄, n₁ + (2 * e.length + 6 + 3), hevprep, hcost, hs₄src, hs₄X, hframe⟩

end Work.IntLib
