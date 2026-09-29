import Mathlib
import Submission.Work.SynFFT.mrgLvDefs
import Submission.Work.SynFFT.grpValZipCatSize
import Submission.Work.SynFFT.foldLoopEv
import Submission.Work.Layout.AA.clearAbove_ev

/-!
# `Work.SynFFT.mergeLevelWord`: one merge level of the transpose word

`stateVal Gs = ofList (Gs.map grpVal)` is the value of a list of groups; `mLevel` merges adjacent
groups with `zipCat`, keeping a dangling last group.  This file proves that the merge word
`mergeLevelProg2 hp` (`Submission/Work/SynFFT/mrgLvDefs.lean`) satisfies `stateVal Gs ↦
stateVal (mLevel Gs)` on stack 0 in time `O (vsz (stateVal Gs))`, relative to an arbitrary pairwise
merge word `hp` (`zipCatWord`).

The implementation: move the input list to a scratch stack above a boundary marker
(`Work.Layout.gMark`) with `Work.Layout.mvVal`; keep a stack of values on stack 0 as the
accumulator (top = last processed element, marker below); walk the input, popping the leading
`cons` with `Work.Layout.unconsTo` (cost `20 * (vsz g + 1)`) and pushing the element on the
accumulator; if the next input glyph is the `nil` terminator, the element just popped is unpaired,
so push it on the accumulator and stop, otherwise pop the next element, move the pending element on
top of it and run `hp` (giving `zipCat` of the pair); finally fold the accumulator into a list value
with `Work.Layout.prependTo` (each step `O (vsz v)`, independent of the accumulated list), yielding
`ofList (mLevel Gs)` without a reversal.  Per-element costs telescope to `O (vsz (stateVal Gs))`.
The built-in `WordR` frame restores stacks `≠ 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Work.SynFFT

open HvdH
open Work.Layout

/-! ## Size arithmetic for the merge walk -/

theorem mlv_gSz_reverse (Ls : List (List (List Val))) : gSz Ls.reverse = gSz Ls := by
  simp [gSz, List.map_reverse, List.sum_reverse]

theorem mlv_map_reverse_eq {α β : Type} (l : List α) (f : α → β) :
    (l.map f).reverse = l.reverse.map f := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.reverse_cons, ih, List.map_append, List.map_nil,
        List.singleton_append, List.cons_append]

theorem mlv_gSz_mLevel_le (Ls : List (List (List Val))) : gSz (mLevel Ls) ≤ 2 * gSz Ls + 2 := by
  induction Ls using mLevel.induct with
  | case1 => simp [mLevel, gSz]
  | case2 G =>
      have h : gSz [G] = vsz (grpVal G) + 1 := by simp [gSz]
      rw [mLevel_singleton, h]
      omega
  | case3 G1 G2 rest ih =>
      rw [mLevel_cons_cons]
      have h1 : gSz (zipCat G1 G2 :: mLevel rest) =
          (vsz (grpVal (zipCat G1 G2)) + 1) + gSz (mLevel rest) := by simp [gSz]
      have h2 : gSz (G1 :: G2 :: rest) =
          (vsz (grpVal G1) + 1) + ((vsz (grpVal G2) + 1) + gSz rest) := by simp [gSz]
      have h3 := grpValZipCatSize G1 G2
      rw [h1, h2]
      omega

theorem mlv_sum_map_mul {α : Type} (l : List α) (c : ℕ) (f : α → ℕ) :
    (l.map (fun x => c * f x)).sum = c * (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- the cost budget of the merge walk on the list of remaining groups `Ls` -/
def mlvCost (KM : ℕ) (Ls : List (List (List Val))) : ℕ :=
  (Ls.map (fun g => KM * (vsz (grpVal g) + 1))).sum + KM

theorem mlvCost_eq (KM : ℕ) (Ls : List (List (List Val))) : mlvCost KM Ls = KM * gSz Ls + KM := by
  rw [mlvCost, gSz, mlv_sum_map_mul]

theorem mlvCost_stateVal (KM : ℕ) (Ls : List (List (List Val))) :
    mlvCost KM Ls = KM * vsz (stateVal Ls) := by
  rw [mlvCost_eq, vsz_stateVal]
  ring

theorem mlvCost_cons (KM : ℕ) (g : List (List Val)) (Ls : List (List (List Val))) :
    mlvCost KM (g :: Ls) = KM * (vsz (grpVal g) + 1) + mlvCost KM Ls := by
  simp only [mlvCost, List.map_cons, List.sum_cons]
  ring

theorem mlvCost_nil (KM : ℕ) : mlvCost KM [] = KM := by simp [mlvCost]

/-! ## A strengthened `unconsTo` (scratch stacks restored) -/

theorem mlv_unconsTo_ev' (main : Cmd) (a b c d : Stk) (rr : Reg)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (g : Reg → Glyph) (X : Stk → List Glyph) (v : Val) (A : List Glyph)
    (ha : X a = Glyph.cons :: (v.enc ++ A)) :
    ∃ s' n, Ev main (unconsTo a b c d rr) ⟨g, X⟩ s' n ∧
      n ≤ 20 * (vsz v + 1) ∧ s'.stk a = A ∧ s'.stk b = v.enc ++ X b ∧
      s'.stk c = X c ∧ s'.stk d = X d ∧
      (∀ j, j ≠ a → j ≠ b → s'.stk j = X j) := by
  have h1 : Ev main (.pop a rr) ⟨g, X⟩
      ⟨Function.update g rr ((X a).headD Glyph.eos), Function.update X a (X a).tail⟩ 1 :=
    ev_pop' main a rr g X
  have ha' : Function.update X a (X a).tail a = v.enc ++ A := by
    simp only [stkFn_same, ha, tail_cons]
  have hb' : Function.update X a (X a).tail b = X b := stkFn_ne X hab.symm (X a).tail
  obtain ⟨s₂, n₂, h2, hn₂, ha₂, hb₂, hc₂, hd₂, hf₂⟩ :=
    Work.Layout.AA.mvVal_ev' (main := main) (a := a) (b := b) (c := c) (d := d)
      hab hac had hbc hbd hcd (g := Function.update g rr ((X a).headD Glyph.eos))
      (X := Function.update X a (X a).tail) (v := v) (A := A) (B := X b) ha' hb'
  have hupd : ∀ j, j ≠ a → Function.update X a (X a).tail j = X j :=
    fun j hj => stkFn_ne X hj (X a).tail
  have hmain : Ev main (unconsTo a b c d rr) ⟨g, X⟩ s₂ (n₂ + 1) := by
    unfold unconsTo
    simp only [seqs]
    exact (Ev.seq h1 h2).mono (by omega)
  refine ⟨s₂, _, hmain, ?_, ha₂, hb₂, ?_, ?_, ?_⟩
  · have hv := one_le_vsz v; omega
  · rw [hc₂]; exact hupd c (Ne.symm hac)
  · rw [hd₂]; exact hupd d (Ne.symm had)
  · intro j hja hjb
    by_cases hjc : j = c
    · subst hjc; rw [hc₂]; exact hupd j (Ne.symm hac)
    · by_cases hjd : j = d
      · subst hjd; rw [hd₂]; exact hupd j (Ne.symm had)
      · rw [hf₂ j hja hjb]; exact hupd j hja

/-- the `cons`-chain tail of a two-element list prefix -/
theorem mlv_encsC_pair_tail (G1 G2 : List (List Val)) (Ls : List (List (List Val))) (T9 : List Glyph) :
    encsC ((G1 :: G2 :: Ls).map grpVal) ++ [Glyph.nil] ++ gMark :: T9 =
      Glyph.cons :: (grpVal G1).enc ++ (Glyph.cons :: (grpVal G2).enc ++
        (encsC (Ls.map grpVal) ++ [Glyph.nil] ++ gMark :: T9)) := by
  simp only [List.map_cons, encsC_cons, encsC_nil, List.append_nil, List.nil_append,
    List.cons_append, List.singleton_append, List.append_assoc]

/-- the `cons`-chain tail of a one-element list prefix -/
theorem mlv_encsC_single (G1 : List (List Val)) (T9 : List Glyph) :
    encsC [grpVal G1] ++ [Glyph.nil] ++ gMark :: T9 =
      Glyph.cons :: (grpVal G1).enc ++ ([Glyph.nil] ++ gMark :: T9) := by
  have h : encsC [grpVal G1] = Glyph.cons :: (grpVal G1).enc := by
    rw [encsC_cons, encsC_nil, List.append_nil]
  rw [h, List.append_assoc]

/-! ## The branches of a merge step -/

theorem mergeBodyLast_ev (main : Cmd) (g : Reg → Glyph) (X : Stk → List Glyph)
    (G1 : List (List Val)) (acc : List Val) (T0 Tmp : List Glyph)
    (h0 : X 0 = encs acc ++ gMark :: T0)
    (htmp : X lvTmp = (grpVal G1).enc ++ gMark :: Tmp) :
    ∃ s' n, Ev main mergeBodyLast ⟨g, X⟩ s' n ∧
      n ≤ 40 * (vsz (grpVal G1) + 1) + 100 ∧
      s'.stk 0 = encs (grpVal G1 :: acc) ++ gMark :: T0 ∧
      s'.stk lvTmp = gMark :: Tmp ∧
      s'.reg lvF = Glyph.eos ∧
      (∀ j, j ≠ 0 → j ≠ lvTmp → s'.stk j = X j) := by
  obtain ⟨s₁, n₁, hmv, hn₁, htmp₁, h0₁, _hs1, _hs2, hfr₁⟩ :=
    Work.Layout.AA.mvVal_ev' (main := main) (a := lvTmp) (b := 0) (c := lvS1) (d := lvS2)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := g) (X := X) (v := grpVal G1) (A := gMark :: Tmp)
      (B := encs acc ++ gMark :: T0) htmp h0
  have hset : Ev main (.set lvF Glyph.eos) s₁
      ⟨Function.update s₁.reg lvF Glyph.eos, s₁.stk⟩ 1 :=
    ev_set' main lvF Glyph.eos s₁.reg s₁.stk
  have hmain : Ev main mergeBodyLast ⟨g, X⟩
      ⟨Function.update s₁.reg lvF Glyph.eos, s₁.stk⟩ (16 * (vsz (grpVal G1) + 1) + 1) := by
    unfold mergeBodyLast
    simp only [seqs]
    exact (Ev.seq hmv hset).mono (by omega)
  refine ⟨_, _, hmain, by omega, ?_, htmp₁, by simp, ?_⟩
  · rw [h0₁, Work.Kernel.encs_cons, List.append_assoc]
  · intro j hj0 hjt
    exact hfr₁ j hjt hj0

theorem mergeBodyPair_ev (main hp : Cmd) (KH : ℕ)
    (hpair : ∀ (m : Cmd) (G₁ G₂ : List (List Val)) (rest : List Val),
      HvdH.WordR m hp
        (fun vs => vs = grpVal G₁ :: grpVal G₂ :: rest)
        (fun _ out => out = grpVal (zipCat G₁ G₂) :: rest)
        (fun _ => KH * (vsz (grpVal G₁) + vsz (grpVal G₂) + 1) + KH))
    (g : Reg → Glyph) (X : Stk → List Glyph) (G1 G2 : List (List Val)) (acc : List Val)
    (A : List Glyph) (T0 Tmp : List Glyph)
    (hin : X lvIn = Glyph.cons :: (grpVal G2).enc ++ A)
    (htmp : X lvTmp = (grpVal G1).enc ++ gMark :: Tmp)
    (h0 : X 0 = encs acc ++ gMark :: T0) :
    ∃ s' n, Ev main (mergeBodyPair hp) ⟨g, X⟩ s' n ∧
      n ≤ (KH + 1000) * ((vsz (grpVal G1) + 1) + (vsz (grpVal G2) + 1)) + KH + 1000 ∧
      s'.stk 0 = encs (grpVal (zipCat G1 G2) :: acc) ++ gMark :: T0 ∧
      s'.stk lvIn = A ∧
      s'.stk lvTmp = gMark :: Tmp ∧
      s'.reg lvF = Glyph.cons ∧
      (∀ j, j ≠ 0 → j ≠ lvIn → j ≠ lvTmp → s'.stk j = X j) := by
  obtain ⟨s₁, n₁, h1, hn₁, ha₁, h0₁, _hc₁, _hd₁, hfr₁⟩ :=
    mlv_unconsTo_ev' main lvIn 0 lvS1 lvS2 lvP
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      g X (grpVal G2) A hin
  have htmp₁ : s₁.stk lvTmp = (grpVal G1).enc ++ gMark :: Tmp := by
    rw [hfr₁ lvTmp (by decide) (by decide)]
    exact htmp
  have h0₁' : s₁.stk 0 = encs (grpVal G2 :: acc) ++ gMark :: T0 := by
    rw [h0₁, h0]
    simp only [Work.Kernel.encs_cons, List.append_assoc]
  obtain ⟨s₂, n₂, h2, hn₂, htmp₂, h0₂, _hc₂, _hd₂, hfr₂⟩ :=
    Work.Layout.AA.mvVal_ev' (main := main) (a := lvTmp) (b := 0) (c := lvS1) (d := lvS2)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s₁.reg) (X := s₁.stk) (v := grpVal G1) (A := gMark :: Tmp)
      (B := encs (grpVal G2 :: acc) ++ gMark :: T0) htmp₁ h0₁'
  have h0₂' : s₂.stk 0 = encs (grpVal G1 :: grpVal G2 :: acc) ++ gMark :: T0 := by
    rw [h0₂]
    simp only [Work.Kernel.encs_cons, List.append_assoc]
  have hwp := hpair main G1 G2 acc
  rw [HvdH.WordR] at hwp
  obtain ⟨out, s₃, n₃, hout, hev₃, hn₃, h0₃, hfr₃⟩ :=
    hwp (grpVal G1 :: grpVal G2 :: acc) rfl s₂ (gMark :: T0) h0₂'
  subst hout
  have hset : Ev main (.set lvF Glyph.cons) s₃
      ⟨Function.update s₃.reg lvF Glyph.cons, s₃.stk⟩ 1 :=
    ev_set' main lvF Glyph.cons s₃.reg s₃.stk
  have hmain : Ev main (mergeBodyPair hp) ⟨g, X⟩
      ⟨Function.update s₃.reg lvF Glyph.cons, s₃.stk⟩ (n₁ + n₂ + n₃ + 1) := by
    unfold mergeBodyPair
    simp only [seqs]
    exact (Ev.seq h1 (Ev.seq h2 (Ev.seq ⟨n₃, hev₃, le_rfl⟩ hset))).mono (by omega)
  have hKH : KH * (vsz (grpVal G1) + vsz (grpVal G2) + 1) + KH =
      KH * ((vsz (grpVal G1) + 1) + (vsz (grpVal G2) + 1)) := by ring
  refine ⟨_, _, hmain, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hC : n₃ ≤ KH * ((vsz (grpVal G1) + 1) + (vsz (grpVal G2) + 1)) := by
      rw [← hKH]; exact hn₃
    nlinarith [hn₁, hn₂, hC]
  · show s₃.stk 0 = encs (grpVal (zipCat G1 G2) :: acc) ++ gMark :: T0
    exact h0₃
  · show s₃.stk lvIn = A
    rw [hfr₃ lvIn (by decide), hfr₂ lvIn (by decide) (by decide)]
    exact ha₁
  · show s₃.stk lvTmp = gMark :: Tmp
    rw [hfr₃ lvTmp (by decide)]
    exact htmp₂
  · show (Function.update s₃.reg lvF Glyph.cons) lvF = Glyph.cons
    simp
  · intro j hj0 hjin hjt
    show s₃.stk j = X j
    rw [hfr₃ j hj0, hfr₂ j hjt hj0, hfr₁ j hjin hj0]

theorem mergeTailLast_ev (main hp : Cmd) (g : Reg → Glyph) (X : Stk → List Glyph)
    (G1 : List (List Val)) (acc : List Val) (T0 T9 Tmp : List Glyph)
    (h0 : X 0 = encs acc ++ gMark :: T0)
    (hin : X lvIn = [Glyph.nil] ++ gMark :: T9)
    (htmp : X lvTmp = (grpVal G1).enc ++ gMark :: Tmp) :
    ∃ s' n, Ev main (mergeTail hp) ⟨g, X⟩ s' n ∧
      n ≤ 40 * (vsz (grpVal G1) + 1) + 200 ∧
      s'.stk 0 = encs (grpVal G1 :: acc) ++ gMark :: T0 ∧
      s'.stk lvIn = [Glyph.nil] ++ gMark :: T9 ∧
      s'.stk lvTmp = gMark :: Tmp ∧
      s'.reg lvF = Glyph.eos ∧
      (∀ j, j ≠ 0 → j ≠ lvIn → j ≠ lvTmp → s'.stk j = X j) := by
  obtain ⟨s', n', h2, hn', h0', htmp', hrF', hfr'⟩ :=
    mergeBodyLast_ev (main := main) (g := Function.update g lvP ((X lvIn).headD Glyph.eos))
      X G1 acc T0 Tmp h0 htmp
  have h1 : Ev main (.peek lvIn lvP) ⟨g, X⟩
      ⟨Function.update g lvP ((X lvIn).headD Glyph.eos), X⟩ 1 := ev_peek' main lvIn lvP g X
  have hhead : (X lvIn).headD Glyph.eos = Glyph.nil := by rw [hin]; rfl
  have h2' : Ev main (.ite lvP Glyph.nil mergeBodyLast (mergeBodyPair hp))
      ⟨Function.update g lvP ((X lvIn).headD Glyph.eos), X⟩ s' (n' + 1) :=
    Ev.iteT (hr := by simp only [regUpd_same]; exact hhead) h2
  have hmain : Ev main (mergeTail hp) ⟨g, X⟩ s' (1 + (n' + 1)) := by
    unfold mergeTail
    simp only [seqs]
    exact Ev.seq h1 h2'
  refine ⟨s', _, hmain, by omega, h0', ?_, htmp', hrF', ?_⟩
  · rw [hfr' lvIn (by decide) (by decide)]
    exact hin
  · intro j hj0 hjin hjt
    exact hfr' j hj0 hjt

theorem mergeTailPair_ev (main hp : Cmd) (KH : ℕ)
    (hpair : ∀ (m : Cmd) (G₁ G₂ : List (List Val)) (rest : List Val),
      HvdH.WordR m hp
        (fun vs => vs = grpVal G₁ :: grpVal G₂ :: rest)
        (fun _ out => out = grpVal (zipCat G₁ G₂) :: rest)
        (fun _ => KH * (vsz (grpVal G₁) + vsz (grpVal G₂) + 1) + KH))
    (g : Reg → Glyph) (X : Stk → List Glyph) (G1 G2 : List (List Val)) (acc : List Val)
    (A : List Glyph) (T0 Tmp : List Glyph)
    (h0 : X 0 = encs acc ++ gMark :: T0)
    (hin : X lvIn = Glyph.cons :: (grpVal G2).enc ++ A)
    (htmp : X lvTmp = (grpVal G1).enc ++ gMark :: Tmp) :
    ∃ s' n, Ev main (mergeTail hp) ⟨g, X⟩ s' n ∧
      n ≤ (KH + 2000) * ((vsz (grpVal G1) + 1) + (vsz (grpVal G2) + 1)) + KH + 2000 ∧
      s'.stk 0 = encs (grpVal (zipCat G1 G2) :: acc) ++ gMark :: T0 ∧
      s'.stk lvIn = A ∧
      s'.stk lvTmp = gMark :: Tmp ∧
      s'.reg lvF = Glyph.cons ∧
      (∀ j, j ≠ 0 → j ≠ lvIn → j ≠ lvTmp → s'.stk j = X j) := by
  obtain ⟨s', n', h2, hn', h0', hin', htmp', hrF', hfr'⟩ :=
    mergeBodyPair_ev (main := main) (hp := hp) (KH := KH) hpair
      (Function.update g lvP ((X lvIn).headD Glyph.eos)) X G1 G2 acc A T0 Tmp hin htmp h0
  have h1 : Ev main (.peek lvIn lvP) ⟨g, X⟩
      ⟨Function.update g lvP ((X lvIn).headD Glyph.eos), X⟩ 1 := ev_peek' main lvIn lvP g X
  have hhead : (X lvIn).headD Glyph.eos = Glyph.cons := by rw [hin]; rfl
  have hne : (Function.update g lvP ((X lvIn).headD Glyph.eos)) lvP ≠ Glyph.nil := by
    simp only [regUpd_same, hhead]; decide
  have h2' : Ev main (.ite lvP Glyph.nil mergeBodyLast (mergeBodyPair hp))
      ⟨Function.update g lvP ((X lvIn).headD Glyph.eos), X⟩ s' (n' + 1) :=
    Ev.iteF (hr := hne) h2
  have hmain : Ev main (mergeTail hp) ⟨g, X⟩ s' (1 + (n' + 1)) := by
    unfold mergeTail
    simp only [seqs]
    exact Ev.seq h1 h2'
  have hS : 1 ≤ (vsz (grpVal G1) + 1) + (vsz (grpVal G2) + 1) := by
    have hv := one_le_vsz (grpVal G1); omega
  have hcost : 1 + (n' + 1) ≤
      (KH + 2000) * ((vsz (grpVal G1) + 1) + (vsz (grpVal G2) + 1)) + KH + 2000 := by
    nlinarith [hn', hS]
  exact ⟨s', _, hmain, hcost, h0', hin', htmp', hrF', hfr'⟩

theorem mergeMidLast_ev (main hp : Cmd) (g : Reg → Glyph) (X : Stk → List Glyph)
    (G1 : List (List Val)) (acc : List Val) (T0 T9 Tmp : List Glyph)
    (h0 : X 0 = encs acc ++ gMark :: T0)
    (hin : X lvIn = Glyph.cons :: (grpVal G1).enc ++ ([Glyph.nil] ++ gMark :: T9))
    (htmp : X lvTmp = gMark :: Tmp) :
    ∃ s' n, Ev main (mergeMid hp) ⟨g, X⟩ s' n ∧
      n ≤ 80 * (vsz (grpVal G1) + 1) + 300 ∧
      s'.stk 0 = encs (grpVal G1 :: acc) ++ gMark :: T0 ∧
      s'.stk lvIn = [Glyph.nil] ++ gMark :: T9 ∧
      s'.stk lvTmp = gMark :: Tmp ∧
      s'.reg lvF = Glyph.eos ∧
      (∀ j, j ≠ 0 → j ≠ lvIn → j ≠ lvTmp → s'.stk j = X j) := by
  obtain ⟨s₁, n₁, h1, hn₁, ha₁, hb₁, _hc₁, _hd₁, hf₁⟩ :=
    mlv_unconsTo_ev' main lvIn lvTmp lvS1 lvS2 lvP
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      g X (grpVal G1) ([Glyph.nil] ++ gMark :: T9) hin
  have hb₁' : s₁.stk lvTmp = (grpVal G1).enc ++ gMark :: Tmp := by rw [hb₁, htmp]
  have h0₁ : s₁.stk 0 = encs acc ++ gMark :: T0 := by
    rw [hf₁ 0 (by decide) (by decide), h0]
  obtain ⟨s', n', h2, hn', h0', hin', htmp', hrF', hfr'⟩ :=
    mergeTailLast_ev (main := main) (hp := hp) s₁.reg s₁.stk G1 acc T0 T9 Tmp h0₁ ha₁ hb₁'
  have hmain : Ev main (mergeMid hp) ⟨g, X⟩ s' (n₁ + n') := by
    unfold mergeMid
    simp only [seqs]
    exact Ev.seq h1 h2
  refine ⟨s', _, hmain, by omega, h0', hin', htmp', hrF', ?_⟩
  intro j hj0 hjin hjt
  rw [hfr' j hj0 hjin hjt, hf₁ j hjin hjt]

theorem mergeMidPair_ev (main hp : Cmd) (KH : ℕ)
    (hpair : ∀ (m : Cmd) (G₁ G₂ : List (List Val)) (rest : List Val),
      HvdH.WordR m hp
        (fun vs => vs = grpVal G₁ :: grpVal G₂ :: rest)
        (fun _ out => out = grpVal (zipCat G₁ G₂) :: rest)
        (fun _ => KH * (vsz (grpVal G₁) + vsz (grpVal G₂) + 1) + KH))
    (g : Reg → Glyph) (X : Stk → List Glyph) (G1 G2 : List (List Val)) (acc : List Val)
    (A : List Glyph) (T0 T9 Tmp : List Glyph)
    (h0 : X 0 = encs acc ++ gMark :: T0)
    (hin : X lvIn = Glyph.cons :: (grpVal G1).enc ++ (Glyph.cons :: (grpVal G2).enc ++ A))
    (htmp : X lvTmp = gMark :: Tmp) :
    ∃ s' n, Ev main (mergeMid hp) ⟨g, X⟩ s' n ∧
      n ≤ (KH + 4000) * ((vsz (grpVal G1) + 1) + (vsz (grpVal G2) + 1)) + KH + 3000 ∧
      s'.stk 0 = encs (grpVal (zipCat G1 G2) :: acc) ++ gMark :: T0 ∧
      s'.stk lvIn = A ∧
      s'.stk lvTmp = gMark :: Tmp ∧
      s'.reg lvF = Glyph.cons ∧
      (∀ j, j ≠ 0 → j ≠ lvIn → j ≠ lvTmp → s'.stk j = X j) := by
  obtain ⟨s₁, n₁, h1, hn₁, ha₁, hb₁, _hc₁, _hd₁, hf₁⟩ :=
    mlv_unconsTo_ev' main lvIn lvTmp lvS1 lvS2 lvP
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      g X (grpVal G1) (Glyph.cons :: (grpVal G2).enc ++ A) hin
  have hb₁' : s₁.stk lvTmp = (grpVal G1).enc ++ gMark :: Tmp := by rw [hb₁, htmp]
  have h0₁ : s₁.stk 0 = encs acc ++ gMark :: T0 := by
    rw [hf₁ 0 (by decide) (by decide), h0]
  obtain ⟨s', n', h2, hn', h0', hin', htmp', hrF', hfr'⟩ :=
    mergeTailPair_ev (main := main) (hp := hp) (KH := KH) hpair s₁.reg s₁.stk G1 G2 acc A
      T0 Tmp h0₁ ha₁ hb₁'
  have hmain : Ev main (mergeMid hp) ⟨g, X⟩ s' (n₁ + n') := by
    unfold mergeMid
    simp only [seqs]
    exact Ev.seq h1 h2
  have hv1 : vsz (grpVal G1) + 1 ≤ (vsz (grpVal G1) + 1) + (vsz (grpVal G2) + 1) :=
    Nat.le_add_right _ _
  have hcost : n₁ + n' ≤
      (KH + 4000) * ((vsz (grpVal G1) + 1) + (vsz (grpVal G2) + 1)) + KH + 3000 := by
    nlinarith [hn₁, hn', hv1]
  refine ⟨s', _, hmain, hcost, h0', hin', htmp', hrF', ?_⟩
  intro j hj0 hjin hjt
  rw [hfr' j hj0 hjin hjt, hf₁ j hjin hjt]

/-! ## One merge step -/

theorem mergeStepStop_ev (main hp : Cmd) (g : Reg → Glyph) (X : Stk → List Glyph)
    (T9 : List Glyph) (hin : X lvIn = [Glyph.nil] ++ gMark :: T9) :
    ∃ s' n, Ev main (mergeStep hp) ⟨g, X⟩ s' n ∧ n ≤ 6 ∧
      s'.stk = X ∧ s'.reg lvF = Glyph.eos := by
  have h1 : Ev main (.peek lvIn lvP) ⟨g, X⟩
      ⟨Function.update g lvP ((X lvIn).headD Glyph.eos), X⟩ 1 :=
    ev_peek' main lvIn lvP g X
  have hhead : (X lvIn).headD Glyph.eos = Glyph.nil := by rw [hin]; rfl
  have h2 : Ev main (.ite lvP Glyph.nil (.set lvF Glyph.eos) (mergeMid hp))
      ⟨Function.update g lvP ((X lvIn).headD Glyph.eos), X⟩
      ⟨Function.update (Function.update g lvP ((X lvIn).headD Glyph.eos)) lvF Glyph.eos, X⟩ 2 :=
    Ev.iteT (hr := by simp only [regUpd_same]; exact hhead)
      (ev_set' main lvF Glyph.eos _ _)
  have hmain : Ev main (mergeStep hp) ⟨g, X⟩
      ⟨Function.update (Function.update g lvP ((X lvIn).headD Glyph.eos)) lvF Glyph.eos, X⟩ 3 := by
    unfold mergeStep
    simp only [seqs]
    exact Ev.seq h1 h2
  exact ⟨_, _, hmain, by omega, by simp, by simp⟩

theorem mergeStepLast_ev (main hp : Cmd) (g : Reg → Glyph) (X : Stk → List Glyph)
    (G1 : List (List Val)) (acc : List Val) (T0 T9 Tmp : List Glyph)
    (h0 : X 0 = encs acc ++ gMark :: T0)
    (hin : X lvIn = encsC [grpVal G1] ++ [Glyph.nil] ++ gMark :: T9)
    (htmp : X lvTmp = gMark :: Tmp) :
    ∃ s' n, Ev main (mergeStep hp) ⟨g, X⟩ s' n ∧
      n ≤ 80 * (vsz (grpVal G1) + 1) + 400 ∧
      s'.stk 0 = encs (grpVal G1 :: acc) ++ gMark :: T0 ∧
      s'.stk lvIn = [Glyph.nil] ++ gMark :: T9 ∧
      s'.stk lvTmp = gMark :: Tmp ∧
      s'.reg lvF = Glyph.eos ∧
      (∀ j, j ≠ 0 → j ≠ lvIn → j ≠ lvTmp → s'.stk j = X j) := by
  have hin' : X lvIn = Glyph.cons :: (grpVal G1).enc ++ ([Glyph.nil] ++ gMark :: T9) := by
    rw [hin]
    exact mlv_encsC_single G1 T9
  obtain ⟨s', n', h2, hn', h0', hin'', htmp', hrF', hfr'⟩ :=
    mergeMidLast_ev (main := main) (hp := hp)
      (g := Function.update g lvP ((X lvIn).headD Glyph.eos)) X G1 acc T0 T9 Tmp h0 hin' htmp
  have h1 : Ev main (.peek lvIn lvP) ⟨g, X⟩
      ⟨Function.update g lvP ((X lvIn).headD Glyph.eos), X⟩ 1 := ev_peek' main lvIn lvP g X
  have hhead : (X lvIn).headD Glyph.eos = Glyph.cons := by rw [hin']; rfl
  have hne : (Function.update g lvP ((X lvIn).headD Glyph.eos)) lvP ≠ Glyph.nil := by
    simp only [regUpd_same, hhead]; decide
  have h2' : Ev main (.ite lvP Glyph.nil (.set lvF Glyph.eos) (mergeMid hp))
      ⟨Function.update g lvP ((X lvIn).headD Glyph.eos), X⟩ s' (n' + 1) :=
    Ev.iteF (hr := hne) h2
  have hmain : Ev main (mergeStep hp) ⟨g, X⟩ s' (1 + (n' + 1)) := by
    unfold mergeStep
    simp only [seqs]
    exact Ev.seq h1 h2'
  exact ⟨s', _, hmain, by omega, h0', hin'', htmp', hrF', hfr'⟩

theorem mergeStepPair_ev (main hp : Cmd) (KH : ℕ)
    (hpair : ∀ (m : Cmd) (G₁ G₂ : List (List Val)) (rest : List Val),
      HvdH.WordR m hp
        (fun vs => vs = grpVal G₁ :: grpVal G₂ :: rest)
        (fun _ out => out = grpVal (zipCat G₁ G₂) :: rest)
        (fun _ => KH * (vsz (grpVal G₁) + vsz (grpVal G₂) + 1) + KH))
    (g : Reg → Glyph) (X : Stk → List Glyph) (G1 G2 : List (List Val)) (acc : List Val)
    (A : List Glyph) (T0 T9 Tmp : List Glyph)
    (h0 : X 0 = encs acc ++ gMark :: T0)
    (hin : X lvIn = Glyph.cons :: (grpVal G1).enc ++ (Glyph.cons :: (grpVal G2).enc ++ A))
    (htmp : X lvTmp = gMark :: Tmp) :
    ∃ s' n, Ev main (mergeStep hp) ⟨g, X⟩ s' n ∧
      n ≤ (KH + 4000) * ((vsz (grpVal G1) + 1) + (vsz (grpVal G2) + 1)) + KH + 4000 ∧
      s'.stk 0 = encs (grpVal (zipCat G1 G2) :: acc) ++ gMark :: T0 ∧
      s'.stk lvIn = A ∧
      s'.stk lvTmp = gMark :: Tmp ∧
      s'.reg lvF = Glyph.cons ∧
      (∀ j, j ≠ 0 → j ≠ lvIn → j ≠ lvTmp → s'.stk j = X j) := by
  obtain ⟨s', n', h2, hn', h0', hin'', htmp', hrF', hfr'⟩ :=
    mergeMidPair_ev (main := main) (hp := hp) (KH := KH) hpair
      (Function.update g lvP ((X lvIn).headD Glyph.eos)) X G1 G2 acc A T0 T9 Tmp h0 hin htmp
  have h1 : Ev main (.peek lvIn lvP) ⟨g, X⟩
      ⟨Function.update g lvP ((X lvIn).headD Glyph.eos), X⟩ 1 := ev_peek' main lvIn lvP g X
  have hhead : (X lvIn).headD Glyph.eos = Glyph.cons := by rw [hin]; rfl
  have hne : (Function.update g lvP ((X lvIn).headD Glyph.eos)) lvP ≠ Glyph.nil := by
    simp only [regUpd_same, hhead]; decide
  have h2' : Ev main (.ite lvP Glyph.nil (.set lvF Glyph.eos) (mergeMid hp))
      ⟨Function.update g lvP ((X lvIn).headD Glyph.eos), X⟩ s' (n' + 1) :=
    Ev.iteF (hr := hne) h2
  have hmain : Ev main (mergeStep hp) ⟨g, X⟩ s' (1 + (n' + 1)) := by
    unfold mergeStep
    simp only [seqs]
    exact Ev.seq h1 h2'
  exact ⟨s', _, hmain, by omega, h0', hin'', htmp', hrF', hfr'⟩

/-! ## The merge walk -/

theorem mergeWalk (main hp : Cmd) (KH KM : ℕ)
    (hpair : ∀ (m : Cmd) (G₁ G₂ : List (List Val)) (rest : List Val),
      HvdH.WordR m hp
        (fun vs => vs = grpVal G₁ :: grpVal G₂ :: rest)
        (fun _ out => out = grpVal (zipCat G₁ G₂) :: rest)
        (fun _ => KH * (vsz (grpVal G₁) + vsz (grpVal G₂) + 1) + KH))
    (hKM : 2 * KH + 8000 ≤ KM) :
    ∀ (Ls : List (List (List Val))) (acc : List Val) (T0 T9 Tmp : List Glyph)
      (g : Reg → Glyph) (X : Stk → List Glyph),
      g lvF = Glyph.cons →
      X 0 = encs acc ++ gMark :: T0 →
      X lvIn = encsC (Ls.map grpVal) ++ [Glyph.nil] ++ gMark :: T9 →
      X lvTmp = gMark :: Tmp →
      ∃ s' n, Ev main (.loop lvF Glyph.cons (mergeStep hp)) ⟨g, X⟩ s' n ∧ n ≤ mlvCost KM Ls ∧
        s'.stk 0 = encs ((mLevel Ls).reverse.map grpVal ++ acc) ++ gMark :: T0 ∧
        s'.stk lvIn = [Glyph.nil] ++ gMark :: T9 ∧
        s'.stk lvTmp = gMark :: Tmp ∧
        s'.reg lvF = Glyph.eos ∧
        (∀ j, j ≠ 0 → j ≠ lvIn → j ≠ lvTmp → s'.stk j = X j) := by
  intro Ls
  induction Ls using mLevel.induct with
  | case1 =>
      intro acc T0 T9 Tmp g X hg h0 hin htmp
      have hin' : X lvIn = [Glyph.nil] ++ gMark :: T9 := by
        simpa only [List.map_nil, encsC_nil, List.nil_append] using hin
      obtain ⟨s', n, hstep, hn, hstk, hrF⟩ := mergeStepStop_ev (main := main) (hp := hp) g X T9 hin'
      have hloop : Ev main (.loop lvF Glyph.cons (mergeStep hp)) ⟨g, X⟩ s' (n + 1 + 1) :=
        Ev.loopT hg hstep (Ev.loopF (by rw [hrF]; decide))
      refine ⟨s', n + 2, hloop, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [mlvCost_nil]; omega
      · rw [hstk, h0]
        simp only [mLevel, List.map_nil, List.reverse_nil, List.nil_append]
      · rw [hstk]; exact hin'
      · rw [hstk]; exact htmp
      · exact hrF
      · intro j hj0 hjin hjt
        rw [hstk]
  | case2 G1 =>
      intro acc T0 T9 Tmp g X hg h0 hin htmp
      have hin' : X lvIn = encsC [grpVal G1] ++ [Glyph.nil] ++ gMark :: T9 := by
        simpa only [List.map_cons, List.map_nil] using hin
      obtain ⟨s', n, hstep, hn, h0', hin'', htmp', hrF, hfr⟩ :=
        mergeStepLast_ev (main := main) (hp := hp) g X G1 acc T0 T9 Tmp h0 hin' htmp
      have hloop : Ev main (.loop lvF Glyph.cons (mergeStep hp)) ⟨g, X⟩ s' (n + 1 + 1) :=
        Ev.loopT hg hstep (Ev.loopF (by rw [hrF]; decide))
      have hc : mlvCost KM [G1] = KM * (vsz (grpVal G1) + 1) + KM := by
        rw [mlvCost_cons, mlvCost_nil]
      refine ⟨s', n + 2, hloop, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hc]
        have hv : 2 ≤ vsz (grpVal G1) + 1 := by have h := one_le_vsz (grpVal G1); omega
        nlinarith [hn, hKM, hv]
      · rw [h0']
        simp only [mLevel_singleton, List.reverse_cons, List.reverse_nil, List.nil_append,
          List.map_cons, List.map_nil, List.singleton_append, List.cons_append]
      · exact hin''
      · exact htmp'
      · exact hrF
      · exact hfr
  | case3 G1 G2 rest ih =>
      intro acc T0 T9 Tmp g X hg h0 hin htmp
      have hin' : X lvIn = Glyph.cons :: (grpVal G1).enc ++ (Glyph.cons :: (grpVal G2).enc ++
          (encsC (rest.map grpVal) ++ [Glyph.nil] ++ gMark :: T9)) := by
        rw [hin]
        exact mlv_encsC_pair_tail G1 G2 rest T9
      obtain ⟨s₁, n₁, hstep, hn₁, h0₁, hin₁, htmp₁, hrF₁, hfr₁⟩ :=
        mergeStepPair_ev (main := main) (hp := hp) (KH := KH) hpair g X G1 G2 acc
          (encsC (rest.map grpVal) ++ [Glyph.nil] ++ gMark :: T9) T0 T9 Tmp h0 hin' htmp
      obtain ⟨s₂, n₂, hrest, hn₂, h0₂, hin₂, htmp₂, hrF₂, hfr₂⟩ :=
        ih (grpVal (zipCat G1 G2) :: acc) T0 T9 Tmp s₁.reg s₁.stk hrF₁ h0₁ hin₁ htmp₁
      have hloop : Ev main (.loop lvF Glyph.cons (mergeStep hp)) ⟨g, X⟩ s₂ (n₁ + n₂ + 1) :=
        Ev.loopT hg hstep hrest
      refine ⟨s₂, n₁ + n₂ + 1, hloop, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have hv1 := one_le_vsz (grpVal G1)
        have hv2 := one_le_vsz (grpVal G2)
        have hS2 : 2 ≤ (vsz (grpVal G1) + 1) + (vsz (grpVal G2) + 1) := by omega
        have hmul1 := Nat.mul_le_mul_left (vsz (grpVal G1) + 1) hKM
        have hmul2 := Nat.mul_le_mul_left (vsz (grpVal G2) + 1) hKM
        have hsum : KM * ((vsz (grpVal G1) + 1) + (vsz (grpVal G2) + 1)) =
            KM * (vsz (grpVal G1) + 1) + KM * (vsz (grpVal G2) + 1) :=
          Nat.mul_add KM _ _
        rw [mlvCost_cons, mlvCost_cons]
        nlinarith [hn₁, hn₂, hmul1, hmul2, hsum, hS2]
      · have hacc : (mLevel (G1 :: G2 :: rest)).reverse.map grpVal ++ acc =
            (mLevel rest).reverse.map grpVal ++ (grpVal (zipCat G1 G2) :: acc) := by
          rw [mLevel_cons_cons, List.reverse_cons, List.map_append, List.map_cons, List.map_nil]
          rw [List.append_assoc]
          rfl
        rw [hacc]
        exact h0₂
      · exact hin₂
      · exact htmp₂
      · exact hrF₂
      · intro j hj0 hjin hjt
        rw [hfr₂ j hj0 hjin hjt, hfr₁ j hj0 hjin hjt]

/-! ## The merge loop -/

theorem mergeLoop_ev (main hp : Cmd) (KH : ℕ)
    (hpair : ∀ (m : Cmd) (G₁ G₂ : List (List Val)) (rest : List Val),
      HvdH.WordR m hp
        (fun vs => vs = grpVal G₁ :: grpVal G₂ :: rest)
        (fun _ out => out = grpVal (zipCat G₁ G₂) :: rest)
        (fun _ => KH * (vsz (grpVal G₁) + vsz (grpVal G₂) + 1) + KH)) :
    ∀ (Ls : List (List (List Val))) (acc : List Val) (T0 T9 Tmp : List Glyph)
      (g : Reg → Glyph) (X : Stk → List Glyph),
      X 0 = encs acc ++ gMark :: T0 →
      X lvIn = encsC (Ls.map grpVal) ++ [Glyph.nil] ++ gMark :: T9 →
      X lvTmp = gMark :: Tmp →
      ∃ s' n, Ev main (mergeLoop hp) ⟨g, X⟩ s' n ∧ n ≤ mlvCost (2 * KH + 8000) Ls + 4 ∧
        s'.stk 0 = encs ((mLevel Ls).reverse.map grpVal ++ acc) ++ gMark :: T0 ∧
        s'.stk lvIn = [Glyph.nil] ++ gMark :: T9 ∧
        s'.stk lvTmp = gMark :: Tmp ∧
        (∀ j, j ≠ 0 → j ≠ lvIn → j ≠ lvTmp → s'.stk j = X j) := by
  intro Ls acc T0 T9 Tmp g X h0 hin htmp
  have hset : Ev main (.set lvF Glyph.cons) ⟨g, X⟩
      ⟨Function.update g lvF Glyph.cons, X⟩ 1 := ev_set' main lvF Glyph.cons g X
  obtain ⟨s', n', hloop, hn', h0', hin', htmp', _hrF', hfr'⟩ :=
    mergeWalk main hp KH (2 * KH + 8000) hpair (le_refl _) Ls acc T0 T9 Tmp
      (Function.update g lvF Glyph.cons) X (by simp) h0 hin htmp
  have hmain : Ev main (mergeLoop hp) ⟨g, X⟩ s' (1 + n') := by
    unfold mergeLoop
    simp only [seqs]
    exact Ev.seq hset hloop
  exact ⟨s', _, hmain, by omega, h0', hin', htmp', hfr'⟩

/-! ## The prologue, the output setup and the epilogue -/

theorem mergeSetup_ev (main : Cmd) (V : Val) (rest : List Val) (g : Reg → Glyph)
    (X : Stk → List Glyph) (R : List Glyph) (h : X 0 = encs (V :: rest) ++ R) :
    ∃ s' n, Ev main mergeSetup ⟨g, X⟩ s' n ∧ n ≤ 20 * (vsz V + 1) + 12 ∧
      s'.stk 0 = gMark :: (encs rest ++ R) ∧
      s'.stk lvIn = V.enc ++ gMark :: X lvIn ∧
      s'.stk lvTmp = gMark :: X lvTmp ∧
      (∀ j, j ≠ 0 → j ≠ lvIn → j ≠ lvTmp → s'.stk j = X j) := by
  obtain ⟨s₁, n₁, h1, hn₁, hin₁, hfr₁⟩ :=
    Work.Layout.AA.pushGlyphs_ev main [gMark] lvIn lvG g X
  have h₁ : s₁.stk 0 = V.enc ++ (encs rest ++ R) := by
    rw [hfr₁ 0 (by decide), h]
    simp only [Work.Kernel.encs_cons, List.append_assoc]
  obtain ⟨s₂, n₂, h2, hn₂, h0₂, hin₂, _hc₂, _hd₂, hfr₂⟩ :=
    Work.Layout.AA.mvVal_ev' (main := main) (a := 0) (b := lvIn) (c := lvS1) (d := lvS2)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s₁.reg) (X := s₁.stk) (v := V) (A := encs rest ++ R) (B := s₁.stk lvIn) h₁ rfl
  obtain ⟨s₃, n₃, h3, hn₃, htmp₃, hfr₃⟩ :=
    Work.Layout.AA.pushGlyphs_ev main [gMark] lvTmp lvG s₂.reg s₂.stk
  obtain ⟨s₄, n₄, h4, hn₄, h0₄, hfr₄⟩ :=
    Work.Layout.AA.pushGlyphs_ev main [gMark] 0 lvG s₃.reg s₃.stk
  have hmain : Ev main mergeSetup ⟨g, X⟩ s₄ (n₁ + n₂ + n₃ + n₄) := by
    unfold mergeSetup
    simp only [seqs]
    exact (Ev.seq h1 (Ev.seq h2 (Ev.seq h3 h4))).mono (by omega)
  have hstk0 : s₄.stk 0 = gMark :: (encs rest ++ R) := by
    rw [h0₄, hfr₃ 0 (by decide), h0₂]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
      List.cons_append]
  have hstkin : s₄.stk lvIn = V.enc ++ gMark :: X lvIn := by
    rw [hfr₄ lvIn (by decide), hfr₃ lvIn (by decide), hin₂, hin₁]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
  have hstktmp : s₄.stk lvTmp = gMark :: X lvTmp := by
    rw [hfr₄ lvTmp (by decide), htmp₃, hfr₂ lvTmp (by decide) (by decide), hfr₁ lvTmp (by decide)]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
  refine ⟨s₄, _, hmain, ?_, hstk0, hstkin, hstktmp, ?_⟩
  · have hlen : ([gMark] : List Glyph).length = 1 := rfl
    have h1' : n₁ ≤ 3 := by rw [hlen] at hn₁; omega
    have h3' : n₃ ≤ 3 := by rw [hlen] at hn₃; omega
    have h4' : n₄ ≤ 3 := by rw [hlen] at hn₄; omega
    have hv := one_le_vsz V
    omega
  · intro j hj0 hjin hjt
    rw [hfr₄ j hj0, hfr₃ j hjt, hfr₂ j hj0 hjin, hfr₁ j hjin]

theorem outSetup_ev (main : Cmd) (g : Reg → Glyph) (X : Stk → List Glyph) :
    ∃ s' n, Ev main outSetup ⟨g, X⟩ s' n ∧ n ≤ 8 ∧
      s'.stk lvOut = (ofList ([] : List Val)).enc ++ gMark :: X lvOut ∧
      (∀ j, j ≠ lvOut → s'.stk j = X j) := by
  obtain ⟨s₁, n₁, h1, hn₁, hout₁, hfr₁⟩ :=
    Work.Layout.AA.pushGlyphs_ev main [gMark] lvOut lvG g X
  obtain ⟨s₂, n₂, h2, hn₂, hout₂, hfr₂⟩ :=
    Work.Layout.AA.pushGlyphs_ev main [Glyph.nil] lvOut lvG s₁.reg s₁.stk
  have hmain : Ev main outSetup ⟨g, X⟩ s₂ (n₁ + n₂) := by
    unfold outSetup
    simp only [seqs]
    exact Ev.seq h1 h2
  have hout : s₂.stk lvOut = (ofList ([] : List Val)).enc ++ gMark :: X lvOut := by
    rw [hout₂, hout₁]
    rw [show (ofList ([] : List Val)).enc = [Glyph.nil] from rfl]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
      List.cons_append]
  refine ⟨s₂, _, hmain, ?_, hout, ?_⟩
  · have hlen : ([Glyph.nil] : List Glyph).length = 1 := rfl
    have hlenG : ([gMark] : List Glyph).length = 1 := rfl
    have h1' : n₁ ≤ 3 := by rw [hlenG] at hn₁; omega
    have h2' : n₂ ≤ 3 := by rw [hlen] at hn₂; omega
    omega
  · intro j hj
    rw [hfr₂ j hj, hfr₁ j hj]

theorem mergeFinish_ev (main : Cmd) (V : Val) (T0 B : List Glyph)
    (g : Reg → Glyph) (X : Stk → List Glyph) (Zin Ztmp : List Glyph)
    (h0 : X 0 = gMark :: T0)
    (hOut : X lvOut = V.enc ++ gMark :: B)
    (hin : X lvIn = [Glyph.nil] ++ gMark :: Zin)
    (htmp : X lvTmp = gMark :: Ztmp) :
    ∃ s' n, Ev main mergeFinish ⟨g, X⟩ s' n ∧
      n ≤ 20 * (vsz V + 1) + 70 ∧
      s'.stk 0 = V.enc ++ T0 ∧
      s'.stk lvIn = Zin ∧ s'.stk lvOut = B ∧ s'.stk lvTmp = Ztmp ∧
      (∀ j, j ≠ 0 → j ≠ lvIn → j ≠ lvOut → j ≠ lvTmp → s'.stk j = X j) := by
  have hclear0 : X 0 = ([] : List Glyph) ++ gMark :: T0 := h0
  obtain ⟨s₁, n₁, h1, hn₁, h0₁, hfr₁⟩ :=
    Work.Layout.AA.clearTo_ev main 0 lvP lvF (by decide) g X [] T0 (by simp) hclear0
  have hOut₁ : s₁.stk lvOut = V.enc ++ gMark :: B := by
    rw [hfr₁ lvOut (by decide), hOut]
  obtain ⟨s₂, n₂, h2, hn₂, hout₂, h0₂, _hc₂, _hd₂, hfr₂⟩ :=
    Work.Layout.AA.mvVal_ev' (main := main) (a := lvOut) (b := 0) (c := lvS1) (d := lvS2)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s₁.reg) (X := s₁.stk) (v := V) (A := gMark :: B) (B := T0) hOut₁ h0₁
  obtain ⟨s₃, n₃, h3, hn₃, hout₃, hfr₃⟩ :=
    Work.Layout.AA.clearTo_ev main lvOut lvP lvF (by decide) s₂.reg s₂.stk [] B (by simp)
      (by rw [hout₂]; rfl)
  have hin₂ : s₂.stk lvIn = [Glyph.nil] ++ gMark :: Zin := by
    rw [hfr₂ lvIn (by decide) (by decide), hfr₁ lvIn (by decide), hin]
  obtain ⟨s₄, n₄, h4, hn₄, hin₄, hfr₄⟩ :=
    Work.Layout.AA.clearTo_ev main lvIn lvP lvF (by decide) s₃.reg s₃.stk [Glyph.nil] Zin
      (by decide) (by rw [hfr₃ lvIn (by decide), hin₂]; rfl)
  have htmp₂ : s₃.stk lvTmp = gMark :: Ztmp := by
    rw [hfr₃ lvTmp (by decide), hfr₂ lvTmp (by decide) (by decide), hfr₁ lvTmp (by decide), htmp]
  obtain ⟨s₅, n₅, h5, hn₅, htmp₅, hfr₅⟩ :=
    Work.Layout.AA.clearTo_ev main lvTmp lvP lvF (by decide) s₄.reg s₄.stk [] Ztmp (by simp)
      (by rw [hfr₄ lvTmp (by decide), htmp₂]; rfl)
  have hmain : Ev main mergeFinish ⟨g, X⟩ s₅ (n₁ + n₂ + n₃ + n₄ + n₅) := by
    unfold mergeFinish
    simp only [seqs]
    exact (Ev.seq h1 (Ev.seq h2 (Ev.seq h3 (Ev.seq h4 h5)))).mono (by omega)
  have hA : s₅.stk 0 = V.enc ++ T0 := by
    rw [hfr₅ 0 (by decide), hfr₄ 0 (by decide), hfr₃ 0 (by decide), h0₂]
  have hB : s₅.stk lvIn = Zin := by
    rw [hfr₅ lvIn (by decide), hin₄]
  have hC : s₅.stk lvOut = B := by
    rw [hfr₅ lvOut (by decide), hfr₄ lvOut (by decide), hout₃]
  refine ⟨s₅, _, hmain, ?_, hA, hB, hC, htmp₅, ?_⟩
  · have hlen0 : ([] : List Glyph).length = 0 := rfl
    have hlen1 : ([Glyph.nil] : List Glyph).length = 1 := rfl
    have h1' : n₁ ≤ 9 := by rw [hlen0] at hn₁; omega
    have h3' : n₃ ≤ 9 := by rw [hlen0] at hn₃; omega
    have h4' : n₄ ≤ 14 := by rw [hlen1] at hn₄; omega
    have h5' : n₅ ≤ 9 := by rw [hlen0] at hn₅; omega
    have hv := one_le_vsz V
    omega
  · intro j hj0 hjin hjout hjt
    rw [hfr₅ j hjt, hfr₄ j hjin, hfr₃ j hjout, hfr₂ j hjout hj0, hfr₁ j hj0]

/-! ## Size of the fold accumulator -/

theorem mlv_vSz_mLevel_reverse_le (Ls : List (List (List Val))) :
    (((mLevel Ls).reverse.map grpVal).map (fun v => vsz v + 1)).sum ≤ 2 * vsz (stateVal Ls) := by
  have h1 : (((mLevel Ls).reverse.map grpVal).map (fun v => vsz v + 1)).sum
      = vSz ((mLevel Ls).reverse.map grpVal) := rfl
  rw [h1, vSz_map_grpVal, mlv_gSz_reverse]
  have h2 := mlv_gSz_mLevel_le Ls
  have h3 := vsz_stateVal Ls
  omega

/-! ## The whole word -/

/-- the one-merge-level word, with an explicit flag reset before the fold (so that the fold loop is
entered with `lvF = cons`). -/
def mergeLevelProg2 (hp : Cmd) : Cmd :=
  Work.Layout.seqs
    [mergeSetup, mergeLoop hp, outSetup, HvdH.Cmd.set lvF Glyph.cons, foldLoop, mergeFinish]

theorem mergeLevelEv (main hp : Cmd) (KH : ℕ)
    (hpair : ∀ (m : Cmd) (G₁ G₂ : List (List Val)) (rest : List Val),
      HvdH.WordR m hp
        (fun vs => vs = grpVal G₁ :: grpVal G₂ :: rest)
        (fun _ out => out = grpVal (zipCat G₁ G₂) :: rest)
        (fun _ => KH * (vsz (grpVal G₁) + vsz (grpVal G₂) + 1) + KH)) :
    ∀ (Gs : List (List (List Val))) (rest : List Val) (g : Reg → Glyph)
      (X : Stk → List Glyph) (R : List Glyph),
      X 0 = encs (stateVal Gs :: rest) ++ R →
      ∃ s' n, Ev main (mergeLevelProg2 hp) ⟨g, X⟩ s' n ∧
        n ≤ (4 * KH + 30000) * (vsz (stateVal Gs) + 1) + (4 * KH + 30000) ∧
        s'.stk 0 = encs (stateVal (mLevel Gs) :: rest) ++ R ∧
        (∀ k, k ≠ 0 → s'.stk k = X k) := by
  intro Gs rest g X R hX
  obtain ⟨s₁, n₁, h1, hn₁, h0₁, hin₁, htmp₁, hfr₁⟩ :=
    mergeSetup_ev main (stateVal Gs) rest g X R hX
  have hin₁' : s₁.stk lvIn = encsC (Gs.map grpVal) ++ [Glyph.nil] ++ gMark :: X lvIn := by
    rw [hin₁]
    simp only [stateVal, enc_ofList, List.append_assoc]
  have h0₁' : s₁.stk 0 = encs ([] : List Val) ++ gMark :: (encs rest ++ R) := by
    rw [h0₁]; rfl
  obtain ⟨s₂, n₂, h2, hn₂, h0₂, hin₂, htmp₂, hfr₂⟩ :=
    mergeLoop_ev main hp KH hpair Gs [] (encs rest ++ R)
      (X lvIn) (X lvTmp) s₁.reg s₁.stk h0₁' hin₁' (by rw [htmp₁])
  obtain ⟨s₃, n₃, h3, hn₃, hout₃, hfr₃⟩ := outSetup_ev main s₂.reg s₂.stk
  have h0₃ : s₃.stk 0 = encs ((mLevel Gs).reverse.map grpVal) ++ gMark :: (encs rest ++ R) := by
    rw [hfr₃ 0 (by decide), h0₂, List.append_nil]
  have hout₃' : s₃.stk lvOut = (ofList ([] : List Val)).enc ++ gMark :: X lvOut := by
    rw [hout₃, hfr₂ lvOut (by decide) (by decide) (by decide),
      hfr₁ lvOut (by decide) (by decide) (by decide)]
  obtain ⟨s₅, n₅, h5, hn₅, h0₅, hout₅, _hrF₅, hfr₅⟩ :=
    foldLoopEv main ((mLevel Gs).reverse.map grpVal) [] (encs rest ++ R) (X lvOut)
      (Function.update s₃.reg lvF Glyph.cons) s₃.stk (by simp) h0₃ hout₃'
  have hacc : ((mLevel Gs).reverse.map grpVal).reverse ++ [] = (mLevel Gs).map grpVal := by
    rw [mlv_map_reverse_eq, List.reverse_reverse, List.append_nil]
  have hin₅ : s₅.stk lvIn = [Glyph.nil] ++ gMark :: X lvIn := by
    rw [hfr₅ lvIn (by decide) (by decide), hfr₃ lvIn (by decide), hin₂]
  have htmp₅ : s₅.stk lvTmp = gMark :: X lvTmp := by
    rw [hfr₅ lvTmp (by decide) (by decide), hfr₃ lvTmp (by decide), htmp₂]
  have hout₅' : s₅.stk lvOut = (stateVal (mLevel Gs)).enc ++ gMark :: X lvOut := by
    rw [hout₅, hacc]
    rfl
  obtain ⟨s₆, n₆, h6, hn₆, h0₆, hin₆, hout₆, htmp₆, hfr₆⟩ :=
    mergeFinish_ev main (stateVal (mLevel Gs)) (encs rest ++ R) (X lvOut) s₅.reg s₅.stk
      (X lvIn) (X lvTmp) h0₅ hout₅' hin₅ htmp₅
  have hmain : Ev main (mergeLevelProg2 hp) ⟨g, X⟩ s₆ (n₁ + n₂ + n₃ + 1 + n₅ + n₆) := by
    unfold mergeLevelProg2
    simp only [seqs]
    exact (Ev.seq h1 (Ev.seq h2 (Ev.seq h3 (Ev.seq
      (ev_set' main lvF Glyph.cons s₃.reg s₃.stk) (Ev.seq h5 h6))))).mono (by omega)
  have hstk : s₆.stk 0 = encs (stateVal (mLevel Gs) :: rest) ++ R := by
    rw [h0₆, Work.Kernel.encs_cons, List.append_assoc]
  refine ⟨s₆, n₁ + n₂ + n₃ + 1 + n₅ + n₆, hmain, ?_, hstk, ?_⟩
  · have hV1 : 1 ≤ vsz (stateVal Gs) := one_le_vsz _
    have hsum := mlv_vSz_mLevel_reverse_le Gs
    have hml := mlvCost_stateVal (2 * KH + 8000) Gs
    have hn₂' : n₂ ≤ (2 * KH + 8000) * vsz (stateVal Gs) + 4 := by
      rw [← hml]; exact hn₂
    have hn₅' : n₅ ≤ 80 * vsz (stateVal Gs) + 80 := by
      have h := hn₅
      omega
    have hn₆' : n₆ ≤ 40 * vsz (stateVal Gs) + 110 := by
      have h := hn₆
      have h2 := mlv_gSz_mLevel_le Gs
      have h3 := vsz_stateVal (mLevel Gs)
      have h4 := vsz_stateVal Gs
      omega
    nlinarith [hn₁, hn₂', hn₃, hn₅', hn₆', hV1]
  · intro k hk
    by_cases hkin : k = lvIn
    · subst hkin; exact hin₆
    by_cases hkout : k = lvOut
    · subst hkout; exact hout₆
    by_cases hktmp : k = lvTmp
    · subst hktmp; exact htmp₆
    rw [hfr₆ k hk hkin hkout hktmp, hfr₅ k hk hkout,
      hfr₃ k hkout, hfr₂ k hk hkin hktmp, hfr₁ k hk hkin hktmp]

-- ONE MERGE LEVEL, stated relative to any pairwise-merge word (see the zipCatWord task).
-- stateVal Gs = ofList (Gs.map grpVal) is the value of a list of groups; mLevel merges adjacent
-- groups with zipCat, keeping a dangling last group. Suggested implementation: move the input list
-- to a scratch stack above a boundary marker (Work.Layout.gMark) with Work.Layout.mvVal; keep a
-- stack of values on stack 0 as the accumulator (top = last processed element, marker below); walk
-- the input, popping the leading cons with Work.Layout.AA.unconsTo (cost 20*(vsz g+1)) and pushing
-- the element on the accumulator; if a parity register says an unpaired element is on top, swap it
-- with the element and run hpair on the top two values (giving accumulator order
-- [pending, m_{k-1},...,m_0]); finally fold the accumulator into a list value with
-- Work.Layout.AA.prependTo (each step O(vsz v), independent of the accumulated list), yielding
-- ofList (mLevel Gs) without a reversal. Per-element costs telescope to O(vsz (stateVal Gs)).
-- The built-in WordR frame restores stacks ≠ 0.
theorem mergeLevelWord
    (hpair : ∃ (prog : HvdH.Cmd) (K : ℕ),
      ∀ (main : HvdH.Cmd) (G₁ G₂ : List (List HvdH.Val)) (rest : List HvdH.Val),
        HvdH.WordR main prog
          (fun vs => vs = Work.SynFFT.grpVal G₁ :: Work.SynFFT.grpVal G₂ :: rest)
          (fun _ out => out = Work.SynFFT.grpVal (Work.SynFFT.zipCat G₁ G₂) :: rest)
          (fun _ => K * (HvdH.vsz (Work.SynFFT.grpVal G₁) + HvdH.vsz (Work.SynFFT.grpVal G₂) + 1) + K)) :
    ∃ (prog : HvdH.Cmd) (K : ℕ),
      ∀ (main : HvdH.Cmd) (Gs : List (List (List HvdH.Val))) (rest : List HvdH.Val),
        HvdH.WordR main prog
          (fun vs => vs = Work.SynFFT.stateVal Gs :: rest)
          (fun _ out => out = Work.SynFFT.stateVal (Work.SynFFT.mLevel Gs) :: rest)
          (fun _ => K * (HvdH.vsz (Work.SynFFT.stateVal Gs) + 1) + K) := by
  obtain ⟨hp, KH, hpairSpec⟩ := hpair
  refine ⟨mergeLevelProg2 hp, 4 * KH + 30000, ?_⟩
  intro main Gs rest
  rw [HvdH.WordR]
  intro vs hvs s R hs0
  subst hvs
  obtain ⟨s', n, hev, hcost, hstk0, hfr⟩ :=
    mergeLevelEv main hp KH hpairSpec Gs rest s.reg s.stk R hs0
  obtain ⟨n', hev', hn'⟩ := hev
  exact ⟨stateVal (mLevel Gs) :: rest, s', n', rfl, hev', by omega, hstk0, hfr⟩


end Work.SynFFT
