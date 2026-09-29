import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Kernel.Raw
import Submission.Work.MainP.crtDefs
import Submission.Work.MainP.crtStripDefs
import Submission.Work.Layout.Base
import Submission.Work.Layout.Move

/-!
# `crtStripWord`: stripping the keys off a list of records

This file proves `Work.MainP.crtStripWord` on top of the shared definitions of
`Submission/Work/MainP/crtStripDefs.lean` (see there for the algorithm) and the raw toolkit of
`Submission/Work/Layout/Base.lean` (`Ev`, `cmdTouches`, `loopRuns`) and
`Submission/Work/Layout/Move.lean` (`mvA_loop_val`).

The value stack is stack 0, the output buffer stack 2, the pending-subtree counter of the mover
stack 1 (restored).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Work.MainP

open HvdH
open Work.Layout (Ev cmdTouches loopRuns)

/-- An `Eval` fact is an `Ev` fact with the exact cost as budget. -/
theorem ev_ofEval {main : Cmd} {p : Cmd} {s s' : State} {n : ℕ} (h : Eval main p s s' n) :
    Ev main p s s' n := ⟨n, h, le_rfl⟩

/-! ## 1. Bounded evaluation facts for the two `KernelLib` words -/

/-- Glyph-level form of `KernelLib.unconsV`: split the top value `cons a b` of stack 0. -/
theorem stripUnconsEv {up : Cmd} {Ku : ℕ}
    (hup : ∀ main : Cmd, WordR main up
      (fun vs => ∃ a b rest, vs = Val.cons a b :: rest)
      (fun vs out => ∃ a b rest, vs = Val.cons a b :: rest ∧ out = a :: b :: rest)
      (fun _ => Ku)) :
    ∀ (main : Cmd) (s : State) (a b : Val) (l : List Glyph),
      s.stk 0 = (Val.cons a b).enc ++ l →
      ∃ (s' : State) (n : ℕ), Eval main up s s' n ∧ n ≤ Ku ∧
        s'.stk 0 = a.enc ++ (b.enc ++ l) ∧ (∀ k : Stk, k ≠ 0 → s'.stk k = s.stk k) := by
  intro main s a b l h0
  have hpre : (fun vs : List Val => ∃ a b rest, vs = Val.cons a b :: rest) [Val.cons a b] :=
    ⟨a, b, [], rfl⟩
  have hstack : s.stk 0 = encs [Val.cons a b] ++ l := by
    rw [h0]; simp [encs_cons, encs_nil]
  obtain ⟨out, s', n, hpost, hev, hn, hstk, hoth⟩ := hup main [Val.cons a b] hpre s l hstack
  obtain ⟨a', b', rest, hvs, hout⟩ := hpost
  rw [List.cons.injEq] at hvs
  obtain ⟨h1, h2⟩ := hvs
  have hrest : rest = [] := h2.symm
  subst hrest
  obtain ⟨ha, hb⟩ := (Val.cons.injEq a b a' b').mp h1
  have hout' : out = a :: b :: ([] : List Val) := by rw [hout, ← ha, ← hb]
  refine ⟨s', n, hev, by simpa using hn, ?_, hoth⟩
  rw [hstk, hout']
  simp [encs_cons, encs_nil, List.append_assoc]

/-- Glyph-level form of `KernelLib.drop`. -/
theorem stripDropEv {dp : Cmd} {Kd : ℕ}
    (hdp : ∀ main : Cmd, WordR main dp (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun vs => Kd * (vsz (vs.headD .nil) + 1))) :
    ∀ (main : Cmd) (s : State) (v : Val) (l : List Glyph),
      s.stk 0 = v.enc ++ l →
      ∃ (s' : State) (n : ℕ), Eval main dp s s' n ∧ n ≤ Kd * (vsz v + 1) ∧
        s'.stk 0 = l ∧ (∀ k : Stk, k ≠ 0 → s'.stk k = s.stk k) := by
  intro main s v l h0
  have hpre : (fun vs : List Val => vs ≠ []) [v] := by simp
  have hstack : s.stk 0 = encs [v] ++ l := by
    rw [h0]; simp [encs_cons, encs_nil]
  obtain ⟨out, s', n, hpost, hev, hn, hstk, hoth⟩ := hdp main [v] hpre s l hstack
  obtain ⟨v', rest, hvs, hout⟩ := hpost
  rw [List.cons.injEq] at hvs
  obtain ⟨h1, h2⟩ := hvs
  have hrest : rest = [] := h2.symm
  subst hrest
  refine ⟨s', n, hev, ?_, ?_, hoth⟩
  · simpa [h1, List.headD_cons] using hn
  · rw [hstk, hout]; simp [encs_nil]

/-! ## 2. The loop test -/

/-- The loop test of the walk: peek the top glyph of stack 0 and set register 2 to `stripStop` (if
it is the `nil` of the empty list) or to `stripGo`. -/
theorem stripTestEv (main : Cmd) (S : State) (P : Prop) [Decidable P]
    (h : (S.stk 0).headD .eos = if P then Glyph.nil else Glyph.cons) :
    ∃ S' n, Ev main stripTest S S' n ∧ n ≤ 3 ∧ S'.stk 0 = S.stk 0 ∧
      S'.reg 2 = (if P then stripStop else stripGo) ∧
      (∀ k : Stk, k ≠ 0 → S'.stk k = S.stk k) := by
  have hpeek : Ev main (.peek 0 1) S (S.updReg 1 ((S.stk 0).headD .eos)) 1 :=
    Work.Layout.ev_peek main 0 1 S
  set S₁ : State := S.updReg 1 ((S.stk 0).headD .eos) with hS₁
  have hS₁reg : S₁.reg 1 = (if P then Glyph.nil else Glyph.cons) := by
    rw [hS₁]
    simp only [State.updReg_apply, if_pos rfl]
    exact h
  have hS₁stk0 : S₁.stk 0 = S.stk 0 := by rw [hS₁]; simp
  have hS₁stk : ∀ k : Stk, k ≠ 0 → S₁.stk k = S.stk k := by
    intro k _; rw [hS₁]; simp
  have hpeek' : Ev main (.peek 0 1) S S₁ 1 := by rw [hS₁]; exact hpeek
  by_cases hP : P
  · have hite : Ev main (.ite 1 Glyph.nil (.set 2 stripStop) (.set 2 stripGo)) S₁
        (S₁.updReg 2 stripStop) 2 := by
      refine Ev.iteT ?_ (Work.Layout.ev_set main 2 stripStop S₁)
      rw [hS₁reg, if_pos hP]
    refine ⟨S₁.updReg 2 stripStop, 3, Ev.seq' hpeek' hite (by omega), by omega, ?_, ?_, ?_⟩
    · rw [State.updReg_stk]; exact hS₁stk0
    · rw [if_pos hP]; simp
    · intro k hk0; rw [State.updReg_stk]; exact hS₁stk k hk0
  · have hite : Ev main (.ite 1 Glyph.nil (.set 2 stripStop) (.set 2 stripGo)) S₁
        (S₁.updReg 2 stripGo) 2 := by
      refine Ev.iteF ?_ (Work.Layout.ev_set main 2 stripGo S₁)
      rw [hS₁reg, if_neg hP]
      exact (by decide : Glyph.cons ≠ Glyph.nil)
    refine ⟨S₁.updReg 2 stripGo, 3, Ev.seq' hpeek' hite (by omega), by omega, ?_, ?_, ?_⟩
    · rw [State.updReg_stk]; exact hS₁stk0
    · rw [if_neg hP]; simp
    · intro k hk0; rw [State.updReg_stk]; exact hS₁stk k hk0

/-! ## 3. The marker-free value mover -/

/-- `stripMvA` touches only the stacks `a`, `c`, `d`. -/
theorem cmdTouches_stripMvA (a c d : Stk) : cmdTouches (stripMvA a c d) ⊆ {a, c, d} := by
  simp only [stripMvA, stripMvAInit, Cmd.seq, Work.Layout.pushConst, Work.Layout.seqs,
    Work.Layout.mvABody, Work.Layout.mvAPrefix, Work.Layout.decStep, cmdTouches]
  intro k hk
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton,
    Finset.notMem_empty] at hk ⊢
  tauto

/-- `stripMvA a c d` moves the top value of stack `a` to stack `c`, reversed, at cost `O(vsz v)`,
restoring everything else (stack `d` is returned to its old content). -/
theorem stripMvAEv {main : Cmd} {a c d : Stk} (hac : a ≠ c) (had : a ≠ d) (hcd : c ≠ d)
    (v : Val) (A C D : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph)
    (ha : X a = v.enc ++ A) (hc : X c = C) (hd : X d = D) :
    ∃ s' n, Ev main (stripMvA a c d) (⟨g, X⟩ : State) s' n ∧ n ≤ 10 * vsz v + 10 ∧
      s'.stk a = A ∧ s'.stk c = v.enc.reverse ++ C ∧ s'.stk d = D ∧
      (∀ k, k ≠ a → k ≠ c → k ≠ d → s'.stk k = X k) := by
  have h0 : Ev main (.set Work.Layout.rLoopG Glyph.cons) (⟨g, X⟩ : State)
      (⟨Function.update g Work.Layout.rLoopG Glyph.cons, X⟩ : State) 1 :=
    Work.Layout.ev_set' main Work.Layout.rLoopG Glyph.cons g X
  obtain ⟨s₁, n₁, h1, hn₁, hk₁, hf₁, -, hg₁⟩ :=
    Work.Layout.pushConst_ev (main := main) (k := d) (cst := Work.Layout.gSent)
      (g := Function.update g Work.Layout.rLoopG Glyph.cons) (X := X)
  obtain ⟨s₂, n₂, h2, hn₂, hk₂, hf₂, -, hg₂⟩ :=
    Work.Layout.pushConst_ev (main := main) (k := d) (cst := Work.Layout.gPend)
      (g := s₁.reg) (X := s₁.stk)
  have hreg₂ : s₂.reg Work.Layout.rLoopG = Glyph.cons := by
    rw [hg₂ Work.Layout.rLoopG (by decide), hg₁ Work.Layout.rLoopG (by decide)]
    simp
  have ha₂ : s₂.stk a = v.enc ++ A := by rw [hf₂ a had, hf₁ a had, ha]
  have hc₂ : s₂.stk c = C := by rw [hf₂ c hcd, hf₁ c hcd, hc]
  have hd₁ : s₁.stk d = Work.Layout.gSent :: D := by rw [hk₁, hd]
  have hd₂ : s₂.stk d = Work.Layout.gPend :: Work.Layout.gSent :: D := by rw [hk₂, hd₁]
  obtain ⟨s₃, hrun₃, ha₃, hc₃, hd₃, hr₃⟩ :=
    Work.Layout.mvA_loop_val (main := main) hac had hcd v [Work.Layout.gPend] A C D
      s₂.reg s₂.stk (by simp) (by intro x hx; simpa using hx) hreg₂ ha₂ hc₂ hd₂
  have hr₃' : s₃.reg Work.Layout.rLoopG ≠ Glyph.cons := by
    rw [hr₃]; simp [List.tail_cons]
  have hloop : Ev main (.loop Work.Layout.rLoopG Glyph.cons (Work.Layout.mvABody a c d))
      s₂ s₃ (10 * vsz v + 1) := Work.Layout.loopRuns.eval hrun₃ hr₃'
  have hd₃' : s₃.stk d = Work.Layout.gSent :: D := by rw [hd₃]; simp [List.tail_cons]
  set s₄ : State :=
    (⟨Function.update s₃.reg Work.Layout.rC ((s₃.stk d).headD .eos),
      Function.update s₃.stk d (s₃.stk d).tail⟩ : State) with hs₄
  have hpop : Ev main (.pop d Work.Layout.rC) s₃ s₄ 1 := by
    rw [hs₄]; exact Work.Layout.ev_pop' main d Work.Layout.rC s₃.reg s₃.stk
  have h12 : Ev main (.seq (Work.Layout.pushConst d Work.Layout.gSent)
      (Work.Layout.pushConst d Work.Layout.gPend))
      (⟨Function.update g Work.Layout.rLoopG Glyph.cons, X⟩ : State) s₂ (n₁ + n₂) :=
    Ev.seq' h1 h2 (le_refl (n₁ + n₂))
  have hinit : Ev main (stripMvAInit d) (⟨g, X⟩ : State) s₂ (1 + (n₁ + n₂)) := by
    unfold stripMvAInit
    exact Ev.seq' h0 h12 (le_refl (1 + (n₁ + n₂)))
  have htail : Ev main (.seq (.loop Work.Layout.rLoopG Glyph.cons (Work.Layout.mvABody a c d))
      (.pop d Work.Layout.rC)) s₂ s₄ (10 * vsz v + 1 + 1) :=
    Ev.seq' hloop hpop (le_refl (10 * vsz v + 1 + 1))
  have hmain : Ev main (stripMvA a c d) (⟨g, X⟩ : State) s₄
      ((1 + (n₁ + n₂)) + (10 * vsz v + 1 + 1)) := by
    unfold stripMvA
    exact Ev.seq' hinit htail (le_refl _)
  refine ⟨s₄, (1 + (n₁ + n₂)) + (10 * vsz v + 1 + 1), hmain, by omega, ?_, ?_, ?_, ?_⟩
  · rw [hs₄]
    exact (by simp only [Function.update_of_ne had, ha₃])
  · rw [hs₄]
    exact (by simp only [Function.update_of_ne hcd, hc₃])
  · rw [hs₄]
    exact (by simp only [Function.update_self, hd₃', List.tail_cons])
  · intro k hka hkc hkd
    have hfr : s₄.stk k = (⟨g, X⟩ : State).stk k :=
      Ev.frame hmain (cmdTouches_stripMvA a c d) (by simp [hka, hkc, hkd])
    simpa using hfr

/-! ## 4. One round of the main loop -/

/-- One round of the walk: from a state whose value stack is `ofList (r :: rs') :: rest` and whose
buffer is `stripBuf acc` above `stripMark`, one round reaches a state whose value stack is
`ofList rs' :: rest` and whose buffer is `stripBuf (acc ++ [r])` above `stripMark`; register 2 says
whether `rs'` is empty. -/
theorem stripRoundEv {main : Cmd} {up dp : Cmd} {Ku Kd : ℕ}
    (hupE : ∀ (main : Cmd) (s : State) (a b : Val) (l : List Glyph),
      s.stk 0 = (Val.cons a b).enc ++ l →
      ∃ (s' : State) (n : ℕ), Eval main up s s' n ∧ n ≤ Ku ∧ s'.stk 0 = a.enc ++ (b.enc ++ l) ∧
        (∀ k : Stk, k ≠ 0 → s'.stk k = s.stk k))
    (hdpE : ∀ (main : Cmd) (s : State) (v : Val) (l : List Glyph),
      s.stk 0 = v.enc ++ l →
      ∃ (s' : State) (n : ℕ), Eval main dp s s' n ∧ n ≤ Kd * (vsz v + 1) ∧ s'.stk 0 = l ∧
        (∀ k : Stk, k ≠ 0 → s'.stk k = s.stk k)) :
    ∀ (S : State) (rest : List Val) (r : Val) (rs' : List Val) (acc : List Val)
      (R w : List Glyph),
      (∃ (k : ℤ) (u : Val), r = Val.cons (Val.int k) u) →
      S.stk 0 = encs (ofList (r :: rs') :: rest) ++ R →
      S.stk 2 = stripBuf acc ++ stripMark :: w →
      ∃ (S' : State) (n : ℕ), Ev main (stripRound up dp (stripMvA 0 2 1)) S S' n ∧
        n ≤ 2 * Ku + (Kd + 10) * (vsz r + 1) + 15 ∧
        S'.stk 0 = encs (ofList rs' :: rest) ++ R ∧
        S'.stk 2 = stripBuf (acc ++ [r]) ++ stripMark :: w ∧
        S'.reg 2 = (if rs' = [] then stripStop else stripGo) ∧
        (∀ k : Stk, k ≠ 0 → k ≠ 2 → S'.stk k = S.stk k) := by
  intro S rest r rs' acc R w hrec h0 h2
  obtain ⟨k, u, hr⟩ := hrec
  have hvr : vsz r = vsz (Val.int k) + vsz u + 1 := by rw [hr, vsz_cons]
  have hrec' : (recPayload r).enc = u.enc := by rw [hr]; rfl
  -- push the output `cons` glyph on the buffer
  have e1 : Ev main (.set 3 Glyph.cons) S (S.updReg 3 Glyph.cons) 1 :=
    Work.Layout.ev_set main 3 Glyph.cons S
  have he2 : Ev main (.push 2 3) (S.updReg 3 Glyph.cons)
      ((S.updReg 3 Glyph.cons).updStk 2 (Glyph.cons :: S.stk 2)) 1 :=
    Work.Layout.ev_push main 2 3 (S.updReg 3 Glyph.cons)
  set S₂ : State := (S.updReg 3 Glyph.cons).updStk 2 (Glyph.cons :: S.stk 2) with hS₂
  have he2' : Ev main (.push 2 3) (S.updReg 3 Glyph.cons) S₂ 1 := by rw [hS₂]; exact he2
  have hS₂stk0 : S₂.stk 0 = encs (ofList (r :: rs') :: rest) ++ R := by
    rw [hS₂]; simpa using h0
  have hS₂stk2 : S₂.stk 2 = Glyph.cons :: (stripBuf acc ++ stripMark :: w) := by
    simp [hS₂, h2]
  have hS₂fr : ∀ k', k' ≠ 0 → k' ≠ 2 → S₂.stk k' = S.stk k' := by
    intro k' hk0 hk2; simp [hS₂, hk0, hk2]
  -- split off the record
  have hsplit1 : S₂.stk 0 =
      (Val.cons (Val.cons (Val.int k) u) (ofList rs')).enc ++ (encs rest ++ R) := by
    have hh : encs (ofList (Val.cons (Val.int k) u :: rs') :: rest) ++ R =
        (Val.cons (Val.cons (Val.int k) u) (ofList rs')).enc ++ (encs rest ++ R) := by
      rw [encs_cons, ofList_cons, List.append_assoc]
    rw [hS₂stk0, hr, hh]
  obtain ⟨S₃, n₃, hev₃, hn₃, h3, hfr₃⟩ :=
    hupE main S₂ (Val.cons (Val.int k) u) (ofList rs') (encs rest ++ R) hsplit1
  -- split off the key
  obtain ⟨S₄, n₄, hev₄, hn₄, h4, hfr₄⟩ :=
    hupE main S₃ (Val.int k) u ((ofList rs').enc ++ (encs rest ++ R)) h3
  -- drop the key
  obtain ⟨S₅, n₅, hev₅, hn₅, h5, hfr₅⟩ :=
    hdpE main S₄ (Val.int k) (u.enc ++ ((ofList rs').enc ++ (encs rest ++ R))) h4
  -- move the payload to the buffer
  obtain ⟨S₆, n₆, hev₆, hn₆, h6a, h6b, h6d, hfr₆⟩ :=
    stripMvAEv (main := main) (a := 0) (c := 2) (d := 1) (by decide) (by decide) (by decide)
      u ((ofList rs').enc ++ (encs rest ++ R)) (S₅.stk 2) (S₅.stk 1) S₅.reg S₅.stk h5 rfl rfl
  -- the test
  have hS₅stk2 : S₅.stk 2 = S₂.stk 2 := by
    rw [hfr₅ 2 (by decide), hfr₄ 2 (by decide), hfr₃ 2 (by decide)]
  have h6c : S₆.stk 0 = encs (ofList rs' :: rest) ++ R := by
    rw [h6a, encs_cons, List.append_assoc]
  have hbuf : S₆.stk 2 = stripBuf (acc ++ [r]) ++ stripMark :: w := by
    rw [stripBuf_append_singleton, hrec', h6b, hS₅stk2, hS₂stk2]
    simp only [List.cons_append, List.append_assoc]
  have hhead : (S₆.stk 0).headD .eos = if rs' = [] then Glyph.nil else Glyph.cons := by
    rw [h6c]; exact headD_encs_ofList rs' rest R
  obtain ⟨S₇, n₇, hev₇, hn₇, h7a, h7b, h7c⟩ := stripTestEv main S₆ (rs' = []) hhead
  -- assemble
  have hB : Ev main (.seq (stripMvA 0 2 1) stripTest) S₅ S₇ (n₆ + 3) :=
    Ev.seq' hev₆ (hev₇.mono hn₇) (by omega)
  have hC : Ev main (.seq dp (.seq (stripMvA 0 2 1) stripTest)) S₄ S₇ (n₅ + (n₆ + 3)) :=
    Ev.seq' (ev_ofEval hev₅) hB (by omega)
  have hD : Ev main (.seq up (.seq dp (.seq (stripMvA 0 2 1) stripTest))) S₃ S₇
      (n₄ + (n₅ + (n₆ + 3))) :=
    Ev.seq' (ev_ofEval hev₄) hC (by omega)
  have hE : Ev main (.seq up (.seq up (.seq dp (.seq (stripMvA 0 2 1) stripTest)))) S₂ S₇
      (n₃ + (n₄ + (n₅ + (n₆ + 3)))) :=
    Ev.seq' (ev_ofEval hev₃) hD (by omega)
  have hE2 : Ev main (.seq (.push 2 3)
      (.seq up (.seq up (.seq dp (.seq (stripMvA 0 2 1) stripTest))))) (S.updReg 3 Glyph.cons) S₇
      (1 + (n₃ + (n₄ + (n₅ + (n₆ + 3))))) :=
    Ev.seq' he2' hE (by omega)
  have hmain : Ev main (stripRound up dp (stripMvA 0 2 1)) S S₇
      (1 + (1 + (n₃ + (n₄ + (n₅ + (n₆ + 3)))))) := by
    unfold stripRound
    exact Ev.seq' e1 hE2 (le_refl _)
  have hcost : 1 + (1 + (n₃ + (n₄ + (n₅ + (n₆ + 3))))) ≤
      2 * Ku + (Kd + 10) * (vsz r + 1) + 15 := by
    have h5' : n₅ ≤ Kd * (vsz r + 1) :=
      le_trans hn₅ (Nat.mul_le_mul_left Kd (by omega))
    have h6' : n₆ ≤ 10 * (vsz r + 1) := by
      refine le_trans hn₆ ?_
      have : 10 * vsz u + 10 = 10 * (vsz u + 1) := by ring
      rw [this]
      exact Nat.mul_le_mul_left 10 (by omega)
    have hX : (Kd + 10) * (vsz r + 1) = Kd * (vsz r + 1) + 10 * (vsz r + 1) := by ring
    omega
  refine ⟨S₇, _, hmain, hcost, ?_, ?_, h7b, ?_⟩
  · rw [h7a]; exact h6c
  · rw [h7c 2 (by decide)]; exact hbuf
  · intro k' hk0 hk2
    rw [h7c k' hk0]
    by_cases hk1 : k' = 1
    · subst hk1
      rw [h6d, hfr₅ 1 (by decide), hfr₄ 1 (by decide), hfr₃ 1 (by decide),
        hS₂fr 1 (by decide) (by decide)]
    · rw [hfr₆ k' hk0 hk2 hk1, hfr₅ k' hk0, hfr₄ k' hk0, hfr₃ k' hk0,
        hS₂fr k' hk0 hk2]

/-! ## 5. The final drain -/

/-- One step of the drain. -/
theorem stripDrainBodyEv (main : Cmd) (S : State) (g : Glyph) (rest : List Glyph)
    (h : S.stk 2 = g :: rest) :
    ∃ S' n, Ev main stripDrainBody S S' n ∧ n ≤ 4 ∧ S'.stk 2 = rest ∧
      S'.reg 4 = (if g = stripMark then stripStop else stripGo) ∧
      S'.stk 0 = (if g = stripMark then S.stk 0 else g :: S.stk 0) ∧
      (∀ k : Stk, k ≠ 0 → k ≠ 2 → S'.stk k = S.stk k) := by
  set T : State :=
    (⟨Function.update S.reg 1 ((S.stk 2).headD .eos),
      Function.update S.stk 2 ((S.stk 2).tail)⟩ : State) with hT
  have hpop : Ev main (.pop 2 1) S T 1 := by rw [hT]; exact Work.Layout.ev_pop' main 2 1 S.reg S.stk
  have hTstk2 : T.stk 2 = rest := by simp [hT, h]
  have hTreg1 : T.reg 1 = g := by simp [hT, h, List.headD_cons]
  have hTstk0 : T.stk 0 = S.stk 0 := by simp [hT]
  have hTfr : ∀ k : Stk, k ≠ 0 → k ≠ 2 → T.stk k = S.stk k := by
    intro k hk0 hk2; simp [hT, hk2]
  by_cases hg : g = stripMark
  · have hreg : T.reg 1 = stripMark := by rw [hTreg1, hg]
    have hbranch : Ev main (.seq (.set 4 stripStop) .skip) T (T.updReg 4 stripStop) 2 :=
      Ev.seq' (Work.Layout.ev_set main 4 stripStop T)
        (Work.Layout.ev_skip main (T.updReg 4 stripStop)) (by omega)
    have hite : Ev main (.ite 1 stripMark (.seq (.set 4 stripStop) .skip)
        (.seq (.push 0 1) (.set 4 stripGo))) T (T.updReg 4 stripStop) 3 := Ev.iteT hreg hbranch
    refine ⟨T.updReg 4 stripStop, 4, Ev.seq' hpop hite (by omega), by omega, ?_, ?_, ?_, ?_⟩
    · rw [State.updReg_stk]; exact hTstk2
    · rw [if_pos hg]; simp
    · rw [if_pos hg, State.updReg_stk]; exact hTstk0
    · intro k hk0 hk2; rw [State.updReg_stk]; exact hTfr k hk0 hk2
  · have hreg : T.reg 1 ≠ stripMark := by rw [hTreg1]; exact hg
    have hpush : Ev main (.push 0 1) T (T.updStk 0 (g :: T.stk 0)) 1 := by
      have hh := Work.Layout.ev_push main 0 1 T
      rw [hTreg1] at hh
      exact hh
    have hset : Ev main (.set 4 stripGo) (T.updStk 0 (g :: T.stk 0))
        ((T.updStk 0 (g :: T.stk 0)).updReg 4 stripGo) 1 :=
      Work.Layout.ev_set main 4 stripGo _
    have hbranch : Ev main (.seq (.push 0 1) (.set 4 stripGo)) T
        ((T.updStk 0 (g :: T.stk 0)).updReg 4 stripGo) 2 :=
      Ev.seq' hpush hset (by omega)
    have hite : Ev main (.ite 1 stripMark (.seq (.set 4 stripStop) .skip)
        (.seq (.push 0 1) (.set 4 stripGo))) T
        ((T.updStk 0 (g :: T.stk 0)).updReg 4 stripGo) 3 := Ev.iteF hreg hbranch
    refine ⟨(T.updStk 0 (g :: T.stk 0)).updReg 4 stripGo, 4,
      Ev.seq' hpop hite (by omega), by omega, ?_, ?_, ?_, ?_⟩
    · simp only [State.updReg_stk, State.updStk_ne _ _ (by decide : (2 : Stk) ≠ 0)]; exact hTstk2
    · rw [if_neg hg]; simp
    · rw [if_neg hg, State.updReg_stk, State.updStk_same]; rfl
    · intro k hk0 hk2
      rw [State.updReg_stk, State.updStk_ne _ _ hk0, hTfr k hk0 hk2]

/-- The drain loop: it moves the whole buffer down to `stripMark` onto stack 0 (reversing it). -/
theorem stripDrainLoopEv (main : Cmd) (s : State) (G : List Glyph) (l0 w : List Glyph)
    (hG : stripMark ∉ G) (h0 : s.stk 0 = l0) (h2 : s.stk 2 = G ++ stripMark :: w)
    (h4 : s.reg 4 = stripGo) :
    ∃ s' n, Ev main (.loop 4 stripGo stripDrainBody) s s' n ∧ n ≤ 5 * (G.length + 1) + 1 ∧
      s'.stk 0 = G.reverse ++ l0 ∧ s'.stk 2 = w ∧ s'.reg 4 = stripStop ∧
      (∀ k : Stk, k ≠ 0 → k ≠ 2 → s'.stk k = s.stk k) := by
  induction G generalizing s l0 with
  | nil =>
      have h2' : s.stk 2 = stripMark :: w := by simpa using h2
      obtain ⟨T, nT, hTB, hT4, hT2, hTreg, hT0, hTfr⟩ :=
        stripDrainBodyEv main s stripMark w h2'
      have hTreg' : T.reg 4 = stripStop := by rw [if_pos rfl] at hTreg; exact hTreg
      have hT0' : T.stk 0 = s.stk 0 := by rw [if_pos rfl] at hT0; exact hT0
      have hloopF : Ev main (.loop 4 stripGo stripDrainBody) T T 1 :=
        Ev.loopF (by rw [hTreg']; decide)
      refine ⟨T, 4 + 1 + 1, Ev.loopT (by rw [h4]) (hTB.mono hT4) hloopF, by omega, ?_, hT2,
        hTreg', ?_⟩
      · rw [hT0', h0]; simp
      · intro k hk0 hk2; exact hTfr k hk0 hk2
  | cons g gs ih =>
      have h2' : s.stk 2 = g :: (gs ++ stripMark :: w) := by simpa using h2
      have hg : g ≠ stripMark := fun hh => hG (by rw [hh]; exact List.mem_cons_self ..)
      have hG' : stripMark ∉ gs := fun hh => hG (List.mem_cons_of_mem g hh)
      obtain ⟨T, nT, hTB, hT4, hT2, hTreg, hT0, hTfr⟩ :=
        stripDrainBodyEv main s g (gs ++ stripMark :: w) h2'
      have hTreg' : T.reg 4 = stripGo := by rw [if_neg hg] at hTreg; exact hTreg
      have hT0' : T.stk 0 = g :: s.stk 0 := by rw [if_neg hg] at hT0; exact hT0
      obtain ⟨T', n', hloop', hn', hT'0, hT'2, hT'reg, hT'fr⟩ :=
        ih T (g :: l0) hG' (by rw [hT0', h0]) hT2 hTreg'
      refine ⟨T', 4 + n' + 1, Ev.loopT (by rw [h4]) (hTB.mono hT4) hloop', ?_, ?_, hT'2,
        hT'reg, ?_⟩
      · have := hn'; simp only [List.length_cons]; omega
      · rw [hT'0, List.reverse_cons, List.append_assoc, List.singleton_append]
      · intro k hk0 hk2; rw [hT'fr k hk0 hk2, hTfr k hk0 hk2]

/-- The final drain: `stripDrain` moves the buffer content `G` onto stack 0 reversed. -/
theorem stripDrainEv (main : Cmd) (s : State) (G : List Glyph) (l0 w : List Glyph)
    (hG : stripMark ∉ G) (h0 : s.stk 0 = l0) (h2 : s.stk 2 = G ++ stripMark :: w) :
    ∃ s' n, Eval main stripDrain s s' n ∧ n ≤ 5 * (G.length + 1) + 2 ∧
      s'.stk 0 = G.reverse ++ l0 ∧ s'.stk 2 = w ∧ s'.reg 4 = stripStop ∧
      (∀ k : Stk, k ≠ 0 → k ≠ 2 → s'.stk k = s.stk k) := by
  obtain ⟨s', n', hloop, hn', h0', h2', h4', hfr'⟩ :=
    stripDrainLoopEv main (s.updReg 4 stripGo) G l0 w hG (by simpa using h0) (by simpa using h2)
      (by simp)
  have hset : Ev main (.set 4 stripGo) s (s.updReg 4 stripGo) 1 :=
    Work.Layout.ev_set main 4 stripGo s
  have hmain : Ev main stripDrain s s' (1 + n') := by
    unfold stripDrain
    exact Ev.seq' hset hloop (le_refl (1 + n'))
  obtain ⟨n, hev, hn⟩ := hmain
  refine ⟨s', n, hev, by omega, h0', h2', h4', ?_⟩
  intro k hk0 hk2
  rw [hfr' k hk0 hk2]
  simp

/-! ## 6. The main loop -/

/-- Cost of one round (body plus the loop test). -/
def stripRoundCost (Ku Kd : ℕ) (r : Val) : ℕ := 2 * Ku + (Kd + 10) * (vsz r + 1) + 15

/-- The main loop of the walk: it consumes the list, one round per record. -/
theorem stripLoopRuns {main : Cmd} {up dp : Cmd} {Ku Kd : ℕ}
    (hupE : ∀ (main : Cmd) (s : State) (a b : Val) (l : List Glyph),
      s.stk 0 = (Val.cons a b).enc ++ l →
      ∃ (s' : State) (n : ℕ), Eval main up s s' n ∧ n ≤ Ku ∧ s'.stk 0 = a.enc ++ (b.enc ++ l) ∧
        (∀ k : Stk, k ≠ 0 → s'.stk k = s.stk k))
    (hdpE : ∀ (main : Cmd) (s : State) (v : Val) (l : List Glyph),
      s.stk 0 = v.enc ++ l →
      ∃ (s' : State) (n : ℕ), Eval main dp s s' n ∧ n ≤ Kd * (vsz v + 1) ∧ s'.stk 0 = l ∧
        (∀ k : Stk, k ≠ 0 → s'.stk k = s.stk k)) :
    ∀ (rs : List Val) (acc : List Val) (S : State) (rest : List Val) (R w : List Glyph),
      (∀ x ∈ rs, ∃ (k : ℤ) (u : Val), x = Val.cons (Val.int k) u) →
      S.stk 0 = encs (ofList rs :: rest) ++ R →
      S.stk 2 = stripBuf acc ++ stripMark :: w →
      S.reg 2 = (if rs = [] then stripStop else stripGo) →
      ∃ S', loopRuns main 2 stripGo (stripRound up dp (stripMvA 0 2 1)) rs.length S S'
          ((rs.map fun r => stripRoundCost Ku Kd r + 1).sum) ∧
        S'.stk 0 = encs (ofList [] :: rest) ++ R ∧
        S'.stk 2 = stripBuf (acc ++ rs) ++ stripMark :: w ∧
        S'.reg 2 = stripStop ∧
        (∀ k : Stk, k ≠ 0 → k ≠ 2 → S'.stk k = S.stk k) := by
  intro rs
  induction rs with
  | nil =>
      intro acc S rest R w hrec h0 h2 hreg
      refine ⟨S, loopRuns.zero, ?_, ?_, ?_, ?_⟩
      · simpa using h0
      · simpa using h2
      · simpa using hreg
      · intro k hk0 hk2; rfl
  | cons r rs' ih =>
      intro acc S rest R w hrec h0 h2 hreg
      have hrecr : ∃ (k : ℤ) (u : Val), r = Val.cons (Val.int k) u := hrec r (by simp)
      have htail : ∀ x ∈ rs', ∃ (k : ℤ) (u : Val), x = Val.cons (Val.int k) u :=
        fun x hx => hrec x (List.mem_cons_of_mem r hx)
      have hregGo : S.reg 2 = stripGo := by rw [hreg]; simp
      obtain ⟨S₁, n₁, hev₁, hn₁, h0₁, h2₁, hreg₁, hfr₁⟩ :=
        stripRoundEv (main := main) hupE hdpE S rest r rs' acc R w hrecr h0 h2
      obtain ⟨S₂, hrun₂, h0₂, h2₂, hreg₂, hfr₂⟩ :=
        ih (acc ++ [r]) S₁ rest R w htail h0₁ h2₁ hreg₁
      have hfr : ∀ k : Stk, k ≠ 0 → k ≠ 2 → S₂.stk k = S.stk k := by
        intro k hk0 hk2; rw [hfr₂ k hk0 hk2, hfr₁ k hk0 hk2]
      have hone : Ev main (stripRound up dp (stripMvA 0 2 1)) S S₁ (stripRoundCost Ku Kd r) :=
        hev₁.mono hn₁
      have hle : stripRoundCost Ku Kd r
          + ((rs'.map fun r => stripRoundCost Ku Kd r + 1).sum) + 1 ≤
          ((r :: rs').map fun r => stripRoundCost Ku Kd r + 1).sum := by
        simp only [List.map_cons, List.sum_cons]
        omega
      refine ⟨S₂, ?_, h0₂, ?_, hreg₂, hfr⟩
      · refine loopRuns.cast ?_ (loopRuns.succ' (main := main) hregGo hone hrun₂ hle)
        simp
      · rw [h2₂, List.append_assoc, List.singleton_append]

/-- Arithmetic for the total cost of the walk. -/
theorem stripLoopCostBound (Ku Kd : ℕ) (rs : List Val) :
    ((rs.map fun r => stripRoundCost Ku Kd r + 1).sum) + 1 ≤
      (2 * Ku + Kd + 26) * vsz (ofList rs) + 3 := by
  induction rs with
  | nil => simp [stripRoundCost, ofList_nil, vsz, Val.enc]
  | cons r rs ih =>
      rw [List.map_cons, List.sum_cons, stripRoundCost]
      have hv : vsz (ofList (r :: rs)) = vsz r + vsz (ofList rs) + 1 := by
        rw [ofList_cons, vsz_cons]
      rw [hv]
      nlinarith [ih]

/-- `stripProg` walks the list, one round per record, and drains the output buffer. -/
theorem stripProgEv {main : Cmd} {up dp : Cmd} {Ku Kd : ℕ}
    (hupE : ∀ (main : Cmd) (s : State) (a b : Val) (l : List Glyph),
      s.stk 0 = (Val.cons a b).enc ++ l →
      ∃ (s' : State) (n : ℕ), Eval main up s s' n ∧ n ≤ Ku ∧ s'.stk 0 = a.enc ++ (b.enc ++ l) ∧
        (∀ k : Stk, k ≠ 0 → s'.stk k = s.stk k))
    (hdpE : ∀ (main : Cmd) (s : State) (v : Val) (l : List Glyph),
      s.stk 0 = v.enc ++ l →
      ∃ (s' : State) (n : ℕ), Eval main dp s s' n ∧ n ≤ Kd * (vsz v + 1) ∧ s'.stk 0 = l ∧
        (∀ k : Stk, k ≠ 0 → s'.stk k = s.stk k)) :
    ∀ (rs : List Val) (rest : List Val) (s : State) (R : List Glyph),
      (∀ x ∈ rs, ∃ (k : ℤ) (u : Val), x = Val.cons (Val.int k) u) →
      s.stk 0 = encs (ofList rs :: rest) ++ R →
      ∃ (S' : State) (n : ℕ), Ev main (stripProg up dp (stripMvA 0 2 1)) s S' n ∧
        n ≤ (2 * Ku + Kd + 50) * (vsz (ofList rs) + 1) ∧
        S'.stk 0 = encs (ofList (rs.map recPayload) :: rest) ++ R ∧
        S'.stk 2 = s.stk 2 ∧
        (∀ k : Stk, k ≠ 0 → S'.stk k = s.stk k) := by
  intro rs rest s R hrec h0
  -- push the frame marker on the buffer
  have e1 : Ev main (.set 3 stripMark) s (s.updReg 3 stripMark) 1 :=
    Work.Layout.ev_set main 3 stripMark s
  have e2 : Ev main (.push 2 3) (s.updReg 3 stripMark)
      ((s.updReg 3 stripMark).updStk 2 (stripMark :: s.stk 2)) 1 :=
    Work.Layout.ev_push main 2 3 (s.updReg 3 stripMark)
  set S₁ : State := (s.updReg 3 stripMark).updStk 2 (stripMark :: s.stk 2) with hS₁
  have he12 : Ev main (.seq (.set 3 stripMark) (.push 2 3)) s S₁ 2 :=
    Ev.seq' e1 (by rw [hS₁]; exact e2) (by omega)
  have hS₁stk0 : S₁.stk 0 = encs (ofList rs :: rest) ++ R := by rw [hS₁]; simpa using h0
  have hS₁stk2 : S₁.stk 2 = stripMark :: s.stk 2 := by simp [hS₁]
  have hS₁fr : ∀ k, k ≠ 0 → k ≠ 2 → S₁.stk k = s.stk k := by
    intro k hk0 hk2; simp [hS₁, hk0, hk2]
  -- the test
  have hhead : (S₁.stk 0).headD .eos = if rs = [] then Glyph.nil else Glyph.cons := by
    rw [hS₁stk0]; exact headD_encs_ofList rs rest R
  obtain ⟨S₂, n₂, hev₂, hn₂, h2a, h2b, h2c⟩ := stripTestEv main S₁ (rs = []) hhead
  -- the main loop
  have h2stk2 : S₂.stk 2 = stripBuf ([] : List Val) ++ stripMark :: s.stk 2 := by
    rw [h2c 2 (by decide), hS₁stk2]; rfl
  obtain ⟨S₃, hrun₃, h3a, h3b, h3c, h3d⟩ :=
    stripLoopRuns (main := main) hupE hdpE rs [] S₂ rest R (s.stk 2) hrec
      (by rw [h2a, hS₁stk0]) h2stk2 h2b
  have hloopEv : Ev main (.loop 2 stripGo (stripRound up dp (stripMvA 0 2 1))) S₂ S₃
      (((rs.map fun r => stripRoundCost Ku Kd r + 1).sum) + 1) :=
    Work.Layout.loopRuns.eval' hrun₃ (by rw [h3c]; exact (by decide : stripStop ≠ stripGo))
  -- drop the standing `nil`
  have hpopEv : Ev main (.pop 0 3) S₃
      ((S₃.updReg 3 ((S₃.stk 0).headD .eos)).updStk 0 ((S₃.stk 0).tail)) 1 :=
    Work.Layout.ev_pop' main 0 3 S₃.reg S₃.stk
  set S₄ : State := (S₃.updReg 3 ((S₃.stk 0).headD .eos)).updStk 0 ((S₃.stk 0).tail) with hS₄
  have hS₄stk0 : S₄.stk 0 = encs rest ++ R := by
    have h1 : encs (ofList ([] : List Val) :: rest) ++ R = Glyph.nil :: (encs rest ++ R) := by
      rw [encs_cons, ofList_nil, Val.enc]; rfl
    have h3a' : S₃.stk 0 = Glyph.nil :: (encs rest ++ R) := by rw [h3a, h1]
    rw [hS₄, h3a']; simp
  -- push the terminating `nil` on the buffer
  have e3 : Ev main (.set 3 Glyph.nil) S₄ (S₄.updReg 3 Glyph.nil) 1 :=
    Work.Layout.ev_set main 3 Glyph.nil S₄
  have e4 : Ev main (.push 2 3) (S₄.updReg 3 Glyph.nil)
      ((S₄.updReg 3 Glyph.nil).updStk 2 (Glyph.nil :: S₄.stk 2)) 1 :=
    Work.Layout.ev_push main 2 3 (S₄.updReg 3 Glyph.nil)
  set S₅ : State := (S₄.updReg 3 Glyph.nil).updStk 2 (Glyph.nil :: S₄.stk 2) with hS₅
  have hS₅stk2 : S₅.stk 2 = Glyph.nil :: (stripBuf rs ++ stripMark :: s.stk 2) := by
    have h : S₄.stk 2 = S₃.stk 2 := by rw [hS₄]; simp
    simp [hS₅, h, h3b]
  -- the drain
  obtain ⟨S₆, n₆, hev₆, hn₆, h6a, h6b, -, h6c⟩ :=
    stripDrainEv main S₅ (Glyph.nil :: stripBuf rs) (encs rest ++ R) (s.stk 2)
      (by
        intro h
        rw [List.mem_cons] at h
        rcases h with h | h
        · exact stripMark_ne_nil h
        · exact stripMark_notMem_stripBuf rs h)
      hS₄stk0 hS₅stk2
  have hDrain : Ev main stripDrain S₅ S₆ n₆ := ev_ofEval hev₆
  have hPushDrain : Ev main (.seq (.push 2 3) stripDrain) (S₄.updReg 3 Glyph.nil) S₆ (1 + n₆) :=
    Ev.seq' e4 hDrain (le_refl _)
  have hNilPush : Ev main (.seq (.set 3 Glyph.nil) (.seq (.push 2 3) stripDrain)) S₄ S₆
      (1 + (1 + n₆)) := Ev.seq' e3 hPushDrain (le_refl _)
  have hPopNil : Ev main
      (.seq (.pop 0 3) (.seq (.set 3 Glyph.nil) (.seq (.push 2 3) stripDrain))) S₃ S₆
      (1 + (1 + (1 + n₆))) := Ev.seq' hpopEv hNilPush (le_refl _)
  have hLoopTail : Ev main
      (.seq (.loop 2 stripGo (stripRound up dp (stripMvA 0 2 1)))
        (.seq (.pop 0 3) (.seq (.set 3 Glyph.nil) (.seq (.push 2 3) stripDrain)))) S₂ S₆
      ((((rs.map fun r => stripRoundCost Ku Kd r + 1).sum) + 1) + (1 + (1 + (1 + n₆)))) :=
    Ev.seq' hloopEv hPopNil (le_refl _)
  have hTestTail : Ev main
      (.seq stripTest (.seq (.loop 2 stripGo (stripRound up dp (stripMvA 0 2 1)))
        (.seq (.pop 0 3) (.seq (.set 3 Glyph.nil) (.seq (.push 2 3) stripDrain))))) S₁ S₆
      (n₂ + ((((rs.map fun r => stripRoundCost Ku Kd r + 1).sum) + 1) + (1 + (1 + (1 + n₆))))) :=
    Ev.seq' hev₂ hLoopTail (le_refl _)
  have hPushTest : Ev main
      (.seq (.push 2 3) (.seq stripTest (.seq (.loop 2 stripGo (stripRound up dp (stripMvA 0 2 1)))
        (.seq (.pop 0 3) (.seq (.set 3 Glyph.nil) (.seq (.push 2 3) stripDrain))))))
      (s.updReg 3 stripMark) S₆
      (1 + (n₂ + ((((rs.map fun r => stripRoundCost Ku Kd r + 1).sum) + 1)
        + (1 + (1 + (1 + n₆)))))) :=
    Ev.seq' (by rw [hS₁]; exact e2) hTestTail (le_refl _)
  have hmain : Ev main (stripProg up dp (stripMvA 0 2 1)) s S₆
      (1 + (1 + (n₂ + ((((rs.map fun r => stripRoundCost Ku Kd r + 1).sum) + 1)
        + (1 + (1 + (1 + n₆))))))) := by
    unfold stripProg
    exact Ev.seq' e1 hPushTest (le_refl _)
  have hcost : 1 + (1 + (n₂ + ((((rs.map fun r => stripRoundCost Ku Kd r + 1).sum) + 1)
      + (1 + (1 + (1 + n₆)))))) ≤ (2 * Ku + Kd + 50) * (vsz (ofList rs) + 1) := by
    have hloop := stripLoopCostBound Ku Kd rs
    have hlen : (stripBuf rs).length + 2 ≤ vsz (ofList rs) + 1 := by
      have h1 := length_stripPush_succ_le rs hrec
      have h2 : (stripBuf rs).length = (stripPush rs).length := by simp [stripBuf]
      omega
    have hn₆' : n₆ ≤ 5 * ((stripBuf rs).length + 2) + 2 := by
      have h2 : (Glyph.nil :: stripBuf rs).length + 1 = (stripBuf rs).length + 2 := by simp
      have := hn₆
      rw [h2] at this
      exact this
    nlinarith [hloop, hn₆', hlen, hn₂]
  have hcost : 1 + (1 + (n₂ + ((((rs.map fun r => stripRoundCost Ku Kd r + 1).sum) + 1)
      + (1 + (1 + (1 + n₆)))))) ≤ (2 * Ku + Kd + 50) * (vsz (ofList rs) + 1) := by
    have hloop := stripLoopCostBound Ku Kd rs
    have hlen : (stripBuf rs).length + 2 ≤ vsz (ofList rs) + 1 := by
      have h1 := length_stripPush_succ_le rs hrec
      have h2 : (stripBuf rs).length = (stripPush rs).length := by simp [stripBuf]
      omega
    have hn₆' : n₆ ≤ 5 * ((stripBuf rs).length + 2) + 2 := by
      have h2 : (Glyph.nil :: stripBuf rs).length + 1 = (stripBuf rs).length + 2 := by simp
      have := hn₆
      rw [h2] at this
      exact this
    nlinarith [hloop, hn₆', hlen]
  refine ⟨S₆, _, hmain, hcost, ?_, ?_, ?_⟩
  · rw [h6a, List.reverse_cons, stripBuf_reverse, target_eq]
    simp only [List.append_assoc]
  · exact h6b
  · intro k hk0
    by_cases hk2 : k = 2
    · subst hk2; exact h6b
    · rw [h6c k hk0 hk2]
      have e : S₅.stk k = S₄.stk k := by simp [hS₅, hk0, hk2]
      rw [e]
      have e' : S₄.stk k = S₃.stk k := by simp [hS₄, hk0]
      rw [e']
      rw [h3d k hk0 hk2, h2c k hk0, hS₁fr k hk0 hk2]

/-! ## 7. The requested theorem -/

theorem crtStripWord (hK : HvdH.KernelLib) (hI : HvdH.IntLib) (hL : HvdH.LayoutLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (rs : List HvdH.Val),
    (∀ x ∈ rs, ∃ (k : ℤ) (v : HvdH.Val), x = HvdH.Val.cons (HvdH.Val.int k) v) →
    HvdH.WordR main prog
      (fun vs => ∃ rest, vs = HvdH.ofList rs :: rest)
      (fun vs out => ∃ rest, vs = HvdH.ofList rs :: rest ∧
        out = HvdH.ofList (rs.map Work.MainP.recPayload) :: rest)
      (fun vs => K * (HvdH.vsz (HvdH.ofList rs) + 1)) := by
  obtain ⟨dp, Kd, hdp⟩ := hK.drop
  obtain ⟨up, Ku, hup⟩ := hK.unconsV
  refine ⟨stripProg up dp (stripMvA 0 2 1), 2 * Ku + Kd + 50, ?_⟩
  intro main rs hrec vs hpre s R hR
  obtain ⟨rest, rfl⟩ := hpre
  have hu := stripUnconsEv (up := up) (Ku := Ku) hup
  have hd := stripDropEv (dp := dp) (Kd := Kd) hdp
  have h0 : s.stk 0 = encs (ofList rs :: rest) ++ R := by rw [hR, encs_cons]
  obtain ⟨S', n', hev', hn', hstk0, hstk2, hfr⟩ :=
    stripProgEv (main := main) hu hd rs rest s R hrec h0
  obtain ⟨n, hev, hn⟩ := hev'
  refine ⟨ofList (rs.map recPayload) :: rest, S', n, ⟨rest, rfl, rfl⟩, hev, le_trans hn hn',
    hstk0, ?_⟩
  intro k hk
  exact hfr k hk

end Work.MainP
