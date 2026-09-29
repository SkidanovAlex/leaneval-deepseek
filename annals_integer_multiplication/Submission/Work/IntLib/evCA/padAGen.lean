import Mathlib
import Submission.Work.IntLib.evCarryDefs

/-!
# `IntLib` / `evCarryAdd`: the padding loop `padA`, general tail

`EvC.padA` (= `seq [padInit, loop rLa gGo padBody]`) turns a unary counter `aCW = Unary m rest`
into `Unary 0 rest`, pushing exactly `m` `false` bits onto `aO` while doing so.  Unlike
`evCA.padAEv`, no frame marker is assumed below the data of `aO`: the part of `aO` below the bits
being padded is an *arbitrary* glyph list `R`, which is left untouched:

`aO = P.reverse.map bit ++ R  ⟹  aO = (P ++ replicate m false).reverse.map bit ++ R`.

No other stack is touched, and the cost is `3 + (7m + 1) = 7m + 4`.

The proof decomposes the loop into

* `padBodyEvGen`: one iteration consumes one counter token and pushes one `false` bit, cost `≤ 6`;
* `padLoopEvGen`: induction on the number of remaining tokens, cost `≤ r*7 + 1`;
* `padInitEvGen`: the initial flag computation, cost `≤ 3`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib
namespace evCA

open HvdH

/-! ## Unfoldings of the three programs -/

private theorem padA_unfold :
    EvC.padA = .seq EvC.padInit (.loop EvC.rLa Shift.gGo EvC.padBody) := rfl

private theorem padInit_unfold :
    EvC.padInit = .seq (.peek aCW EvC.rTa)
      (.ite EvC.rTa gTok (.set EvC.rLa Shift.gGo) (.set EvC.rLa Shift.gStop)) := rfl

private theorem padBody_unfold :
    EvC.padBody = .seq (.set EvC.rZa (Glyph.bit false))
      (.seq (.push aO EvC.rZa)
        (.seq (.pop aCW EvC.rTa)
          (.seq (.peek aCW EvC.rTa)
            (.ite EvC.rTa gTok (.set EvC.rLa Shift.gGo) (.set EvC.rLa Shift.gStop))))) := rfl

/-! ## Elementary list facts -/

/-- The head of a unary counter, as a case distinction on emptiness. -/
private theorem unary_headD (r : ℕ) (rest : List Glyph) :
    (Unary r rest).headD Glyph.eos = (if r = 0 then gEnd else gTok) := by
  rcases r with _ | k
  · simp [Unary]
  · rw [Unary_succ, if_neg (Nat.succ_ne_zero k)]
    rfl

/-- Pushing one more `false` onto the reversed bit list prepends one glyph. -/
private theorem rev_rep_map (Pb : List Bool) (i : ℕ) :
    (Pb ++ List.replicate (i + 1) false).reverse.map Glyph.bit =
      Glyph.bit false :: (Pb ++ List.replicate i false).reverse.map Glyph.bit := by
  have h : Pb ++ List.replicate (i + 1) false = (Pb ++ List.replicate i false) ++ [false] := by
    rw [List.replicate_succ']; simp [List.append_assoc]
  rw [h, List.reverse_append, List.map_append]
  simp

/-! ## The initialisation `padInit` -/

/-- `padInit` sets the loop flag according to whether the counter is empty; it touches no stack. -/
private theorem padInitEvGen (main : Cmd) (g : Reg → Glyph) (X : Stk → List Glyph) (m : ℕ)
    (Gs : List Glyph) (hCW : X aCW = Unary m Gs) :
    ∃ (s1 : State) (n1 : ℕ), Work.Layout.Ev main EvC.padInit ⟨g, X⟩ s1 n1 ∧ n1 ≤ 3 ∧
      s1.stk = X ∧
      s1.reg EvC.rLa = (if m = 0 then Shift.gStop else Shift.gGo) := by
  let t1 : State := ⟨Function.update g EvC.rTa ((Unary m Gs).headD Glyph.eos), X⟩
  let t2 : State := ⟨Function.update t1.reg EvC.rLa (if m = 0 then Shift.gStop else Shift.gGo), X⟩
  have h1 : Eval main (.peek aCW EvC.rTa) ⟨g, X⟩ t1 1 := by
    simpa only [t1, hCW] using Eval.peek aCW EvC.rTa (⟨g, X⟩ : State)
  have h2 : Eval main (.ite EvC.rTa gTok (.set EvC.rLa Shift.gGo) (.set EvC.rLa Shift.gStop))
      t1 t2 2 := by
    have ht1reg : t1.reg EvC.rTa = (if m = 0 then gEnd else gTok) := by
      simp only [t1, Function.update_self, unary_headD]
    by_cases hm : m = 0
    · have hne : t1.reg EvC.rTa ≠ gTok := by
        rw [ht1reg, if_pos hm]
        exact gEnd_ne_gTok
      have hset : Eval main (.set EvC.rLa Shift.gStop) t1 t2 1 := by
        have h := Eval.set (main := main) EvC.rLa Shift.gStop t1
        have ht2 : t2 = ⟨Function.update t1.reg EvC.rLa
            (if m = 0 then Shift.gStop else Shift.gGo), t1.stk⟩ := rfl
        rw [ht2, if_pos hm]; exact h
      exact Eval.iteF hne hset
    · have heq : t1.reg EvC.rTa = gTok := by
        rw [ht1reg, if_neg hm]
      have hset : Eval main (.set EvC.rLa Shift.gGo) t1 t2 1 := by
        have h := Eval.set (main := main) EvC.rLa Shift.gGo t1
        have ht2 : t2 = ⟨Function.update t1.reg EvC.rLa
            (if m = 0 then Shift.gStop else Shift.gGo), t1.stk⟩ := rfl
        rw [ht2, if_neg hm]; exact h
      exact Eval.iteT heq hset
  have hseq : Eval main EvC.padInit ⟨g, X⟩ t2 3 := by
    rw [padInit_unfold]
    exact Eval.seq h1 h2
  refine ⟨t2, 3, ⟨3, hseq, le_rfl⟩, le_rfl, ?_, ?_⟩
  · rfl
  · simp only [t2, Function.update_self]

/-! ## The loop body -/

/-- One iteration of the padding loop: push `bit false` onto `aO`, consume one counter token,
and reset the loop flag.  Cost `≤ 6`.  The glyph list `R` below the padded bits is arbitrary and
untouched. -/
private theorem padBodyEvGen (main : Cmd) (Pb : List Bool) (R Cs : List Glyph)
    (X : Stk → List Glyph) (r i : ℕ) (s : State)
    (hO : s.stk aO = (Pb ++ List.replicate i false).reverse.map Glyph.bit ++ R)
    (hCW : s.stk aCW = Unary (r + 1) (Shift.gmk aCW :: Cs))
    (hfr : ∀ j : Stk, j ≠ aO → j ≠ aCW → s.stk j = X j) :
    ∃ s' n, Work.Layout.Ev main EvC.padBody s s' n ∧ n ≤ 6 ∧
      s'.stk aO = (Pb ++ List.replicate (i + 1) false).reverse.map Glyph.bit ++ R ∧
      s'.stk aCW = Unary r (Shift.gmk aCW :: Cs) ∧
      (∀ j : Stk, j ≠ aO → j ≠ aCW → s'.stk j = X j) ∧
      s'.reg EvC.rLa = (if r = 0 then Shift.gStop else Shift.gGo) := by
  have hneAO : aO ≠ aCW := by decide
  have hneOA : aCW ≠ aO := by decide
  let s1 : State := ⟨Function.update s.reg EvC.rZa (Glyph.bit false), s.stk⟩
  let s2 : State := ⟨s1.reg, Function.update s1.stk aO (Glyph.bit false :: s1.stk aO)⟩
  let s3 : State := ⟨Function.update s2.reg EvC.rTa gTok,
    Function.update s2.stk aCW (Unary r (Shift.gmk aCW :: Cs))⟩
  let s4 : State := ⟨Function.update s3.reg EvC.rTa
    ((Unary r (Shift.gmk aCW :: Cs)).headD Glyph.eos), s3.stk⟩
  let s5 : State := ⟨Function.update s4.reg EvC.rLa
    (if r = 0 then Shift.gStop else Shift.gGo), s3.stk⟩
  have h1 : Eval main (.set EvC.rZa (Glyph.bit false)) s s1 1 := Eval.set_eq
  have hreg1 : s1.reg EvC.rZa = Glyph.bit false := by simp only [s1, Function.update_self]
  have h2 : Eval main (.push aO EvC.rZa) s1 s2 1 := Eval.push_eq hreg1
  have hstk2 : s2.stk aCW = gTok :: Unary r (Shift.gmk aCW :: Cs) := by
    simp only [s2, s1, Shift.upStk_ne' hneAO]
    rw [hCW, Unary_succ]
  have h3 : Eval main (.pop aCW EvC.rTa) s2 s3 1 := Eval.pop_cons hstk2
  have h4 : Eval main (.peek aCW EvC.rTa) s3 s4 1 := by
    have hstk3 : s3.stk aCW = Unary r (Shift.gmk aCW :: Cs) := by
      simp only [s3, Shift.upStk_same]
    have h : Eval main (.peek aCW EvC.rTa) s3
        ⟨Function.update s3.reg EvC.rTa ((s3.stk aCW).headD Glyph.eos), s3.stk⟩ 1 :=
      Eval.peek aCW EvC.rTa s3
    simp only [s4]
    rw [hstk3] at h
    exact h
  have hs4reg : s4.reg EvC.rTa = (if r = 0 then gEnd else gTok) := by
    simp only [s4, Function.update_self, unary_headD]
  have h5 : Eval main (.ite EvC.rTa gTok (.set EvC.rLa Shift.gGo) (.set EvC.rLa Shift.gStop))
      s4 s5 2 := by
    by_cases hr : r = 0
    · have hne : s4.reg EvC.rTa ≠ gTok := by
        rw [hs4reg, if_pos hr]
        exact gEnd_ne_gTok
      have hset : Eval main (.set EvC.rLa Shift.gStop) s4 s5 1 := by
        have h := Eval.set (main := main) EvC.rLa Shift.gStop s4
        have hs5 : s5 = ⟨Function.update s4.reg EvC.rLa
            (if r = 0 then Shift.gStop else Shift.gGo), s4.stk⟩ := rfl
        rw [hs5, if_pos hr]; exact h
      exact Eval.iteF hne hset
    · have heq : s4.reg EvC.rTa = gTok := by
        rw [hs4reg, if_neg hr]
      have hset : Eval main (.set EvC.rLa Shift.gGo) s4 s5 1 := by
        have h := Eval.set (main := main) EvC.rLa Shift.gGo s4
        have hs5 : s5 = ⟨Function.update s4.reg EvC.rLa
            (if r = 0 then Shift.gStop else Shift.gGo), s4.stk⟩ := rfl
        rw [hs5, if_neg hr]; exact h
      exact Eval.iteT heq hset
  have hbody : Eval main EvC.padBody s s5 6 := by
    rw [padBody_unfold]
    exact Eval.seq h1 (Eval.seq h2 (Eval.seq h3 (Eval.seq h4 h5)))
  refine ⟨s5, 6, ⟨6, hbody, le_rfl⟩, le_rfl, ?_, ?_, ?_, ?_⟩
  · have hA : s5.stk aO = Glyph.bit false :: s.stk aO := by
      simp only [s5, s4, s3, s2, s1, Shift.upStk_same, Shift.upStk_ne' hneOA]
    rw [hA, hO, rev_rep_map]
    simp only [List.cons_append, List.append_assoc]
  · simp only [s5, s4, s3, Shift.upStk_same]
  · intro j hj1 hj2
    have hsj : s5.stk j = s.stk j := by
      simp only [s5, s4, s3, s2, s1, Shift.upStk_ne' (Ne.symm hj2), Shift.upStk_ne' (Ne.symm hj1)]
    rw [hsj]; exact hfr j hj1 hj2
  · simp only [s5, Function.update_self]

/-! ## The loop -/

/-- The padding loop: from a counter with `r` tokens it runs `r` iterations, leaving the counter
empty, `r` further `false` bits on `aO`, and the loop flag at `gStop`.  Cost `≤ r*7 + 1`. -/
private theorem padLoopEvGen (main : Cmd) (Pb : List Bool) (R Cs : List Glyph)
    (X : Stk → List Glyph) :
    ∀ (r i : ℕ) (s : State),
      s.stk aO = (Pb ++ List.replicate i false).reverse.map Glyph.bit ++ R →
      s.stk aCW = Unary r (Shift.gmk aCW :: Cs) →
      (∀ j : Stk, j ≠ aO → j ≠ aCW → s.stk j = X j) →
      s.reg EvC.rLa = (if r = 0 then Shift.gStop else Shift.gGo) →
      ∃ s' n, Work.Layout.Ev main (.loop EvC.rLa Shift.gGo EvC.padBody) s s' n ∧ n ≤ r * 7 + 1 ∧
        s'.stk aO = (Pb ++ List.replicate (i + r) false).reverse.map Glyph.bit ++ R ∧
        s'.stk aCW = Unary 0 (Shift.gmk aCW :: Cs) ∧
        (∀ j : Stk, j ≠ aO → j ≠ aCW → s'.stk j = X j) ∧
        s'.reg EvC.rLa = Shift.gStop := by
  intro r
  induction r with
  | zero =>
    intro i s hO hCW hfr hrLa
    have hne : s.reg EvC.rLa ≠ Shift.gGo := by rw [hrLa]; decide
    refine ⟨s, 1, Work.Layout.Ev.loopF hne, ?_, ?_, hCW, hfr, ?_⟩
    · simp
    · simpa using hO
    · rw [hrLa]; decide
  | succ r ih =>
    intro i s hO hCW hfr hrLa
    obtain ⟨s1, n1, hev1, hn1, hO1, hCW1, hfr1, hrLa1⟩ :=
      padBodyEvGen main Pb R Cs X r i s hO hCW hfr
    have hgo : s.reg EvC.rLa = Shift.gGo := by rw [hrLa, if_neg (Nat.succ_ne_zero r)]
    obtain ⟨s2, n2, hev2, hn2, hO2, hCW2, hfr2, hrLa2⟩ := ih (i + 1) s1 hO1 hCW1 hfr1 hrLa1
    refine ⟨s2, n1 + n2 + 1, Work.Layout.Ev.loopT hgo hev1 hev2, ?_, ?_, hCW2, hfr2, hrLa2⟩
    · have := hn1; have := hn2; omega
    · rw [show i + (r + 1) = (i + 1) + r by omega]; exact hO2

/-! ## The padding word -/

private theorem padA_combined (main : Cmd) (g : Reg → Glyph) (X : Stk → List Glyph)
    (N r : ℕ) (s1 s2 : State) (hev1 : Work.Layout.Ev main EvC.padInit ⟨g, X⟩ s1 N)
    (hev2 : Work.Layout.Ev main (.loop EvC.rLa Shift.gGo EvC.padBody) s1 s2 r) :
    Work.Layout.Ev main EvC.padA ⟨g, X⟩ s2 (N + r) := by
  have h : Work.Layout.Ev main (.seq EvC.padInit (.loop EvC.rLa Shift.gGo EvC.padBody))
      ⟨g, X⟩ s2 (N + r) := Work.Layout.Ev.seq' hev1 hev2 (le_refl (N + r))
  simpa [padA_unfold] using h

/-- **The padding loop with an arbitrary tail.**  `EvC.padA` pushes `m` `false` bits onto `aO` and
empties the counter `Unary m (gmk aCW :: Cs)`, leaving everything else (including the glyph list
`R` below the bits on `aO`) untouched.  Cost `≤ 7m + 4`. -/
theorem padAGen (main : HvdH.Cmd) (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph)
    (m : ℕ) (P : List Bool) (R Cs : List HvdH.Glyph)
    (hO : X Work.IntLib.aO = P.reverse.map HvdH.Glyph.bit ++ R)
    (hCW : X Work.IntLib.aCW = Work.IntLib.Unary m (Work.IntLib.Shift.gmk Work.IntLib.aCW :: Cs)) :
    ∃ (s' : HvdH.State) (n : ℕ),
      Work.Layout.Ev main Work.IntLib.EvC.padA ⟨g, X⟩ s' n ∧ n ≤ 7 * m + 4 ∧
      s'.stk Work.IntLib.aO = (P ++ List.replicate m false).reverse.map HvdH.Glyph.bit ++ R ∧
      s'.stk Work.IntLib.aCW = Work.IntLib.Unary 0 (Work.IntLib.Shift.gmk Work.IntLib.aCW :: Cs) ∧
      (∀ j : HvdH.Stk, j ≠ Work.IntLib.aO → j ≠ Work.IntLib.aCW → s'.stk j = X j) := by
  rcases m with _ | k
  · obtain ⟨s1, n1, hev1, hn1, hstk1, hrLa1⟩ :=
      padInitEvGen main g X 0 (Shift.gmk aCW :: Cs) hCW
    have hne : s1.reg EvC.rLa ≠ Shift.gGo := by rw [hrLa1]; decide
    refine ⟨s1, n1 + 1, ?_, ?_, ?_, ?_, ?_⟩
    · exact padA_combined main g X n1 1 s1 s1 hev1 (Work.Layout.Ev.loopF (body := EvC.padBody) hne)
    · have := hn1; omega
    · rw [hstk1]; simpa using hO
    · rw [hstk1]; exact hCW
    · intro j _ _
      rw [hstk1]
  · obtain ⟨s1, n1, hev1, hn1, hstk1, hrLa1⟩ :=
      padInitEvGen main g X (k + 1) (Shift.gmk aCW :: Cs) hCW
    have hgo : s1.reg EvC.rLa = Shift.gGo := by rw [hrLa1, if_neg (Nat.succ_ne_zero k)]
    obtain ⟨s2, n2, hev2, hn2, hO2, hCW2, hfr2, _⟩ :=
      padLoopEvGen main P R Cs X (k + 1) 0 s1 (by rw [hstk1]; simpa using hO)
        (by rw [hstk1]; exact hCW) (by intro j _ _; rw [hstk1]) hgo
    refine ⟨s2, n1 + n2, ?_, ?_, ?_, hCW2, hfr2⟩
    · exact padA_combined main g X n1 n2 s1 s2 hev1 hev2
    · have := hn1; have := hn2; omega
    · simpa using hO2

end evCA
end Work.IntLib
