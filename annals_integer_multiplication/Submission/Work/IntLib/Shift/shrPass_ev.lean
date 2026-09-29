import Mathlib
import Submission.Work.IntLib.Shift.Defs
import Submission.Work.IntLib.Shift.Loop

/-!
# `IntLib` / shift words: the `shr` block pass

`Eval` specification of the `shr` block pass (`shrPassBody`): starting from a block region of `p`
units on `sP`, a region of bits of `|a|` on `sM`, a region of `T0` units on `sT2` and the loop flag
`rI = gGo`, the pass consumes `min p (length bs)` units of the block together with as many bits of
`|a|` (pushing two fresh units per bit onto `sT2`); if the bits of `|a|` run out first it consumes
one further block unit and raises the `rE` flag.  `rD` records whether a `true` bit was dropped.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Work.IntLib.Shift

open HvdH

/-! ## Register distinctness facts used by the pass -/

@[simp] theorem shrPass_ne_rI_rD : rI ≠ rD := by decide
@[simp] theorem shrPass_ne_rD_rE : rD ≠ rE := by decide
@[simp] theorem shrPass_ne_rE_rD : rE ≠ rD := by decide
@[simp] theorem shrPass_ne_rE_rY : rE ≠ rY := by decide
@[simp] theorem shrPass_ne_rD_rY : rD ≠ rY := by decide
@[simp] theorem shrPass_ne_rY_rD : rY ≠ rD := by decide
@[simp] theorem shrPass_ne_rI_rE : rI ≠ rE := by decide
@[simp] theorem shrPass_ne_rW_rE : rW ≠ rE := by decide
@[simp] theorem shrPass_ne_rW_rD : rW ≠ rD := by decide

/-! ## Helpers on `gUnit` regions and the arithmetic of `min` -/

/-- Replicating `a` commutes with concatenating a region all of whose glyphs are `a`. -/
theorem shrPass_AllEq_replicate_append {a : Glyph} {l : List Glyph} (h : AllEq a l) (n : ℕ) :
    List.replicate n a ++ l = l ++ List.replicate n a := by
  rw [h.eq_replicate, ← List.replicate_add, ← List.replicate_add]
  congr 1
  omega

/-- Adding the two fresh units of one block-pass step to a region of units. -/
theorem shrPass_allUnit_append_repl {T0 : List Glyph} (hU : AllUnit T0) (k : ℕ) :
    ([gUnit, gUnit] ++ T0) ++ List.replicate (2 * k) gUnit
      = T0 ++ List.replicate (2 * (k + 1)) gUnit := by
  have h2 : 2 + 2 * k = 2 * (k + 1) := by omega
  have h1 : ([gUnit, gUnit] : List Glyph) = List.replicate 2 gUnit := rfl
  rw [h1, shrPass_AllEq_replicate_append hU 2, List.append_assoc, ← List.replicate_add, h2]

/-- The number of remaining block units after one pass step. -/
theorem shrPass_sub_min_succ (p n : ℕ) :
    (p + 1) - (min (p + 1) (n + 1) + (if p + 1 ≤ n + 1 then 0 else 1))
      = p - (min p n + (if p ≤ n then 0 else 1)) := by
  have hmin : min (p+1) (n+1) = min p n + 1 := by omega
  rw [hmin]
  by_cases h : p ≤ n
  · rw [if_pos (Nat.succ_le_succ h), if_pos h, Nat.min_eq_left h]
    omega
  · rw [if_neg (by omega), if_neg h, Nat.min_eq_right (le_of_lt (not_le.mp h))]
    omega

theorem shrPass_min_succ_succ (p n : ℕ) : min (p+1) (n+1) = min p n + 1 := by omega

/-! ## One iteration of the `shr` block pass -/

/-- One "working" iteration: both the block region and the bits of `|a|` are nonempty.  One block
unit and one bit are consumed, two fresh units are pushed onto `sT2`, and `rD` is raised to `gAny`
if the dropped bit was `true`. -/
theorem shrPass_go_ev (main : Cmd) (s : State) (b : Bool) (LP LM : List Glyph)
    (hP : s.stk sP = gUnit :: LP) (hM : s.stk sM = Glyph.bit b :: LM) :
    ∃ (s' : State) (n : ℕ), Eval main shrPassBody s s' n ∧ n ≤ 10 ∧
      s'.reg rI = s.reg rI ∧ s'.reg rE = s.reg rE ∧
      (s'.reg rD = gAny ↔ (s.reg rD = gAny ∨ true = b)) ∧
      s'.stk sP = LP ∧ s'.stk sM = LM ∧
      s'.stk sT2 = gUnit :: gUnit :: s.stk sT2 ∧
      (∀ j : Stk, j ≠ sP → j ≠ sM → j ≠ sT2 → s'.stk j = s.stk j) := by
  cases b
  case false =>
    let t1 : State := ⟨Function.update s.reg rX gUnit, Function.update s.stk sP LP⟩
    let t2 : State := ⟨Function.update t1.reg rX (Glyph.bit false), Function.update t1.stk sM LM⟩
    let t4 : State := ⟨Function.update t2.reg rY gUnit, Function.update t2.stk sT2 (gUnit :: t2.stk sT2)⟩
    let t5 : State := ⟨Function.update t4.reg rY gUnit, Function.update t4.stk sT2 (gUnit :: t4.stk sT2)⟩
    have h1 : Ev main (.pop sP rX) s t1 1 := by
      have h := ev_pop_st main sP rX s
      dsimp only [t1] at h ⊢
      simpa [hP] using h
    have hne1 : t1.reg rX ≠ gmk sP := by dsimp only [t1]; simp [unit_ne_markerP]
    have h2 : Ev main (.pop sM rX) t1 t2 1 := by
      have h := ev_pop_st main sM rX t1
      dsimp only [t1, t2] at h ⊢
      simpa [hM] using h
    have hne2 : t2.reg rX ≠ gmk sM := by dsimp only [t2, t1]; simp [bit_ne_marker]
    have hx : t2.reg rX ≠ Glyph.bit true := by dsimp only [t2, t1]; simp
    have hD : Ev main (.ite rX (Glyph.bit true) (.set rD gAny) .skip) t2 t2 2 := by
      refine Ev.iteF hx ?_
      exact ⟨1, Eval.skip t2, le_rfl⟩
    have hpu1 : Ev main (pushC sT2 gUnit rY) t2 t4 2 := by
      dsimp only [t4]; exact ev_pushC_st main sT2 gUnit rY t2
    have hpu2 : Ev main (pushC sT2 gUnit rY) t4 t5 2 := by
      dsimp only [t5]; exact ev_pushC_st main sT2 gUnit rY t4
    have hDseq : Ev main (seqs [.ite rX (Glyph.bit true) (.set rD gAny) .skip,
        pushC sT2 gUnit rY, pushC sT2 gUnit rY]) t2 t5 6 :=
      Ev.seq' hD (Ev.seq' hpu1 hpu2 (le_rfl)) (by omega)
    have hite2 : Ev main (.ite rX (gmk sM) (seqs [.push sM rX, .set rE gStop, .set rI gStop])
        (seqs [.ite rX (Glyph.bit true) (.set rD gAny) .skip,
          pushC sT2 gUnit rY, pushC sT2 gUnit rY])) t2 t5 7 :=
      Ev.iteF hne2 hDseq
    have hB : Ev main (seqs [.pop sM rX, .ite rX (gmk sM)
        (seqs [.push sM rX, .set rE gStop, .set rI gStop])
        (seqs [.ite rX (Glyph.bit true) (.set rD gAny) .skip,
          pushC sT2 gUnit rY, pushC sT2 gUnit rY])]) t1 t5 8 :=
      Ev.seq' h2 hite2 (le_rfl)
    have hite1 : Ev main (.ite rX (gmk sP) (seqs [.push sP rX, .set rI gStop])
        (seqs [.pop sM rX, .ite rX (gmk sM) (seqs [.push sM rX, .set rE gStop, .set rI gStop])
        (seqs [.ite rX (Glyph.bit true) (.set rD gAny) .skip,
          pushC sT2 gUnit rY, pushC sT2 gUnit rY])])) t1 t5 9 :=
      Ev.iteF hne1 hB
    have hall : Ev main shrPassBody s t5 10 := by
      dsimp only [shrPassBody]
      exact Ev.seq' h1 hite1 (le_rfl)
    obtain ⟨n, he, hn⟩ := hall
    refine ⟨t5, n, he, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp only [t5, t4, t2, t1]; simp
    · dsimp only [t5, t4, t2, t1]; simp
    · dsimp only [t5, t4, t2, t1]; simp
    · dsimp only [t5, t4, t2, t1]; simp
    · dsimp only [t5, t4, t2, t1]; simp
    · dsimp only [t5, t4, t2, t1]; simp
    · intro j hj1 hj2 hj3; dsimp only [t5, t4, t2, t1]; simp [hj1, hj2, hj3]
  case true =>
    let t1 : State := ⟨Function.update s.reg rX gUnit, Function.update s.stk sP LP⟩
    let t2 : State := ⟨Function.update t1.reg rX (Glyph.bit true), Function.update t1.stk sM LM⟩
    let t3 : State := ⟨Function.update t2.reg rD gAny, t2.stk⟩
    let t4 : State := ⟨Function.update t3.reg rY gUnit, Function.update t3.stk sT2 (gUnit :: t3.stk sT2)⟩
    let t5 : State := ⟨Function.update t4.reg rY gUnit, Function.update t4.stk sT2 (gUnit :: t4.stk sT2)⟩
    have h1 : Ev main (.pop sP rX) s t1 1 := by
      have h := ev_pop_st main sP rX s
      dsimp only [t1] at h ⊢
      simpa [hP] using h
    have hne1 : t1.reg rX ≠ gmk sP := by dsimp only [t1]; simp [unit_ne_markerP]
    have h2 : Ev main (.pop sM rX) t1 t2 1 := by
      have h := ev_pop_st main sM rX t1
      dsimp only [t1, t2] at h ⊢
      simpa [hM] using h
    have hne2 : t2.reg rX ≠ gmk sM := by dsimp only [t2, t1]; simp [bit_ne_marker]
    have hx : t2.reg rX = Glyph.bit true := by dsimp only [t2, t1]; simp
    have hD : Ev main (.ite rX (Glyph.bit true) (.set rD gAny) .skip) t2 t3 2 := by
      dsimp only [t3]; exact Ev.iteT hx (ev_set_st main rD gAny t2)
    have hpu1 : Ev main (pushC sT2 gUnit rY) t3 t4 2 := by
      dsimp only [t4]; exact ev_pushC_st main sT2 gUnit rY t3
    have hpu2 : Ev main (pushC sT2 gUnit rY) t4 t5 2 := by
      dsimp only [t5]; exact ev_pushC_st main sT2 gUnit rY t4
    have hDseq : Ev main (seqs [.ite rX (Glyph.bit true) (.set rD gAny) .skip,
        pushC sT2 gUnit rY, pushC sT2 gUnit rY]) t2 t5 6 :=
      Ev.seq' hD (Ev.seq' hpu1 hpu2 (le_rfl)) (by omega)
    have hite2 : Ev main (.ite rX (gmk sM) (seqs [.push sM rX, .set rE gStop, .set rI gStop])
        (seqs [.ite rX (Glyph.bit true) (.set rD gAny) .skip,
          pushC sT2 gUnit rY, pushC sT2 gUnit rY])) t2 t5 7 :=
      Ev.iteF hne2 hDseq
    have hB : Ev main (seqs [.pop sM rX, .ite rX (gmk sM)
        (seqs [.push sM rX, .set rE gStop, .set rI gStop])
        (seqs [.ite rX (Glyph.bit true) (.set rD gAny) .skip,
          pushC sT2 gUnit rY, pushC sT2 gUnit rY])]) t1 t5 8 :=
      Ev.seq' h2 hite2 (le_rfl)
    have hite1 : Ev main (.ite rX (gmk sP) (seqs [.push sP rX, .set rI gStop])
        (seqs [.pop sM rX, .ite rX (gmk sM) (seqs [.push sM rX, .set rE gStop, .set rI gStop])
        (seqs [.ite rX (Glyph.bit true) (.set rD gAny) .skip,
          pushC sT2 gUnit rY, pushC sT2 gUnit rY])])) t1 t5 9 :=
      Ev.iteF hne1 hB
    have hall : Ev main shrPassBody s t5 10 := by
      dsimp only [shrPassBody]
      exact Ev.seq' h1 hite1 (le_rfl)
    obtain ⟨n, he, hn⟩ := hall
    refine ⟨t5, n, he, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp only [t5, t4, t3, t2, t1]; simp
    · dsimp only [t5, t4, t3, t2, t1]; simp
    · dsimp only [t5, t4, t3, t2, t1]; simp
    · dsimp only [t5, t4, t3, t2, t1]; simp
    · dsimp only [t5, t4, t3, t2, t1]; simp
    · dsimp only [t5, t4, t3, t2, t1]; simp
    · intro j hj1 hj2 hj3; dsimp only [t5, t4, t3, t2, t1]; simp [hj1, hj2, hj3]

/-- The iteration that stops the pass because the block region is exhausted (the top of `sP` is the
frame marker `gmk sP`): the marker is pushed back and `rI` is set to `gStop`. -/
theorem shrPass_hitP_ev (main : Cmd) (s : State) (LP : List Glyph)
    (hP : s.stk sP = gmk sP :: LP) :
    ∃ (s' : State) (n : ℕ), Eval main shrPassBody s s' n ∧ n ≤ 4 ∧
      s'.reg rI = gStop ∧ s'.reg rE = s.reg rE ∧ s'.reg rD = s.reg rD ∧
      s'.stk sP = gmk sP :: LP ∧
      (∀ j : Stk, j ≠ sP → s'.stk j = s.stk j) := by
  let t1 : State := ⟨Function.update s.reg rX (gmk sP), Function.update s.stk sP LP⟩
  let t2 : State := ⟨Function.update s.reg rX (gmk sP),
    Function.update (Function.update s.stk sP LP) sP (gmk sP :: LP)⟩
  let t3 : State := ⟨Function.update (Function.update s.reg rX (gmk sP)) rI gStop, t2.stk⟩
  have h1 : Ev main (.pop sP rX) s t1 1 := by
    have h := ev_pop_st main sP rX s
    dsimp only [t1] at h ⊢
    simpa [hP] using h
  have htest : t1.reg rX = gmk sP := by dsimp only [t1]; simp
  have hpush : Ev main (.push sP rX) t1 t2 1 := by
    have h := ev_push_st main sP rX t1
    dsimp only [t1, t2] at h ⊢
    simpa using h
  have hset : Ev main (.set rI gStop) t2 t3 1 := by
    dsimp only [t3]; exact ev_set_st main rI gStop t2
  have hseq : Ev main (seqs [.push sP rX, .set rI gStop]) t1 t3 2 := Ev.seq' hpush hset (le_rfl)
  have hall : Ev main shrPassBody s t3 4 := by
    dsimp only [shrPassBody]
    exact Ev.seq' h1 (Ev.iteT htest hseq) (le_rfl)
  obtain ⟨n, he, hn⟩ := hall
  refine ⟨t3, n, he, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [t3, t2, t1]; simp
  · dsimp only [t3, t2, t1]; simp
  · dsimp only [t3, t2, t1]; simp
  · dsimp only [t3, t2, t1]; simp
  · intro j hj; dsimp only [t3, t2, t1]; simp [hj]

/-- The iteration that stops the pass because the bits of `|a|` are exhausted (the top of `sM` is
the frame marker `gmk sM`): the marker is pushed back, `rE` and `rI` are set to `gStop`, and the
block unit popped in this iteration is not returned. -/
theorem shrPass_hitM_ev (main : Cmd) (s : State) (LP LM : List Glyph)
    (hP : s.stk sP = gUnit :: LP) (hM : s.stk sM = gmk sM :: LM) :
    ∃ (s' : State) (n : ℕ), Eval main shrPassBody s s' n ∧ n ≤ 8 ∧
      s'.reg rI = gStop ∧ s'.reg rE = gStop ∧ s'.reg rD = s.reg rD ∧
      s'.stk sP = LP ∧ s'.stk sM = s.stk sM ∧
      (∀ j : Stk, j ≠ sP → j ≠ sM → s'.stk j = s.stk j) := by
  let t1 : State := ⟨Function.update s.reg rX gUnit, Function.update s.stk sP LP⟩
  let t2 : State := ⟨Function.update t1.reg rX (gmk sM), Function.update t1.stk sM LM⟩
  let t3 : State := ⟨t2.reg, Function.update t2.stk sM (t2.reg rX :: t2.stk sM)⟩
  let t4 : State := ⟨Function.update t2.reg rE gStop, t3.stk⟩
  let t5 : State := ⟨Function.update (Function.update t2.reg rE gStop) rI gStop, t3.stk⟩
  have h1 : Ev main (.pop sP rX) s t1 1 := by
    have h := ev_pop_st main sP rX s
    dsimp only [t1] at h ⊢
    simpa [hP] using h
  have hne1 : t1.reg rX ≠ gmk sP := by dsimp only [t1]; simp [unit_ne_markerP]
  have h2 : Ev main (.pop sM rX) t1 t2 1 := by
    have h := ev_pop_st main sM rX t1
    dsimp only [t1, t2] at h ⊢
    simpa [hM] using h
  have hx : t2.reg rX = gmk sM := by dsimp only [t2, t1]; simp
  have hpush : Ev main (.push sM rX) t2 t3 1 := by
    have h := ev_push_st main sM rX t2
    dsimp only [t3, t2, t1] at h ⊢
    simpa using h
  have hsetE : Ev main (.set rE gStop) t3 t4 1 := by
    dsimp only [t4]; exact ev_set_st main rE gStop t3
  have hsetI : Ev main (.set rI gStop) t4 t5 1 := by
    dsimp only [t5, t4]; exact ev_set_st main rI gStop t4
  have hC : Ev main (seqs [.push sM rX, .set rE gStop, .set rI gStop]) t2 t5 3 :=
    Ev.seq' hpush (Ev.seq' hsetE hsetI (le_rfl)) (by omega)
  have hite2 : Ev main (.ite rX (gmk sM) (seqs [.push sM rX, .set rE gStop, .set rI gStop])
      (seqs [.ite rX (Glyph.bit true) (.set rD gAny) .skip,
        pushC sT2 gUnit rY, pushC sT2 gUnit rY])) t2 t5 4 :=
    Ev.iteT hx hC
  have hB : Ev main (seqs [.pop sM rX, .ite rX (gmk sM)
      (seqs [.push sM rX, .set rE gStop, .set rI gStop])
      (seqs [.ite rX (Glyph.bit true) (.set rD gAny) .skip,
        pushC sT2 gUnit rY, pushC sT2 gUnit rY])]) t1 t5 5 :=
    Ev.seq' h2 hite2 (le_rfl)
  have hite1 : Ev main (.ite rX (gmk sP) (seqs [.push sP rX, .set rI gStop])
      (seqs [.pop sM rX, .ite rX (gmk sM) (seqs [.push sM rX, .set rE gStop, .set rI gStop])
      (seqs [.ite rX (Glyph.bit true) (.set rD gAny) .skip,
        pushC sT2 gUnit rY, pushC sT2 gUnit rY])])) t1 t5 6 :=
    Ev.iteF hne1 hB
  have hall : Ev main shrPassBody s t5 7 := by
    dsimp only [shrPassBody]
    exact Ev.seq' h1 hite1 (le_rfl)
  obtain ⟨n, he, hn⟩ := hall
  refine ⟨t5, n, he, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [t5, t4, t3, t2, t1]; simp
  · dsimp only [t5, t4, t3, t2, t1]; simp
  · dsimp only [t5, t4, t3, t2, t1]; simp
  · dsimp only [t5, t4, t3, t2, t1]; simp
  · dsimp only [t5, t4, t3, t2, t1]; simp [hM]
  · intro j hj1 hj2; dsimp only [t5, t4, t3, t2, t1]; simp [hj1, hj2]

/-! ## The block pass -/

theorem shrPass_loop_ev (main : Cmd) :
    ∀ (bs : List Bool) (p : ℕ) (T0 JP JM JT2 : List Glyph) (s : State),
      AllUnit T0 →
      s.stk sP = List.replicate p gUnit ++ gmk sP :: JP →
      s.stk sM = bs.map Glyph.bit ++ gmk sM :: JM →
      s.stk sT2 = T0 ++ gmk sT2 :: JT2 →
      s.reg rI = gGo →
      ∃ (s' : State) (n : ℕ),
        Eval main (.loop rI gGo shrPassBody) s s' n ∧
        n ≤ 20 * (min p bs.length + 2) ∧
        s'.reg rI ≠ gGo ∧
        s'.stk sP = List.replicate (p - (min p bs.length + if p ≤ bs.length then 0 else 1)) gUnit
          ++ gmk sP :: JP ∧
        s'.stk sM = (bs.drop (min p bs.length)).map Glyph.bit ++ gmk sM :: JM ∧
        s'.stk sT2 = T0 ++ List.replicate (2 * min p bs.length) gUnit ++ gmk sT2 :: JT2 ∧
        (p ≤ bs.length → s'.reg rE = s.reg rE) ∧
        (bs.length < p → s'.reg rE = gStop) ∧
        (s'.reg rD = gAny ↔ (s.reg rD = gAny ∨ true ∈ bs.take (min p bs.length))) ∧
        (∀ j : Stk, j ≠ sP → j ≠ sM → j ≠ sT2 → s'.stk j = s.stk j) := by
  intro bs
  induction bs with
  | nil =>
    intro p T0 JP JM JT2 s hU hP hM hT hgo
    rcases p with _ | p'
    · obtain ⟨s1, n1, he1, hn1, hrI1, hrE1, hrD1, hP1, hfr1⟩ :=
        shrPass_hitP_ev main s JP (by simpa using hP)
      have hloop : Ev main (.loop rI gGo shrPassBody) s s1 (n1 + 1 + 1) :=
        Ev.loopT hgo ⟨n1, he1, le_rfl⟩
          (Ev.loopF (main := main) (by rw [hrI1]; exact gStop_ne_gGo))
      obtain ⟨m, hm, hmle⟩ := hloop
      refine ⟨s1, m, hm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [List.length_nil, Nat.zero_min]; omega
      · rw [hrI1]; exact gStop_ne_gGo
      · simpa only [Nat.zero_sub, List.replicate_zero, List.nil_append] using hP1
      · simpa only [List.drop_nil, List.map_nil, List.nil_append]
          using (hfr1 sM (by decide)).trans hM
      · simpa only [Nat.zero_min, Nat.mul_zero, List.replicate_zero, List.append_nil]
          using (hfr1 sT2 (by decide)).trans hT
      · intro _; exact hrE1
      · intro h; exact absurd h (by decide)
      · rw [hrD1]; simp only [List.take_nil, List.not_mem_nil, or_false]
      · exact fun j h1 _ _ => hfr1 j h1
    · have hP' : s.stk sP = gUnit :: (List.replicate p' gUnit ++ gmk sP :: JP) := by
        rw [hP, List.replicate_succ, List.cons_append]
      obtain ⟨s1, n1, he1, hn1, hrI1, hrE1, hrD1, hP1, hM1, hfr1⟩ :=
        shrPass_hitM_ev main s (List.replicate p' gUnit ++ gmk sP :: JP) JM hP'
          (by simpa using hM)
      have hloop : Ev main (.loop rI gGo shrPassBody) s s1 (n1 + 1 + 1) :=
        Ev.loopT hgo ⟨n1, he1, le_rfl⟩
          (Ev.loopF (main := main) (by rw [hrI1]; exact gStop_ne_gGo))
      obtain ⟨m, hm, hmle⟩ := hloop
      refine ⟨s1, m, hm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [List.length_nil, Nat.min_zero]; omega
      · rw [hrI1]; exact gStop_ne_gGo
      · rw [show (p' + 1 - (min (p'+1) ([] : List Bool).length +
            if (p'+1) ≤ ([] : List Bool).length then 0 else 1)) = p' by simp [List.length_nil]]
        exact hP1
      · simpa only [List.drop_nil, List.map_nil, List.nil_append] using hM1.trans (by simpa using hM)
      · simpa only [List.length_nil, Nat.min_zero, Nat.mul_zero, List.replicate_zero,
            List.append_nil]
          using (hfr1 sT2 (by decide) (by decide)).trans hT
      · intro h; exact absurd h (by simp [List.length_nil])
      · intro _; exact hrE1
      · rw [hrD1]; simp only [List.take_nil, List.not_mem_nil, or_false]
      · exact fun j h1 h2 _ => hfr1 j h1 h2
  | cons b bs' ih =>
    intro p T0 JP JM JT2 s hU hP hM hT hgo
    rcases p with _ | p'
    · obtain ⟨s1, n1, he1, hn1, hrI1, hrE1, hrD1, hP1, hfr1⟩ :=
        shrPass_hitP_ev main s JP (by simpa using hP)
      have hloop : Ev main (.loop rI gGo shrPassBody) s s1 (n1 + 1 + 1) :=
        Ev.loopT hgo ⟨n1, he1, le_rfl⟩
          (Ev.loopF (main := main) (by rw [hrI1]; exact gStop_ne_gGo))
      obtain ⟨m, hm, hmle⟩ := hloop
      refine ⟨s1, m, hm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [Nat.zero_min]; omega
      · rw [hrI1]; exact gStop_ne_gGo
      · simpa only [Nat.zero_sub, List.replicate_zero, List.nil_append] using hP1
      · simpa only [Nat.zero_min, List.drop_zero, List.nil_append]
          using (hfr1 sM (by decide)).trans hM
      · simpa only [Nat.zero_min, Nat.mul_zero, List.replicate_zero, List.append_nil]
          using (hfr1 sT2 (by decide)).trans hT
      · intro _; exact hrE1
      · intro h; exact absurd h (by omega)
      · rw [hrD1]; simp only [Nat.zero_min, List.take_zero, List.not_mem_nil, or_false]
      · exact fun j h1 _ _ => hfr1 j h1
    · have hP' : s.stk sP = gUnit :: (List.replicate p' gUnit ++ gmk sP :: JP) := by
        rw [hP, List.replicate_succ, List.cons_append]
      have hM' : s.stk sM = Glyph.bit b :: (bs'.map Glyph.bit ++ gmk sM :: JM) := by
        rw [hM, List.map_cons, List.cons_append]
      obtain ⟨s1, n1, he1, hn1, hrI1, hrE1, hrD1, hP1, hM1, hT1, hfr1⟩ :=
        shrPass_go_ev main s b (List.replicate p' gUnit ++ gmk sP :: JP)
          (bs'.map Glyph.bit ++ gmk sM :: JM) hP' hM'
      have hU1 : AllUnit ([gUnit, gUnit] ++ T0) := AllEq.append (allEq_replicate gUnit 2) hU
      have hT1' : s1.stk sT2 = ([gUnit, gUnit] ++ T0) ++ gmk sT2 :: JT2 := by
        rw [hT1, hT]; rfl
      obtain ⟨s2, n2, he2, hn2, hrI2, hP2, hM2, hT2, hrE2a, hrE2b, hrD2, hfr2⟩ :=
        ih p' ([gUnit, gUnit] ++ T0) JP JM JT2 s1 hU1 hP1 hM1 hT1' (hrI1.trans hgo)
      have hloop : Ev main (.loop rI gGo shrPassBody) s s2 (n1 + n2 + 1) :=
        Ev.loopT hgo ⟨n1, he1, le_rfl⟩ ⟨n2, he2, le_rfl⟩
      obtain ⟨m, hm, hmle⟩ := hloop
      refine ⟨s2, m, hm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [List.length_cons, shrPass_min_succ_succ p' bs'.length]; omega
      · exact hrI2
      · rw [List.length_cons, shrPass_sub_min_succ p' bs'.length]; exact hP2
      · rw [List.length_cons, shrPass_min_succ_succ p' bs'.length, List.drop_succ_cons]; exact hM2
      · rw [List.length_cons, shrPass_min_succ_succ p' bs'.length,
            ← shrPass_allUnit_append_repl hU (min p' bs'.length)]
        exact hT2
      · intro h; rw [hrE2a (Nat.succ_le_succ_iff.mp h), hrE1]
      · intro h; exact hrE2b (Nat.lt_of_succ_lt_succ h)
      · rw [List.length_cons, shrPass_min_succ_succ p' bs'.length, List.take_succ_cons,
            List.mem_cons, hrD2, hrD1]
        simp only [or_assoc]
      · exact fun j h1 h2 h3 => (hfr2 j h1 h2 h3).trans (hfr1 j h1 h2 h3)

/-- The `shr` block pass. -/
theorem shrPass_ev (main : HvdH.Cmd) (p : ℕ) (bs : List Bool) (T0 : List HvdH.Glyph)
    (JP JM JT2 : List HvdH.Glyph) (s : HvdH.State)
    (hT0 : ∀ h ∈ T0, h = Work.IntLib.Shift.gUnit)
    (hP : s.stk Work.IntLib.Shift.sP = List.replicate p Work.IntLib.Shift.gUnit ++ Work.IntLib.Shift.gmk Work.IntLib.Shift.sP :: JP)
    (hM : s.stk Work.IntLib.Shift.sM = bs.map HvdH.Glyph.bit ++ Work.IntLib.Shift.gmk Work.IntLib.Shift.sM :: JM)
    (hT : s.stk Work.IntLib.Shift.sT2 = T0 ++ Work.IntLib.Shift.gmk Work.IntLib.Shift.sT2 :: JT2)
    (hr : s.reg Work.IntLib.Shift.rI = Work.IntLib.Shift.gGo) :
    ∃ (s' : HvdH.State) (n : ℕ),
      HvdH.Eval main (HvdH.Cmd.loop Work.IntLib.Shift.rI Work.IntLib.Shift.gGo Work.IntLib.Shift.shrPassBody) s s' n ∧
      n ≤ 20 * (min p bs.length + 2) ∧
      s'.reg Work.IntLib.Shift.rI ≠ Work.IntLib.Shift.gGo ∧
      s'.stk Work.IntLib.Shift.sP = List.replicate
        (p - (min p bs.length + if p ≤ bs.length then 0 else 1)) Work.IntLib.Shift.gUnit
          ++ Work.IntLib.Shift.gmk Work.IntLib.Shift.sP :: JP ∧
      s'.stk Work.IntLib.Shift.sM = (bs.drop (min p bs.length)).map HvdH.Glyph.bit ++ Work.IntLib.Shift.gmk Work.IntLib.Shift.sM :: JM ∧
      s'.stk Work.IntLib.Shift.sT2 = T0 ++ List.replicate (2 * min p bs.length) Work.IntLib.Shift.gUnit ++ Work.IntLib.Shift.gmk Work.IntLib.Shift.sT2 :: JT2 ∧
      (p ≤ bs.length → s'.reg Work.IntLib.Shift.rE = s.reg Work.IntLib.Shift.rE) ∧
      (bs.length < p → s'.reg Work.IntLib.Shift.rE = Work.IntLib.Shift.gStop) ∧
      (s'.reg Work.IntLib.Shift.rD = Work.IntLib.Shift.gAny ↔
        (s.reg Work.IntLib.Shift.rD = Work.IntLib.Shift.gAny ∨ true ∈ (bs.take (min p bs.length)))) ∧
      (∀ j : HvdH.Stk, j ≠ Work.IntLib.Shift.sP → j ≠ Work.IntLib.Shift.sM →
        j ≠ Work.IntLib.Shift.sT2 → s'.stk j = s.stk j) :=
  shrPass_loop_ev main bs p T0 JP JM JT2 s hT0 hP hM hT hr

end Work.IntLib.Shift
