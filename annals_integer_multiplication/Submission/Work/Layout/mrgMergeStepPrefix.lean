import Mathlib
import Submission.Work.Layout.mrgDefs

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-!
# `Work.Layout.mrgMergeStepPrefix`

The twelve-command *prefix* of `Sk.mergeStep`: pop the `cons` tags of the two front records of
`SX`/`SY`, copy the cached key sizes from `SA`/`SB` onto the value stack and compare them (`pLt`),
keeping the two comparison results on `F1`/`F2`, then read both flags into `rH` (does `SY`'s front
have the smaller key?) and `rG` (does `SX`'s front have the smaller key?).

The proof is a straight chain of the primitive `Ev` facts (`ev_pop'`, `dupInt_ev`,
`mvVal_ev_full`, the `BinOp` hypothesis `hLt`, and `merge_readFlag_reg`), threading the states
`s1 … s12` and the frames of each step.
-/

namespace Work.Layout

open HvdH Work.Layout
open Work.Layout.Sk

/-! ## local helpers -/

/-- `a ∉ l` and `b ∈ l` give `a ≠ b` -/
private theorem ne_of_notMem {a y : Stk} {l : List Stk} (h : a ∉ l) (hy : y ∈ l) : a ≠ y :=
  fun hay => h (hay ▸ hy)

/-- the individual `∉`-facts carried by the pairwise distinctness of the ten stacks -/
private theorem hdis10_peel {SX SY T SA SB F1 F2 t d : Stk}
    (hdis : ([SX, SY, T, SA, SB, F1, F2, t, d, 0] : List Stk).Nodup) :
    (SX ∉ ([SY, T, SA, SB, F1, F2, t, d, 0] : List Stk)) ∧
    (SY ∉ ([T, SA, SB, F1, F2, t, d, 0] : List Stk)) ∧
    (T ∉ ([SA, SB, F1, F2, t, d, 0] : List Stk)) ∧
    (SA ∉ ([SB, F1, F2, t, d, 0] : List Stk)) ∧
    (SB ∉ ([F1, F2, t, d, 0] : List Stk)) ∧
    (F1 ∉ ([F2, t, d, 0] : List Stk)) ∧
    (F2 ∉ ([t, d, 0] : List Stk)) ∧
    (t ∉ ([d, 0] : List Stk)) ∧
    (d ∉ ([0] : List Stk)) := by
  rw [List.nodup_cons] at hdis; obtain ⟨h1, hdis⟩ := hdis
  rw [List.nodup_cons] at hdis; obtain ⟨h2, hdis⟩ := hdis
  rw [List.nodup_cons] at hdis; obtain ⟨h3, hdis⟩ := hdis
  rw [List.nodup_cons] at hdis; obtain ⟨h4, hdis⟩ := hdis
  rw [List.nodup_cons] at hdis; obtain ⟨h5, hdis⟩ := hdis
  rw [List.nodup_cons] at hdis; obtain ⟨h6, hdis⟩ := hdis
  rw [List.nodup_cons] at hdis; obtain ⟨h7, hdis⟩ := hdis
  rw [List.nodup_cons] at hdis; obtain ⟨h8, hdis⟩ := hdis
  rw [List.nodup_cons] at hdis; obtain ⟨h9, -⟩ := hdis
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- a one-element `encs` -/
private theorem encs_single (v : Val) : encs [v] = v.enc := by simp [encs]

/-- a one-element `encs`, with the tail -/
private theorem encs_single_append (v : Val) (R : List Glyph) : encs [v] ++ R = v.enc ++ R := by
  simp [encs_single]

/-! ## register frames

`Sk.readFlag f r` clobbers the register `rJ` as well as `r`; the second flag of the prefix must
not destroy the first one, so we need a register-frame lemma for `readFlag`.
-/

/-- the registers a command may write -/
private def cmdWrites : Cmd → Finset Reg
  | .skip => ∅
  | .pop _ r => {r}
  | .peek _ r => {r}
  | .push _ _ => ∅
  | .set r _ => {r}
  | .mov dst _ => {dst}
  | .seq a b => cmdWrites a ∪ cmdWrites b
  | .ite _ _ a b => cmdWrites a ∪ cmdWrites b
  | .loop _ _ a => cmdWrites a
  | .self => Finset.univ

/-- a command that cannot write `r` leaves `r` unchanged -/
private theorem eval_reg_frame {main : Cmd} {c : Cmd} {s s' : State} {n : ℕ}
    (h : Eval main c s s' n) {r : Reg} (hr : r ∉ cmdWrites c) : s'.reg r = s.reg r := by
  induction h with
  | skip s => rfl
  | pop k r' s =>
      simp only [cmdWrites, Finset.mem_singleton] at hr
      exact Function.update_of_ne hr _ _
  | peek k r' s =>
      simp only [cmdWrites, Finset.mem_singleton] at hr
      exact Function.update_of_ne hr _ _
  | push k r' s => rfl
  | set r' c s =>
      simp only [cmdWrites, Finset.mem_singleton] at hr
      exact Function.update_of_ne hr _ _
  | mov dst src s =>
      simp only [cmdWrites, Finset.mem_singleton] at hr
      exact Function.update_of_ne hr _ _
  | seq h1 h2 ih1 ih2 =>
      simp only [cmdWrites, Finset.mem_union, not_or] at hr
      rw [ih2 hr.2, ih1 hr.1]
  | iteT hr' h ih =>
      simp only [cmdWrites, Finset.mem_union, not_or] at hr
      exact ih hr.1
  | iteF hr' h ih =>
      simp only [cmdWrites, Finset.mem_union, not_or] at hr
      exact ih hr.2
  | loopF hr' => rfl
  | loopT hr' h1 h2 ih1 ih2 =>
      simp only [cmdWrites] at hr
      rw [ih2 hr, ih1 hr]
  | self h ih => exact absurd (Finset.mem_univ _) hr

/-- the same for bounded evaluation -/
private theorem ev_reg_frame {main : Cmd} {p : Cmd} {s s' : State} {C : ℕ}
    (h : Ev main p s s' C) {r : Reg} (hr : r ∉ cmdWrites p) : s'.reg r = s.reg r := by
  obtain ⟨n, he, -⟩ := h
  exact eval_reg_frame he hr

/-! ## the flag word -/

private theorem vsz_flag_le (b : Bool) : vsz (Val.int (if b then (1 : ℤ) else 0)) ≤ 3 := by
  cases b <;> decide

private theorem vsz_flag_le' (p : Prop) [Decidable p] :
    vsz (Val.int (if p then (1 : ℤ) else 0)) ≤ 3 := by
  by_cases hp : p
  · rw [ite_eq_left hp]
    exact vsz_flag_le true
  · rw [ite_eq_right hp]
    exact vsz_flag_le false

/-! ## `readFlag` -/

/-- `readFlag` with the flag written as a propositional `if` -/
private theorem merge_readFlag' {main : Cmd} {f : Stk} {r : Reg} (hrJ : r ≠ rJ) {g : Reg → Glyph}
    {X : Stk → List Glyph} {p : Prop} [Decidable p] {G : List Glyph}
    (hf : X f = (Val.int (if p then (1 : ℤ) else 0)).enc ++ G) :
    ∃ s' n, Ev main (Sk.readFlag f r) ⟨g, X⟩ s' n ∧ n ≤ 6 ∧ s'.stk f = G ∧
      s'.reg r = (if p then Glyph.bit true else Glyph.iend) ∧
      (∀ k', k' ≠ f → s'.stk k' = X k') := by
  by_cases hp : p
  · rw [ite_eq_left hp] at hf
    obtain ⟨s', n, hev, hn, hstk, hreg, hfr⟩ :=
      merge_readFlag (main := main) (f := f) (r := r) hrJ (b := true) (G := G) hf
    rw [ite_eq_left hp]
    exact ⟨s', n, hev, hn, hstk, hreg, hfr⟩
  · rw [ite_eq_right hp] at hf
    obtain ⟨s', n, hev, hn, hstk, hreg, hfr⟩ :=
      merge_readFlag (main := main) (f := f) (r := r) hrJ (b := false) (G := G) hf
    rw [ite_eq_right hp]
    exact ⟨s', n, hev, hn, hstk, hreg, hfr⟩

/-- `readFlag`, with the additional information that it writes nothing but `r` and `rJ` -/
private theorem merge_readFlag_reg {main : Cmd} {f : Stk} {r : Reg} (hrJ : r ≠ rJ)
    {g : Reg → Glyph} {X : Stk → List Glyph} {p : Prop} [Decidable p] {G : List Glyph}
    (hf : X f = (Val.int (if p then (1 : ℤ) else 0)).enc ++ G) :
    ∃ s' n, Ev main (Sk.readFlag f r) ⟨g, X⟩ s' n ∧ n ≤ 6 ∧ s'.stk f = G ∧
      s'.reg r = (if p then Glyph.bit true else Glyph.iend) ∧
      (∀ k', k' ≠ f → s'.stk k' = X k') ∧
      (∀ r' : Reg, r' ≠ r → r' ≠ rJ → s'.reg r' = g r') := by
  obtain ⟨s', n, hev, hn, hstk, hreg, hfr⟩ :=
    merge_readFlag' (main := main) (f := f) (r := r) hrJ (p := p) (G := G) hf
  refine ⟨s', n, hev, hn, hstk, hreg, hfr, ?_⟩
  have hw : cmdWrites (Sk.readFlag f r) = ({r, rJ} : Finset Reg) := by
    ext x
    simp only [Sk.readFlag, cmdWrites, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, or_false]
    tauto
  intro r' hr'r hr'rJ
  exact ev_reg_frame hev (by
    rw [hw]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hr'r, hr'rJ⟩)

theorem mrgMergeStepPrefix {main pLt : HvdH.Cmd} {KLt : ℕ}
    (hLt : ∀ main : HvdH.Cmd, HvdH.BinOp main pLt (fun _ _ => True) (fun a b => if a < b then 1 else 0)
      (fun a b => KLt * (HvdH.isz a + HvdH.isz b)))
    {SX SY T SA SB F1 F2 t d : HvdH.Stk}
    (hdis : ([SX, SY, T, SA, SB, F1, F2, t, d, 0] : List HvdH.Stk).Nodup)
    {g : HvdH.Reg → HvdH.Glyph} {X : HvdH.Stk → List HvdH.Glyph} {k l : ℕ} {v' w' : HvdH.Val} {ps qs : List HvdH.Val}
    {A B' Sc Sc' R : List HvdH.Glyph}
    (hSX : X SX = (HvdH.Val.cons (HvdH.Val.int (k : ℤ)) v').enc ++ HvdH.encs ps ++ Work.Layout.gMark :: A)
    (hSY : X SY = (HvdH.Val.cons (HvdH.Val.int (l : ℤ)) w').enc ++ HvdH.encs qs ++ Work.Layout.gMark :: B')
    (hSA : X SA = (HvdH.Val.int (k.size : ℤ)).enc ++ Sc)
    (hSB : X SB = (HvdH.Val.int (l.size : ℤ)).enc ++ Sc')
    (h0 : X 0 = R) :
    ∃ s' n, Work.Layout.Ev main (seqs [ .pop SX Work.Layout.Sk.rI, .pop SY Work.Layout.Sk.rJ, Work.Layout.Sk.dupInt SA 0 t d, Work.Layout.Sk.dupInt SB 0 t d,
        pLt, Work.Layout.mvVal 0 F1 t d, Work.Layout.Sk.dupInt SB 0 t d, Work.Layout.Sk.dupInt SA 0 t d, pLt, Work.Layout.mvVal 0 F2 t d,
        Work.Layout.Sk.readFlag F1 Work.Layout.Sk.rH, Work.Layout.Sk.readFlag F2 Work.Layout.Sk.rG ]) ⟨g, X⟩ s' n ∧
      n ≤ 2 + 40 * (HvdH.isz (k.size : ℤ) + 1) + 40 * (HvdH.isz (l.size : ℤ) + 1)
            + KLt * (HvdH.isz (l.size : ℤ) + HvdH.isz (k.size : ℤ)) + 64
            + 40 * (HvdH.isz (l.size : ℤ) + 1) + 40 * (HvdH.isz (k.size : ℤ) + 1)
            + KLt * (HvdH.isz (k.size : ℤ) + HvdH.isz (l.size : ℤ)) + 64 + 6 + 6 ∧
      s'.stk 0 = R ∧
      s'.stk SX = (HvdH.Val.int (k : ℤ)).enc ++ (v'.enc ++ (HvdH.encs ps ++ Work.Layout.gMark :: A)) ∧
      s'.stk SY = (HvdH.Val.int (l : ℤ)).enc ++ (w'.enc ++ (HvdH.encs qs ++ Work.Layout.gMark :: B')) ∧
      s'.stk T = X T ∧ s'.stk SA = X SA ∧ s'.stk SB = X SB ∧
      s'.stk F1 = X F1 ∧ s'.stk F2 = X F2 ∧ s'.stk t = X t ∧ s'.stk d = X d ∧
      s'.reg Work.Layout.Sk.rH = (if l.size < k.size then HvdH.Glyph.bit true else HvdH.Glyph.iend) ∧
      s'.reg Work.Layout.Sk.rG = (if k.size < l.size then HvdH.Glyph.bit true else HvdH.Glyph.iend) ∧
      (∀ k' : HvdH.Stk, k' ∉ ({SX, SY, SA, SB, F1, F2, t, d, 0} : Finset HvdH.Stk) → s'.stk k' = X k') := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9⟩ := hdis10_peel hdis
  have hSX_SY : SX ≠ SY := ne_of_notMem i1 (by simp)
  have hSX_T : SX ≠ T := ne_of_notMem i1 (by simp)
  have hSX_SA : SX ≠ SA := ne_of_notMem i1 (by simp)
  have hSX_SB : SX ≠ SB := ne_of_notMem i1 (by simp)
  have hSX_t : SX ≠ t := ne_of_notMem i1 (by simp)
  have hSX_d : SX ≠ d := ne_of_notMem i1 (by simp)
  have hSX_0 : SX ≠ 0 := ne_of_notMem i1 (by simp)
  have hSX_F1 : SX ≠ F1 := ne_of_notMem i1 (by simp)
  have hSX_F2 : SX ≠ F2 := ne_of_notMem i1 (by simp)
  have hSY_T : SY ≠ T := ne_of_notMem i2 (by simp)
  have hSY_SA : SY ≠ SA := ne_of_notMem i2 (by simp)
  have hSY_SB : SY ≠ SB := ne_of_notMem i2 (by simp)
  have hSY_t : SY ≠ t := ne_of_notMem i2 (by simp)
  have hSY_d : SY ≠ d := ne_of_notMem i2 (by simp)
  have hSY_0 : SY ≠ 0 := ne_of_notMem i2 (by simp)
  have hSY_F1 : SY ≠ F1 := ne_of_notMem i2 (by simp)
  have hSY_F2 : SY ≠ F2 := ne_of_notMem i2 (by simp)
  have hT_SA : T ≠ SA := ne_of_notMem i3 (by simp)
  have hT_SB : T ≠ SB := ne_of_notMem i3 (by simp)
  have hT_t : T ≠ t := ne_of_notMem i3 (by simp)
  have hT_d : T ≠ d := ne_of_notMem i3 (by simp)
  have hT_0 : T ≠ 0 := ne_of_notMem i3 (by simp)
  have hT_F1 : T ≠ F1 := ne_of_notMem i3 (by simp)
  have hT_F2 : T ≠ F2 := ne_of_notMem i3 (by simp)
  have hSA_0 : SA ≠ 0 := ne_of_notMem i4 (by simp)
  have hSA_t : SA ≠ t := ne_of_notMem i4 (by simp)
  have hSA_d : SA ≠ d := ne_of_notMem i4 (by simp)
  have hSA_SB : SA ≠ SB := ne_of_notMem i4 (by simp)
  have hSA_F1 : SA ≠ F1 := ne_of_notMem i4 (by simp)
  have hSA_F2 : SA ≠ F2 := ne_of_notMem i4 (by simp)
  have hSB_0 : SB ≠ 0 := ne_of_notMem i5 (by simp)
  have hSB_t : SB ≠ t := ne_of_notMem i5 (by simp)
  have hSB_d : SB ≠ d := ne_of_notMem i5 (by simp)
  have hSB_F1 : SB ≠ F1 := ne_of_notMem i5 (by simp)
  have hSB_F2 : SB ≠ F2 := ne_of_notMem i5 (by simp)
  have hF1_t : F1 ≠ t := ne_of_notMem i6 (by simp)
  have hF1_d : F1 ≠ d := ne_of_notMem i6 (by simp)
  have hF1_0 : F1 ≠ 0 := ne_of_notMem i6 (by simp)
  have hF1_F2 : F1 ≠ F2 := ne_of_notMem i6 (by simp)
  have hF1_SB : F1 ≠ SB := hSB_F1.symm
  have hF1_SA : F1 ≠ SA := hSA_F1.symm
  have hF1_SY : F1 ≠ SY := hSY_F1.symm
  have hF1_SX : F1 ≠ SX := hSX_F1.symm
  have hF2_t : F2 ≠ t := ne_of_notMem i7 (by simp)
  have hF2_d : F2 ≠ d := ne_of_notMem i7 (by simp)
  have hF2_0 : F2 ≠ 0 := ne_of_notMem i7 (by simp)
  have hF2_SB : F2 ≠ SB := hSB_F2.symm
  have hF2_SA : F2 ≠ SA := hSA_F2.symm
  have hF2_SY : F2 ≠ SY := hSY_F2.symm
  have hF2_SX : F2 ≠ SX := hSX_F2.symm
  have hF2_F1 : F2 ≠ F1 := hF1_F2.symm
  have h0_t : (0 : Stk) ≠ t := (ne_of_notMem i8 (by simp)).symm
  have h0_d : (0 : Stk) ≠ d := (ne_of_notMem i9 (by simp)).symm
  have h0_F1 : (0 : Stk) ≠ F1 := hF1_0.symm
  have h0_F2 : (0 : Stk) ≠ F2 := hF2_0.symm
  have ht_d : t ≠ d := ne_of_notMem i8 (by simp)
  have hSXd : X SX = Glyph.cons ::
      ((Val.int (k : ℤ)).enc ++ (v'.enc ++ (encs ps ++ gMark :: A))) := by
    rw [hSX]
    simp only [Val.enc, List.cons_append, List.append_assoc]
  have hSYd : X SY = Glyph.cons ::
      ((Val.int (l : ℤ)).enc ++ (w'.enc ++ (encs qs ++ gMark :: B'))) := by
    rw [hSY]
    simp only [Val.enc, List.cons_append, List.append_assoc]
  -- (1) `pop SX rI`
  obtain ⟨s1, e1, h1SX, hf1⟩ : ∃ s1 : State, Ev main (.pop SX rI) ⟨g, X⟩ s1 1 ∧
      s1.stk SX = (Val.int (k : ℤ)).enc ++ (v'.enc ++ (encs ps ++ gMark :: A)) ∧
      (∀ j, j ≠ SX → s1.stk j = X j) := by
    refine ⟨⟨Function.update g rI ((X SX).headD Glyph.eos), Function.update X SX (X SX).tail⟩,
      ev_pop' main SX rI g X, ?_, ?_⟩
    · show (Function.update X SX (X SX).tail) SX =
        (Val.int (k : ℤ)).enc ++ (v'.enc ++ (encs ps ++ gMark :: A))
      rw [Function.update_self, hSXd]
      rfl
    · intro j hj
      simp [Function.update_of_ne hj]
  -- (2) `pop SY rJ`
  obtain ⟨s2, e2, h2SY, hf2⟩ : ∃ s2 : State, Ev main (.pop SY rJ) s1 s2 1 ∧
      s2.stk SY = (Val.int (l : ℤ)).enc ++ (w'.enc ++ (encs qs ++ gMark :: B')) ∧
      (∀ j, j ≠ SY → s2.stk j = s1.stk j) := by
    refine ⟨⟨Function.update s1.reg rJ ((s1.stk SY).headD Glyph.eos),
      Function.update s1.stk SY (s1.stk SY).tail⟩,
      ev_pop' main SY rJ s1.reg s1.stk, ?_, ?_⟩
    · show (Function.update s1.stk SY (s1.stk SY).tail) SY =
        (Val.int (l : ℤ)).enc ++ (w'.enc ++ (encs qs ++ gMark :: B'))
      rw [Function.update_self, hf1 SY hSX_SY.symm, hSYd]
      rfl
    · intro j hj
      simp [Function.update_of_ne hj]
  -- (3) `dupInt SA 0 t d`
  have h2SA : s2.stk SA = (Val.int (k.size : ℤ)).enc ++ Sc := by
    rw [hf2 SA hSY_SA.symm, hf1 SA hSX_SA.symm, hSA]
  obtain ⟨s3, n3, e3, hn3, h3SA, h3s0, h3t, h3d, hf3⟩ :=
    dupInt_ev (main := main) (S := SA) (B := 0) (T := t) (d := d) hSA_0 hSA_t hSA_d h0_t h0_d
      ht_d (g := s2.reg) (z := (k.size : ℤ)) (A := Sc) h2SA
  -- (4) `dupInt SB 0 t d`
  have h3SB : s3.stk SB = (Val.int (l.size : ℤ)).enc ++ Sc' := by
    rw [hf3 SB hSA_SB.symm hSB_0 hSB_t hSB_d, hf2 SB hSY_SB.symm, hf1 SB hSX_SB.symm, hSB]
  obtain ⟨s4, n4, e4, hn4, h4SB, h4s0, h4t, h4d, hf4⟩ :=
    dupInt_ev (main := main) (S := SB) (B := 0) (T := t) (d := d) hSB_0 hSB_t hSB_d h0_t h0_d
      ht_d (g := s3.reg) (z := (l.size : ℤ)) (A := Sc') h3SB
  have h4s0d : s4.stk 0 = encs [Val.int (l.size : ℤ), Val.int (k.size : ℤ)] ++ R := by
    rw [h4s0, h3s0, hf2 0 hSY_0.symm, hf1 0 hSX_0.symm, h0]
    exact (encs_two _ _ R).symm
  -- (5) `pLt` on the key sizes
  obtain ⟨out5, s5, n5, hpost5, e5, hn5, h5s0, hf5⟩ :=
    (hLt main) [Val.int (l.size : ℤ), Val.int (k.size : ℤ)]
      ⟨(l.size : ℤ), (k.size : ℤ), ([] : List Val), rfl, trivial⟩ s4 R h4s0d
  have hev5 : Ev main pLt s4 s5 n5 := ⟨n5, e5, le_rfl⟩
  obtain ⟨a5, b5, r5, hvs5, hout5⟩ := hpost5
  have ha5 : a5 = (l.size : ℤ) := (Val.int.inj (List.cons.inj hvs5).1).symm
  have hb5 : b5 = (k.size : ℤ) := (Val.int.inj (List.cons.inj (List.cons.inj hvs5).2).1).symm
  have hr5 : r5 = ([] : List Val) := ((List.cons.inj (List.cons.inj hvs5).2).2).symm
  have h5s0d : s5.stk 0 = (Val.int (if l.size < k.size then (1 : ℤ) else 0)).enc ++ R := by
    rw [h5s0, hout5, ha5, hb5, hr5]
    simp only [Int.ofNat_lt]
    exact encs_single_append _ R
  -- (6) `mvVal 0 F1 t d`
  have h5F1 : s5.stk F1 = X F1 := by
    rw [hf5 F1 hF1_0, hf4 F1 hF1_SB hF1_0 hF1_t hF1_d, hf3 F1 hF1_SA hF1_0 hF1_t hF1_d,
      hf2 F1 hF1_SY, hf1 F1 hF1_SX]
  obtain ⟨s6, n6, e6, hn6, h6s0, h6F1, h6t, h6d, hf6⟩ :=
    mvVal_ev_full (main := main) (a := 0) (b := F1) (c := t) (d := d) hF1_0.symm h0_t h0_d
      hF1_t hF1_d ht_d (g := s5.reg) (v := Val.int (if l.size < k.size then (1 : ℤ) else 0))
      (A := R) (B := X F1) h5s0d h5F1
  -- (7) `dupInt SB 0 t d`
  have h6SB : s6.stk SB = (Val.int (l.size : ℤ)).enc ++ Sc' := by
    rw [hf6 SB hSB_0 hSB_F1 hSB_t hSB_d, hf5 SB hSB_0, h4SB, h3SB]
  obtain ⟨s7, n7, e7, hn7, h7SB, h7s0, h7t, h7d, hf7⟩ :=
    dupInt_ev (main := main) (S := SB) (B := 0) (T := t) (d := d) hSB_0 hSB_t hSB_d h0_t h0_d
      ht_d (g := s6.reg) (z := (l.size : ℤ)) (A := Sc') h6SB
  -- (8) `dupInt SA 0 t d`
  have h7SA : s7.stk SA = (Val.int (k.size : ℤ)).enc ++ Sc := by
    rw [hf7 SA hSA_SB hSA_0 hSA_t hSA_d, hf6 SA hSA_0 hSA_F1 hSA_t hSA_d, hf5 SA hSA_0,
      hf4 SA hSA_SB hSA_0 hSA_t hSA_d, h3SA, hf2 SA hSY_SA.symm,
      hf1 SA hSX_SA.symm, hSA]
  obtain ⟨s8, n8, e8, hn8, h8SA, h8s0, h8t, h8d, hf8⟩ :=
    dupInt_ev (main := main) (S := SA) (B := 0) (T := t) (d := d) hSA_0 hSA_t hSA_d h0_t h0_d
      ht_d (g := s7.reg) (z := (k.size : ℤ)) (A := Sc) h7SA
  have h8s0d : s8.stk 0 = encs [Val.int (k.size : ℤ), Val.int (l.size : ℤ)] ++ R := by
    rw [h8s0, h7s0, h6s0]
    exact (encs_two _ _ R).symm
  -- (9) `pLt` on the keys
  obtain ⟨out9, s9, n9, hpost9, e9, hn9, h9s0, hf9⟩ :=
    (hLt main) [Val.int (k.size : ℤ), Val.int (l.size : ℤ)]
      ⟨(k.size : ℤ), (l.size : ℤ), ([] : List Val), rfl, trivial⟩ s8 R h8s0d
  have hev9 : Ev main pLt s8 s9 n9 := ⟨n9, e9, le_rfl⟩
  obtain ⟨a9, b9, r9, hvs9, hout9⟩ := hpost9
  have ha9 : a9 = (k.size : ℤ) := (Val.int.inj (List.cons.inj hvs9).1).symm
  have hb9 : b9 = (l.size : ℤ) := (Val.int.inj (List.cons.inj (List.cons.inj hvs9).2).1).symm
  have hr9 : r9 = ([] : List Val) := ((List.cons.inj (List.cons.inj hvs9).2).2).symm
  have h9s0d : s9.stk 0 = (Val.int (if k.size < l.size then (1 : ℤ) else 0)).enc ++ R := by
    rw [h9s0, hout9, ha9, hb9, hr9]
    simp only [Int.ofNat_lt]
    exact encs_single_append _ R
  -- (10) `mvVal 0 F2 t d`
  have h9F2 : s9.stk F2 = X F2 := by
    rw [hf9 F2 hF2_0, hf8 F2 hF2_SA hF2_0 hF2_t hF2_d, hf7 F2 hF2_SB hF2_0 hF2_t hF2_d,
      hf6 F2 hF2_0 hF2_F1 hF2_t hF2_d, hf5 F2 hF2_0, hf4 F2 hF2_SB hF2_0 hF2_t hF2_d,
      hf3 F2 hF2_SA hF2_0 hF2_t hF2_d, hf2 F2 hF2_SY, hf1 F2 hF2_SX]
  obtain ⟨s10, n10, e10, hn10, h10s0, h10F2, h10t, h10d, hf10⟩ :=
    mvVal_ev_full (main := main) (a := 0) (b := F2) (c := t) (d := d) hF2_0.symm h0_t h0_d
      hF2_t hF2_d ht_d (g := s9.reg) (v := Val.int (if k.size < l.size then (1 : ℤ) else 0))
      (A := R) (B := X F2) h9s0d h9F2
  -- (11) `readFlag F1 rH`
  have h10F1 : s10.stk F1 = (Val.int (if l.size < k.size then (1 : ℤ) else 0)).enc ++ X F1 := by
    rw [hf10 F1 hF1_0 hF1_F2 hF1_t hF1_d, hf9 F1 hF1_0, hf8 F1 hF1_SA hF1_0 hF1_t hF1_d,
      hf7 F1 hF1_SB hF1_0 hF1_t hF1_d, h6F1]
  obtain ⟨s11, n11, e11, hn11, h11F1, h11rH, hf11, hreg11⟩ :=
    merge_readFlag_reg (main := main) (f := F1) (r := rH) (by decide) (g := s10.reg)
      (p := l.size < k.size) (G := X F1) h10F1
  -- (12) `readFlag F2 rG`
  have h11F2 : s11.stk F2 = (Val.int (if k.size < l.size then (1 : ℤ) else 0)).enc ++ X F2 := by
    rw [hf11 F2 hF2_F1, h10F2]
  obtain ⟨s12, n12, e12, hn12, h12F2, h12rG, hf12, hreg12⟩ :=
    merge_readFlag_reg (main := main) (f := F2) (r := rG) (by decide) (g := s11.reg)
      (p := k.size < l.size) (G := X F2) h11F2
  -- the values of the "restored" stacks at the end of the prefix
  have h12_T : s12.stk T = X T := by rw [hf12 T hT_F2, hf11 T hT_F1, hf10 T hT_0 hT_F2 hT_t hT_d, hf9 T hT_0, hf8 T hT_SA hT_0 hT_t hT_d, hf7 T hT_SB hT_0 hT_t hT_d, hf6 T hT_0 hT_F1 hT_t hT_d, hf5 T hT_0, hf4 T hT_SB hT_0 hT_t hT_d, hf3 T hT_SA hT_0 hT_t hT_d, hf2 T hSY_T.symm, hf1 T hSX_T.symm]
  have h12_0 : s12.stk 0 = X 0 := by rw [hf12 0 hF2_0.symm, hf11 0 hF1_0.symm, h10s0, h0]
  have h12_SA : s12.stk SA = X SA := by rw [hf12 SA hSA_F2, hf11 SA hSA_F1, hf10 SA hSA_0 hSA_F2 hSA_t hSA_d, hf9 SA hSA_0, h8SA, hf7 SA hSA_SB hSA_0 hSA_t hSA_d, hf6 SA hSA_0 hSA_F1 hSA_t hSA_d, hf5 SA hSA_0, hf4 SA hSA_SB hSA_0 hSA_t hSA_d, h3SA, hf2 SA hSY_SA.symm, hf1 SA hSX_SA.symm]
  have h12_SB : s12.stk SB = X SB := by rw [hf12 SB hSB_F2, hf11 SB hSB_F1, hf10 SB hSB_0 hSB_F2 hSB_t hSB_d, hf9 SB hSB_0, hf8 SB hSA_SB.symm hSB_0 hSB_t hSB_d, h7SB, hf6 SB hSB_0 hSB_F1 hSB_t hSB_d, hf5 SB hSB_0, h4SB, hf3 SB hSA_SB.symm hSB_0 hSB_t hSB_d, hf2 SB hSY_SB.symm, hf1 SB hSX_SB.symm]
  have h12_t : s12.stk t = X t := by rw [hf12 t hF2_t.symm, hf11 t hF1_t.symm, h10t, hf9 t h0_t.symm, h8t, h7t, h6t, hf5 t h0_t.symm, h4t, h3t, hf2 t hSY_t.symm, hf1 t hSX_t.symm]
  have h12_d : s12.stk d = X d := by rw [hf12 d hF2_d.symm, hf11 d hF1_d.symm, h10d, hf9 d h0_d.symm, h8d, h7d, h6d, hf5 d h0_d.symm, h4d, h3d, hf2 d hSY_d.symm, hf1 d hSX_d.symm]
  have h12_F1 : s12.stk F1 = X F1 := by rw [hf12 F1 hF1_F2, h11F1]
  have h12_F2 : s12.stk F2 = X F2 := by rw [h12F2]
  have h12SX : s12.stk SX = (Val.int (k : ℤ)).enc ++ (v'.enc ++ (encs ps ++ gMark :: A)) := by
    rw [hf12 SX hSX_F2, hf11 SX hSX_F1, hf10 SX hSX_0 hSX_F2 hSX_t hSX_d,
      hf9 SX hSX_0, hf8 SX hSX_SA hSX_0 hSX_t hSX_d,
      hf7 SX hSX_SB hSX_0 hSX_t hSX_d, hf6 SX hSX_0 hSX_F1 hSX_t hSX_d,
      hf5 SX hSX_0, hf4 SX hSX_SB hSX_0 hSX_t hSX_d,
      hf3 SX hSX_SA hSX_0 hSX_t hSX_d, hf2 SX hSX_SY, h1SX]
  have h12SY : s12.stk SY = (Val.int (l : ℤ)).enc ++ (w'.enc ++ (encs qs ++ gMark :: B')) := by
    rw [hf12 SY hSY_F2, hf11 SY hSY_F1, hf10 SY hSY_0 hSY_F2 hSY_t hSY_d,
      hf9 SY hSY_0, hf8 SY hSY_SA hSY_0 hSY_t hSY_d,
      hf7 SY hSY_SB hSY_0 hSY_t hSY_d, hf6 SY hSY_0 hSY_F1 hSY_t hSY_d,
      hf5 SY hSY_0, hf4 SY hSY_SB hSY_0 hSY_t hSY_d,
      hf3 SY hSY_SA hSY_0 hSY_t hSY_d, h2SY]
  have h12rH : s12.reg rH = (if l.size < k.size then Glyph.bit true else Glyph.iend) := by
    rw [hreg12 rH (by decide) (by decide), h11rH]
  have h12frT : ∀ k', k' ∉ ({SX, SY, SA, SB, T, F1, F2, t, d, 0} : Finset Stk) →
      s12.stk k' = X k' := by
    intro k' hk
    have eSX : k' ≠ SX := by rintro rfl; exact hk (by simp)
    have eSY : k' ≠ SY := by rintro rfl; exact hk (by simp)
    have eSA : k' ≠ SA := by rintro rfl; exact hk (by simp)
    have eSB : k' ≠ SB := by rintro rfl; exact hk (by simp)
    have eT : k' ≠ T := by rintro rfl; exact hk (by simp)
    have eF1 : k' ≠ F1 := by rintro rfl; exact hk (by simp)
    have eF2 : k' ≠ F2 := by rintro rfl; exact hk (by simp)
    have et : k' ≠ t := by rintro rfl; exact hk (by simp)
    have ed : k' ≠ d := by rintro rfl; exact hk (by simp)
    have e0 : k' ≠ 0 := by rintro rfl; exact hk (by simp)
    rw [hf12 k' eF2, hf11 k' eF1, hf10 k' e0 eF2 et ed, hf9 k' e0, hf8 k' eSA e0 et ed,
      hf7 k' eSB e0 et ed, hf6 k' e0 eF1 et ed, hf5 k' e0, hf4 k' eSB e0 et ed,
      hf3 k' eSA e0 et ed, hf2 k' eSY, hf1 k' eSX]
  -- the frame of the statement excludes only the stacks the prefix can touch (`T` is untouched)
  have h12fr : ∀ k', k' ∉ ({SX, SY, SA, SB, F1, F2, t, d, 0} : Finset Stk) →
      s12.stk k' = X k' := by
    intro k' hk
    by_cases hT : k' = T
    · rw [hT]; exact h12_T
    · refine h12frT k' ?_
      intro hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk hmem
      tauto
  have hEv12 : Ev main (seqs [.pop SX rI, .pop SY rJ, Sk.dupInt SA 0 t d, Sk.dupInt SB 0 t d,
      pLt, mvVal 0 F1 t d, Sk.dupInt SB 0 t d, Sk.dupInt SA 0 t d, pLt, mvVal 0 F2 t d,
      Sk.readFlag F1 rH, Sk.readFlag F2 rG]) ⟨g, X⟩ s12
      (1 + (1 + (n3 + (n4 + (n5 + (n6 + (n7 + (n8 + (n9 + (n10 + (6 + (6)))))))))))) :=
    Ev.seq' (C := 1 + (1 + (n3 + (n4 + (n5 + (n6 + (n7 + (n8 + (n9 + (n10 + (6 + (6)))))))))))) e1 (Ev.seq' (C := 1 + (n3 + (n4 + (n5 + (n6 + (n7 + (n8 + (n9 + (n10 + (6 + (6))))))))))) e2 (Ev.seq' (C := n3 + (n4 + (n5 + (n6 + (n7 + (n8 + (n9 + (n10 + (6 + (6)))))))))) e3 (Ev.seq' (C := n4 + (n5 + (n6 + (n7 + (n8 + (n9 + (n10 + (6 + (6))))))))) e4 (Ev.seq' (C := n5 + (n6 + (n7 + (n8 + (n9 + (n10 + (6 + (6)))))))) hev5 (Ev.seq' (C := n6 + (n7 + (n8 + (n9 + (n10 + (6 + (6))))))) e6 (Ev.seq' (C := n7 + (n8 + (n9 + (n10 + (6 + (6)))))) e7 (Ev.seq' (C := n8 + (n9 + (n10 + (6 + (6))))) e8 (Ev.seq' (C := n9 + (n10 + (6 + (6)))) hev9 (Ev.seq' (C := n10 + (6 + (6))) e10 (Ev.seq' (C := 6 + (6)) (e11.mono hn11) ((e12.mono hn12)) (by omega)) (by omega)) (by omega)) (by omega)) (by omega)) (by omega)) (by omega)) (by omega)) (by omega)) (by omega)) (by omega)
  have hcost12 : (1 + (1 + (n3 + (n4 + (n5 + (n6 + (n7 + (n8 + (n9 + (n10 + (6 + (6)))))))))))) ≤ 2 + 40 * (isz (k.size : ℤ) + 1) + 40 * (isz (l.size : ℤ) + 1)
          + KLt * (isz (l.size : ℤ) + isz (k.size : ℤ)) + 64
          + 40 * (isz (l.size : ℤ) + 1) + 40 * (isz (k.size : ℤ) + 1)
          + KLt * (isz (k.size : ℤ) + isz (l.size : ℤ)) + 64 + 6 + 6 := by
    have h3b : n3 ≤ 40 * (isz (k.size : ℤ) + 1) := by rw [vsz_int] at hn3; exact hn3
    have h4b : n4 ≤ 40 * (isz (l.size : ℤ) + 1) := by rw [vsz_int] at hn4; exact hn4
    have h7b : n7 ≤ 40 * (isz (l.size : ℤ) + 1) := by rw [vsz_int] at hn7; exact hn7
    have h8b : n8 ≤ 40 * (isz (k.size : ℤ) + 1) := by rw [vsz_int] at hn8; exact hn8
    have h5b : n5 ≤ KLt * (isz (l.size : ℤ) + isz (k.size : ℤ)) := by
      simpa [binCost] using hn5
    have h9b : n9 ≤ KLt * (isz (k.size : ℤ) + isz (l.size : ℤ)) := by
      simpa [binCost] using hn9
    have h6b : n6 ≤ 64 := by
      have hv := vsz_flag_le' (l.size < k.size)
      exact le_trans hn6 (by omega)
    have h10b : n10 ≤ 64 := by
      have hv := vsz_flag_le' (k.size < l.size)
      exact le_trans hn10 (by omega)
    omega

  exact ⟨s12, 1 + (1 + (n3 + (n4 + (n5 + (n6 + (n7 + (n8 + (n9 + (n10 + (6 + (6))))))))))),
    hEv12, hcost12, by rw [h12_0, h0], h12SX, h12SY, h12_T, h12_SA, h12_SB, h12_F1, h12_F2,
    h12_t, h12_d, h12rH, h12rG, h12fr⟩

end Work.Layout
