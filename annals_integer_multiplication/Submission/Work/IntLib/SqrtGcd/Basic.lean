import Submission.Work.IntLib.SqrtGcd.Defs

/-!
# Sqrt / gcd: the raw toolkit

Raw StackLang loops over *bit regions* (defined in `Defs.lean`):

* `rLoop k T d r` — pop the glyphs above the marker `T` on stack `k`, pushing each of them onto
  stack `d` (`d = none` means "discard"); the marker `T` is pushed back and stays.  So `d = none`
  is a *drop*, `d = some d'` a *reversed move*.
* `stripZeros k r` — drop the leading `Glyph.bit false` glyphs of the region on stack `k`, leaving
  the first non-`false` glyph (the marker, or a `true` bit) on top.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib
namespace SG

open HvdH Work.Layout

theorem State.ext' {s t : State} (h1 : ∀ r, s.reg r = t.reg r) (h2 : ∀ k, s.stk k = t.stk k) :
    s = t := by
  cases s with
  | mk a b =>
    cases t with
    | mk c d => simp only [State.mk.injEq]; exact ⟨funext h1, funext h2⟩

/-! ## `rLoop`: move / drop a region -/

/-- The "push" performed by `rLoop` for each popped glyph. -/
def pushOpt (d : Option Stk) (r : Reg) : Cmd :=
  match d with
  | none => .skip
  | some d' => .push d' r

/-- One step of `rLoop`. -/
def rBody (k : Stk) (T : Glyph) (d : Option Stk) (r : Reg) : Cmd :=
  .seq (.pop k r)
    (.ite r T (.seq (.push k r) (.set r T)) (.seq (pushOpt d r) (.set r Glyph.eos)))

def rLoop (k : Stk) (T : Glyph) (d : Option Stk) (r : Reg) : Cmd :=
  .seq (.set r Glyph.eos) (.loop r Glyph.eos (rBody k T d r))

/-- Result state of dropping the region `gs` (above the marker `T`) of stack `k`. -/
def dSt (k : Stk) (T : Glyph) (r : Reg) (below : List Glyph) (s : State) : State :=
  ⟨Function.update s.reg r T, Function.update s.stk k (T :: below)⟩

/-- Result state of moving the region `gs` (above the marker `T`) of stack `k` onto stack `d`. -/
def mSt (k : Stk) (T : Glyph) (d : Stk) (r : Reg) (gs below : List Glyph) (s : State) : State :=
  ⟨Function.update s.reg r T,
    Function.update (Function.update s.stk k (T :: below)) d (gs.reverse ++ s.stk d)⟩

theorem dLoopAux (main : Cmd) (k : Stk) (T : Glyph) (r : Reg) (hTe : T ≠ Glyph.eos) :
    ∀ (gs : List Glyph) (below : List Glyph) (s : State), s.stk k = gs ++ T :: below →
      (∀ g ∈ gs, g ≠ T) → s.reg r = Glyph.eos →
      Eval main (.loop r Glyph.eos (rBody k T none r)) s (dSt k T r below s)
        (6 + gs.length * 5) := by
  intro gs
  induction gs with
  | nil =>
      intro below s hstk _ hr
      let s1 : State := ⟨Function.update s.reg r T, Function.update s.stk k below⟩
      let s2 : State := ⟨s1.reg, Function.update s1.stk k (T :: below)⟩
      let s3 : State := ⟨Function.update s2.reg r T, s2.stk⟩
      have hs1k : s1.stk k = below := by simp [s1, Function.update_apply]
      have e1 : Eval main (.pop k r) s s1 1 := by
        have h := Eval.pop (main := main) k r s
        rw [hstk] at h
        simpa [s1, Function.update_apply, List.headD_cons, List.tail_cons] using h
      have hr1 : s1.reg r = T := by simp [s1, Function.update_apply]
      have e2 : Eval main (.push k r) s1 s2 1 := by
        have h := Eval.push (main := main) k r s1
        simpa [s2, State.tPush, hr1, hs1k] using h
      have e3 : Eval main (.set r T) s2 s3 1 := by
        have h := Eval.set (main := main) r T s2
        simpa [s3] using h
      have e23 : Eval main (.seq (.push k r) (.set r T)) s1 s3 2 := Eval.seq e2 e3
      have eite : Eval main (.ite r T (.seq (.push k r) (.set r T))
          (.seq (pushOpt none r) (.set r Glyph.eos))) s1 s3 3 := Eval.iteT hr1 e23
      have ebody : Eval main (rBody k T none r) s s3 4 := Eval.seq e1 eite
      have hr2 : s3.reg r ≠ Glyph.eos := by
        have h : s3.reg r = T := by simp [s3, s2, Function.update_apply]
        rw [h]; exact hTe
      have eloop : Eval main (.loop r Glyph.eos (rBody k T none r)) s3 s3 1 := Eval.loopF hr2
      have hmain : Eval main (.loop r Glyph.eos (rBody k T none r)) s s3 6 :=
        Eval.loopT hr ebody eloop
      have hstate : s3 = dSt k T r below s := by
        apply State.ext'
        · intro q; simp only [dSt, s3, s2, s1, Function.update_apply]
          by_cases hq : q = r
          · subst hq; simp
          · simp [hq]
        · intro q; simp only [dSt, s3, s2, s1, Function.update_apply]
          by_cases hq : q = k
          · subst hq; simp
          · simp [hq]
      rw [hstate] at hmain
      have hc : 6 + ([] : List Glyph).length * 5 = 6 := by simp
      rw [hc]
      exact hmain
  | cons g gs' ih =>
      intro below s hstk hT hr
      have hgT : g ≠ T := hT g (by simp)
      have hgs'T : ∀ g' ∈ gs', g' ≠ T := fun g' h' => hT g' (by simp [h'])
      have hstk' : s.stk k = g :: (gs' ++ T :: below) := by simpa using hstk
      let s1 : State := ⟨Function.update s.reg r g, Function.update s.stk k (gs' ++ T :: below)⟩
      let s2 : State := s1
      let s3 : State := ⟨Function.update s2.reg r Glyph.eos, s2.stk⟩
      have e1 : Eval main (.pop k r) s s1 1 := by
        have h := Eval.pop (main := main) k r s
        rw [hstk'] at h
        simpa [s1, Function.update_apply, List.headD_cons, List.tail_cons] using h
      have hr1 : s1.reg r = g := by simp [s1, Function.update_apply]
      have hgT' : ¬ (s1.reg r = T) := by rw [hr1]; exact hgT
      have e2 : Eval main (.skip : Cmd) s1 s2 1 := Eval.skip (main := main) s1
      have e3 : Eval main (.set r Glyph.eos) s2 s3 1 := by
        have h := Eval.set (main := main) r Glyph.eos s2
        simpa [s3] using h
      have e23 : Eval main (.seq (.skip : Cmd) (.set r Glyph.eos)) s1 s3 2 := Eval.seq e2 e3
      have eite : Eval main (.ite r T (.seq (.push k r) (.set r T))
          (.seq (pushOpt none r) (.set r Glyph.eos))) s1 s3 3 := Eval.iteF hgT' e23
      have ebody : Eval main (rBody k T none r) s s3 4 := Eval.seq e1 eite
      have hr3 : s3.reg r = Glyph.eos := by simp [s3, s2, Function.update_apply]
      have hs3k : s3.stk k = gs' ++ T :: below := by simp [s3, s2, s1, Function.update_apply]
      have hrec := ih below s3 hs3k hgs'T hr3
      have hmain : Eval main (.loop r Glyph.eos (rBody k T none r)) s (dSt k T r below s3)
          (4 + (6 + gs'.length * 5) + 1) := Eval.loopT hr ebody hrec
      have hstate : dSt k T r below s3 = dSt k T r below s := by
        apply State.ext'
        · intro q; simp only [dSt, s3, s2, s1, Function.update_apply]
          by_cases hq : q = r
          · subst hq; simp
          · simp [hq]
        · intro q; simp only [dSt, s3, s2, s1, Function.update_apply]
          by_cases hq : q = k
          · subst hq; simp
          · simp [hq]
      rw [hstate] at hmain
      have hc : 4 + (6 + gs'.length * 5) + 1 = 6 + (g :: gs').length * 5 := by
        simp only [List.length_cons]; ring
      rw [← hc]
      exact hmain

theorem mLoopAux (main : Cmd) (k : Stk) (T : Glyph) (d : Stk) (r : Reg) (hTe : T ≠ Glyph.eos)
    (hdk : d ≠ k) :
    ∀ (gs : List Glyph) (below : List Glyph) (s : State), s.stk k = gs ++ T :: below →
      (∀ g ∈ gs, g ≠ T) → s.reg r = Glyph.eos →
      Eval main (.loop r Glyph.eos (rBody k T (some d) r)) s (mSt k T d r gs below s)
        (6 + gs.length * 5) := by
  intro gs
  induction gs with
  | nil =>
      intro below s hstk _ hr
      let s1 : State := ⟨Function.update s.reg r T, Function.update s.stk k below⟩
      let s2 : State := ⟨s1.reg, Function.update s1.stk k (T :: below)⟩
      let s3 : State := ⟨Function.update s2.reg r T, s2.stk⟩
      have hs1k : s1.stk k = below := by simp [s1, Function.update_apply]
      have e1 : Eval main (.pop k r) s s1 1 := by
        have h := Eval.pop (main := main) k r s
        rw [hstk] at h
        simpa [s1, Function.update_apply, List.headD_cons, List.tail_cons] using h
      have hr1 : s1.reg r = T := by simp [s1, Function.update_apply]
      have e2 : Eval main (.push k r) s1 s2 1 := by
        have h := Eval.push (main := main) k r s1
        simpa [s2, State.tPush, hr1, hs1k] using h
      have e3 : Eval main (.set r T) s2 s3 1 := by
        have h := Eval.set (main := main) r T s2
        simpa [s3] using h
      have e23 : Eval main (.seq (.push k r) (.set r T)) s1 s3 2 := Eval.seq e2 e3
      have eite : Eval main (.ite r T (.seq (.push k r) (.set r T))
          (.seq (pushOpt (some d) r) (.set r Glyph.eos))) s1 s3 3 := Eval.iteT hr1 e23
      have ebody : Eval main (rBody k T (some d) r) s s3 4 := Eval.seq e1 eite
      have hr2 : s3.reg r ≠ Glyph.eos := by
        have h : s3.reg r = T := by simp [s3, s2, Function.update_apply]
        rw [h]; exact hTe
      have eloop : Eval main (.loop r Glyph.eos (rBody k T (some d) r)) s3 s3 1 :=
        Eval.loopF hr2
      have hmain : Eval main (.loop r Glyph.eos (rBody k T (some d) r)) s s3 6 :=
        Eval.loopT hr ebody eloop
      have hstate : s3 = mSt k T d r [] below s := by
        apply State.ext'
        · intro q; simp only [mSt, s3, s2, s1, Function.update_apply]
          by_cases hq : q = r
          · subst hq; simp
          · simp [hq]
        · intro q; simp only [mSt, s3, s2, s1, Function.update_apply]
          by_cases hq : q = k
          · subst hq; simp [Ne.symm hdk]
          · by_cases hq' : q = d
            · subst hq'; simp [hq]
            · simp [hq, hq']
      rw [hstate] at hmain
      have hc : 6 + ([] : List Glyph).length * 5 = 6 := by simp
      rw [hc]
      exact hmain
  | cons g gs' ih =>
      intro below s hstk hT hr
      have hgT : g ≠ T := hT g (by simp)
      have hgs'T : ∀ g' ∈ gs', g' ≠ T := fun g' h' => hT g' (by simp [h'])
      have hstk' : s.stk k = g :: (gs' ++ T :: below) := by simpa using hstk
      let s1 : State := ⟨Function.update s.reg r g, Function.update s.stk k (gs' ++ T :: below)⟩
      let s2 : State := ⟨s1.reg, Function.update s1.stk d (s1.reg r :: s1.stk d)⟩
      let s3 : State := ⟨Function.update s2.reg r Glyph.eos, s2.stk⟩
      have e1 : Eval main (.pop k r) s s1 1 := by
        have h := Eval.pop (main := main) k r s
        rw [hstk'] at h
        simpa [s1, Function.update_apply, List.headD_cons, List.tail_cons] using h
      have hr1 : s1.reg r = g := by simp [s1, Function.update_apply]
      have hgT' : ¬ (s1.reg r = T) := by rw [hr1]; exact hgT
      have e2 : Eval main (.push d r) s1 s2 1 := by
        have h := Eval.push (main := main) d r s1
        simpa [s2, State.tPush, hr1] using h
      have e3 : Eval main (.set r Glyph.eos) s2 s3 1 := by
        have h := Eval.set (main := main) r Glyph.eos s2
        simpa [s3] using h
      have e23 : Eval main (.seq (.push d r) (.set r Glyph.eos)) s1 s3 2 := Eval.seq e2 e3
      have eite : Eval main (.ite r T (.seq (.push k r) (.set r T))
          (.seq (pushOpt (some d) r) (.set r Glyph.eos))) s1 s3 3 := Eval.iteF hgT' e23
      have ebody : Eval main (rBody k T (some d) r) s s3 4 := Eval.seq e1 eite
      have hr3 : s3.reg r = Glyph.eos := by simp [s3, s2, Function.update_apply]
      have hs3k : s3.stk k = gs' ++ T :: below := by
        simp [s3, s2, s1, Function.update_apply, Ne.symm hdk]
      have hrec := ih below s3 hs3k hgs'T hr3
      have hmain : Eval main (.loop r Glyph.eos (rBody k T (some d) r)) s
          (mSt k T d r gs' below s3) (4 + (6 + gs'.length * 5) + 1) := Eval.loopT hr ebody hrec
      have hstate : mSt k T d r gs' below s3 = mSt k T d r (g :: gs') below s := by
        apply State.ext'
        · intro q; simp only [mSt, s3, s2, s1, Function.update_apply]
          by_cases hq : q = r
          · subst hq; simp
          · simp [hq]
        · intro q; simp only [mSt, s3, s2, s1, Function.update_apply]
          by_cases hq : q = k
          · subst hq; simp [Ne.symm hdk, List.reverse_cons, List.append_assoc]
          · by_cases hq' : q = d
            · subst hq'
              simp [hq, List.reverse_cons, List.append_assoc]
            · simp [hq, hq']
      rw [hstate] at hmain
      have hc : 4 + (6 + gs'.length * 5) + 1 = 6 + (g :: gs').length * 5 := by
        simp only [List.length_cons]; ring
      rw [← hc]
      exact hmain

theorem dLoop_eval (main : Cmd) (k : Stk) (T : Glyph) (r : Reg) (hTe : T ≠ Glyph.eos)
    (gs : List Glyph) (below : List Glyph) (s : State) (hstk : s.stk k = gs ++ T :: below)
    (hT : ∀ g ∈ gs, g ≠ T) :
    Eval main (rLoop k T none r) s (dSt k T r below s) (7 + gs.length * 5) := by
  have h1 : Eval main (.set r Glyph.eos) s (s.updReg r Glyph.eos) 1 := Eval.set r Glyph.eos s
  have h2 : Eval main (.loop r Glyph.eos (rBody k T none r)) (s.updReg r Glyph.eos)
      (dSt k T r below (s.updReg r Glyph.eos)) (6 + gs.length * 5) :=
    dLoopAux main k T r hTe gs below (s.updReg r Glyph.eos) (by simpa using hstk) hT (by simp)
  have h3 : dSt k T r below (s.updReg r Glyph.eos) = dSt k T r below s := by
    apply State.ext'
    · intro q; simp only [dSt, State.updReg_apply]
      by_cases hq : q = r
      · subst hq; simp
      · simp [hq]
    · intro q; simp only [dSt, State.updReg_stk]
  rw [h3] at h2
  have h4 := Eval.seq h1 h2
  have hc : 7 + gs.length * 5 = 1 + (6 + gs.length * 5) := by ring
  rw [hc]
  exact h4

theorem mLoop_eval (main : Cmd) (k : Stk) (T : Glyph) (d : Stk) (r : Reg) (hTe : T ≠ Glyph.eos)
    (hdk : d ≠ k) (gs : List Glyph) (below : List Glyph) (s : State)
    (hstk : s.stk k = gs ++ T :: below) (hT : ∀ g ∈ gs, g ≠ T) :
    Eval main (rLoop k T (some d) r) s (mSt k T d r gs below s) (7 + gs.length * 5) := by
  have h1 : Eval main (.set r Glyph.eos) s (s.updReg r Glyph.eos) 1 := Eval.set r Glyph.eos s
  have h2 : Eval main (.loop r Glyph.eos (rBody k T (some d) r)) (s.updReg r Glyph.eos)
      (mSt k T d r gs below (s.updReg r Glyph.eos)) (6 + gs.length * 5) :=
    mLoopAux main k T d r hTe hdk gs below (s.updReg r Glyph.eos) (by simpa using hstk) hT (by simp)
  have h3 : mSt k T d r gs below (s.updReg r Glyph.eos) = mSt k T d r gs below s := by
    apply State.ext'
    · intro q; simp only [mSt, State.updReg_apply]
      by_cases hq : q = r
      · subst hq; simp
      · simp [hq]
    · intro q; simp only [mSt, State.updReg_stk]
  rw [h3] at h2
  have h4 := Eval.seq h1 h2
  have hc : 7 + gs.length * 5 = 1 + (6 + gs.length * 5) := by ring
  rw [hc]
  exact h4


/-! ## `stripZeros`: drop the leading `false` bits of a region -/

def stripZeros (k : Stk) (r : Reg) : Cmd :=
  .seq (.set r (.bit false))
    (.seq (.loop r (.bit false) (.pop k r)) (.ite r .eos .skip (.push k r)))

/-- The loop of `stripZeros` pops the leading `false` bits of the region *and* the first other
glyph; the following `ite` pushes that glyph back. -/
theorem stripLoop_eval (main : Cmd) (k : Stk) (r : Reg) :
    ∀ (zs : ℕ) (rest : List Glyph) (s : State),
      s.stk k = (List.replicate zs false).map Glyph.bit ++ rest →
      rest.head? ≠ some (Glyph.bit false) → s.reg r = Glyph.bit false →
      Eval main (.loop r (.bit false) (.pop k r)) s
        ⟨Function.update s.reg r (rest.headD .eos), Function.update s.stk k rest.tail⟩ (2 * zs + 3) := by
  intro zs
  induction zs with
  | zero =>
      intro rest s hstk hrest hr
      simp only [List.replicate_zero, List.map_nil, List.nil_append] at hstk
      rcases rest with - | ⟨g, gs⟩
      · have h := Eval.pop (main := main) k r s
        rw [hstk] at h
        have hr' : (⟨Function.update s.reg r (([] : List Glyph).headD Glyph.eos),
            Function.update s.stk k (([] : List Glyph).tail)⟩ : State).reg r = Glyph.eos := by simp
        have h2 : Eval main (.loop r (.bit false) (.pop k r))
            ⟨Function.update s.reg r (([] : List Glyph).headD Glyph.eos),
              Function.update s.stk k (([] : List Glyph).tail)⟩
            ⟨Function.update s.reg r (([] : List Glyph).headD Glyph.eos),
              Function.update s.stk k (([] : List Glyph).tail)⟩ 1 :=
          Eval.loopF (by rw [hr']; decide)
        have h3 := Eval.loopT hr h h2
        have hc : 2 * 0 + 3 = 3 := by norm_num
        rw [hc]
        exact h3
      · have hg : g ≠ Glyph.bit false := by intro hcon; exact hrest (by simp [hcon])
        have h := Eval.pop (main := main) k r s
        rw [hstk] at h
        have hr' : (⟨Function.update s.reg r ((g :: gs).headD Glyph.eos),
            Function.update s.stk k ((g :: gs).tail)⟩ : State).reg r = g := by simp
        have h2 : Eval main (.loop r (.bit false) (.pop k r))
            ⟨Function.update s.reg r ((g :: gs).headD Glyph.eos),
              Function.update s.stk k ((g :: gs).tail)⟩
            ⟨Function.update s.reg r ((g :: gs).headD Glyph.eos),
              Function.update s.stk k ((g :: gs).tail)⟩ 1 :=
          Eval.loopF (by rw [hr']; exact hg)
        have h3 := Eval.loopT hr h h2
        have hc : 2 * 0 + 3 = 3 := by norm_num
        rw [hc]
        exact h3
  | succ zs ih =>
      intro rest s hstk hrest hr
      have hstk' : s.stk k = Glyph.bit false ::
          ((List.replicate zs false).map Glyph.bit ++ rest) := by
        simpa [List.replicate_succ, List.map_cons] using hstk
      let s1 : State := ⟨Function.update s.reg r (Glyph.bit false),
        Function.update s.stk k ((List.replicate zs false).map Glyph.bit ++ rest)⟩
      have h : Eval main (.pop k r) s s1 1 := by
        have hh := Eval.pop (main := main) k r s
        rw [hstk'] at hh
        simpa [s1, List.headD_cons, List.tail_cons] using hh
      have hreg : s1.reg r = Glyph.bit false := by simp [s1, Function.update_apply]
      have hs1 : s1.stk k = (List.replicate zs false).map Glyph.bit ++ rest := by
        simp [s1, Function.update_apply]
      have hrec := ih rest s1 hs1 hrest hreg
      have hmain := Eval.loopT hr h hrec
      have hstate : (⟨Function.update s1.reg r (rest.headD Glyph.eos),
            Function.update s1.stk k rest.tail⟩ : State)
          = ⟨Function.update s.reg r (rest.headD Glyph.eos), Function.update s.stk k rest.tail⟩ := by
        apply State.ext'
        · intro q; simp only [s1, Function.update_apply]
          by_cases hq : q = r
          · subst hq; simp
          · simp [hq]
        · intro q; simp only [s1, Function.update_apply]
          by_cases hq : q = k
          · subst hq; simp
          · simp [hq]
      rw [hstate] at hmain
      have hc : 2 * (zs + 1) + 3 = 1 + (2 * zs + 3) + 1 := by ring
      rw [hc]
      exact hmain

theorem stripZeros_eval (main : Cmd) (k : Stk) (r : Reg) (zs : ℕ) (rest : List Glyph) (s : State)
    (hstk : s.stk k = (List.replicate zs false).map Glyph.bit ++ rest)
    (hrest : rest.head? ≠ some (Glyph.bit false)) (heos : rest.head? ≠ some Glyph.eos) :
    Eval main (stripZeros k r) s
      ⟨Function.update s.reg r (rest.headD .eos), Function.update s.stk k rest⟩ (2 * zs + 6) := by
  let s1 : State := ⟨Function.update s.reg r (.bit false), s.stk⟩
  have h1 : Eval main (.set r (.bit false)) s s1 1 := by
    have h := Eval.set (main := main) r (.bit false) s
    simpa [s1] using h
  have h2 : Eval main (.loop r (.bit false) (.pop k r)) s1
      ⟨Function.update s1.reg r (rest.headD Glyph.eos), Function.update s1.stk k rest.tail⟩
      (2 * zs + 3) :=
    stripLoop_eval main k r zs rest s1 (by simp [s1, hstk, Function.update_apply]) hrest (by simp [s1])
  rcases rest with - | ⟨g, gs⟩
  · have ht : (⟨Function.update s1.reg r (([].headD Glyph.eos)),
        Function.update s1.stk k ([] : List Glyph).tail⟩ : State).reg r = Glyph.eos := by
      simp [s1, Function.update_apply]
    have h3 : Eval main (.ite r .eos .skip (.push k r))
        ⟨Function.update s1.reg r (([].headD Glyph.eos)),
          Function.update s1.stk k ([] : List Glyph).tail⟩
        ⟨Function.update s1.reg r (([].headD Glyph.eos)),
          Function.update s1.stk k ([] : List Glyph).tail⟩ 2 :=
      Eval.iteT ht (by simpa using Eval.skip (main := main) _)
    have h4 := Eval.seq h2 h3
    have hstate : (⟨Function.update s1.reg r (([].headD Glyph.eos)),
          Function.update s1.stk k ([] : List Glyph).tail⟩ : State)
        = ⟨Function.update s.reg r (([].headD Glyph.eos)), Function.update s.stk k ([] : List Glyph)⟩ := by
      apply State.ext'
      · intro q; simp only [s1, Function.update_apply]
        by_cases hq : q = r
        · subst hq; simp
        · simp [hq]
      · intro q; simp [s1, Function.update_apply]
    rw [hstate] at h4
    have hc : 2 * zs + 6 = 1 + ((2 * zs + 3) + 2) := by ring_nf
    rw [hc]
    exact Eval.seq h1 h4
  · have hg : g ≠ Glyph.eos := by intro hcon; exact heos (by simp [hcon])
    let T : State := ⟨Function.update s1.reg r ((g :: gs).headD Glyph.eos),
      Function.update s1.stk k (g :: gs).tail⟩
    have hT : T.reg r = g := by simp [T, s1, Function.update_apply]
    have hpush : Eval main (.push k r) T ⟨T.reg, Function.update T.stk k (T.reg r :: T.stk k)⟩ 1 :=
      Eval.push k r T
    have h3 : Eval main (.ite r .eos .skip (.push k r)) T
        ⟨T.reg, Function.update T.stk k (T.reg r :: T.stk k)⟩ 2 :=
      Eval.iteF (by rw [hT]; exact hg) hpush
    have h4 := Eval.seq h2 h3
    have hstate : (⟨T.reg, Function.update T.stk k (T.reg r :: T.stk k)⟩ : State)
        = ⟨Function.update s.reg r ((g :: gs).headD Glyph.eos),
            Function.update s.stk k (g :: gs)⟩ := by
      apply State.ext'
      · intro q; simp only [T, s1, Function.update_apply]
        by_cases hq : q = r
        · subst hq; simp
        · simp [hq]
      · intro q; simp only [T, s1, Function.update_apply]
        by_cases hq : q = k
        · subst hq; simp
        · simp [hq]
    rw [hstate] at h4
    have hc : 2 * zs + 6 = 1 + ((2 * zs + 3) + 2) := by ring_nf
    rw [hc]
    exact Eval.seq h1 h4

end SG
end Work.IntLib
