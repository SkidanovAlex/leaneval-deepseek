import Mathlib
import Submission.Work.IntLib.mulSDefs

/-!
# `mulSInitEv`: the initialisation phase `initRProg` of the schoolbook multiplier

`initRProg` lays down `α.length` zero bits (the initial remainder `ρ`) on `sR`, saving the bits of
`α` on the scratch stack `sW` and restoring `sA` afterwards:

* phase 1 (`consume sA mkA rL (push sW rL; push sR rZ)`) moves the bits of `α` from `sA` to `sW`,
  pushing one `false` glyph (the fixed content of register `rZ`) onto `sR` per bit;
* phase 2 (a `drain sW sA mkW rL`) moves them back onto `sA`.

The file is deliberately self-contained (it imports only the stable definitions module
`Submission.Work.IntLib.mulSDefs`, which brings the `Ev` toolkit): the two `Eval` inductions it
needs -- the two-push `consumeLoop` and the `drain` `consumeLoop` -- are kept here as private
lemmas, so that the theorem does not depend on any file whose owner is still editing it.
-/

set_option autoImplicit false

namespace Work.IntLib
namespace MulS

open HvdH

/-! ## The `Eval` inductions needed by `initRProg` -/

private theorem evOfEval {main : Cmd} {p : Cmd} {s s' : State} {n : ℕ} (h : Eval main p s s' n) :
    Ev main p s s' n := ⟨n, h, le_rfl⟩

/-- `consumeLoop` with the "move the glyph to `dst`" handler: linear cost, and no other stack
is touched. -/
private theorem drainEv {main : Cmd} {src dst : Stk} (hne : src ≠ dst) {T : Glyph} {r : Reg}
    {below : List Glyph} (ws : List Glyph) (rest : List Glyph) (s : State)
    (hsrc : s.stk src = ws ++ T :: below) (hdst : s.stk dst = rest)
    (hws : ∀ g ∈ ws, g ≠ T) (hr : s.reg r = .eos) :
    ∃ s' n, Eval main (consumeLoop src T r (.push dst r)) s s' n ∧
      n ≤ 5 * (ws.length + 1) + 1 ∧
      s'.stk src = T :: below ∧ s'.stk dst = ws.reverse ++ rest ∧
      (∀ k, k ≠ src → k ≠ dst → s'.stk k = s.stk k) ∧ s'.reg r = mkStop := by
  induction ws generalizing rest s with
  | nil =>
    simp only [List.nil_append] at hsrc
    have hpop : Ev main (.pop src r) s
        ⟨Function.update s.reg r T, Function.update s.stk src below⟩ 1 := by
      simpa [hsrc] using ev_pop main src r s
    have hpush : Ev main (.push src r)
        ⟨Function.update s.reg r T, Function.update s.stk src below⟩
        ⟨Function.update s.reg r T,
          Function.update (Function.update s.stk src below) src (T :: below)⟩ 1 := by
      have h := ev_push main src r (⟨Function.update s.reg r T,
        Function.update s.stk src below⟩ : State)
      simpa using h
    have hset : Ev main (.set r mkStop)
        ⟨Function.update s.reg r T,
          Function.update (Function.update s.stk src below) src (T :: below)⟩
        ⟨Function.update (Function.update s.reg r T) r mkStop,
          Function.update (Function.update s.stk src below) src (T :: below)⟩ 1 :=
      ev_set main r mkStop _
    have hite : Ev main
        (.ite r T (.seq (.push src r) (.set r mkStop)) (.seq (.push dst r) (.set r .eos)))
        ⟨Function.update s.reg r T, Function.update s.stk src below⟩
        ⟨Function.update (Function.update s.reg r T) r mkStop,
          Function.update (Function.update s.stk src below) src (T :: below)⟩ 3 := by
      refine Ev.iteT (by simp) ?_
      exact Ev.seq' hpush hset (by norm_num)
    have hbody : Ev main (consumeStep src T r (.push dst r)) s
        ⟨Function.update (Function.update s.reg r T) r mkStop,
          Function.update (Function.update s.stk src below) src (T :: below)⟩ 4 :=
      Ev.seq' hpop hite (by norm_num)
    have hloopF : Ev main (consumeLoop src T r (.push dst r))
        ⟨Function.update (Function.update s.reg r T) r mkStop,
          Function.update (Function.update s.stk src below) src (T :: below)⟩
        ⟨Function.update (Function.update s.reg r T) r mkStop,
          Function.update (Function.update s.stk src below) src (T :: below)⟩ 1 :=
      Ev.loopF (by simp)
    have hmain := Ev.loopT hr hbody hloopF
    obtain ⟨n, hev, hn⟩ := hmain
    exact ⟨(⟨Function.update (Function.update s.reg r T) r mkStop,
        Function.update (Function.update s.stk src below) src (T :: below)⟩ : State),
      n, hev, hn, by simp [Function.update_self],
      by simp [hdst, Function.update_of_ne (Ne.symm hne)],
      by intro k hk1 hk2; simp [Function.update_of_ne hk1, Function.update_of_ne hk2],
      by simp⟩
  | cons g gs ih =>
    simp only [List.cons_append] at hsrc
    have hg : g ≠ T := hws g (by simp)
    have hws' : ∀ x ∈ gs, x ≠ T := fun x hx => hws x (by simp [hx])
    have hpop : Ev main (.pop src r) s
        ⟨Function.update s.reg r g, Function.update s.stk src (gs ++ T :: below)⟩ 1 := by
      simpa [hsrc] using ev_pop main src r s
    have hpush : Ev main (.push dst r)
        ⟨Function.update s.reg r g, Function.update s.stk src (gs ++ T :: below)⟩
        ⟨Function.update s.reg r g,
          Function.update (Function.update s.stk src (gs ++ T :: below)) dst (g :: rest)⟩ 1 := by
      have h := ev_push main dst r (⟨Function.update s.reg r g,
        Function.update s.stk src (gs ++ T :: below)⟩ : State)
      simpa [Function.update_self, Function.update_of_ne (Ne.symm hne), hdst] using h
    have hset : Ev main (.set r .eos)
        ⟨Function.update s.reg r g,
          Function.update (Function.update s.stk src (gs ++ T :: below)) dst (g :: rest)⟩
        ⟨Function.update (Function.update s.reg r g) r .eos,
          Function.update (Function.update s.stk src (gs ++ T :: below)) dst (g :: rest)⟩ 1 :=
      ev_set main r .eos _
    have hite : Ev main
        (.ite r T (.seq (.push src r) (.set r mkStop)) (.seq (.push dst r) (.set r .eos)))
        ⟨Function.update s.reg r g, Function.update s.stk src (gs ++ T :: below)⟩
        ⟨Function.update (Function.update s.reg r g) r .eos,
          Function.update (Function.update s.stk src (gs ++ T :: below)) dst (g :: rest)⟩ 3 := by
      refine Ev.iteF ?_ ?_
      · simpa using hg
      · exact Ev.seq' hpush hset (by norm_num)
    have hbody : Ev main (consumeStep src T r (.push dst r)) s
        ⟨Function.update (Function.update s.reg r g) r .eos,
          Function.update (Function.update s.stk src (gs ++ T :: below)) dst (g :: rest)⟩ 4 :=
      Ev.seq' hpop hite (by norm_num)
    obtain ⟨s', n', hev', hn', hsrc', hdst', hfr', hr'⟩ :=
      ih (g :: rest)
        ⟨Function.update (Function.update s.reg r g) r .eos,
          Function.update (Function.update s.stk src (gs ++ T :: below)) dst (g :: rest)⟩
        (by simp [Function.update_self, Function.update_of_ne hne])
        (by simp [Function.update_self, Function.update_of_ne (Ne.symm hne)])
        hws' (by simp)
    obtain ⟨n, hev, hn⟩ := Ev.loopT hr hbody (evOfEval hev')
    refine ⟨s', n, hev, ?_, hsrc', ?_, ?_, hr'⟩
    · simp only [List.length_cons]; omega
    · rw [hdst', List.reverse_cons]
      simp [List.append_assoc]
    · intro k hk1 hk2
      rw [hfr' k hk1 hk2]
      simp [Function.update_of_ne hk1, Function.update_of_ne hk2]

/-- `drain` (with the initialising `set`): move every glyph above the marker `T` on `src` to `dst`,
reversing the order. -/
private theorem drainEv' {main : Cmd} {src dst : Stk} (hne : src ≠ dst) {T : Glyph} {r : Reg}
    {below : List Glyph} (ws : List Glyph) (rest : List Glyph) (s : State)
    (hsrc : s.stk src = ws ++ T :: below) (hdst : s.stk dst = rest)
    (hws : ∀ g ∈ ws, g ≠ T) :
    ∃ s' n, Eval main (drain src dst T r) s s' n ∧ n ≤ 5 * (ws.length + 1) + 2 ∧
      s'.stk src = T :: below ∧ s'.stk dst = ws.reverse ++ rest ∧
      (∀ k, k ≠ src → k ≠ dst → s'.stk k = s.stk k) := by
  have hset : Ev main (.set r .eos) s ⟨Function.update s.reg r .eos, s.stk⟩ 1 :=
    ev_set main r .eos s
  obtain ⟨s', n, hev, hn, h1, h2, h3, _⟩ :=
    drainEv (r := r) hne ws rest (⟨Function.update s.reg r .eos, s.stk⟩ : State) hsrc hdst hws
      (by simp)
  obtain ⟨n2, hev2, hn2⟩ := Ev.seq' hset (evOfEval hev)
    (C := 5 * (ws.length + 1) + 2) (by omega)
  refine ⟨s', n2, hev2, hn2, h1, h2, ?_⟩
  intro k hk1 hk2
  rw [h3 k hk1 hk2]
private theorem consumeLoop2Ev {main : Cmd} {src dst1 dst2 : Stk} {T g2 : Glyph} {r r2 : Reg}
    {below : List Glyph} (ws c1 c2 : List Glyph) (s : State)
    (hne1 : src ≠ dst1) (hne2 : src ≠ dst2) (hne12 : dst1 ≠ dst2) (hrne : r ≠ r2)
    (hsrc : s.stk src = ws ++ T :: below) (hc1 : s.stk dst1 = c1) (hc2 : s.stk dst2 = c2)
    (hws : ∀ x ∈ ws, x ≠ T) (hr : s.reg r = .eos) (hr2 : s.reg r2 = g2) :
    ∃ s' n, Eval main (consumeLoop src T r (.seq (.push dst1 r) (.push dst2 r2))) s s' n ∧
      n ≤ 6 * (ws.length + 1) ∧
      s'.stk src = T :: below ∧ s'.stk dst1 = ws.reverse ++ c1 ∧
      s'.stk dst2 = List.replicate ws.length g2 ++ c2 ∧
      (∀ k, k ≠ src → k ≠ dst1 → k ≠ dst2 → s'.stk k = s.stk k) ∧
      s'.reg r = mkStop := by
  induction ws generalizing c1 c2 s with
  | nil =>
    simp only [List.nil_append] at hsrc
    have hpop : Ev main (.pop src r) s
        ⟨Function.update s.reg r T, Function.update s.stk src below⟩ 1 := by
      simpa [hsrc] using ev_pop main src r s
    have hpush : Ev main (.push src r)
        ⟨Function.update s.reg r T, Function.update s.stk src below⟩
        ⟨Function.update s.reg r T,
          Function.update (Function.update s.stk src below) src (T :: below)⟩ 1 := by
      have h := ev_push main src r (⟨Function.update s.reg r T,
        Function.update s.stk src below⟩ : State)
      simpa using h
    have hset : Ev main (.set r mkStop)
        ⟨Function.update s.reg r T,
          Function.update (Function.update s.stk src below) src (T :: below)⟩
        ⟨Function.update (Function.update s.reg r T) r mkStop,
          Function.update (Function.update s.stk src below) src (T :: below)⟩ 1 :=
      ev_set main r mkStop _
    have hite : Ev main
        (.ite r T (.seq (.push src r) (.set r mkStop))
          (.seq (.seq (.push dst1 r) (.push dst2 r2)) (.set r .eos)))
        ⟨Function.update s.reg r T, Function.update s.stk src below⟩
        ⟨Function.update (Function.update s.reg r T) r mkStop,
          Function.update (Function.update s.stk src below) src (T :: below)⟩ 3 := by
      refine Ev.iteT (by simp) ?_
      exact Ev.seq' hpush hset (by norm_num)
    have hbody : Ev main (consumeStep src T r (.seq (.push dst1 r) (.push dst2 r2))) s
        ⟨Function.update (Function.update s.reg r T) r mkStop,
          Function.update (Function.update s.stk src below) src (T :: below)⟩ 4 :=
      Ev.seq' hpop hite (by norm_num)
    have hloopF : Ev main (consumeLoop src T r (.seq (.push dst1 r) (.push dst2 r2)))
        ⟨Function.update (Function.update s.reg r T) r mkStop,
          Function.update (Function.update s.stk src below) src (T :: below)⟩
        ⟨Function.update (Function.update s.reg r T) r mkStop,
          Function.update (Function.update s.stk src below) src (T :: below)⟩ 1 :=
      Ev.loopF (by simp)
    obtain ⟨n, hev, hn⟩ := Ev.loopT hr hbody hloopF
    refine ⟨_, n, hev, by omega, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Function.update_self]
    · simp [hc1, Function.update_of_ne (Ne.symm hne1)]
    · simp [hc2, Function.update_of_ne (Ne.symm hne2)]
    · intro k hk1 hk2 hk3
      simp [Function.update_of_ne hk1]
    · simp [Function.update_self]
  | cons g gs ih =>
    simp only [List.cons_append] at hsrc
    have hg : g ≠ T := hws g (by simp)
    have hws' : ∀ x ∈ gs, x ≠ T := fun x hx => hws x (by simp [hx])
    have hpop : Ev main (.pop src r) s
        ⟨Function.update s.reg r g, Function.update s.stk src (gs ++ T :: below)⟩ 1 := by
      simpa [hsrc] using ev_pop main src r s
    have hunit : Ev main (.push dst1 r)
        ⟨Function.update s.reg r g, Function.update s.stk src (gs ++ T :: below)⟩
        ⟨Function.update s.reg r g,
          Function.update (Function.update s.stk src (gs ++ T :: below)) dst1 (g :: c1)⟩ 1 := by
      have h := ev_push main dst1 r (⟨Function.update s.reg r g,
        Function.update s.stk src (gs ++ T :: below)⟩ : State)
      simpa [Function.update_self, hc1, Function.update_of_ne (Ne.symm hne1)] using h
    have hreg1 : Function.update s.reg r g r2 = g2 := by
      rw [Function.update_of_ne (Ne.symm hrne)]; exact hr2
    have hpush2 : Ev main (.push dst2 r2)
        ⟨Function.update s.reg r g,
          Function.update (Function.update s.stk src (gs ++ T :: below)) dst1 (g :: c1)⟩
        ⟨Function.update s.reg r g,
          Function.update
            (Function.update (Function.update s.stk src (gs ++ T :: below)) dst1 (g :: c1))
            dst2 (g2 :: c2)⟩ 1 := by
      have h := ev_push main dst2 r2 (⟨Function.update s.reg r g,
        Function.update (Function.update s.stk src (gs ++ T :: below)) dst1 (g :: c1)⟩ : State)
      simpa [hreg1, hc2, Function.update_of_ne (Ne.symm hne12),
        Function.update_of_ne (Ne.symm hne2)] using h
    have hhand : Ev main (.seq (.push dst1 r) (.push dst2 r2))
        ⟨Function.update s.reg r g, Function.update s.stk src (gs ++ T :: below)⟩
        ⟨Function.update s.reg r g,
          Function.update
            (Function.update (Function.update s.stk src (gs ++ T :: below)) dst1 (g :: c1))
            dst2 (g2 :: c2)⟩ 2 := Ev.seq' hunit hpush2 (by norm_num)
    have hset : Ev main (.set r .eos)
        ⟨Function.update s.reg r g,
          Function.update
            (Function.update (Function.update s.stk src (gs ++ T :: below)) dst1 (g :: c1))
            dst2 (g2 :: c2)⟩
        ⟨Function.update (Function.update s.reg r g) r .eos,
          Function.update
            (Function.update (Function.update s.stk src (gs ++ T :: below)) dst1 (g :: c1))
            dst2 (g2 :: c2)⟩ 1 := ev_set main r .eos _
    have hite : Ev main
        (.ite r T (.seq (.push src r) (.set r mkStop))
          (.seq (.seq (.push dst1 r) (.push dst2 r2)) (.set r .eos)))
        ⟨Function.update s.reg r g, Function.update s.stk src (gs ++ T :: below)⟩
        ⟨Function.update (Function.update s.reg r g) r .eos,
          Function.update
            (Function.update (Function.update s.stk src (gs ++ T :: below)) dst1 (g :: c1))
            dst2 (g2 :: c2)⟩ 4 :=
      Ev.iteF (by simpa using hg)
        (show Ev main _ _ _ 3 from Ev.seq' hhand hset (by norm_num))
    have hbody : Ev main (consumeStep src T r (.seq (.push dst1 r) (.push dst2 r2))) s
        ⟨Function.update (Function.update s.reg r g) r .eos,
          Function.update
            (Function.update (Function.update s.stk src (gs ++ T :: below)) dst1 (g :: c1))
            dst2 (g2 :: c2)⟩ 5 := Ev.seq' hpop hite (by norm_num)
    let S3 : State := ⟨Function.update (Function.update s.reg r g) r .eos,
      Function.update
        (Function.update (Function.update s.stk src (gs ++ T :: below)) dst1 (g :: c1))
        dst2 (g2 :: c2)⟩
    have hsrc3 : S3.stk src = gs ++ T :: below := by
      simp [S3, Function.update_self, Function.update_of_ne hne1, Function.update_of_ne hne2]
    have hc13 : S3.stk dst1 = g :: c1 := by
      simp [S3, Function.update_self, Function.update_of_ne hne12]
    have hc23 : S3.stk dst2 = g2 :: c2 := by simp [S3]
    have hr3 : S3.reg r = .eos := by simp [S3]
    have hr23 : S3.reg r2 = g2 := by
      simp [S3, Function.update_of_ne (Ne.symm hrne), hr2]
    obtain ⟨s', n', hev', hn', hsrc', hdst1', hdst2', hfr', hr'⟩ :=
      ih (g :: c1) (g2 :: c2) S3 hsrc3 hc13 hc23 hws' hr3 hr23
    obtain ⟨n, hev, hn⟩ :=
      Ev.loopT hr hbody (show Ev main (consumeLoop src T r (.seq (.push dst1 r) (.push dst2 r2)))
        S3 s' (6 * (gs.length + 1)) from ⟨n', hev', hn'⟩)
    refine ⟨s', n, hev, ?_, hsrc', ?_, ?_, ?_, hr'⟩
    · simp only [List.length_cons]; omega
    · rw [hdst1', List.reverse_cons]; simp [List.append_assoc]
    · rw [hdst2', List.length_cons, List.replicate_succ']; simp [List.append_assoc]
    · intro k hk1 hk2 hk3
      rw [hfr' k hk1 hk2 hk3]
      simp [S3, Function.update_of_ne hk1, Function.update_of_ne hk2, Function.update_of_ne hk3]

/-! ## `initRProg` phase 1 as a `consumeLoop` -/

private theorem initLoopEv {main : Cmd} {s : State} {α : List Bool} {below bW bR : List Glyph}
    (hA : s.stk sA = α.map Glyph.bit ++ [mkA] ++ below)
    (hW : s.stk sW = bW) (hR : s.stk sR = bR)
    (hZ : s.reg rZ = Glyph.bit false) (hL : s.reg rL = .eos) :
    ∃ s' n, Eval main (consumeLoop sA mkA rL (.seq (.push sW rL) (.push sR rZ))) s s' n ∧
      n ≤ 6 * (α.length + 1) ∧
      s'.stk sA = [mkA] ++ below ∧
      s'.stk sW = α.reverse.map Glyph.bit ++ bW ∧
      s'.stk sR = (List.replicate α.length false).map Glyph.bit ++ bR ∧
      (∀ k : Stk, k ≠ sA → k ≠ sR → k ≠ sW → s'.stk k = s.stk k) ∧
      s'.reg rL = mkStop := by
  have hws : ∀ x ∈ α.map Glyph.bit, x ≠ mkA := by
    intro x hx
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx
    simp
  have hA' : s.stk sA = α.map Glyph.bit ++ mkA :: below := by
    rw [hA, List.append_assoc, List.singleton_append]
  obtain ⟨s', n, hev, hn, hsrc', hW', hR', hframe, hL'⟩ :=
    consumeLoop2Ev (main := main) (src := sA) (dst1 := sW) (dst2 := sR)
      (T := mkA) (g2 := Glyph.bit false) (r := rL) (r2 := rZ)
      (below := below) (α.map Glyph.bit) bW bR s
      (by decide) (by decide) (by decide) (by decide) hA' hW hR hws hL hZ
  refine ⟨s', n, hev, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [List.length_map] using hn
  · rw [hsrc', List.singleton_append]
  · rw [hW', List.map_reverse]
  · rw [hR', List.length_map, ← List.map_replicate]
  · intro k hk1 hk2 hk3
    exact hframe k hk1 hk3 hk2
  · exact hL'

end MulS

open HvdH
open MulS

/-- `initRProg`: drain the bits of `α` off `sA` onto `sW` (pushing one `false` onto `sR` per bit),
then drain `sW` back onto `sA`; result: `sR` holds `α.length` false bits above its old content,
and `sA`, `sW` are restored. -/
theorem mulSInitEv {main : Cmd} {s : State} {α : List Bool}
    {belowA belowW bR : List Glyph}
    (hA : s.stk sA = α.map Glyph.bit ++ [mkA] ++ belowA)
    (hW : s.stk sW = [mkW] ++ belowW) (hR : s.stk sR = bR)
    (hrZ : s.reg rZ = Glyph.bit false) :
    ∃ s' n, Eval main initRProg s s' n ∧ n ≤ 14 * (α.length + 1) + 14 ∧
      s'.stk sA = α.map Glyph.bit ++ [mkA] ++ belowA ∧
      s'.stk sR = (List.replicate α.length false).map Glyph.bit ++ bR ∧
      s'.stk sW = [mkW] ++ belowW ∧
      (∀ k : Stk, k ≠ sA → k ≠ sR → k ≠ sW → s'.stk k = s.stk k) := by
  have hZ0 : (Function.update s.reg rL .eos) rZ = Glyph.bit false := by
    rw [Function.update_of_ne (by decide : (rZ : Reg) ≠ rL)]
    exact hrZ
  -- ## Phase 1: move the bits of `α` from `sA` to `sW`, one `false` onto `sR` per bit
  obtain ⟨s1, n1, h1, hn1, hA1, hW1, hR1, hfr1, _hrL1⟩ :=
    initLoopEv (main := main)
      (s := (⟨Function.update s.reg rL .eos, s.stk⟩ : State))
      (α := α) (below := belowA) (bW := [mkW] ++ belowW) (bR := bR)
      hA hW hR hZ0 (by simp)
  have hstep1 : Ev main (consume sA mkA rL (.seq (.push sW rL) (.push sR rZ))) s s1
      (6 * (α.length + 1) + 1) :=
    Ev.seq' (ev_set main rL .eos s) (evOfEval h1) (C := 6 * (α.length + 1) + 1) (by omega)
  -- ## Phase 2: drain `sW` back onto `sA`
  have hW1' : s1.stk sW = α.reverse.map Glyph.bit ++ mkW :: belowW := by
    rw [hW1, List.singleton_append]
  obtain ⟨s2, n2, h2, hn2, hsrc2, hdst2, hfr2⟩ :=
    drainEv' (main := main) (src := sW) (dst := sA) (T := mkW) (r := rL) (below := belowW)
      (by decide : sW ≠ sA) (α.reverse.map Glyph.bit) ([mkA] ++ belowA) s1 hW1' hA1 (by
        intro g hg
        obtain ⟨b, _, rfl⟩ := List.mem_map.mp hg
        exact fun h => by cases h)
  have hstep2 : Ev main (drain sW sA mkW rL) s1 s2 (5 * (α.length + 1) + 2) :=
    Ev.mono (evOfEval h2) (by simpa only [List.length_map, List.length_reverse] using hn2)
  -- ## Compose
  have hfull : Ev main initRProg s s2 (14 * (α.length + 1) + 14) := by
    change Ev main
      (.seq (consume sA mkA rL (.seq (.push sW rL) (.push sR rZ)))
            (consume sW mkW rL (.push sA rL))) s s2 (14 * (α.length + 1) + 14)
    exact Ev.seq' hstep1 hstep2 (C := 14 * (α.length + 1) + 14) (by omega)
  obtain ⟨n, hev, hnle⟩ := hfull
  refine ⟨s2, n, hev, hnle, ?_, ?_, ?_, ?_⟩
  · rw [hdst2, List.map_reverse, List.reverse_reverse, List.append_assoc]
  · rw [hfr2 sR (by decide) (by decide)]
    exact hR1
  · simpa only [List.singleton_append] using hsrc2
  · intro k hk1 hk2 hk3
    rw [hfr2 k hk3 hk1, hfr1 k hk1 hk2 hk3]

end Work.IntLib
