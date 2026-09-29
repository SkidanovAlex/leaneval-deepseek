import Mathlib
import Submission.Work.Layout.MergeDefs
import Submission.Work.Layout.dupInt_ev
import Submission.Work.Layout.mvVal_ev_full
import Submission.Work.Layout.Move

set_option autoImplicit false

namespace Work.Layout

open HvdH Work.Layout

private theorem mrgUpd_encs_single (v : Val) : encs [v] = v.enc := by simp [encs]

private theorem mrgUpd_consEnc (k : ℕ) (v' : Val) (A : List Glyph) :
    (Val.cons (Val.int (k : ℤ)) v').enc ++ A =
      Glyph.cons :: ((Val.int (k : ℤ)).enc ++ (v'.enc ++ A)) := by
  simp only [Val.enc, List.cons_append, List.append_assoc]

/-- `pop` on a stack whose top glyph is `Glyph.cons`. -/
private theorem mrgUpd_pop_cons_ev {main : Cmd} {S : Stk} {r : Reg} {g : Reg → Glyph}
    {X : Stk → List Glyph} {A' : List Glyph} (hX : X S = Glyph.cons :: A') :
    ∃ s' n, Ev main (.pop S r) ⟨g, X⟩ s' n ∧ n ≤ 1 ∧ s'.stk S = A' ∧
      (∀ k', k' ≠ S → s'.stk k' = X k') ∧ s'.reg r = Glyph.cons := by
  have h1 : Ev main (.pop S r) ⟨g, X⟩
      ⟨Function.update g r Glyph.cons, Function.update X S A'⟩ 1 := by
    have hp := ev_pop' main S r g X
    rw [hX] at hp
    exact hp
  exact ⟨_, _, h1, le_rfl, Function.update_self S A' X,
    (fun k' hk => Function.update_of_ne hk A' X), Function.update_self r Glyph.cons g⟩

/-- `peek` on a stack whose top glyph is `Glyph.cons`: no stack changes, the register reads `cons`. -/
private theorem mrgUpd_peek_cons_ev {main : Cmd} {S : Stk} {r : Reg} {g : Reg → Glyph}
    {X : Stk → List Glyph} {A' : List Glyph} (hX : X S = Glyph.cons :: A') :
    ∃ s' n, Ev main (.peek S r) ⟨g, X⟩ s' n ∧ n ≤ 1 ∧ s'.stk S = X S ∧
      (∀ k', s'.stk k' = X k') ∧ s'.reg r = Glyph.cons := by
  have h1 : Ev main (.peek S r) ⟨g, X⟩ ⟨Function.update g r Glyph.cons, X⟩ 1 := by
    have hp := ev_peek' main S r g X
    rw [hX] at hp
    exact hp
  exact ⟨_, _, h1, le_rfl, rfl, (fun k' => rfl), Function.update_self r Glyph.cons g⟩

/-- `Sk.pushSize`: the cost form of the `cons` branch of `Sk.updSize`. -/
private theorem mrgUpd_pushSize {main pSize : Cmd} {KSz : ℕ}
    (hSz : ∀ main : Cmd, UnOp main pSize (fun _ => True) (fun a => (a.natAbs.size : ℤ))
      (fun a => KSz * isz a))
    {S SA t d : Stk} (hSSA : S ≠ SA) (hS0 : S ≠ 0) (hSt : S ≠ t) (hSd : S ≠ d)
    (hSA0 : SA ≠ 0) (hSAt : SA ≠ t) (hSAd : SA ≠ d)
    (h0t : (0 : Stk) ≠ t) (h0d : (0 : Stk) ≠ d) (htd : t ≠ d)
    {g : Reg → Glyph} {X : Stk → List Glyph} {k : ℕ} {v' : Val} {A Sc : List Glyph}
    (hS : X S = (Val.cons (Val.int (k : ℤ)) v').enc ++ A) (hSA : X SA = Sc) :
    ∃ s' n, Ev main (Sk.pushSize pSize S SA t d) ⟨g, X⟩ s' n ∧
      n ≤ 40 * (isz (k : ℤ) + 1) + KSz * isz (k : ℤ) + 16 * (isz (k.size : ℤ) + 1) + 8 ∧
      s'.stk S = X S ∧ s'.stk SA = (Val.int (k.size : ℤ)).enc ++ Sc ∧
      s'.stk 0 = X 0 ∧ s'.stk t = X t ∧ s'.stk d = X d ∧
      (∀ k' : Stk, k' ≠ S → k' ≠ SA → k' ≠ 0 → k' ≠ t → k' ≠ d → s'.stk k' = X k') := by
  have hSdec : X S = Glyph.cons :: ((Val.int (k : ℤ)).enc ++ (v'.enc ++ A)) := by
    rw [hS, mrgUpd_consEnc]
  -- 1. `pop S rI`
  obtain ⟨s1, n1, e1, hn1, h1S, h1fr, h1r⟩ :=
    mrgUpd_pop_cons_ev (main := main) (S := S) (r := Sk.rI) (g := g) (X := X)
      (A' := (Val.int (k : ℤ)).enc ++ (v'.enc ++ A)) hSdec
  -- 2. `dupInt S 0 t d`
  obtain ⟨s2, n2, e2, hn2, h2S, h20, h2t, h2d, h2fr⟩ :=
    dupInt_ev (main := main) (S := S) (B := 0) (T := t) (d := d)
      hS0 hSt hSd h0t h0d htd (g := s1.reg) (X := s1.stk) (z := (k : ℤ))
      (A := v'.enc ++ A) h1S
  -- 3. `pSize`
  have h20' : s2.stk 0 = encs [Val.int (k : ℤ)] ++ X 0 := by
    rw [h20, mrgUpd_encs_single, h1fr 0 hS0.symm]
  obtain ⟨out, s3, n3, hpost3, e3, hn3, h30, h3fr⟩ :=
    (hSz main) [Val.int (k : ℤ)] ⟨(k : ℤ), [], rfl, trivial⟩ s2 (X 0) h20'
  have h3ev : Ev main pSize s2 s3 (KSz * isz (k : ℤ)) := ⟨n3, e3, hn3⟩
  have houtv : out = [Val.int (((k : ℤ).natAbs.size : ℤ))] := by
    obtain ⟨a, rest, hv, hoo⟩ := hpost3
    have hrest : rest = [] := ((List.cons.inj hv).2).symm
    have ha : a = (k : ℤ) := (Val.int.inj (List.cons.inj hv).1).symm
    rw [hoo, ha, hrest]
  have h30' : s3.stk 0 = (Val.int (k.size : ℤ)).enc ++ X 0 := by
    rw [h30, houtv, mrgUpd_encs_single]
    simp
  -- 4. `mvVal 0 SA t d`
  have h3SA : s3.stk SA = Sc := by
    rw [h3fr SA hSA0, h2fr SA hSSA.symm hSA0 hSAt hSAd, h1fr SA hSSA.symm, hSA]
  obtain ⟨s4, n4, e4, hn4, h40, h4SA, h4t, h4d, h4fr⟩ :=
    mvVal_ev_full (main := main) (a := 0) (b := SA) (c := t) (d := d)
      hSA0.symm h0t h0d hSAt hSAd htd (g := s3.reg) (v := Val.int (k.size : ℤ))
      (A := X 0) (B := Sc) h30' h3SA
  -- 5. `pushConst S Glyph.cons`
  obtain ⟨s5, n5, e5, hn5, h5S, h5fr, -, -⟩ :=
    pushConst_ev (main := main) (k := S) (cst := Glyph.cons) (g := s4.reg) (X := s4.stk)
  have h4S : s4.stk S = (Val.int (k : ℤ)).enc ++ (v'.enc ++ A) := by
    rw [h4fr S hS0 hSSA hSt hSd, h3fr S hS0, h2S, h1S]
  have h5S' : s5.stk S = X S := by
    rw [h5S, h4S]
    exact hSdec.symm
  -- cost bookkeeping
  have hn2' : n2 ≤ 40 * (isz (k : ℤ) + 1) := by
    rw [vsz_int] at hn2; exact hn2
  have hn4' : n4 ≤ 16 * (isz (k.size : ℤ) + 1) := by
    rw [vsz_int] at hn4; exact hn4
  have htot : Ev main (Sk.pushSize pSize S SA t d) ⟨g, X⟩ s5
      (1 + (40 * (isz (k : ℤ) + 1) +
        (KSz * isz (k : ℤ) + (16 * (isz (k.size : ℤ) + 1) + 2)))) := by
    unfold Sk.pushSize
    exact Ev.seq (e1.mono hn1)
      (Ev.seq (e2.mono hn2') (Ev.seq h3ev (Ev.seq (e4.mono hn4') (e5.mono hn5))))
  refine ⟨s5, _, htot, ?_, h5S', ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · rw [h5fr SA hSSA.symm, h4SA]
  · rw [h5fr 0 hS0.symm, h40]
  · rw [h5fr t hSt.symm, h4t, h3fr t h0t.symm, h2t, h1fr t hSt.symm]
  · rw [h5fr d hSd.symm, h4d, h3fr d h0d.symm, h2d, h1fr d hSd.symm]
  · intro k' hkS hkSA hk0 hkt hkd
    rw [h5fr k' hkS, h4fr k' hk0 hkSA hkt hkd, h3fr k' hk0, h2fr k' hkS hk0 hkt hkd,
      h1fr k' hkS]

theorem mrgUpdSize {main pSize : Cmd} {KSz : ℕ} (hSz : ∀ main : Cmd, UnOp main pSize (fun _ => True) (fun a => (a.natAbs.size : ℤ)) (fun a => KSz * isz a)) {S SA t d : Stk} (hSSA : S ≠ SA) (hS0 : S ≠ 0) (hSt : S ≠ t) (hSd : S ≠ d) (hSA0 : SA ≠ 0) (hSAt : SA ≠ t) (hSAd : SA ≠ d) (h0t : (0 : Stk) ≠ t) (h0d : (0 : Stk) ≠ d) (htd : t ≠ d) {g : Reg → Glyph} {X : Stk → List Glyph} {k : ℕ} {v' : Val} {A Sc : List Glyph} (hS : X S = (Val.cons (Val.int (k : ℤ)) v').enc ++ A) (hSA : X SA = Sc) : ∃ s' n, Ev main (Sk.updSize pSize S SA t d) ⟨g, X⟩ s' n ∧ n ≤ 40 * (isz (k : ℤ) + 1) + KSz * isz (k : ℤ) + 16 * (isz (k.size : ℤ) + 1) + 12 ∧ s'.stk S = X S ∧ s'.stk SA = (Val.int (k.size : ℤ)).enc ++ Sc ∧ s'.stk 0 = X 0 ∧ s'.stk t = X t ∧ s'.stk d = X d ∧ (∀ k' : Stk, k' ≠ S → k' ≠ SA → k' ≠ 0 → k' ≠ t → k' ≠ d → s'.stk k' = X k') := by
  have hSdec : X S = Glyph.cons :: ((Val.int (k : ℤ)).enc ++ (v'.enc ++ A)) := by
    rw [hS, mrgUpd_consEnc]
  -- `peek S rH`
  obtain ⟨s1, n1, e1, hn1, h1S, h1fr, h1r⟩ :=
    mrgUpd_peek_cons_ev (main := main) (S := S) (r := Sk.rH) (g := g) (X := X)
      (A' := (Val.int (k : ℤ)).enc ++ (v'.enc ++ A)) hSdec
  -- the `cons` branch: `pushSize`
  have h1SA : s1.stk SA = Sc := by rw [h1fr SA, hSA]
  obtain ⟨s2, n2, e2, hn2, h2S, h2SA, h20, h2t, h2d, h2fr⟩ :=
    mrgUpd_pushSize (main := main) (pSize := pSize) (KSz := KSz) hSz
      hSSA hS0 hSt hSd hSA0 hSAt hSAd h0t h0d htd (g := s1.reg) (X := s1.stk)
      (by rw [h1S]; exact hS) h1SA
  -- the `ite` on `rH`
  have e3 : Ev main (.ite Sk.rH Glyph.cons (Sk.pushSize pSize S SA t d) .skip) s1 s2 (n2 + 1) :=
    Ev.iteT h1r e2
  have hmain : Ev main (Sk.updSize pSize S SA t d) ⟨g, X⟩ s2 (n2 + 2) := by
    unfold Sk.updSize
    exact Ev.seq' (e1.mono hn1) e3 (by omega)
  refine ⟨s2, n2 + 2, hmain, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h2S, h1S]
  · exact h2SA
  · rw [h20, h1fr 0]
  · rw [h2t, h1fr t]
  · rw [h2d, h1fr d]
  · intro k' hkS hkSA hk0 hkt hkd
    rw [h2fr k' hkS hkSA hk0 hkt hkd, h1fr k']

end Work.Layout
