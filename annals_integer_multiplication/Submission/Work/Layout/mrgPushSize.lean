import Mathlib
import Submission.Work.Layout.MergeDefs
import Submission.Work.Layout.dupInt_ev
import Submission.Work.Layout.mvVal_ev_full
import Submission.Work.Layout.Move

set_option maxHeartbeats 2000000

/-!
# `pushSize`

`Sk.pushSize pSize S SA t d` pushes the key size of the record at the top of `S` onto `SA`
(the record itself is left intact).  This file is self-contained: the proof uses only the raw
`Eval`/`Ev` toolkit of `Base`/`Move`, the `dupInt` word and the full `mvVal` word.

Program: `pop S rI` (drop the `cons` of the record), `dupInt S 0 t d` (copy the key `int k` of
the record onto stack `0`), `pSize` (replace it by `int k.size`), `mvVal 0 SA t d` (move it onto
`SA`) and `pushConst S Glyph.cons` (restore the leading `cons` on `S`).
-/

namespace Work.Layout

open HvdH Work.Layout.Sk

private theorem encs_single (v : Val) : encs [v] = v.enc := by simp [encs]

private theorem enc_record_append' (k : ℕ) (v' : Val) (A : List Glyph) :
    (Val.cons (Val.int (k : ℤ)) v').enc ++ A =
      Glyph.cons :: ((Val.int (k : ℤ)).enc ++ (v'.enc ++ A)) := by
  simp only [Val.enc, List.cons_append, List.append_assoc]

theorem mrgPushSize {main pSize : Cmd} {KSz : ℕ} (hSz : ∀ main : Cmd, UnOp main pSize (fun _ => True) (fun a => (a.natAbs.size : ℤ)) (fun a => KSz * isz a)) {S SA t d : Stk} (hSSA : S ≠ SA) (hS0 : S ≠ 0) (hSt : S ≠ t) (hSd : S ≠ d) (hSA0 : SA ≠ 0) (hSAt : SA ≠ t) (hSAd : SA ≠ d) (h0t : (0 : Stk) ≠ t) (h0d : (0 : Stk) ≠ d) (htd : t ≠ d) {g : Reg → Glyph} {X : Stk → List Glyph} {k : ℕ} {v' : Val} {A Sc : List Glyph} (hS : X S = (Val.cons (Val.int (k : ℤ)) v').enc ++ A) (hSA : X SA = Sc) : ∃ s' n, Ev main (Sk.pushSize pSize S SA t d) ⟨g, X⟩ s' n ∧ n ≤ 40 * (isz (k : ℤ) + 1) + KSz * isz (k : ℤ) + 16 * (isz (k.size : ℤ) + 1) + 8 ∧ s'.stk S = X S ∧ s'.stk SA = (Val.int (k.size : ℤ)).enc ++ Sc ∧ s'.stk 0 = X 0 ∧ s'.stk t = X t ∧ s'.stk d = X d ∧ (∀ k' : Stk, k' ≠ S → k' ≠ SA → k' ≠ 0 → k' ≠ t → k' ≠ d → s'.stk k' = X k') := by
  have hSdec : X S = Glyph.cons :: ((Val.int (k : ℤ)).enc ++ (v'.enc ++ A)) := by
    rw [hS, enc_record_append']
  -- pop S rI
  let s1 : State := ⟨Function.update g rI Glyph.cons,
    Function.update X S ((Val.int (k : ℤ)).enc ++ (v'.enc ++ A))⟩
  have e1 : Ev main (.pop S rI) ⟨g, X⟩ s1 1 := by
    have hp := ev_pop' main S rI g X
    rw [hSdec] at hp
    exact hp
  have hs1 : s1.stk S = (Val.int (k : ℤ)).enc ++ (v'.enc ++ A) := by
    show (Function.update X S ((Val.int (k : ℤ)).enc ++ (v'.enc ++ A))) S = _
    rw [Function.update_self]
  have hs10 : s1.stk 0 = X 0 := by
    show (Function.update X S ((Val.int (k : ℤ)).enc ++ (v'.enc ++ A))) 0 = X 0
    rw [Function.update_of_ne hS0.symm]
  -- dupInt S 0 t d: copy the key of the record onto stack 0
  obtain ⟨s2, n2, e2, hn2, hs2S, hs20, hs2t, hs2d, hfr2⟩ :=
    dupInt_ev (main := main) (S := S) (B := 0) (T := t) (d := d)
      hS0 hSt hSd h0t h0d htd (z := (k : ℤ)) (A := v'.enc ++ A) hs1
  -- pSize: replace `int k` by `int k.size`
  obtain ⟨out, s3, n3, hpost3, e3, hn3, hs3stk0, hfr3⟩ :=
    (hSz main) [Val.int (k : ℤ)] ⟨(k : ℤ), [], rfl, trivial⟩ s2 (X 0)
      (by rw [hs20, hs10, encs_single])
  have e3' : Ev main pSize s2 s3 n3 := ⟨n3, e3, le_rfl⟩
  have hs3S' : s3.stk S = (Val.int (k : ℤ)).enc ++ (v'.enc ++ A) := by
    rw [hfr3 S hS0, hs2S, hs1]
  have hs1SA : s1.stk SA = Sc := by
    show (Function.update X S ((Val.int (k : ℤ)).enc ++ (v'.enc ++ A))) SA = Sc
    rw [Function.update_of_ne hSSA.symm]
    exact hSA
  have hs3SA : s3.stk SA = Sc := by
    rw [hfr3 SA hSA0, hfr2 SA hSSA.symm hSA0 hSAt hSAd]
    exact hs1SA
  have houtv : out = [Val.int (((k : ℤ).natAbs.size : ℤ))] := by
    obtain ⟨a, rest, hv, hoo⟩ := hpost3
    have hrest : rest = [] := (List.cons.inj hv).2.symm
    have ha : a = (k : ℤ) := (Val.int.inj (List.cons.inj hv).1).symm
    rw [hoo, ha, hrest]
  have hs3stk : s3.stk 0 = (Val.int (k.size : ℤ)).enc ++ X 0 := by
    rw [hs3stk0, houtv, encs_single]; rfl
  -- mvVal 0 SA t d: move the computed size onto `SA`
  obtain ⟨s4, n4, e4, hn4, hs40, hs4SA, hs4t, hs4d, hfr4⟩ :=
    mvVal_ev_full (main := main) (a := 0) (b := SA) (c := t) (d := d)
      hSA0.symm h0t h0d hSAt hSAd htd (v := Val.int (k.size : ℤ)) (A := X 0) (B := Sc)
      hs3stk hs3SA
  -- pushConst S cons: restore the leading `cons` of the record on `S`
  obtain ⟨s5, n5, e5, hn5, hs5S, hfr5, -, -⟩ :=
    pushConst_ev (main := main) (k := S) (cst := Glyph.cons) (g := s4.reg) (X := s4.stk)
  have hs4S : s4.stk S = (Val.int (k : ℤ)).enc ++ (v'.enc ++ A) := by
    rw [hfr4 S hS0 hSSA hSt hSd]
    exact hs3S'
  have hs5 : s5.stk S = X S := by
    rw [hs5S, hs4S, ← hSdec]
  have hs3t : s3.stk t = X t := by
    rw [hfr3 t h0t.symm, hs2t]
    show (Function.update X S ((Val.int (k : ℤ)).enc ++ (v'.enc ++ A))) t = X t
    rw [Function.update_of_ne hSt.symm]
  have hs3d : s3.stk d = X d := by
    rw [hfr3 d h0d.symm, hs2d]
    show (Function.update X S ((Val.int (k : ℤ)).enc ++ (v'.enc ++ A))) d = X d
    rw [Function.update_of_ne hSd.symm]
  refine ⟨s5, n2 + n3 + n4 + 3, ?_, ?_, hs5, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Sk.pushSize
    exact Ev.seq' (C := n2 + n3 + n4 + 3) e1
      (Ev.seq' (C := n2 + n3 + n4 + 2) e2
        (Ev.seq' (C := n3 + n4 + 2) e3'
          (Ev.seq' (C := n4 + 2) e4 (e5.mono hn5) (by omega)) (by omega)) (by omega))
      (by omega)
  · -- cost: `n2 ≤ 40(isz k + 1)`, `n3 ≤ KSz·isz k`, `n4 ≤ 16(isz k.size + 1)`
    have h2 : n2 ≤ 40 * (isz (k : ℤ) + 1) := by rw [vsz_int] at hn2; exact hn2
    have h3 : n3 ≤ KSz * isz (k : ℤ) := hn3
    have h4 : n4 ≤ 16 * (vsz (Val.int (k.size : ℤ)) + 1) := hn4
    rw [vsz_int] at h4
    omega
  · rw [hfr5 SA hSSA.symm]; exact hs4SA
  · rw [hfr5 0 hS0.symm]; exact hs40
  · rw [hfr5 t hSt.symm, hs4t, hs3t]
  · rw [hfr5 d hSd.symm, hs4d, hs3d]
  · intro k' hkS hkSA hk0 hkt hkd
    have g1 : s5.stk k' = s4.stk k' := hfr5 k' hkS
    have g2 : s4.stk k' = s3.stk k' := hfr4 k' hk0 hkSA hkt hkd
    have g3 : s3.stk k' = s2.stk k' := hfr3 k' hk0
    have g4 : s2.stk k' = s1.stk k' := hfr2 k' hkS hk0 hkt hkd
    have g5 : s1.stk k' = X k' := by
      show (Function.update X S ((Val.int (k : ℤ)).enc ++ (v'.enc ++ A))) k' = X k'
      rw [Function.update_of_ne hkS]
    rw [g1, g2, g3, g4, g5]

end Work.Layout
