import Mathlib
import Submission.Work.Layout.dupIntDefs
import Submission.Work.Layout.dupIntBodyGlyph

set_option autoImplicit false

namespace Work.Layout

open Work.Layout.Sk HvdH

/-! ## The `dupInt` loop

`dupIntBody S B T` pops one glyph of `T` and pushes it on `S` and on `B`, stopping at the boundary
marker `gMark`.  The two one-step lemmas are `dupIntBodyGlyph` (non-marker glyph, proved in
`Submission/Work/Layout/dupIntBodyGlyph.lean`) and the terminating step below. -/

/-- The terminating iteration of the loop: the top of `T` is the boundary marker, which is popped,
and the loop flag is set to `gMark` so that the loop stops. -/
private theorem dupIntBodyMarkStep {main : Cmd} {S B T : Stk} (hST : S ≠ T) (hBT : B ≠ T)
    {g : Reg → Glyph} {X : Stk → List Glyph} {C S0 B0 : List Glyph}
    (hT : X T = gMark :: C) (hS : X S = S0) (hB : X B = B0) :
    ∃ s' n, Ev main (Sk.dupIntBody S B T) ⟨g, X⟩ s' n ∧ n ≤ 3 ∧
      s'.stk S = S0 ∧ s'.stk B = B0 ∧ s'.stk T = C ∧ s'.reg Sk.rF = gMark := by
  have hhead : (X T).headD Glyph.eos = gMark := by rw [hT]; rfl
  have htail : (X T).tail = C := by rw [hT]; rfl
  let s1 : State := ⟨Function.update g Sk.rK gMark, Function.update X T C⟩
  let s2 : State := ⟨Function.update s1.reg Sk.rF gMark, s1.stk⟩
  have e1 : Ev main (.pop T Sk.rK) ⟨g, X⟩ s1 1 := by
    have hp := ev_pop' main T Sk.rK g X
    rw [hhead, htail] at hp
    exact hp
  have hne : s1.reg Sk.rK = gMark := by simp only [s1, Function.update_self]
  have e2 : Ev main (.set Sk.rF gMark) s1 s2 1 := ev_set main Sk.rF gMark s1
  have e3 : Ev main
      (.ite Sk.rK gMark (.set Sk.rF gMark)
        (.seq (.push S Sk.rK) (.seq (.push B Sk.rK) (.set Sk.rF Glyph.cons)))) s1 s2 2 :=
    Ev.iteT hne e2
  have e4 : Ev main (Sk.dupIntBody S B T) ⟨g, X⟩ s2 3 := by
    unfold Sk.dupIntBody
    exact Ev.seq' e1 e3 (by norm_num)
  refine ⟨s2, 3, e4, le_rfl, ?_, ?_, ?_, ?_⟩
  · simp only [s2, s1]
    rw [Function.update_of_ne hST, hS]
  · simp only [s2, s1]
    rw [Function.update_of_ne hBT, hB]
  · simp only [s2, s1]
    rw [Function.update_self]
  · simp only [s2, Function.update_self]

/-! ## The loop -/

/-- The `dupInt` loop: starting with `G ++ gMark :: C` on `T`, `S0` on `S` and `B0` on `B`, the loop
consumes all of `G` — pushing each glyph on `S` and on `B` — removes the marker and stops, leaving
`G.reverse ++ S0` on `S`, `G.reverse ++ B0` on `B` and `C` on `T`. -/
theorem dupIntLoop {main : Cmd} {S B T : Stk} (hSB : S ≠ B) (hST : S ≠ T) (hBT : B ≠ T) :
    ∀ (G C S0 B0 : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph),
      gMark ∉ G → g rF = Glyph.cons → X T = G ++ gMark :: C → X S = S0 → X B = B0 →
      ∃ s', loopRuns main rF Glyph.cons (dupIntBody S B T) (G.length + 1) ⟨g, X⟩ s'
          (6 * (G.length + 1)) ∧
        s'.stk S = G.reverse ++ S0 ∧ s'.stk B = G.reverse ++ B0 ∧ s'.stk T = C ∧
        s'.reg rF = gMark := by
  intro G
  induction G with
  | nil =>
      intro C S0 B0 g X _ hreg hT hS hB
      obtain ⟨s', n, hev, hn, hS', hB', hT', hr'⟩ :=
        dupIntBodyMarkStep (main := main) hST hBT hT hS hB
      have hrun : loopRuns main rF Glyph.cons (dupIntBody S B T) 1 ⟨g, X⟩ s' (3 + 1) :=
        loopRuns.one hreg (hev.mono hn)
      exact ⟨s', loopRuns.mono (by omega) hrun (by omega), by simpa using hS',
        by simpa using hB', by simpa using hT', hr'⟩
  | cons h G' ih =>
      intro C S0 B0 g X hmem hreg hT hS hB
      have hh : h ≠ gMark := fun hh => hmem (hh ▸ List.mem_cons_self ..)
      have hmem' : gMark ∉ G' := fun hx => hmem (List.mem_cons_of_mem h hx)
      obtain ⟨s₁, n₁, hev₁, hn₁, hS₁, hB₁, hT₁, hr₁⟩ :=
        dupIntBodyGlyph (main := main) hSB hST hBT hh hT hS hB
      obtain ⟨s₂, hrun₂, hS₂, hB₂, hT₂, hr₂⟩ :=
        ih C (h :: S0) (h :: B0) s₁.reg s₁.stk hmem' hr₁ hT₁ hS₁ hB₁
      have hcat := loopRuns.concat (G'.length + 1)
        (loopRuns.one hreg (hev₁.mono hn₁)) hrun₂
      refine ⟨s₂, loopRuns.congr ?_ ?_ hcat, ?_, ?_, ?_, hr₂⟩
      · simp only [List.length_cons]; omega
      · simp only [List.length_cons]; omega
      · rw [hS₂]; simp
      · rw [hB₂]; simp
      · exact hT₂

/-! ## `dupInt` -/

/-- `dupInt S B T d` copies the `int` value at the top of stack `S` onto stack `B` (leaving `S`
unchanged), using `T` as a reversal buffer (it runs `mvA S T d`, which pushes
`(Val.int z).enc.reverse ++ [gMark]` on `T`, then pops the glyphs of `T` one by one, pushing each
onto `S` and onto `B`, and stops after removing the `gMark`). -/
theorem dupInt_ev {main : Cmd} {S B T d : Stk}
    (hSB : S ≠ B) (hST : S ≠ T) (hSd : S ≠ d) (hBT : B ≠ T) (hBd : B ≠ d) (hTd : T ≠ d)
    {g : Reg → Glyph} {X : Stk → List Glyph} {z : ℤ} {A : List Glyph}
    (hS : X S = (Val.int z).enc ++ A) :
    ∃ s' n, Ev main (dupInt S B T d) ⟨g, X⟩ s' n ∧ n ≤ 40 * (vsz (Val.int z) + 1) ∧
      s'.stk S = X S ∧ s'.stk B = (Val.int z).enc ++ X B ∧
      s'.stk T = X T ∧ s'.stk d = X d ∧
      (∀ k : Stk, k ≠ S → k ≠ B → k ≠ T → k ≠ d → s'.stk k = X k) := by
  -- the value is moved to `T`, reversed, above the boundary marker
  obtain ⟨s₁, n₁, h1, hn₁, hA₁, hT₁, hd₁, hf₁⟩ :=
    mvA_ev (main := main) hST hSd hTd (Val.int z) A (X T) (X d) g X hS rfl rfl
  -- arm the loop flag
  let sf : State := ⟨Function.update s₁.reg rF Glyph.cons, s₁.stk⟩
  have h2 : Ev main (.set rF Glyph.cons) s₁ sf 1 := ev_set main rF Glyph.cons s₁
  -- run the loop over `(Val.int z).enc.reverse`
  have hL : ((Val.int z).enc.reverse).length = vsz (Val.int z) := by simp [vsz]
  obtain ⟨s₃, hrun, hS₃, hB₃, hT₃, hr₃⟩ :=
    dupIntLoop (main := main) hSB hST hBT ((Val.int z).enc.reverse) (X T) A (X B)
      sf.reg sf.stk (gMark_not_mem_enc_rev (Val.int z)) (by simp only [sf, Function.update_self])
      hT₁ hA₁ (hf₁ B hSB.symm hBT hBd)
  have hloop : Ev main (.loop rF Glyph.cons (dupIntBody S B T)) sf s₃
      (6 * (((Val.int z).enc.reverse).length + 1) + 1) :=
    loopRuns.eval hrun (by rw [hr₃]; exact gMark_ne_cons)
  have hmain : Ev main (dupInt S B T d) ⟨g, X⟩ s₃
      (n₁ + (1 + (6 * (((Val.int z).enc.reverse).length + 1) + 1))) := by
    rw [dupInt_eq]
    exact Ev.seq h1 (Ev.seq h2 hloop)
  refine ⟨s₃, _, hmain, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hL]; omega
  · rw [hS₃, List.reverse_reverse, hS]
  · rw [hB₃, List.reverse_reverse]
  · exact hT₃
  · have hfr : s₃.stk d = s₁.stk d := by
      have h := Ev.frame hloop (S := {S, T, B})
        (by intro x hx
            simp only [cmdTouches] at hx
            rw [cmdTouches_dupIntBody] at hx
            exact hx)
        (by simp only [Finset.mem_insert, Finset.mem_singleton]
            rintro (e1 | e2 | e3)
            · exact hSd e1.symm
            · exact hTd e2.symm
            · exact hBd e3.symm)
      simpa using h
    rw [hfr, hd₁]
  · intro k hkS hkB hkT hkd
    have h := Ev.frame hmain (S := {S, T, B, d}) (by rw [cmdTouches_dupInt])
      (by simp only [Finset.mem_insert, Finset.mem_singleton]
          rintro (e1 | e2 | e3 | e4)
          · exact hkS e1
          · exact hkT e2
          · exact hkB e3
          · exact hkd e4)
    simpa using h

end Work.Layout
