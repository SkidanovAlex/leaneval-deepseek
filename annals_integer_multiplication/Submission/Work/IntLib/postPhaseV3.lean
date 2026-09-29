import Mathlib
import Submission.Work.IntLib.chunkProg
import Submission.Work.IntLib.Shift.Base
import Submission.Work.Layout.Base
import Submission.Work.IntLib.clearAllsEv

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Work.IntLib

open HvdH
open Work.Layout

/-!
# `postPhaseV3`

The `postProg` of the `chunk` word pushes the terminator `nil` on the string stack `sS`, drains
`sS` onto the value stack `0` (reversing it), and clears the ten scratch stacks down to their
frame markers.

`postPhaseV3` is the general form of `postPhaseV2`: the contents of the three stacks `sX`, `sB`,
`sN` are no longer required to be concrete `Val.enc` encodings of naturals -- they are arbitrary
lists `Gx`, `Gb`, `Gn`, with the marker-freeness needed by `clearAll` supplied as hypotheses.
The cost bound is `5 * (lengths + 22)`.
-/

/-- The regions above the frame markers of the ten stacks `postProg` clears. -/
def postRgn3 (Gx Gb Gn R1 R2 R3 R4 R5 R6 : List Glyph) : Stk → List Glyph := fun k =>
  if k = sX then Gx
  else if k = sB then Gb
  else if k = sN then Gn
  else if k = sR then R1 else if k = sCW then R2 else if k = sCB then R3
  else if k = sCT then R4 else if k = sCN then R5 else if k = sZ then R6 else []

theorem postRgn3_sX (Gx Gb Gn R1 R2 R3 R4 R5 R6 : List Glyph) :
    postRgn3 Gx Gb Gn R1 R2 R3 R4 R5 R6 sX = Gx := by
  simp only [postRgn3, ↓reduceIte]

theorem postRgn3_sB (Gx Gb Gn R1 R2 R3 R4 R5 R6 : List Glyph) :
    postRgn3 Gx Gb Gn R1 R2 R3 R4 R5 R6 sB = Gb := by
  have h1 : ¬ ((sB : Stk) = sX) := by decide
  simp only [postRgn3, h1, ↓reduceIte]

theorem postRgn3_sN (Gx Gb Gn R1 R2 R3 R4 R5 R6 : List Glyph) :
    postRgn3 Gx Gb Gn R1 R2 R3 R4 R5 R6 sN = Gn := by
  have h1 : ¬ ((sN : Stk) = sX) := by decide
  have h2 : ¬ ((sN : Stk) = sB) := by decide
  simp only [postRgn3, h1, h2, ↓reduceIte]

theorem postRgn3_sR (Gx Gb Gn R1 R2 R3 R4 R5 R6 : List Glyph) :
    postRgn3 Gx Gb Gn R1 R2 R3 R4 R5 R6 sR = R1 := by
  have h1 : ¬ ((sR : Stk) = sX) := by decide
  have h2 : ¬ ((sR : Stk) = sB) := by decide
  have h3 : ¬ ((sR : Stk) = sN) := by decide
  simp only [postRgn3, h1, h2, h3, ↓reduceIte]

theorem postRgn3_sS (Gx Gb Gn R1 R2 R3 R4 R5 R6 : List Glyph) :
    postRgn3 Gx Gb Gn R1 R2 R3 R4 R5 R6 sS = [] := by
  have h1 : ¬ ((sS : Stk) = sX) := by decide
  have h2 : ¬ ((sS : Stk) = sB) := by decide
  have h3 : ¬ ((sS : Stk) = sN) := by decide
  have h4 : ¬ ((sS : Stk) = sR) := by decide
  have h5 : ¬ ((sS : Stk) = sCW) := by decide
  have h6 : ¬ ((sS : Stk) = sCB) := by decide
  have h7 : ¬ ((sS : Stk) = sCT) := by decide
  have h8 : ¬ ((sS : Stk) = sCN) := by decide
  have h9 : ¬ ((sS : Stk) = sZ) := by decide
  simp only [postRgn3, h1, h2, h3, h4, h5, h6, h7, h8, h9, ↓reduceIte]

theorem postRgn3_sCW (Gx Gb Gn R1 R2 R3 R4 R5 R6 : List Glyph) :
    postRgn3 Gx Gb Gn R1 R2 R3 R4 R5 R6 sCW = R2 := by
  have h1 : ¬ ((sCW : Stk) = sX) := by decide
  have h2 : ¬ ((sCW : Stk) = sB) := by decide
  have h3 : ¬ ((sCW : Stk) = sN) := by decide
  have h4 : ¬ ((sCW : Stk) = sR) := by decide
  simp only [postRgn3, h1, h2, h3, h4, ↓reduceIte]

theorem postRgn3_sCB (Gx Gb Gn R1 R2 R3 R4 R5 R6 : List Glyph) :
    postRgn3 Gx Gb Gn R1 R2 R3 R4 R5 R6 sCB = R3 := by
  have h1 : ¬ ((sCB : Stk) = sX) := by decide
  have h2 : ¬ ((sCB : Stk) = sB) := by decide
  have h3 : ¬ ((sCB : Stk) = sN) := by decide
  have h4 : ¬ ((sCB : Stk) = sR) := by decide
  have h5 : ¬ ((sCB : Stk) = sCW) := by decide
  simp only [postRgn3, h1, h2, h3, h4, h5, ↓reduceIte]

theorem postRgn3_sCT (Gx Gb Gn R1 R2 R3 R4 R5 R6 : List Glyph) :
    postRgn3 Gx Gb Gn R1 R2 R3 R4 R5 R6 sCT = R4 := by
  have h1 : ¬ ((sCT : Stk) = sX) := by decide
  have h2 : ¬ ((sCT : Stk) = sB) := by decide
  have h3 : ¬ ((sCT : Stk) = sN) := by decide
  have h4 : ¬ ((sCT : Stk) = sR) := by decide
  have h5 : ¬ ((sCT : Stk) = sCW) := by decide
  have h6 : ¬ ((sCT : Stk) = sCB) := by decide
  simp only [postRgn3, h1, h2, h3, h4, h5, h6, ↓reduceIte]

theorem postRgn3_sCN (Gx Gb Gn R1 R2 R3 R4 R5 R6 : List Glyph) :
    postRgn3 Gx Gb Gn R1 R2 R3 R4 R5 R6 sCN = R5 := by
  have h1 : ¬ ((sCN : Stk) = sX) := by decide
  have h2 : ¬ ((sCN : Stk) = sB) := by decide
  have h3 : ¬ ((sCN : Stk) = sN) := by decide
  have h4 : ¬ ((sCN : Stk) = sR) := by decide
  have h5 : ¬ ((sCN : Stk) = sCW) := by decide
  have h6 : ¬ ((sCN : Stk) = sCB) := by decide
  have h7 : ¬ ((sCN : Stk) = sCT) := by decide
  simp only [postRgn3, h1, h2, h3, h4, h5, h6, h7, ↓reduceIte]

theorem postRgn3_sZ (Gx Gb Gn R1 R2 R3 R4 R5 R6 : List Glyph) :
    postRgn3 Gx Gb Gn R1 R2 R3 R4 R5 R6 sZ = R6 := by
  have h1 : ¬ ((sZ : Stk) = sX) := by decide
  have h2 : ¬ ((sZ : Stk) = sB) := by decide
  have h3 : ¬ ((sZ : Stk) = sN) := by decide
  have h4 : ¬ ((sZ : Stk) = sR) := by decide
  have h5 : ¬ ((sZ : Stk) = sCW) := by decide
  have h6 : ¬ ((sZ : Stk) = sCB) := by decide
  have h7 : ¬ ((sZ : Stk) = sCT) := by decide
  have h8 : ¬ ((sZ : Stk) = sCN) := by decide
  simp only [postRgn3, h1, h2, h3, h4, h5, h6, h7, h8, ↓reduceIte]

theorem postPhaseV3 (main : HvdH.Cmd) (X₀ : HvdH.Stk → List HvdH.Glyph)
    (Sval Gx Gb Gn R1 R2 R3 R4 R5 R6 : List HvdH.Glyph)
    (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph)
    (h0 : X 0 = X₀ 0)
    (hS : X Work.IntLib.sS = Sval ++ Work.IntLib.Shift.gmk Work.IntLib.sS :: X₀ Work.IntLib.sS)
    (hX : X Work.IntLib.sX = Gx ++ Work.IntLib.Shift.gmk Work.IntLib.sX :: X₀ Work.IntLib.sX)
    (hB : X Work.IntLib.sB = Gb ++ Work.IntLib.Shift.gmk Work.IntLib.sB :: X₀ Work.IntLib.sB)
    (hNv : X Work.IntLib.sN = Gn ++ Work.IntLib.Shift.gmk Work.IntLib.sN :: X₀ Work.IntLib.sN)
    (hR : X Work.IntLib.sR = R1 ++ Work.IntLib.Shift.gmk Work.IntLib.sR :: X₀ Work.IntLib.sR)
    (hCW : X Work.IntLib.sCW = R2 ++ Work.IntLib.Shift.gmk Work.IntLib.sCW :: X₀ Work.IntLib.sCW)
    (hCB : X Work.IntLib.sCB = R3 ++ Work.IntLib.Shift.gmk Work.IntLib.sCB :: X₀ Work.IntLib.sCB)
    (hCT : X Work.IntLib.sCT = R4 ++ Work.IntLib.Shift.gmk Work.IntLib.sCT :: X₀ Work.IntLib.sCT)
    (hCN : X Work.IntLib.sCN = R5 ++ Work.IntLib.Shift.gmk Work.IntLib.sCN :: X₀ Work.IntLib.sCN)
    (hZ : X Work.IntLib.sZ = R6 ++ Work.IntLib.Shift.gmk Work.IntLib.sZ :: X₀ Work.IntLib.sZ)
    (hoth : ∀ j : HvdH.Stk, j ≠ 0 → j ≠ Work.IntLib.sX → j ≠ Work.IntLib.sB → j ≠ Work.IntLib.sN → j ≠ Work.IntLib.sR →
      j ≠ Work.IntLib.sS → j ≠ Work.IntLib.sCW → j ≠ Work.IntLib.sCB → j ≠ Work.IntLib.sCT → j ≠ Work.IntLib.sCN →
      j ≠ Work.IntLib.sZ → X j = X₀ j)
    (hSafeS : ∀ h ∈ Sval ++ [HvdH.Glyph.nil], h ≠ Work.IntLib.Shift.gmk Work.IntLib.sS)
    (hSafeX : ∀ h ∈ Gx, h ≠ Work.IntLib.Shift.gmk Work.IntLib.sX)
    (hSafeB : ∀ h ∈ Gb, h ≠ Work.IntLib.Shift.gmk Work.IntLib.sB)
    (hSafeN : ∀ h ∈ Gn, h ≠ Work.IntLib.Shift.gmk Work.IntLib.sN)
    (hSafeR : ∀ h ∈ R1, h ≠ Work.IntLib.Shift.gmk Work.IntLib.sR)
    (hSafeW : ∀ h ∈ R2, h ≠ Work.IntLib.Shift.gmk Work.IntLib.sCW)
    (hSafeB2 : ∀ h ∈ R3, h ≠ Work.IntLib.Shift.gmk Work.IntLib.sCB)
    (hSafeT : ∀ h ∈ R4, h ≠ Work.IntLib.Shift.gmk Work.IntLib.sCT)
    (hSafeN2 : ∀ h ∈ R5, h ≠ Work.IntLib.Shift.gmk Work.IntLib.sCN)
    (hSafeZ : ∀ h ∈ R6, h ≠ Work.IntLib.Shift.gmk Work.IntLib.sZ) :
    ∃ (s' : HvdH.State) (n : ℕ), Work.Layout.Ev main Work.IntLib.postProg ⟨g, X⟩ s' n ∧
      n ≤ 5 * (Sval.length + Gx.length + Gb.length + Gn.length + R1.length + R2.length + R3.length
        + R4.length + R5.length + R6.length + 22) ∧
      s'.stk 0 = Sval.reverse ++ [HvdH.Glyph.nil] ++ X₀ 0 ∧
      (∀ j : HvdH.Stk, j ≠ 0 → s'.stk j = X₀ j) := by
  -- ## Step 1: push the terminator `nil` on the string stack `sS`
  have hstep1 : Ev main (seqs [Cmd.set rH Glyph.nil, Cmd.push sS rH]) ⟨g, X⟩
      ⟨Function.update g rH Glyph.nil, Function.update X sS (Glyph.nil :: X sS)⟩ (1 + 1) :=
    Ev.seqs_cons (ev_set' main rH Glyph.nil g X)
      (by simpa [seqs] using ev_push' main sS rH (Function.update g rH Glyph.nil) X)
  obtain ⟨m1, he1, hm1⟩ := hstep1
  -- ## Step 2: drain `sS` (the `nil` plus `Sval`) onto the value stack `0`
  have hsafeD : ∀ h ∈ (Glyph.nil :: Sval), h ≠ Shift.gmk sS := by
    intro h hh
    rcases List.mem_cons.mp hh with h' | h'
    · subst h'; exact (Shift.gmk_ne_nil sS).symm
    · exact hSafeS h (List.mem_append_left [Glyph.nil] h')
  have hX1S : (Function.update X sS (Glyph.nil :: X sS)) sS
      = (Glyph.nil :: Sval) ++ Shift.gmk sS :: X₀ sS := by
    simp only [Function.update_self, hS, List.cons_append]
  have hX10 : (Function.update X sS (Glyph.nil :: X sS)) 0 = X₀ 0 := by
    rw [Function.update_of_ne (by decide : (0 : Stk) ≠ sS), h0]
  obtain ⟨s2, n2, he2, hn2, -, hs2S, hs20, hs2o⟩ :=
    Shift.drain_ev main sS 0 (Shift.gmk sS) rH rK (by decide) (by decide)
      (Glyph.nil :: Sval) (X₀ sS) (X₀ 0)
      (Function.update g rH Glyph.nil) (Function.update X sS (Glyph.nil :: X sS)) hsafeD hX1S hX10
  -- ## Step 3: clear the ten scratch stacks
  have h0notin : (0 : Stk) ∉ clearList := by decide
  have hnodup : clearList.Nodup := by decide
  have hXrgn : ∀ k ∈ clearList, k ≠ sS →
      X k = postRgn3 Gx Gb Gn R1 R2 R3 R4 R5 R6 k ++ Shift.gmk k :: X₀ k := by
    intro k hk hkS
    fin_cases hk
    · rw [postRgn3_sX]; exact hX
    · rw [postRgn3_sB]; exact hB
    · rw [postRgn3_sN]; exact hNv
    · rw [postRgn3_sR]; exact hR
    · exact absurd rfl hkS
    · rw [postRgn3_sCW]; exact hCW
    · rw [postRgn3_sCB]; exact hCB
    · rw [postRgn3_sCT]; exact hCT
    · rw [postRgn3_sCN]; exact hCN
    · rw [postRgn3_sZ]; exact hZ
  have hZform : ∀ k ∈ clearList,
      s2.stk k = postRgn3 Gx Gb Gn R1 R2 R3 R4 R5 R6 k ++ Shift.gmk k :: X₀ k := by
    intro k hk
    by_cases hkS : k = sS
    · subst hkS
      simp only [hs2S, postRgn3_sS, List.nil_append]
    · have hk0 : k ≠ 0 := fun h => h0notin (h ▸ hk)
      simp only [hs2o k hkS hk0, Function.update_of_ne hkS, hXrgn k hk hkS]
  have hsafe : ∀ k ∈ clearList, ∀ h ∈ postRgn3 Gx Gb Gn R1 R2 R3 R4 R5 R6 k, h ≠ Shift.gmk k := by
    intro k hk h hh
    fin_cases hk
    · rw [postRgn3_sX] at hh; exact hSafeX h hh
    · rw [postRgn3_sB] at hh; exact hSafeB h hh
    · rw [postRgn3_sN] at hh; exact hSafeN h hh
    · rw [postRgn3_sR] at hh; exact hSafeR h hh
    · rw [postRgn3_sS] at hh; exact absurd hh (by simp)
    · rw [postRgn3_sCW] at hh; exact hSafeW h hh
    · rw [postRgn3_sCB] at hh; exact hSafeB2 h hh
    · rw [postRgn3_sCT] at hh; exact hSafeT h hh
    · rw [postRgn3_sCN] at hh; exact hSafeN2 h hh
    · rw [postRgn3_sZ] at hh; exact hSafeZ h hh
  obtain ⟨s3, c3, he3ev, hc3, h3in, h3out⟩ :=
    clearAllsEv_aux main rH rK clearList s2.stk (postRgn3 Gx Gb Gn R1 R2 R3 R4 R5 R6) X₀ s2.reg
      hnodup hsafe hZform
  obtain ⟨n3, he3, hn3⟩ := he3ev
  -- ## Assembly
  have hev : Eval main postProg ⟨g, X⟩ s3 (m1 + (n2 + n3)) := by
    unfold postProg
    exact Eval.seq he1 (Eval.seq he2 he3)
  have hsum : (clearList.map fun k => (postRgn3 Gx Gb Gn R1 R2 R3 R4 R5 R6 k).length).sum
      = Gx.length + Gb.length + Gn.length
        + R1.length + R2.length + R3.length + R4.length + R5.length + R6.length := by
    simp [clearList, postRgn3_sX, postRgn3_sB, postRgn3_sN, postRgn3_sR, postRgn3_sS,
      postRgn3_sCW, postRgn3_sCB, postRgn3_sCT, postRgn3_sCN, postRgn3_sZ]
    omega
  refine ⟨s3, m1 + (n2 + n3), ⟨m1 + (n2 + n3), hev, le_rfl⟩, ?_, ?_, ?_⟩
  · -- the cost bound
    have h2 : n2 ≤ 5 * (Sval.length + 1 + 1) + 2 := by simpa using hn2
    have h3b : n3 ≤ 5 * (Gx.length + Gb.length + Gn.length + R1.length + R2.length + R3.length
        + R4.length + R5.length + R6.length + 10) + 4 * 10 + 1 := by
      refine le_trans hn3 ?_
      rw [hsum] at hc3
      simpa [clearList] using hc3
    omega
  · -- the value stack
    simp only [h3out 0 h0notin, hs20, hX10, List.reverse_cons]
  · -- every other stack is restored
    intro j hj0
    by_cases hj : j ∈ clearList
    · exact h3in j hj
    · have hjS : j ≠ sS := fun h => hj (by rw [h]; decide)
      rw [h3out j hj, hs2o j hjS hj0, Function.update_of_ne hjS]
      exact hoth j hj0
        (fun h => hj (by rw [h]; decide))
        (fun h => hj (by rw [h]; decide))
        (fun h => hj (by rw [h]; decide))
        (fun h => hj (by rw [h]; decide))
        (fun h => hj (by rw [h]; decide))
        (fun h => hj (by rw [h]; decide))
        (fun h => hj (by rw [h]; decide))
        (fun h => hj (by rw [h]; decide))
        (fun h => hj (by rw [h]; decide))
        (fun h => hj (by rw [h]; decide))

end Work.IntLib
