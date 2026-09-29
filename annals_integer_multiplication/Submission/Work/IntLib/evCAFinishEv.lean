import Mathlib
import Submission.Work.IntLib.evCA.Defs
import Submission.Work.IntLib.evCA.padAGen

/-!
# `IntLib` / `evCarryAddAny`: the padding and the final move

`evCAFinishEv` runs the last two phases of the `evCarryAddAny` word from the state `EvC.postP`
produced by the tail: `padA` pushes `b - |addAll W hbits|` zero bits onto `aO` (so that exactly `b`
bits have been finalised), and the final `Shift.drain` moves the remaining high bits from `a2` back
onto `aW` (least significant bit on top).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib

open HvdH

theorem evCAFinishEv (main : HvdH.Cmd) (b : ℕ) (W hbits LO : List Bool)
    (Ws Os Cs A2s Bs : List HvdH.Glyph) (s : HvdH.State)
    (hP : Work.IntLib.EvC.postP b W hbits LO Ws Os Cs A2s Bs s) :
    ∃ (s' : HvdH.State) (n : ℕ), Work.Layout.Ev main Work.IntLib.EvCA.progFinish s s' n ∧
      n ≤ 7 * b + 5 * Work.IntLib.EvC.addN W hbits + 20 ∧
      s'.stk Work.IntLib.aW = ((Work.IntLib.EvC.addAll W hbits).drop b).map HvdH.Glyph.bit ++
        Work.IntLib.Shift.gmk Work.IntLib.aW :: Ws ∧
      s'.stk Work.IntLib.aB = Work.IntLib.Shift.gmk Work.IntLib.aB :: Bs ∧
      s'.stk Work.IntLib.aO = (Work.IntLib.EvC.lowBits b (Work.IntLib.EvC.addAll W hbits)).reverse.map HvdH.Glyph.bit ++
        (LO.reverse.map HvdH.Glyph.bit ++ [HvdH.Glyph.pos] ++ Work.IntLib.Shift.gmk Work.IntLib.aO :: Os) ∧
      s'.stk Work.IntLib.aCW = Work.IntLib.Unary 0 (Work.IntLib.Shift.gmk Work.IntLib.aCW :: Cs) ∧
      s'.stk Work.IntLib.a2 = Work.IntLib.Shift.gmk Work.IntLib.a2 :: A2s ∧
      (∀ j : HvdH.Stk, j ≠ Work.IntLib.aW → j ≠ Work.IntLib.aB → j ≠ Work.IntLib.aO →
        j ≠ Work.IntLib.a2 → j ≠ Work.IntLib.aCW → s'.stk j = s.stk j) := by
  obtain ⟨sg, sX⟩ := s
  obtain ⟨hW, hB, hO, h2, hCW⟩ := hP
  simp only [Work.Layout.stk_mk] at hW hB hO h2 hCW
  obtain ⟨s1, n1, hev1, hn1, hO1, hCW1, hfr1⟩ :=
    evCA.padAGen main sg sX (b - (Work.IntLib.EvC.addAll W hbits).length)
      ((Work.IntLib.EvC.addAll W hbits).take b)
      (LO.reverse.map Glyph.bit ++ [Glyph.pos] ++ Shift.gmk aO :: Os) Cs
      (by simpa only [List.append_assoc] using hO) hCW
  have hG : ∀ g ∈ ((Work.IntLib.EvC.addAll W hbits).drop b).reverse.map Glyph.bit,
      g ≠ Shift.gmk a2 := by
    intro g hg
    obtain ⟨bb, -, rfl⟩ := List.mem_map.mp hg
    exact Shift.bit_ne_gmk a2 bb
  have ha2 : s1.stk a2 = ((Work.IntLib.EvC.addAll W hbits).drop b).reverse.map Glyph.bit ++
      Shift.gmk a2 :: A2s := by
    rw [hfr1 a2 (by decide : a2 ≠ aO) (by decide : a2 ≠ aCW)]; exact h2
  have haW : s1.stk aW = Shift.gmk aW :: Ws := by
    rw [hfr1 aW (by decide : aW ≠ aO) (by decide : aW ≠ aCW)]; exact hW
  obtain ⟨s2, n2, hev2, hn2, _hne, hA2, hWa, hfr2⟩ :=
    Shift.drain_ev main a2 aW (Shift.gmk a2) Work.IntLib.EvC.rGa Work.IntLib.EvC.rLa
      (by decide : a2 ≠ aW) (by decide : Work.IntLib.EvC.rLa ≠ Work.IntLib.EvC.rGa)
      (((Work.IntLib.EvC.addAll W hbits).drop b).reverse.map Glyph.bit) A2s (Shift.gmk aW :: Ws)
      s1.reg s1.stk hG ha2 haW
  have hev2' : Work.Layout.Ev main Work.IntLib.EvCA.progFinal s1 s2 n2 := ⟨n2, hev2, le_rfl⟩
  have hev : Work.Layout.Ev main Work.IntLib.EvCA.progFinish ⟨sg, sX⟩ s2 (n1 + n2) :=
    Work.Layout.Ev.seqs_cons hev1 hev2'
  have hcost : n1 + n2 ≤ 7 * b + 5 * Work.IntLib.EvC.addN W hbits + 20 := by
    have h3 : ((Work.IntLib.EvC.addAll W hbits).drop b).length ≤
        Work.IntLib.EvC.addN W hbits + 1 := by
      have h4 := Work.IntLib.EvC.addAll_length_le W hbits
      rw [List.length_drop]; omega
    simp only [List.length_map, List.length_reverse] at hn2
    omega
  refine ⟨s2, n1 + n2, hev, hcost, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hWa]
    simp only [List.map_reverse, List.reverse_reverse]
  · rw [hfr2 aB (by decide : aB ≠ a2) (by decide : aB ≠ aW),
      hfr1 aB (by decide : aB ≠ aO) (by decide : aB ≠ aCW)]
    exact hB
  · rw [hfr2 aO (by decide : aO ≠ a2) (by decide : aO ≠ aW), hO1]
    simp only [Work.IntLib.EvC.lowBits]
  · rw [hfr2 aCW (by decide : aCW ≠ a2) (by decide : aCW ≠ aW)]
    exact hCW1
  · exact hA2
  · intro j hjW hjB hjO hj2 hjC
    rw [hfr2 j hj2 hjW, hfr1 j hjO hjC]

end Work.IntLib
