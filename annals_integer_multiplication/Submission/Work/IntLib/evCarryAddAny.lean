import Submission.Work.IntLib.evCA.Defs
import Submission.Work.IntLib.evCA.Body
import Submission.Work.IntLib.evCA.ofBitsAddAll
import Submission.Work.IntLib.evCASetupEv
import Submission.Work.IntLib.evCATailEv
import Submission.Work.IntLib.evCAFinishEv

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib

open HvdH

theorem evCarryAddAny :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (b : ℕ) (main : HvdH.Cmd) (g : HvdH.Reg → HvdH.Glyph)
      (X : HvdH.Stk → List HvdH.Glyph) (h : ℕ) (W LO : List Bool)
      (Ws Os Cs Bs A2s As : List HvdH.Glyph),
      X Work.IntLib.aA = (HvdH.Val.enc (.int (h : ℤ))).reverse ++ Work.IntLib.Shift.gmk Work.IntLib.aA :: As →
      X Work.IntLib.aW = W.map HvdH.Glyph.bit ++ Work.IntLib.Shift.gmk Work.IntLib.aW :: Ws →
      X Work.IntLib.aO = LO.reverse.map HvdH.Glyph.bit ++ [HvdH.Glyph.pos] ++ Work.IntLib.Shift.gmk Work.IntLib.aO :: Os →
      X Work.IntLib.aCW = Work.IntLib.Unary b (Work.IntLib.Shift.gmk Work.IntLib.aCW :: Cs) →
      X Work.IntLib.aB = Work.IntLib.Shift.gmk Work.IntLib.aB :: Bs →
      X Work.IntLib.a2 = Work.IntLib.Shift.gmk Work.IntLib.a2 :: A2s →
      ∃ (s' : HvdH.State) (n : ℕ), Work.Layout.Ev main prog ⟨g, X⟩ s' n ∧
        n ≤ K * (b + W.length + h.size + 1) ∧
        s'.stk Work.IntLib.aA = Work.IntLib.Shift.gmk Work.IntLib.aA :: As ∧
        (∃ W' : List Bool, s'.stk Work.IntLib.aW = W'.map HvdH.Glyph.bit ++ Work.IntLib.Shift.gmk Work.IntLib.aW :: Ws ∧
          Work.IntLib.ofBits W' = (Work.IntLib.ofBits W + h) / 2 ^ b ∧
          W'.length ≤ max W.length (h.size + 1) + 1 ∧
          (1 ≤ b → W.length ≤ 3 * b + 1 → h.size ≤ 3 * b → W'.length ≤ 3 * b + 1)) ∧
        (∃ LO' : List Bool, s'.stk Work.IntLib.aO = LO'.reverse.map HvdH.Glyph.bit ++ [HvdH.Glyph.pos] ++ Work.IntLib.Shift.gmk Work.IntLib.aO :: Os ∧
          LO'.length = LO.length + b ∧
          Work.IntLib.ofBits LO' = Work.IntLib.ofBits LO + 2 ^ LO.length * ((Work.IntLib.ofBits W + h) % 2 ^ b)) ∧
        s'.stk Work.IntLib.aCW = Work.IntLib.Unary 0 (Work.IntLib.Shift.gmk Work.IntLib.aCW :: Cs) ∧
        s'.stk Work.IntLib.aB = Work.IntLib.Shift.gmk Work.IntLib.aB :: Bs ∧
        s'.stk Work.IntLib.a2 = Work.IntLib.Shift.gmk Work.IntLib.a2 :: A2s ∧
        (∀ j : HvdH.Stk, j ≠ Work.IntLib.aA → j ≠ Work.IntLib.aW → j ≠ Work.IntLib.aO →
          j ≠ Work.IntLib.aCW → j ≠ Work.IntLib.aB → j ≠ Work.IntLib.a2 → s'.stk j = X j) := by
  refine ⟨EvCA.prog, 100, ?_⟩
  intro b main g X h W LO Ws Os Cs Bs A2s As hA hW hO hC hB h2
  -- setup
  obtain ⟨s1, n1, hev1, hn1, hP1, hA1, hfr1⟩ :=
    evCASetupEv main h b W LO g X As Ws Os Cs A2s Bs hA hW hO hC hB h2
  have hev1' : Work.Layout.Ev main EvCA.progSetup ⟨g, X⟩ s1 n1 := hev1
  -- loop
  obtain ⟨s2, n2, hev2, hn2, hP2⟩ :=
    EvC.addLoop_ev main b W h.bits LO (EvCA.XA X As) Ws Os Cs A2s Bs s1
      (fun k t hP hk => EvC.bodyA_ev main b W h.bits LO (EvCA.XA X As) Ws Os Cs A2s Bs k t hP hk) hP1
  have hev2' : Work.Layout.Ev main EvCA.progLoop s1 s2 n2 := hev2
  -- tail
  obtain ⟨s3, n3, hev3, hn3, hP3, hfr3⟩ :=
    evCATailEv main b W h.bits LO (EvCA.XA X As) Ws Os Cs A2s Bs s2 hP2
  have hev3' : Work.Layout.Ev main EvCA.progTail s2 s3 n3 := hev3
  -- pad + final
  obtain ⟨s4, n4, hev4, hn4, hW4, hB4, hO4, hC4, h24, hfr4⟩ :=
    evCAFinishEv main b W h.bits LO Ws Os Cs A2s Bs s3 hP3
  have hev4' : Work.Layout.Ev main EvCA.progFinish s3 s4 n4 := hev4
  have hevAll : Work.Layout.Ev main EvCA.prog ⟨g, X⟩ s4 (n1 + (n2 + (n3 + n4))) :=
    Work.Layout.Ev.seqs_cons hev1'
      (Work.Layout.Ev.seqs_cons hev2' (Work.Layout.Ev.seqs_cons hev3' hev4'))
  -- `aA` is restored
  have hA4 : s4.stk aA = Shift.gmk aA :: As := by
    have e1 : s4.stk aA = s3.stk aA := hfr4 aA (by decide) (by decide) (by decide) (by decide) (by decide)
    have e2 : s3.stk aA = s2.stk aA := hfr3 aA (by decide) (by decide) (by decide) (by decide)
    have e3 : s2.stk aA = (EvCA.XA X As) aA := hP2.2.2.1 aA (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [e1, e2, e3, EvCA.XA_self]
  -- the arithmetic of the two streams
  have hN : EvC.addN W h.bits = max W.length h.size := by
    rw [EvC.addN, Nat.size_eq_bits_len]
  have hSlen : (EvC.addAll W h.bits).length ≤ max W.length h.size + 1 := by
    have h := EvC.addAll_length_le W h.bits
    rw [hN] at h; exact h
  have hofW : Work.IntLib.ofBits ((EvC.addAll W h.bits).drop b) =
      (Work.IntLib.ofBits W + h) / 2 ^ b := by
    rw [EvC.ofBits_drop_div, evCA.ofBitsAddAll, Work.IntLib.ofBits_bits]
  have hlenW : ((EvC.addAll W h.bits).drop b).length ≤ max W.length (h.size + 1) + 1 := by
    have h1 : ((EvC.addAll W h.bits).drop b).length ≤ (EvC.addAll W h.bits).length := by
      rw [List.length_drop]; omega
    omega
  have hcondW : 1 ≤ b → W.length ≤ 3 * b + 1 → h.size ≤ 3 * b →
      ((EvC.addAll W h.bits).drop b).length ≤ 3 * b + 1 := by
    intro hb1 hWl hhs
    have h1 : ((EvC.addAll W h.bits).drop b).length = (EvC.addAll W h.bits).length - b :=
      List.length_drop
    have h3 : max W.length h.size ≤ 3 * b + 1 := by omega
    omega
  have hO' : s4.stk aO = (LO ++ EvC.lowBits b (EvC.addAll W h.bits)).reverse.map Glyph.bit ++
      [Glyph.pos] ++ Shift.gmk aO :: Os := by
    rw [hO4, List.reverse_append, List.map_append]
    try rw [List.append_assoc]
    try rw [List.append_assoc]
    try rw [List.append_assoc]
    try rfl
  have hlenLO : (LO ++ EvC.lowBits b (EvC.addAll W h.bits)).length = LO.length + b := by
    rw [List.length_append, EvC.lowBits_length]
  have hofLO : Work.IntLib.ofBits (LO ++ EvC.lowBits b (EvC.addAll W h.bits)) =
      Work.IntLib.ofBits LO + 2 ^ LO.length * ((Work.IntLib.ofBits W + h) % 2 ^ b) := by
    rw [Work.IntLib.ofBits_append, EvC.ofBits_lowBits, evCA.ofBitsAddAll, Work.IntLib.ofBits_bits]
  have hframe : ∀ j : HvdH.Stk, j ≠ aA → j ≠ aW → j ≠ aO → j ≠ aCW → j ≠ aB → j ≠ a2 →
      s4.stk j = X j := by
    intro j hjA hjW hjO hjC hjB hj2
    have e1 : s4.stk j = s3.stk j := hfr4 j hjW hjB hjO hj2 hjC
    have e2 : s3.stk j = s2.stk j := hfr3 j hjO hj2 hjC hjB
    have e3 : s2.stk j = (EvCA.XA X As) j := hP2.2.2.1 j hjW hjB hjO hj2 hjC
    rw [e1, e2, e3, EvCA.XA_ne X As hjA]
  have hcost : n1 + (n2 + (n3 + n4)) ≤ 100 * (b + W.length + h.size + 1) := by
    have h2 : n2 ≤ EvC.addN W h.bits * 24 + 1 := hn2
    have h4 : n4 ≤ 7 * b + 5 * EvC.addN W h.bits + 20 := hn4
    have h5 : EvC.addN W h.bits ≤ W.length + h.size := by
      rw [hN]
      exact Nat.max_le.mpr ⟨Nat.le_add_right _ _, Nat.le_add_left _ _⟩
    omega
  refine ⟨s4, n1 + (n2 + (n3 + n4)), hevAll, hcost, hA4,
    ⟨(EvC.addAll W h.bits).drop b, hW4, hofW, hlenW, hcondW⟩,
    ⟨LO ++ EvC.lowBits b (EvC.addAll W h.bits), hO', hlenLO, hofLO⟩,
    hC4, hB4, h24, hframe⟩

end Work.IntLib
