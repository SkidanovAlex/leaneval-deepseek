import Mathlib
import Submission.Work.IntLib.evCA.Infra

/-!
# `IntLib` / `evCarryAdd`: `readA` moves the digit from `aA` to `aB`

`EvC.readA` drains the reversed encoding of an integer `h` from the region above the marker
`Shift.gmk aA` of stack `aA` onto stack `aB` (which reverses it back into the standard encoding
`pos :: bits ++ [iend]`) and then pops the sign glyph, leaving the bits of `h`, least significant
first, `iend`-terminated, on top of `aB`.  The cost is linear in `h.size`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib.evCA

open HvdH

/-- The encoding of a natural number contains no frame marker. -/
theorem noMark_enc_int_nat (h : ℕ) : Work.IntLib.Shift.NoMark (Val.enc (.int (h : ℤ))) := by
  have hnonneg : ¬ ((h : ℤ) < 0) := by
    have h0 : (0 : ℤ) ≤ (h : ℤ) := Int.natCast_nonneg h
    omega
  rw [Work.IntLib.enc_int, ite_eq_right hnonneg, Int.natAbs_natCast]
  intro g hg k
  rcases List.mem_cons.mp hg with hg | hg
  · rw [hg]; exact (Work.IntLib.Shift.gmk_ne_pos k).symm
  · rcases List.mem_append.mp hg with hg | hg
    · obtain ⟨b, _, rfl⟩ := List.mem_map.mp hg
      exact Work.IntLib.Shift.bit_ne_gmk k b
    · rw [List.mem_singleton.mp hg]; exact (Work.IntLib.Shift.gmk_ne_iend k).symm

/-- The reversed encoding of a natural number contains no frame marker. -/
theorem noMark_enc_rev (h : ℕ) : Work.IntLib.Shift.NoMark (Val.enc (.int (h : ℤ))).reverse :=
  fun g hg k => noMark_enc_int_nat h g (List.mem_reverse.mp hg) k

theorem readAEv (main : HvdH.Cmd) (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph)
    (h : ℕ) (As Bs : List HvdH.Glyph)
    (hA : X Work.IntLib.aA = (HvdH.Val.enc (.int (h : ℤ))).reverse ++ Work.IntLib.Shift.gmk Work.IntLib.aA :: As)
    (hB : X Work.IntLib.aB = Work.IntLib.Shift.gmk Work.IntLib.aB :: Bs) :
    ∃ (s' : HvdH.State) (n : ℕ),
      Work.Layout.Ev main Work.IntLib.EvC.readA ⟨g, X⟩ s' n ∧ n ≤ 5 * (h.size + 3) + 8 ∧
      s'.stk Work.IntLib.aA = Work.IntLib.Shift.gmk Work.IntLib.aA :: As ∧
      s'.stk Work.IntLib.aB = h.bits.map HvdH.Glyph.bit ++ [HvdH.Glyph.iend] ++ Work.IntLib.Shift.gmk Work.IntLib.aB :: Bs ∧
      (∀ j : HvdH.Stk, j ≠ Work.IntLib.aA → j ≠ Work.IntLib.aB → s'.stk j = X j) := by
  -- Drain the reversed encoding of `h` from `aA` onto `aB`.
  obtain ⟨s1, n1, hev1, hc1, _hreg1, hA1, hB1, hfr1⟩ :=
    Work.IntLib.Shift.drain_ev main Work.IntLib.aA Work.IntLib.aB
      (Work.IntLib.Shift.gmk Work.IntLib.aA) Work.IntLib.EvC.rGa Work.IntLib.EvC.rLa
      (by decide) (by decide)
      (HvdH.Val.enc (.int (h : ℤ))).reverse As
      (Work.IntLib.Shift.gmk Work.IntLib.aB :: Bs) g X
      (fun x hx => noMark_enc_rev h x hx Work.IntLib.aA) hA hB
  have hnonneg : ¬ ((h : ℤ) < 0) := by
    have h0 : (0 : ℤ) ≤ (h : ℤ) := Int.natCast_nonneg h
    omega
  -- `aB` now carries the standard encoding `pos :: bits ++ [iend]`.
  have hs1B : s1.stk Work.IntLib.aB =
      HvdH.Val.enc (.int (h : ℤ)) ++ Work.IntLib.Shift.gmk Work.IntLib.aB :: Bs := by
    rw [hB1, List.reverse_reverse]
  have hsec : HvdH.Val.enc (.int (h : ℤ)) =
      HvdH.Glyph.pos :: ((Computability.encodeNat h).map HvdH.Glyph.bit ++ [HvdH.Glyph.iend]) := by
    rw [Work.IntLib.enc_int, ite_eq_right hnonneg, Int.natAbs_natCast]
  have hhead : (s1.stk Work.IntLib.aB).headD HvdH.Glyph.eos = HvdH.Glyph.pos := by
    rw [hs1B, hsec]; rfl
  have htail : (s1.stk Work.IntLib.aB).tail =
      (Computability.encodeNat h).map HvdH.Glyph.bit ++ [HvdH.Glyph.iend] ++
        Work.IntLib.Shift.gmk Work.IntLib.aB :: Bs := by
    rw [hs1B, hsec]
    simp only [List.cons_append, List.tail_cons, List.append_assoc]
  -- Pop the sign glyph, leaving the bits of `h` on top of `aB`.
  have hpop : Work.Layout.Ev main (HvdH.Cmd.pop Work.IntLib.aB Work.IntLib.EvC.rGa) s1
      ⟨Function.update s1.reg Work.IntLib.EvC.rGa ((s1.stk Work.IntLib.aB).headD HvdH.Glyph.eos),
       Function.update s1.stk Work.IntLib.aB (s1.stk Work.IntLib.aB).tail⟩ 1 :=
    Work.Layout.ev_pop' main Work.IntLib.aB Work.IntLib.EvC.rGa s1.reg s1.stk
  have hreadA : Work.Layout.Ev main Work.IntLib.EvC.readA ⟨g, X⟩
      ⟨Function.update s1.reg Work.IntLib.EvC.rGa ((s1.stk Work.IntLib.aB).headD HvdH.Glyph.eos),
       Function.update s1.stk Work.IntLib.aB (s1.stk Work.IntLib.aB).tail⟩ (n1 + 1) := by
    have hd : Work.Layout.Ev main
        (Work.IntLib.Shift.drain Work.IntLib.aA Work.IntLib.aB
          (Work.IntLib.Shift.gmk Work.IntLib.aA) Work.IntLib.EvC.rGa Work.IntLib.EvC.rLa)
        ⟨g, X⟩ s1 n1 := ⟨n1, hev1, le_rfl⟩
    have hseqs : Work.Layout.Ev main
        (Work.Layout.seqs [HvdH.Cmd.pop Work.IntLib.aB Work.IntLib.EvC.rGa])
        s1 ⟨Function.update s1.reg Work.IntLib.EvC.rGa ((s1.stk Work.IntLib.aB).headD HvdH.Glyph.eos),
            Function.update s1.stk Work.IntLib.aB (s1.stk Work.IntLib.aB).tail⟩ 1 := hpop
    unfold Work.IntLib.EvC.readA
    exact Work.Layout.Ev.seqs_cons hd hseqs
  have hlen : ((HvdH.Val.enc (.int (h : ℤ))).reverse).length = h.size + 2 := by
    rw [List.length_reverse, Work.IntLib.vsz_int, Work.IntLib.isz_eq, Int.natAbs_natCast]
  refine ⟨⟨Function.update s1.reg Work.IntLib.EvC.rGa ((s1.stk Work.IntLib.aB).headD HvdH.Glyph.eos),
       Function.update s1.stk Work.IntLib.aB (s1.stk Work.IntLib.aB).tail⟩, n1 + 1,
    hreadA, ?_, ?_, ?_, ?_⟩
  · rw [hlen] at hc1; omega
  · show (Function.update s1.stk Work.IntLib.aB (s1.stk Work.IntLib.aB).tail) Work.IntLib.aA
        = Work.IntLib.Shift.gmk Work.IntLib.aA :: As
    rw [Function.update_of_ne (show Work.IntLib.aA ≠ Work.IntLib.aB by decide)
      (s1.stk Work.IntLib.aB).tail s1.stk]
    exact hA1
  · show (Function.update s1.stk Work.IntLib.aB (s1.stk Work.IntLib.aB).tail) Work.IntLib.aB
        = h.bits.map HvdH.Glyph.bit ++ [HvdH.Glyph.iend] ++ Work.IntLib.Shift.gmk Work.IntLib.aB :: Bs
    rw [Function.update_self, htail, Work.IntLib.encodeNat_eq_bits]
  · intro j hjA hjB
    show (Function.update s1.stk Work.IntLib.aB (s1.stk Work.IntLib.aB).tail) j = X j
    rw [Function.update_of_ne hjB ((s1.stk Work.IntLib.aB).tail) s1.stk]
    exact hfr1 j hjA hjB

end Work.IntLib.evCA
