import Mathlib
import Submission.Work.Resample.buQWpostDefs
import Submission.Work.Resample.buQWelemShr
import Submission.Work.Resample.buQWelemKit

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Resample

open HvdH
open Work.Main.word

/-- **Element word for the division by `2^p` inside a `mapList`.**

Consume the pair `cfxVal a` at the top of the value stack, divide both coordinates by `2^p`, and
leave the value `Val.int (p : ℤ)` (which sits just below it, directly above the fixed tail `T`) in
place, i.e. `cfxVal a :: int p :: T  ↦  cfxVal (a₁ /ᵗ 2^p, a₂ /ᵗ 2^p) :: int p :: T`.

Suggested program: `KL.pick 1 ;;; KL.roll 1 ;;; <the 8-step division program of
`Work.Resample.buQWelemShr>` (`uncP ;;; pickP 2 ;;; rollP 2 ;;; shrP ;;; rollP 2 ;;; rollP 2 ;;; shrP
;;; consP`).  The leading `pick 1 ;;; roll 1` duplicates `int p` on top of the pair, so that the
division program (which *consumes* its `pp`) leaves the original `int p` in the tail; the composed
cost is of the form `Kc·(P+1)`.  (`Work.Resample.buQWelemKit` has the `Pipe` adapters
`bu_pickK`/`bu_rollK`/`bu_unconsTail`/`bu_binOpTail`/`bu_consTail` used by `buQWelemShr`.) -/
theorem buPostShrElem (KL : HvdH.KernelLib) (IL : HvdH.IntLib) :
    ∃ (q : HvdH.Cmd) (Kc : ℕ),
    ∀ (main : HvdH.Cmd) (P p : ℕ) (a : ℤ × ℤ) (T : List HvdH.Val),
      HvdH.isz a.1 ≤ P → HvdH.isz a.2 ≤ P → HvdH.isz (p : ℤ) ≤ P →
      HvdH.WordR main q
        (fun vs => vs = HvdH.cfxVal a :: HvdH.Val.int (p : ℤ) :: T)
        (fun vs out => vs = HvdH.cfxVal a :: HvdH.Val.int (p : ℤ) :: T ∧
          out = HvdH.cfxVal (Int.tdiv a.1 ((2 : ℤ) ^ p),
            Int.tdiv a.2 ((2 : ℤ) ^ p)) :: HvdH.Val.int (p : ℤ) :: T)
        (fun _ => Kc * (P + 1)) := by
  obtain ⟨shrP, Ksh, hshr⟩ := buQWelemShr KL IL
  obtain ⟨pickP, KP, hpick⟩ := KL.pick
  obtain ⟨rollP, KR, hroll⟩ := KL.roll
  refine ⟨HvdH.Cmd.seq (HvdH.Cmd.seq (pickP 1) (rollP 1)) shrP, 120 * KP + 120 * KR + Ksh, ?_⟩
  intro main P p a T ha1 ha2 hpp
  -- sizes of every window entry
  have e_a : vsz (HvdH.cfxVal a) ≤ 3 * P + 4 := by
    simpa [HvdH.cfxVal] using vsz_cfxVal_le (x := a.1) (y := a.2) ha1 ha2
  have e_p : vsz (Val.int (p : ℤ)) ≤ 3 * P + 4 := by rw [vsz_int]; omega
  have hM2 : ∀ v ∈ ([HvdH.cfxVal a, Val.int (p : ℤ)] : List Val), vsz v ≤ 3 * P + 4 := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact e_a
    · exact e_p
  have hM3 : ∀ v ∈ ([Val.int (p : ℤ), HvdH.cfxVal a, Val.int (p : ℤ)] : List Val),
      vsz v ≤ 3 * P + 4 := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact e_p
    · exact e_a
    · exact e_p
  -- step 1: duplicate `int p` on top of the pair
  have HA : Pipe main (pickP 1) [HvdH.cfxVal a, Val.int (p : ℤ)]
      [Val.int (p : ℤ), HvdH.cfxVal a, Val.int (p : ℤ)] (120 * KP * (P + 1)) :=
    bu_pickK main hpick (A := [HvdH.cfxVal a, Val.int (p : ℤ)]) (k := 1) (P := P)
      (by simp) (by omega) hM2
  -- step 2: move the pair back on top of the two `int p`s
  have HB : Pipe main (rollP 1) [Val.int (p : ℤ), HvdH.cfxVal a, Val.int (p : ℤ)]
      [HvdH.cfxVal a, Val.int (p : ℤ), Val.int (p : ℤ)] (120 * KR * (P + 1)) :=
    bu_rollK main hroll (A := [Val.int (p : ℤ), HvdH.cfxVal a, Val.int (p : ℤ)]) (k := 1)
      (P := P) (by simp) (by omega) hM3
  -- step 3: the `buQWelemShr` program, on the window `[cfxVal a, int p]`
  have HC0 : Pipe main shrP [HvdH.cfxVal a, Val.int (p : ℤ)]
      [HvdH.cfxVal (Int.tdiv a.1 ((2 : ℤ) ^ p), Int.tdiv a.2 ((2 : ℤ) ^ p))]
      (Ksh * (P + 1)) := by
    intro rest vs hvs s R hR
    have hpre : vs = HvdH.cfxVal a :: Val.int (p : ℤ) :: rest := by rw [hvs]; rfl
    obtain ⟨out, s', n, ⟨rest', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
      hshr main P p a ha1 ha2 hpp vs ⟨rest, hpre⟩ s R hR
    have h1 := List.cons.inj (hvs'.symm.trans hpre)
    have hrest : rest' = rest := (List.cons.inj h1.2).2
    refine ⟨out, s', n, ?_, hev, hn, hstk, hoth⟩
    rw [hout, hrest]
    rfl
  have HC : Pipe main shrP [HvdH.cfxVal a, Val.int (p : ℤ), Val.int (p : ℤ)]
      [HvdH.cfxVal (Int.tdiv a.1 ((2 : ℤ) ^ p), Int.tdiv a.2 ((2 : ℤ) ^ p)),
        Val.int (p : ℤ)] (Ksh * (P + 1)) :=
    Pipe.appendTail [Val.int (p : ℤ)] HC0
  have HAB : Pipe main (HvdH.Cmd.seq (pickP 1) (rollP 1)) [HvdH.cfxVal a, Val.int (p : ℤ)]
      [HvdH.cfxVal a, Val.int (p : ℤ), Val.int (p : ℤ)]
      (120 * KP * (P + 1) + 120 * KR * (P + 1)) := Pipe.comp HA HB
  have HABC : Pipe main (HvdH.Cmd.seq (HvdH.Cmd.seq (pickP 1) (rollP 1)) shrP)
      [HvdH.cfxVal a, Val.int (p : ℤ)]
      [HvdH.cfxVal (Int.tdiv a.1 ((2 : ℤ) ^ p), Int.tdiv a.2 ((2 : ℤ) ^ p)),
        Val.int (p : ℤ)] (120 * KP * (P + 1) + 120 * KR * (P + 1) + Ksh * (P + 1)) :=
    Pipe.comp HAB HC
  have hsum : 120 * KP * (P + 1) + 120 * KR * (P + 1) + Ksh * (P + 1)
      = (120 * KP + 120 * KR + Ksh) * (P + 1) := by ring
  have Hfin : Pipe main (HvdH.Cmd.seq (HvdH.Cmd.seq (pickP 1) (rollP 1)) shrP)
      [HvdH.cfxVal a, Val.int (p : ℤ)]
      [HvdH.cfxVal (Int.tdiv a.1 ((2 : ℤ) ^ p), Int.tdiv a.2 ((2 : ℤ) ^ p)),
        Val.int (p : ℤ)] ((120 * KP + 120 * KR + Ksh) * (P + 1)) :=
    Pipe.le HABC (le_of_eq hsum)
  intro vs hvs s R hR
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := Hfin T vs (by rw [hvs]; rfl) s R hR
  exact ⟨out, s', n, ⟨hvs, by rw [hout]; rfl⟩, hev, hn, hstk, hoth⟩

end Work.Resample
