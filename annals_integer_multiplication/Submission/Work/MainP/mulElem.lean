import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.ConvR.basic

/-!
# `Work.MainP.mulElem`: the pointwise product of two fixed-point complex numbers

Paper Corollary 2.10 (Lemma 2.9 for a single coordinate): multiply two coefficients of `C̃◦` and
leave the precision `p` (an `int` value sitting just under the two operands) in place, with scaled
error `< 2`.  The word is `KernelLib.pick 2` (copy `int p` to the top) followed by `FxLib.mulS`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.MainP

open HvdH

/-- One step of the pointwise product of two fixed-point complex vectors. -/
theorem mulElem (hK : HvdH.KernelLib) (hFx : HvdH.FxLib) :
    ∃ (q : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p : ℕ) (rest : List HvdH.Val) (a b : ℤ × ℤ),
      HvdH.inDisc p a → HvdH.inDisc p b →
      HvdH.WordR main q
        (fun vs => vs = HvdH.cfxVal a :: HvdH.cfxVal b :: HvdH.Val.int (p : ℤ) :: rest)
        (fun _ out => ∃ w : ℤ × ℤ, out = HvdH.cfxVal w :: HvdH.Val.int (p : ℤ) :: rest ∧
          HvdH.inDisc p w ∧ (2 : ℝ) ^ p * ‖HvdH.fxC p w - HvdH.fxC p a * HvdH.fxC p b‖ < 2)
        (fun _ => K * (p + 1) ^ 2) := by
  obtain ⟨pickP, Kp, hpk⟩ := hK.pick
  obtain ⟨mulSP, Km, hmul⟩ := hFx.mulS
  refine ⟨HvdH.Cmd.seq (pickP 2) mulSP, 100 * Kp + Km, ?_⟩
  intro main p rest a b ha hb
  have hva : HvdH.vsz (HvdH.cfxVal a) ≤ Work.ConvR.cfxSz p := Work.ConvR.vsz_cfxVal_le ha
  have hvb : HvdH.vsz (HvdH.cfxVal b) ≤ Work.ConvR.cfxSz p := Work.ConvR.vsz_cfxVal_le hb
  have hvp : HvdH.vsz (HvdH.Val.int (p : ℤ)) ≤ p + 2 := by
    rw [Work.ConvR.vsz_int, HvdH.isz, Int.natAbs_natCast]
    have : p.size ≤ p := Nat.size_le.mpr Nat.lt_two_pow_self
    omega
  -- step 1: copy `int p` to the top
  have h1 : Work.ConvR.WordC main (pickP 2)
      (fun vs => vs = HvdH.cfxVal a :: HvdH.cfxVal b :: HvdH.Val.int (p : ℤ) :: rest)
      (fun _ out => out = HvdH.Val.int (p : ℤ) :: HvdH.cfxVal a :: HvdH.cfxVal b ::
        HvdH.Val.int (p : ℤ) :: rest)
      (100 * Kp * (p + 1) ^ 2) := by
    refine hK.conseq main (pickP 2) (fun vs => 2 < vs.length)
      (fun vs => vs = HvdH.cfxVal a :: HvdH.cfxVal b :: HvdH.Val.int (p : ℤ) :: rest)
      (fun vs out => out = vs.getD 2 .nil :: vs)
      (fun _ out => out = HvdH.Val.int (p : ℤ) :: HvdH.cfxVal a :: HvdH.cfxVal b ::
        HvdH.Val.int (p : ℤ) :: rest)
      (fun vs => Kp * (2 + 1) * (((vs.take 3).map HvdH.vsz).sum + 1))
      (fun _ => 100 * Kp * (p + 1) ^ 2)
      (hpk main 2) ?_ ?_ ?_
    · intro vs hvs; rw [hvs]; simp
    · intro vs out hvs hout
      rw [hvs] at hout
      rw [hout]
      simp
    · intro vs hvs
      rw [hvs]
      have hsum0 : ((List.take 3 (HvdH.cfxVal a :: HvdH.cfxVal b ::
          HvdH.Val.int (p : ℤ) :: rest)).map HvdH.vsz).sum
          = HvdH.vsz (HvdH.cfxVal a) + HvdH.vsz (HvdH.cfxVal b) +
            HvdH.vsz (HvdH.Val.int (p : ℤ)) := by
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil]
        ring
      rw [hsum0]
      have hsum : HvdH.vsz (HvdH.cfxVal a) + HvdH.vsz (HvdH.cfxVal b) +
          HvdH.vsz (HvdH.Val.int (p : ℤ)) + 1 ≤ 5 * p + 19 := by
        have hc : Work.ConvR.cfxSz p = 2 * p + 8 := rfl
        rw [hc] at hva hvb
        omega
      have h3 : 3 * (5 * p + 19) ≤ 100 * (p + 1) ^ 2 := by nlinarith
      calc Kp * 3 * (HvdH.vsz (HvdH.cfxVal a) + HvdH.vsz (HvdH.cfxVal b) +
              HvdH.vsz (HvdH.Val.int (p : ℤ)) + 1)
          = Kp * (3 * (HvdH.vsz (HvdH.cfxVal a) + HvdH.vsz (HvdH.cfxVal b) +
              HvdH.vsz (HvdH.Val.int (p : ℤ)) + 1)) := by ring
        _ ≤ Kp * (3 * (5 * p + 19)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 3 hsum)
        _ ≤ Kp * (100 * (p + 1) ^ 2) := Nat.mul_le_mul_left _ h3
        _ = 100 * Kp * (p + 1) ^ 2 := by ring
  -- step 2: schoolbook product
  have h2 : Work.ConvR.WordC main mulSP
      (fun vs => vs = HvdH.Val.int (p : ℤ) :: HvdH.cfxVal a :: HvdH.cfxVal b ::
        HvdH.Val.int (p : ℤ) :: rest)
      (fun _ out => ∃ w : ℤ × ℤ, out = HvdH.cfxVal w :: HvdH.Val.int (p : ℤ) :: rest ∧
        HvdH.inDisc p w ∧ (2 : ℝ) ^ p * ‖HvdH.fxC p w - HvdH.fxC p a * HvdH.fxC p b‖ < 2)
      (Km * (p + 1) ^ 2) := by
    refine hK.conseq main mulSP
      (fun vs => ∃ (u v : ℤ × ℤ) (rest' : List HvdH.Val),
        vs = HvdH.Val.int (p : ℤ) :: HvdH.cfxVal u :: HvdH.cfxVal v :: rest' ∧
          HvdH.inDisc p u ∧ HvdH.inDisc p v)
      (fun vs => vs = HvdH.Val.int (p : ℤ) :: HvdH.cfxVal a :: HvdH.cfxVal b ::
        HvdH.Val.int (p : ℤ) :: rest)
      (fun vs out => ∃ (u v : ℤ × ℤ) (rest' : List HvdH.Val) (w : ℤ × ℤ),
        vs = HvdH.Val.int (p : ℤ) :: HvdH.cfxVal u :: HvdH.cfxVal v :: rest' ∧
          out = HvdH.cfxVal w :: rest' ∧ HvdH.inDisc p w ∧
            (2 : ℝ) ^ p * ‖HvdH.fxC p w - HvdH.fxC p u * HvdH.fxC p v‖ < 2)
      (fun _ out => ∃ w : ℤ × ℤ, out = HvdH.cfxVal w :: HvdH.Val.int (p : ℤ) :: rest ∧
        HvdH.inDisc p w ∧ (2 : ℝ) ^ p * ‖HvdH.fxC p w - HvdH.fxC p a * HvdH.fxC p b‖ < 2)
      (fun _ => Km * (p + 1) ^ 2) (fun _ => Km * (p + 1) ^ 2)
      (hmul main p) ?_ ?_ ?_
    · intro vs hvs
      exact ⟨a, b, HvdH.Val.int (p : ℤ) :: rest, hvs, ha, hb⟩
    · intro vs out hvs hq
      subst hvs
      obtain ⟨u, v, rest', w, hvs', hout, hw, herr⟩ := hq
      have he2 : HvdH.cfxVal a = HvdH.cfxVal u :=
        congrArg (fun (l : List HvdH.Val) => l.getD 1 .nil) hvs'
      have he3 : HvdH.cfxVal b = HvdH.cfxVal v :=
        congrArg (fun (l : List HvdH.Val) => l.getD 2 .nil) hvs'
      have hrest : HvdH.Val.int (p : ℤ) :: rest = rest' :=
        congrArg (fun (l : List HvdH.Val) => l.drop 3) hvs'
      have hua : u = a := by
        have h := he2
        simp only [HvdH.cfxVal, HvdH.Val.cons.injEq, HvdH.Val.int.injEq] at h
        exact Prod.ext h.1.symm h.2.symm
      have hvb : v = b := by
        have h := he3
        simp only [HvdH.cfxVal, HvdH.Val.cons.injEq, HvdH.Val.int.injEq] at h
        exact Prod.ext h.1.symm h.2.symm
      subst hua
      subst hvb
      rw [← hrest] at hout
      exact ⟨w, hout, hw, herr⟩
    · intro vs _
      exact le_rfl
  -- compose
  have hseq := Work.ConvR.WordC.seq hK h1 h2 (fun vs mid hvs hq => hq)
  refine Work.ConvR.WordC.conseq hK hseq (fun vs hvs => hvs) ?_ ?_
  · rintro vs out hvs ⟨mid, hmid, hq⟩
    exact hq
  · exact le_of_eq (by ring)

end Work.MainP
