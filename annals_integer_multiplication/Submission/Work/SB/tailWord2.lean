import Mathlib
import Submission.Work.Layout.SB.Specs
import Submission.Work.Layout.SB.Toolkit
import Submission.Work.SB.tailRaw

set_option autoImplicit false

namespace Work.SB

open HvdH
open Work.Layout

/-!
# `TailSpec2`: the raw tail with the corrected size hypotheses

This is `Work.SB.tailRaw_aux` with the two *value* size hypotheses of the corrected statement
`Work.Layout.TailSpec2` (each `≤ TailSpec2`'s own cost scale `tailTriple N L + 1`), and without
needing the `vsz (ofList (unslices A n B outs)) ≤ A*n*B*(L+3)+1` estimate: the size bound for
`xout` is exactly hypothesis `hQ2` of `TailSpec2`.
-/

/-- **The raw tail, corrected sizes.** `epilogue ; phase3b ; (roll 2, drop, roll 1, drop)`. -/
theorem tailWord2 (hK : HvdH.KernelLib) (hEpi : Work.Layout.EpilogueSpec)
    (hP3 : Work.Layout.Phase3bSpec) : Work.Layout.TailSpec2 := by
  obtain ⟨epiP, Kepi, hepi⟩ := hEpi
  obtain ⟨ph3P, Kph3, hph3⟩ := hP3
  obtain ⟨rmP, Krm, hrm⟩ := dropTwoUnder hK
  refine ⟨Cmd.seq epiP (Cmd.seq ph3P rmP), 1000 * (Kepi + Kph3 + Krm + 1), ?_⟩
  intro main g X R T1 A n B N L outs rest hAB hABn hlen hsl hslz hQ1 hQ2 hX0 hX1
  set flat : Val := ofList (outs.map ofList) with hflat
  set xout : Val := ofList (unslices A n B outs) with hxout
  -- size hypotheses in the local vocabulary
  have hQ1' : vsz flat + 1 ≤ tailTriple N L + 1 := by rw [hflat, tailTriple]; exact hQ1
  have hQ2' : vsz xout + 1 ≤ tailTriple N L + 1 := by rw [hxout, tailTriple]; exact hQ2
  -- ================= step 1: the epilogue =================
  obtain ⟨s1, N1, hE1, hN1, h01, h11, hfr1⟩ :=
    hepi main g X R T1 n B flat rest (by rw [hflat, hX0]) hX1
  obtain ⟨m1, he1, hl1⟩ := hE1
  -- ================= step 2: the output phase =================
  have hW3 := hph3 main A n B N L outs rest hAB hABn hlen hsl hslz
  obtain ⟨out3, s3, hQ3, hE3, h03, hfr3⟩ :=
    WordR.applyEv (h := hW3) (vs := flat :: Val.int (n : ℤ) :: Val.int (B : ℤ) :: rest)
      (hP := rfl) (g := s1.reg) (X := s1.stk) (R := R) (by rw [h01, hflat])
  obtain ⟨m3, he3, hl3⟩ := hE3
  -- ================= step 3: delete the two parameters =================
  obtain ⟨out4, s4, hQ4, hE4, h04, hfr4⟩ :=
    WordR.applyEv (h := hrm main xout n B rest)
      (vs := xout :: Val.int (n : ℤ) :: Val.int (B : ℤ) :: rest)
      (hP := rfl) (g := s3.reg) (X := s3.stk) (R := R) (by rw [h03, hQ3, hxout])
  obtain ⟨m4, he4, hl4⟩ := hE4
  -- ================= the cost estimate =================
  have hX1' : m1 ≤ 1000 * Kepi * (tailTriple N L + tailPair n B + 1) := by
    have hA1 : (vsz flat + 1) + isz (n : ℤ) + isz (B : ℤ) + 1
        ≤ 1000 * (tailTriple N L + tailPair n B + 1) := by
      rw [tailPair]
      omega
    calc m1 ≤ N1 := hl1
      _ ≤ Kepi * ((vsz flat + 1) + isz (n : ℤ) + isz (B : ℤ) + 1) := hN1
      _ ≤ Kepi * (1000 * (tailTriple N L + tailPair n B + 1)) := Nat.mul_le_mul_left Kepi hA1
      _ = 1000 * Kepi * (tailTriple N L + tailPair n B + 1) := by ring
  have hX3 : m3 ≤ 1000 * Kph3 * (tailTriple N L + tailPair n B + 1) := by
    have htail : tailTriple N L ≤ 1000 * (tailTriple N L + tailPair n B + 1) := by
      refine le_trans ?_ (le_thousand_mul _)
      omega
    calc m3 ≤ Kph3 * (N + 1) * (L + N.size + 1) * (N.size + 1) := hl3
      _ = Kph3 * tailTriple N L := by rw [tailTriple]; ring
      _ ≤ Kph3 * (1000 * (tailTriple N L + tailPair n B + 1)) := Nat.mul_le_mul_left Kph3 htail
      _ = 1000 * Kph3 * (tailTriple N L + tailPair n B + 1) := by ring
  have hX4 : m4 ≤ 1000 * Krm * (tailTriple N L + tailPair n B + 1) := by
    have hA4 : (vsz xout + 1) + isz (n : ℤ) + isz (B : ℤ) + 1
        ≤ 1000 * (tailTriple N L + tailPair n B + 1) := by
      rw [tailPair]
      omega
    calc m4 ≤ Krm * ((vsz xout + 1) + isz (n : ℤ) + isz (B : ℤ) + 1) := hl4
      _ ≤ Krm * (1000 * (tailTriple N L + tailPair n B + 1)) := Nat.mul_le_mul_left Krm hA4
      _ = 1000 * Krm * (tailTriple N L + tailPair n B + 1) := by ring
  have hK' : 1000 * Kepi + (1000 * Kph3 + 1000 * Krm) ≤ 1000 * (Kepi + Kph3 + Krm + 1) := by
    omega
  have htotal : m1 + (m3 + m4)
      ≤ 1000 * (Kepi + Kph3 + Krm + 1) * (tailTriple N L + tailPair n B + 1) := by
    have hsum : m1 + (m3 + m4)
        ≤ (1000 * Kepi + (1000 * Kph3 + 1000 * Krm))
          * (tailTriple N L + tailPair n B + 1) := by
      calc m1 + (m3 + m4)
          ≤ 1000 * Kepi * (tailTriple N L + tailPair n B + 1)
            + (1000 * Kph3 * (tailTriple N L + tailPair n B + 1)
              + 1000 * Krm * (tailTriple N L + tailPair n B + 1)) :=
            add_le_add hX1' (add_le_add hX3 hX4)
        _ = (1000 * Kepi + (1000 * Kph3 + 1000 * Krm))
            * (tailTriple N L + tailPair n B + 1) := by ring
    calc m1 + (m3 + m4)
        ≤ (1000 * Kepi + (1000 * Kph3 + 1000 * Krm))
          * (tailTriple N L + tailPair n B + 1) := hsum
      _ ≤ 1000 * (Kepi + Kph3 + Krm + 1) * (tailTriple N L + tailPair n B + 1) :=
          Nat.mul_le_mul_right _ hK'
  -- ================= the result =================
  refine ⟨s4, m1 + (m3 + m4), ?_, ?_, ?_, ?_, ?_⟩
  · exact Ev.seq ⟨m1, he1, le_rfl⟩ (Ev.seq ⟨m3, he3, le_rfl⟩ ⟨m4, he4, le_rfl⟩)
  · simpa only [tailTriple, tailPair] using htotal
  · rw [h04, hQ4, hxout]
  · rw [hfr4 (1 : Stk) (by decide), hfr3 (1 : Stk) (by decide), h11]
  · intro k hk0 hk1
    rw [hfr4 k hk0, hfr3 k hk0]
    exact hfr1 k hk0 hk1

end Work.SB
