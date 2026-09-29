import Mathlib
import Submission.Work.Layout.SB.Toolkit
import Submission.Work.Layout.SB.Specs
import Submission.Work.ConvR.dropUnder
import Submission.Work.SB.RawOps.vszUnslicesLe

set_option autoImplicit false

namespace Work.SB

open HvdH
open Work.Layout

/-!
# The raw tail of the sort-based `applyAlong` (`Work.Layout.TailSpec`)

Given the epilogue (`EpilogueSpec`, which parks `int B` and `int n` under the working list) and
the non-degenerate output phase (`Phase3bSpec`, which sorts the labelled flat list back into the
`A × n × B` layout), the tail is

```
epilogue ; phase3b ; (roll 2, drop, roll 1, drop)
```

i.e. fetch the two parameters from stack 1, run the output phase, and finally delete the two
parameters again so that stack 0 carries only `ofList (unslices A n B outs)`.

The last two costs are bounded by the *value hypothesis* on the slices: every entry of
`unslices A n B outs` is either an entry of one of the slices (size `≤ L`) or the default value
(size `2`), so its size is at most `L + 2`.
-/

/-- The phase-3 cost scale `(N+1) * (L + N.size + 1) * (N.size + 1)`. -/
def tailTriple (N L : ℕ) : ℕ := (N + 1) * (L + N.size + 1) * (N.size + 1)

/-- `isz n + isz B`: the size of the two dropped parameters. -/
def tailPair (n B : ℕ) : ℕ := isz (n : ℤ) + isz (B : ℤ)

/-- `a ≤ 1000 * a`. -/
theorem le_thousand_mul (a : ℕ) : a ≤ 1000 * a := by
  calc a = a * 1 := (Nat.mul_one a).symm
    _ ≤ a * 1000 := Nat.mul_le_mul_left a (by norm_num)
    _ = 1000 * a := by ring

/-- `vsz (.int z) = isz z`. -/
theorem vsz_int_val (z : ℤ) : vsz (Val.int z) = isz z := Work.ConvR.vsz_int z

/-- The word deleting the two values just below the top (`x :: int n :: int B :: rest ↦ x :: rest`),
obtained from the generic `Work.ConvR.dropUnder`. -/
theorem dropTwoUnder (hK : HvdH.KernelLib) :
    ∃ (p : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (x : HvdH.Val) (n B : ℕ) (rest : List HvdH.Val),
      HvdH.WordR main p
        (fun vs => vs = x :: Val.int (n : ℤ) :: Val.int (B : ℤ) :: rest)
        (fun _ out => out = x :: rest)
        (fun _ => K * ((vsz x + 1) + isz (n : ℤ) + isz (B : ℤ) + 1)) := by
  obtain ⟨prog, KC, hprog⟩ := Work.ConvR.dropUnder hK
  refine ⟨prog, KC, ?_⟩
  intro main x n B rest
  refine hK.conseq main prog
    (fun vs => vs = x :: Val.int (n : ℤ) :: Val.int (B : ℤ) :: rest)
    (fun vs => vs = x :: Val.int (n : ℤ) :: Val.int (B : ℤ) :: rest)
    (fun _ out => out = x :: rest)
    (fun _ out => out = x :: rest)
    (fun _ => KC * (vsz x + vsz (Val.int (n : ℤ)) + vsz (Val.int (B : ℤ)) + 1))
    (fun _ => KC * ((vsz x + 1) + isz (n : ℤ) + isz (B : ℤ) + 1))
    (hprog main x (Val.int (n : ℤ)) (Val.int (B : ℤ)) rest)
    (fun vs h => h) (fun vs out _ h => h) ?_
  intro vs _
  rw [vsz_int_val, vsz_int_val]
  exact Nat.mul_le_mul_left _ (by omega)

/-- **The raw tail.**  `epilogue ; phase3b ; (roll 2, drop, roll 1, drop)`. -/
theorem tailRaw_aux (hK : HvdH.KernelLib) (hFl : FlattenSpec) (hEpi : EpilogueSpec)
    (hP3 : Phase3bSpec)
    (hsize : ∀ (A n B : ℕ) (outs : List (List Val)) (L : ℕ),
      outs.length = A * B → (∀ s, s < A * B → (outs.getD s []).length = n) →
      (∀ s, s < A * B → ∀ y ∈ outs.getD s [], vsz y ≤ L) →
      vsz (ofList (unslices A n B outs)) ≤ A * n * B * (L + 3) + 1) :
    TailSpec := by
  obtain ⟨epiP, Kepi, hepi⟩ := hEpi
  obtain ⟨ph3P, Kph3, hph3⟩ := hP3
  obtain ⟨rmP, Krm, hrm⟩ := dropTwoUnder hK
  refine ⟨Cmd.seq epiP (Cmd.seq ph3P rmP), 1000 * (Kepi + Kph3 + Krm + 1), ?_⟩
  intro main g X R T1 A n B N L outs rest hAB hABn hlen hsl hslz hQ1 _hQ2 hX0 hX1
  set flat : Val := ofList (outs.map ofList) with hflat
  set xout : Val := ofList (unslices A n B outs) with hxout
  -- size hypotheses in the local vocabulary
  have hQ1' : vsz flat + 1 ≤ (N + 1) * (L + 1) := by rw [hflat]; exact hQ1
  have hxs : vsz xout ≤ A * n * B * (L + 3) + 1 := by rw [hxout]; exact hsize A n B outs L hlen hsl hslz
  have hQleP : (N + 1) * (L + 1) ≤ tailTriple N L := by
    rw [tailTriple]
    have h1 : L + 1 ≤ L + N.size + 1 := by omega
    have h2 : 1 ≤ N.size + 1 := by omega
    calc (N + 1) * (L + 1) ≤ (N + 1) * (L + N.size + 1) := Nat.mul_le_mul_left _ h1
      _ = (N + 1) * (L + N.size + 1) * 1 := (Nat.mul_one _).symm
      _ ≤ (N + 1) * (L + N.size + 1) * (N.size + 1) := Nat.mul_le_mul_left _ h2
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
  have hAnB : A * n * B ≤ N := by
    have h : A * n * B = A * B * n := by ring
    rw [h]; exact hABn
  have hVx1000 : vsz xout + 1 ≤ 1000 * tailTriple N L := by
    have h2 : A * n * B * (L + 3) ≤ N * (L + 3) := Nat.mul_le_mul_right _ hAnB
    have h3 : N * (L + 3) + 2 ≤ 4 * ((N + 1) * (L + 1)) := by
      nlinarith [Nat.zero_le N, Nat.zero_le L]
    calc vsz xout + 1 ≤ N * (L + 3) + 2 := by omega
      _ ≤ 4 * ((N + 1) * (L + 1)) := h3
      _ ≤ 4 * tailTriple N L := Nat.mul_le_mul_left 4 hQleP
      _ ≤ 1000 * tailTriple N L := Nat.mul_le_mul_right _ (by norm_num)
  have hX1 : m1 ≤ 1000 * Kepi * (tailTriple N L + tailPair n B + 1) := by
    have hA1 : (vsz flat + 1) + isz (n : ℤ) + isz (B : ℤ) + 1
        ≤ 1000 * (tailTriple N L + tailPair n B + 1) := by
      have hV : vsz flat + 1 ≤ tailTriple N L := le_trans hQ1' hQleP
      have h3 : isz (n : ℤ) + isz (B : ℤ) + 1 ≤ 1000 * (tailPair n B + 1) := by
        rw [tailPair]; exact le_thousand_mul _
      calc (vsz flat + 1) + isz (n : ℤ) + isz (B : ℤ) + 1
          = (vsz flat + 1) + (isz (n : ℤ) + isz (B : ℤ) + 1) := by ring
        _ ≤ tailTriple N L + 1000 * (tailPair n B + 1) := add_le_add hV h3
        _ ≤ 1000 * tailTriple N L + 1000 * (tailPair n B + 1) := by
            have := le_thousand_mul (tailTriple N L); omega
        _ = 1000 * (tailTriple N L + tailPair n B + 1) := by ring
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
      have hq : isz (n : ℤ) + isz (B : ℤ) + 1 ≤ 1000 * (tailPair n B + 1) := by
        rw [tailPair]; exact le_thousand_mul _
      calc (vsz xout + 1) + isz (n : ℤ) + isz (B : ℤ) + 1
          = (vsz xout + 1) + (isz (n : ℤ) + isz (B : ℤ) + 1) := by ring
        _ ≤ 1000 * tailTriple N L + 1000 * (tailPair n B + 1) := add_le_add hVx1000 hq
        _ = 1000 * (tailTriple N L + tailPair n B + 1) := by ring
    calc m4 ≤ Krm * ((vsz xout + 1) + isz (n : ℤ) + isz (B : ℤ) + 1) := hl4
      _ ≤ Krm * (1000 * (tailTriple N L + tailPair n B + 1)) := Nat.mul_le_mul_left Krm hA4
      _ = 1000 * Krm * (tailTriple N L + tailPair n B + 1) := by ring
  have hK' : 1000 * Kepi + (1000 * Kph3 + 1000 * Krm) ≤ 1000 * (Kepi + Kph3 + Krm + 1) := by omega
  have htotal : m1 + (m3 + m4)
      ≤ 1000 * (Kepi + Kph3 + Krm + 1) * (tailTriple N L + tailPair n B + 1) := by
    have hsum : m1 + (m3 + m4)
        ≤ (1000 * Kepi + (1000 * Kph3 + 1000 * Krm))
          * (tailTriple N L + tailPair n B + 1) := by
      calc m1 + (m3 + m4)
          ≤ 1000 * Kepi * (tailTriple N L + tailPair n B + 1)
            + (1000 * Kph3 * (tailTriple N L + tailPair n B + 1)
              + 1000 * Krm * (tailTriple N L + tailPair n B + 1)) := add_le_add hX1 (add_le_add hX3 hX4)
        _ = (1000 * Kepi + (1000 * Kph3 + 1000 * Krm))
            * (tailTriple N L + tailPair n B + 1) := by ring
    calc m1 + (m3 + m4)
        ≤ (1000 * Kepi + (1000 * Kph3 + 1000 * Krm)) * (tailTriple N L + tailPair n B + 1) := hsum
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

theorem tailRaw (hK : HvdH.KernelLib) (hFl : FlattenSpec) (hEpi : EpilogueSpec)
    (hP3 : Phase3bSpec) : TailSpec :=
  tailRaw_aux hK hFl hEpi hP3 Work.SB.RawOps.vszUnslicesLe

end Work.SB
