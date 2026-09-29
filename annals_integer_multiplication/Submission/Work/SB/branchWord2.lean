import Mathlib
import Submission.Work.Kernel.Raw
import Submission.Work.Resample.sliceA1prepW
import Submission.Work.Layout.SB.Toolkit
import Submission.Work.Layout.SB.Specs
import Submission.Work.SB.BW2.Defs
import Submission.Work.SB.slicesFacts
import Submission.Work.SB.phase1
import Submission.Work.SB.BW2.degWord
import Submission.Work.SB.BW2.bgenWord
import Submission.Work.SB.BW2.sizeKit

/-!
# `Work.SB.branchWord2` — the slices step of `applyAlong` (paper Lemma 2.11, branch `brP`)

The word takes the value list

`ofList es :: int m :: int B :: int A :: rest`

to the value list `ofList ((slices A m B es).map ofList) :: rest`, where `es` is a flat array of
shape `A × m × B` and `slices A m B es` is its list of `A*B` slices of length `m`.

It is assembled from the three *forced* branches proved in the sibling files

* `Work.SB.BW2.degWord`   (`m = 0`):   `slices A 0 B es = replicate (A*B) []`,
* `Work.SB.BW2.bzeroWord` (`B = 0`, proved below): `A*B = 0`, `es = []`, answer `nil`,
* `Work.SB.BW2.bgenWord`  (`0 < m`, `B ≠ 0`): `phase1` then `chunksOf m`,

glued by two `KernelLib.ifZero` dispatches.  Both dispatches test a *copy* (`KernelLib.pick`) of
the integer they branch on, so that the value list below is left untouched and the branch programs
are free of static parameters.  The two integers dropped by the branches are paid for by the
`isz` part `K*(isz A + isz m + isz B)` of the bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.SB.BW2

open HvdH
open Work.Layout

/-! ## Elementary size facts -/

theorem bw_vsz_int (z : ℤ) : vsz (.int z) = isz z := Work.IntLib.vsz_int z

theorem bw_vsz_nil : vsz (Val.nil : Val) = 1 := rfl

theorem map_take1p1_sum (a b : Val) (l : List Val) :
    (List.map vsz (List.take (1 + 1) (a :: b :: l))).sum = vsz a + vsz b := by simp

theorem map_take2p1_sum (a b c : Val) (l : List Val) :
    (List.map vsz (List.take (2 + 1) (a :: b :: c :: l))).sum = vsz a + (vsz b + vsz c) := by simp

theorem max_le_add (a b : ℕ) : max a b ≤ a + b :=
  max_le (Nat.le_add_right a b) (Nat.le_add_left b a)

/-- the exit condition of `branchWord2`, as a one-argument predicate (for `KernelLib.ifZero`) -/
abbrev SlicesPost (A m B : ℕ) (es rest : List Val) : List Val → Prop :=
  fun out => ∃ sls : List (List Val), out = ofList (sls.map ofList) :: rest ∧ sls = slices A m B es

/-! ## The fourfold `drop` word (`B = 0` branch) -/

/-- four copies of `KernelLib.drop`, then `skip` -/
def dropFourProg (d : Cmd) : Cmd := .seq d (.seq d (.seq d (.seq d .skip)))

/-- **`B = 0` branch.**  Here `A*B = 0` and `es = []`, so all four values on top are dropped and
`nil` is pushed; the result is `ofList (slices A m B es) = nil`. -/
theorem bzeroWord (hK : KernelLib) :
    ∃ (p : Cmd) (K : ℕ), ∀ (main : Cmd) (A m B N L : ℕ) (es rest : List Val),
      B = 0 → A * B ≤ N → A * m * B ≤ N → es.length = A * m * B → (∀ x ∈ es, vsz x ≤ L) →
      WordR main p (Pre A m B es rest) (Post A m B es rest)
        (fun _ => K * BIG N L + K * S A m B) := by
  obtain ⟨dropP, Kdrop, hdrop⟩ := hK.drop
  obtain ⟨pushP, Kpush, hpush⟩ := hK.pushVal
  refine ⟨.seq (dropFourProg dropP) (pushP Val.nil), 100 * (Kdrop + Kpush + 1), ?_⟩
  intro main A m B N L es rest hB hAB hAmB hlen hv
  obtain ⟨hone, hvszE, -, hiszA, hiszM, hiszB, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    sizeKit A m B N L es hAB hAmB hlen hv
  have hes : es = [] := by
    have h0 : es.length = 0 := by rw [hlen, hB, Nat.mul_zero]
    cases es with
    | nil => rfl
    | cons x t => simp at h0
  have hsl : slices A m B es = [] := by
    rw [hes, hB]
    simp [HvdH.slices]
  have hd4 : WordR main (dropFourProg dropP)
      (fun vs => vs = ofList es :: .int (m : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest)
      (fun _ out => out = rest)
      (fun _ => (Kdrop + 1) *
        ((List.map vsz [ofList es, .int (m : ℤ), .int (B : ℤ), .int (A : ℤ)]).sum + 5)) :=
    Work.Resample.prepWDropAll (main := main) (progD := dropP) (Kd := Kdrop) (hdrop main)
      [ofList es, .int (m : ℤ), .int (B : ℤ), .int (A : ℤ)] rest
  have hpushNil : WordR main (pushP Val.nil) (fun _ => True) (fun vs out => out = Val.nil :: vs)
      (fun _ => Kpush * (vsz Val.nil + 1)) := hpush main Val.nil
  have hcomp := Work.Kernel.WordR_seq hd4 hpushNil
    (B := fun _ => Kpush * (vsz Val.nil + 1)) (fun vs mid _ hmid => ⟨trivial, le_rfl⟩)
  refine Work.Kernel.WordR_conseq hcomp ?_ ?_ ?_
  · intro vs hvs; exact hvs
  · intro vs out _ hq
    obtain ⟨mid, hmid, hout⟩ := hq
    refine ⟨[], ?_, ?_⟩
    · rw [hout, hmid]; rfl
    · exact hsl.symm
  · intro vs hvs
    have hD : (List.map vsz [ofList es, .int (m : ℤ), .int (B : ℤ), .int (A : ℤ)]).sum
        = vsz (ofList es) + isz (m : ℤ) + isz (B : ℤ) + isz (A : ℤ) := by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        Nat.add_assoc, bw_vsz_int]
    have hsum : vsz (ofList es) + isz (m : ℤ) + isz (B : ℤ) + isz (A : ℤ)
        ≤ BW2.BIG N L + 3 * BW2.S A m B := by omega
    have h9 : (List.map vsz [ofList es, .int (m : ℤ), .int (B : ℤ), .int (A : ℤ)]).sum + 5
        ≤ 9 * (BW2.BIG N L + BW2.S A m B) := by
      rw [hD]
      nlinarith [hone, hsum]
    have h2 : Kpush * (vsz Val.nil + 1) ≤ 2 * Kpush * (BW2.BIG N L + BW2.S A m B) := by
      rw [bw_vsz_nil]
      calc Kpush * (1 + 1) = 2 * Kpush * 1 := by ring
        _ ≤ 2 * Kpush * (BW2.BIG N L + BW2.S A m B) := Nat.mul_le_mul_left _ hone
    have hcoef : (Kdrop + 1) * 9 + 2 * Kpush ≤ 100 * (Kdrop + Kpush + 1) := by omega
    calc (Kdrop + 1) * ((List.map vsz [ofList es, .int (m : ℤ), .int (B : ℤ), .int (A : ℤ)]).sum + 5)
          + Kpush * (vsz Val.nil + 1)
        ≤ (Kdrop + 1) * (9 * (BW2.BIG N L + BW2.S A m B)) + Kpush * (vsz Val.nil + 1) :=
          Nat.add_le_add_right (Nat.mul_le_mul_left (Kdrop + 1) h9) _
      _ ≤ (Kdrop + 1) * (9 * (BW2.BIG N L + BW2.S A m B)) + 2 * Kpush * (BW2.BIG N L + BW2.S A m B) :=
          Nat.add_le_add_left h2 _
      _ = ((Kdrop + 1) * 9 + 2 * Kpush) * (BW2.BIG N L + BW2.S A m B) := by ring
      _ ≤ 100 * (Kdrop + Kpush + 1) * (BW2.BIG N L + BW2.S A m B) :=
          Nat.mul_le_mul_right _ hcoef
      _ = 100 * (Kdrop + Kpush + 1) * BW2.BIG N L + 100 * (Kdrop + Kpush + 1) * BW2.S A m B := by ring

/-! ## The final arithmetic of the assembly -/

theorem finalArith (Kpick Kifz Kdeg Kbz Kbg A m B N L : ℕ)
    (hM : isz (m : ℤ) + 1 ≤ 2 * (BIG N L + S A m B))
    (hB2 : isz (B : ℤ) + 1 ≤ 2 * (BIG N L + S A m B)) :
    4 * Kpick * (BIG N L + S A m B)
        + (Kifz * (isz (m : ℤ) + 1) + max (Kdeg * (BIG N L + S A m B))
            (6 * Kpick * (BIG N L + S A m B) + (Kifz * (isz (B : ℤ) + 1)
              + max (Kbz * (BIG N L + S A m B)) (Kbg * (BIG N L + S A m B)))))
      ≤ 100 * (Kpick + Kifz + Kdeg + Kbz + Kbg + 1) * (BIG N L + S A m B) := by
  have h1 : Kifz * (isz (m : ℤ) + 1) ≤ Kifz * (2 * (BIG N L + S A m B)) :=
    Nat.mul_le_mul_left Kifz hM
  have h2 : Kifz * (isz (B : ℤ) + 1) ≤ Kifz * (2 * (BIG N L + S A m B)) :=
    Nat.mul_le_mul_left Kifz hB2
  have hmax1 : max (Kbz * (BIG N L + S A m B)) (Kbg * (BIG N L + S A m B))
      ≤ Kbz * (BIG N L + S A m B) + Kbg * (BIG N L + S A m B) := max_le_add _ _
  have hmax2 : max (Kdeg * (BIG N L + S A m B))
      (6 * Kpick * (BIG N L + S A m B) + (Kifz * (isz (B : ℤ) + 1)
        + max (Kbz * (BIG N L + S A m B)) (Kbg * (BIG N L + S A m B))))
      ≤ Kdeg * (BIG N L + S A m B)
        + (6 * Kpick * (BIG N L + S A m B) + (Kifz * (isz (B : ℤ) + 1)
          + max (Kbz * (BIG N L + S A m B)) (Kbg * (BIG N L + S A m B)))) := max_le_add _ _
  have hinn : 6 * Kpick * (BIG N L + S A m B)
      + (Kifz * (isz (B : ℤ) + 1) + max (Kbz * (BIG N L + S A m B)) (Kbg * (BIG N L + S A m B)))
      ≤ 6 * Kpick * (BIG N L + S A m B)
        + (Kifz * (2 * (BIG N L + S A m B)) + (Kbz * (BIG N L + S A m B)
          + Kbg * (BIG N L + S A m B))) :=
    Nat.add_le_add_left (Nat.add_le_add h2 hmax1) _
  have houter : max (Kdeg * (BIG N L + S A m B))
      (6 * Kpick * (BIG N L + S A m B) + (Kifz * (isz (B : ℤ) + 1)
        + max (Kbz * (BIG N L + S A m B)) (Kbg * (BIG N L + S A m B))))
      ≤ Kdeg * (BIG N L + S A m B)
        + (6 * Kpick * (BIG N L + S A m B) + (Kifz * (2 * (BIG N L + S A m B))
          + (Kbz * (BIG N L + S A m B) + Kbg * (BIG N L + S A m B)))) :=
    le_trans hmax2 (Nat.add_le_add_left hinn _)
  have hcoef : 10 * Kpick + 4 * Kifz + Kdeg + Kbz + Kbg
      ≤ 100 * (Kpick + Kifz + Kdeg + Kbz + Kbg + 1) := by omega
  calc 4 * Kpick * (BIG N L + S A m B)
        + (Kifz * (isz (m : ℤ) + 1) + max (Kdeg * (BIG N L + S A m B))
            (6 * Kpick * (BIG N L + S A m B) + (Kifz * (isz (B : ℤ) + 1)
              + max (Kbz * (BIG N L + S A m B)) (Kbg * (BIG N L + S A m B)))))
      ≤ 4 * Kpick * (BIG N L + S A m B)
        + (Kifz * (2 * (BIG N L + S A m B)) + (Kdeg * (BIG N L + S A m B)
          + (6 * Kpick * (BIG N L + S A m B) + (Kifz * (2 * (BIG N L + S A m B))
            + (Kbz * (BIG N L + S A m B) + Kbg * (BIG N L + S A m B)))))) :=
        Nat.add_le_add_left (Nat.add_le_add h1 houter) _
    _ = (10 * Kpick + 4 * Kifz + Kdeg + Kbz + Kbg) * (BIG N L + S A m B) := by ring
    _ ≤ 100 * (Kpick + Kifz + Kdeg + Kbz + Kbg + 1) * (BIG N L + S A m B) :=
        Nat.mul_le_mul_right _ hcoef

end Work.SB.BW2

namespace Work.SB

open HvdH
open Work.Layout

/-- **the `isz B` form of the `branchWord2` bound** (the statement of `Work.Layout.Branch2Spec`):
the slices step, assembled from the three forced branches. -/
theorem branchWord2_isz (hK : HvdH.KernelLib) (hI : HvdH.IntLib) (hCh : ChunksSpec)
    (hRp : ReplicateSpec) (hP1 : Phase1Spec) :
    ∃ (p : Cmd) (K : ℕ), ∀ (main : Cmd) (A m B N L : ℕ) (es : List Val) (rest : List Val),
      A * B ≤ N → A * m * B ≤ N → es.length = A * m * B → (∀ x ∈ es, vsz x ≤ L) →
      WordR main p
        (fun vs => vs = ofList es :: .int (m : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest)
        (fun _ out => ∃ sls : List (List Val), out = ofList (sls.map ofList) :: rest ∧
          sls = slices A m B es)
        (fun _ => K * (N + 1) * (L + N.size + 1) * (N.size + 1) + K * (isz A + isz m + isz B)) := by
  obtain ⟨degP, Kdeg, hdeg⟩ := BW2.degWord hK hI hRp
  obtain ⟨bzP, Kbz, hbz⟩ := BW2.bzeroWord hK
  obtain ⟨bgP, Kbg, hbg⟩ := BW2.bgenWord hK hCh hP1
  obtain ⟨pickP, Kpick, hpick⟩ := hK.pick
  obtain ⟨ifzComb, Kifz, hifz⟩ := hK.ifZero
  refine ⟨.seq (pickP 1) (ifzComb degP (.seq (pickP 2) (ifzComb bzP bgP))),
    100 * (Kpick + Kifz + Kdeg + Kbz + Kbg + 1), ?_⟩
  intro main A m B N L es rest hAB hAmB hlen hv
  obtain ⟨-, -, -, -, -, -, -, hM1, hB1, -, hEM1, hEMB1, -, -, -, -, -⟩ :=
    BW2.sizeKit A m B N L es hAB hAmB hlen hv
  -- the outer `pick 1`
  have hp1 : WordR main (pickP 1)
      (fun vs => vs = ofList es :: .int (m : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest)
      (fun _ out => out = .int (m : ℤ) ::
        (ofList es :: .int (m : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest))
      (fun _ => 4 * Kpick * (BW2.BIG N L + BW2.S A m B)) := by
    refine Work.Kernel.WordR_conseq (hpick main 1) ?_ ?_ ?_
    · intro vs hvs; rw [hvs]; simp
    · intro vs out hvs hout
      rw [hvs] at hout
      rw [hout]; rfl
    · intro vs hvs
      rw [hvs, BW2.map_take1p1_sum]
      simp only [BW2.bw_vsz_int]
      calc Kpick * (1 + 1) * (vsz (ofList es) + isz (m : ℤ) + 1)
          ≤ Kpick * (1 + 1) * (2 * (BW2.BIG N L + BW2.S A m B)) :=
            Nat.mul_le_mul_left _ hEM1
        _ = 4 * Kpick * (BW2.BIG N L + BW2.S A m B) := by ring
  -- the inner `pick 2` (inside the `m ≠ 0` branch)
  have hp2 : WordR main (pickP 2)
      (fun vs => vs = ofList es :: .int (m : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest)
      (fun _ out => out = .int (B : ℤ) ::
        (ofList es :: .int (m : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest))
      (fun _ => 6 * Kpick * (BW2.BIG N L + BW2.S A m B)) := by
    refine Work.Kernel.WordR_conseq (hpick main 2) ?_ ?_ ?_
    · intro vs hvs; rw [hvs]; simp
    · intro vs out hvs hout
      rw [hvs] at hout
      rw [hout]; rfl
    · intro vs hvs
      rw [hvs, BW2.map_take2p1_sum]
      simp only [BW2.bw_vsz_int]
      calc Kpick * (2 + 1) * (vsz (ofList es) + (isz (m : ℤ) + isz (B : ℤ)) + 1)
          = Kpick * (2 + 1) * (vsz (ofList es) + isz (m : ℤ) + isz (B : ℤ) + 1) := by ring
        _ ≤ Kpick * (2 + 1) * (2 * (BW2.BIG N L + BW2.S A m B)) :=
            Nat.mul_le_mul_left _ hEMB1
        _ = 6 * Kpick * (BW2.BIG N L + BW2.S A m B) := by ring
  -- the `deg` branch (`m = 0`)
  have hdeg' : (m : ℤ) = 0 → WordR main degP
      (fun vs => vs = ofList es :: .int (m : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest)
      (BW2.Post A m B es rest) (fun _ => Kdeg * (BW2.BIG N L + BW2.S A m B)) := by
    intro hm0
    have hm : m = 0 := by omega
    refine Work.Kernel.WordR_conseq (hdeg main A m B N L es rest hm hAB hAmB hlen hv) ?_ ?_ ?_
    · intro vs hvs; exact hvs
    · intro vs out _ hout; exact hout
    · intro vs _
      exact le_of_eq (by ring)
  -- the whole `m ≠ 0` branch
  have hgen : (m : ℤ) ≠ 0 → WordR main (.seq (pickP 2) (ifzComb bzP bgP))
      (fun vs => vs = ofList es :: .int (m : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest)
      (BW2.Post A m B es rest) (fun _ => 6 * Kpick * (BW2.BIG N L + BW2.S A m B)
        + (Kifz * (isz (B : ℤ) + 1)
          + max (Kbz * (BW2.BIG N L + BW2.S A m B)) (Kbg * (BW2.BIG N L + BW2.S A m B)))) := by
    intro hm0
    have hm : m ≠ 0 := by omega
    -- the `B = 0` branch
    have hbz' : (B : ℤ) = 0 → WordR main bzP
        (fun vs => vs = ofList es :: .int (m : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest)
        (BW2.Post A m B es rest) (fun _ => Kbz * (BW2.BIG N L + BW2.S A m B)) := by
      intro hB0
      have hBz : B = 0 := by omega
      refine Work.Kernel.WordR_conseq (hbz main A m B N L es rest hBz hAB hAmB hlen hv) ?_ ?_ ?_
      · intro vs hvs; exact hvs
      · intro vs out _ hout; exact hout
      · intro vs _
        exact le_of_eq (by ring)
    -- the `0 < m`, `B ≠ 0` branch
    have hbg' : (B : ℤ) ≠ 0 → WordR main bgP
        (fun vs => vs = ofList es :: .int (m : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest)
        (BW2.Post A m B es rest) (fun _ => Kbg * (BW2.BIG N L + BW2.S A m B)) := by
      intro hB0
      have hBz : B ≠ 0 := by omega
      refine Work.Kernel.WordR_conseq
        (hbg main A m B N L es rest (Nat.pos_of_ne_zero hm) hBz hAmB hlen hv) ?_ ?_ ?_
      · intro vs hvs; exact hvs
      · intro vs out _ hout; exact hout
      · intro vs _
        exact le_of_eq (by ring)
    -- the `B` dispatch
    have hinnerB : WordR main (ifzComb bzP bgP)
        (fun vs => vs = .int (B : ℤ) ::
          (ofList es :: .int (m : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest))
        (fun _ out => ((B : ℤ) = 0 → BW2.SlicesPost A m B es rest out) ∧
          ((B : ℤ) ≠ 0 → BW2.SlicesPost A m B es rest out))
        (fun _ => Kifz * (isz (B : ℤ) + 1)
          + max (Kbz * (BW2.BIG N L + BW2.S A m B)) (Kbg * (BW2.BIG N L + BW2.S A m B))) :=
      hifz main bzP bgP (B : ℤ)
        (ofList es :: .int (m : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest)
        (BW2.SlicesPost A m B es rest) (BW2.SlicesPost A m B es rest)
        (Kbz * (BW2.BIG N L + BW2.S A m B)) (Kbg * (BW2.BIG N L + BW2.S A m B)) hbz' hbg'
    have hseq := Work.Kernel.WordR_seq hp2 hinnerB
      (B := fun _ => Kifz * (isz (B : ℤ) + 1)
        + max (Kbz * (BW2.BIG N L + BW2.S A m B)) (Kbg * (BW2.BIG N L + BW2.S A m B)))
      (fun vs mid _ hmid => ⟨by rw [hmid], le_rfl⟩)
    refine Work.Kernel.WordR_conseq hseq ?_ ?_ ?_
    · intro vs hvs; exact hvs
    · intro vs out _ hq
      obtain ⟨mid, hmid, hb⟩ := hq
      by_cases hB0 : (B : ℤ) = 0
      · exact hb.1 hB0
      · exact hb.2 hB0
    · intro vs _
      exact le_rfl
  -- the `m` dispatch
  have hOut : WordR main (ifzComb degP (.seq (pickP 2) (ifzComb bzP bgP)))
      (fun vs => vs = .int (m : ℤ) ::
        (ofList es :: .int (m : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest))
      (fun _ out => ((m : ℤ) = 0 → BW2.SlicesPost A m B es rest out) ∧
        ((m : ℤ) ≠ 0 → BW2.SlicesPost A m B es rest out))
      (fun _ => Kifz * (isz (m : ℤ) + 1)
        + max (Kdeg * (BW2.BIG N L + BW2.S A m B))
            (6 * Kpick * (BW2.BIG N L + BW2.S A m B)
              + (Kifz * (isz (B : ℤ) + 1)
                + max (Kbz * (BW2.BIG N L + BW2.S A m B)) (Kbg * (BW2.BIG N L + BW2.S A m B))))) :=
    hifz main degP (.seq (pickP 2) (ifzComb bzP bgP)) (m : ℤ)
      (ofList es :: .int (m : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest)
      (BW2.SlicesPost A m B es rest) (BW2.SlicesPost A m B es rest)
      (Kdeg * (BW2.BIG N L + BW2.S A m B))
      (6 * Kpick * (BW2.BIG N L + BW2.S A m B)
        + (Kifz * (isz (B : ℤ) + 1)
          + max (Kbz * (BW2.BIG N L + BW2.S A m B)) (Kbg * (BW2.BIG N L + BW2.S A m B))))
      hdeg' hgen
  -- the composition
  have hmain := Work.Kernel.WordR_seq hp1 hOut
    (B := fun _ => Kifz * (isz (m : ℤ) + 1)
      + max (Kdeg * (BW2.BIG N L + BW2.S A m B))
          (6 * Kpick * (BW2.BIG N L + BW2.S A m B)
            + (Kifz * (isz (B : ℤ) + 1)
              + max (Kbz * (BW2.BIG N L + BW2.S A m B)) (Kbg * (BW2.BIG N L + BW2.S A m B)))))
    (fun vs mid _ hmid => ⟨by rw [hmid], le_rfl⟩)
  refine Work.Kernel.WordR_conseq hmain ?_ ?_ ?_
  · intro vs hvs; exact hvs
  · intro vs out _ hq
    obtain ⟨mid, hmid, hb⟩ := hq
    by_cases hm0 : (m : ℤ) = 0
    · exact hb.1 hm0
    · exact hb.2 hm0
  · intro vs _
    exact le_trans (BW2.finalArith Kpick Kifz Kdeg Kbz Kbg A m B N L hM1 hB1)
      (le_of_eq (by simp only [BW2.BIG, BW2.S]; ring))

/-- `Work.Layout.Branch2Spec` (the `brP` field of `LayoutLib.applyAlong`), i.e. the `isz B`
form of the bound: this is the statement to use downstream. -/
theorem branch2Spec (hK : HvdH.KernelLib) (hI : HvdH.IntLib) (hCh : ChunksSpec)
    (hRp : ReplicateSpec) (hP1 : Phase1Spec) : Branch2Spec :=
  branchWord2_isz hK hI hCh hRp hP1

end Work.SB

namespace Work.SB

open HvdH
open Work.Layout

/-!
## The requested statement

`branchWord2` is stated verbatim as requested.  Its cost carries the extra summand `isz n`, where
`n` is *unbound* in the requested text; with the workspace's default `autoImplicit = false` the
declaration does not even elaborate, so the `section` below re-enables `autoImplicit` for it, and
Lean binds `n : ℤ` implicitly in front of the explicit arguments (exactly as the statement was
elaborated when it was requested).  Since `isz _` is a natural number, the extra summand can only
*increase* the bound, and `branchWord2` follows from `branchWord2_isz` with the very same `K`:
downstream, use `Work.SB.branch2Spec` (or `Work.SB.branchWord2_isz`) rather than `branchWord2` itself.
-/

section BranchWord2N

set_option autoImplicit true

theorem branchWord2 (hK : HvdH.KernelLib) (hI : HvdH.IntLib) (hCh : ChunksSpec)
    (hRp : ReplicateSpec) (hP1 : Phase1Spec) :
    ∃ (p : Cmd) (K : ℕ), ∀ (main : Cmd) (A m B N L : ℕ) (es : List Val) (rest : List Val),
      A * B ≤ N → A * m * B ≤ N → es.length = A * m * B → (∀ x ∈ es, vsz x ≤ L) →
      WordR main p
        (fun vs => vs = ofList es :: .int (m : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest)
        (fun _ out => ∃ sls : List (List Val), out = ofList (sls.map ofList) :: rest ∧
          sls = slices A m B es)
        (fun _ => K * (N + 1) * (L + N.size + 1) * (N.size + 1) +
          K * (isz A + isz m + isz n + isz B)) := by
  obtain ⟨p, K, h⟩ := branchWord2_isz hK hI hCh hRp hP1
  refine ⟨p, K, ?_⟩
  intro main A m B N L es rest hAB hAmB hlen hv
  refine Work.Kernel.WordR_conseq (h main A m B N L es rest hAB hAmB hlen hv) ?_ ?_ ?_
  · intro vs hvs; exact hvs
  · intro vs out _ hout; exact hout
  · intro vs _
    have hle : isz A + isz m + isz B ≤ isz A + isz m + isz n + isz B := by omega
    exact Nat.add_le_add_left (Nat.mul_le_mul_left K hle) _

end BranchWord2N

end Work.SB
