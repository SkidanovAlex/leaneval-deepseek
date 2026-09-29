import Mathlib
import Submission.Work.KronP.defs
import Submission.Work.Fx.mulFField

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KronP

open HvdH

/-! ## Small size helpers -/

/-- `isz` of `(z.natAbs : ℤ)` is `isz z`. -/
theorem isz_natAbs_cast (z : ℤ) : HvdH.isz ((z.natAbs : ℕ) : ℤ) = HvdH.isz z := by
  simp only [HvdH.isz, Int.natAbs_natCast]

/-- Total size of a list of integer values. -/
theorem szl_ints (l : List ℤ) : Work.Fx.szl (l.map HvdH.Val.int) = (l.map HvdH.isz).sum := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      simp only [List.map_cons, Work.Fx.szl_cons, ih, Work.Fx.vsz_int, List.sum_cons]

/-- A prefix has no larger total size. -/
theorem szl_take_le (W : List HvdH.Val) (n : ℕ) : Work.Fx.szl (W.take n) ≤ Work.Fx.szl W := by
  have h := Work.Fx.szl_append (W.take n) (W.drop n)
  rw [List.take_append_drop] at h
  omega

/-- For nonnegative integers, `natAbs` is `toNat`. -/
theorem natAbs_of_nonneg' {z : ℤ} (hz : 0 ≤ z) : z.natAbs = z.toNat := by
  have h : z = ((z.toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg hz).symm
  conv_lhs => rw [h]
  exact Int.natAbs_natCast _

/-! ## A `TopSpec` adapter for `KernelLib.pick` -/

theorem topPick (hK : HvdH.KernelLib) :
    ∃ (prog : ℕ → HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (k : ℕ) (W : List HvdH.Val),
      k < W.length →
      Work.Fx.TopSpec main (prog k) W (W.getD k .nil :: W)
        (K * (k + 1) * (Work.Fx.szl W + 1)) := by
  obtain ⟨prog, K, h⟩ := hK.pick
  refine ⟨prog, K, fun main k W hklt => ?_⟩
  intro rest
  have hlt : k < (W ++ rest).length := by
    rw [List.length_append]; omega
  have htake : (W ++ rest).take (k + 1) = W.take (k + 1) :=
    List.take_append_of_le_length (by omega)
  refine hK.conseq (main := main) (p := prog k)
    (P := fun vs => k < vs.length) (Q := fun vs out => out = vs.getD k .nil :: vs)
    (C := fun vs => K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1))
    (P' := fun vs => vs = W ++ rest)
    (Q' := fun _ out => out = (W.getD k .nil :: W) ++ rest)
    (C' := fun _ => K * (k + 1) * (Work.Fx.szl W + 1)) (h main k) ?_ ?_ ?_
  · intro vs hv
    rw [hv]; exact hlt
  · intro vs out hv hq
    rw [hv] at hq
    rw [hq, Work.Fx.getD_append_of_lt hklt]
    rfl
  · intro vs hv
    rw [hv, htake]
    have hsz : ((W.take (k + 1)).map vsz).sum ≤ Work.Fx.szl W := szl_take_le W (k + 1)
    exact Nat.mul_le_mul_left _ (Nat.succ_le_succ hsz)

/-! ## The signed product `X * Y` via `Cmd.self` -/

theorem signedProd (hK : HvdH.KernelLib) (hI : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ),
      Monotone Cm → HvdH.MulBelow main N Cm → ∀ (X Y : ℤ),
      X.natAbs.size < N → Y.natAbs.size < N →
      Work.Fx.TopSpec main prog [HvdH.Val.int X, HvdH.Val.int Y] [HvdH.Val.int (X * Y)]
        (Cm (max X.natAbs.size Y.natAbs.size) + K * (HvdH.isz X + HvdH.isz Y + 1)) := by
  obtain ⟨AS, Kas, hAS⟩ := Work.Fx.TopSpec.absSgn hK hI
  obtain ⟨Rl, Kro, hRl⟩ := Work.Fx.TopSpec.rollS hK
  obtain ⟨Sw, Ksw, hSw⟩ := Work.Fx.TopSpec.swap hK
  obtain ⟨mulSP, Kms, hms⟩ := hI.mulS
  refine ⟨.seq (.seq (.seq (.seq (.seq (.seq (.seq AS (Rl 2)) AS) (Rl 2)) .self) Sw) mulSP)
      mulSP, 1000 * (Kas + Kro + Ksw + Kms + 1), ?_⟩
  intro main N Cm hmono hmul X Y hX hY
  set B : ℕ := HvdH.isz X + HvdH.isz Y + 1 with hB
  have hiszX : HvdH.isz X = X.natAbs.size + 2 := rfl
  have hiszY : HvdH.isz Y = Y.natAbs.size + 2 := rfl
  have hiszX' : 2 ≤ HvdH.isz X := by rw [hiszX]; omega
  have hiszY' : 2 ≤ HvdH.isz Y := by rw [hiszY]; omega
  have hB5 : 5 ≤ B := by omega
  have hsgnX : HvdH.isz (Int.sign X) ≤ 3 := Work.Fx.isz_sign_le X
  have hsgnY : HvdH.isz (Int.sign Y) ≤ 3 := Work.Fx.isz_sign_le Y
  have hqB : HvdH.isz (((X.natAbs * Y.natAbs : ℕ) : ℤ)) ≤ B := by
    have h1 : (X.natAbs * Y.natAbs).size ≤ X.natAbs.size + Y.natAbs.size := by
      rw [Nat.size_le, pow_add]
      exact Nat.mul_lt_mul'' (Nat.lt_size_self _) (Nat.lt_size_self _)
    simp only [HvdH.isz, Int.natAbs_natCast]
    omega
  -- ### step 1: the magnitude and the sign of `X`
  have hs1 : Work.Fx.TopSpec main AS [HvdH.Val.int X]
      [HvdH.Val.int (X.natAbs : ℤ), HvdH.Val.int (Int.sign X)] (Kas * B) := by
    refine Work.Fx.TopSpec.mono hK (hAS main X) rfl rfl ?_
    exact Nat.mul_le_mul_left Kas (by omega)
  have hs1' : Work.Fx.TopSpec main AS [HvdH.Val.int X, HvdH.Val.int Y]
      [HvdH.Val.int (X.natAbs : ℤ), HvdH.Val.int (Int.sign X), HvdH.Val.int Y]
      (Kas * B) := by
    simpa using Work.Fx.TopSpec.extend hs1 [HvdH.Val.int Y]
  -- ### step 2: bring `Y` to the top
  have hs2 : Work.Fx.TopSpec main (Rl 2)
      [HvdH.Val.int (X.natAbs : ℤ), HvdH.Val.int (Int.sign X), HvdH.Val.int Y]
      [HvdH.Val.int Y, HvdH.Val.int (X.natAbs : ℤ), HvdH.Val.int (Int.sign X)]
      (6 * Kro * B) := by
    have h := hRl main 2
      [HvdH.Val.int (X.natAbs : ℤ), HvdH.Val.int (Int.sign X), HvdH.Val.int Y] (by simp)
    refine Work.Fx.TopSpec.mono hK h rfl ?_ ?_
    · simp
    · have he : Work.Fx.szl
            [HvdH.Val.int (X.natAbs : ℤ), HvdH.Val.int (Int.sign X), HvdH.Val.int Y]
            = HvdH.isz X + HvdH.isz (Int.sign X) + HvdH.isz Y := by
        simp only [Work.Fx.szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          Work.Fx.vsz_int, Nat.add_zero, isz_natAbs_cast]
        omega
      have hsz : Work.Fx.szl
          [HvdH.Val.int (X.natAbs : ℤ), HvdH.Val.int (Int.sign X), HvdH.Val.int Y] + 1
          ≤ 2 * B := by rw [he]; omega
      calc Kro * (2 + 1) * (Work.Fx.szl
            [HvdH.Val.int (X.natAbs : ℤ), HvdH.Val.int (Int.sign X), HvdH.Val.int Y] + 1)
          = Kro * (3 * (Work.Fx.szl
            [HvdH.Val.int (X.natAbs : ℤ), HvdH.Val.int (Int.sign X), HvdH.Val.int Y] + 1)) := by
            ring
        _ ≤ Kro * (3 * (2 * B)) := Nat.mul_le_mul_left Kro (Nat.mul_le_mul_left 3 hsz)
        _ = 6 * Kro * B := by ring
  -- ### step 3: the magnitude and the sign of `Y`
  have hs3 : Work.Fx.TopSpec main AS
      [HvdH.Val.int Y, HvdH.Val.int (X.natAbs : ℤ), HvdH.Val.int (Int.sign X)]
      [HvdH.Val.int (Y.natAbs : ℤ), HvdH.Val.int (Int.sign Y),
        HvdH.Val.int (X.natAbs : ℤ), HvdH.Val.int (Int.sign X)] (Kas * B) := by
    refine Work.Fx.TopSpec.mono hK (Work.Fx.TopSpec.extend (hAS main Y)
      [HvdH.Val.int (X.natAbs : ℤ), HvdH.Val.int (Int.sign X)]) rfl rfl ?_
    exact Nat.mul_le_mul_left Kas (by omega)
  -- ### step 4: bring `|X|` back to the top
  have hs4 : Work.Fx.TopSpec main (Rl 2)
      [HvdH.Val.int (Y.natAbs : ℤ), HvdH.Val.int (Int.sign Y),
        HvdH.Val.int (X.natAbs : ℤ), HvdH.Val.int (Int.sign X)]
      [HvdH.Val.int (X.natAbs : ℤ), HvdH.Val.int (Y.natAbs : ℤ),
        HvdH.Val.int (Int.sign Y), HvdH.Val.int (Int.sign X)] (12 * Kro * B) := by
    have h := hRl main 2
      [HvdH.Val.int (Y.natAbs : ℤ), HvdH.Val.int (Int.sign Y),
        HvdH.Val.int (X.natAbs : ℤ), HvdH.Val.int (Int.sign X)] (by simp)
    refine Work.Fx.TopSpec.mono hK h rfl ?_ ?_
    · simp
    · have he : Work.Fx.szl
            [HvdH.Val.int (Y.natAbs : ℤ), HvdH.Val.int (Int.sign Y),
              HvdH.Val.int (X.natAbs : ℤ), HvdH.Val.int (Int.sign X)]
            = HvdH.isz Y + HvdH.isz (Int.sign Y) + HvdH.isz X + HvdH.isz (Int.sign X) := by
        simp only [Work.Fx.szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          Work.Fx.vsz_int, Nat.add_zero, isz_natAbs_cast]
        omega
      have hsz : Work.Fx.szl
          [HvdH.Val.int (Y.natAbs : ℤ), HvdH.Val.int (Int.sign Y),
            HvdH.Val.int (X.natAbs : ℤ), HvdH.Val.int (Int.sign X)] + 1 ≤ 4 * B := by
        rw [he]; omega
      calc Kro * (2 + 1) * (Work.Fx.szl
            [HvdH.Val.int (Y.natAbs : ℤ), HvdH.Val.int (Int.sign Y),
              HvdH.Val.int (X.natAbs : ℤ), HvdH.Val.int (Int.sign X)] + 1)
          = Kro * (3 * (Work.Fx.szl
            [HvdH.Val.int (Y.natAbs : ℤ), HvdH.Val.int (Int.sign Y),
              HvdH.Val.int (X.natAbs : ℤ), HvdH.Val.int (Int.sign X)] + 1)) := by ring
        _ ≤ Kro * (3 * (4 * B)) := Nat.mul_le_mul_left Kro (Nat.mul_le_mul_left 3 hsz)
        _ = 12 * Kro * B := by ring
  -- ### step 5: the product of the magnitudes, by `self`
  have hs5 : Work.Fx.TopSpec main .self
      [HvdH.Val.int (X.natAbs : ℤ), HvdH.Val.int (Y.natAbs : ℤ),
        HvdH.Val.int (Int.sign Y), HvdH.Val.int (Int.sign X)]
      [HvdH.Val.int (((X.natAbs * Y.natAbs : ℕ) : ℤ)),
        HvdH.Val.int (Int.sign Y), HvdH.Val.int (Int.sign X)]
      (Cm (max X.natAbs.size Y.natAbs.size)) := by
    simpa using Work.Fx.TopSpec.extend
      (Work.Fx.TopSpec.selfMul hK hmul (x := X.natAbs) (y := Y.natAbs) hX hY)
      [HvdH.Val.int (Int.sign Y), HvdH.Val.int (Int.sign X)]
  -- ### step 6: swap the two signs
  have hs6 : Work.Fx.TopSpec main Sw
      [HvdH.Val.int (((X.natAbs * Y.natAbs : ℕ) : ℤ)), HvdH.Val.int (Int.sign Y),
        HvdH.Val.int (Int.sign X)]
      [HvdH.Val.int (Int.sign Y), HvdH.Val.int (((X.natAbs * Y.natAbs : ℕ) : ℤ)),
        HvdH.Val.int (Int.sign X)] (2 * Ksw * B) := by
    refine Work.Fx.TopSpec.mono hK (Work.Fx.TopSpec.extend
      (hSw main (HvdH.Val.int (((X.natAbs * Y.natAbs : ℕ) : ℤ)))
        (HvdH.Val.int (Int.sign Y))) [HvdH.Val.int (Int.sign X)]) rfl rfl ?_
    simp only [Work.Fx.vsz_int]
    have h1 : HvdH.isz (((X.natAbs * Y.natAbs : ℕ) : ℤ)) + HvdH.isz (Int.sign Y) + 1 ≤ 2 * B := by
      omega
    calc Ksw * (HvdH.isz (((X.natAbs * Y.natAbs : ℕ) : ℤ)) + HvdH.isz (Int.sign Y) + 1)
        ≤ Ksw * (2 * B) := Nat.mul_le_mul_left Ksw h1
      _ = 2 * Ksw * B := by ring
  -- ### step 7: multiply the two signs
  have hs7 : Work.Fx.TopSpec main mulSP
      [HvdH.Val.int (Int.sign Y), HvdH.Val.int (((X.natAbs * Y.natAbs : ℕ) : ℤ)),
        HvdH.Val.int (Int.sign X)]
      [HvdH.Val.int (Int.sign Y * ((X.natAbs * Y.natAbs : ℕ) : ℤ)),
        HvdH.Val.int (Int.sign X)] (3 * Kms * B) := by
    refine Work.Fx.TopSpec.mono hK (Work.Fx.TopSpec.extend
      (Work.Fx.TopSpec.binOp hK (hms main)
        (a := Int.sign Y) (b := ((X.natAbs * Y.natAbs : ℕ) : ℤ)) trivial)
      [HvdH.Val.int (Int.sign X)]) rfl rfl ?_
    have h1 : HvdH.isz (Int.sign Y) * HvdH.isz (((X.natAbs * Y.natAbs : ℕ) : ℤ)) ≤ 3 * B :=
      Nat.mul_le_mul hsgnY hqB
    calc Kms * HvdH.isz (Int.sign Y) * HvdH.isz (((X.natAbs * Y.natAbs : ℕ) : ℤ))
        = Kms * (HvdH.isz (Int.sign Y) * HvdH.isz (((X.natAbs * Y.natAbs : ℕ) : ℤ))) := by ring
      _ ≤ Kms * (3 * B) := Nat.mul_le_mul_left Kms h1
      _ = 3 * Kms * B := by ring
  -- ### step 8: fold the sign product into the magnitudes
  have hs8 : Work.Fx.TopSpec main mulSP
      [HvdH.Val.int (Int.sign Y * ((X.natAbs * Y.natAbs : ℕ) : ℤ)),
        HvdH.Val.int (Int.sign X)]
      [HvdH.Val.int ((Int.sign Y * ((X.natAbs * Y.natAbs : ℕ) : ℤ)) * Int.sign X)]
      (16 * Kms * B) := by
    have hle : HvdH.isz (Int.sign Y * ((X.natAbs * Y.natAbs : ℕ) : ℤ)) ≤ B + 3 := by
      have h1 : HvdH.isz (Int.sign Y * ((X.natAbs * Y.natAbs : ℕ) : ℤ))
          ≤ HvdH.isz (Int.sign Y) + HvdH.isz (((X.natAbs * Y.natAbs : ℕ) : ℤ)) :=
        Work.Fx.isz_mul_le _ _
      omega
    refine Work.Fx.TopSpec.mono hK (Work.Fx.TopSpec.binOp hK (hms main)
      (a := Int.sign Y * ((X.natAbs * Y.natAbs : ℕ) : ℤ)) (b := Int.sign X) trivial) rfl rfl ?_
    have h1 : HvdH.isz (Int.sign Y * ((X.natAbs * Y.natAbs : ℕ) : ℤ)) * HvdH.isz (Int.sign X)
        ≤ (B + 3) * 3 := Nat.mul_le_mul hle hsgnX
    calc Kms * HvdH.isz (Int.sign Y * ((X.natAbs * Y.natAbs : ℕ) : ℤ)) * HvdH.isz (Int.sign X)
        = Kms * (HvdH.isz (Int.sign Y * ((X.natAbs * Y.natAbs : ℕ) : ℤ)) *
            HvdH.isz (Int.sign X)) := by ring
      _ ≤ Kms * ((B + 3) * 3) := Nat.mul_le_mul_left Kms h1
      _ ≤ Kms * (16 * B) := Nat.mul_le_mul_left Kms (by omega)
      _ = 16 * Kms * B := by ring
  -- ### assemble
  have hS1 : Work.Fx.TopSpec main (.seq AS (Rl 2)) [HvdH.Val.int X, HvdH.Val.int Y]
      [HvdH.Val.int Y, HvdH.Val.int (X.natAbs : ℤ), HvdH.Val.int (Int.sign X)]
      (Kas * B + 6 * Kro * B) := Work.Fx.TopSpec.seq hK hs1' hs2
  have hS2 : Work.Fx.TopSpec main (.seq (.seq AS (Rl 2)) AS)
      [HvdH.Val.int X, HvdH.Val.int Y]
      [HvdH.Val.int (Y.natAbs : ℤ), HvdH.Val.int (Int.sign Y),
        HvdH.Val.int (X.natAbs : ℤ), HvdH.Val.int (Int.sign X)]
      (Kas * B + 6 * Kro * B + Kas * B) := Work.Fx.TopSpec.seq hK hS1 hs3
  have hS3 : Work.Fx.TopSpec main (.seq (.seq (.seq AS (Rl 2)) AS) (Rl 2))
      [HvdH.Val.int X, HvdH.Val.int Y]
      [HvdH.Val.int (X.natAbs : ℤ), HvdH.Val.int (Y.natAbs : ℤ),
        HvdH.Val.int (Int.sign Y), HvdH.Val.int (Int.sign X)]
      (Kas * B + 6 * Kro * B + Kas * B + 12 * Kro * B) := Work.Fx.TopSpec.seq hK hS2 hs4
  have hS4 : Work.Fx.TopSpec main (.seq (.seq (.seq (.seq AS (Rl 2)) AS) (Rl 2)) .self)
      [HvdH.Val.int X, HvdH.Val.int Y]
      [HvdH.Val.int (((X.natAbs * Y.natAbs : ℕ) : ℤ)),
        HvdH.Val.int (Int.sign Y), HvdH.Val.int (Int.sign X)]
      (Kas * B + 6 * Kro * B + Kas * B + 12 * Kro * B +
        Cm (max X.natAbs.size Y.natAbs.size)) := Work.Fx.TopSpec.seq hK hS3 hs5
  have hS5 : Work.Fx.TopSpec main
      (.seq (.seq (.seq (.seq (.seq AS (Rl 2)) AS) (Rl 2)) .self) Sw)
      [HvdH.Val.int X, HvdH.Val.int Y]
      [HvdH.Val.int (Int.sign Y), HvdH.Val.int (((X.natAbs * Y.natAbs : ℕ) : ℤ)),
        HvdH.Val.int (Int.sign X)]
      (Kas * B + 6 * Kro * B + Kas * B + 12 * Kro * B +
        Cm (max X.natAbs.size Y.natAbs.size) + 2 * Ksw * B) :=
    Work.Fx.TopSpec.seq hK hS4 hs6
  have hS6 : Work.Fx.TopSpec main
      (.seq (.seq (.seq (.seq (.seq (.seq AS (Rl 2)) AS) (Rl 2)) .self) Sw) mulSP)
      [HvdH.Val.int X, HvdH.Val.int Y]
      [HvdH.Val.int (Int.sign Y * ((X.natAbs * Y.natAbs : ℕ) : ℤ)),
        HvdH.Val.int (Int.sign X)]
      (Kas * B + 6 * Kro * B + Kas * B + 12 * Kro * B +
        Cm (max X.natAbs.size Y.natAbs.size) + 2 * Ksw * B + 3 * Kms * B) :=
    Work.Fx.TopSpec.seq hK hS5 hs7
  have hS7 : Work.Fx.TopSpec main
      (.seq (.seq (.seq (.seq (.seq (.seq (.seq AS (Rl 2)) AS) (Rl 2)) .self) Sw) mulSP)
        mulSP)
      [HvdH.Val.int X, HvdH.Val.int Y]
      [HvdH.Val.int ((Int.sign Y * ((X.natAbs * Y.natAbs : ℕ) : ℤ)) * Int.sign X)]
      (Kas * B + 6 * Kro * B + Kas * B + 12 * Kro * B +
        Cm (max X.natAbs.size Y.natAbs.size) + 2 * Ksw * B + 3 * Kms * B + 16 * Kms * B) :=
    Work.Fx.TopSpec.seq hK hS6 hs8
  have hkey : (Int.sign Y * ((X.natAbs * Y.natAbs : ℕ) : ℤ)) * Int.sign X = X * Y := by
    rw [show ((X.natAbs * Y.natAbs : ℕ) : ℤ) = (X.natAbs : ℤ) * (Y.natAbs : ℤ) from by
      push_cast; ring]
    rw [show (Int.sign Y * ((X.natAbs : ℤ) * (Y.natAbs : ℤ))) * Int.sign X
        = (Int.sign Y * (Y.natAbs : ℤ)) * (Int.sign X * (X.natAbs : ℤ)) from by ring]
    rw [Work.Fx.sign_mul_natAbs Y, Work.Fx.sign_mul_natAbs X]
    ring
  refine Work.Fx.TopSpec.mono hK hS7 rfl ?_ ?_
  · simp only [hkey.symm]
  · rw [hB]
    nlinarith [Nat.zero_le Kas, Nat.zero_le Kro, Nat.zero_le Ksw, Nat.zero_le Kms,
      hiszX', hiszY']

/-! ## Pull a copy of the third constant to the top of the window -/

theorem prepC (hK : HvdH.KernelLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (X Y : ℤ) (b n : ℕ) (C : ℤ),
      Work.Fx.TopSpec main prog
        [HvdH.Val.int X, HvdH.Val.int Y, HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ),
          HvdH.Val.int C]
        [HvdH.Val.int X, HvdH.Val.int Y, HvdH.Val.int C,
          HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ), HvdH.Val.int C]
        (K * (HvdH.isz X + HvdH.isz Y + HvdH.isz (b : ℤ) + HvdH.isz (n : ℤ) + HvdH.isz C + 1)) := by
  obtain ⟨pickP, Kp, hpick⟩ := topPick hK
  obtain ⟨Rl, Kro, hRl⟩ := Work.Fx.TopSpec.rollS hK
  refine ⟨.seq (.seq (.seq (pickP 4) (Rl 1)) (Rl 2)) (Rl 1), 100 * (Kp + Kro + 1), ?_⟩
  intro main X Y b n C
  set B : ℕ := HvdH.isz X + HvdH.isz Y + HvdH.isz (b : ℤ) + HvdH.isz (n : ℤ) +
    HvdH.isz C + 1 with hB
  have hCB : HvdH.isz C ≤ B := by omega
  have hsz0 : Work.Fx.szl
      [HvdH.Val.int X, HvdH.Val.int Y, HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ),
        HvdH.Val.int C] + 1 = B := by
    have he : Work.Fx.szl
        [HvdH.Val.int X, HvdH.Val.int Y, HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ),
          HvdH.Val.int C] = HvdH.isz X + HvdH.isz Y + HvdH.isz (b : ℤ) + HvdH.isz (n : ℤ) +
          HvdH.isz C := by
      simp only [Work.Fx.szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Work.Fx.vsz_int, Nat.add_zero]
      omega
    rw [he, hB]
  -- ### step 1: `pick 4`
  have hs1 : Work.Fx.TopSpec main (pickP 4)
      [HvdH.Val.int X, HvdH.Val.int Y, HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ),
        HvdH.Val.int C]
      [HvdH.Val.int C, HvdH.Val.int X, HvdH.Val.int Y, HvdH.Val.int (b : ℤ),
        HvdH.Val.int (n : ℤ), HvdH.Val.int C] (Kp * 5 * B) := by
    have h := hpick main 4
      [HvdH.Val.int X, HvdH.Val.int Y, HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ),
        HvdH.Val.int C] (by simp)
    refine Work.Fx.TopSpec.mono hK h rfl ?_ ?_
    · simp
    · rw [hsz0]
  -- ### step 2: `roll 1`
  have hs2 : Work.Fx.TopSpec main (Rl 1)
      [HvdH.Val.int C, HvdH.Val.int X, HvdH.Val.int Y, HvdH.Val.int (b : ℤ),
        HvdH.Val.int (n : ℤ), HvdH.Val.int C]
      [HvdH.Val.int X, HvdH.Val.int C, HvdH.Val.int Y, HvdH.Val.int (b : ℤ),
        HvdH.Val.int (n : ℤ), HvdH.Val.int C] (4 * Kro * B) := by
    have h := hRl main 1
      [HvdH.Val.int C, HvdH.Val.int X, HvdH.Val.int Y, HvdH.Val.int (b : ℤ),
        HvdH.Val.int (n : ℤ), HvdH.Val.int C] (by simp)
    refine Work.Fx.TopSpec.mono hK h rfl ?_ ?_
    · simp
    · have he : Work.Fx.szl
            [HvdH.Val.int C, HvdH.Val.int X, HvdH.Val.int Y, HvdH.Val.int (b : ℤ),
              HvdH.Val.int (n : ℤ), HvdH.Val.int C]
            = HvdH.isz C + HvdH.isz X + HvdH.isz Y + HvdH.isz (b : ℤ) + HvdH.isz (n : ℤ) +
              HvdH.isz C := by
        simp only [Work.Fx.szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          Work.Fx.vsz_int, Nat.add_zero]
        omega
      have hsz : Work.Fx.szl
          [HvdH.Val.int C, HvdH.Val.int X, HvdH.Val.int Y, HvdH.Val.int (b : ℤ),
            HvdH.Val.int (n : ℤ), HvdH.Val.int C] + 1 ≤ 2 * B := by rw [he]; omega
      calc Kro * (1 + 1) * (Work.Fx.szl
            [HvdH.Val.int C, HvdH.Val.int X, HvdH.Val.int Y, HvdH.Val.int (b : ℤ),
              HvdH.Val.int (n : ℤ), HvdH.Val.int C] + 1)
          = Kro * (2 * (Work.Fx.szl
            [HvdH.Val.int C, HvdH.Val.int X, HvdH.Val.int Y, HvdH.Val.int (b : ℤ),
              HvdH.Val.int (n : ℤ), HvdH.Val.int C] + 1)) := by ring
        _ ≤ Kro * (2 * (2 * B)) := Nat.mul_le_mul_left Kro (Nat.mul_le_mul_left 2 hsz)
        _ = 4 * Kro * B := by ring
  -- ### step 3: `roll 2`
  have hs3 : Work.Fx.TopSpec main (Rl 2)
      [HvdH.Val.int X, HvdH.Val.int C, HvdH.Val.int Y, HvdH.Val.int (b : ℤ),
        HvdH.Val.int (n : ℤ), HvdH.Val.int C]
      [HvdH.Val.int Y, HvdH.Val.int X, HvdH.Val.int C, HvdH.Val.int (b : ℤ),
        HvdH.Val.int (n : ℤ), HvdH.Val.int C] (6 * Kro * B) := by
    have h := hRl main 2
      [HvdH.Val.int X, HvdH.Val.int C, HvdH.Val.int Y, HvdH.Val.int (b : ℤ),
        HvdH.Val.int (n : ℤ), HvdH.Val.int C] (by simp)
    refine Work.Fx.TopSpec.mono hK h rfl ?_ ?_
    · simp
    · have he : Work.Fx.szl
            [HvdH.Val.int X, HvdH.Val.int C, HvdH.Val.int Y, HvdH.Val.int (b : ℤ),
              HvdH.Val.int (n : ℤ), HvdH.Val.int C]
            = HvdH.isz X + HvdH.isz C + HvdH.isz Y + HvdH.isz (b : ℤ) + HvdH.isz (n : ℤ) +
              HvdH.isz C := by
        simp only [Work.Fx.szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          Work.Fx.vsz_int, Nat.add_zero]
        omega
      have hsz : Work.Fx.szl
          [HvdH.Val.int X, HvdH.Val.int C, HvdH.Val.int Y, HvdH.Val.int (b : ℤ),
            HvdH.Val.int (n : ℤ), HvdH.Val.int C] + 1 ≤ 2 * B := by rw [he]; omega
      calc Kro * (2 + 1) * (Work.Fx.szl
            [HvdH.Val.int X, HvdH.Val.int C, HvdH.Val.int Y, HvdH.Val.int (b : ℤ),
              HvdH.Val.int (n : ℤ), HvdH.Val.int C] + 1)
          = Kro * (3 * (Work.Fx.szl
            [HvdH.Val.int X, HvdH.Val.int C, HvdH.Val.int Y, HvdH.Val.int (b : ℤ),
              HvdH.Val.int (n : ℤ), HvdH.Val.int C] + 1)) := by ring
        _ ≤ Kro * (3 * (2 * B)) := Nat.mul_le_mul_left Kro (Nat.mul_le_mul_left 3 hsz)
        _ = 6 * Kro * B := by ring
  -- ### step 4: `roll 1`
  have hs4 : Work.Fx.TopSpec main (Rl 1)
      [HvdH.Val.int Y, HvdH.Val.int X, HvdH.Val.int C, HvdH.Val.int (b : ℤ),
        HvdH.Val.int (n : ℤ), HvdH.Val.int C]
      [HvdH.Val.int X, HvdH.Val.int Y, HvdH.Val.int C, HvdH.Val.int (b : ℤ),
        HvdH.Val.int (n : ℤ), HvdH.Val.int C] (4 * Kro * B) := by
    have h := hRl main 1
      [HvdH.Val.int Y, HvdH.Val.int X, HvdH.Val.int C, HvdH.Val.int (b : ℤ),
        HvdH.Val.int (n : ℤ), HvdH.Val.int C] (by simp)
    refine Work.Fx.TopSpec.mono hK h rfl ?_ ?_
    · simp
    · have he : Work.Fx.szl
            [HvdH.Val.int Y, HvdH.Val.int X, HvdH.Val.int C, HvdH.Val.int (b : ℤ),
              HvdH.Val.int (n : ℤ), HvdH.Val.int C]
            = HvdH.isz Y + HvdH.isz X + HvdH.isz C + HvdH.isz (b : ℤ) + HvdH.isz (n : ℤ) +
              HvdH.isz C := by
        simp only [Work.Fx.szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          Work.Fx.vsz_int, Nat.add_zero]
        omega
      have hsz : Work.Fx.szl
          [HvdH.Val.int Y, HvdH.Val.int X, HvdH.Val.int C, HvdH.Val.int (b : ℤ),
            HvdH.Val.int (n : ℤ), HvdH.Val.int C] + 1 ≤ 2 * B := by rw [he]; omega
      calc Kro * (1 + 1) * (Work.Fx.szl
            [HvdH.Val.int Y, HvdH.Val.int X, HvdH.Val.int C, HvdH.Val.int (b : ℤ),
              HvdH.Val.int (n : ℤ), HvdH.Val.int C] + 1)
          = Kro * (2 * (Work.Fx.szl
            [HvdH.Val.int Y, HvdH.Val.int X, HvdH.Val.int C, HvdH.Val.int (b : ℤ),
              HvdH.Val.int (n : ℤ), HvdH.Val.int C] + 1)) := by ring
        _ ≤ Kro * (2 * (2 * B)) := Nat.mul_le_mul_left Kro (Nat.mul_le_mul_left 2 hsz)
        _ = 4 * Kro * B := by ring
  -- ### assemble
  have hA : Work.Fx.TopSpec main (.seq (.seq (pickP 4) (Rl 1)) (Rl 2))
      [HvdH.Val.int X, HvdH.Val.int Y, HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ),
        HvdH.Val.int C]
      [HvdH.Val.int Y, HvdH.Val.int X, HvdH.Val.int C, HvdH.Val.int (b : ℤ),
        HvdH.Val.int (n : ℤ), HvdH.Val.int C]
      (Kp * 5 * B + 4 * Kro * B + 6 * Kro * B) :=
    Work.Fx.TopSpec.seq hK (Work.Fx.TopSpec.seq hK hs1 hs2) hs3
  have hall : Work.Fx.TopSpec main (.seq (.seq (.seq (pickP 4) (Rl 1)) (Rl 2)) (Rl 1))
      [HvdH.Val.int X, HvdH.Val.int Y, HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ),
        HvdH.Val.int C]
      [HvdH.Val.int X, HvdH.Val.int Y, HvdH.Val.int C, HvdH.Val.int (b : ℤ),
        HvdH.Val.int (n : ℤ), HvdH.Val.int C]
      (Kp * 5 * B + 4 * Kro * B + 6 * Kro * B + 4 * Kro * B) :=
    Work.Fx.TopSpec.seq hK hA hs4
  exact Work.Fx.TopSpec.mono hK hall rfl rfl (by
    rw [hB]
    nlinarith [Nat.zero_le Kp, Nat.zero_le Kro, hCB])

/-! ## Base-`2^b` digits, keeping the constants `b, n, C` below -/

theorem chunkRestore (hK : HvdH.KernelLib) (hI : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (x b n : ℕ) (C : ℤ),
      1 ≤ b → 1 ≤ n → x < 2 ^ (b * n) →
      Work.Fx.TopSpec main prog
        [HvdH.Val.int x, HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ), HvdH.Val.int C]
        [HvdH.intList (HvdH.chunks x b n), HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ),
          HvdH.Val.int C]
        (K * (HvdH.isz (x : ℤ) + (n + 1) * (b + 1) + HvdH.isz C + 1)) := by
  obtain ⟨pickP, Kp, hpick⟩ := topPick hK
  obtain ⟨Rl, Kro, hRl⟩ := Work.Fx.TopSpec.rollS hK
  obtain ⟨ckP, Kc, hck⟩ := hI.chunk
  refine ⟨.seq (.seq (.seq (pickP 2) (pickP 2)) (Rl 2)) ckP, 100 * (Kp + Kro + Kc + 1), ?_⟩
  intro main x b n C hb hn hxlt
  set B : ℕ := HvdH.isz (x : ℤ) + (n + 1) * (b + 1) + HvdH.isz C + 1 with hB
  have hxB : HvdH.isz (x : ℤ) ≤ B := by omega
  have hCB : HvdH.isz C ≤ B := by omega
  have hnb : (n + 1) * (b + 1) ≤ B := by omega
  have hn1f : n * (b + 1) ≤ (n + 1) * (b + 1) := Nat.mul_le_mul_right (b + 1) (by omega)
  have hiszb : HvdH.isz (b : ℤ) = b.size + 2 := rfl
  have hiszn : HvdH.isz (n : ℤ) = n.size + 2 := rfl
  have hiszb' : HvdH.isz (b : ℤ) ≤ (n + 1) * (b + 1) := by
    rw [hiszb]
    have h1 : b.size ≤ b := Nat.size_le.mpr (Nat.lt_two_pow_self (n := b))
    have h2 : 2 * (b + 1) ≤ (n + 1) * (b + 1) :=
      Nat.mul_le_mul_right (b + 1) (by omega : 2 ≤ n + 1)
    omega
  have hiszn' : HvdH.isz (n : ℤ) ≤ (n + 1) * (b + 1) := by
    rw [hiszn]
    have h1 : n.size ≤ n := Nat.size_le.mpr (Nat.lt_two_pow_self (n := n))
    have h2 : 2 * (n + 1) ≤ (n + 1) * (b + 1) := by
      calc 2 * (n + 1) = (n + 1) * 2 := by ring
        _ ≤ (n + 1) * (b + 1) := Nat.mul_le_mul_left (n + 1) (by omega : 2 ≤ b + 1)
    omega
  have hbB : HvdH.isz (b : ℤ) ≤ B := by omega
  have hnB : HvdH.isz (n : ℤ) ≤ B := by omega
  -- ### step 1: `pick 2` (copy `int n`)
  have hs1 : Work.Fx.TopSpec main (pickP 2)
      [HvdH.Val.int x, HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ), HvdH.Val.int C]
      [HvdH.Val.int (n : ℤ), HvdH.Val.int x, HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ),
        HvdH.Val.int C] (6 * Kp * B) := by
    have h := hpick main 2
      [HvdH.Val.int x, HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ), HvdH.Val.int C] (by simp)
    refine Work.Fx.TopSpec.mono hK h rfl ?_ ?_
    · simp
    · have he : Work.Fx.szl
            [HvdH.Val.int x, HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ), HvdH.Val.int C]
            = HvdH.isz (x : ℤ) + HvdH.isz (b : ℤ) + HvdH.isz (n : ℤ) + HvdH.isz C := by
        simp only [Work.Fx.szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          Work.Fx.vsz_int, Nat.add_zero]
        omega
      have hsz : Work.Fx.szl
          [HvdH.Val.int x, HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ), HvdH.Val.int C] + 1
          ≤ 2 * B := by rw [he]; omega
      calc Kp * (2 + 1) * (Work.Fx.szl
            [HvdH.Val.int x, HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ), HvdH.Val.int C] + 1)
          = Kp * (3 * (Work.Fx.szl
            [HvdH.Val.int x, HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ), HvdH.Val.int C]
              + 1)) := by ring
        _ ≤ Kp * (3 * (2 * B)) := Nat.mul_le_mul_left Kp (Nat.mul_le_mul_left 3 hsz)
        _ = 6 * Kp * B := by ring
  -- ### step 2: `pick 2` (copy `int b`)
  have hs2 : Work.Fx.TopSpec main (pickP 2)
      [HvdH.Val.int (n : ℤ), HvdH.Val.int x, HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ),
        HvdH.Val.int C]
      [HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ), HvdH.Val.int x, HvdH.Val.int (b : ℤ),
        HvdH.Val.int (n : ℤ), HvdH.Val.int C] (9 * Kp * B) := by
    have h := hpick main 2
      [HvdH.Val.int (n : ℤ), HvdH.Val.int x, HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ),
        HvdH.Val.int C] (by simp)
    refine Work.Fx.TopSpec.mono hK h rfl ?_ ?_
    · simp
    · have he : Work.Fx.szl
            [HvdH.Val.int (n : ℤ), HvdH.Val.int x, HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ),
              HvdH.Val.int C]
            = HvdH.isz (n : ℤ) + HvdH.isz (x : ℤ) + HvdH.isz (b : ℤ) + HvdH.isz (n : ℤ) +
              HvdH.isz C := by
        simp only [Work.Fx.szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          Work.Fx.vsz_int, Nat.add_zero]
        omega
      have hsz : Work.Fx.szl
          [HvdH.Val.int (n : ℤ), HvdH.Val.int x, HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ),
            HvdH.Val.int C] + 1 ≤ 3 * B := by rw [he]; omega
      calc Kp * (2 + 1) * (Work.Fx.szl
            [HvdH.Val.int (n : ℤ), HvdH.Val.int x, HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ),
              HvdH.Val.int C] + 1)
          = Kp * (3 * (Work.Fx.szl
            [HvdH.Val.int (n : ℤ), HvdH.Val.int x, HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ),
              HvdH.Val.int C] + 1)) := by ring
        _ ≤ Kp * (3 * (3 * B)) := Nat.mul_le_mul_left Kp (Nat.mul_le_mul_left 3 hsz)
        _ = 9 * Kp * B := by ring
  -- ### step 3: `roll 2`
  have hs3 : Work.Fx.TopSpec main (Rl 2)
      [HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ), HvdH.Val.int x, HvdH.Val.int (b : ℤ),
        HvdH.Val.int (n : ℤ), HvdH.Val.int C]
      [HvdH.Val.int x, HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ), HvdH.Val.int (b : ℤ),
        HvdH.Val.int (n : ℤ), HvdH.Val.int C] (12 * Kro * B) := by
    have h := hRl main 2
      [HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ), HvdH.Val.int x, HvdH.Val.int (b : ℤ),
        HvdH.Val.int (n : ℤ), HvdH.Val.int C] (by simp)
    refine Work.Fx.TopSpec.mono hK h rfl ?_ ?_
    · simp
    · have he : Work.Fx.szl
            [HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ), HvdH.Val.int x, HvdH.Val.int (b : ℤ),
              HvdH.Val.int (n : ℤ), HvdH.Val.int C]
            = HvdH.isz (b : ℤ) + HvdH.isz (n : ℤ) + HvdH.isz (x : ℤ) + HvdH.isz (b : ℤ) +
              HvdH.isz (n : ℤ) + HvdH.isz C := by
        simp only [Work.Fx.szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          Work.Fx.vsz_int, Nat.add_zero]
        omega
      have hsz : Work.Fx.szl
          [HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ), HvdH.Val.int x, HvdH.Val.int (b : ℤ),
            HvdH.Val.int (n : ℤ), HvdH.Val.int C] + 1 ≤ 4 * B := by rw [he]; omega
      calc Kro * (2 + 1) * (Work.Fx.szl
            [HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ), HvdH.Val.int x, HvdH.Val.int (b : ℤ),
              HvdH.Val.int (n : ℤ), HvdH.Val.int C] + 1)
          = Kro * (3 * (Work.Fx.szl
            [HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ), HvdH.Val.int x, HvdH.Val.int (b : ℤ),
              HvdH.Val.int (n : ℤ), HvdH.Val.int C] + 1)) := by ring
        _ ≤ Kro * (3 * (4 * B)) := Nat.mul_le_mul_left Kro (Nat.mul_le_mul_left 3 hsz)
        _ = 12 * Kro * B := by ring
  -- ### step 4: `chunk`
  have hs4 : Work.Fx.TopSpec main ckP
      [HvdH.Val.int x, HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ)]
      [HvdH.intList (HvdH.chunks x b n)]
      (Kc * (HvdH.isz (x : ℤ) + n * (b + 1) + HvdH.isz (b : ℤ) + HvdH.isz (n : ℤ))) := by
    intro rest
    refine hK.conseq (main := main) (p := ckP)
      (P := fun vs => ∃ rest : List HvdH.Val,
        vs = HvdH.Val.int x :: HvdH.Val.int (b : ℤ) :: HvdH.Val.int (n : ℤ) :: rest)
      (Q := fun vs out => ∃ rest : List HvdH.Val,
        vs = HvdH.Val.int x :: HvdH.Val.int (b : ℤ) :: HvdH.Val.int (n : ℤ) :: rest ∧
        out = HvdH.intList (HvdH.chunks x b n) :: rest)
      (C := fun _ => Kc * (HvdH.isz (x : ℤ) + n * (b + 1) + HvdH.isz (b : ℤ) + HvdH.isz (n : ℤ)))
      (P' := fun vs => vs = [HvdH.Val.int x, HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ)] ++ rest)
      (Q' := fun _ out => out = [HvdH.intList (HvdH.chunks x b n)] ++ rest)
      (C' := fun _ => Kc * (HvdH.isz (x : ℤ) + n * (b + 1) + HvdH.isz (b : ℤ) + HvdH.isz (n : ℤ)))
      (hck main x b n hb hxlt) ?_ ?_ ?_
    · intro vs hv
      exact ⟨rest, by simpa using hv⟩
    · intro vs out hv hq
      obtain ⟨rest', hvs, hout⟩ := hq
      rw [hv] at hvs
      have hr : rest = rest' :=
        Work.Fx.tail_eq_of_append_eq (A := [HvdH.Val.int x, HvdH.Val.int (b : ℤ),
          HvdH.Val.int (n : ℤ)]) (B := [HvdH.Val.int x, HvdH.Val.int (b : ℤ),
          HvdH.Val.int (n : ℤ)]) rfl (by simpa using hvs)
      rw [hout, ← hr]
      rfl
    · intro vs hv
      exact le_refl _
  have hs4' : Work.Fx.TopSpec main ckP
      [HvdH.Val.int x, HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ), HvdH.Val.int (b : ℤ),
        HvdH.Val.int (n : ℤ), HvdH.Val.int C]
      [HvdH.intList (HvdH.chunks x b n), HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ),
        HvdH.Val.int C] (4 * Kc * B) := by
    refine Work.Fx.TopSpec.mono hK (Work.Fx.TopSpec.extend hs4
      [HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ), HvdH.Val.int C]) rfl rfl ?_
    have h1 : HvdH.isz (x : ℤ) + n * (b + 1) + HvdH.isz (b : ℤ) + HvdH.isz (n : ℤ) ≤ 4 * B := by
      omega
    calc Kc * (HvdH.isz (x : ℤ) + n * (b + 1) + HvdH.isz (b : ℤ) + HvdH.isz (n : ℤ))
        ≤ Kc * (4 * B) := Nat.mul_le_mul_left Kc h1
      _ = 4 * Kc * B := by ring
  -- ### assemble
  have hA : Work.Fx.TopSpec main (.seq (.seq (pickP 2) (pickP 2)) (Rl 2))
      [HvdH.Val.int x, HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ), HvdH.Val.int C]
      [HvdH.Val.int x, HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ), HvdH.Val.int (b : ℤ),
        HvdH.Val.int (n : ℤ), HvdH.Val.int C] (6 * Kp * B + 9 * Kp * B + 12 * Kro * B) :=
    Work.Fx.TopSpec.seq hK (Work.Fx.TopSpec.seq hK hs1 hs2) hs3
  have hall : Work.Fx.TopSpec main (.seq (.seq (.seq (pickP 2) (pickP 2)) (Rl 2)) ckP)
      [HvdH.Val.int x, HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ), HvdH.Val.int C]
      [HvdH.intList (HvdH.chunks x b n), HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ),
        HvdH.Val.int C] (6 * Kp * B + 9 * Kp * B + 12 * Kro * B + 4 * Kc * B) :=
    Work.Fx.TopSpec.seq hK hA hs4'
  exact Work.Fx.TopSpec.mono hK hall rfl rfl (by
    rw [hB]
    nlinarith [Nat.zero_le Kp, Nat.zero_le Kro, Nat.zero_le Kc, hxB, hCB, hnb, hn1f])

/-! ## The per-element word of the Kronecker `zipWith` -/

theorem prodDigits (hK : HvdH.KernelLib) (hI : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm →
      HvdH.MulBelow main N Cm → ∀ (X Y : ℤ) (b n : ℕ) (C : ℤ) (rest : List HvdH.Val),
      X.natAbs.size < N → Y.natAbs.size < N → 1 ≤ b → 1 ≤ n → 0 ≤ X * Y + C →
      X * Y + C < 2 ^ (b * n) →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.Val.int X :: HvdH.Val.int Y ::
            HvdH.Val.int (b : ℤ) :: HvdH.Val.int (n : ℤ) :: HvdH.Val.int C :: rest)
        (fun _ out => out = HvdH.intList (HvdH.chunks (X * Y + C).toNat b n) ::
            HvdH.Val.int (b : ℤ) :: HvdH.Val.int (n : ℤ) :: HvdH.Val.int C :: rest)
        (fun _ => Cm (max X.natAbs.size Y.natAbs.size) +
          K * (X.natAbs.size + Y.natAbs.size + (n + 1) * (b + 1) + C.natAbs.size + 1)) := by
  obtain ⟨prP, K1, hpr⟩ := prepC hK
  obtain ⟨spP, K2, hsp⟩ := signedProd hK hI
  obtain ⟨adP, Kad, had⟩ := hI.add
  obtain ⟨ckP, K3, hck⟩ := chunkRestore hK hI
  refine ⟨.seq (.seq (.seq prP spP) adP) ckP, 1000 * (K1 + K2 + Kad + K3 + 1), ?_⟩
  intro main N Cm hmono hmul X Y b n C rest hX hY hb hn hnonneg hlt
  set S : ℕ := X.natAbs.size + Y.natAbs.size + (n + 1) * (b + 1) + C.natAbs.size + 1 with hS
  have hiszX : HvdH.isz X = X.natAbs.size + 2 := rfl
  have hiszY : HvdH.isz Y = Y.natAbs.size + 2 := rfl
  have hiszC : HvdH.isz C = C.natAbs.size + 2 := rfl
  have hiszb : HvdH.isz (b : ℤ) = b.size + 2 := rfl
  have hiszn : HvdH.isz (n : ℤ) = n.size + 2 := rfl
  have hS1 : 1 ≤ S := by omega
  have hXB : HvdH.isz X ≤ 3 * S := by rw [hiszX]; omega
  have hYB : HvdH.isz Y ≤ 3 * S := by rw [hiszY]; omega
  have hCB : HvdH.isz C ≤ 3 * S := by rw [hiszC]; omega
  have hbB : HvdH.isz (b : ℤ) ≤ S := by
    rw [hiszb]
    have h1 : b.size ≤ b := Nat.size_le.mpr (Nat.lt_two_pow_self (n := b))
    have h2 : 2 * (b + 1) ≤ (n + 1) * (b + 1) :=
      Nat.mul_le_mul_right (b + 1) (by omega : 2 ≤ n + 1)
    omega
  have hnB : HvdH.isz (n : ℤ) ≤ S := by
    rw [hiszn]
    have h1 : n.size ≤ n := Nat.size_le.mpr (Nat.lt_two_pow_self (n := n))
    have h2 : 2 * (n + 1) ≤ (n + 1) * (b + 1) := by
      calc 2 * (n + 1) = (n + 1) * 2 := by ring
        _ ≤ (n + 1) * (b + 1) := Nat.mul_le_mul_left (n + 1) (by omega : 2 ≤ b + 1)
    omega
  -- the `toNat` facts
  have htoNat : (((X * Y + C).toNat : ℕ) : ℤ) = X * Y + C := Int.toNat_of_nonneg hnonneg
  have hxN : (X * Y + C).toNat < 2 ^ (b * n) := by
    rw [Int.toNat_lt hnonneg]
    simpa using hlt
  have hxSZ : HvdH.isz (((X * Y + C).toNat : ℕ) : ℤ) ≤ 2 * S := by
    have h1 : (X * Y + C).toNat.size ≤ b * n := Nat.size_le.mpr hxN
    have h2 : b * n ≤ (n + 1) * (b + 1) := by nlinarith
    simp only [HvdH.isz, Int.natAbs_natCast]
    omega
  have hxy : HvdH.isz (X * Y) ≤ 4 * S := by
    have h1 : (X * Y + C).natAbs.size ≤ b * n := by
      rw [natAbs_of_nonneg' hnonneg]
      exact Nat.size_le.mpr hxN
    have h2 : ((X * Y + C) - C).natAbs.size ≤ max (X * Y + C).natAbs.size C.natAbs.size + 1 :=
      Work.Fx.natAbs_sub_size_le _ _
    have h3 : (X * Y + C) - C = X * Y := by ring
    rw [h3] at h2
    have h4 : (X * Y).natAbs.size ≤ S + 1 := by
      have h5 : max (X * Y + C).natAbs.size C.natAbs.size ≤ S := by
        apply max_le
        · have h6 : b * n ≤ (n + 1) * (b + 1) := by nlinarith
          omega
        · omega
      omega
    simp only [HvdH.isz]
    omega
  -- ### the four steps
  have h1 : Work.Fx.TopSpec main prP
      [HvdH.Val.int X, HvdH.Val.int Y, HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ),
        HvdH.Val.int C]
      [HvdH.Val.int X, HvdH.Val.int Y, HvdH.Val.int C, HvdH.Val.int (b : ℤ),
        HvdH.Val.int (n : ℤ), HvdH.Val.int C]
      (K1 * (HvdH.isz X + HvdH.isz Y + HvdH.isz (b : ℤ) + HvdH.isz (n : ℤ) +
        HvdH.isz C + 1)) := hpr main X Y b n C
  have h2 : Work.Fx.TopSpec main spP
      [HvdH.Val.int X, HvdH.Val.int Y, HvdH.Val.int C, HvdH.Val.int (b : ℤ),
        HvdH.Val.int (n : ℤ), HvdH.Val.int C]
      [HvdH.Val.int (X * Y), HvdH.Val.int C, HvdH.Val.int (b : ℤ),
        HvdH.Val.int (n : ℤ), HvdH.Val.int C]
      (Cm (max X.natAbs.size Y.natAbs.size) + K2 * (HvdH.isz X + HvdH.isz Y + 1)) := by
    simpa using Work.Fx.TopSpec.extend (hsp main N Cm hmono hmul X Y hX hY)
      [HvdH.Val.int C, HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ), HvdH.Val.int C]
  have h3 : Work.Fx.TopSpec main adP
      [HvdH.Val.int (X * Y), HvdH.Val.int C, HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ),
        HvdH.Val.int C]
      [HvdH.Val.int (X * Y + C), HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ),
        HvdH.Val.int C] (Kad * (HvdH.isz (X * Y) + HvdH.isz C)) := by
    simpa using Work.Fx.TopSpec.extend
      (Work.Fx.TopSpec.binOp hK (had main) (a := X * Y) (b := C) trivial)
      [HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ), HvdH.Val.int C]
  have h4 : Work.Fx.TopSpec main ckP
      [HvdH.Val.int (X * Y + C), HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ),
        HvdH.Val.int C]
      [HvdH.intList (HvdH.chunks (X * Y + C).toNat b n), HvdH.Val.int (b : ℤ),
        HvdH.Val.int (n : ℤ), HvdH.Val.int C]
      (K3 * (HvdH.isz (((X * Y + C).toNat : ℕ) : ℤ) + (n + 1) * (b + 1) + HvdH.isz C + 1)) := by
    refine Work.Fx.TopSpec.mono hK (hck main (X * Y + C).toNat b n C hb hn hxN) ?_ rfl
      (le_refl _)
    simp only [htoNat]
  have hchain : Work.Fx.TopSpec main (.seq (.seq (.seq prP spP) adP) ckP)
      [HvdH.Val.int X, HvdH.Val.int Y, HvdH.Val.int (b : ℤ), HvdH.Val.int (n : ℤ),
        HvdH.Val.int C]
      [HvdH.intList (HvdH.chunks (X * Y + C).toNat b n), HvdH.Val.int (b : ℤ),
        HvdH.Val.int (n : ℤ), HvdH.Val.int C]
      ((K1 * (HvdH.isz X + HvdH.isz Y + HvdH.isz (b : ℤ) + HvdH.isz (n : ℤ) +
          HvdH.isz C + 1) +
        (Cm (max X.natAbs.size Y.natAbs.size) + K2 * (HvdH.isz X + HvdH.isz Y + 1)) +
        Kad * (HvdH.isz (X * Y) + HvdH.isz C)) +
        K3 * (HvdH.isz (((X * Y + C).toNat : ℕ) : ℤ) + (n + 1) * (b + 1) + HvdH.isz C + 1)) :=
    Work.Fx.TopSpec.seq hK (Work.Fx.TopSpec.seq hK (Work.Fx.TopSpec.seq hK h1 h2) h3) h4
  refine hK.conseq (main := main) (p := (.seq (.seq (.seq prP spP) adP) ckP)) _ _ _ _ _ _
    (hchain rest) ?_ ?_ ?_
  · intro vs hv
    simpa using hv
  · intro vs out hv hq
    simpa using hq
  · intro vs hv
    have e1 : K1 * (HvdH.isz X + HvdH.isz Y + HvdH.isz (b : ℤ) + HvdH.isz (n : ℤ) +
        HvdH.isz C + 1) ≤ K1 * (11 * S + 1) := Nat.mul_le_mul_left K1 (by omega)
    have e2 : K2 * (HvdH.isz X + HvdH.isz Y + 1) ≤ K2 * (6 * S + 1) :=
      Nat.mul_le_mul_left K2 (by omega)
    have e3 : Kad * (HvdH.isz (X * Y) + HvdH.isz C) ≤ Kad * (7 * S) :=
      Nat.mul_le_mul_left Kad (by omega)
    have e4 : K3 * (HvdH.isz (((X * Y + C).toNat : ℕ) : ℤ) + (n + 1) * (b + 1) +
        HvdH.isz C + 1) ≤ K3 * (6 * S + 1) := Nat.mul_le_mul_left K3 (by omega)
    nlinarith [e1, e2, e3, e4, Nat.zero_le K1, Nat.zero_le K2, Nat.zero_le Kad,
      Nat.zero_le K3, hS1]

end Work.KronP
