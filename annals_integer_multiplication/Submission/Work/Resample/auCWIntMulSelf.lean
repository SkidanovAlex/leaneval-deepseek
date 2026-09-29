import Mathlib
import Submission.Work.Resample.auKit
import Submission.Work.Resample.auCWDefs
import Submission.Work.Fx.mulFField

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.Resample

open HvdH

/-!
# `Work.Resample.auCWIntMulSelf`

`Pipe main prog [int a, int b] [int (a*b)]` at cost `Cm (max size) + O (size a + size b)`, where
`self` (`MulBelow main N Cm`) is used once, on the two *magnitudes* `|a|, |b|`:

* **front** (`auCWMulFront_aux`): `[int a, int b] ↦ [int |a|, int |b|, int (sign b), int (sign a)]`
  (two `Work.Fx.TopSpec.absSgn` and two rolls `k = 2`), cost `O (isz a + isz b)`;
* **middle**: `self` multiplies the magnitudes `|a|, |b|` (top two values), cost `Cm (max · ·)`;
* **tail** (`auCWMulTail_aux`): `[int (|a|·|b|), int (sign b), int (sign a)] ↦ [int (a*b)]`
  (two `IntLib.mulS`), cost `O (isz (|a|·|b|)) = O (size a + size b)`.
-/

/-- `(Int.sign a).natAbs ≤ 1`. -/
theorem auCW_sgn_natAbs_le (a : ℤ) : (Int.sign a).natAbs ≤ 1 := by
  rw [Int.natAbs_sign]; split <;> omega

/-- `↑(m · n) : ℤ` has `natAbs` at most `2 ^ (m.size + n.size)`. -/
theorem auCW_prod_natAbs_le {m n : ℕ} : ((m * n : ℕ) : ℤ).natAbs ≤ 2 ^ (m.size + n.size) := by
  rw [Int.natAbs_natCast]
  exact le_of_lt (lt_of_lt_of_le (Nat.mul_lt_mul'' (Nat.lt_size_self m) (Nat.lt_size_self n))
    (le_of_eq (Nat.pow_add 2 m.size n.size).symm))

/-- `|a| · |b| · sign b · sign a = a · b`. -/
theorem auCW_mul_sign (a b : ℤ) :
    (((a.natAbs * b.natAbs : ℕ) : ℤ) * Int.sign b) * Int.sign a = a * b := by
  have h1 : (a.natAbs : ℤ) * Int.sign a = a := by rw [mul_comm]; exact Int.sign_mul_natAbs a
  have h2 : (b.natAbs : ℤ) * Int.sign b = b := by rw [mul_comm]; exact Int.sign_mul_natAbs b
  calc (((a.natAbs * b.natAbs : ℕ) : ℤ) * Int.sign b) * Int.sign a
      = ((a.natAbs : ℤ) * Int.sign a) * ((b.natAbs : ℤ) * Int.sign b) := by
        push_cast; ring
    _ = a * b := by rw [h1, h2]

/-! ## The front piece -/

theorem auCWMulFront_aux (hk : HvdH.KernelLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (a b : ℤ),
      Work.Fx.TopSpec main prog [.int a, .int b]
        [.int (a.natAbs : ℤ), .int (b.natAbs : ℤ), .int (Int.sign b), .int (Int.sign a)]
        (K * (a.natAbs.size + b.natAbs.size + 1)) := by
  obtain ⟨AS, Kas, hAS⟩ := Work.Fx.TopSpec.absSgn hk hi
  obtain ⟨Rl, Kro, hRl⟩ := Work.Fx.TopSpec.rollS hk
  set KB : ℕ := 1000000 * (Kas + Kro + 1) with hKB
  have hKas : Kas * 1000000 ≤ KB := by rw [hKB]; exact Work.Fx.coeffK (by omega)
  have hKro : Kro * 1000000 ≤ KB := by rw [hKB]; exact Work.Fx.coeffK (by omega)
  refine ⟨.seq (.seq (.seq AS (Rl 2)) AS) (Rl 2), 4 * KB, ?_⟩
  intro main a b
  set p : ℕ := a.natAbs.size + b.natAbs.size with hp
  have han : a.natAbs ≤ 2 ^ p := by
    rw [hp]
    exact le_of_lt (lt_of_lt_of_le (Nat.lt_size_self a.natAbs)
      (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hbn : b.natAbs ≤ 2 ^ p := by
    rw [hp]
    exact le_of_lt (lt_of_lt_of_le (Nat.lt_size_self b.natAbs)
      (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hiA : isz a ≤ 1000 * (p + 1) := Work.Fx.isz_le_M han
  have hiB : isz b ≤ 1000 * (p + 1) := Work.Fx.isz_le_M hbn
  have hiAabs : isz ((a.natAbs : ℤ)) ≤ 1000 * (p + 1) := by
    have h : isz ((a.natAbs : ℤ)) = isz a := by rw [isz, isz, Int.natAbs_natCast]
    rw [h]; exact hiA
  have hiBabs : isz ((b.natAbs : ℤ)) ≤ 1000 * (p + 1) := by
    have h : isz ((b.natAbs : ℤ)) = isz b := by rw [isz, isz, Int.natAbs_natCast]
    rw [h]; exact hiB
  have hiSA : isz (Int.sign a) ≤ 1000 * (p + 1) := by
    have := Work.Fx.isz_sign_le a; omega
  have hiSB : isz (Int.sign b) ≤ 1000 * (p + 1) := by
    have := Work.Fx.isz_sign_le b; omega
  have hvA : vsz (.int a) ≤ 3000 * (p + 1) := by rw [Work.Fx.vsz_int]; have := hiA; omega
  have hvB : vsz (.int b) ≤ 3000 * (p + 1) := by rw [Work.Fx.vsz_int]; have := hiB; omega
  have hvAabs : vsz (.int (a.natAbs : ℤ)) ≤ 3000 * (p + 1) := by
    rw [Work.Fx.vsz_int]; have := hiAabs; omega
  have hvBabs : vsz (.int (b.natAbs : ℤ)) ≤ 3000 * (p + 1) := by
    rw [Work.Fx.vsz_int]; have := hiBabs; omega
  have hvSA : vsz (.int (Int.sign a)) ≤ 3000 * (p + 1) := by
    rw [Work.Fx.vsz_int]; have := hiSA; omega
  have hvSB : vsz (.int (Int.sign b)) ≤ 3000 * (p + 1) := by
    rw [Work.Fx.vsz_int]; have := hiSB; omega
  have sa1 : Work.Fx.TopSpec main AS [.int a, .int b]
      [.int (a.natAbs : ℤ), .int (Int.sign a), .int b] (KB * (p + 1)) := by
    refine Work.Fx.TopSpec.mono hk (Work.Fx.TopSpec.extend (hAS main a) [.int b]) rfl (by simp) ?_
    exact Work.Fx.cost_one_x1 hKas (by have := hiA; omega)
  have sr2 : Work.Fx.TopSpec main (Rl 2) [.int (a.natAbs : ℤ), .int (Int.sign a), .int b]
      [.int b, .int (a.natAbs : ℤ), .int (Int.sign a)] (KB * (p + 1)) := by
    refine Work.Fx.TopSpec.mono hk
      (hRl main 2 [.int (a.natAbs : ℤ), .int (Int.sign a), .int b] (by simp)) rfl (by simp) ?_
    exact Work.Fx.cost_roll hKro (by norm_num)
      (Work.Fx.szl_bnd3 p (.int (a.natAbs : ℤ)) (.int (Int.sign a)) (.int b)
        hvAabs hvSA hvB)
  have sa3 : Work.Fx.TopSpec main AS [.int b, .int (a.natAbs : ℤ), .int (Int.sign a)]
      [.int (b.natAbs : ℤ), .int (Int.sign b), .int (a.natAbs : ℤ), .int (Int.sign a)]
      (KB * (p + 1)) := by
    refine Work.Fx.TopSpec.mono hk
      (Work.Fx.TopSpec.extend (hAS main b) [.int (a.natAbs : ℤ), .int (Int.sign a)])
      rfl (by simp) ?_
    exact Work.Fx.cost_one_x1 hKas (by have := hiB; omega)
  have sr4 : Work.Fx.TopSpec main (Rl 2)
      [.int (b.natAbs : ℤ), .int (Int.sign b), .int (a.natAbs : ℤ), .int (Int.sign a)]
      [.int (a.natAbs : ℤ), .int (b.natAbs : ℤ), .int (Int.sign b), .int (Int.sign a)]
      (KB * (p + 1)) := by
    refine Work.Fx.TopSpec.mono hk
      (hRl main 2 [.int (b.natAbs : ℤ), .int (Int.sign b), .int (a.natAbs : ℤ),
        .int (Int.sign a)] (by simp)) rfl (by simp) ?_
    exact Work.Fx.cost_roll hKro (by norm_num)
      (Work.Fx.szl_bnd4 p (.int (b.natAbs : ℤ)) (.int (Int.sign b)) (.int (a.natAbs : ℤ))
        (.int (Int.sign a)) hvBabs hvSB hvAabs hvSA)
  have h12 := Work.Fx.TopSpec.seq hk sa1 sr2
  have h123 := Work.Fx.TopSpec.seq hk h12 sa3
  have h1234 := Work.Fx.TopSpec.seq hk h123 sr4
  exact Work.Fx.TopSpec.mono hk h1234 rfl rfl (le_of_eq (by ring))

/-! ## The tail piece -/

theorem auCWMulTail_aux (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (a b : ℤ),
      Pipe main prog
        [.int ((a.natAbs * b.natAbs : ℕ) : ℤ), .int (Int.sign b), .int (Int.sign a)]
        [.int (a * b)] (K * (a.natAbs.size + b.natAbs.size + 1)) := by
  obtain ⟨MS, Kms, hms⟩ := hi.mulS
  set KB : ℕ := 1000000 * (Kms + 1) with hKB
  have hKms : Kms * 1000000 ≤ KB := by rw [hKB]; exact Work.Fx.coeffK (by omega)
  refine ⟨.seq MS MS, 2 * KB, ?_⟩
  intro main a b
  set p : ℕ := a.natAbs.size + b.natAbs.size with hp
  set P : ℤ := ((a.natAbs * b.natAbs : ℕ) : ℤ) with hP
  set ea : ℤ := Int.sign a with hea
  set eb : ℤ := Int.sign b with heb
  have hPn : P.natAbs ≤ 2 ^ p := by
    rw [hP, hp]
    exact auCW_prod_natAbs_le
  have hiP : isz P ≤ 1000 * (p + 1) := Work.Fx.isz_le_M hPn
  have hiP3000 : isz P ≤ 3000 * (p + 1) := by omega
  have hiEB3 : isz eb ≤ 3 := by rw [heb]; exact Work.Fx.isz_sign_le b
  have hiEA3 : isz ea ≤ 3 := by rw [hea]; exact Work.Fx.isz_sign_le a
  have hPBn : (P * eb).natAbs ≤ 2 ^ p := by
    have hb1 : eb.natAbs ≤ 1 := by rw [heb]; exact auCW_sgn_natAbs_le b
    rw [Int.natAbs_mul]
    calc P.natAbs * eb.natAbs ≤ 2 ^ p * 1 := Nat.mul_le_mul hPn hb1
      _ = 2 ^ p := by ring
  have hiPB3000 : isz (P * eb) ≤ 3000 * (p + 1) := by
    have h := Work.Fx.isz_le_M hPBn; omega
  have st1 : Pipe main MS [.int P, .int eb, .int ea] [.int (P * eb), .int ea]
      (KB * (p + 1)) := by
    refine Pipe.le (Pipe.appendTail [.int ea] (Pipe.binOp (hms main) trivial)) ?_
    calc Kms * isz P * isz eb = Kms * isz eb * isz P := by ring
      _ ≤ KB * (p + 1) := Work.Fx.cost_smallmul hKms hiEB3 hiP3000
  have hmul : (P * eb) * ea = a * b := by
    rw [hP, hea, heb]
    exact auCW_mul_sign a b
  have st2 : Pipe main MS [.int (P * eb), .int ea] [.int ((P * eb) * ea)]
      (KB * (p + 1)) := by
    refine Pipe.le (Pipe.binOp (hms main) trivial) ?_
    calc Kms * isz (P * eb) * isz ea = Kms * isz ea * isz (P * eb) := by ring
      _ ≤ KB * (p + 1) := Work.Fx.cost_smallmul hKms hiEA3 hiPB3000
  have hchain : Pipe main (.seq MS MS) [.int P, .int eb, .int ea] [.int ((P * eb) * ea)]
      (KB * (p + 1) + KB * (p + 1)) := Pipe.comp st1 st2
  refine Pipe.le (Pipe.rw hchain ?_) ?_
  · rw [hmul]
  · exact le_of_eq (by ring)

/-! ## Assembly -/

theorem auCWIntMulSelf (hk : HvdH.KernelLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm →
      HvdH.MulBelow main N Cm → ∀ (a b : ℤ), a.natAbs.size < N → b.natAbs.size < N →
      Work.Resample.Pipe main prog [HvdH.Val.int a, HvdH.Val.int b] [HvdH.Val.int (a * b)]
        (Cm (max a.natAbs.size b.natAbs.size) + K * (a.natAbs.size + b.natAbs.size + 1)) := by
  obtain ⟨F, Kf, hF⟩ := auCWMulFront_aux hk hi
  obtain ⟨T, Kt, hT⟩ := auCWMulTail_aux hi
  refine ⟨.seq (.seq F .self) T, Kf + Kt + 1, ?_⟩
  intro main N Cm hmono hmul a b ha hb
  have hfront : Pipe main F [.int a, .int b]
      [.int (a.natAbs : ℤ), .int (b.natAbs : ℤ), .int (Int.sign b), .int (Int.sign a)]
      (Kf * (a.natAbs.size + b.natAbs.size + 1)) := hF main a b
  have hself : Pipe main .self
      [.int (a.natAbs : ℤ), .int (b.natAbs : ℤ), .int (Int.sign b), .int (Int.sign a)]
      [.int ((a.natAbs * b.natAbs : ℕ) : ℤ), .int (Int.sign b), .int (Int.sign a)]
      (Cm (max a.natAbs.size b.natAbs.size)) :=
    Work.Fx.TopSpec.extend
      (Work.Fx.TopSpec.selfMul hk hmul (x := a.natAbs) (y := b.natAbs) ha hb)
      [.int (Int.sign b), .int (Int.sign a)]
  have htail : Pipe main T
      [.int ((a.natAbs * b.natAbs : ℕ) : ℤ), .int (Int.sign b), .int (Int.sign a)]
      [.int (a * b)] (Kt * (a.natAbs.size + b.natAbs.size + 1)) := hT main a b
  have h1 := Pipe.comp hfront hself
  have h2 := Pipe.comp h1 htail
  refine Pipe.le h2 ?_
  have hsplit : (Kf + Kt + 1) * (a.natAbs.size + b.natAbs.size + 1)
      = Kf * (a.natAbs.size + b.natAbs.size + 1)
        + Kt * (a.natAbs.size + b.natAbs.size + 1)
        + (a.natAbs.size + b.natAbs.size + 1) := by ring
  rw [hsplit]
  omega

end Work.Resample
