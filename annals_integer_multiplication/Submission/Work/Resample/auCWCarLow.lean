import Mathlib
import Submission.Work.Resample.auKit

/-!
# `Work.Resample.auCWCarLow`: the one-step carry / low-part word

From the three values `M, lo, A` with `0 ≤ lo < M` and `0 ≤ A ≤ M` the word produces

* `int ((lo + A) - tdiv (lo + A) M * M)` (the low part, `lo + A` reduced mod `M`), and
* `int (tdiv (lo + A) M)` (the carry, `∈ {0,1}`),

at cost linear in the sizes of the three inputs.  The point is that `0 ≤ lo + A < 2M`, so the
quotient is `0` or `1` and is decided by the *comparison* `lo + A < M`; no division is needed
(a division would cost a product of the two sizes).

The word is the fixed sequence

* `roll 2`, `roll 2` (bring `lo`, `A` to the top), `add` (giving `lo + A`),
* `dup`, `pick 2`, `swap`, `lt` (the flag `lo + A < M`, on copies), `pushVal 1`, `sub` (the carry
  `q = 1 - flag`),
* `dup`, `roll 3`, `swap`, `mulS` (`q * M`), `roll 2`, `sub` (giving `lo + A - q * M`),

fifteen primitive words, each of cost `≤ clBud Λ ρ` where `ρ = isz M + isz lo + isz A + 1` and
`Λ` is one plus the sum of the library constants.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Resample

open HvdH Work.Fx

local infixl:68 " ;;; " => HvdH.Cmd.seq

/-! ## Budgets -/

/-- `isz` is always at least `2`. -/
theorem two_le_isz (z : ℤ) : 2 ≤ isz z := by simp [isz]

/-- The uniform one-step budget of the carry word: `Λ` bounds every library constant and `ρ` is an
upper bound for every size occurring in the computation. -/
def clBud (Λ ρ : ℕ) : ℕ := 40 * (Λ * ρ)

theorem clBud_one {Λ ρ K u : ℕ} (hρ : 1 ≤ ρ) (hK : K ≤ Λ) (hu : u ≤ ρ) :
    K * (u + 1) ≤ clBud Λ ρ := by
  rw [clBud]
  have h1 : K * (u + 1) ≤ Λ * (ρ + 1) := Nat.mul_le_mul hK (by omega)
  have h2 : ρ + 1 ≤ 2 * ρ := by omega
  calc K * (u + 1) ≤ Λ * (ρ + 1) := h1
    _ ≤ Λ * (2 * ρ) := Nat.mul_le_mul_left _ h2
    _ = 2 * (Λ * ρ) := by ring
    _ ≤ 40 * (Λ * ρ) := Nat.mul_le_mul_right _ (by norm_num)

theorem clBud_two {Λ ρ K u v : ℕ} (hρ : 1 ≤ ρ) (hK : K ≤ Λ) (hu : u ≤ ρ) (hv : v ≤ ρ) :
    K * (u + v) ≤ clBud Λ ρ := by
  rw [clBud]
  calc K * (u + v) ≤ Λ * (2 * ρ) := Nat.mul_le_mul hK (by omega)
    _ = 2 * (Λ * ρ) := by ring
    _ ≤ 40 * (Λ * ρ) := Nat.mul_le_mul_right _ (by norm_num)

theorem clBud_two_one {Λ ρ K u v : ℕ} (hρ : 1 ≤ ρ) (hK : K ≤ Λ) (hu : u ≤ ρ) (hv : v ≤ ρ) :
    K * (u + v + 1) ≤ clBud Λ ρ := by
  rw [clBud]
  calc K * (u + v + 1) ≤ Λ * (3 * ρ) := Nat.mul_le_mul hK (by omega)
    _ = 3 * (Λ * ρ) := by ring
    _ ≤ 40 * (Λ * ρ) := Nat.mul_le_mul_right _ (by norm_num)

theorem clBud_const {Λ ρ K c : ℕ} (hρ : 1 ≤ ρ) (hK : K ≤ Λ) (hc : c ≤ 6) :
    K * c ≤ clBud Λ ρ := by
  rw [clBud]
  have h2 : 6 ≤ 6 * ρ := by omega
  calc K * c ≤ Λ * 6 := Nat.mul_le_mul hK hc
    _ ≤ Λ * (6 * ρ) := Nat.mul_le_mul_left _ h2
    _ = 6 * (Λ * ρ) := by ring
    _ ≤ 40 * (Λ * ρ) := Nat.mul_le_mul_right _ (by norm_num)

theorem clBud_mul {Λ ρ K u v : ℕ} (hρ : 1 ≤ ρ) (hK : K ≤ Λ) (hu : u ≤ 3) (hv : v ≤ ρ) :
    K * u * v ≤ clBud Λ ρ := by
  rw [clBud]
  calc K * u * v ≤ Λ * 3 * ρ := Nat.mul_le_mul (Nat.mul_le_mul hK hu) hv
    _ = 3 * (Λ * ρ) := by ring
    _ ≤ 40 * (Λ * ρ) := Nat.mul_le_mul_right _ (by norm_num)

theorem clBud_roll {Λ ρ K k B : ℕ} (hρ : 1 ≤ ρ) (hK : K ≤ Λ) (hk : k + 1 ≤ 4)
    (hB : B ≤ 4 * ρ) : K * (k + 1) * (B + 1) ≤ clBud Λ ρ := by
  rw [clBud]
  have h1 : K * (k + 1) ≤ Λ * 4 := Nat.mul_le_mul hK hk
  have h2 : B + 1 ≤ 5 * ρ := by omega
  calc K * (k + 1) * (B + 1) ≤ Λ * 4 * (5 * ρ) := Nat.mul_le_mul h1 h2
    _ = 20 * (Λ * ρ) := by ring
    _ ≤ 40 * (Λ * ρ) := Nat.mul_le_mul_right _ (by norm_num)

/-- `Pipe` composition with an explicit cost bound on the sum. -/
theorem Pipe.comp_le {main p q : Cmd} {A B D : List Val} {c d e : ℕ} (h1 : Pipe main p A B c)
    (h2 : Pipe main q B D d) (h : c + d ≤ e) : Pipe main (p ;;; q) A D e :=
  Pipe.le (Pipe.comp h1 h2) h

/-! ## The arithmetic of the quotient -/

/-- With `0 ≤ lo < M` and `0 ≤ A ≤ M` one has `0 ≤ lo + A < 2M`, so the quotient of `lo + A` by `M`
is `1` exactly when `M ≤ lo + A`; equivalently it is `1 - [lo + A < M]`. -/
theorem tdiv_eq_one_sub (M lo A : ℤ) (hlo : 0 ≤ lo) (hloM : lo < M) (hA : 0 ≤ A) (hAM : A ≤ M) :
    Int.tdiv (lo + A) M = 1 - (if lo + A < M then (1 : ℤ) else 0) := by
  have hs0 : 0 ≤ lo + A := by linarith
  have hMpos : (0 : ℤ) < M := by linarith
  rw [Int.tdiv_eq_ediv_of_nonneg hs0]
  by_cases h : lo + A < M
  · rw [if_pos h]
    have hz := Int.ediv_eq_zero_of_lt hs0 h
    rw [hz]; ring
  · rw [if_neg h]
    have hMle : M ≤ lo + A := le_of_not_gt h
    have hMne : M ≠ 0 := ne_of_gt hMpos
    have hsub0 : 0 ≤ lo + A - M := by linarith
    have hsublt : lo + A - M < M := by linarith
    have h4 : (lo + A) / M = ((lo + A - M) + M * 1) / M := by ring_nf
    rw [h4, Int.add_mul_ediv_left (lo + A - M) (b := M) 1 hMne,
      Int.ediv_eq_zero_of_lt hsub0 hsublt]
    ring

/-! ## The word -/

theorem auCWCarLow (hk : HvdH.KernelLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (M lo A : ℤ),
      0 ≤ lo → lo < M → 0 ≤ A → A ≤ M →
      Work.Resample.Pipe main prog
        [HvdH.Val.int M, HvdH.Val.int lo, HvdH.Val.int A]
        [HvdH.Val.int ((lo + A) - Int.tdiv (lo + A) M * M), HvdH.Val.int (Int.tdiv (lo + A) M)]
        (K * (HvdH.isz M + HvdH.isz lo + HvdH.isz A + 1)) := by
  obtain ⟨dupP, Kdup, hdup⟩ := hk.dup
  obtain ⟨swapP, Ksw, hsw⟩ := hk.swap
  obtain ⟨pickP, Kpick, hpick⟩ := hk.pick
  obtain ⟨rollP, Kroll, hroll⟩ := hk.roll
  obtain ⟨pushP, Kpv, hpv⟩ := hk.pushVal
  obtain ⟨addP, Kadd, hadd⟩ := hi.add
  obtain ⟨subP, Ksub, hsub⟩ := hi.sub
  obtain ⟨ltP, Klt, hlt⟩ := hi.lt
  obtain ⟨mulP, Kmul, hmul⟩ := hi.mulS
  let Λ : ℕ := Kdup + Ksw + Kpick + Kroll + Kpv + Kadd + Ksub + Klt + Kmul + 1
  refine ⟨rollP 2 ;;; rollP 2 ;;; addP ;;; dupP ;;; pickP 2 ;;; swapP ;;; ltP ;;; pushP (.int 1) ;;;
    subP ;;; dupP ;;; rollP 3 ;;; swapP ;;; mulP ;;; rollP 2 ;;; subP, 600 * Λ, ?_⟩
  intro main M lo A hlo hloM hA0 hAM
  -- ## the size budget
  let ρ : ℕ := isz M + isz lo + isz A + 1
  have hρdef : ρ = isz M + isz lo + isz A + 1 := rfl
  -- ## the library constants are all `≤ Λ`
  have hLdup : Kdup ≤ Λ := by simp only [Λ]; omega
  have hLsw : Ksw ≤ Λ := by simp only [Λ]; omega
  have hLpick : Kpick ≤ Λ := by simp only [Λ]; omega
  have hLroll : Kroll ≤ Λ := by simp only [Λ]; omega
  have hLpv : Kpv ≤ Λ := by simp only [Λ]; omega
  have hLadd : Kadd ≤ Λ := by simp only [Λ]; omega
  have hLsub : Ksub ≤ Λ := by simp only [Λ]; omega
  have hLlt : Klt ≤ Λ := by simp only [Λ]; omega
  have hLmul : Kmul ≤ Λ := by simp only [Λ]; omega
  -- ## size bounds
  have hM2 : 2 ≤ isz M := two_le_isz M
  have hlo2 : 2 ≤ isz lo := two_le_isz lo
  have hA2 : 2 ≤ isz A := two_le_isz A
  have hρ1 : 1 ≤ ρ := by omega
  have hMle : isz M ≤ ρ := by omega
  have hlole : isz lo ≤ ρ := by omega
  have hAle : isz A ≤ ρ := by omega
  have hsle : isz (lo + A) ≤ ρ := by
    have h := isz_add_le lo A
    simp only [ρ]
    omega
  have hf3 : isz (if lo + A < M then (1 : ℤ) else 0) ≤ 3 := by
    by_cases h : lo + A < M <;> simp [isz, h]
  have hq3 : isz (1 - (if lo + A < M then (1 : ℤ) else 0)) ≤ 3 := by
    by_cases h : lo + A < M <;> simp [isz, h]
  have hqle : isz (1 - (if lo + A < M then (1 : ℤ) else 0)) ≤ ρ := by omega
  have hqMle : isz ((1 - (if lo + A < M then (1 : ℤ) else 0)) * M) ≤ ρ := by
    by_cases h : lo + A < M
    · rw [if_pos h, sub_self, zero_mul]
      simp only [ρ, isz, Int.natAbs_zero, Nat.size_zero]; omega
    · rw [if_neg h, sub_zero, one_mul]; exact hMle
  have h1z : isz (1 : ℤ) = 3 := by simp [isz]
  have hsub1 : isz (1 : ℤ) + isz (if lo + A < M then (1 : ℤ) else 0) ≤ 6 := by omega
  -- ## the quotient identity
  have hqeq : Int.tdiv (lo + A) M = 1 - (if lo + A < M then (1 : ℤ) else 0) :=
    tdiv_eq_one_sub M lo A hlo hloM hA0 hAM
  -- ## the fifteen stages, each of cost `≤ clBud Λ ρ`
  have s1 : Pipe main (rollP 2) [Val.int M, Val.int lo, Val.int A]
      [Val.int A, Val.int M, Val.int lo] (clBud Λ ρ) := by
    refine Pipe.le (Pipe.rw (Pipe.roll main hroll (A := [Val.int M, Val.int lo, Val.int A])
      (k := 2) (by simp)) (by simp)) ?_
    have hszl : szl (([Val.int M, Val.int lo, Val.int A] : List Val).take (2 + 1)) ≤ 4 * ρ := by
      simp [szl, vsz_int]
      omega
    exact clBud_roll hρ1 hLroll (by omega) hszl
  have s2 : Pipe main (rollP 2) [Val.int A, Val.int M, Val.int lo]
      [Val.int lo, Val.int A, Val.int M] (clBud Λ ρ) := by
    refine Pipe.le (Pipe.rw (Pipe.roll main hroll (A := [Val.int A, Val.int M, Val.int lo])
      (k := 2) (by simp)) (by simp)) ?_
    have hszl : szl (([Val.int A, Val.int M, Val.int lo] : List Val).take (2 + 1)) ≤ 4 * ρ := by
      simp [szl, vsz_int]
      omega
    exact clBud_roll hρ1 hLroll (by omega) hszl
  have s3 : Pipe main addP [Val.int lo, Val.int A, Val.int M] [Val.int (lo + A), Val.int M]
      (clBud Λ ρ) := by
    refine Pipe.le (Pipe.appendTail [Val.int M]
      (Pipe.binOp (hadd main) (a := lo) (b := A) trivial)) ?_
    exact clBud_two hρ1 hLadd hlole hAle
  have s4 : Pipe main dupP [Val.int (lo + A), Val.int M]
      [Val.int (lo + A), Val.int (lo + A), Val.int M] (clBud Λ ρ) := by
    refine Pipe.le (Pipe.appendTail [Val.int M] (Pipe.dup main hdup (Val.int (lo + A)))) ?_
    rw [vsz_int]
    exact clBud_one hρ1 hLdup hsle
  have s5 : Pipe main (pickP 2) [Val.int (lo + A), Val.int (lo + A), Val.int M]
      [Val.int M, Val.int (lo + A), Val.int (lo + A), Val.int M] (clBud Λ ρ) := by
    refine Pipe.le (Pipe.rw (Pipe.pick main hpick
      (A := [Val.int (lo + A), Val.int (lo + A), Val.int M]) (k := 2) (by simp)) (by simp)) ?_
    have hszl : szl (([Val.int (lo + A), Val.int (lo + A), Val.int M] : List Val).take (2 + 1))
        ≤ 4 * ρ := by
      simp [szl, vsz_int]
      omega
    exact clBud_roll hρ1 hLpick (by omega) hszl
  have s6 : Pipe main swapP [Val.int M, Val.int (lo + A), Val.int (lo + A), Val.int M]
      [Val.int (lo + A), Val.int M, Val.int (lo + A), Val.int M] (clBud Λ ρ) := by
    refine Pipe.le (Pipe.appendTail [Val.int (lo + A), Val.int M]
      (Pipe.swap main hsw (Val.int M) (Val.int (lo + A)))) ?_
    rw [vsz_int, vsz_int]
    exact clBud_two_one hρ1 hLsw hMle hsle
  have s7 : Pipe main ltP [Val.int (lo + A), Val.int M, Val.int (lo + A), Val.int M]
      [Val.int (if lo + A < M then (1 : ℤ) else 0), Val.int (lo + A), Val.int M]
      (clBud Λ ρ) := by
    refine Pipe.le (Pipe.appendTail [Val.int (lo + A), Val.int M]
      (Pipe.binOp (hlt main) (a := lo + A) (b := M) trivial)) ?_
    exact clBud_two hρ1 hLlt hsle hMle
  have s8 : Pipe main (pushP (.int 1))
      [Val.int (if lo + A < M then (1 : ℤ) else 0), Val.int (lo + A), Val.int M]
      [Val.int 1, Val.int (if lo + A < M then (1 : ℤ) else 0), Val.int (lo + A), Val.int M]
      (clBud Λ ρ) := by
    refine Pipe.le (Pipe.pushOnAny (hpv main (Val.int 1))) ?_
    have hv : vsz (Val.int (1 : ℤ)) + 1 ≤ 6 := by rw [vsz_int]; simp [isz]
    exact clBud_const hρ1 hLpv hv
  have s9 : Pipe main subP
      [Val.int 1, Val.int (if lo + A < M then (1 : ℤ) else 0), Val.int (lo + A), Val.int M]
      [Val.int (1 - (if lo + A < M then (1 : ℤ) else 0)), Val.int (lo + A), Val.int M]
      (clBud Λ ρ) := by
    refine Pipe.le (Pipe.appendTail [Val.int (lo + A), Val.int M]
      (Pipe.binOp (hsub main) (a := (1 : ℤ)) (b := (if lo + A < M then (1 : ℤ) else 0))
        trivial)) ?_
    exact clBud_const hρ1 hLsub hsub1
  have s10 : Pipe main dupP
      [Val.int (1 - (if lo + A < M then (1 : ℤ) else 0)), Val.int (lo + A), Val.int M]
      [Val.int (1 - (if lo + A < M then (1 : ℤ) else 0)),
        Val.int (1 - (if lo + A < M then (1 : ℤ) else 0)), Val.int (lo + A), Val.int M]
      (clBud Λ ρ) := by
    refine Pipe.le (Pipe.appendTail [Val.int (lo + A), Val.int M]
      (Pipe.dup main hdup (Val.int (1 - (if lo + A < M then (1 : ℤ) else 0))))) ?_
    rw [vsz_int]
    exact clBud_one hρ1 hLdup hqle
  have s11 : Pipe main (rollP 3)
      [Val.int (1 - (if lo + A < M then (1 : ℤ) else 0)),
        Val.int (1 - (if lo + A < M then (1 : ℤ) else 0)), Val.int (lo + A), Val.int M]
      [Val.int M, Val.int (1 - (if lo + A < M then (1 : ℤ) else 0)),
        Val.int (1 - (if lo + A < M then (1 : ℤ) else 0)), Val.int (lo + A)]
      (clBud Λ ρ) := by
    refine Pipe.le (Pipe.rw (Pipe.roll main hroll
      (A := [Val.int (1 - (if lo + A < M then (1 : ℤ) else 0)),
        Val.int (1 - (if lo + A < M then (1 : ℤ) else 0)), Val.int (lo + A), Val.int M])
      (k := 3) (by simp)) (by simp)) ?_
    have hszl : szl (([Val.int (1 - (if lo + A < M then (1 : ℤ) else 0)),
        Val.int (1 - (if lo + A < M then (1 : ℤ) else 0)), Val.int (lo + A),
        Val.int M] : List Val).take (3 + 1)) ≤ 4 * ρ := by
      simp [szl, vsz_int]
      omega
    exact clBud_roll hρ1 hLroll (by omega) hszl
  have s12 : Pipe main swapP
      [Val.int M, Val.int (1 - (if lo + A < M then (1 : ℤ) else 0)),
        Val.int (1 - (if lo + A < M then (1 : ℤ) else 0)), Val.int (lo + A)]
      [Val.int (1 - (if lo + A < M then (1 : ℤ) else 0)), Val.int M,
        Val.int (1 - (if lo + A < M then (1 : ℤ) else 0)), Val.int (lo + A)]
      (clBud Λ ρ) := by
    refine Pipe.le (Pipe.appendTail
      [Val.int (1 - (if lo + A < M then (1 : ℤ) else 0)), Val.int (lo + A)]
      (Pipe.swap main hsw (Val.int M) (Val.int (1 - (if lo + A < M then (1 : ℤ) else 0))))) ?_
    rw [vsz_int, vsz_int]
    exact clBud_two_one hρ1 hLsw hMle hqle
  have s13 : Pipe main mulP
      [Val.int (1 - (if lo + A < M then (1 : ℤ) else 0)), Val.int M,
        Val.int (1 - (if lo + A < M then (1 : ℤ) else 0)), Val.int (lo + A)]
      [Val.int ((1 - (if lo + A < M then (1 : ℤ) else 0)) * M),
        Val.int (1 - (if lo + A < M then (1 : ℤ) else 0)), Val.int (lo + A)]
      (clBud Λ ρ) := by
    refine Pipe.le (Pipe.appendTail
      [Val.int (1 - (if lo + A < M then (1 : ℤ) else 0)), Val.int (lo + A)]
      (Pipe.binOp (hmul main) (a := (1 - (if lo + A < M then (1 : ℤ) else 0))) (b := M)
        trivial)) ?_
    exact clBud_mul hρ1 hLmul hq3 hMle
  have s14 : Pipe main (rollP 2)
      [Val.int ((1 - (if lo + A < M then (1 : ℤ) else 0)) * M),
        Val.int (1 - (if lo + A < M then (1 : ℤ) else 0)), Val.int (lo + A)]
      [Val.int (lo + A), Val.int ((1 - (if lo + A < M then (1 : ℤ) else 0)) * M),
        Val.int (1 - (if lo + A < M then (1 : ℤ) else 0))]
      (clBud Λ ρ) := by
    refine Pipe.le (Pipe.rw (Pipe.roll main hroll
      (A := [Val.int ((1 - (if lo + A < M then (1 : ℤ) else 0)) * M),
        Val.int (1 - (if lo + A < M then (1 : ℤ) else 0)), Val.int (lo + A)])
      (k := 2) (by simp)) (by simp)) ?_
    have hszl : szl (([Val.int ((1 - (if lo + A < M then (1 : ℤ) else 0)) * M),
        Val.int (1 - (if lo + A < M then (1 : ℤ) else 0)),
        Val.int (lo + A)] : List Val).take (2 + 1)) ≤ 4 * ρ := by
      simp [szl, vsz_int]
      omega
    exact clBud_roll hρ1 hLroll (by omega) hszl
  have s15 : Pipe main subP
      [Val.int (lo + A), Val.int ((1 - (if lo + A < M then (1 : ℤ) else 0)) * M),
        Val.int (1 - (if lo + A < M then (1 : ℤ) else 0))]
      [Val.int ((lo + A) - (1 - (if lo + A < M then (1 : ℤ) else 0)) * M),
        Val.int (1 - (if lo + A < M then (1 : ℤ) else 0))]
      (clBud Λ ρ) := by
    refine Pipe.le (Pipe.appendTail
      [Val.int (1 - (if lo + A < M then (1 : ℤ) else 0))]
      (Pipe.binOp (hsub main) (a := lo + A)
        (b := (1 - (if lo + A < M then (1 : ℤ) else 0)) * M) trivial)) ?_
    exact clBud_two hρ1 hLsub hsle hqMle
  -- ## assembly
  have c2 : Pipe main (rollP 2 ;;; rollP 2) [Val.int M, Val.int lo, Val.int A]
      [Val.int lo, Val.int A, Val.int M] (2 * clBud Λ ρ) :=
    Pipe.comp_le s1 s2 (by omega)
  have c3 : Pipe main (rollP 2 ;;; rollP 2 ;;; addP) [Val.int M, Val.int lo, Val.int A]
      [Val.int (lo + A), Val.int M] (3 * clBud Λ ρ) :=
    Pipe.comp_le c2 s3 (by omega)
  have c4 : Pipe main (rollP 2 ;;; rollP 2 ;;; addP ;;; dupP) [Val.int M, Val.int lo, Val.int A]
      [Val.int (lo + A), Val.int (lo + A), Val.int M] (4 * clBud Λ ρ) :=
    Pipe.comp_le c3 s4 (by omega)
  have c5 : Pipe main (rollP 2 ;;; rollP 2 ;;; addP ;;; dupP ;;; pickP 2)
      [Val.int M, Val.int lo, Val.int A]
      [Val.int M, Val.int (lo + A), Val.int (lo + A), Val.int M] (5 * clBud Λ ρ) :=
    Pipe.comp_le c4 s5 (by omega)
  have c6 : Pipe main (rollP 2 ;;; rollP 2 ;;; addP ;;; dupP ;;; pickP 2 ;;; swapP)
      [Val.int M, Val.int lo, Val.int A]
      [Val.int (lo + A), Val.int M, Val.int (lo + A), Val.int M] (6 * clBud Λ ρ) :=
    Pipe.comp_le c5 s6 (by omega)
  have c7 : Pipe main (rollP 2 ;;; rollP 2 ;;; addP ;;; dupP ;;; pickP 2 ;;; swapP ;;; ltP)
      [Val.int M, Val.int lo, Val.int A]
      [Val.int (if lo + A < M then (1 : ℤ) else 0), Val.int (lo + A), Val.int M]
      (7 * clBud Λ ρ) :=
    Pipe.comp_le c6 s7 (by omega)
  have c8 : Pipe main (rollP 2 ;;; rollP 2 ;;; addP ;;; dupP ;;; pickP 2 ;;; swapP ;;; ltP ;;;
      pushP (.int 1)) [Val.int M, Val.int lo, Val.int A]
      [Val.int 1, Val.int (if lo + A < M then (1 : ℤ) else 0), Val.int (lo + A), Val.int M]
      (8 * clBud Λ ρ) :=
    Pipe.comp_le c7 s8 (by omega)
  have c9 : Pipe main (rollP 2 ;;; rollP 2 ;;; addP ;;; dupP ;;; pickP 2 ;;; swapP ;;; ltP ;;;
      pushP (.int 1) ;;; subP) [Val.int M, Val.int lo, Val.int A]
      [Val.int (1 - (if lo + A < M then (1 : ℤ) else 0)), Val.int (lo + A), Val.int M]
      (9 * clBud Λ ρ) :=
    Pipe.comp_le c8 s9 (by omega)
  have c10 : Pipe main (rollP 2 ;;; rollP 2 ;;; addP ;;; dupP ;;; pickP 2 ;;; swapP ;;; ltP ;;;
      pushP (.int 1) ;;; subP ;;; dupP) [Val.int M, Val.int lo, Val.int A]
      [Val.int (1 - (if lo + A < M then (1 : ℤ) else 0)),
        Val.int (1 - (if lo + A < M then (1 : ℤ) else 0)), Val.int (lo + A), Val.int M]
      (10 * clBud Λ ρ) :=
    Pipe.comp_le c9 s10 (by omega)
  have c11 : Pipe main (rollP 2 ;;; rollP 2 ;;; addP ;;; dupP ;;; pickP 2 ;;; swapP ;;; ltP ;;;
      pushP (.int 1) ;;; subP ;;; dupP ;;; rollP 3) [Val.int M, Val.int lo, Val.int A]
      [Val.int M, Val.int (1 - (if lo + A < M then (1 : ℤ) else 0)),
        Val.int (1 - (if lo + A < M then (1 : ℤ) else 0)), Val.int (lo + A)]
      (11 * clBud Λ ρ) :=
    Pipe.comp_le c10 s11 (by omega)
  have c12 : Pipe main (rollP 2 ;;; rollP 2 ;;; addP ;;; dupP ;;; pickP 2 ;;; swapP ;;; ltP ;;;
      pushP (.int 1) ;;; subP ;;; dupP ;;; rollP 3 ;;; swapP) [Val.int M, Val.int lo, Val.int A]
      [Val.int (1 - (if lo + A < M then (1 : ℤ) else 0)), Val.int M,
        Val.int (1 - (if lo + A < M then (1 : ℤ) else 0)), Val.int (lo + A)]
      (12 * clBud Λ ρ) :=
    Pipe.comp_le c11 s12 (by omega)
  have c13 : Pipe main (rollP 2 ;;; rollP 2 ;;; addP ;;; dupP ;;; pickP 2 ;;; swapP ;;; ltP ;;;
      pushP (.int 1) ;;; subP ;;; dupP ;;; rollP 3 ;;; swapP ;;; mulP)
      [Val.int M, Val.int lo, Val.int A]
      [Val.int ((1 - (if lo + A < M then (1 : ℤ) else 0)) * M),
        Val.int (1 - (if lo + A < M then (1 : ℤ) else 0)), Val.int (lo + A)]
      (13 * clBud Λ ρ) :=
    Pipe.comp_le c12 s13 (by omega)
  have c14 : Pipe main (rollP 2 ;;; rollP 2 ;;; addP ;;; dupP ;;; pickP 2 ;;; swapP ;;; ltP ;;;
      pushP (.int 1) ;;; subP ;;; dupP ;;; rollP 3 ;;; swapP ;;; mulP ;;; rollP 2)
      [Val.int M, Val.int lo, Val.int A]
      [Val.int (lo + A), Val.int ((1 - (if lo + A < M then (1 : ℤ) else 0)) * M),
        Val.int (1 - (if lo + A < M then (1 : ℤ) else 0))]
      (14 * clBud Λ ρ) :=
    Pipe.comp_le c13 s14 (by omega)
  have c15 : Pipe main (rollP 2 ;;; rollP 2 ;;; addP ;;; dupP ;;; pickP 2 ;;; swapP ;;; ltP ;;;
      pushP (.int 1) ;;; subP ;;; dupP ;;; rollP 3 ;;; swapP ;;; mulP ;;; rollP 2 ;;; subP)
      [Val.int M, Val.int lo, Val.int A]
      [Val.int ((lo + A) - (1 - (if lo + A < M then (1 : ℤ) else 0)) * M),
        Val.int (1 - (if lo + A < M then (1 : ℤ) else 0))]
      (15 * clBud Λ ρ) :=
    Pipe.comp_le c14 s15 (by omega)
  -- ## cost and output
  have hcost : 15 * clBud Λ ρ = 600 * Λ * (isz M + isz lo + isz A + 1) := by
    rw [clBud, hρdef]; ring
  have hfin := Pipe.le c15 (le_of_eq hcost)
  refine Pipe.rw hfin ?_
  rw [hqeq]

end Work.Resample
