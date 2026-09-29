import Mathlib
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.mrgBlkDefs

/-!
# `WordR` step lemmas for the slice-word (`HasFFT1`) construction

The `WordR` plumbing lives in `Submission/Work/SynFFT/mrgBlkDefs.lean` (namespace
`Work.SynFFT.MrgKit`): `WordR_weaken`, `WordR_conseqC`, `WordR_seqC` and the `*Step` lemmas for
`pick`, `roll`, `swap`, `drop`, `dup`, `neg`, `add`, `max`, `mul`, `fmod`, `cons`, `uncons`,
`pushVal`, `flatten`-style list words and `mapList`.  Missing from that file are the step lemmas
for the remaining `IntLib`/`LayoutLib` words used by the `Submission/Work/SynFFT/fft1/*`
construction, so they are collected here (all with the same proof pattern: unfold the
`BinOp`/`UnOp` field, apply `WordR_conseqC`, `simp`).
-/

set_option autoImplicit false

namespace Work.SynFFT.Fft1Kit

open HvdH
open Work.SynFFT.MrgKit

local infixr:68 " ;;; " => HvdH.Cmd.seq

theorem subStep {main : Cmd} {subP : Cmd} {Ks : ℕ}
    (h : BinOp main subP (fun _ _ => True) (· - ·) (fun a b => Ks * (isz a + isz b)))
    (a b : ℤ) (t : List Val) (D : ℕ) (hD : Ks * (isz a + isz b) ≤ D) :
    WordR main subP (fun vs => vs = .int a :: .int b :: t) (fun _ out => out = .int (a - b) :: t)
      (fun _ => D) := by
  unfold BinOp at h
  refine WordR_conseqC h ⟨a, b, t, rfl, trivial⟩ ?_ hD
  intro out hout
  obtain ⟨a', b', t', h1, hout'⟩ := hout
  simp only [List.cons.injEq, Val.int.injEq] at h1
  obtain ⟨rfl, rfl, rfl⟩ := h1
  exact hout'

theorem shrTStep {main : Cmd} {shrP : Cmd} {Ks : ℕ}
    (h : BinOp main shrP (fun _ k => 0 ≤ k) (fun a k => Int.tdiv a (2 ^ k.toNat))
      (fun a k => Ks * (isz a + isz k)))
    (a k : ℤ) (t : List Val) (hk : 0 ≤ k) (D : ℕ) (hD : Ks * (isz a + isz k) ≤ D) :
    WordR main shrP (fun vs => vs = .int a :: .int k :: t)
      (fun _ out => out = .int (Int.tdiv a (2 ^ k.toNat)) :: t) (fun _ => D) := by
  unfold BinOp at h
  refine WordR_conseqC h ⟨a, k, t, rfl, hk⟩ ?_ hD
  intro out hout
  obtain ⟨a', k', t', h1, hout'⟩ := hout
  simp only [List.cons.injEq, Val.int.injEq] at h1
  obtain ⟨rfl, rfl, rfl⟩ := h1
  exact hout'

theorem pow2Step {main : Cmd} {powP : Cmd} {Kp : ℕ}
    (h : UnOp main powP (fun k => 0 ≤ k) (fun k => 2 ^ k.toNat) (fun k => Kp * (k.toNat + isz k)))
    (k : ℤ) (t : List Val) (hk : 0 ≤ k) (D : ℕ) (hD : Kp * (k.toNat + isz k) ≤ D) :
    WordR main powP (fun vs => vs = .int k :: t) (fun _ out => out = .int (2 ^ k.toNat) :: t)
      (fun _ => D) := by
  unfold UnOp at h
  refine WordR_conseqC h ⟨k, t, rfl, hk⟩ ?_ hD
  intro out hout
  obtain ⟨k', t', h1, hout'⟩ := hout
  simp only [List.cons.injEq, Val.int.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  exact hout'

theorem clog2Step {main : Cmd} {clP : Cmd} {Kc : ℕ}
    (h : UnOp main clP (fun a => 0 ≤ a) (fun a => (Nat.clog 2 a.toNat : ℤ)) (fun a => Kc * isz a))
    (a : ℤ) (t : List Val) (ha : 0 ≤ a) (D : ℕ) (hD : Kc * isz a ≤ D) :
    WordR main clP (fun vs => vs = .int a :: t)
      (fun _ out => out = .int (Nat.clog 2 a.toNat : ℤ) :: t) (fun _ => D) := by
  unfold UnOp at h
  refine WordR_conseqC h ⟨a, t, rfl, ha⟩ ?_ hD
  intro out hout
  obtain ⟨a', t', h1, hout'⟩ := hout
  simp only [List.cons.injEq, Val.int.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  exact hout'

theorem sizeStep {main : Cmd} {szP : Cmd} {Kz : ℕ}
    (h : UnOp main szP (fun _ => True) (fun a => (a.natAbs.size : ℤ)) (fun a => Kz * isz a))
    (a : ℤ) (t : List Val) (D : ℕ) (hD : Kz * isz a ≤ D) :
    WordR main szP (fun vs => vs = .int a :: t) (fun _ out => out = .int (a.natAbs.size : ℤ) :: t)
      (fun _ => D) := by
  unfold UnOp at h
  refine WordR_conseqC h ⟨a, t, rfl, trivial⟩ ?_ hD
  intro out hout
  obtain ⟨a', t', h1, hout'⟩ := hout
  simp only [List.cons.injEq, Val.int.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  exact hout'

theorem shlStep {main : Cmd} {shlP : Cmd} {Ks : ℕ}
    (h : BinOp main shlP (fun _ k => 0 ≤ k) (fun a k => a * 2 ^ k.toNat)
      (fun a k => Ks * (isz a + k.toNat + isz k)))
    (a k : ℤ) (t : List Val) (hk : 0 ≤ k) (D : ℕ) (hD : Ks * (isz a + k.toNat + isz k) ≤ D) :
    WordR main shlP (fun vs => vs = .int a :: .int k :: t)
      (fun _ out => out = .int (a * 2 ^ k.toNat) :: t) (fun _ => D) := by
  unfold BinOp at h
  refine WordR_conseqC h ⟨a, k, t, rfl, hk⟩ ?_ hD
  intro out hout
  obtain ⟨a', k', t', h1, hout'⟩ := hout
  simp only [List.cons.injEq, Val.int.injEq] at h1
  obtain ⟨rfl, rfl, rfl⟩ := h1
  exact hout'

theorem replicateStep {main : Cmd} {repP : Cmd} {Kr : ℕ}
    (h : ∀ (k : ℕ) (v : Val), WordR main repP
      (fun vs => ∃ rest, vs = .int (k : ℤ) :: v :: rest)
      (fun vs out => ∃ rest, vs = .int (k : ℤ) :: v :: rest ∧
        out = ofList (List.replicate k v) :: rest)
      (fun _ => Kr * ((k + 1) * (vsz v + 1) + isz (k : ℤ) + 1)))
    (k : ℕ) (v : Val) (t : List Val) (D : ℕ)
    (hD : Kr * ((k + 1) * (vsz v + 1) + isz (k : ℤ) + 1) ≤ D) :
    WordR main repP (fun vs => vs = .int (k : ℤ) :: v :: t)
      (fun _ out => out = ofList (List.replicate k v) :: t) (fun _ => D) := by
  refine WordR_conseqC (h k v) ⟨t, rfl⟩ ?_ hD
  intro out hout
  obtain ⟨r, hr1, hr2⟩ := hout
  simp only [List.cons.injEq] at hr1
  obtain ⟨-, -, rfl⟩ := hr1
  exact hr2

/-- The `seq` law of `KLib` for constant costs and singleton pre/post conditions. -/
theorem seqC {main : Cmd} {p q : Cmd} {A B Cc : List Val} {c1 c2 : ℕ}
    (hseq : ∀ (main : Cmd) (p q : Cmd) (P : List Val → Prop) (Q : List Val → List Val → Prop)
      (C : List Val → ℕ) (P' : List Val → Prop) (Q' : List Val → List Val → Prop)
      (C' Bd : List Val → ℕ),
      WordR main p P Q C → WordR main q P' Q' C' →
      (∀ vs mid, P vs → Q vs mid → P' mid ∧ C' mid ≤ Bd vs) →
      WordR main (p ;;; q) P (fun vs out => ∃ mid, Q vs mid ∧ Q' mid out)
        (fun vs => C vs + Bd vs))
    (h1 : WordR main p (fun vs => vs = A) (fun _ out => out = B) (fun _ => c1))
    (h2 : WordR main q (fun vs => vs = B) (fun _ out => out = Cc) (fun _ => c2)) :
    WordR main (p ;;; q) (fun vs => vs = A) (fun _ out => out = Cc) (fun _ => c1 + c2) := by
  have h := hseq main p q (fun vs => vs = A) (fun _ out => out = B) (fun _ => c1)
    (fun vs => vs = B) (fun _ out => out = Cc) (fun _ => c2) (fun _ => c2) h1 h2
    (fun vs mid hvs hmid => ⟨hmid, le_rfl⟩)
  refine WordR_weaken h (fun vs hvs => hvs) ?_ (fun vs _ => le_rfl)
  intro vs out hvs hQ
  obtain ⟨mid, h1', h2'⟩ := hQ
  rw [h2']

/-- `(2 n).size ≤ n.size + 1` (multiplying by two adds at most one bit). -/
theorem size_two_mul (n : ℕ) : (2 * n).size ≤ n.size + 1 := by
  rw [Nat.size_le]
  calc 2 * n < 2 * 2 ^ n.size := by
        have := Nat.lt_size_self n
        omega
    _ = 2 ^ (n.size + 1) := by rw [pow_succ']

/-- `isz (2 s) ≤ isz s + 1`. -/
theorem isz_two_mul_le (s : ℤ) : isz (2 * s) ≤ isz s + 1 := by
  have h : (2 * s).natAbs = 2 * s.natAbs := by
    rw [show (2 : ℤ) * s = 2 * s from rfl, Int.natAbs_mul]
    norm_num
  simp only [isz, h]
  have := size_two_mul s.natAbs
  omega

/-- `isz (n : ℤ) ≤ n + 2`. -/
theorem isz_natCast_le (n : ℕ) : isz (n : ℤ) ≤ n + 2 := by
  have h : ((n : ℤ)).natAbs = n := Int.natAbs_natCast n
  simp only [isz, h]
  have := Nat.size_le.mpr (Nat.lt_two_pow_self (n := n))
  omega

/-- `isz (n + 1) ≤ isz n + 1`. -/
theorem isz_succ_le (n : ℕ) : isz ((n + 1 : ℕ) : ℤ) ≤ isz (n : ℤ) + 1 := by
  have ha : (((n + 1 : ℕ) : ℤ)).natAbs = n + 1 := Int.natAbs_natCast (n + 1)
  have hb : ((n : ℤ)).natAbs = n := Int.natAbs_natCast n
  simp only [isz, ha, hb]
  have h : (n + 1).size ≤ n.size + 1 := by
    rw [Nat.size_le]
    have := Nat.lt_size_self n
    rw [pow_succ']
    omega
  omega

/-- `isz` is monotone on natural numbers. -/
theorem isz_natCast_mono {a b : ℕ} (h : a ≤ b) : isz (a : ℤ) ≤ isz (b : ℤ) := by
  have ha : ((a : ℤ)).natAbs = a := Int.natAbs_natCast a
  have hb : ((b : ℤ)).natAbs = b := Int.natAbs_natCast b
  simp only [isz, ha, hb]
  have h1 : a < 2 ^ b.size := lt_of_le_of_lt h (Nat.lt_size_self b)
  have h2 : a.size ≤ b.size := Nat.size_le.mpr h1
  omega

/-- `vsz (.int 1) = 3`. -/
theorem vsz_int_one : vsz (.int (1 : ℤ)) = 3 := by
  rw [Work.SynFFT.MrgKit.vsz_int']
  decide

/-- `isz (2^k) = k + 3`. -/
theorem isz_two_pow (k : ℕ) : isz (((2 ^ k : ℕ)) : ℤ) = k + 3 := by
  have h : (((2 ^ k : ℕ)) : ℤ).natAbs = 2 ^ k := Int.natAbs_natCast (2 ^ k)
  simp only [isz, h, Nat.size_pow]

/-- `vsz .nil = 1`. -/
theorem vsz_nil : vsz (.nil : Val) = 1 := rfl

/-- `vsz (ofList (replicate k .nil)) = 2k + 1`. -/
theorem vsz_ofList_replicate_nil (k : ℕ) :
    vsz (ofList (List.replicate k (Val.nil))) = 2 * k + 1 := by
  rw [Work.SynFFT.MrgKit.vsz_ofList]
  simp [vsz_nil]
  ring

/-- `isz (1 : ℤ) = 3`. -/
theorem isz_one : isz (1 : ℤ) = 3 := by decide

/-- `2 ≤ isz z`. -/
theorem two_le_isz (z : ℤ) : 2 ≤ isz z := by
  simp only [isz]
  omega

/-- `1 ≤ vsz v`. -/
theorem one_le_vsz (v : Val) : 1 ≤ vsz v := by
  cases v with
  | int z => simp [vsz, Val.enc]
  | nil => simp [vsz, Val.enc]
  | cons a b => simp [vsz, Val.enc]

/-- `isz sgn = 3` for a sign. -/
theorem isz_of_sign {sgn : ℤ} (h : sgn = 1 ∨ sgn = -1) : isz sgn = 3 := by
  rcases h with h | h <;> subst h
  · exact isz_one
  · rw [show isz (-1 : ℤ) = isz (1 : ℤ) from Work.SynFFT.MrgKit.isz_neg' 1, isz_one]

end Work.SynFFT.Fft1Kit
