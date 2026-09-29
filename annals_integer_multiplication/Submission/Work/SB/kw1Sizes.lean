import Mathlib
import Submission.Work.Layout.SB.Specs
import Submission.Work.IntLib.encodeNatBridge

/-!
# Size bookkeeping for the first labelling word of the sort-based `applyAlong`

`Work.SB.kw1Sizes` collects the *arithmetic* content of `Work.Layout.Kw1Spec`: given that the flat
index `i` and its slice-major label `keyIdx1 m B i` both stay below `N`, every intermediate value
produced by the labelling word (`i / B`, `i % B`, `(i / B) / m`, `(i / B) % m`, `B * ((i / B) / m)`,
`s + B * p`, `m * (s + B * p)` and finally the label itself) has size at most `N.size + 2`.

The mathematical heart is the mixed-radix identity

`keyIdx1 m B i = (i / B) % m + m * (i % B + B * ((i / B) / m))`

which is why the label fits in the size bound: the label is built from the *digits* of `i` in the
mixed base `(m, B)`, and each of those digits is bounded by the size of `i`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.SB

open HvdH

/-- `vsz` of a `cons` value: the size is the size of the head, plus the size of the tail, plus 1. -/
private lemma vsz_cons (a b : Val) : vsz (Val.cons a b) = vsz a + vsz b + 1 := by
  simp [HvdH.vsz, HvdH.Val.enc, List.length_append]

/-- An integer of absolute value `≤ N` has value-size at most `N.size + 2`. -/
private lemma isz_natCast_le {a N : ℕ} (h : a ≤ N) : isz (a : ℤ) ≤ N.size + 2 := by
  have h1 : isz (a : ℤ) = a.size + 2 := by simp [HvdH.isz]
  have h2 := Nat.size_le_size h
  omega

/-- `Int.fdiv` of two natural numbers is natural division. -/
private lemma fdiv_natCast (a b : ℕ) : Int.fdiv (a : ℤ) (b : ℤ) = ((a / b : ℕ) : ℤ) := by
  simp [Int.fdiv_eq_ediv, Int.natCast_ediv]

/-- `Int.fmod` of two natural numbers is natural remainder. -/
private lemma fmod_natCast (a b : ℕ) : Int.fmod (a : ℤ) (b : ℤ) = ((a % b : ℕ) : ℤ) := by
  simp [Int.fmod_eq_emod, Int.natCast_emod]

/-- `vsz` of an integer value is `isz`. -/
private lemma vsz_int (z : ℤ) : vsz (Val.int z) = isz z := by
  simpa [HvdH.vsz] using Work.IntLib.vsz_int z

/-- `Int.fdiv` of a nonnegative integer by a natural number is natural division of `toNat`. -/
private lemma fdiv_toNat {a : ℤ} (ha : 0 ≤ a) (b : ℕ) :
    Int.fdiv a (b : ℤ) = ((a.toNat / b : ℕ) : ℤ) := by
  rw [← Int.toNat_of_nonneg ha]
  exact fdiv_natCast a.toNat b

/-- `Int.fmod` of a nonnegative integer by a natural number is the natural remainder of `toNat`. -/
private lemma fmod_toNat {a : ℤ} (ha : 0 ≤ a) (b : ℕ) :
    Int.fmod a (b : ℤ) = ((a.toNat % b : ℕ) : ℤ) := by
  rw [← Int.toNat_of_nonneg ha]
  exact fmod_natCast a.toNat b

/-- The mixed-radix identity: `keyIdx1` is the mixed-base `(m, B)` digit recombination of `i`. -/
private lemma keyIdx1_eq (m B i : ℕ) :
    Work.Layout.keyIdx1 m B i = i / B % m + m * (i % B + B * (i / B / m)) := by
  have h1 : i / (m * B) = i / B / m := by rw [mul_comm m B, ← Nat.div_div_eq_div_mul]
  rw [Work.Layout.keyIdx1, h1]
  ring

/-- All the `ℕ`-level bounds behind `kw1Sizes`. -/
private lemma keyDecomp (m B I N : ℕ) (hm : 0 < m) (hI : I < N)
    (hk : Work.Layout.keyIdx1 m B I < N) :
    I / B ≤ N ∧ I % B ≤ N ∧ I / B / m ≤ N ∧ I / B % m ≤ N ∧
    B * (I / B / m) ≤ N ∧ I % B + B * (I / B / m) ≤ N ∧
    m * (I % B + B * (I / B / m)) ≤ N ∧
    I / B % m + m * (I % B + B * (I / B / m)) = Work.Layout.keyIdx1 m B I := by
  have hkey := keyIdx1_eq m B I
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc I / B ≤ I := Nat.div_le_self _ _
      _ ≤ N := le_of_lt hI
  · calc I % B ≤ I := Nat.mod_le _ _
      _ ≤ N := le_of_lt hI
  · calc I / B / m ≤ I / B := Nat.div_le_self _ _
      _ ≤ N := le_of_lt (lt_of_le_of_lt (Nat.div_le_self I B) hI)
  · calc I / B % m ≤ I / B := Nat.mod_le _ _
      _ ≤ N := le_of_lt (lt_of_le_of_lt (Nat.div_le_self I B) hI)
  · calc B * (I / B / m) ≤ B * (I / B) := Nat.mul_le_mul_left B (Nat.div_le_self _ _)
      _ ≤ I := by have h := Nat.div_add_mod I B; omega
      _ ≤ N := le_of_lt hI
  · calc I % B + B * (I / B / m) ≤ I % B + B * (I / B) :=
        Nat.add_le_add_left (Nat.mul_le_mul_left B (Nat.div_le_self _ _)) _
      _ = I := Nat.mod_add_div I B
      _ ≤ N := le_of_lt hI
  · calc m * (I % B + B * (I / B / m))
        ≤ I / B % m + m * (I % B + B * (I / B / m)) := Nat.le_add_left _ _
      _ = Work.Layout.keyIdx1 m B I := hkey.symm
      _ ≤ N := le_of_lt hk
  · exact hkey.symm

theorem kw1Sizes (m B N Lin : ℕ) (i : ℤ) (v : HvdH.Val)
    (hm : 0 < m) (hB : 0 < B) (hi : 0 ≤ i) (hiN : i.toNat < N)
    (hk : Work.Layout.keyIdx1 m B i.toNat < N)
    (hLm : HvdH.isz (m:ℤ) ≤ Lin) (hLB : HvdH.isz (B:ℤ) ≤ Lin)
    (hLv : HvdH.vsz (HvdH.Val.cons (HvdH.Val.int i) v) ≤ Lin) :
    HvdH.vsz v + 1 ≤ Lin ∧
    HvdH.isz i ≤ N.size + 2 ∧
    HvdH.isz (Int.fdiv i (B:ℤ)) ≤ N.size + 2 ∧
    HvdH.isz (Int.fmod i (B:ℤ)) ≤ N.size + 2 ∧
    HvdH.isz (Int.fdiv (Int.fdiv i (B:ℤ)) (m:ℤ)) ≤ N.size + 2 ∧
    HvdH.isz (Int.fmod (Int.fdiv i (B:ℤ)) (m:ℤ)) ≤ N.size + 2 ∧
    HvdH.isz ((B:ℤ) * Int.fdiv (Int.fdiv i (B:ℤ)) (m:ℤ)) ≤ N.size + 2 ∧
    HvdH.isz (Int.fmod i (B:ℤ) + (B:ℤ) * Int.fdiv (Int.fdiv i (B:ℤ)) (m:ℤ)) ≤ N.size + 2 ∧
    HvdH.isz ((m:ℤ) * (Int.fmod i (B:ℤ) + (B:ℤ) * Int.fdiv (Int.fdiv i (B:ℤ)) (m:ℤ))) ≤ N.size + 2 ∧
    HvdH.isz (Int.fmod (Int.fdiv i (B:ℤ)) (m:ℤ) +
       (m:ℤ) * (Int.fmod i (B:ℤ) + (B:ℤ) * Int.fdiv (Int.fdiv i (B:ℤ)) (m:ℤ))) ≤ N.size + 2 ∧
    (Int.fmod (Int.fdiv i (B:ℤ)) (m:ℤ) +
       (m:ℤ) * (Int.fmod i (B:ℤ) + (B:ℤ) * Int.fdiv (Int.fdiv i (B:ℤ)) (m:ℤ))
       = ((Work.Layout.keyIdx1 m B i.toNat : ℕ) : ℤ)) ∧
    HvdH.vsz (HvdH.Val.cons (HvdH.Val.int ((Work.Layout.keyIdx1 m B i.toNat : ℕ) : ℤ)) v)
      ≤ Lin + N.size + 2 := by
  obtain ⟨hQle, hSle, hTle, hUle, hBTle, hSBle, hmSle, hkey⟩ :=
    keyDecomp m B i.toNat N hm hiN hk
  have hI : ((i.toNat : ℕ) : ℤ) = i := Int.toNat_of_nonneg hi
  have hq : Int.fdiv i (B:ℤ) = ((i.toNat / B : ℕ) : ℤ) := fdiv_toNat hi B
  have hs : Int.fmod i (B:ℤ) = ((i.toNat % B : ℕ) : ℤ) := fmod_toNat hi B
  have hp : Int.fdiv (Int.fdiv i (B:ℤ)) (m:ℤ) = ((i.toNat / B / m : ℕ) : ℤ) := by
    rw [hq]; exact fdiv_natCast _ _
  have hu : Int.fmod (Int.fdiv i (B:ℤ)) (m:ℤ) = ((i.toNat / B % m : ℕ) : ℤ) := by
    rw [hq]; exact fmod_natCast _ _
  have hklt : i.toNat / B % m + m * (i.toNat % B + B * (i.toNat / B / m)) < N := by
    have h := hk; rwa [hkey.symm] at h
  have hv : vsz v + 1 ≤ Lin := by
    have hc : vsz (Val.cons (Val.int i) v) = isz i + vsz v + 1 := by
      rw [vsz_cons, vsz_int]
    omega
  have hkz : isz ((Work.Layout.keyIdx1 m B i.toNat : ℕ) : ℤ) ≤ N.size + 2 := by
    have h := isz_natCast_le (le_of_lt hklt)
    rwa [hkey] at h
  refine ⟨hv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hI]; exact isz_natCast_le (le_of_lt hiN)
  · rw [hq]; exact isz_natCast_le hQle
  · rw [hs]; exact isz_natCast_le hSle
  · rw [hp]; exact isz_natCast_le hTle
  · rw [hu]; exact isz_natCast_le hUle
  · rw [hp]; push_cast; exact isz_natCast_le hBTle
  · rw [hs, hp]; push_cast; exact isz_natCast_le hSBle
  · rw [hs, hp]; push_cast; exact isz_natCast_le hmSle
  · rw [hu, hs, hp]; push_cast; exact isz_natCast_le (le_of_lt hklt)
  · rw [hu, hs, hp, ← hkey]; push_cast; ring
  · rw [vsz_cons, vsz_int]
    omega

end Work.SB
