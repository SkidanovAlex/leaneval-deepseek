import Mathlib
import Submission.Work.PTCert.GlueDefs
import Submission.Work.PTCert.digitArith
import Submission.Work.PTCert.chiSFive
import Submission.Work.PTCert.chiSTwo
import Submission.Work.PTCert.scOf_zBool_add

/-!
# GL12: the bit/code bridge

This file proves `BitsBridge` (`Submission/Work/PTCert/GlueDefs.lean`), the bridge between the
`(ℤ/2)^m`-vector / `chiS` world and the binary-code / `chiS5` world used by the kernel checker.

The pieces:

* `zOfSc` is a bijection from `Finset.range (2^m)` onto `Fin m → ZMod 2` (binary digits), so sums
  over the vector space can be computed as sums over the codes `sc < 2^m`;
* `chiS (maskSet S)` agrees with the kernel's `chiS5 S` on codes (`m = 5`, and `m = 2` for the
  Klein-level character);
* `zBool ∘ zOfSc = scBits` and `scOf` turns addition in `(ℤ/2)^5` into `Nat.xor` of the codes.

-/

namespace Work.PTCert

open Submission.PTCert

/-! ## Binary codes of `ZMod 2`-vectors -/

/-- The `j`-th bit of a `ZMod 2`-vector as `0`/`1` (bits outside `Fin m` vanish). -/
private def bitsBitOf {m : ℕ} (a : Fin m → ZMod 2) (j : ℕ) : ℕ :=
  if h : j < m then (if a ⟨j, h⟩ = 1 then 1 else 0) else 0

/-- The binary code `∑ i, bit i · 2^i` of a `ZMod 2`-vector. -/
private def bitsEnc {m : ℕ} (a : Fin m → ZMod 2) : ℕ :=
  ∑ i : Fin m, (if a i = 1 then 1 else 0) * 2 ^ i.val

private lemma bitsBitOf_lt_two {m : ℕ} (a : Fin m → ZMod 2) (j : ℕ) : bitsBitOf a j < 2 := by
  unfold bitsBitOf
  split_ifs <;> omega

private lemma bitsEnc_eq_range {m : ℕ} (a : Fin m → ZMod 2) :
    bitsEnc a = ∑ j ∈ Finset.range m, bitsBitOf a j * 2 ^ j := by
  have h1 : bitsEnc a = ∑ i : Fin m, bitsBitOf a i.val * 2 ^ i.val := by
    rw [bitsEnc]
    exact Finset.sum_congr rfl (fun i _ => by simp [bitsBitOf])
  rw [h1, Fin.sum_univ_eq_sum_range (fun j => bitsBitOf a j * 2 ^ j) m]

private lemma bitsEnc_lt {m : ℕ} (a : Fin m → ZMod 2) : bitsEnc a < 2 ^ m := by
  rw [bitsEnc_eq_range]
  exact Work.PTCert.digits.sum_mul_pow_lt_pow (by norm_num) (bitsBitOf a) m
    (fun j _ => bitsBitOf_lt_two a j)

private lemma zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have h2 : x.val < 2 := ZMod.val_lt x
  rcases (show x.val = 0 ∨ x.val = 1 by omega) with h | h
  · exact Or.inl (ZMod.val_injective 2 (by rw [h, ZMod.val_zero]))
  · exact Or.inr (ZMod.val_injective 2 (by rw [h, ZMod.val_one 2]))

private lemma natCast_ite_eq_self (x : ZMod 2) :
    (((if x = 1 then 1 else 0 : ℕ)) : ZMod 2) = x := by
  by_cases h : x = 1
  · rw [if_pos h, h]; norm_num
  · rw [if_neg h]
    rcases zmod2_eq_zero_or_one x with h0 | h1
    · rw [h0]; norm_num
    · exact absurd h1 h

/-- The bits of the code `bitsEnc a` are the bits of `a`. -/
private lemma sbit_bitsEnc {m : ℕ} (a : Fin m → ZMod 2) (i : Fin m) :
    sbit (bitsEnc a) i.val = (if a i = 1 then 1 else 0) := by
  have h := Work.PTCert.digits.sum_mul_pow_div_mod (b := 2) (d := bitsBitOf a) (n := m)
    (i := i.val) (by norm_num) (fun j _ => bitsBitOf_lt_two a j) i.isLt
  rw [← bitsEnc_eq_range] at h
  rw [sbit, Nat.shiftRight_eq_div_pow, h]
  simp [bitsBitOf]

/-- `zOfSc` of the binary code of `a` is `a`. -/
private lemma zOfSc_bitsEnc {m : ℕ} (a : Fin m → ZMod 2) :
    zOfSc (m := m) (bitsEnc a) = a := by
  funext i
  show (((sbit (bitsEnc a) i.val : ℕ)) : ZMod 2) = a i
  rw [sbit_bitsEnc a i]
  exact natCast_ite_eq_self (a i)

/-- **(GL12 a)** Every `ZMod 2`-vector is the binary code vector of a unique `sc < 2^m`. -/
theorem zOfSc_surj (m : ℕ) (a : Fin m → ZMod 2) : ∃ sc < 2 ^ m, zOfSc (m := m) sc = a :=
  ⟨bitsEnc a, bitsEnc_lt a, zOfSc_bitsEnc a⟩

/-- **(GL12 b)** Sums over `(ℤ/2)^m` can be computed over the codes `sc < 2^m`. -/
theorem sum_zmod_eq_sum_range (m : ℕ) {M : Type} [AddCommMonoid M]
    (F : (Fin m → ZMod 2) → M) :
    ∑ a, F a = ∑ sc ∈ Finset.range (2 ^ m), F (zOfSc sc) := by
  have hcard : Fintype.card (Fin (2 ^ m)) = Fintype.card (Fin m → ZMod 2) := by
    rw [Fintype.card_fin, Fintype.card_fun, Fintype.card_fin, ZMod.card]
  have hbij : Function.Bijective (fun i : Fin (2 ^ m) => zOfSc (m := m) i.val) :=
    (Fintype.bijective_iff_surjective_and_card _).mpr
      ⟨fun a => by
        obtain ⟨sc, hsc, h⟩ := zOfSc_surj m a
        exact ⟨⟨sc, hsc⟩, h⟩, hcard⟩
  rw [← Equiv.sum_comp (Equiv.ofBijective _ hbij) F]
  simp only [Equiv.ofBijective_apply]
  exact Fin.sum_univ_eq_sum_range (fun sc => F (zOfSc sc)) (2 ^ m)

/-! ## `zBool`, `scBits` and `scOf` -/

private lemma sbit_lt_two (sc i : ℕ) : sbit sc i < 2 := by
  rw [sbit]; exact Nat.mod_lt _ (by norm_num)

private lemma natCast_two_eq_one_iff {n : ℕ} (hn : n < 2) : ((n : ℕ) : ZMod 2) = 1 ↔ n = 1 := by
  constructor
  · intro h
    have h1 : ((n : ℕ) : ZMod 2).val = 1 := by rw [h, ZMod.val_one 2]
    rw [ZMod.val_natCast] at h1
    omega
  · intro h; rw [h]; norm_num

private lemma zBool_zOfSc (sc : ℕ) : zBool (zOfSc (m := 5) sc) = scBits sc := by
  funext i
  simp only [zBool, zOfSc, scBits]
  have h := natCast_two_eq_one_iff (n := sbit sc i.val) (sbit_lt_two sc i.val)
  by_cases hb : sbit sc i.val = 1
  · simp [hb]
  · have h1 : ¬ (((sbit sc i.val : ℕ)) : ZMod 2) = 1 := fun hh => hb (h.mp hh)
    simp [hb, h1]

theorem bitsBridge : BitsBridge := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m F; exact sum_zmod_eq_sum_range m F
  · intro m a; exact zOfSc_surj m a
  · intro S sc hS hsc; exact Work.PTCert.chiSFive S sc hS hsc
  · intro psi b hp hb; exact Work.PTCert.chiSTwo psi b hp hb
  · intro sc _; exact zBool_zOfSc sc
  · intro a b; exact Work.PTCert.scOf_zBool_add a b

end Work.PTCert
