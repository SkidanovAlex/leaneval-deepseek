import Mathlib
import Submission.Work.Resample.buKit
import Submission.Work.Resample.buHornerKit
import Submission.Work.Resample.buZDefs
import Submission.Work.Resample.auMapListTail
import Submission.Work.Resample.auPreKit
import Submission.Work.Resample.buSignsDefs

/-!
# `Work.Resample.buSignsWord`

From a word `signProg` computing the sign `(-1)^{i+1}` of one label `cons (int i) nil`, this file
builds a word computing the whole alternating-sign list `buL11 p α s t` (entry 10 of the table
`buTabList`) out of the canonical block `buCB p α s t`.

The pipeline reads `n = egN p α s t` out of the block, forms `n-1`, replicates `nil` that many
times, labels the copies with `enumerate`, and maps the element word `signProg; neg` over the
labels.
-/

set_option autoImplicit true
set_option maxHeartbeats 4000000

namespace Work.Resample

open HvdH
open Work.Fx

/-! ## Elementary facts about the signs -/

/-- The sign attached to the label `cons (int i) nil` of the sign list. -/
def buSignOf : Val → Val
  | .cons (.int i) .nil => .int ((-1 : ℤ) ^ (i.toNat + 1))
  | _ => .nil

theorem buSignOf_cons (i : ℕ) :
    buSignOf (Val.cons (Val.int (i : ℤ)) Val.nil) = Val.int ((-1 : ℤ) ^ (i + 1)) := by
  simp only [buSignOf, Int.toNat_natCast]

theorem buSignIdx (i : ℕ) :
    (-1 : ℤ) ^ (i + 1) = -(1 - 2 * ((i % 2 : ℕ) : ℤ)) ∧
    isz (1 - 2 * ((i % 2 : ℕ) : ℤ)) ≤ 3 := by
  have h2 : i % 2 = 0 ∨ i % 2 = 1 := by
    have h := Nat.mod_lt i (show 0 < 2 by norm_num)
    omega
  constructor
  · rcases h2 with h | h
    · have ho : Odd (i + 1) := (Nat.even_iff.mpr h).add_one
      rw [ho.neg_one_pow, h]
      norm_num
    · have he : Even (i + 1) := (Nat.odd_iff.mpr h).add_one
      rw [he.neg_one_pow, h]
      norm_num
  · rcases h2 with h | h
    · rw [h]
      decide
    · rw [h]
      decide

theorem buVszNil : vsz (Val.nil : Val) = 1 := rfl

theorem buIszOne : isz (1 : ℤ) = 3 := by decide

theorem buSignMapEq (p α s t : ℕ) :
    ofList ((List.range (egN p α s t - 1)).map (fun i : ℕ => Val.int ((-1 : ℤ) ^ (i + 1))))
      = buL11 p α s t := by
  unfold buL11 zl
  rw [List.map_map]
  rfl

/-- Numeric facts about `egN p α s t` used by the sign word. -/
theorem buSignEGN (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hp : 100 ≤ p) (htp : t < 2 ^ p) :
    1 ≤ egN p α s t ∧ egN p α s t ≤ 2 ^ (2 * p) ∧
      ((egN p α s t : ℤ) - 1 = (((egN p α s t - 1 : ℕ)) : ℤ)) ∧
      isz ((egN p α s t : ℤ) - 1) ≤ buSZ p := by
  have hsp : s < 2 ^ p := lt_trans hst htp
  have h1 : 1 ≤ egN p α s t := by
    have h0 : (0 : ℕ) ≤ (p * s - 1) / (α ^ 2 * (t - s)) := Nat.zero_le _
    simp only [egN]
    omega
  have h2 : egN p α s t ≤ 2 ^ (2 * p) := by
    have hle : egN p α s t ≤ p * s := by
      have h := Nat.div_le_self (p * s - 1) (α ^ 2 * (t - s))
      have h3 : 1 ≤ p * s := Nat.mul_pos (by omega) (by omega)
      simp only [egN]
      omega
    have h4 : p * s ≤ 2 ^ (2 * p) := by
      have hp1 : p ≤ 2 ^ p := le_of_lt (Nat.lt_two_pow_self (n := p))
      have hs2 : s ≤ 2 ^ p := le_of_lt hsp
      calc p * s ≤ 2 ^ p * 2 ^ p := Nat.mul_le_mul hp1 hs2
        _ = 2 ^ (2 * p) := by rw [← pow_add]; ring_nf
    exact le_trans hle h4
  have h3 : isz ((((egN p α s t - 1 : ℕ)) : ℤ)) ≤ buSZ p :=
    isz_natCast_le_buSZ_of (p := p) (A := 2 * p) (by simp only [buSZ]; omega) (by omega)
  have h4 : (((egN p α s t - 1 : ℕ)) : ℤ) = (egN p α s t : ℤ) - 1 := Nat.cast_sub h1
  refine ⟨h1, h2, h4.symm, ?_⟩
  rw [h4] at h3
  exact h3

/-- The inner cost of the `mapList` step is bounded by the normalised expression. -/
theorem buSignSumLe (Kpick Kpush Kswap Ksub Krep Kenum Kml Ks Kneg p : ℕ) (hp : 100 ≤ p) :
    Ks * (p + 1) ^ Ks + Kneg * 3 + Kml * (2 * p + 4 + 1)
      ≤ (Ks + Kneg + Kml) *
          (p + 1) ^ buSignsKc Kpick Kpush Kswap Ksub Krep Kenum Kml Ks Kneg := by
  set Kc := buSignsKc Kpick Kpush Kswap Ksub Krep Kenum Kml Ks Kneg with hKc
  have hKs : Ks ≤ Kc := by
    rw [hKc, buSignsKc]
    calc Ks ≤ 2 ^ Ks := le_of_lt (Nat.lt_two_pow_self (n := Ks))
      _ ≤ 2 ^ (Kpick + Kpush + Kswap + Ksub + Krep + Kenum + Kml + Ks + Kneg + 40) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
  have hKc2 : 2 ≤ Kc := by
    rw [hKc, buSignsKc]
    calc (2 : ℕ) = 2 ^ 1 := rfl
      _ ≤ 2 ^ (Kpick + Kpush + Kswap + Ksub + Krep + Kenum + Kml + Ks + Kneg + 40) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : (3 : ℕ) ≤ (p + 1) ^ Kc := by
    calc (3 : ℕ) ≤ (p + 1) ^ 2 := by nlinarith
      _ ≤ (p + 1) ^ Kc := Nat.pow_le_pow_right (by omega) hKc2
  have h4 : 2 * p + 4 + 1 ≤ (p + 1) ^ Kc := by
    calc 2 * p + 4 + 1 ≤ (p + 1) ^ 2 := by nlinarith
      _ ≤ (p + 1) ^ Kc := Nat.pow_le_pow_right (by omega) hKc2
  have hA : Ks * (p + 1) ^ Ks ≤ Ks * (p + 1) ^ Kc :=
    Nat.mul_le_mul_left Ks (Nat.pow_le_pow_right (by omega) hKs)
  have hB : Kneg * 3 ≤ Kneg * (p + 1) ^ Kc := Nat.mul_le_mul_left Kneg h3
  have hC : Kml * (2 * p + 4 + 1) ≤ Kml * (p + 1) ^ Kc := Nat.mul_le_mul_left Kml h4
  calc Ks * (p + 1) ^ Ks + Kneg * 3 + Kml * (2 * p + 4 + 1)
      ≤ Ks * (p + 1) ^ Kc + Kneg * (p + 1) ^ Kc + Kml * (p + 1) ^ Kc :=
        add_le_add (add_le_add hA hB) hC
    _ = (Ks + Kneg + Kml) * (p + 1) ^ Kc := by ring

/-- The cost arithmetic of the signs word. -/
theorem buSignsCost {Kpick Kpush Kswap Ksub Krep Kenum Kml Ks Kneg p n : ℕ}
    (hp : 100 ≤ p) (hn : n ≤ 2 ^ (2 * p)) :
    buSignsE Kpick Kpush Kswap Ksub Krep Kenum Kml Ks Kneg p n
      ≤ buSignsKc Kpick Kpush Kswap Ksub Krep Kenum Kml Ks Kneg * (n + 1)
        * (p + 1) ^ buSignsKc Kpick Kpush Kswap Ksub Krep Kenum Kml Ks Kneg := by
  set Kc := buSignsKc Kpick Kpush Kswap Ksub Krep Kenum Kml Ks Kneg with hKc
  set S := Kpick + Kpush + Kswap + Ksub + Krep + Kenum + Kml + Ks + Kneg with hS
  have hKc_eq : Kc = 2 ^ (S + 40) := by rw [hKc, hS, buSignsKc]
  have hKc4 : 4 ≤ Kc := by
    rw [hKc_eq]
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (S + 40) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hKc2 : 2 ≤ Kc := le_trans (by norm_num : (2 : ℕ) ≤ 4) hKc4
  have hKc1 : 1 ≤ Kc := le_trans (by norm_num : (1 : ℕ) ≤ 2) hKc2
  have hSKc : S ≤ Kc := by
    rw [hKc_eq]
    calc S ≤ 2 ^ S := le_of_lt (Nat.lt_two_pow_self (n := S))
      _ ≤ 2 ^ (S + 40) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hSZ : buSZ p ≤ (p + 1) ^ Kc := by
    calc buSZ p ≤ (p + 1) ^ 4 := by simp only [buSZ]; nlinarith
      _ ≤ (p + 1) ^ Kc := Nat.pow_le_pow_right (by omega) hKc4
  have hB1 : 1 ≤ (p + 1) ^ Kc := Nat.one_le_pow' Kc p
  have h2p1 : 2 * p + 1 ≤ (p + 1) ^ Kc := by
    calc 2 * p + 1 ≤ (p + 1) ^ 2 := by nlinarith
      _ ≤ (p + 1) ^ Kc := Nat.pow_le_pow_right (by omega) hKc2
  have hszsub : (n - 1).size ≤ 2 * p := by
    have hpos : 0 < 2 ^ (2 * p) := pow_pos (by norm_num) _
    apply Nat.size_le.mpr
    omega
  have hXn : 1 ≤ (n + 1) * (p + 1) ^ Kc := by
    have h1 : 0 < (p + 1) ^ Kc := pow_pos (by omega) _
    have h : 0 < (n + 1) * (p + 1) ^ Kc := Nat.mul_pos (by omega) h1
    omega
  have hle3 : ∀ a : ℕ, a ≤ (n + 1) * a := fun a => by
    calc a = 1 * a := (one_mul a).symm
      _ ≤ (n + 1) * a := Nat.mul_le_mul_right a (by omega)
  have hKpickS : Kpick ≤ S := by omega
  have hKpushS : Kpush ≤ S := by omega
  have hKswapS : Kswap ≤ S := by omega
  have hKsubS : Ksub ≤ S := by omega
  have hKrepS : Krep ≤ S := by omega
  have hKenumS : Kenum ≤ S := by omega
  have hKmlS : Kml ≤ S := by omega
  have hKsumS : Ks + Kneg + Kml ≤ S := by omega
  have h1 : Kpick * 6 * (6 * buSZ p + 1) ≤ 42 * (S * ((n + 1) * (p + 1) ^ Kc)) := by
    have h6 : 6 * buSZ p + 1 ≤ 7 * (p + 1) ^ Kc := by
      have h := hSZ; have h0 := hB1; omega
    calc Kpick * 6 * (6 * buSZ p + 1)
        ≤ Kpick * 6 * (7 * (p + 1) ^ Kc) := Nat.mul_le_mul_left _ h6
      _ = 42 * (Kpick * (p + 1) ^ Kc) := by ring
      _ ≤ 42 * (S * (p + 1) ^ Kc) := Nat.mul_le_mul_left 42 (Nat.mul_le_mul_right _ hKpickS)
      _ ≤ 42 * (S * ((n + 1) * (p + 1) ^ Kc)) :=
          Nat.mul_le_mul_left 42 (Nat.mul_le_mul_left S (hle3 ((p + 1) ^ Kc)))
  have h2 : Kpush * 4 ≤ 4 * (S * ((n + 1) * (p + 1) ^ Kc)) := by
    calc Kpush * 4 = 4 * Kpush := by ring
      _ ≤ 4 * S := Nat.mul_le_mul_left 4 hKpushS
      _ ≤ 4 * (S * ((n + 1) * (p + 1) ^ Kc)) := Nat.mul_le_mul_left 4 (by
            calc S = S * 1 := (mul_one S).symm
              _ ≤ S * ((n + 1) * (p + 1) ^ Kc) := Nat.mul_le_mul_left S hXn)
  have h3 : Kswap * (buSZ p + 4) ≤ 5 * (S * ((n + 1) * (p + 1) ^ Kc)) := by
    have h5 : buSZ p + 4 ≤ 5 * (p + 1) ^ Kc := by
      have h := hSZ; have h0 := hB1; omega
    calc Kswap * (buSZ p + 4) ≤ Kswap * (5 * (p + 1) ^ Kc) := Nat.mul_le_mul_left _ h5
      _ = 5 * (Kswap * (p + 1) ^ Kc) := by ring
      _ ≤ 5 * (S * (p + 1) ^ Kc) := Nat.mul_le_mul_left 5 (Nat.mul_le_mul_right _ hKswapS)
      _ ≤ 5 * (S * ((n + 1) * (p + 1) ^ Kc)) :=
          Nat.mul_le_mul_left 5 (Nat.mul_le_mul_left S (hle3 ((p + 1) ^ Kc)))
  have h4 : Ksub * (buSZ p + 3) ≤ 4 * (S * ((n + 1) * (p + 1) ^ Kc)) := by
    have h5 : buSZ p + 3 ≤ 4 * (p + 1) ^ Kc := by
      have h := hSZ; have h0 := hB1; omega
    calc Ksub * (buSZ p + 3) ≤ Ksub * (4 * (p + 1) ^ Kc) := Nat.mul_le_mul_left _ h5
      _ = 4 * (Ksub * (p + 1) ^ Kc) := by ring
      _ ≤ 4 * (S * (p + 1) ^ Kc) := Nat.mul_le_mul_left 4 (Nat.mul_le_mul_right _ hKsubS)
      _ ≤ 4 * (S * ((n + 1) * (p + 1) ^ Kc)) :=
          Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left S (hle3 ((p + 1) ^ Kc)))
  have h5 : Kpush * 2 ≤ 2 * (S * ((n + 1) * (p + 1) ^ Kc)) := by
    calc Kpush * 2 = 2 * Kpush := by ring
      _ ≤ 2 * S := Nat.mul_le_mul_left 2 hKpushS
      _ ≤ 2 * (S * ((n + 1) * (p + 1) ^ Kc)) := Nat.mul_le_mul_left 2 (by
            calc S = S * 1 := (mul_one S).symm
              _ ≤ S * ((n + 1) * (p + 1) ^ Kc) := Nat.mul_le_mul_left S hXn)
  have h6 : Kswap * (buSZ p + 4) ≤ 5 * (S * ((n + 1) * (p + 1) ^ Kc)) := h3
  have h7 : Krep * (2 * ((n - 1) + 1) + buSZ p + 1)
      ≤ 4 * (S * ((n + 1) * (p + 1) ^ Kc)) := by
    have hA : (n + 1) ≤ (n + 1) * (p + 1) ^ Kc := by
      calc (n + 1) = (n + 1) * 1 := (mul_one _).symm
        _ ≤ (n + 1) * (p + 1) ^ Kc := Nat.mul_le_mul_left _ hB1
    have hB' : (p + 1) ^ Kc ≤ (n + 1) * (p + 1) ^ Kc := hle3 ((p + 1) ^ Kc)
    have hc : 2 * ((n - 1) + 1) + buSZ p + 1 ≤ 4 * ((n + 1) * (p + 1) ^ Kc) := by
      have h1 : 2 * ((n - 1) + 1) ≤ 2 * ((n + 1) * (p + 1) ^ Kc) :=
        le_trans (Nat.mul_le_mul_left 2 (by omega)) (Nat.mul_le_mul_left 2 hA)
      have h2 : buSZ p + 1 ≤ 2 * ((n + 1) * (p + 1) ^ Kc) := by
        have h2a : buSZ p ≤ (n + 1) * (p + 1) ^ Kc := le_trans hSZ hB'
        have h2b : 1 ≤ (n + 1) * (p + 1) ^ Kc := hXn
        omega
      omega
    calc Krep * (2 * ((n - 1) + 1) + buSZ p + 1)
        ≤ Krep * (4 * ((n + 1) * (p + 1) ^ Kc)) := Nat.mul_le_mul_left _ hc
      _ = 4 * (Krep * ((n + 1) * (p + 1) ^ Kc)) := by ring
      _ ≤ 4 * (S * ((n + 1) * (p + 1) ^ Kc)) :=
          Nat.mul_le_mul_left 4 (Nat.mul_le_mul_right _ hKrepS)
  have h8 : Kenum * (2 * ((n - 1) + 1) + (n - 1) * ((n - 1).size + 1) + 1)
      ≤ 4 * (S * ((n + 1) * (p + 1) ^ Kc)) := by
    have hA : (n + 1) ≤ (n + 1) * (p + 1) ^ Kc := by
      calc (n + 1) = (n + 1) * 1 := (mul_one _).symm
        _ ≤ (n + 1) * (p + 1) ^ Kc := Nat.mul_le_mul_left _ hB1
    have hc : 2 * ((n - 1) + 1) + (n - 1) * ((n - 1).size + 1) + 1
        ≤ 4 * ((n + 1) * (p + 1) ^ Kc) := by
      have h1 : 2 * ((n - 1) + 1) ≤ 2 * ((n + 1) * (p + 1) ^ Kc) :=
        le_trans (Nat.mul_le_mul_left 2 (by omega)) (Nat.mul_le_mul_left 2 hA)
      have h2 : (n - 1) * ((n - 1).size + 1) ≤ (n + 1) * (p + 1) ^ Kc := by
        calc (n - 1) * ((n - 1).size + 1) ≤ (n - 1) * (2 * p + 1) :=
              Nat.mul_le_mul_left _ (by omega)
          _ ≤ (n + 1) * (2 * p + 1) := Nat.mul_le_mul_right _ (by omega)
          _ ≤ (n + 1) * (p + 1) ^ Kc := Nat.mul_le_mul_left _ h2p1
      have h3 : 1 ≤ (n + 1) * (p + 1) ^ Kc := hXn
      omega
    calc Kenum * (2 * ((n - 1) + 1) + (n - 1) * ((n - 1).size + 1) + 1)
        ≤ Kenum * (4 * ((n + 1) * (p + 1) ^ Kc)) := Nat.mul_le_mul_left _ hc
      _ = 4 * (Kenum * ((n + 1) * (p + 1) ^ Kc)) := by ring
      _ ≤ 4 * (S * ((n + 1) * (p + 1) ^ Kc)) :=
          Nat.mul_le_mul_left 4 (Nat.mul_le_mul_right _ hKenumS)
  have h9 : (n - 1) * ((Ks + Kneg + Kml) * (p + 1) ^ Kc) + Kml
      ≤ 2 * (S * ((n + 1) * (p + 1) ^ Kc)) := by
    have hT1 : (n - 1) * ((Ks + Kneg + Kml) * (p + 1) ^ Kc)
        ≤ S * ((n + 1) * (p + 1) ^ Kc) := by
      calc (n - 1) * ((Ks + Kneg + Kml) * (p + 1) ^ Kc)
          ≤ (n + 1) * ((Ks + Kneg + Kml) * (p + 1) ^ Kc) :=
            Nat.mul_le_mul_right _ (by omega)
        _ ≤ (n + 1) * (S * (p + 1) ^ Kc) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hKsumS)
        _ = S * ((n + 1) * (p + 1) ^ Kc) := by ring
    have hT2 : Kml ≤ S * ((n + 1) * (p + 1) ^ Kc) := by
      refine le_trans hKmlS ?_
      calc S = S * 1 := (mul_one S).symm
        _ ≤ S * ((n + 1) * (p + 1) ^ Kc) := Nat.mul_le_mul_left S hXn
    omega
  have hmain : buSignsE Kpick Kpush Kswap Ksub Krep Kenum Kml Ks Kneg p n
      ≤ 72 * (S * ((n + 1) * (p + 1) ^ Kc)) := by
    unfold buSignsE
    rw [← hKc]
    omega
  have h72 : 72 * S ≤ Kc := by
    have h2 : 72 * S ≤ 2 ^ 7 * 2 ^ S :=
      Nat.mul_le_mul (by norm_num) (le_of_lt (Nat.lt_two_pow_self (n := S)))
    refine le_trans h2 ?_
    rw [hKc_eq]
    calc 2 ^ 7 * 2 ^ S = 2 ^ (7 + S) := (pow_add 2 7 S).symm
      _ ≤ 2 ^ (S + 40) := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc buSignsE Kpick Kpush Kswap Ksub Krep Kenum Kml Ks Kneg p n
      ≤ 72 * (S * ((n + 1) * (p + 1) ^ Kc)) := hmain
    _ = 72 * S * ((n + 1) * (p + 1) ^ Kc) := by ring
    _ ≤ Kc * ((n + 1) * (p + 1) ^ Kc) := Nat.mul_le_mul_right _ h72
    _ = Kc * (n + 1) * (p + 1) ^ Kc := by ring

/-! ## The word -/

theorem buSignsWord (KL : HvdH.KernelLib) (IL : HvdH.IntLib) (LL : HvdH.LayoutLib)
    (signProg : HvdH.Cmd) (Ks : ℕ)
    (signSpec : ∀ (main : HvdH.Cmd) (p : ℕ) (hp : 1 ≤ p) (i : ℕ) (hi : i < 2 ^ (2 * p)),
      ∀ rest : List HvdH.Val, HvdH.WordR main signProg
        (fun vs => vs = [HvdH.Val.cons (HvdH.Val.int (i : ℤ)) HvdH.Val.nil] ++ rest)
        (fun vs out => vs = [HvdH.Val.cons (HvdH.Val.int (i : ℤ)) HvdH.Val.nil] ++ rest ∧
          out = [HvdH.Val.int (1 - 2 * ((i % 2 : ℕ) : ℤ))] ++ rest)
        (fun _ => Ks * (p + 1) ^ Ks)) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t)
      (hα : 2 ≤ α) (hp : 100 ≤ p) (htp : t < 2 ^ p) (hαp : α ^ 2 < p),
      Work.Resample.Pipe main prog (Work.Resample.buCB p α s t)
        (Work.Resample.buL11 p α s t :: Work.Resample.buCB p α s t)
        (K * (Work.Resample.egN p α s t + 1) * (p + 1) ^ K) := by
  obtain ⟨pickProg, Kpick, hPick⟩ := KL.pick
  obtain ⟨pushProg, Kpush, hPush⟩ := KL.pushVal
  obtain ⟨swapProg, Kswap, hSwap⟩ := KL.swap
  obtain ⟨mlComb, Kml, hML⟩ := MapListField.of_kernel KL
  obtain ⟨negProg, Kneg, hNeg⟩ := IL.neg
  obtain ⟨subProg, Ksub, hSub⟩ := IL.sub
  obtain ⟨repProg, Krep, hRep⟩ := LL.replicate
  obtain ⟨enumProg, Kenum, hEnum⟩ := LL.enumerate
  refine ⟨Cmd.seq (pickProg 5)
      (Cmd.seq (pushProg (.int 1))
      (Cmd.seq swapProg
      (Cmd.seq subProg
      (Cmd.seq (pushProg .nil)
      (Cmd.seq swapProg
      (Cmd.seq repProg
      (Cmd.seq enumProg
      (mlComb (Cmd.seq signProg negProg))))))))),
    buSignsKc Kpick Kpush Kswap Ksub Krep Kenum Kml Ks Kneg, ?_⟩
  intro main p α s t hs hst hα hp htp hαp
  set A : List Val := buCB p α s t with hA
  set xs : List Val := (List.range (egN p α s t - 1)).map
      (fun i : ℕ => Val.cons (.int (i : ℤ)) Val.nil) with hxs
  obtain ⟨hn1, hn2p, hncast, hnsub⟩ := buSignEGN p α s t hs hst hp htp
  have hsp : s < 2 ^ p := lt_trans hst htp
  have hszN : isz ((egN p α s t : ℤ)) ≤ buSZ p :=
    isz_egN_le p α s t (by omega) hsp (by omega)
  have hCB : ∀ v ∈ A, vsz v ≤ buSZ p := by
    intro v hv
    rw [hA] at hv
    exact buCB_small p α s t hs hst hα hp htp hαp v hv
  have hszsub : (egN p α s t - 1).size ≤ 2 * p := by
    have hpos : 0 < 2 ^ (2 * p) := pow_pos (by norm_num) _
    apply Nat.size_le.mpr
    omega
  -- the element word
  have hElemSign (i : ℕ) (hi : i < egN p α s t - 1) :
      Pipe main signProg [Val.cons (Val.int (i : ℤ)) Val.nil]
        [Val.int (1 - 2 * ((i % 2 : ℕ) : ℤ))] (Ks * (p + 1) ^ Ks) := by
    intro rest vs hvs s R hR
    obtain ⟨out, s', nn, hpost, hev, hn, hstk, hoth⟩ :=
      signSpec main p (by omega) i (by omega) rest vs hvs s R hR
    exact ⟨out, s', nn, hpost.2, hev, hn, hstk, hoth⟩
  have hx : ∀ x ∈ xs, vsz x ≤ 2 * p + 4 := by
    intro x hx
    rw [hxs] at hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have hi' : i < egN p α s t - 1 := List.mem_range.mp hi
    have hlt : i < 2 ^ (2 * p) := by omega
    have hsz : isz ((i : ℤ)) ≤ 2 * p + 2 := by
      have h1 : ((i : ℤ)).natAbs = i := Int.natAbs_natCast i
      have h2 : i.size ≤ 2 * p := Nat.size_le.mpr hlt
      simp only [HvdH.isz, h1]
      omega
    rw [Work.Fx.vsz_cons, Work.Fx.vsz_int, buVszNil]
    omega
  have hy : ∀ x ∈ xs, vsz (buSignOf x) ≤ 2 * p + 4 := by
    intro x hx
    rw [hxs] at hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have hidx := buSignIdx i
    rw [buSignOf_cons, Work.Fx.vsz_int, hidx.1, Work.Fx.isz_neg]
    have := hidx.2
    omega
  have hElem : ∀ x ∈ xs, Pipe main (Cmd.seq signProg negProg) (x :: A) (buSignOf x :: A)
      (Ks * (p + 1) ^ Ks + Kneg * 3) := by
    intro x hx
    rw [hxs] at hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have hi' : i < egN p α s t - 1 := List.mem_range.mp hi
    have h1 := hElemSign i hi'
    have h2 : Pipe main negProg [Val.int (1 - 2 * ((i % 2 : ℕ) : ℤ))]
        [Val.int (-(1 - 2 * ((i % 2 : ℕ) : ℤ)))]
        (Kneg * isz (1 - 2 * ((i % 2 : ℕ) : ℤ))) :=
      Pipe.unOp (hNeg main) trivial
    have h3 := Pipe.comp (Pipe.appendTail A h1) (Pipe.appendTail A h2)
    have hidx := buSignIdx i
    refine Pipe.le (Pipe.rw h3 ?_) ?_
    · exact congrArg (fun w : Val => w :: A)
        ((congrArg Val.int hidx.1.symm).trans (buSignOf_cons i).symm)
    · refine Nat.add_le_add_left ?_ (Ks * (p + 1) ^ Ks)
      exact Nat.mul_le_mul_left Kneg hidx.2
  -- the pipeline
  have hG1 : Pipe main (pickProg 5) A (.int ((egN p α s t : ℕ) : ℤ) :: A)
      (Kpick * 6 * (6 * buSZ p + 1)) := by
    refine Pipe.le (Pipe.rw (Pipe.pick (K := Kpick) main hPick (A := A) (k := 5) ?_) ?_) ?_
    · rw [hA]; simp [buCB]
    · have hgetd : A.getD 5 .nil = Val.int ((egN p α s t : ℕ) : ℤ) := by
        rw [hA]; simp [buCB]
      exact congrArg (fun w : Val => w :: A) hgetd
    · change Kpick * 6 * (szl (List.take 6 A) + 1) ≤ Kpick * 6 * (6 * buSZ p + 1)
      have hsl : szl (List.take 6 A) ≤ 6 * buSZ p := by
        refine le_trans (szl_le_len_mul (A := List.take 6 A) (n := buSZ p) ?_) ?_
        · intro v hv
          exact hCB v (List.mem_of_mem_take hv)
        · exact Nat.mul_le_mul_right (buSZ p) (List.length_take_le 6 A)
      exact Nat.mul_le_mul_left (Kpick * 6) (by omega)
  have hG2 : Pipe main (pushProg (.int 1)) (.int ((egN p α s t : ℕ) : ℤ) :: A)
      (.int 1 :: .int ((egN p α s t : ℕ) : ℤ) :: A) (Kpush * 4) := by
    refine Pipe.le (Pipe.pushOnAny (hPush main (.int 1))) ?_
    exact Nat.mul_le_mul_left Kpush (by decide)
  have hG3 : Pipe main swapProg (.int 1 :: .int ((egN p α s t : ℕ) : ℤ) :: A)
      (.int ((egN p α s t : ℕ) : ℤ) :: .int 1 :: A) (Kswap * (buSZ p + 4)) := by
    refine Pipe.le (Pipe.appendTail A (Pipe.swap (K := Kswap) main hSwap (.int 1)
      (.int ((egN p α s t : ℕ) : ℤ)))) ?_
    refine Nat.mul_le_mul_left Kswap ?_
    rw [Work.Fx.vsz_int, Work.Fx.vsz_int, buIszOne]
    have hN := hszN
    omega
  have hG4 : Pipe main subProg (.int ((egN p α s t : ℕ) : ℤ) :: .int 1 :: A)
      (.int (((egN p α s t - 1 : ℕ)) : ℤ) :: A) (Ksub * (buSZ p + 3)) := by
    refine Pipe.le (Pipe.rw (Pipe.appendTail A (Pipe.binOp (hSub main)
      (a := ((egN p α s t : ℕ) : ℤ)) (b := 1) trivial)) ?_) ?_
    · exact congrArg (fun w : Val => w :: A) (congrArg Val.int hncast)
    · refine Nat.mul_le_mul_left Ksub ?_
      rw [buIszOne]
      have hN := hszN
      omega
  have hG5 : Pipe main (pushProg .nil) (.int (((egN p α s t - 1 : ℕ)) : ℤ) :: A)
      (.nil :: .int (((egN p α s t - 1 : ℕ)) : ℤ) :: A) (Kpush * 2) := by
    refine Pipe.le (Pipe.pushOnAny (hPush main .nil)) ?_
    exact Nat.mul_le_mul_left Kpush (by decide)
  have hG6 : Pipe main swapProg (.nil :: .int (((egN p α s t - 1 : ℕ)) : ℤ) :: A)
      (.int (((egN p α s t - 1 : ℕ)) : ℤ) :: .nil :: A) (Kswap * (buSZ p + 4)) := by
    refine Pipe.le (Pipe.appendTail A (Pipe.swap (K := Kswap) main hSwap .nil
      (.int (((egN p α s t - 1 : ℕ)) : ℤ)))) ?_
    refine Nat.mul_le_mul_left Kswap ?_
    rw [Work.Fx.vsz_int, buVszNil, ← hncast]
    have hN := hnsub
    omega
  have hG7 : Pipe main repProg (.int (((egN p α s t - 1 : ℕ)) : ℤ) :: .nil :: A)
      (ofList (List.replicate (egN p α s t - 1) Val.nil) :: A)
      (Krep * (2 * ((egN p α s t - 1) + 1) + buSZ p + 1)) := by
    refine Pipe.le (Pipe.appendTail A (Pipe.replicate (K := Krep) main hRep
      (k := egN p α s t - 1) (v := Val.nil))) ?_
    refine Nat.mul_le_mul_left Krep ?_
    rw [buVszNil, ← hncast]
    have hN := hnsub
    omega
  have hG8 : Pipe main enumProg (ofList (List.replicate (egN p α s t - 1) Val.nil) :: A)
      (ofList xs :: A)
      (Kenum * (2 * ((egN p α s t - 1) + 1) + (egN p α s t - 1) * ((egN p α s t - 1).size + 1)
        + 1)) := by
    refine Pipe.le (Pipe.rw (Pipe.appendTail A (Pipe.enumerate (K := Kenum) main hEnum
      (xs := List.replicate (egN p α s t - 1) Val.nil))) ?_) ?_
    · rw [hxs]
      exact congrArg (fun w : Val => w :: A)
        (congrArg ofList (enumerate_replicate (egN p α s t - 1) Val.nil))
    · rw [replicate_length]
      refine Nat.mul_le_mul_left Kenum ?_
      have hvsl : vsz (ofList (List.replicate (egN p α s t - 1) Val.nil))
          ≤ ((egN p α s t - 1) + 1) * 2 := by
        have hmem : ∀ x ∈ (List.replicate (egN p α s t - 1) Val.nil : List Val), vsz x ≤ 1 := by
          intro x hx
          rw [List.eq_of_mem_replicate hx, buVszNil]
        have h := vsz_ofList_le (l := List.replicate (egN p α s t - 1) Val.nil) (B := 1) hmem
        rw [List.length_replicate] at h
        calc vsz (ofList (List.replicate (egN p α s t - 1) Val.nil))
            ≤ ((egN p α s t - 1) + 1) * (1 + 1) := h
          _ = ((egN p α s t - 1) + 1) * 2 := rfl
      have hs2 := hszsub
      omega
  have hG9 : Pipe main (mlComb (Cmd.seq signProg negProg)) (ofList xs :: A)
      (buL11 p α s t :: A)
      ((egN p α s t - 1) * ((Ks + Kneg + Kml) *
          (p + 1) ^ buSignsKc Kpick Kpush Kswap Ksub Krep Kenum Kml Ks Kneg) + Kml) := by
    refine Pipe.le (Pipe.rw (auMapListTail (comb := mlComb) (Kml := Kml) hML
      (main := main) (q := Cmd.seq signProg negProg) (T := A) (xs := xs) (F := buSignOf)
      (c := Ks * (p + 1) ^ Ks + Kneg * 3) (L := 2 * p + 4) hElem hx hy) ?_) ?_
    · have hmap : xs.map buSignOf =
          (List.range (egN p α s t - 1)).map (fun i : ℕ => Val.int ((-1 : ℤ) ^ (i + 1))) := by
        rw [hxs, List.map_map]
        apply List.map_congr_left
        intro i _
        exact buSignOf_cons i
      have h2 : ofList (xs.map buSignOf) = buL11 p α s t := by
        rw [hmap]
        exact buSignMapEq p α s t
      exact congrArg (fun w : Val => w :: A) h2
    · rw [hxs, List.length_map, List.length_range]
      refine Nat.add_le_add_right (Nat.mul_le_mul_left _ ?_) Kml
      exact buSignSumLe Kpick Kpush Kswap Ksub Krep Kenum Kml Ks Kneg p hp
  have hG89 := Pipe.comp hG8 hG9
  have hG789 := Pipe.comp hG7 hG89
  have hG6789 := Pipe.comp hG6 hG789
  have hG56789 := Pipe.comp hG5 hG6789
  have hG456789 := Pipe.comp hG4 hG56789
  have hG3456789 := Pipe.comp hG3 hG456789
  have hG23456789 := Pipe.comp hG2 hG3456789
  have hall := Pipe.comp hG1 hG23456789
  exact Pipe.le hall (buSignsCost (Kpick := Kpick) (Kpush := Kpush) (Kswap := Kswap)
    (Ksub := Ksub) (Krep := Krep) (Kenum := Kenum) (Kml := Kml) (Ks := Ks) (Kneg := Kneg)
    (p := p) (n := egN p α s t) hp hn2p)

end Work.Resample
