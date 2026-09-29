import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.IntLib.encodeNatBridge
import Submission.Work.Resample.sliceA1defs
import Submission.Work.Resample.sliceA1Ext
import Submission.Work.Resample.sliceA1Sum

/-!
# The static-table word `prep` of the `Ã₁` slice (paper Lemma 4.9)

For the *non-uniform* statement `Work.Resample.sliceA1` the parameters `p, α, s, t` are fixed
before the existential, so the static data block `P = [slT p α s t]` is a *constant*: the word
`prep` merely drops the four parameter values and pushes the table.  This module proves the size
bound on `slT` that its cost needs.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-- `vsz` of an integer value is `isz`. -/
theorem vsz_int' (z : ℤ) : vsz (Val.int z) = isz z := by
  show (Val.int z).enc.length = isz z
  exact Work.IntLib.vsz_int z

/-- `vsz` of a cons value. -/
theorem vsz_cons (a b : Val) : vsz (Val.cons a b) = 1 + vsz a + vsz b := by
  simp only [vsz, Val.enc, List.length_cons, List.length_append]
  omega

theorem vsz_nil : vsz (Val.nil : Val) = 1 := by
  simp [vsz, Val.enc]

/-- `vsz` of a list value. -/
theorem vsz_ofList (l : List Val) : vsz (ofList l) = l.length + 1 + (l.map vsz).sum := by
  induction l with
  | nil => simp [ofList, vsz_nil]
  | cons v vs ih =>
    have h : ofList (v :: vs) = Val.cons v (ofList vs) := rfl
    rw [h, vsz_cons, ih]
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    ring

/-- Sum of a bounded list. -/
theorem list_sum_le_mul {l : List ℕ} {B : ℕ} (h : ∀ x ∈ l, x ≤ B) : l.sum ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : a ≤ B := h a (by simp)
    have hl : ∀ x ∈ l, x ≤ B := fun x hx => h x (by simp [hx])
    simp only [List.sum_cons, List.length_cons]
    have := ih hl
    nlinarith

/-- The integer weights `slW` are nonnegative and below `2^p`. -/
theorem slW_le (p α s t : ℕ) (hs : 2 ≤ s) (hα : 2 ≤ α) {k : ℕ} (hk : k < t) (i : ℕ) :
    0 ≤ slW p α s t k i ∧ slW p α s t k i ≤ (2 : ℤ) ^ p := by
  have h0 : (0 : ℝ) ≤ slA p α s t k i := (sliceA1Sum p α s t hs hα k hk).1 i
  have h1 : slA p α s t k i ≤ 1 := (sliceA1Sum p α s t hs hα k hk).2.1 i
  have hp : (0 : ℝ) < (2 : ℝ) ^ p := by positivity
  have hmul : (2 : ℝ) ^ p * slA p α s t k i ≤ (2 : ℝ) ^ p := by nlinarith
  have hfl := Int.floor_le ((2 : ℝ) ^ p * slA p α s t k i + 1 / 2)
  have hfr := Int.lt_floor_add_one ((2 : ℝ) ^ p * slA p α s t k i + 1 / 2)
  have hle : (slW p α s t k i : ℝ) ≤ (2 : ℝ) ^ p * slA p α s t k i + 1 / 2 := by
    simpa [slW, rnd] using hfl
  have hlt : (2 : ℝ) ^ p * slA p α s t k i + 1 / 2 - 1 < (slW p α s t k i : ℝ) := by
    simpa [slW, rnd] using hfr
  have hupR : ((slW p α s t k i : ℤ) : ℝ) < ((2 : ℤ) ^ p : ℝ) + 1 := by
    push_cast
    linarith
  have hlowR : (-1 : ℝ) < ((slW p α s t k i : ℤ) : ℝ) := by nlinarith [hlt, h0, hp]
  refine ⟨?_, ?_⟩
  · have h2 : (-1 : ℤ) < slW p α s t k i := by exact_mod_cast hlowR
    omega
  · have h2 : (slW p α s t k i : ℤ) < (2 : ℤ) ^ p + 1 := by exact_mod_cast hupR
    exact Int.lt_add_one_iff.mp h2

/-- The integer weights `slW` have at most `p + 3` glyphs. -/
theorem isz_slW_le (p α s t : ℕ) (hs : 2 ≤ s) (hα : 2 ≤ α) {k : ℕ} (hk : k < t) (i : ℕ) :
    isz (slW p α s t k i) ≤ p + 3 := by
  obtain ⟨h0, hupZ⟩ := slW_le p α s t hs hα hk i
  have habs : (slW p α s t k i).natAbs ≤ 2 ^ p := by
    have h2 : ((slW p α s t k i).natAbs : ℤ) ≤ ((2 ^ p : ℕ) : ℤ) := by
      rw [Int.natAbs_of_nonneg h0]
      push_cast
      exact hupZ
    exact_mod_cast h2
  have hsize : (slW p α s t k i).natAbs.size ≤ p + 1 := by
    rw [Nat.size_le]
    calc (slW p α s t k i).natAbs ≤ 2 ^ p := habs
      _ < 2 ^ (p + 1) := by
          rw [pow_succ]
          have h2p : 0 < 2 ^ p := by positivity
          omega
  simp only [isz]
  omega

/-- Bound on the size of one table record. -/
theorem vsz_slRec_le (p α s t : ℕ) (hs : 2 ≤ s) (hα : 2 ≤ α) (ht : 0 < t) (hst : s ≤ t)
    {k : ℕ} (hk : k < t) : vsz (slRec p α s t k) ≤ 8 + 2 * slL p α s * (p + 4) := by
  have hd : slD s t k ≤ 1 := (sliceA1Ext p α s t hs ht hst).2.2.2.2.2.2.1 k
  have hlenmap : ((List.ofFn (fun i : Fin (2 * slL p α s) =>
      slW p α s t k ((i : ℕ) / 2))).map (fun w => Val.int w)).length = 2 * slL p α s := by
    rw [List.length_map, List.length_ofFn]
  have hsum0 := list_sum_le_mul (B := p + 3) (l := List.map vsz
      ((List.ofFn (fun i : Fin (2 * slL p α s) =>
        slW p α s t k ((i : ℕ) / 2))).map (fun w => Val.int w))) (by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    rw [List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    rw [List.mem_ofFn] at hw
    obtain ⟨i, rfl⟩ := hw
    rw [vsz_int']
    exact isz_slW_le p α s t hs hα hk ((i : ℕ) / 2))
  have hlen2 : (List.map vsz ((List.ofFn (fun i : Fin (2 * slL p α s) =>
      slW p α s t k ((i : ℕ) / 2))).map (fun w => Val.int w))).length = 2 * slL p α s := by
    rw [List.length_map, hlenmap]
  have hsum : (List.map vsz ((List.ofFn (fun i : Fin (2 * slL p α s) =>
      slW p α s t k ((i : ℕ) / 2))).map (fun w => Val.int w))).sum
      ≤ 2 * slL p α s * (p + 3) := by
    rw [hlen2] at hsum0; exact hsum0
  have hw : vsz (ofList ((List.ofFn (fun i : Fin (2 * slL p α s) =>
      slW p α s t k ((i : ℕ) / 2))).map (fun w => Val.int w)))
      ≤ 2 * slL p α s * (p + 3) + 2 * slL p α s + 1 := by
    rw [vsz_ofList, hlenmap]
    linarith [hsum, hlen2]
  have hd2 : vsz (Val.int (slD s t k : ℤ)) ≤ 3 := by
    have hs1 : (slD s t k).size ≤ 1 := by rw [Nat.size_le]; omega
    rw [vsz_int']
    show isz ((slD s t k : ℕ) : ℤ) ≤ 3
    have hna : (((slD s t k : ℕ) : ℤ)).natAbs = slD s t k := by
      have h := Int.natAbs_of_nonneg (show (0 : ℤ) ≤ (slD s t k : ℤ) by omega)
      exact_mod_cast h
    rw [isz, hna]
    omega
  rw [slRec, vsz_cons]
  have hL : 0 ≤ slL p α s := Nat.zero_le _
  nlinarith [hw, hd2, hL]

/-- Bound on the size of the whole table `slT`. -/
theorem vsz_slT_le (p α s t : ℕ) (hs : 2 ≤ s) (hα : 2 ≤ α) (ht : 0 < t) (hst : s ≤ t) :
    vsz (slT p α s t) ≤ (t + 1) * (12 + 2 * slL p α s * (p + 4)) := by
  have hlenmap : (List.map vsz (List.ofFn (fun k : Fin t => slRec p α s t k))).length = t := by
    rw [List.length_map, List.length_ofFn]
  have hsum0 := list_sum_le_mul (l := List.map vsz (List.ofFn (fun k : Fin t => slRec p α s t k)))
    (B := 8 + 2 * slL p α s * (p + 4)) (by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨v, hv, rfl⟩ := hx
      rw [List.mem_ofFn] at hv
      obtain ⟨k, rfl⟩ := hv
      exact vsz_slRec_le p α s t hs hα ht hst k.isLt)
  have hsum : (List.map vsz (List.ofFn (fun k : Fin t => slRec p α s t k))).sum
      ≤ t * (8 + 2 * slL p α s * (p + 4)) := by
    rw [hlenmap] at hsum0; exact hsum0
  rw [slT, vsz_ofList, List.length_ofFn]
  have hL : 0 ≤ slL p α s := Nat.zero_le _
  nlinarith [hsum, hL]

end Work.Resample
