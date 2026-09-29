/-
# Size estimates for the uniform `B̃` preparation word

This module proves `Work.Resample.buPrepSmall`: the small arithmetic/size preparation lemma
used by the assembly of the one-dimensional `B̃` resampling word.  It bounds the encoding size
of the alternating-sign entry `buL11`, the uniform integer bound `buSZ`, the table parameters
`egM` and `egN` (the number of Neumann rounds), and records the elementary power inequality
which lets the final cost estimate absorb a factor `18`.

The mathematical content is the paper's bound `egN p α s t ≤ p + 1` (from the hypothesis
`θ ≥ p/α⁴` on the resampling ratio), together with the elementary estimates
`buSZ p + 1 ≤ (p+1)^4`, `egM p α + 1 ≤ (p+1)^5` and `vsz (buL11 p α s t) ≤ 4(p+1)`.

These estimates were first isolated, with the same names, in
`Submission/Work/Resample/buPrep.lean` (the module that assembles the full preparation word);
they are reproduced here so that this lemma carries no dependency on that larger module.
-/
import Mathlib
import Submission.Work.Resample.buKit

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Resample

open HvdH
open Work.Fx

/-! ## Elementary numerical bounds -/

/-- `buSZ p + 1 ≤ (p+1)^4` for `p ≥ 100`. -/
theorem buSZ_add_one_le (p : ℕ) (hp : 100 ≤ p) : buSZ p + 1 ≤ (p + 1) ^ 4 := by
  have h1 : buSZ p + 1 ≤ 100 * p ^ 3 := by
    simp only [buSZ]
    nlinarith [hp]
  have h2 : 100 * p ^ 3 ≤ (p + 1) ^ 3 * (p + 1) := by
    have h3 : p ^ 3 ≤ (p + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    calc 100 * p ^ 3 ≤ (p + 1) * (p + 1) ^ 3 := Nat.mul_le_mul (by omega) h3
      _ = (p + 1) ^ 3 * (p + 1) := by ring
  calc buSZ p + 1 ≤ 100 * p ^ 3 := h1
    _ ≤ (p + 1) ^ 3 * (p + 1) := h2
    _ = (p + 1) ^ 4 := by ring

/-- `egM p α + 1 ≤ (p+1)^5`. -/
theorem egM_add_one_le (p α : ℕ) (hp : 1 ≤ p) : egM p α + 1 ≤ (p + 1) ^ 5 := by
  have h1 : egM p α + 1 ≤ 2 * (p + 1) := by
    have := egM_le p α
    omega
  calc egM p α + 1 ≤ 2 * (p + 1) := h1
    _ ≤ (p + 1) * (p + 1) := by
        have : (2 : ℕ) ≤ p + 1 := by omega
        exact Nat.mul_le_mul_right _ this
    _ = (p + 1) ^ 2 := by ring
    _ ≤ (p + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)

/-- `4 * (p+1) ≤ (p+1)^20` for `p ≥ 100`. -/
theorem four_mul_succ_le_pow20 (p : ℕ) (hp : 100 ≤ p) : 4 * (p + 1) ≤ (p + 1) ^ 20 := by
  have h5 : (4 : ℕ) ≤ (p + 1) ^ 19 := by
    calc (4 : ℕ) ≤ 2 ^ 19 := by norm_num
      _ ≤ (p + 1) ^ 19 := Nat.pow_le_pow_left (by omega : 2 ≤ p + 1) 19
  calc 4 * (p + 1) ≤ (p + 1) ^ 19 * (p + 1) := Nat.mul_le_mul_right _ h5
    _ = (p + 1) ^ 20 := by rw [← pow_succ]

/-- `18 * (T * q^E) ≤ T * q^(E+5)`, for `q = p+1` with `18 ≤ q^5`. -/
theorem tmul_pow_le {p t E : ℕ} (h : (18 : ℕ) ≤ (p + 1) ^ 5) :
    18 * ((t + 1) * (p + 1) ^ E) ≤ (t + 1) * (p + 1) ^ (E + 5) := by
  calc 18 * ((t + 1) * (p + 1) ^ E)
      ≤ (p + 1) ^ 5 * ((t + 1) * (p + 1) ^ E) := Nat.mul_le_mul_right _ h
    _ = (t + 1) * (p + 1) ^ (E + 5) := by rw [pow_add]; ring

/-! ## Sizes of list values and of `buL11` -/

/-- `vsz` of a cons-list of values. -/
theorem vsz_ofList_val (l : List Val) : vsz (ofList l) = l.length + 1 + (l.map vsz).sum := by
  induction l with
  | nil => simp [ofList, vsz, Val.enc]
  | cons v vs ih =>
    rw [show ofList (v :: vs) = Val.cons v (ofList vs) from rfl, vsz_cons, ih]
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    ring

/-- `vsz` of the integer list value `zl l`. -/
theorem vsz_zl_PS (l : List ℤ) : vsz (zl l) = l.length + 1 + (l.map isz).sum := by
  rw [zl, vsz_ofList_val, List.length_map, List.map_map]
  have h : (l.map (vsz ∘ Val.int)) = (l.map isz) := by
    apply List.map_congr_left
    intro z _
    exact vsz_int z
  rw [h]

/-- `(-1)^{j+1}` has three glyphs. -/
theorem isz_neg_one_pow (j : ℕ) : isz ((-1 : ℤ) ^ (j + 1)) = 3 := by
  have h : (((-1 : ℤ) ^ (j + 1)).natAbs) = 1 := by
    rw [Int.natAbs_pow]
    have h2 : ((-1 : ℤ)).natAbs = 1 := by norm_num
    rw [h2, one_pow]
  simp only [isz, h]
  norm_num

/-- The sum of `isz` over the sign list. -/
theorem sum_isz_neg_one_pow (n : ℕ) :
    ((List.range n).map (isz ∘ fun j => (-1 : ℤ) ^ (j + 1))).sum = 3 * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Function.comp_apply,
      isz_neg_one_pow]
    ring

/-! ## The Neumann round count -/

/-- `egN p α s t ≤ p + 1`, from the paper's hypothesis `θ ≥ p/α⁴`. -/
theorem egN_le_p1 (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hαp : α ^ 2 < p)
    (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1) : egN p α s t ≤ p + 1 := by
  have hspos : 0 < s := by omega
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hspos
  have htsR : (0 : ℝ) < ((t - s : ℕ) : ℝ) := by
    have : 0 < t - s := Nat.sub_pos_of_lt hst
    exact_mod_cast this
  have hkeyR : (p : ℝ) * (s : ℝ) ≤ (α : ℝ) ^ 4 * ((t : ℝ) - (s : ℝ)) := by
    have h1 : ((p : ℝ) / (α : ℝ) ^ 4) ≤ ((t : ℝ) - (s : ℝ)) / (s : ℝ) := by
      have h0 : (t : ℝ) / (s : ℝ) - 1 = ((t : ℝ) - (s : ℝ)) / (s : ℝ) := by
        field_simp
      rw [← h0]
      exact hθ
    have h2 : (0 : ℝ) ≤ (α : ℝ) ^ 4 * (s : ℝ) := by positivity
    have h3 : ((p : ℝ) / (α : ℝ) ^ 4) * ((α : ℝ) ^ 4 * (s : ℝ)) ≤
        (((t : ℝ) - (s : ℝ)) / (s : ℝ)) * ((α : ℝ) ^ 4 * (s : ℝ)) :=
      mul_le_mul_of_nonneg_right h1 h2
    have h4 : ((p : ℝ) / (α : ℝ) ^ 4) * ((α : ℝ) ^ 4 * (s : ℝ)) = (p : ℝ) * (s : ℝ) := by
      field_simp
    have h5 : (((t : ℝ) - (s : ℝ)) / (s : ℝ)) * ((α : ℝ) ^ 4 * (s : ℝ)) =
        (α : ℝ) ^ 4 * ((t : ℝ) - (s : ℝ)) := by
      field_simp
    linarith
  have hkey : p * s ≤ α ^ 4 * (t - s) := by
    have hcast : ((t : ℝ) - (s : ℝ)) = ((t - s : ℕ) : ℝ) := by
      rw [Nat.cast_sub (le_of_lt hst)]
    rw [hcast] at hkeyR
    exact_mod_cast hkeyR
  have h2 : (p * s - 1) / (α ^ 2 * (t - s)) ≤ α ^ 2 := by
    refine Nat.div_le_of_le_mul ?_
    have hp5 : 0 < p := by nlinarith [hαp, hα]
    have hb : p * s - 1 < α ^ 2 * (α ^ 2 * (t - s)) := by
      calc p * s - 1 < p * s := Nat.sub_lt (Nat.mul_pos hp5 (by omega)) (by norm_num)
        _ ≤ α ^ 4 * (t - s) := hkey
        _ = α ^ 2 * (α ^ 2 * (t - s)) := by ring
    calc p * s - 1 ≤ α ^ 2 * (α ^ 2 * (t - s)) := le_of_lt hb
      _ = α ^ 2 * (t - s) * α ^ 2 := by ring
  have h8 : α ^ 2 + 1 ≤ p + 1 := by omega
  have h9 : egN p α s t = (p * s - 1) / (α ^ 2 * (t - s)) + 1 := rfl
  omega

/-- The encoding size of the sign entry `buL11`. -/
theorem vsz_buL11_le (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hαp : α ^ 2 < p)
    (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1) :
    vsz (buL11 p α s t) ≤ 4 * (p + 1) := by
  have hN : egN p α s t ≤ p + 1 := egN_le_p1 p α s t hs hst hα hαp hθ
  have h1 : (List.range (egN p α s t - 1)).length = egN p α s t - 1 := List.length_range
  rw [buL11, vsz_zl_PS, List.length_map, h1, List.map_map, sum_isz_neg_one_pow]
  omega

/-! ## The requested preparation lemma -/

theorem buPrepSmall (p α s t E : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p)
    (htp : t < 2 ^ p) (hαp : α ^ 2 < p)
    (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1) (hE : 100 ≤ E) :
    HvdH.vsz (Work.Resample.buL11 p α s t) ≤ (t + 1) * (p + 1) ^ 20 ∧
    Work.Resample.buSZ p ≤ (t + 1) * (p + 1) ^ 20 ∧
    Work.Resample.buSZ p + 1 ≤ (p + 1) ^ 4 ∧
    Work.Resample.egN p α s t + 1 ≤ (p + 1) ^ 2 ∧
    Work.Resample.egM p α + 1 ≤ (p + 1) ^ 5 ∧
    (18 : ℕ) ≤ (p + 1) ^ 5 ∧
    18 * ((t + 1) * (p + 1) ^ E) ≤ (t + 1) * (p + 1) ^ (E + 5) := by
  have hq : (2 : ℕ) ≤ p + 1 := by omega
  have ht1 : (1 : ℕ) ≤ t + 1 := by omega
  have h18 : (18 : ℕ) ≤ (p + 1) ^ 5 := by
    calc (18 : ℕ) ≤ 2 ^ 5 := by norm_num
      _ ≤ (p + 1) ^ 5 := Nat.pow_le_pow_left hq 5
  have hN : egN p α s t ≤ p + 1 := egN_le_p1 p α s t hs hst hα hαp hθ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_trans (vsz_buL11_le p α s t hs hst hα hαp hθ)
      (le_trans (four_mul_succ_le_pow20 p hp) (le_mul_of_one_le_left (Nat.zero_le _) ht1))
  · have hA : buSZ p ≤ (p + 1) ^ 20 := by
      have h4 := buSZ_add_one_le p hp
      have h45 : (p + 1) ^ 4 ≤ (p + 1) ^ 20 :=
        Nat.pow_le_pow_right (by omega : 0 < p + 1) (by norm_num : 4 ≤ 20)
      omega
    exact le_trans hA (le_mul_of_one_le_left (Nat.zero_le _) ht1)
  · exact buSZ_add_one_le p hp
  · calc egN p α s t + 1 ≤ (p + 1) + 1 := Nat.add_le_add_right hN 1
      _ ≤ (p + 1) * (p + 1) := by nlinarith [hq]
      _ = (p + 1) ^ 2 := (pow_two _).symm
  · exact egM_add_one_le p α (by omega)
  · exact h18
  · exact tmul_pow_le (p := p) (t := t) (E := E) h18

end Work.Resample
