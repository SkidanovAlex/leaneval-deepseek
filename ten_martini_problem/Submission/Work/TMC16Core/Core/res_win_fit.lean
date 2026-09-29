import Mathlib
import Submission.Work.TMC16Core.Core.windows

namespace Work.TMC16Core.Core

open Work.TMC16Core

/-!
# Fitting AJ's resonant windows into the balanced geometry

`res_win_fit` provides, for every `qn ≥ 200` and every offset `r` with
`|r| ≤ qn/40 - 4`, a half-length `h` with `3qn ≤ 5h` and `8h ≤ 5qn` (i.e. `h ≈ 0.6 qn`)
such that AJ's resonant windows

* `I1resG qn h` (the `A`-window, `2h` sites) and
* `I2resG qn h ℓ` (the balanced window around `ℓ qn + r`, `2(qn - h)` sites)

sit inside the two windows of the balanced geometry (`A2blk (2qn-1)` and
`I2set (ℓ qn + r) (2qn-1)`) and have union of cardinality `2 qn` — the exact input
needed by AJ's uniformity/non-generation step at scale `K = 2qn - 1`.

The half-length chosen is `h = ⌊5 qn/8⌋`.  The arithmetic conditions are all tight
(the `A`-window and the balanced window meet with one unit of slack), and the content
of the proof is the integer window arithmetic below, together with the observation
that in the last two inequalities the *real* obstruction is a strict bound
`-0.7 < 0` (resp. `2.3 > 0`) which, being an inequality between integers, improves
to `0 ≤ 0`.
-/

/-! ## Two-sided bounds for the floor/ceil window parameters -/

private lemma b7_two_sided (K : ℕ) :
    10 * b7 K ≤ 7 * (K : ℤ) ∧ 7 * (K : ℤ) - 10 < 10 * b7 K := by
  have hle : ((b7 K : ℤ) : ℝ) ≤ 7 * (K : ℝ) / 10 := by rw [b7]; exact Int.floor_le _
  have hlt : 7 * (K : ℝ) / 10 < ((b7 K : ℤ) : ℝ) + 1 := by
    rw [b7]; exact Int.lt_floor_add_one _
  constructor
  · have h : (10 : ℝ) * ((b7 K : ℤ) : ℝ) ≤ 7 * (K : ℝ) := by linarith
    exact_mod_cast h
  · have h : 7 * (K : ℝ) - 10 < (10 : ℝ) * ((b7 K : ℤ) : ℝ) := by linarith
    exact_mod_cast h

private lemma b3_two_sided (K : ℕ) :
    3 * (K : ℤ) ≤ 10 * b3 K ∧ 10 * b3 K < 3 * (K : ℤ) + 10 := by
  have hle : 3 * (K : ℝ) / 10 ≤ ((b3 K : ℤ) : ℝ) := by rw [b3]; exact Int.le_ceil _
  have hlt : ((b3 K : ℤ) : ℝ) < 3 * (K : ℝ) / 10 + 1 := by
    rw [b3]; exact Int.ceil_lt_add_one _
  constructor
  · have h : 3 * (K : ℝ) ≤ (10 : ℝ) * ((b3 K : ℤ) : ℝ) := by linarith
    exact_mod_cast h
  · have h : (10 : ℝ) * ((b3 K : ℤ) : ℝ) < 3 * (K : ℝ) + 10 := by linarith
    exact_mod_cast h

private lemma b1316_two_sided (K : ℕ) :
    16 * b1316 K ≤ 13 * (K : ℤ) ∧ 13 * (K : ℤ) - 16 < 16 * b1316 K := by
  have hle : ((b1316 K : ℤ) : ℝ) ≤ 13 * (K : ℝ) / 16 := by
    rw [b1316]; exact Int.floor_le _
  have hlt : 13 * (K : ℝ) / 16 < ((b1316 K : ℤ) : ℝ) + 1 := by
    rw [b1316]; exact Int.lt_floor_add_one _
  constructor
  · have h : (16 : ℝ) * ((b1316 K : ℤ) : ℝ) ≤ 13 * (K : ℝ) := by linarith
    exact_mod_cast h
  · have h : 13 * (K : ℝ) - 16 < (16 : ℝ) * ((b1316 K : ℤ) : ℝ) := by linarith
    exact_mod_cast h

private lemma b316_two_sided (K : ℕ) :
    3 * (K : ℤ) ≤ 16 * b316 K ∧ 16 * b316 K < 3 * (K : ℤ) + 16 := by
  have hle : 3 * (K : ℝ) / 16 ≤ ((b316 K : ℤ) : ℝ) := by rw [b316]; exact Int.le_ceil _
  have hlt : ((b316 K : ℤ) : ℝ) < 3 * (K : ℝ) / 16 + 1 := by
    rw [b316]; exact Int.ceil_lt_add_one _
  constructor
  · have h : 3 * (K : ℝ) ≤ (16 : ℝ) * ((b316 K : ℤ) : ℝ) := by linarith
    exact_mod_cast h
  · have h : (16 : ℝ) * ((b316 K : ℤ) : ℝ) < 3 * (K : ℝ) + 16 := by linarith
    exact_mod_cast h

/-! ## Real bounds for the half-length `⌊5 qn/8⌋` -/

private lemma eight_mul_div_le (qn : ℕ) : 8 * (5 * qn / 8) ≤ 5 * qn := by
  have h : 5 * qn / 8 * 8 ≤ 5 * qn := Nat.div_mul_le_self (5 * qn) 8
  omega

private lemma div_lt_succ (qn : ℕ) : 5 * qn < 8 * (5 * qn / 8 + 1) := by
  have h1 : 8 * (5 * qn / 8) + 5 * qn % 8 = 5 * qn := Nat.div_add_mod (5 * qn) 8
  have h2 : 5 * qn % 8 < 8 := Nat.mod_lt _ (by norm_num)
  omega

private lemma div_real_le (qn : ℕ) : ((5 * qn / 8 : ℕ) : ℝ) ≤ 5 * (qn : ℝ) / 8 := by
  have h : ((8 * (5 * qn / 8) : ℕ) : ℝ) ≤ ((5 * qn : ℕ) : ℝ) := by
    exact_mod_cast eight_mul_div_le qn
  push_cast at h
  linarith

private lemma div_real_lt (qn : ℕ) : 5 * (qn : ℝ) / 8 - 1 < ((5 * qn / 8 : ℕ) : ℝ) := by
  have h : ((5 * qn : ℕ) : ℝ) < ((8 * (5 * qn / 8 + 1) : ℕ) : ℝ) := by
    exact_mod_cast div_lt_succ qn
  push_cast at h
  linarith

private lemma div_nat_le (qn : ℕ) : 5 * qn / 8 ≤ qn := by
  have h : 8 * (5 * qn / 8) ≤ 5 * qn := eight_mul_div_le qn
  omega

theorem res_win_fit {qn : ℕ} (hqn : 200 ≤ qn) {r : ℤ} (hr : |r| ≤ (qn : ℤ) / 40 - 4) :
    ∃ h : ℕ, 3 * (qn : ℤ) ≤ 5 * (h : ℤ) ∧ 8 * (h : ℤ) ≤ 5 * (qn : ℤ) ∧
      Work.TMC16Core.Core.I1resG qn h ⊆ Work.TMC16Core.Core.A2blk (2 * qn - 1) ∧
      (∀ ℓ : ℕ, 1 ≤ ℓ → Work.TMC16Core.Core.I2resG qn h ℓ ⊆
        Work.TMC16Core.Core.I2set ((ℓ : ℤ) * (qn : ℤ) + r) (2 * qn - 1)) ∧
      (∀ ℓ : ℕ, 1 ≤ ℓ →
        (Work.TMC16Core.Core.I1resG qn h ∪ Work.TMC16Core.Core.I2resG qn h ℓ).card = 2 * qn) := by
  obtain ⟨hrlo, hrhi⟩ := abs_le.mp hr
  have hKcastR : (((2 * qn - 1 : ℕ)) : ℝ) = 2 * (qn : ℝ) - 1 := by
    have h : 1 ≤ 2 * qn := by omega
    rw [Nat.cast_sub h]; push_cast; ring
  -- the four window parameters at the scale `K = 2 qn - 1`
  have hb7' : 7 * (((2 * qn - 1 : ℕ)) : ℝ) / 10 - 1 < ((b7 (2 * qn - 1) : ℤ) : ℝ) := by
    have := Int.lt_floor_add_one (7 * (((2 * qn - 1 : ℕ)) : ℝ) / 10)
    rw [b7]; linarith
  have hb3' : ((b3 (2 * qn - 1) : ℤ) : ℝ) < 3 * (((2 * qn - 1 : ℕ)) : ℝ) / 10 + 1 := by
    rw [b3]; exact Int.ceil_lt_add_one _
  have hb316' : ((b316 (2 * qn - 1) : ℤ) : ℝ) < 3 * (((2 * qn - 1 : ℕ)) : ℝ) / 16 + 1 := by
    rw [b316]; exact Int.ceil_lt_add_one _
  have hg : ((((qn : ℤ) / 40) : ℤ) : ℝ) ≤ (qn : ℝ) / 40 := by
    have h := Int.ediv_mul_le (qn : ℤ) (show (40 : ℤ) ≠ 0 by norm_num)
    have h' : ((((qn : ℤ) / 40 : ℤ)) : ℝ) * 40 ≤ (qn : ℝ) := by exact_mod_cast h
    linarith
  have hHle : ((5 * qn / 8 : ℕ) : ℝ) ≤ 5 * (qn : ℝ) / 8 := div_real_le qn
  have hHlt : 5 * (qn : ℝ) / 8 - 1 < ((5 * qn / 8 : ℕ) : ℝ) := div_real_lt qn
  -- the two size conditions
  have h345 : 3 * (qn : ℤ) ≤ 5 * (((5 * qn / 8 : ℕ)) : ℤ) := by
    have h : 5 * (qn : ℤ) < 8 * (((5 * qn / 8 : ℕ)) : ℤ) + 8 := by
      exact_mod_cast div_lt_succ qn
    omega
  have h8 : 8 * (((5 * qn / 8 : ℕ)) : ℤ) ≤ 5 * (qn : ℤ) := by
    exact_mod_cast eight_mul_div_le qn
  -- the `A`-window endpoints
  have hA : (((5 * qn / 8 : ℕ)) : ℤ) + (qn : ℤ) - 1 ≤ b1316 (2 * qn - 1) := by
    rw [b1316, Int.le_floor, hKcastR]
    have hcast : (((((5 * qn / 8 : ℕ)) : ℤ) + (qn : ℤ) - 1 : ℤ) : ℝ)
        = ((5 * qn / 8 : ℕ) : ℝ) + (qn : ℝ) - 1 := by
      simp only [Int.cast_add, Int.cast_sub, Int.cast_natCast, Int.cast_one]
    rw [hcast]; linarith
  have hB : (((5 * qn / 8 : ℕ)) : ℤ) - (qn : ℤ) ≤ -b316 (2 * qn - 1) := by
    have hreal : ((((((5 * qn / 8 : ℕ)) : ℤ)) + b316 (2 * qn - 1) : ℤ) : ℝ)
        < ((((qn : ℤ) + 1 : ℤ)) : ℝ) := by
      have hc1 : ((((((5 * qn / 8 : ℕ)) : ℤ)) + b316 (2 * qn - 1) : ℤ) : ℝ)
          = ((5 * qn / 8 : ℕ) : ℝ) + ((b316 (2 * qn - 1) : ℤ) : ℝ) := by
        simp only [Int.cast_add, Int.cast_natCast]
      have hc2 : (((((qn : ℤ) + 1 : ℤ)) : ℝ)) = (qn : ℝ) + 1 := by
        simp only [Int.cast_add, Int.cast_natCast, Int.cast_one]
      rw [hc1, hc2]
      rw [hKcastR] at hb316'
      linarith
    have hz : ((((5 * qn / 8 : ℕ)) : ℤ)) + b316 (2 * qn - 1) < (qn : ℤ) + 1 :=
      Int.cast_lt.mp hreal
    omega
  -- the balanced-window endpoints
  have hC : 2 * (qn : ℤ) + r - b7 (2 * qn - 1) + 2 ≤ (((5 * qn / 8 : ℕ)) : ℤ) := by
    have hreal : ((((-1 : ℤ)) : ℝ)) <
        ((((((5 * qn / 8 : ℕ)) : ℤ)) + b7 (2 * qn - 1) - 2 * (qn : ℤ) - (qn : ℤ) / 40 + 2 : ℤ) : ℝ) := by
      have hc1 : (((-1 : ℤ)) : ℝ) = (-1 : ℝ) := by norm_num
      have hc2 : ((((((5 * qn / 8 : ℕ)) : ℤ)) + b7 (2 * qn - 1) - 2 * (qn : ℤ) -
          (qn : ℤ) / 40 + 2 : ℤ) : ℝ)
          = ((5 * qn / 8 : ℕ) : ℝ) + ((b7 (2 * qn - 1) : ℤ) : ℝ) - 2 * (qn : ℝ)
            - (((qn : ℤ) / 40 : ℤ) : ℝ) + 2 := by
        simp only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat]
      rw [hc1, hc2]
      rw [hKcastR] at hb7'
      linarith
    have hz : (-1 : ℤ) < (((5 * qn / 8 : ℕ)) : ℤ) + b7 (2 * qn - 1) - 2 * (qn : ℤ) -
        (qn : ℤ) / 40 + 2 := Int.cast_lt.mp hreal
    omega
  have hD : b3 (2 * qn - 1) - r ≤ (((5 * qn / 8 : ℕ)) : ℤ) := by
    have hreal : ((((-1 : ℤ)) : ℝ)) <
        ((((((5 * qn / 8 : ℕ)) : ℤ)) - b3 (2 * qn - 1) - (qn : ℤ) / 40 + 4 : ℤ) : ℝ) := by
      have hc1 : (((-1 : ℤ)) : ℝ) = (-1 : ℝ) := by norm_num
      have hc2 : ((((((5 * qn / 8 : ℕ)) : ℤ)) - b3 (2 * qn - 1) - (qn : ℤ) / 40 + 4 : ℤ) : ℝ)
          = ((5 * qn / 8 : ℕ) : ℝ) - ((b3 (2 * qn - 1) : ℤ) : ℝ)
            - (((qn : ℤ) / 40 : ℤ) : ℝ) + 4 := by
        simp only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat]
      rw [hc1, hc2]
      rw [hKcastR] at hb3'
      linarith
    have hz : (-1 : ℤ) < (((5 * qn / 8 : ℕ)) : ℤ) - b3 (2 * qn - 1) - (qn : ℤ) / 40 + 4 :=
      Int.cast_lt.mp hreal
    omega
  -- ## the finset geometry
  have hsub1 : I1resG qn ((5 * qn / 8 : ℕ)) ⊆ A2blk (2 * qn - 1) := by
    intro x hx
    simp only [I1resG, J1resG, Finset.mem_image, Finset.mem_Icc] at hx
    obtain ⟨j, ⟨hjlo, hjhi⟩, rfl⟩ := hx
    simp only [A2blk, Finset.mem_Icc]
    constructor <;> omega
  have hsub2 : ∀ ℓ : ℕ, 1 ≤ ℓ → I2resG qn ((5 * qn / 8 : ℕ)) ℓ ⊆
      I2set ((ℓ : ℤ) * (qn : ℤ) + r) (2 * qn - 1) := by
    intro ℓ hℓ x hx
    simp only [I2resG, J2resG, Finset.mem_image, Finset.mem_Icc] at hx
    obtain ⟨j, ⟨hjlo, hjhi⟩, rfl⟩ := hx
    simp only [I2set, Finset.mem_Icc]
    have hexp : ((ℓ : ℤ) - 1) * (qn : ℤ) = (ℓ : ℤ) * (qn : ℤ) - (qn : ℤ) := by ring
    rw [hexp] at hjlo
    have hexp2 : ((ℓ : ℤ) + 1) * (qn : ℤ) = (ℓ : ℤ) * (qn : ℤ) + (qn : ℤ) := by ring
    rw [hexp2] at hjhi
    constructor <;> omega
  have hinj : Function.Injective (fun j : ℤ => j - ((qn : ℤ) - 1)) := by
    intro a b hab
    linarith
  have hcard1 : (I1resG qn ((5 * qn / 8 : ℕ))).card = 2 * (5 * qn / 8) := by
    unfold I1resG
    rw [Finset.card_image_of_injective _ hinj, J1resG, Int.card_Icc]
    have h1 : (↑(5 * qn / 8 : ℕ) : ℤ) - 1 + 1 - -(↑(5 * qn / 8 : ℕ) : ℤ) =
        2 * (↑(5 * qn / 8 : ℕ) : ℤ) := by ring
    rw [h1]
    apply Nat.cast_injective (R := ℤ)
    push_cast
    exact Int.toNat_of_nonneg (by positivity)
  have hcard2 : ∀ ℓ : ℕ, 1 ≤ ℓ →
      (I2resG qn ((5 * qn / 8 : ℕ)) ℓ).card = 2 * qn - 2 * (5 * qn / 8) := by
    intro ℓ hℓ
    unfold I2resG
    rw [Finset.card_image_of_injective _ hinj, J2resG, Int.card_Icc]
    have h1 : ((ℓ : ℤ) + 1) * (qn : ℤ) - (↑(5 * qn / 8 : ℕ) : ℤ) - 1 + 1 -
        (((ℓ : ℤ) - 1) * (qn : ℤ) + (↑(5 * qn / 8 : ℕ) : ℤ)) =
        2 * ((qn : ℤ) - (↑(5 * qn / 8 : ℕ) : ℤ)) := by ring
    rw [h1]
    have hh : 5 * qn / 8 ≤ qn := div_nat_le qn
    have h3 : (2 * ((qn : ℤ) - (↑(5 * qn / 8 : ℕ) : ℤ))) =
        ((2 * (qn - 5 * qn / 8) : ℕ) : ℤ) := by
      rw [Nat.cast_mul, Nat.cast_sub hh]; push_cast; ring
    rw [h3, Int.toNat_natCast]
    omega
  have hdisj : ∀ ℓ : ℕ, 1 ≤ ℓ →
      Disjoint (I1resG qn ((5 * qn / 8 : ℕ))) (I2resG qn ((5 * qn / 8 : ℕ)) ℓ) := by
    intro ℓ hℓ
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [I1resG, J1resG, Finset.mem_image, Finset.mem_Icc] at hx1
    simp only [I2resG, J2resG, Finset.mem_image, Finset.mem_Icc] at hx2
    obtain ⟨j1, ⟨hj1lo, hj1hi⟩, he1⟩ := hx1
    obtain ⟨j2, ⟨hj2lo, hj2hi⟩, he2⟩ := hx2
    have hnn : (0 : ℤ) ≤ ((ℓ : ℤ) - 1) * (qn : ℤ) :=
      mul_nonneg (by omega) (by positivity)
    omega
  have hcardU : ∀ ℓ : ℕ, 1 ≤ ℓ →
      (I1resG qn ((5 * qn / 8 : ℕ)) ∪ I2resG qn ((5 * qn / 8 : ℕ)) ℓ).card = 2 * qn := by
    intro ℓ hℓ
    rw [Finset.card_union_of_disjoint (hdisj ℓ hℓ), hcard1, hcard2 ℓ hℓ]
    have hh : 5 * qn / 8 ≤ qn := div_nat_le qn
    omega
  exact ⟨5 * qn / 8, h345, h8, hsub1, hsub2, hcardU⟩

end Work.TMC16Core.Core
