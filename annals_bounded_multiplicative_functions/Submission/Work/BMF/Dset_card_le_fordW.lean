import Mathlib
import Submission.Work.BMF.vkford51_defs
import Submission.Work.BMF.count_resonant_le
import Submission.Work.BMF.TentDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `#D_j ≤ W_j`

The resonant set of Ford's extraction is

`D_j = { d ∈ ℤ : |d| ≤ s M₂^j - 1, nint (d γ_j) < 1/(2 r M₁^j) }`,
with `γ_j = (-1)^j t/(2π j z^j)` (`Work.BMF.Dset`, `Work.BMF.gam`), and Ford's count is

`W_j = min (2 s M₂^j) (2 s M₂^j/(r M₁^j) + s t M₂^j/(π j N^j) + 4π j (2N)^j/(r t M₁^j) + 2)`
(`Work.BMF.fordW`).

This file proves `#D_j ≤ W_j` under `1 ≤ r, 1 ≤ s, 1 ≤ M₁, 1 ≤ M₂`, `t > 0`, `N < z ≤ 2N`, `1 ≤ j`.

The two branches are:

* the *trivial* branch `#D_j ≤ 2 s M₂^j`, because `D_j ⊆ [-K,K]` with `K = s M₂^j - 1`
  has at most `2K+1` elements;
* the branch coming from `Work.BMF.count_resonant_le` (the fibre count over `round (d γ)`),

  `#D_j ≤ 4Kδ + 2K|γ_j| + 4δ/|γ_j| + 2`,   `δ = 1/(2rM₁^j)`, `|γ_j| = t/(2πjz^j)`,

  whose three summands are bounded by `2sM₂^j/(rM₁^j)`, `s t M₂^j/(π j N^j)` and
  `4π j z^j/(r t M₁^j) ≤ 4π j (2N)^j/(r t M₁^j)` respectively (using `N < z ≤ 2N`).
-/

namespace Work.BMF

open Finset

/-- For `1 ≤ j`, the absolute value of the phase `γ_j = (-1)^j t/(2π j z^j)` is
`t/(2π j z^j)`. -/
lemma gam_abs (j : ℕ) (t z : ℝ) (ht : 0 < t) (hz : 0 < z) (hj : 1 ≤ j) :
    |gam j t z| = t / (2 * Real.pi * (j : ℝ) * z ^ j) := by
  unfold gam
  rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi * (j:ℝ) * z^j),
      abs_of_pos ht]

/-- Since `nint` is even, the resonant set only depends on `|γ|`. -/
lemma Dset_abs (r s M₁ M₂ j : ℕ) (γ : ℝ) :
    Dset r s M₁ M₂ j γ = Dset r s M₁ M₂ j |γ| := by
  unfold Dset
  apply Finset.filter_congr
  intro d _
  rcases le_total 0 γ with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h, mul_neg, nint_neg]

/-- The trivial bound on the resonant set: `#D_j ≤ 2 s M₂^j`. -/
lemma Dset_card_le_two_sM₂ (r s M₁ M₂ j : ℕ) (hs : 1 ≤ s) (hM₂ : 1 ≤ M₂) (γ : ℝ) :
    ((Dset r s M₁ M₂ j γ).card : ℝ) ≤ 2 * (s : ℝ) * (M₂ : ℝ) ^ j := by
  have hK1 : 1 ≤ s * M₂ ^ j := by
    have h1 : 1 ≤ M₂ ^ j := Nat.one_le_pow j M₂ (by omega)
    calc 1 = 1 * 1 := by ring
      _ ≤ s * M₂ ^ j := Nat.mul_le_mul hs h1
  have hsub : Dset r s M₁ M₂ j γ ⊆
      Finset.Icc (-(((s * M₂ ^ j - 1 : ℕ)) : ℤ)) (((s * M₂ ^ j - 1 : ℕ) : ℤ)) :=
    Finset.filter_subset _ _
  have hcard : (Dset r s M₁ M₂ j γ).card ≤
      (Finset.Icc (-(((s * M₂ ^ j - 1 : ℕ)) : ℤ)) (((s * M₂ ^ j - 1 : ℕ) : ℤ))).card :=
    Finset.card_le_card hsub
  rw [Int.card_Icc] at hcard
  have htoNat : (((s * M₂ ^ j - 1 : ℕ) : ℤ) + 1 - (-(((s * M₂ ^ j - 1 : ℕ)) : ℤ))).toNat
      = 2 * (s * M₂ ^ j - 1) + 1 := by
    have : (((s * M₂ ^ j - 1 : ℕ) : ℤ) + 1 - (-(((s * M₂ ^ j - 1 : ℕ)) : ℤ)))
        = ((2 * (s * M₂ ^ j - 1) + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this, Int.toNat_natCast]
  rw [htoNat] at hcard
  have hcast : ((s * M₂ ^ j - 1 : ℕ) : ℝ) = (s : ℝ) * (M₂ : ℝ) ^ j - 1 := by
    push_cast [Nat.cast_sub hK1]
    ring
  calc ((Dset r s M₁ M₂ j γ).card : ℝ)
      ≤ ((2 * (s * M₂ ^ j - 1) + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = 2 * ((s : ℝ) * (M₂ : ℝ) ^ j - 1) + 1 := by push_cast [hcast]; ring
    _ ≤ 2 * (s : ℝ) * (M₂ : ℝ) ^ j := by linarith

/-- First summand of the `count_resonant_le` bound: `4Kδ ≤ 2 s M₂^j/(r M₁^j)`. -/
lemma Dset_term_i (r s M₁ M₂ j : ℕ) (hr : 1 ≤ r) (hM₁ : 1 ≤ M₁) :
    4 * ((s * M₂ ^ j - 1 : ℕ) : ℝ) * (1 / (2 * (r : ℝ) * (M₁ : ℝ) ^ j))
      ≤ 2 * (s : ℝ) * (M₂ : ℝ) ^ j / ((r : ℝ) * (M₁ : ℝ) ^ j) := by
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hM1 : (1 : ℝ) ≤ (M₁ : ℝ) := by exact_mod_cast hM₁
  have hden : 0 < (r : ℝ) * (M₁ : ℝ) ^ j := by positivity
  have hKle : (((s * M₂ ^ j - 1 : ℕ)) : ℝ) ≤ (s : ℝ) * (M₂ : ℝ) ^ j := by
    have h1 : (s * M₂ ^ j - 1 : ℕ) ≤ s * M₂ ^ j := Nat.sub_le _ _
    calc (((s * M₂ ^ j - 1 : ℕ)) : ℝ) ≤ ((s * M₂ ^ j : ℕ) : ℝ) := by exact_mod_cast h1
      _ = (s : ℝ) * (M₂ : ℝ) ^ j := by push_cast; ring
  have h4 : 4 * ((s * M₂ ^ j - 1 : ℕ) : ℝ) * (1 / (2 * (r : ℝ) * (M₁ : ℝ) ^ j))
      = 2 * (((s * M₂ ^ j - 1 : ℕ)) : ℝ) / ((r : ℝ) * (M₁ : ℝ) ^ j) := by
    field_simp
    ring
  rw [h4]
  exact div_le_div_of_nonneg_right (by linarith) hden.le

/-- Second summand of the `count_resonant_le` bound: `2K|γ_j| ≤ s t M₂^j/(π j N^j)`,
using `|γ_j| = t/(2π j z^j)` and `z > N`. -/
lemma Dset_term_ii (s M₂ j : ℕ) (N t z : ℝ) (ht : 0 < t) (hN : 0 < N)
    (hNz : N < z) (hj : 1 ≤ j) :
    2 * ((s * M₂ ^ j - 1 : ℕ) : ℝ) * |gam j t z|
      ≤ (s : ℝ) * t * (M₂ : ℝ) ^ j / (Real.pi * (j : ℝ) * N ^ j) := by
  have hjpos : (0:ℝ) < (j:ℝ) := by exact_mod_cast hj
  have hzpos : 0 < z := lt_trans hN hNz
  have hKle : (((s * M₂ ^ j - 1 : ℕ)) : ℝ) ≤ (s : ℝ) * (M₂ : ℝ) ^ j := by
    have h1 : (s * M₂ ^ j - 1 : ℕ) ≤ s * M₂ ^ j := Nat.sub_le _ _
    calc (((s * M₂ ^ j - 1 : ℕ)) : ℝ) ≤ ((s * M₂ ^ j : ℕ) : ℝ) := by exact_mod_cast h1
      _ = (s : ℝ) * (M₂ : ℝ) ^ j := by push_cast; ring
  have hg : |gam j t z| = t / (2 * Real.pi * (j : ℝ) * z ^ j) :=
    gam_abs j t z ht hzpos hj
  have h2 : 2 * (((s * M₂ ^ j - 1 : ℕ)) : ℝ) * |gam j t z|
      ≤ 2 * ((s : ℝ) * (M₂ : ℝ) ^ j) * |gam j t z| := by
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    linarith
  rw [hg] at h2 ⊢
  have h3 : 2 * ((s : ℝ) * (M₂ : ℝ) ^ j) * (t / (2 * Real.pi * (j : ℝ) * z ^ j))
      = (s : ℝ) * t * (M₂ : ℝ) ^ j / (Real.pi * (j : ℝ) * z ^ j) := by
    field_simp
  have h4 : (s : ℝ) * t * (M₂ : ℝ) ^ j / (Real.pi * (j : ℝ) * z ^ j)
      ≤ (s : ℝ) * t * (M₂ : ℝ) ^ j / (Real.pi * (j : ℝ) * N ^ j) := by
    have hdenN : 0 < Real.pi * (j:ℝ) * N^j := mul_pos (mul_pos Real.pi_pos hjpos) (pow_pos hN j)
    have hmain : Real.pi * (j:ℝ) * N^j ≤ Real.pi * (j:ℝ) * z^j :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hN.le hNz.le j)
        (le_of_lt (mul_pos Real.pi_pos hjpos))
    exact div_le_div₀ (by positivity) le_rfl hdenN hmain
  linarith

/-- Third summand of the `count_resonant_le` bound: `4δ/|γ_j| ≤ 4π j (2N)^j/(r t M₁^j)`,
using `|γ_j| = t/(2π j z^j)` and `z ≤ 2N`. -/
lemma Dset_term_iii (r M₁ j : ℕ) (hr : 1 ≤ r) (hM₁ : 1 ≤ M₁) (N t z : ℝ) (ht : 0 < t)
    (hN : 0 < N) (hNz : N < z) (hz2 : z ≤ 2 * N) (hj : 1 ≤ j) :
    4 * (1 / (2 * (r : ℝ) * (M₁ : ℝ) ^ j)) / |gam j t z|
      ≤ 4 * Real.pi * (j : ℝ) * (2 * N) ^ j / ((r : ℝ) * t * (M₁ : ℝ) ^ j) := by
  have hjpos : (0:ℝ) < (j:ℝ) := by exact_mod_cast hj
  have hzpos : 0 < z := lt_trans hN hNz
  have hg : |gam j t z| = t / (2 * Real.pi * (j : ℝ) * z ^ j) :=
    gam_abs j t z ht hzpos hj
  have h3 : 4 * (1 / (2 * (r:ℝ) * (M₁:ℝ)^j)) / |gam j t z|
      = 4 * Real.pi * (j:ℝ) * z^j / ((r:ℝ) * t * (M₁:ℝ)^j) := by
    rw [hg]
    field_simp
  have h4 : 4 * Real.pi * (j:ℝ) * z^j / ((r:ℝ) * t * (M₁:ℝ)^j)
      ≤ 4 * Real.pi * (j:ℝ) * (2*N)^j / ((r:ℝ) * t * (M₁:ℝ)^j) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hzpos.le hz2 j) (by positivity)
  linarith

/--
The number of resonant integers `d ∈ D_j` is at most Ford's `W_j`.
-/
theorem Dset_card_le_fordW (r s M₁ M₂ j : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂)
    (N t z : ℝ) (ht : 0 < t) (hz : N < z) (hz2 : z ≤ 2 * N) (hj : 1 ≤ j) :
    ((Dset r s M₁ M₂ j (gam j t z)).card : ℝ) ≤ fordW (r : ℝ) (s : ℝ) t N (M₁ : ℝ) (M₂ : ℝ) j := by
  have hNpos : 0 < N := by linarith
  have hzpos : 0 < z := lt_trans hNpos hz
  -- the fibre count of `count_resonant_le`
  have hγ : 0 < |gam j t z| := by
    rw [gam_abs j t z ht hzpos hj]
    exact div_pos ht (by positivity)
  have hδ : 0 < 1 / (2 * (r:ℝ) * (M₁:ℝ)^j) := by positivity
  have hcount := count_resonant_le (s * M₂ ^ j - 1) (1 / (2 * (r:ℝ) * (M₁:ℝ)^j))
    |gam j t z| hδ hγ
  have hcount' : ((Dset r s M₁ M₂ j (gam j t z)).card : ℝ) ≤
      4 * ((s * M₂ ^ j - 1 : ℕ) : ℝ) * (1 / (2 * (r:ℝ) * (M₁:ℝ)^j))
        + 2 * ((s * M₂ ^ j - 1 : ℕ) : ℝ) * |gam j t z|
        + 4 * (1 / (2 * (r:ℝ) * (M₁:ℝ)^j)) / |gam j t z| + 2 := by
    rw [Dset_abs r s M₁ M₂ j (gam j t z)]
    simpa only [Dset] using hcount
  have hi := Dset_term_i r s M₁ M₂ j hr hM₁
  have hii := Dset_term_ii s M₂ j N t z ht hNpos hz hj
  have hiii := Dset_term_iii r M₁ j hr hM₁ N t z ht hNpos hz hz2 hj
  have hA : ((Dset r s M₁ M₂ j (gam j t z)).card : ℝ) ≤ 2 * (s : ℝ) * (M₂ : ℝ) ^ j :=
    Dset_card_le_two_sM₂ r s M₁ M₂ j hs hM₂ (gam j t z)
  have hB : ((Dset r s M₁ M₂ j (gam j t z)).card : ℝ) ≤
      2 * (s : ℝ) * (M₂ : ℝ) ^ j / ((r : ℝ) * (M₁ : ℝ) ^ j)
        + (s : ℝ) * t * (M₂ : ℝ) ^ j / (Real.pi * (j : ℝ) * N ^ j)
        + 4 * Real.pi * (j : ℝ) * (2 * N) ^ j / ((r : ℝ) * t * (M₁ : ℝ) ^ j) + 2 := by
    linarith
  rw [fordW]
  exact le_min hA hB

end Work.BMF
