/-
# `FIArea2/R6/Cutoffs6.lean` — the two `C⁴` cutoffs of the round-6 area-2 assembly

`Work.FITop4.IsMajorant6 Pa f` supplies a `C⁴` interpolant `F₀` of `f` with
`|F₀^{(j)}| ≤ cMaj j·Pa.M^{-j}` but **no support control** off the integers; multiplying it by the
two cutoffs below makes it compactly supported with support in a ratio-`64` window, at a cost of
only an absolute constant: the sequence `f` vanishes at every integer outside `[M/4,4M]`, so the
products`χ·F₀`, `ψ·F₀` have traces `f`, `f` on `ℤ` (for `ψ` additionally on `[M/8,M]`).

Both cutoffs are *differences* of two rescaled clamped nonics `step9` (so no product rule is
needed, exactly as in `Work.FITop4.Witness6.majF`):

* `χ x = step9 (8x/M - 1) - step9 (x/(4M) - 1)`: `1` on `[M/4, 4M]`, `0` off `[M/8, 8M]`;
* `ψ x = step9 (8x/M) - step9 (x/M - 1)`: `1` on `[M/8, M]`, `0` off `[0, 2M]`.

The derivative chain and the affine `step9` API are imported from
`Submission.Work.FITop4.Witness6.exists_isMajorant6_seq` (there for the same-purpose `majF`); the
proofs below are that file's proofs with the two slopes made distinct.
-/
import Mathlib
import Submission.Work.FITop4.Witness6.exists_isMajorant6_seq

set_option autoImplicit false

namespace Work.FIArea2.R6

open scoped BigOperators

noncomputable section

open Work.FITop4.Witness6

/-! ## 1. A general difference of two affine `step9`'s -/

/-- The difference of two affine rescalings of the clamped nonic `step9`. -/
def diff (a1 b1 a2 b2 : ℝ) : ℝ → ℝ := sOf a1 b1 - sOf a2 b2

lemma diff_apply (a1 b1 a2 b2 u : ℝ) :
    diff a1 b1 a2 b2 u = step9 (a1 * u + b1) - step9 (a2 * u + b2) := rfl

lemma hasDerivAt_diff (a1 b1 a2 b2 x : ℝ) :
    HasDerivAt (diff a1 b1 a2 b2)
      (rh1 a1 b1 x - rh1 a2 b2 x) x := by
  have h := (hasDerivAt_sOf a1 b1 x).sub (hasDerivAt_sOf a2 b2 x)
  have hv : st8 (a1 * x + b1) * a1 - st8 (a2 * x + b2) * a2
      = rh1 a1 b1 x - rh1 a2 b2 x := by
    show st8 (a1 * x + b1) * a1 - st8 (a2 * x + b2) * a2
        = a1 * st8 (a1 * x + b1) - a2 * st8 (a2 * x + b2)
    ring
  rw [hv] at h
  rw [show diff a1 b1 a2 b2 = sOf a1 b1 - sOf a2 b2 from rfl]
  exact h

lemma hasDerivAt_diff1 (a1 b1 a2 b2 x : ℝ) :
    HasDerivAt (fun u => rh1 a1 b1 u - rh1 a2 b2 u)
      (rh2 a1 b1 x - rh2 a2 b2 x) x := by
  have h := (hasDerivAt_rh1 a1 b1 x).sub (hasDerivAt_rh1 a2 b2 x)
  have hv : a1 * (st7 (a1 * x + b1) * a1) - a2 * (st7 (a2 * x + b2) * a2)
      = rh2 a1 b1 x - rh2 a2 b2 x := by
    show a1 * (st7 (a1 * x + b1) * a1) - a2 * (st7 (a2 * x + b2) * a2)
        = a1 * (a1 * st7 (a1 * x + b1)) - a2 * (a2 * st7 (a2 * x + b2))
    ring
  rw [hv] at h
  rwa [show (rh1 a1 b1 - rh1 a2 b2)
      = (fun u => rh1 a1 b1 u - rh1 a2 b2 u) from rfl] at h

lemma hasDerivAt_diff2 (a1 b1 a2 b2 x : ℝ) :
    HasDerivAt (fun u => rh2 a1 b1 u - rh2 a2 b2 u)
      (rh3 a1 b1 x - rh3 a2 b2 x) x := by
  have h := (hasDerivAt_rh2 a1 b1 x).sub (hasDerivAt_rh2 a2 b2 x)
  have hv : a1 * ((a1 * st6 (a1 * x + b1)) * a1) - a2 * ((a2 * st6 (a2 * x + b2)) * a2)
      = rh3 a1 b1 x - rh3 a2 b2 x := by
    show a1 * ((a1 * st6 (a1 * x + b1)) * a1) - a2 * ((a2 * st6 (a2 * x + b2)) * a2)
        = a1 * (a1 * (a1 * st6 (a1 * x + b1))) - a2 * (a2 * (a2 * st6 (a2 * x + b2)))
    ring
  rw [hv] at h
  rwa [show (rh2 a1 b1 - rh2 a2 b2)
      = (fun u => rh2 a1 b1 u - rh2 a2 b2 u) from rfl] at h

lemma hasDerivAt_diff3 (a1 b1 a2 b2 x : ℝ) :
    HasDerivAt (fun u => rh3 a1 b1 u - rh3 a2 b2 u)
      (rh4 a1 b1 x - rh4 a2 b2 x) x := by
  have h := (hasDerivAt_rh3 a1 b1 x).sub (hasDerivAt_rh3 a2 b2 x)
  have hv : a1 * ((a1 * (a1 * st5 (a1 * x + b1))) * a1)
        - a2 * ((a2 * (a2 * st5 (a2 * x + b2))) * a2)
      = rh4 a1 b1 x - rh4 a2 b2 x := by
    show a1 * ((a1 * (a1 * st5 (a1 * x + b1))) * a1)
        - a2 * ((a2 * (a2 * st5 (a2 * x + b2))) * a2)
        = a1 * (a1 * (a1 * (a1 * st5 (a1 * x + b1))))
          - a2 * (a2 * (a2 * (a2 * st5 (a2 * x + b2))))
    ring
  rw [hv] at h
  rwa [show (rh3 a1 b1 - rh3 a2 b2)
      = (fun u => rh3 a1 b1 u - rh3 a2 b2 u) from rfl] at h

lemma iteratedDeriv1_diff (a1 b1 a2 b2 u : ℝ) :
    iteratedDeriv 1 (diff a1 b1 a2 b2) u = rh1 a1 b1 u - rh1 a2 b2 u := by
  rw [iteratedDeriv_one]
  exact (hasDerivAt_diff a1 b1 a2 b2 u).deriv

lemma iteratedDeriv2_diff (a1 b1 a2 b2 u : ℝ) :
    iteratedDeriv 2 (diff a1 b1 a2 b2) u = rh2 a1 b1 u - rh2 a2 b2 u := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have h1 : deriv (diff a1 b1 a2 b2)
      = fun u => rh1 a1 b1 u - rh1 a2 b2 u :=
    funext fun x => (hasDerivAt_diff a1 b1 a2 b2 x).deriv
  rw [h1]
  exact (hasDerivAt_diff1 a1 b1 a2 b2 u).deriv

lemma iteratedDeriv3_diff (a1 b1 a2 b2 u : ℝ) :
    iteratedDeriv 3 (diff a1 b1 a2 b2) u = rh3 a1 b1 u - rh3 a2 b2 u := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ, show (2 : ℕ) = 1 + 1 from rfl,
    iteratedDeriv_succ, iteratedDeriv_one]
  have h1 : deriv (diff a1 b1 a2 b2)
      = fun u => rh1 a1 b1 u - rh1 a2 b2 u :=
    funext fun x => (hasDerivAt_diff a1 b1 a2 b2 x).deriv
  have h2 : deriv (fun u => rh1 a1 b1 u - rh1 a2 b2 u)
      = fun u => rh2 a1 b1 u - rh2 a2 b2 u :=
    funext fun x => (hasDerivAt_diff1 a1 b1 a2 b2 x).deriv
  rw [h1, h2]
  exact (hasDerivAt_diff2 a1 b1 a2 b2 u).deriv

lemma iteratedDeriv4_diff (a1 b1 a2 b2 u : ℝ) :
    iteratedDeriv 4 (diff a1 b1 a2 b2) u = rh4 a1 b1 u - rh4 a2 b2 u := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, iteratedDeriv_succ, show (3 : ℕ) = 2 + 1 from rfl,
    iteratedDeriv_succ, show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have h1 : deriv (diff a1 b1 a2 b2)
      = fun u => rh1 a1 b1 u - rh1 a2 b2 u :=
    funext fun x => (hasDerivAt_diff a1 b1 a2 b2 x).deriv
  have h2 : deriv (fun u => rh1 a1 b1 u - rh1 a2 b2 u)
      = fun u => rh2 a1 b1 u - rh2 a2 b2 u :=
    funext fun x => (hasDerivAt_diff1 a1 b1 a2 b2 x).deriv
  have h3 : deriv (fun u => rh2 a1 b1 u - rh2 a2 b2 u)
      = fun u => rh3 a1 b1 u - rh3 a2 b2 u :=
    funext fun x => (hasDerivAt_diff2 a1 b1 a2 b2 x).deriv
  rw [h1, h2, h3]
  exact (hasDerivAt_diff3 a1 b1 a2 b2 u).deriv

/-- For `M ≥ 1`, `M^{-(k:ℝ)} = (M^k)⁻¹`. -/
lemma rpow_neg_nat (M : ℝ) (hM : 1 ≤ M) (k : ℕ) :
    M ^ (-(k : ℝ)) = (M ^ k)⁻¹ := by
  rw [Real.rpow_neg (le_of_lt (lt_of_lt_of_le zero_lt_one hM)), Real.rpow_natCast]

/-- The derivative bound for a general difference of two affine `step9`'s: with `a₁M ≤ 8` and
`a₂M ≤ 1`, all derivatives up to order `4` are bounded by `10^11 M^{-j}`. -/
lemma diff_deriv_bound (M a1 a2 b1 b2 : ℝ) (hM : 1 ≤ M) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2)
    (hb1 : a1 * M ≤ 8) (hb2 : a2 * M ≤ 1) :
    ∀ j : ℕ, j ≤ 4 → ∀ x : ℝ,
      |iteratedDeriv j (diff a1 b1 a2 b2) x| ≤ 10 ^ 11 * M ^ (-(j : ℝ)) := by
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  have hle1 : a1 ≤ 8 / M := by rw [le_div_iff₀ hMpos]; linarith
  have hle2 : a2 ≤ 1 / M := by rw [le_div_iff₀ hMpos]; linarith
  have hmono1 : ∀ j : ℕ, a1 ^ j ≤ (8 / M) ^ j := fun j => pow_le_pow_left₀ ha1 hle1 j
  have hmono2 : ∀ j : ℕ, a2 ^ j ≤ (1 / M) ^ j := fun j => pow_le_pow_left₀ ha2 hle2 j
  have hpow : ∀ k : ℕ, M ^ (-(k : ℝ)) = (M ^ k)⁻¹ := rpow_neg_nat M hM
  intro j hj x
  interval_cases j
  · -- `j = 0`
    rw [iteratedDeriv_zero]
    simp only [Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one]
    have h1 := (step9_mem01 (a1 * x + b1))
    have h2 := (step9_mem01 (a2 * x + b2))
    rw [diff_apply, abs_le]
    refine ⟨by linarith [h1.1, h1.2, h2.1, h2.2], by linarith [h1.1, h1.2, h2.1, h2.2]⟩
  · -- `j = 1`
    rw [iteratedDeriv1_diff]
    have h1 := abs_rh1_le a1 b1 x ha1
    have h2 := abs_rh1_le a2 b2 x ha2
    have h3 : a1 * (5 / 2) + a2 * (5 / 2) ≤ 10 ^ 11 * M ^ (-((1 : ℕ) : ℝ)) := by
      rw [hpow 1]
      have hb1' : a1 * M * (5 / 2) ≤ 8 * (5 / 2) := mul_le_mul_of_nonneg_right hb1 (by norm_num)
      have hb2' : a2 * M * (5 / 2) ≤ 1 * (5 / 2) := mul_le_mul_of_nonneg_right hb2 (by norm_num)
      rw [pow_one, le_mul_inv_iff₀ hMpos]
      have e : (a1 * (5 / 2) + a2 * (5 / 2)) * M = a1 * M * (5 / 2) + a2 * M * (5 / 2) := by ring
      rw [e]
      linarith [hb1', hb2']
    calc |rh1 a1 b1 x - rh1 a2 b2 x| ≤ |rh1 a1 b1 x| + |rh1 a2 b2 x| := abs_sub _ _
      _ ≤ a1 * (5 / 2) + a2 * (5 / 2) := add_le_add h1 h2
      _ ≤ 10 ^ 11 * M ^ (-((1 : ℕ) : ℝ)) := h3
  · -- `j = 2`
    rw [iteratedDeriv2_diff]
    have h1 := abs_rh2_le a1 b1 x ha1
    have h2 := abs_rh2_le a2 b2 x ha2
    have h4 : a1 ^ 2 * 25 ≤ (8 / M) ^ 2 * 25 :=
      mul_le_mul_of_nonneg_right (hmono1 2) (by norm_num)
    have h5 : a2 ^ 2 * 25 ≤ (1 / M) ^ 2 * 25 :=
      mul_le_mul_of_nonneg_right (hmono2 2) (by norm_num)
    have h3 : (8 / M) ^ 2 * 25 + (1 / M) ^ 2 * 25 ≤ 10 ^ 11 * M ^ (-((2 : ℕ) : ℝ)) := by
      rw [hpow 2, div_pow, div_pow, div_eq_mul_inv, div_eq_mul_inv]
      have h7 : (0 : ℝ) ≤ (M ^ 2)⁻¹ := inv_nonneg.mpr (by positivity)
      nlinarith [h7]
    calc |rh2 a1 b1 x - rh2 a2 b2 x| ≤ |rh2 a1 b1 x| + |rh2 a2 b2 x| := abs_sub _ _
      _ ≤ a1 ^ 2 * 25 + a2 ^ 2 * 25 := add_le_add h1 h2
      _ ≤ (8 / M) ^ 2 * 25 + (1 / M) ^ 2 * 25 := add_le_add h4 h5
      _ ≤ 10 ^ 11 * M ^ (-((2 : ℕ) : ℝ)) := h3
  · -- `j = 3`
    rw [iteratedDeriv3_diff]
    have h1 := abs_rh3_le a1 b1 x ha1
    have h2 := abs_rh3_le a2 b2 x ha2
    have h4 : a1 ^ 3 * 312480 ≤ (8 / M) ^ 3 * 312480 :=
      mul_le_mul_of_nonneg_right (hmono1 3) (by norm_num)
    have h5 : a2 ^ 3 * 312480 ≤ (1 / M) ^ 3 * 312480 :=
      mul_le_mul_of_nonneg_right (hmono2 3) (by norm_num)
    have h3 : (8 / M) ^ 3 * 312480 + (1 / M) ^ 3 * 312480 ≤ 10 ^ 11 * M ^ (-((3 : ℕ) : ℝ)) := by
      rw [hpow 3, div_pow, div_pow, div_eq_mul_inv, div_eq_mul_inv]
      have h7 : (0 : ℝ) ≤ (M ^ 3)⁻¹ := inv_nonneg.mpr (by positivity)
      nlinarith [h7]
    calc |rh3 a1 b1 x - rh3 a2 b2 x| ≤ |rh3 a1 b1 x| + |rh3 a2 b2 x| := abs_sub _ _
      _ ≤ a1 ^ 3 * 312480 + a2 ^ 3 * 312480 := add_le_add h1 h2
      _ ≤ (8 / M) ^ 3 * 312480 + (1 / M) ^ 3 * 312480 := add_le_add h4 h5
      _ ≤ 10 ^ 11 * M ^ (-((3 : ℕ) : ℝ)) := h3
  · -- `j = 4`
    rw [iteratedDeriv4_diff]
    have h1 := abs_rh4_le a1 b1 x ha1
    have h2 := abs_rh4_le a2 b2 x ha2
    have h4 : a1 ^ 4 * 1360800 ≤ (8 / M) ^ 4 * 1360800 :=
      mul_le_mul_of_nonneg_right (hmono1 4) (by norm_num)
    have h5 : a2 ^ 4 * 1360800 ≤ (1 / M) ^ 4 * 1360800 :=
      mul_le_mul_of_nonneg_right (hmono2 4) (by norm_num)
    have h3 : (8 / M) ^ 4 * 1360800 + (1 / M) ^ 4 * 1360800
        ≤ 10 ^ 11 * M ^ (-((4 : ℕ) : ℝ)) := by
      rw [hpow 4, div_pow, div_pow, div_eq_mul_inv, div_eq_mul_inv]
      have h7 : (0 : ℝ) ≤ (M ^ 4)⁻¹ := inv_nonneg.mpr (by positivity)
      nlinarith [h7]
    calc |rh4 a1 b1 x - rh4 a2 b2 x| ≤ |rh4 a1 b1 x| + |rh4 a2 b2 x| := abs_sub _ _
      _ ≤ a1 ^ 4 * 1360800 + a2 ^ 4 * 1360800 := add_le_add h1 h2
      _ ≤ (8 / M) ^ 4 * 1360800 + (1 / M) ^ 4 * 1360800 := add_le_add h4 h5
      _ ≤ 10 ^ 11 * M ^ (-((4 : ℕ) : ℝ)) := h3

lemma contDiff_diff (a1 b1 a2 b2 : ℝ) : ContDiff ℝ 4 (diff a1 b1 a2 b2) := by
  have h1 : ContDiff ℝ 4 (sOf a1 b1) := by
    have h : ContDiff ℝ 4 (fun u : ℝ => a1 * u + b1) := by fun_prop
    exact step9_props.1.comp h
  have h2 : ContDiff ℝ 4 (sOf a2 b2) := by
    have h : ContDiff ℝ 4 (fun u : ℝ => a2 * u + b2) := by fun_prop
    exact step9_props.1.comp h
  exact h1.sub h2

/-! ## 2. The two cutoffs and their derivative bounds -/

/-- the annulus cutoff `χ`: `1` on `[M/4,4M]`, `0` off `[M/8,8M]`. -/
def chiF (M : ℝ) : ℝ → ℝ := diff (8 / M) (-1) (1 / (4 * M)) (-1)

/-- the plateau step `ψ`: `1` on `[M/8,M]`, `0` off `[0,2M]`. -/
def psiF (M : ℝ) : ℝ → ℝ := diff (8 / M) 0 (1 / M) (-1)

lemma chiF_apply (M u : ℝ) : chiF M u = step9 (8 / M * u + (-1)) - step9 (1 / (4 * M) * u + (-1)) :=
  rfl

lemma psiF_apply (M u : ℝ) : psiF M u = step9 (8 / M * u + 0) - step9 (1 / M * u + (-1)) := rfl

/-! ## 3. The elementary pointwise facts about the two cutoffs -/

lemma chiF_eq_zero_of_le (M x : ℝ) (hM : 0 < M) (h : x ≤ M / 8) : chiF M x = 0 := by
  have h1 : 8 / M * x + -1 ≤ 0 := by
    rw [show 8 / M * x + -1 = (8 * x) / M - 1 by ring]
    rw [sub_nonpos, div_le_iff₀ hM]
    linarith
  have h2 : 1 / (4 * M) * x + -1 ≤ 0 := by
    rw [show 1 / (4 * M) * x + -1 = x / (4 * M) - 1 by ring]
    rw [sub_nonpos, div_le_iff₀ (by positivity : (0 : ℝ) < 4 * M)]
    linarith
  rw [chiF_apply, step9_eq_zero _ h1, step9_eq_zero _ h2, sub_zero]

lemma chiF_eq_zero_of_ge (M x : ℝ) (hM : 0 < M) (h : 8 * M ≤ x) : chiF M x = 0 := by
  have h1 : 1 ≤ 8 / M * x + -1 := by
    rw [show 8 / M * x + -1 = (8 * x) / M - 1 by ring]
    rw [le_sub_iff_add_le, le_div_iff₀ hM]
    linarith
  have h2 : 1 ≤ 1 / (4 * M) * x + -1 := by
    rw [show 1 / (4 * M) * x + -1 = x / (4 * M) - 1 by ring]
    rw [le_sub_iff_add_le, le_div_iff₀ (by positivity : (0 : ℝ) < 4 * M)]
    linarith
  rw [chiF_apply, step9_eq_one _ h1, step9_eq_one _ h2, sub_self]

lemma chiF_eq_one_on (M x : ℝ) (hM : 0 < M) (h1 : M / 4 ≤ x) (h2 : x ≤ 4 * M) :
    chiF M x = 1 := by
  have ha : 1 ≤ 8 / M * x + -1 := by
    rw [show 8 / M * x + -1 = (8 * x) / M - 1 by ring]
    rw [le_sub_iff_add_le, le_div_iff₀ hM]
    linarith
  have hb : 1 / (4 * M) * x + -1 ≤ 0 := by
    rw [show 1 / (4 * M) * x + -1 = x / (4 * M) - 1 by ring]
    rw [sub_nonpos, div_le_iff₀ (by positivity : (0 : ℝ) < 4 * M)]
    linarith
  rw [chiF_apply, step9_eq_one _ ha, step9_eq_zero _ hb, sub_zero]

lemma psiF_eq_zero_of_le (M x : ℝ) (hM : 0 < M) (h : x ≤ 0) : psiF M x = 0 := by
  have h1 : 8 / M * x + 0 ≤ 0 := by
    rw [show 8 / M * x + 0 = (8 * x) / M by ring]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hM.le
  have h2 : 1 / M * x + -1 ≤ 0 := by
    rw [show 1 / M * x + -1 = x / M - 1 by ring, sub_nonpos, div_le_iff₀ hM]
    linarith
  rw [psiF_apply, step9_eq_zero _ h1, step9_eq_zero _ h2, sub_zero]

lemma psiF_eq_zero_of_ge (M x : ℝ) (hM : 0 < M) (h : 2 * M ≤ x) : psiF M x = 0 := by
  have h1 : 1 ≤ 8 / M * x + 0 := by
    rw [show 8 / M * x + 0 = (8 * x) / M by ring, le_div_iff₀ hM]
    linarith
  have h2 : 1 ≤ 1 / M * x + -1 := by
    rw [show 1 / M * x + -1 = x / M - 1 by ring, le_sub_iff_add_le, le_div_iff₀ hM]
    linarith
  rw [psiF_apply, step9_eq_one _ h1, step9_eq_one _ h2, sub_self]

lemma psiF_eq_one_on (M x : ℝ) (hM : 0 < M) (h1 : M / 8 ≤ x) (h2 : x ≤ M) :
    psiF M x = 1 := by
  have ha : 1 ≤ 8 / M * x + 0 := by
    rw [show 8 / M * x + 0 = (8 * x) / M by ring, le_div_iff₀ hM]
    linarith
  have hb : 1 / M * x + -1 ≤ 0 := by
    rw [show 1 / M * x + -1 = x / M - 1 by ring, sub_nonpos, div_le_iff₀ hM]
    linarith
  rw [psiF_apply, step9_eq_one _ ha, step9_eq_zero _ hb, sub_zero]

lemma chiF_abs_le_one (M x : ℝ) : |chiF M x| ≤ 1 := by
  rw [chiF_apply, abs_le]
  have h1 := (step9_mem01 (8 / M * x + -1))
  have h2 := (step9_mem01 (1 / (4 * M) * x + -1))
  exact ⟨by linarith [h1.1, h1.2, h2.1, h2.2], by linarith [h1.1, h1.2, h2.1, h2.2]⟩

lemma psiF_abs_le_one (M x : ℝ) : |psiF M x| ≤ 1 := by
  rw [psiF_apply, abs_le]
  have h1 := (step9_mem01 (8 / M * x + 0))
  have h2 := (step9_mem01 (1 / M * x + -1))
  exact ⟨by linarith [h1.1, h1.2, h2.1, h2.2], by linarith [h1.1, h1.2, h2.1, h2.2]⟩

/-! ## 4. The cutoffs satisfy the required properties -/

theorem exists_cutoffs6 :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : ℝ, 1 ≤ M →
        ∃ χ ψ : ℝ → ℝ,
          ContDiff ℝ 4 χ ∧ HasCompactSupport χ ∧ ContDiff ℝ 4 ψ ∧ HasCompactSupport ψ ∧
          (∀ x : ℝ, |χ x| ≤ 1) ∧ (∀ x : ℝ, |ψ x| ≤ 1) ∧
          (∀ x : ℝ, M / 4 ≤ x → x ≤ 4 * M → χ x = 1) ∧
          (∀ x : ℝ, χ x ≠ 0 → M / 8 ≤ x ∧ x ≤ 8 * M) ∧
          (∀ x : ℝ, M / 8 ≤ x → x ≤ M → ψ x = 1) ∧
          (∀ x : ℝ, ψ x ≠ 0 → 0 ≤ x ∧ x ≤ 2 * M) ∧
          (∀ j : ℕ, j ≤ 4 → ∀ x : ℝ, |iteratedDeriv j χ x| ≤ C * M ^ (-(j : ℝ))) ∧
          (∀ j : ℕ, j ≤ 4 → ∀ x : ℝ, |iteratedDeriv j ψ x| ≤ C * M ^ (-(j : ℝ))) := by
  refine ⟨10 ^ 11, by norm_num, fun M hM => ?_⟩
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  have ha1 : (0 : ℝ) ≤ 8 / M := by positivity
  have ha2 : (0 : ℝ) ≤ 1 / (4 * M) := by positivity
  have ha2' : (0 : ℝ) ≤ 1 / M := by positivity
  have hb1 : (8 / M) * M ≤ 8 := by field_simp; linarith
  have hb2 : (1 / (4 * M)) * M ≤ 1 := by field_simp; linarith
  have hb2' : (1 / M) * M ≤ 1 := by field_simp; linarith
  have hchi_der := diff_deriv_bound M (8 / M) (1 / (4 * M)) (-1) (-1) hM ha1 ha2 hb1 hb2
  have hpsi_der := diff_deriv_bound M (8 / M) (1 / M) 0 (-1) hM ha1 ha2' hb1 hb2'
  refine ⟨chiF M, psiF M, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact contDiff_diff _ _ _ _
  · refine HasCompactSupport.intro (isCompact_Icc (a := M / 8) (b := 8 * M)) ?_
    intro x hx
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with hx | hx
    · exact chiF_eq_zero_of_le M x hMpos (le_of_lt hx)
    · exact chiF_eq_zero_of_ge M x hMpos (le_of_lt hx)
  · exact contDiff_diff _ _ _ _
  · refine HasCompactSupport.intro (isCompact_Icc (a := 0) (b := 2 * M)) ?_
    intro x hx
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with hx | hx
    · exact psiF_eq_zero_of_le M x hMpos (le_of_lt hx)
    · exact psiF_eq_zero_of_ge M x hMpos (le_of_lt hx)
  · exact fun x => chiF_abs_le_one M x
  · exact fun x => psiF_abs_le_one M x
  · intro x h1 h2; exact chiF_eq_one_on M x hMpos h1 h2
  · intro x hx
    constructor
    · by_contra h1
      exact hx (chiF_eq_zero_of_le M x hMpos (le_of_lt (not_le.mp h1)))
    · by_contra h2
      exact hx (chiF_eq_zero_of_ge M x hMpos (le_of_lt (not_le.mp h2)))
  · intro x h1 h2; exact psiF_eq_one_on M x hMpos h1 h2
  · intro x hx
    constructor
    · by_contra h1
      exact hx (psiF_eq_zero_of_le M x hMpos (le_of_lt (not_le.mp h1)))
    · by_contra h2
      exact hx (psiF_eq_zero_of_ge M x hMpos (le_of_lt (not_le.mp h2)))
  · intro j hj x
    simpa only [chiF] using hchi_der j hj x
  · intro j hj x
    simpa only [psiF] using hpsi_der j hj x

end

end Work.FIArea2.R6
