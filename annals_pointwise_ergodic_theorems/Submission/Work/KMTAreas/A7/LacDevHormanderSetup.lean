/-
# The discrete Hörmander condition for the lacunary deviation kernels: setup

This module fixes the "single-scale" deviation kernel

  `devKernM K m j = (1/m) K (j/m) − (∫K) · triKernel (lacLevN m) j`

(the kernel `devKern K σ n` of `Work.KMTAreas.A7.lacDilDefs` depends on `σ` and `n` only through
the scale `σ n`), together with the elementary estimates on it used by the discrete Hörmander
condition `Work.KMTAreas.A7.lacDevHormander`:

* `devKern_eq_devKernM` — `devKern K σ n = devKernM K (σ n)`;
* the lacunary arithmetic of the dyadic level `lacLevN m = ⌊log₂ (max m 2)⌋`;
* `triKernel_lacLevN_le`, `triKernel_lacLevN_eq_zero_of_abs_gt` — the size and support of the
  triangular kernel at that level;
* `devKernM_norm_le` — the Schwartz decay `‖devKernM K m j‖ ≤ A m (1 + |j|)^{-2}` (the decay
  regime `m ≤ |y|` of the Hörmander estimate);
* `triKernel_lip` — the Lipschitz bound `|triKernel L j − triKernel L j'| ≤ |j − j'| / 4^L`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LacDevBasics

set_option autoImplicit false

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

/-- The dyadic level of the integral scale `m`: `⌊log₂ (max m 2)⌋` (the natural-number form of
`lacLev σ n` when `m = σ n`). -/
def lacLevN (m : ℕ) : ℕ := Nat.log 2 (max m 2)

/-- The sampled bump kernel at the integral scale `m`: `j ↦ (1/m) K (j/m)`. -/
def bumpKernM (K : SchwartzMap ℝ ℂ) (m : ℕ) (j : ℤ) : ℂ :=
  (1 / (m : ℝ)) * K ((j : ℝ) / (m : ℝ))

/-- The deviation kernel at the integral scale `m`: the sampled bump minus `∫K` times the
triangular kernel at the dyadic level `lacLevN m`. -/
def devKernM (K : SchwartzMap ℝ ℂ) (m : ℕ) (j : ℤ) : ℂ :=
  bumpKernM K m j
    - lacConst K * (((Work.Analysis.Hilbert.triKernel (lacLevN m) j : ℝ)) : ℂ)

lemma lacLev_eq_lacLevN (σ : ℕ → ℕ) (n : ℕ) : lacLev σ n = lacLevN (σ n) := rfl

lemma devKern_eq_devKernM (K : SchwartzMap ℝ ℂ) (σ : ℕ → ℕ) (n : ℕ) (j : ℤ) :
    devKern K σ n j = devKernM K (σ n) j := rfl

lemma bumpKern_eq_bumpKernM (K : SchwartzMap ℝ ℂ) (σ : ℕ → ℕ) (n : ℕ) (j : ℤ) :
    bumpKern K σ n j = bumpKernM K (σ n) j := rfl

/-! ## Lacunary arithmetic of `lacLevN` -/

lemma pow_lacLevN_le {m : ℕ} (hm : 1 ≤ m) : 2 ^ lacLevN m ≤ 2 * m :=
  pow_lacLev_le (σ := fun _ => m) (fun _ => hm) 0

lemma le_two_pow_lacLevN (m : ℕ) : m ≤ 2 ^ (lacLevN m + 1) :=
  le_two_pow_lacLev (σ := fun _ => m) 0

lemma pow_lacLevN_pos (m : ℕ) : 0 < (2 : ℝ) ^ lacLevN m := by positivity

/-- `2 ^ lacLevN m ≥ m / 2`, hence `4 ^ lacLevN m ≥ m ^ 2 / 4`. -/
lemma sq_div_four_le_pow_four_lacLevN (m : ℕ) :
    ((m : ℝ)) ^ 2 / 4 ≤ (4 : ℝ) ^ lacLevN m := by
  have h := le_two_pow_lacLevN m
  have h2 : ((m : ℝ)) ≤ 2 * (2 : ℝ) ^ lacLevN m := by
    have h' : ((m : ℕ) : ℝ) ≤ (((2 : ℕ) ^ (lacLevN m + 1) : ℕ) : ℝ) := by exact_mod_cast h
    rw [Nat.cast_pow, Nat.cast_ofNat, pow_succ] at h'
    push_cast at h'
    linarith
  have h4 : (4 : ℝ) ^ lacLevN m = ((2 : ℝ) ^ lacLevN m) ^ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
    congr 1
    ring
  rw [h4]
  nlinarith [h2, sq_nonneg ((2 : ℝ) ^ lacLevN m)]

lemma triKernel_lacLevN_le {m : ℕ} (hm : 1 ≤ m) (j : ℤ) :
    Work.Analysis.Hilbert.triKernel (lacLevN m) j ≤ 2 * ((m : ℝ))⁻¹ :=
  triKernel_lacLev_le (σ := fun _ => m) (fun _ => hm) 0 j

lemma triKernel_lacLevN_eq_zero_of_abs_gt {m : ℕ} {j : ℤ}
    (h : (2 : ℝ) ^ lacLevN m < |(j : ℝ)|) :
    Work.Analysis.Hilbert.triKernel (lacLevN m) j = 0 := by
  refine triKernel_eq_zero_of_abs (lacLevN m) ?_
  have hcast : (((2 : ℤ) ^ lacLevN m : ℤ) : ℝ) = (2 : ℝ) ^ lacLevN m := by push_cast; ring
  rw [hcast]
  exact h

/-! ## The decay of the deviation kernel at scale `m` -/

/-- `x^{-2} = 1/x^2` for `x > 0` (real powers). -/
lemma rpow_neg_two_eq {x : ℝ} (hx : 0 < x) : x ^ (-2 : ℝ) = 1 / x ^ 2 := by
  rw [Real.rpow_neg hx.le, Real.rpow_two, one_div]

/-- **Schwartz decay of the deviation kernel at the integral scale `m`**:
`‖devKernM K m j‖ ≤ A m (1 + |j|)^{-2}`. -/
theorem devKernM_norm_le (K : SchwartzMap ℝ ℂ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (m : ℕ), 1 ≤ m → ∀ j : ℤ,
      ‖devKernM K m j‖ ≤ A * (m : ℝ) * (1 + |(j : ℝ)|) ^ (-2 : ℝ) := by
  obtain ⟨A, hApos, hA⟩ := devKern_norm_le K
  refine ⟨A, hApos, ?_⟩
  intro m hm j
  have hσ1 : ∀ n : ℕ, 1 ≤ (fun _ => m : ℕ → ℕ) n := fun _ => hm
  have h1 : m ≤ (fun _ => m : ℕ → ℕ) 0 := le_rfl
  have hbase := hA (fun _ => m) hσ1 0 j
  rw [show devKern K (fun _ => m) 0 j = devKernM K m j from rfl] at hbase
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hdiv := one_add_div_rpow_neg_two_le (m : ℝ) hm1 ((j : ℝ))
  refine hbase.trans ?_
  have hnn : (0 : ℝ) ≤ ((m : ℝ))⁻¹ := by positivity
  calc A * ((m : ℝ))⁻¹ * (1 + |(j : ℝ)| / (m : ℝ)) ^ (-2 : ℝ)
      ≤ A * ((m : ℝ))⁻¹ * ((m : ℝ) ^ 2 * (1 + |(j : ℝ)|) ^ (-2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hdiv (mul_nonneg hApos.le hnn)
    _ = A * (m : ℝ) * (1 + |(j : ℝ)|) ^ (-2 : ℝ) := by
        field_simp

/-! ## The triangular kernel is Lipschitz at scale `4^{-L}` -/

/-- `max 0` is `1`-Lipschitz. -/
lemma abs_max_zero_sub_max_zero (u v : ℝ) : |max 0 u - max 0 v| ≤ |u - v| := by
  simpa only [max_comm 0 u, max_comm 0 v] using abs_max_sub_max_le_abs u v (0 : ℝ)

theorem triKernel_lip (L : ℕ) (j j' : ℤ) :
    |Work.Analysis.Hilbert.triKernel L j - Work.Analysis.Hilbert.triKernel L j'|
      ≤ |(j : ℝ) - (j' : ℝ)| / (4 : ℝ) ^ L := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (2 * L) := by positivity
  have hpow : (2 : ℝ) ^ (2 * L) = (4 : ℝ) ^ L := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, pow_mul]
  have hu : Work.Analysis.Hilbert.triKernel L j
      = max 0 (((2 : ℝ) ^ L - |(j : ℝ)|) / (2 : ℝ) ^ (2 * L)) := rfl
  have hv : Work.Analysis.Hilbert.triKernel L j'
      = max 0 (((2 : ℝ) ^ L - |(j' : ℝ)|) / (2 : ℝ) ^ (2 * L)) := rfl
  rw [hu, hv]
  have hnum : ((2 : ℝ) ^ L - |(j : ℝ)|) / (2 : ℝ) ^ (2 * L)
      - ((2 : ℝ) ^ L - |(j' : ℝ)|) / (2 : ℝ) ^ (2 * L)
      = (|(j' : ℝ)| - |(j : ℝ)|) / (2 : ℝ) ^ (2 * L) := by
    rw [← sub_div]
    congr 1
    ring
  calc |max 0 (((2 : ℝ) ^ L - |(j : ℝ)|) / (2 : ℝ) ^ (2 * L))
        - max 0 (((2 : ℝ) ^ L - |(j' : ℝ)|) / (2 : ℝ) ^ (2 * L))|
      ≤ |((2 : ℝ) ^ L - |(j : ℝ)|) / (2 : ℝ) ^ (2 * L)
          - ((2 : ℝ) ^ L - |(j' : ℝ)|) / (2 : ℝ) ^ (2 * L)| :=
        abs_max_zero_sub_max_zero _ _
    _ = |(|(j' : ℝ)| - |(j : ℝ)|)| / (2 : ℝ) ^ (2 * L) := by
        rw [hnum, abs_div, abs_of_pos h2]
    _ ≤ |(j : ℝ) - (j' : ℝ)| / (2 : ℝ) ^ (2 * L) := by
        refine div_le_div_of_nonneg_right ?_ h2.le
        rw [abs_sub_comm]
        exact abs_abs_sub_abs_le_abs_sub _ _
    _ = |(j : ℝ) - (j' : ℝ)| / (4 : ℝ) ^ L := by rw [hpow]

end

end Work.KMTAreas.A7
