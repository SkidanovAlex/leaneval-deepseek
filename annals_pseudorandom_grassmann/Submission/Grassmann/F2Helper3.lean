import Submission.Grassmann.F2Helper2
import Submission.Grassmann.InfluenceBound
import Submission.Commons.Analysis.Inequalities.sum_sq_le_mul_sum_of_pointwise
import Submission.Commons.Combinatorics.QBinomial.gb_pair_pow_sum_lt_one_of_le_two_mul

/-!
# `lem:F2` of arXiv:2209.04243 — the Cauchy--Schwarz assembly

The triangle-inequality bound `F2_helper` (`Submission/Grassmann/F2Helper.lean`) is upgraded to
a bound on *squares* by the weighted Cauchy--Schwarz inequality over the index set of quadruples
`(i, j, V₁, W₁)`:

`(∑ a)² ≤ (∑ b)(∑ c)`,  `a_{ijV₁W₁} = [bcond] · q^{2i²+2j²} ‖ĉ‖`,
`b_{ijV₁W₁} = [bcond] · q^{-7d(i+j)} q^{4i²+4j²}`,  `c_{ijV₁W₁} = [bcond] · q^{7d(i+j)} ‖ĉ‖²`,

with `b_k² = b_k c_k` pointwise, `∑ b ≤ 1` (`sum_b_le_one`, the arithmetic of `lem:F2`) and
`∑ c` the displayed right-hand side.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

/-- The index set of the `𝓕₂` Cauchy--Schwarz step. -/
abbrev BSIdx (m n : ℕ) :=
  Fin (n + 1) × Fin (m + 1) × Submodule 𝔽₂ (Fin n → 𝔽₂) × Submodule 𝔽₂ (Fin m → 𝔽₂)

variable {m n : ℕ}

/-- The condition `V₁ ∈ 𝓥_i(X) ∧ W₁ ∈ 𝓦_j(X)`.

Kept as an `abbrev` on purpose: the *displayed* and the *named* form of the condition can then be
rewritten interchangeably by `if_pos`/`if_neg`/`rw`, which is impossible with a plain `def`
(keyed matching does not unfold a `def`). -/
abbrev bcond (X : Matrix (Fin n) (Fin m) 𝔽₂) (i j : ℕ)
    (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) : Prop :=
  V₁ ≤ LinearMap.range X.mulVecLin ∧ LinearMap.ker X.mulVecLin ≤ W₁ ∧
    Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j

/-- The first factor of the Cauchy--Schwarz inequality. -/
def aF (X : Matrix (Fin n) (Fin m) 𝔽₂) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ)
    (k : BSIdx m n) : ℝ :=
  (if k.1.val = 0 ∧ k.2.1.val = 0 then 0
    else (2 : ℝ) ^ (2 * k.1.val ^ 2 + 2 * k.2.1.val ^ 2)) *
  (if bcond X k.1.val k.2.1.val k.2.2.1 k.2.2.2 then
      ‖fcoeff (Lap2 k.2.2.1 k.2.2.2 f) X‖ else 0)

/-- The second factor of the Cauchy--Schwarz inequality. -/
def bF (d : ℕ) (X : Matrix (Fin n) (Fin m) 𝔽₂) (k : BSIdx m n) : ℝ :=
  (if k.1.val = 0 ∧ k.2.1.val = 0 then 0
    else ((2 : ℝ) ^ (7 * d * (k.1.val + k.2.1.val)))⁻¹ *
      (2 : ℝ) ^ (4 * k.1.val ^ 2 + 4 * k.2.1.val ^ 2)) *
  (if bcond X k.1.val k.2.1.val k.2.2.1 k.2.2.2 then 1 else 0)

/-- The third factor of the Cauchy--Schwarz inequality. -/
def cF (d : ℕ) (X : Matrix (Fin n) (Fin m) 𝔽₂) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ)
    (k : BSIdx m n) : ℝ :=
  (if k.1.val = 0 ∧ k.2.1.val = 0 then 0
    else (2 : ℝ) ^ (7 * d * (k.1.val + k.2.1.val))) *
  (if bcond X k.1.val k.2.1.val k.2.2.1 k.2.2.2 then
      ‖fcoeff (Lap2 k.2.2.1 k.2.2.2 f) X‖ ^ 2 else 0)

/-! ## Reindexing a sum over `BSIdx` -/

/-- A sum over the product type `BSIdx` is a nested sum over `range`- and `Fintype`-indices. -/
lemma sum_BSIdx_eq (m n : ℕ)
    (F : ℕ → ℕ → Submodule 𝔽₂ (Fin n → 𝔽₂) → Submodule 𝔽₂ (Fin m → 𝔽₂) → ℝ) :
    (∑ k : BSIdx m n, F k.1.val k.2.1.val k.2.2.1 k.2.2.2)
      = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
          ∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
            F i j V₁ W₁ := by
  simp only [Fintype.sum_prod_type]
  rw [Fin.sum_univ_eq_sum_range (fun i => ∑ j : Fin (m + 1),
        ∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
          F i j.val V₁ W₁) (n + 1)]
  apply Finset.sum_congr rfl; intro i _
  rw [Fin.sum_univ_eq_sum_range (fun j =>
        ∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
          F i j V₁ W₁) (m + 1)]

/-! ## The three sums -/

/-- `∑ aF` is the right-hand side of `F2_helper`. -/
lemma sum_aF_eq {m n : ℕ} (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    (∑ k : BSIdx m n, aF X f k)
      = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
          (if i = 0 ∧ j = 0 then 0 else (2 : ℝ) ^ (2 * i ^ 2 + 2 * j ^ 2)) *
            (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
              (if bcond X i j V₁ W₁ then ‖fcoeff (Lap2 V₁ W₁ f) X‖ else 0)) := by
  have h1 : (∑ k : BSIdx m n, aF X f k)
      = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
          ∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
            (if i = 0 ∧ j = 0 then 0 else (2 : ℝ) ^ (2 * i ^ 2 + 2 * j ^ 2)) *
              (if bcond X i j V₁ W₁ then ‖fcoeff (Lap2 V₁ W₁ f) X‖ else 0) := by
    rw [show (∑ k : BSIdx m n, aF X f k) = (∑ k : BSIdx m n,
        (fun i j V₁ W₁ => (if i = 0 ∧ j = 0 then 0 else (2 : ℝ) ^ (2 * i ^ 2 + 2 * j ^ 2)) *
          (if bcond X i j V₁ W₁ then ‖fcoeff (Lap2 V₁ W₁ f) X‖ else 0))
          k.1.val k.2.1.val k.2.2.1 k.2.2.2) from by simp only [aF]]
    exact sum_BSIdx_eq m n (fun i j V₁ W₁ =>
      (if i = 0 ∧ j = 0 then 0 else (2 : ℝ) ^ (2 * i ^ 2 + 2 * j ^ 2)) *
        (if bcond X i j V₁ W₁ then ‖fcoeff (Lap2 V₁ W₁ f) X‖ else 0))
  rw [h1]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun V₁ _ => ?_)
  rw [Finset.mul_sum]

/-- `∑ bF` in the shape of `sum_b_le_one`. -/
lemma sum_bF_eq {m n : ℕ} (d : ℕ) (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    (∑ k : BSIdx m n, bF d X k)
      = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
          (if i = 0 ∧ j = 0 then 0 else
            (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
              (if bcond X i j V₁ W₁ then (1 : ℝ) else 0)) *
            ((2 : ℝ) ^ (7 * d * (i + j)))⁻¹ * (2 : ℝ) ^ (4 * i ^ 2 + 4 * j ^ 2)) := by
  have h1 : (∑ k : BSIdx m n, bF d X k)
      = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
          (if i = 0 ∧ j = 0 then 0 else
            ((2 : ℝ) ^ (7 * d * (i + j)))⁻¹ * (2 : ℝ) ^ (4 * i ^ 2 + 4 * j ^ 2)) *
            (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
              (if bcond X i j V₁ W₁ then (1 : ℝ) else 0)) := by
    have h2 : (∑ k : BSIdx m n, bF d X k)
        = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
            ∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
              (if i = 0 ∧ j = 0 then 0 else
                ((2 : ℝ) ^ (7 * d * (i + j)))⁻¹ * (2 : ℝ) ^ (4 * i ^ 2 + 4 * j ^ 2)) *
                (if bcond X i j V₁ W₁ then (1 : ℝ) else 0) := by
      rw [show (∑ k : BSIdx m n, bF d X k) = (∑ k : BSIdx m n,
          (fun i j V₁ W₁ => (if i = 0 ∧ j = 0 then 0 else
            ((2 : ℝ) ^ (7 * d * (i + j)))⁻¹ * (2 : ℝ) ^ (4 * i ^ 2 + 4 * j ^ 2)) *
            (if bcond X i j V₁ W₁ then (1 : ℝ) else 0))
            k.1.val k.2.1.val k.2.2.1 k.2.2.2) from by simp only [bF]]
      exact sum_BSIdx_eq m n (fun i j V₁ W₁ =>
        (if i = 0 ∧ j = 0 then 0 else
          ((2 : ℝ) ^ (7 * d * (i + j)))⁻¹ * (2 : ℝ) ^ (4 * i ^ 2 + 4 * j ^ 2)) *
          (if bcond X i j V₁ W₁ then (1 : ℝ) else 0))
    rw [h2]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun V₁ _ => ?_)
    rw [Finset.mul_sum]
  rw [h1]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  by_cases hcase : i = 0 ∧ j = 0
  · simp [hcase]
  · simp only [if_neg hcase]
    ring

/-- **The arithmetic bound of `lem:F2`**: `∑ bF ≤ 1`. -/
lemma sum_bF_le_one {m n : ℕ} (d : ℕ) (X : Matrix (Fin n) (Fin m) 𝔽₂) (hX : X.rank ≤ d) :
    (∑ k : BSIdx m n, bF d X k) ≤ 1 := by
  rw [sum_bF_eq]
  exact sum_b_le_one d X hX

/-- `∑ cF` in the shape of the target bound. -/
lemma sum_cF_eq {m n : ℕ} (d : ℕ) (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    (∑ k : BSIdx m n, cF d X f k)
      = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
          (if i = 0 ∧ j = 0 then 0 else (2 : ℝ) ^ (7 * d * (i + j))) *
            (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
              (if bcond X i j V₁ W₁ then ‖fcoeff (Lap2 V₁ W₁ f) X‖ ^ 2 else 0)) := by
  have h1 : (∑ k : BSIdx m n, cF d X f k)
      = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
          ∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
            (if i = 0 ∧ j = 0 then 0 else (2 : ℝ) ^ (7 * d * (i + j))) *
              (if bcond X i j V₁ W₁ then ‖fcoeff (Lap2 V₁ W₁ f) X‖ ^ 2 else 0) := by
    rw [show (∑ k : BSIdx m n, cF d X f k) = (∑ k : BSIdx m n,
        (fun i j V₁ W₁ => (if i = 0 ∧ j = 0 then 0 else (2 : ℝ) ^ (7 * d * (i + j))) *
          (if bcond X i j V₁ W₁ then ‖fcoeff (Lap2 V₁ W₁ f) X‖ ^ 2 else 0))
          k.1.val k.2.1.val k.2.2.1 k.2.2.2) from by simp only [cF]]
    exact sum_BSIdx_eq m n (fun i j V₁ W₁ => (if i = 0 ∧ j = 0 then 0 else (2 : ℝ) ^ (7 * d * (i + j))) *
      (if bcond X i j V₁ W₁ then ‖fcoeff (Lap2 V₁ W₁ f) X‖ ^ 2 else 0))
  rw [h1]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun V₁ _ => ?_)
  rw [Finset.mul_sum]

/-- `∑ cF` is bounded by the displayed right-hand side of `F2_sq_le`. -/
lemma sum_cF_le {m n : ℕ} (d : ℕ) (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    (∑ k : BSIdx m n, cF d X f k) ≤
      ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
        (2 : ℝ) ^ (7 * d * (i + j)) *
          (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
            (if bcond X i j V₁ W₁ then ‖fcoeff (Lap2 V₁ W₁ f) X‖ ^ 2 else 0)) := by
  rw [sum_cF_eq]
  refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
  by_cases hcase : i = 0 ∧ j = 0
  · rw [if_pos hcase]
    have hS : 0 ≤ ∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
        (if bcond X i j V₁ W₁ then ‖fcoeff (Lap2 V₁ W₁ f) X‖ ^ 2 else 0) := by
      refine Finset.sum_nonneg fun V₁ _ => Finset.sum_nonneg fun W₁ _ => ?_
      by_cases h : bcond X i j V₁ W₁
      · rw [if_pos h]; positivity
      · rw [if_neg h]
    have h0 : i + j = 0 := by omega
    rw [h0, mul_zero, pow_zero, one_mul, zero_mul]
    exact hS
  · rw [if_neg hcase]

/-! ## The pointwise Cauchy--Schwarz inequality -/

/-- Nonnegativity of `bF`. -/
lemma bF_nonneg (d : ℕ) (X : Matrix (Fin n) (Fin m) 𝔽₂) (k : BSIdx m n) :
    0 ≤ bF d X k := by
  simp only [bF]
  by_cases h0 : k.1.val = 0 ∧ k.2.1.val = 0
  · rw [if_pos h0, zero_mul]
  · rw [if_neg h0]
    by_cases hc : bcond X k.1.val k.2.1.val k.2.2.1 k.2.2.2
    · rw [if_pos hc, mul_one]; positivity
    · rw [if_neg hc, mul_zero]

/-- Nonnegativity of `cF`. -/
lemma cF_nonneg (d : ℕ) (X : Matrix (Fin n) (Fin m) 𝔽₂) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ)
    (k : BSIdx m n) : 0 ≤ cF d X f k := by
  simp only [cF]
  by_cases h0 : k.1.val = 0 ∧ k.2.1.val = 0
  · rw [if_pos h0, zero_mul]
  · rw [if_neg h0]
    by_cases hc : bcond X k.1.val k.2.1.val k.2.2.1 k.2.2.2
    · rw [if_pos hc]; positivity
    · rw [if_neg hc, mul_zero]

/-- The pointwise Cauchy--Schwarz inequality `aF² ≤ bF · cF`. -/
lemma aF_sq_le (d : ℕ) (X : Matrix (Fin n) (Fin m) 𝔽₂) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ)
    (k : BSIdx m n) : aF X f k ^ 2 ≤ bF d X k * cF d X f k := by
  unfold aF bF cF
  set z : ℝ := ‖fcoeff (Lap2 k.2.2.1 k.2.2.2 f) X‖ with hz
  by_cases h0 : k.1.val = 0 ∧ k.2.1.val = 0
  · simp only [if_pos h0, zero_mul]
    norm_num
  · simp only [if_neg h0]
    by_cases hc : bcond X k.1.val k.2.1.val k.2.2.1 k.2.2.2
    · simp only [if_pos hc, mul_one]
      have hx : (2 : ℝ) ^ (7 * d * (k.1.val + k.2.1.val)) ≠ 0 := by positivity
      have hL : ((2 : ℝ) ^ (2 * k.1.val ^ 2 + 2 * k.2.1.val ^ 2) * z) ^ 2
          = (2 : ℝ) ^ (4 * k.1.val ^ 2 + 4 * k.2.1.val ^ 2) * z ^ 2 := by
        rw [mul_pow, ← pow_mul,
          show (2 * k.1.val ^ 2 + 2 * k.2.1.val ^ 2) * 2
            = 4 * k.1.val ^ 2 + 4 * k.2.1.val ^ 2 from by ring]
      have hR : ((2 : ℝ) ^ (7 * d * (k.1.val + k.2.1.val)))⁻¹ *
            (2 : ℝ) ^ (4 * k.1.val ^ 2 + 4 * k.2.1.val ^ 2) *
              ((2 : ℝ) ^ (7 * d * (k.1.val + k.2.1.val)) * z ^ 2)
          = (2 : ℝ) ^ (4 * k.1.val ^ 2 + 4 * k.2.1.val ^ 2) * z ^ 2 := by
        rw [show ((2 : ℝ) ^ (7 * d * (k.1.val + k.2.1.val)))⁻¹ *
              (2 : ℝ) ^ (4 * k.1.val ^ 2 + 4 * k.2.1.val ^ 2) *
                ((2 : ℝ) ^ (7 * d * (k.1.val + k.2.1.val)) * z ^ 2)
            = ((2 : ℝ) ^ (7 * d * (k.1.val + k.2.1.val)))⁻¹ *
              (2 : ℝ) ^ (7 * d * (k.1.val + k.2.1.val)) *
                (2 : ℝ) ^ (4 * k.1.val ^ 2 + 4 * k.2.1.val ^ 2) * z ^ 2 from by ring]
        rw [inv_mul_cancel₀ hx, one_mul]
      rw [hL, hR]
    · simp only [if_neg hc, mul_zero]
      norm_num

/-! ## The main bound -/

/-- **`lem:F2` of arXiv:2209.04243**: the square of the `𝓕₂` contribution is bounded by the
`q^{7d(i+j)}`-weighted sum of the squares of the `(L_{V₁}∘L_{W₁}[f])²` Fourier coefficients. -/
theorem F2_sq_le {m n : ℕ} (d : ℕ) (X : Matrix (Fin n) (Fin m) 𝔽₂) (hX : X.rank ≤ d)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    ‖F2Sum X f‖ ^ 2 ≤
      ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
        (2 : ℝ) ^ (7 * d * (i + j)) *
          (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
            (if bcond X i j V₁ W₁ then ‖fcoeff (Lap2 V₁ W₁ f) X‖ ^ 2 else 0)) := by
  have hA : ‖F2Sum X f‖ ≤ ∑ k : BSIdx m n, aF X f k := by
    rw [sum_aF_eq]; exact F2_helper X f
  have hcs := Commons.Analysis.Inequalities.sum_sq_le_mul_sum_of_pointwise
    (aF X f) (bF d X) (cF d X f) (fun k => bF_nonneg d X k) (fun k => cF_nonneg d X f k)
    (fun k => aF_sq_le d X f k)
  have hb1 : (∑ k : BSIdx m n, bF d X k) ≤ 1 := sum_bF_le_one d X hX
  have hcT : (∑ k : BSIdx m n, cF d X f k) ≤
      ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
        (2 : ℝ) ^ (7 * d * (i + j)) *
          (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
            (if bcond X i j V₁ W₁ then ‖fcoeff (Lap2 V₁ W₁ f) X‖ ^ 2 else 0)) :=
    sum_cF_le d X f
  have hcnn : 0 ≤ ∑ k : BSIdx m n, cF d X f k :=
    Finset.sum_nonneg fun k _ => cF_nonneg d X f k
  calc ‖F2Sum X f‖ ^ 2
      ≤ (∑ k : BSIdx m n, aF X f k) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hA 2
    _ ≤ (∑ k : BSIdx m n, bF d X k) * (∑ k : BSIdx m n, cF d X f k) := hcs
    _ ≤ 1 * (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
          (2 : ℝ) ^ (7 * d * (i + j)) *
            (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
              (if bcond X i j V₁ W₁ then ‖fcoeff (Lap2 V₁ W₁ f) X‖ ^ 2 else 0))) :=
        mul_le_mul hb1 hcT hcnn (by norm_num)
    _ = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
          (2 : ℝ) ^ (7 * d * (i + j)) *
            (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
              (if bcond X i j V₁ W₁ then ‖fcoeff (Lap2 V₁ W₁ f) X‖ ^ 2 else 0)) := one_mul _

/-! ## `lem:F2` for functions of degree `≤ d`, and the sum over `X`

For a function `f` of degree `≤ d` the coefficients `fcoeff (Lap2 V₁ W₁ f) X` vanish unless
`finrank V₁ ≤ d` and `m - finrank W₁ ≤ d`; this restricts the Cauchy--Schwarz sum of `lem:F2`
to the range `i, j ≤ d`, in which the arithmetic factor stays `< 1` for all `X` with
`X.rank ≤ 2 d`.  Summing over `X` then gives the second display of `lem:F2`.
-/

/-- `‖g*g‖₂² = ‖g‖₄⁴`. -/
lemma l2sq_mul_self {m n : ℕ} (g : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    l2sq (fun A => g A * g A) = l4q g := by
  rw [l2sq, l4q]
  congr 1
  refine Finset.sum_congr rfl (fun A _ => ?_)
  rw [norm_mul, mul_pow]
  ring

/-- The right-hand side of `lem:F2`: the `q^{7d(i+j)}`-weighted sum of the squared normalised
Fourier coefficients of `(L_{V₁} ∘ L_{W₁}[f])²`. -/
def F2RHS {m n : ℕ} (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ)
    (X : Matrix (Fin n) (Fin m) 𝔽₂) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
    (if i = 0 ∧ j = 0 then 0 else (2 : ℝ) ^ (7 * d * (i + j))) *
      (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
        (if bcond X i j V₁ W₁ then ‖fcoeff (Lap2 V₁ W₁ f) X‖ ^ 2 else 0))

/-- For `f` of degree `≤ d`, the coefficient of `X` in `(L_{V₁}∘L_{W₁}f)²` vanishes when
`V₁` is more than `d`-dimensional. -/
lemma fcoeff_Lap2_eq_zero_of_finrank_gt {m n d : ℕ} {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ}
    (hf : DegLe d f) (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (hV : d < Module.finrank 𝔽₂ V₁) (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    fcoeff (Lap2 V₁ W₁ f) X = 0 := by
  rw [fcoeff_Lap2]
  refine Finset.sum_eq_zero (fun Y _ => ?_)
  by_cases h : V₁ ≤ LinearMap.range Y.mulVecLin ∧ LinearMap.ker Y.mulVecLin ≤ W₁ ∧
      V₁ ≤ LinearMap.range (X + Y).mulVecLin ∧ LinearMap.ker (X + Y).mulVecLin ≤ W₁
  · rw [if_pos h]
    have h1 : d < Y.rank := by
      have hle := Submodule.finrank_mono h.1
      rw [finrank_range_mulVecLin] at hle
      omega
    rw [fcoeff_eq, fcoeff_eq, hf Y h1]
    ring
  · rw [if_neg h]

/-- For `f` of degree `≤ d`, the coefficient of `X` in `(L_{V₁}∘L_{W₁}f)²` vanishes when `W₁`
has codimension more than `d`. -/
lemma fcoeff_Lap2_eq_zero_of_codim_gt {m n d : ℕ} {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ}
    (hf : DegLe d f) (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (hW : d < m - Module.finrank 𝔽₂ W₁) (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    fcoeff (Lap2 V₁ W₁ f) X = 0 := by
  rw [fcoeff_Lap2]
  refine Finset.sum_eq_zero (fun Y _ => ?_)
  by_cases h : V₁ ≤ LinearMap.range Y.mulVecLin ∧ LinearMap.ker Y.mulVecLin ≤ W₁ ∧
      V₁ ≤ LinearMap.range (X + Y).mulVecLin ∧ LinearMap.ker (X + Y).mulVecLin ≤ W₁
  · rw [if_pos h]
    have h1 : d < Y.rank := by
      have hle := Submodule.finrank_mono h.2.1
      rw [finrank_ker_mulVecLin] at hle
      have h2 : Y.rank ≤ m := Matrix.rank_le_width Y
      omega
    rw [fcoeff_eq, fcoeff_eq, hf Y h1]
    ring
  · rw [if_neg h]

/-- The second Cauchy--Schwarz factor, restricted to the degrees `i, j ≤ d` (the only range in
which `fcoeff (Lap2 V₁ W₁ f) X` can be non-zero when `f` has degree `≤ d`). -/
def bF2 {m n : ℕ} (d : ℕ) (X : Matrix (Fin n) (Fin m) 𝔽₂) (k : BSIdx m n) : ℝ :=
  (if k.1.val ≤ d ∧ k.2.1.val ≤ d then 1 else 0) * bF d X k

lemma bF2_nonneg (d : ℕ) (X : Matrix (Fin n) (Fin m) 𝔽₂) (k : BSIdx m n) :
    0 ≤ bF2 d X k := by
  simp only [bF2]
  by_cases h : k.1.val ≤ d ∧ k.2.1.val ≤ d
  · rw [if_pos h, one_mul]; exact bF_nonneg d X k
  · rw [if_neg h, zero_mul]

/-- `aF` vanishes outside the range `i, j ≤ d` for a function of degree `≤ d`. -/
lemma aF_eq_zero_of_deg_gt {m n d : ℕ} {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ}
    (hf : DegLe d f) (X : Matrix (Fin n) (Fin m) 𝔽₂) (k : BSIdx m n)
    (h : ¬ (k.1.val ≤ d ∧ k.2.1.val ≤ d)) : aF X f k = 0 := by
  simp only [aF]
  by_cases hb : bcond X k.1.val k.2.1.val k.2.2.1 k.2.2.2
  · rw [if_pos hb]
    have hfc : fcoeff (Lap2 k.2.2.1 k.2.2.2 f) X = 0 := by
      rcases not_and_or.mp h with h1 | h2
      · have hlt : d < k.1.val := by omega
        exact fcoeff_Lap2_eq_zero_of_finrank_gt hf _ _ (by rw [hb.2.2.1]; exact hlt) X
      · have hlt : d < k.2.1.val := by omega
        have hjm : k.2.1.val ≤ m := Nat.lt_succ_iff.mp k.2.1.isLt
        refine fcoeff_Lap2_eq_zero_of_codim_gt hf _ _ ?_ X
        rw [hb.2.2.2, Nat.sub_sub_self hjm]
        exact hlt
    rw [hfc, norm_zero, mul_zero]
  · rw [if_neg hb, mul_zero]

/-- The pointwise Cauchy--Schwarz inequality with the degree-restricted second factor. -/
lemma aF_sq_le_bF2 (d : ℕ) (X : Matrix (Fin n) (Fin m) 𝔽₂) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ)
    (hf : DegLe d f) (k : BSIdx m n) : aF X f k ^ 2 ≤ bF2 d X k * cF d X f k := by
  simp only [bF2]
  by_cases h : k.1.val ≤ d ∧ k.2.1.val ≤ d
  · rw [if_pos h, one_mul]; exact aF_sq_le d X f k
  · rw [if_neg h, zero_mul, aF_eq_zero_of_deg_gt hf X k h]
    norm_num

/-- Pulling a constant out of a double `Fintype` sum. -/
lemma sum_sum_mul_const {α β : Type*} [Fintype α] [Fintype β] (a : ℝ) (f : α → β → ℝ) :
    (∑ x : α, ∑ y : β, a * f x y) = a * ∑ x : α, ∑ y : β, f x y := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.mul_sum]

/-- A sum over `range N` of `[j ≤ d] · f j` is at most the sum over `range (d+1)`. -/
lemma sum_range_ite_le {f : ℕ → ℝ} (hf : ∀ j, 0 ≤ f j) (N d : ℕ) :
    (∑ j ∈ Finset.range N, (if j ≤ d then f j else 0)) ≤ ∑ j ∈ Finset.range (d + 1), f j := by
  rw [← Finset.sum_filter]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    omega
  · intro j _ _
    exact hf j

/-- Reindexing of `∑ bF2`, with the degree guard `i, j ≤ d` made explicit. -/
lemma sum_bF2_eq {m n : ℕ} (d : ℕ) (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    (∑ k : BSIdx m n, bF2 d X k)
      = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
          ((if i ≤ d ∧ j ≤ d then 1 else 0) *
            (if i = 0 ∧ j = 0 then 0 else
              ((2 : ℝ) ^ (7 * d * (i + j)))⁻¹ * (2 : ℝ) ^ (4 * i ^ 2 + 4 * j ^ 2))) *
            (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
              (if bcond X i j V₁ W₁ then (1 : ℝ) else 0)) := by
  have h2 : (∑ k : BSIdx m n, bF2 d X k)
      = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
          ∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
            (if i ≤ d ∧ j ≤ d then 1 else 0) *
              ((if i = 0 ∧ j = 0 then 0 else
                  ((2 : ℝ) ^ (7 * d * (i + j)))⁻¹ * (2 : ℝ) ^ (4 * i ^ 2 + 4 * j ^ 2)) *
                (if bcond X i j V₁ W₁ then (1 : ℝ) else 0)) := by
    rw [show (∑ k : BSIdx m n, bF2 d X k) = (∑ k : BSIdx m n,
        (fun i j V₁ W₁ => (if i ≤ d ∧ j ≤ d then 1 else 0) *
          ((if i = 0 ∧ j = 0 then 0 else
              ((2 : ℝ) ^ (7 * d * (i + j)))⁻¹ * (2 : ℝ) ^ (4 * i ^ 2 + 4 * j ^ 2)) *
            (if bcond X i j V₁ W₁ then (1 : ℝ) else 0)))
          k.1.val k.2.1.val k.2.2.1 k.2.2.2) from by simp only [bF2, bF]]
    exact sum_BSIdx_eq m n (fun i j V₁ W₁ => (if i ≤ d ∧ j ≤ d then 1 else 0) *
      ((if i = 0 ∧ j = 0 then 0 else
          ((2 : ℝ) ^ (7 * d * (i + j)))⁻¹ * (2 : ℝ) ^ (4 * i ^ 2 + 4 * j ^ 2)) *
        (if bcond X i j V₁ W₁ then (1 : ℝ) else 0)))
  rw [h2]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [show (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
        (if i ≤ d ∧ j ≤ d then 1 else 0) *
          ((if i = 0 ∧ j = 0 then 0 else
              ((2 : ℝ) ^ (7 * d * (i + j)))⁻¹ * (2 : ℝ) ^ (4 * i ^ 2 + 4 * j ^ 2)) *
            (if bcond X i j V₁ W₁ then (1 : ℝ) else 0)))
      = ∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
          ((if i ≤ d ∧ j ≤ d then 1 else 0) *
            (if i = 0 ∧ j = 0 then 0 else
              ((2 : ℝ) ^ (7 * d * (i + j)))⁻¹ * (2 : ℝ) ^ (4 * i ^ 2 + 4 * j ^ 2))) *
          (if bcond X i j V₁ W₁ then (1 : ℝ) else 0) from by
        refine Finset.sum_congr rfl (fun V₁ _ => Finset.sum_congr rfl (fun W₁ _ => by ring))]
  exact sum_sum_mul_const _ _

/-- `fcoeff f Y = 0` for a function of degree `≤ d` once `Y.rank > d`. -/
lemma fcoeff_eq_zero_of_rank_gt {m n d : ℕ} {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ}
    (hf : DegLe d f) {Y : Matrix (Fin n) (Fin m) 𝔽₂} (hY : d < Y.rank) : fcoeff f Y = 0 := by
  rw [fcoeff_eq, hf Y hY, mul_zero]

/-- `F2Sum X f` vanishes once `X.rank > 2d` for a function of degree `≤ d`. -/
lemma F2Sum_eq_zero_of_rank_gt {m n d : ℕ} {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ}
    (hf : DegLe d f) {X : Matrix (Fin n) (Fin m) 𝔽₂} (hX : 2 * d < X.rank) :
    F2Sum X f = 0 := by
  rw [F2Sum]
  refine Finset.sum_eq_zero (fun Y _ => ?_)
  by_cases h : IsF2BS X Y (X + Y)
  · rw [if_pos h]
    by_cases hY : Y.rank ≤ d
    · have hsum : Y + (X + Y) = X := by
        rw [← add_assoc, add_comm Y X, add_assoc, mtx_add_self, add_zero]
      have hle := Commons.LinearAlgebra.Matrix.rank_add_le Y (X + Y)
      rw [hsum] at hle
      have hXY : d < (X + Y).rank := by omega
      rw [fcoeff_eq_zero_of_rank_gt hf hXY, mul_zero]
    · rw [fcoeff_eq_zero_of_rank_gt hf (by omega), zero_mul]
  · rw [if_neg h]

/-- Nonnegativity of `F2RHS`. -/
lemma F2RHS_nonneg (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ)
    (X : Matrix (Fin n) (Fin m) 𝔽₂) : 0 ≤ F2RHS d f X := by
  rw [F2RHS]
  refine Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => ?_))
  refine mul_nonneg (by positivity) ?_
  refine Finset.sum_nonneg (fun V₁ _ => Finset.sum_nonneg (fun W₁ _ => ?_))
  by_cases h : bcond X i j V₁ W₁
  · rw [if_pos h]; positivity
  · rw [if_neg h]

/-- A double sum with the `[i ≤ d ∧ j ≤ d]` guard is at most the unrestricted double sum over
`range (d+1) × range (d+1)`. -/
lemma sum_sum_ite_le {f : ℕ → ℕ → ℝ} (hf : ∀ i j, 0 ≤ f i j) (N M d : ℕ) :
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range M,
        (if i ≤ d ∧ j ≤ d then 1 else 0) * f i j)
      ≤ ∑ i ∈ Finset.range (d + 1), ∑ j ∈ Finset.range (d + 1), f i j := by
  have h1 : (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range M,
        (if i ≤ d ∧ j ≤ d then 1 else 0) * f i j)
      = ∑ i ∈ Finset.range N, (if i ≤ d then 1 else 0) *
          (∑ j ∈ Finset.range M, (if j ≤ d then 1 else 0) * f i j) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases hi : i ≤ d <;> by_cases hj : j ≤ d <;> simp [hi, hj]
  rw [h1]
  have h2 : (∑ i ∈ Finset.range N, (if i ≤ d then 1 else 0) *
        (∑ j ∈ Finset.range M, (if j ≤ d then 1 else 0) * f i j))
      ≤ ∑ i ∈ Finset.range N, (if i ≤ d then 1 else 0) *
        (∑ j ∈ Finset.range (d + 1), f i j) := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    by_cases hi : i ≤ d
    · simp only [if_pos hi, one_mul]
      have hconv : (∑ j ∈ Finset.range M, (if j ≤ d then 1 else 0) * f i j)
          = ∑ j ∈ Finset.range M, (if j ≤ d then f i j else 0) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        by_cases hj : j ≤ d
        · simp only [if_pos hj, one_mul]
        · simp only [if_neg hj, zero_mul]
      rw [hconv]
      exact sum_range_ite_le (fun j => hf i j) M d
    · simp [hi]
  refine le_trans h2 ?_
  have h3 : ∀ i, 0 ≤ ∑ j ∈ Finset.range (d + 1), f i j :=
    fun i => Finset.sum_nonneg (fun j _ => hf i j)
  have h4 := sum_range_ite_le h3 N d
  refine le_trans (le_of_eq ?_) h4
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hi : i ≤ d
  · simp only [if_pos hi, one_mul]
  · simp [hi]

/-- **The arithmetic bound of `lem:F2` under the sole hypothesis `rank X ≤ 2 d`**:
the degree-restricted Cauchy--Schwarz factor is at most `1`. -/
lemma sum_bF2_le_one {m n d : ℕ} (X : Matrix (Fin n) (Fin m) 𝔽₂) (hX : X.rank ≤ 2 * d) :
    (∑ k : BSIdx m n, bF2 d X k) ≤ 1 := by
  rw [sum_bF2_eq]
  have hstep : ∀ i j, j ≤ m →
      (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
        (if bcond X i j V₁ W₁ then (1 : ℝ) else 0))
      = (Commons.Combinatorics.QBinomial.gb X.rank i : ℝ) *
        (Commons.Combinatorics.QBinomial.gb X.rank j : ℝ) :=
    fun i j hj => card_cond_eq X i j hj
  have h1 : (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
        ((if i ≤ d ∧ j ≤ d then 1 else 0) *
          (if i = 0 ∧ j = 0 then 0 else
            ((2 : ℝ) ^ (7 * d * (i + j)))⁻¹ * (2 : ℝ) ^ (4 * i ^ 2 + 4 * j ^ 2))) *
          (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
            (if bcond X i j V₁ W₁ then (1 : ℝ) else 0)))
      = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
          (if i ≤ d ∧ j ≤ d then 1 else 0) *
            ((if i = 0 ∧ j = 0 then 0 else
              ((2 : ℝ) ^ (7 * d * (i + j)))⁻¹ * (2 : ℝ) ^ (4 * i ^ 2 + 4 * j ^ 2)) *
              ((Commons.Combinatorics.QBinomial.gb X.rank i : ℝ) *
                (Commons.Combinatorics.QBinomial.gb X.rank j : ℝ))) := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j hj => ?_))
    have hjm : j ≤ m := by simp only [Finset.mem_range] at hj; omega
    rw [hstep i j hjm]
    ring
  rw [h1]
  have hgc : ∀ i j, 0 ≤
      (if i = 0 ∧ j = 0 then 0 else
        ((2 : ℝ) ^ (7 * d * (i + j)))⁻¹ * (2 : ℝ) ^ (4 * i ^ 2 + 4 * j ^ 2)) *
      ((Commons.Combinatorics.QBinomial.gb X.rank i : ℝ) *
        (Commons.Combinatorics.QBinomial.gb X.rank j : ℝ)) := by
    intro i j
    by_cases h : i = 0 ∧ j = 0
    · simp [h]
    · simp only [if_neg h]; positivity
  refine le_trans (sum_sum_ite_le hgc (n + 1) (m + 1) d) ?_
  have harith := Commons.Combinatorics.QBinomial.gb_pair_pow_sum_lt_one_of_le_two_mul d X.rank hX
  have hEq : (∑ i ∈ Finset.range (d + 1), ∑ j ∈ Finset.range (d + 1),
        (if i = 0 ∧ j = 0 then 0 else
          ((2 : ℝ) ^ (7 * d * (i + j)))⁻¹ * (2 : ℝ) ^ (4 * i ^ 2 + 4 * j ^ 2)) *
        ((Commons.Combinatorics.QBinomial.gb X.rank i : ℝ) *
          (Commons.Combinatorics.QBinomial.gb X.rank j : ℝ)))
      = ∑ i ∈ Finset.range (d + 1), ∑ j ∈ Finset.range (d + 1),
          (if i = 0 ∧ j = 0 then 0 else
            (Commons.Combinatorics.QBinomial.gb X.rank i : ℝ) *
              (Commons.Combinatorics.QBinomial.gb X.rank j : ℝ) *
              ((2 : ℝ) ^ (7 * d * (i + j)))⁻¹ * (2 : ℝ) ^ (4 * i ^ 2 + 4 * j ^ 2)) := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    by_cases h : i = 0 ∧ j = 0
    · simp only [if_pos h, zero_mul]
    · simp only [if_neg h]; ring
  rw [hEq]
  exact le_of_lt harith

/-- **`lem:F2` for a function of degree `≤ d`, in the sharp range `X.rank ≤ 2 d`.** -/
theorem F2_sq_le_degLe {m n d : ℕ} (X : Matrix (Fin n) (Fin m) 𝔽₂) (hX : X.rank ≤ 2 * d)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (hf : DegLe d f) :
    ‖F2Sum X f‖ ^ 2 ≤ F2RHS d f X := by
  have hA : ‖F2Sum X f‖ ≤ ∑ k : BSIdx m n, aF X f k := by
    rw [sum_aF_eq]; exact F2_helper X f
  have hcs := Commons.Analysis.Inequalities.sum_sq_le_mul_sum_of_pointwise
    (aF X f) (bF2 d X) (cF d X f) (fun k => bF2_nonneg d X k) (fun k => cF_nonneg d X f k)
    (fun k => aF_sq_le_bF2 d X f hf k)
  have hb1 : (∑ k : BSIdx m n, bF2 d X k) ≤ 1 := sum_bF2_le_one X hX
  have hcnn : 0 ≤ ∑ k : BSIdx m n, cF d X f k :=
    Finset.sum_nonneg fun k _ => cF_nonneg d X f k
  calc ‖F2Sum X f‖ ^ 2
      ≤ (∑ k : BSIdx m n, aF X f k) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hA 2
    _ ≤ (∑ k : BSIdx m n, bF2 d X k) * (∑ k : BSIdx m n, cF d X f k) := hcs
    _ ≤ 1 * (∑ k : BSIdx m n, cF d X f k) := mul_le_mul_of_nonneg_right hb1 hcnn
    _ = ∑ k : BSIdx m n, cF d X f k := one_mul _
    _ ≤ F2RHS d f X := le_of_eq (sum_cF_eq d X f)

/-- **The second display of `lem:F2`**: summing `F2_sq_le_degLe` over all `X` and dropping the
constraint `V₁ ≤ Im X`, `ker X ≤ W₁` (using Parseval for the normalised Fourier transform)
gives the paper's bound. -/
theorem F2_sq_sum_le {m n : ℕ} (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (hf : DegLe d f) :
    (∑ X : Matrix (Fin n) (Fin m) 𝔽₂, ‖F2Sum X f‖ ^ 2) ≤
      ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
        (if i = 0 ∧ j = 0 then 0 else (2 : ℝ) ^ (7 * d * (i + j))) *
          (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
            (if Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j
              then l4q (Lup V₁ (Ldown W₁ f)) else 0)) := by
  have hA : (∑ X : Matrix (Fin n) (Fin m) 𝔽₂, ‖F2Sum X f‖ ^ 2)
      ≤ ∑ X : Matrix (Fin n) (Fin m) 𝔽₂, F2RHS d f X := by
    refine Finset.sum_le_sum (fun X _ => ?_)
    by_cases hX : X.rank ≤ 2 * d
    · exact F2_sq_le_degLe X hX f hf
    · rw [F2Sum_eq_zero_of_rank_gt hf (by omega), norm_zero]
      norm_num
      exact F2RHS_nonneg d f X
  refine le_trans hA ?_
  have e1 : (∑ X : Matrix (Fin n) (Fin m) 𝔽₂, F2RHS d f X)
      = ∑ X : Matrix (Fin n) (Fin m) 𝔽₂, ∑ i ∈ Finset.range (n + 1),
          ∑ j ∈ Finset.range (m + 1),
            (if i = 0 ∧ j = 0 then 0 else (2 : ℝ) ^ (7 * d * (i + j))) *
              (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
                (if bcond X i j V₁ W₁ then ‖fcoeff (Lap2 V₁ W₁ f) X‖ ^ 2 else 0)) := by
    refine Finset.sum_congr rfl (fun X _ => rfl)
  rw [e1]
  have e2 : (∑ X : Matrix (Fin n) (Fin m) 𝔽₂, ∑ i ∈ Finset.range (n + 1),
        ∑ j ∈ Finset.range (m + 1),
          (if i = 0 ∧ j = 0 then 0 else (2 : ℝ) ^ (7 * d * (i + j))) *
            (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
              (if bcond X i j V₁ W₁ then ‖fcoeff (Lap2 V₁ W₁ f) X‖ ^ 2 else 0)))
      = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
          (if i = 0 ∧ j = 0 then 0 else (2 : ℝ) ^ (7 * d * (i + j))) *
            ∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
              (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
                (if bcond X i j V₁ W₁ then ‖fcoeff (Lap2 V₁ W₁ f) X‖ ^ 2 else 0)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
  rw [e2]
  refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have e3 : (∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
        (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
          (if bcond X i j V₁ W₁ then ‖fcoeff (Lap2 V₁ W₁ f) X‖ ^ 2 else 0)))
      = ∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
          ∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
            (if bcond X i j V₁ W₁ then ‖fcoeff (Lap2 V₁ W₁ f) X‖ ^ 2 else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun V₁ _ => ?_)
    rw [Finset.sum_comm]
  rw [e3]
  refine Finset.sum_le_sum (fun V₁ _ => Finset.sum_le_sum (fun W₁ _ => ?_))
  by_cases hd : Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j
  · rw [if_pos hd]
    have hpt : (∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
          (if bcond X i j V₁ W₁ then ‖fcoeff (Lap2 V₁ W₁ f) X‖ ^ 2 else 0))
        ≤ ∑ X : Matrix (Fin n) (Fin m) 𝔽₂, ‖fcoeff (Lap2 V₁ W₁ f) X‖ ^ 2 := by
      refine Finset.sum_le_sum (fun X _ => ?_)
      by_cases hb : bcond X i j V₁ W₁
      · rw [if_pos hb]
      · rw [if_neg hb]; positivity
    refine hpt.trans ?_
    rw [sum_normSq_fcoeff]
    exact le_of_eq (l2sq_mul_self (Lup V₁ (Ldown W₁ f)))
  · rw [if_neg hd]
    refine le_of_eq (Finset.sum_eq_zero (fun X _ => ?_))
    rw [if_neg (fun hc => hd ⟨hc.2.2.1, hc.2.2.2⟩)]

end

end Submission.Grassmann
