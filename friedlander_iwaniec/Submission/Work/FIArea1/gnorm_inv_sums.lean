/-
# `Submission.Work.FIArea1.gnorm_inv_sums`

Two elementary reciprocal estimates for the Gaussian box `gBox R` that the Area-1 part of
Friedlander–Iwaniec, *The polynomial X² + Y⁴ captures its primes*, needs:

* `∑_{d ∈ gBox R, gnorm d > P} (gnorm d)^{-2} ≤ C/P`, the two-dimensional tail of `Σ 1/|z|⁴`; and
* `∑_{d ∈ gBox R} (gnorm d)^{-1} ≤ C (1 + log(R+2))`, the logarithmic divergence of `Σ 1/|z|²`
  over a square box.

Route.  A sum over `gBox R` is a double sum over the coordinate box `[-R,R]²`; the reflection
`(a,b) ↦ (|a|,|b|)` turns that into (at most) four copies of a sum over the quadrant `[0,R]²`
(`pair_natAbs_le`); the quadrant sums are estimated by explicit telescoping bounds
(`Σ_{n≥K} 1/n³ ≤ 2/K²`, `Σ_{n≥K} 1/n² ≤ 2/K`) together with the diagonal/axis decomposition
of the pair sums (`sum_inv_sq_quad_le`, `sum_inv_quad_le`, `sum_Icc_axis_pow4_le`).
-/
import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea2.hits_card_le
import Submission.Work.FIArea1.pair_natAbs_le
import Submission.Work.FIArea1.sum_inv_quad_le
import Submission.Work.FIArea1.sum_inv_sq_quad_le

namespace Work.FIArea1

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The box `gBox R` in coordinates -/

/-- `gnorm` of a coordinate pair, as a real number: `|a + bi|² = a² + b²`. -/
lemma gnorm_mk_cast (a b : ℤ) :
    ((Work.FIPlan.gnorm (⟨a, b⟩ : GaussianInt) : ℕ) : ℝ)
      = (a.natAbs : ℝ) ^ 2 + (b.natAbs : ℝ) ^ 2 := by
  rw [gnorm_coords]
  push_cast
  ring

/-- The "`gnorm d > P`" condition for `d = a + bi`, in real coordinates. -/
lemma gnorm_mk_iff (P : ℕ) (a b : ℤ) :
    (P < Work.FIPlan.gnorm (⟨a, b⟩ : GaussianInt))
      ↔ ((P : ℝ) < (a.natAbs : ℝ) ^ 2 + (b.natAbs : ℝ) ^ 2) := by
  rw [← gnorm_mk_cast a b]
  exact Nat.cast_lt.symm

/-- A sum over the Gaussian box `gBox R` is a double sum over the coordinate box. -/
lemma sum_gBox_eq (R : ℤ) (f : GaussianInt → ℝ) :
    ∑ z ∈ Work.FIPlan.gBox R, f z
      = ∑ a ∈ Finset.Icc (-R) R, ∑ b ∈ Finset.Icc (-R) R, f (⟨a, b⟩ : GaussianInt) := by
  rw [Work.FIPlan.gBox, Finset.sum_image Work.FIPlan.gaussMk_injective.injOn,
    Finset.product_eq_sprod, Finset.sum_product]

/-! ## 2. Elementary bounds for sums over `ℕ` -/

/-- `Finset.Icc 0 N = {0} ∪ Finset.Icc 1 N`. -/
lemma Icc_zero_eq_insert (N : ℕ) : Finset.Icc 0 N = insert 0 (Finset.Icc 1 N) := by
  ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega

/-- Telescoping: `∑_{n=K}^{N} (f n - f (n+1)) = f K - f (N+1)`. -/
lemma sum_Icc_sub_telescope (K N : ℕ) (h : K ≤ N) (f : ℕ → ℝ) :
    ∑ n ∈ Finset.Icc K N, (f n - f (n + 1)) = f K - f (N + 1) := by
  have htel := Finset.sum_Icc_sub h (fun i : ℕ => - f i)
  have h1 : (∑ i ∈ Finset.Icc K N, (-f (i + 1) - -f i))
      = ∑ i ∈ Finset.Icc K N, (f i - f (i + 1)) := by
    apply Finset.sum_congr rfl; intro x _; ring
  rw [← h1, htel]
  ring

/-- The square tail: `∑_{n=K}^{N} 1/n² ≤ 2/K`. -/
lemma sum_Icc_inv_sq_le_two_div (K N : ℕ) (hK : 1 ≤ K) :
    (∑ n ∈ Finset.Icc K N, (((n : ℝ) ^ 2)⁻¹)) ≤ 2 / (K : ℝ) := by
  have hK0 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  rcases Nat.lt_or_ge N K with hNK | hKN
  · rw [Finset.Icc_eq_empty (by omega : ¬ K ≤ N)]
    simp only [Finset.sum_empty]
    positivity
  · have hset : Finset.Icc K N = insert K (Finset.Ioc K N) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]; omega
    rw [hset, Finset.sum_insert (by simp [Finset.mem_Ioc])]
    have h1 : (∑ i ∈ Finset.Ioc K N, ((i : ℝ) ^ 2)⁻¹) ≤ (K : ℝ)⁻¹ - (N : ℝ)⁻¹ :=
      sum_Ioc_inv_sq_le_sub (by omega) hKN
    have h2 : ((K : ℝ) ^ 2)⁻¹ ≤ (K : ℝ)⁻¹ := by
      rw [inv_le_inv₀ (by positivity : (0 : ℝ) < (K : ℝ) ^ 2) hK0]
      nlinarith
    have h3 : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
    rw [div_eq_mul_inv]
    linarith

/-- `∑_{n=1}^{N} 1/n² ≤ 2`. -/
lemma sum_Icc_inv_sq_le_two (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (((n : ℝ) ^ 2)⁻¹)) ≤ 2 := by
  have h := sum_Icc_inv_sq_le_two_div 1 N le_rfl
  simpa using h

/-- The elementary step of the cube telescoping: `1/n³ ≤ 2(1/n² - 1/(n+1)²)` for `n ≥ 1`. -/
lemma inv_cube_le (n : ℕ) (hn : 1 ≤ n) :
    ((n : ℝ)⁻¹) ^ 3 ≤ 2 * (((n : ℝ) ^ 2)⁻¹ - (((n : ℝ) + 1) ^ 2)⁻¹) := by
  have hx1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < (n : ℝ) := by linarith
  rw [show 2 * (((n : ℝ) ^ 2)⁻¹ - (((n : ℝ) + 1) ^ 2)⁻¹)
      = 2 * (2 * (n : ℝ) + 1) / ((n : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 2) by
        field_simp
        ring]
  rw [le_div_iff₀ (by positivity)]
  rw [show ((n : ℝ)⁻¹) ^ 3 * ((n : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 2) = ((n : ℝ) + 1) ^ 2 / (n : ℝ) by
        field_simp]
  rw [div_le_iff₀ hx0]
  nlinarith [sq_nonneg ((n : ℝ))]

/-- The cube tail: `∑_{n=K}^{N} 1/n³ ≤ 2/K²`. -/
lemma sum_Icc_inv_cube_le (K N : ℕ) (hK : 1 ≤ K) :
    (∑ n ∈ Finset.Icc K N, ((n : ℝ)⁻¹) ^ 3) ≤ 2 / (K : ℝ) ^ 2 := by
  have hK0 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  rcases Nat.lt_or_ge N K with hNK | hKN
  · rw [Finset.Icc_eq_empty (by omega : ¬ K ≤ N)]
    simp only [Finset.sum_empty]
    positivity
  · have htel : (∑ n ∈ Finset.Icc K N, (((n : ℝ) ^ 2)⁻¹ - (((n : ℝ) + 1) ^ 2)⁻¹))
        = ((K : ℝ) ^ 2)⁻¹ - (((N : ℝ) + 1) ^ 2)⁻¹ := by
      have key : (∑ n ∈ Finset.Icc K N, (((n : ℝ) ^ 2)⁻¹ - (((n : ℝ) + 1) ^ 2)⁻¹))
          = ∑ n ∈ Finset.Icc K N, ((fun i : ℕ => (((i : ℝ) ^ 2)⁻¹)) n
              - (fun i : ℕ => (((i : ℝ) ^ 2)⁻¹)) (n + 1)) := by
        apply Finset.sum_congr rfl
        intro n _
        push_cast
        ring
      rw [key, sum_Icc_sub_telescope K N hKN (fun i => (((i : ℝ) ^ 2)⁻¹))]
      push_cast
      ring
    calc ∑ n ∈ Finset.Icc K N, ((n : ℝ)⁻¹) ^ 3
        ≤ ∑ n ∈ Finset.Icc K N, 2 * (((n : ℝ) ^ 2)⁻¹ - (((n : ℝ) + 1) ^ 2)⁻¹) := by
          apply Finset.sum_le_sum
          intro n hn
          exact inv_cube_le n (by rw [Finset.mem_Icc] at hn; omega)
      _ = 2 * (∑ n ∈ Finset.Icc K N, (((n : ℝ) ^ 2)⁻¹ - (((n : ℝ) + 1) ^ 2)⁻¹)) := by
          rw [Finset.mul_sum]
      _ = 2 * (((K : ℝ) ^ 2)⁻¹ - (((N : ℝ) + 1) ^ 2)⁻¹) := by rw [htel]
      _ ≤ 2 / (K : ℝ) ^ 2 := by
          have h1 : (0 : ℝ) ≤ (((N : ℝ) + 1) ^ 2)⁻¹ := by positivity
          have h3 : ((K : ℝ) ^ 2)⁻¹ ≤ (K : ℝ)⁻¹ := by
            rw [inv_le_inv₀ (by positivity : (0 : ℝ) < (K : ℝ) ^ 2) hK0]
            nlinarith
          rw [div_eq_mul_inv]
          linarith

/-- The "axis" sum of the fourth powers: `∑_{n ≤ N, n² > P} 1/n⁴ ≤ 4/P`. -/
lemma sum_Icc_axis_pow4_le (P N : ℕ) (hP : 1 ≤ P) :
    (∑ n ∈ Finset.Icc 1 N, (if (P : ℝ) < (n : ℝ) ^ 2 then (((n : ℝ) ^ 2)⁻¹ ^ 2) else 0))
      ≤ 4 / (P : ℝ) := by
  set K : ℕ := Nat.sqrt P + 1 with hKdef
  have hKpos : 1 ≤ K := by omega
  have hKsq : (P : ℝ) < (K : ℝ) ^ 2 := by
    have h1 : P < K ^ 2 := by simpa [hKdef, pow_two] using Nat.lt_succ_sqrt P
    exact_mod_cast h1
  have hP0 : (0 : ℝ) < (P : ℝ) := by
    have : (1 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
    linarith
  have hsub : (Finset.Icc 1 N).filter (fun n : ℕ => (P : ℝ) < (n : ℝ) ^ 2)
      ⊆ Finset.Icc K N := by
    intro n hn
    simp only [Finset.mem_filter] at hn
    obtain ⟨hn1, hn2⟩ := hn
    have hn1' : 1 ≤ n ∧ n ≤ N := Finset.mem_Icc.mp hn1
    have hlt : Nat.sqrt P < n := by
      by_contra hcon
      push Not at hcon
      have h2 : n ^ 2 ≤ P := by simpa [pow_two] using Nat.le_sqrt.mp hcon
      have h3 : (n : ℝ) ^ 2 ≤ (P : ℝ) := by exact_mod_cast h2
      linarith
    exact Finset.mem_Icc.mpr ⟨by omega, hn1'.2⟩
  calc (∑ n ∈ Finset.Icc 1 N, (if (P : ℝ) < (n : ℝ) ^ 2 then (((n : ℝ) ^ 2)⁻¹ ^ 2) else 0))
      = ∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => (P : ℝ) < (n : ℝ) ^ 2),
          (((n : ℝ) ^ 2)⁻¹ ^ 2) :=
        (Finset.sum_filter (fun n : ℕ => (P : ℝ) < (n : ℝ) ^ 2)
          (fun n => (((n : ℝ) ^ 2)⁻¹ ^ 2))).symm
    _ ≤ ∑ n ∈ Finset.Icc K N, (((n : ℝ) ^ 2)⁻¹ ^ 2) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)
    _ ≤ ∑ n ∈ Finset.Icc K N, ((K : ℝ) ^ 2)⁻¹ * (((n : ℝ) ^ 2)⁻¹) := by
        apply Finset.sum_le_sum; intro n hn
        rw [Finset.mem_Icc] at hn
        have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
        have hKle : (K : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
        have hK2 : (0 : ℝ) < (K : ℝ) ^ 2 := by positivity
        have hn2 : (0 : ℝ) ≤ ((n : ℝ) ^ 2)⁻¹ := by positivity
        have hinv : ((n : ℝ) ^ 2)⁻¹ ≤ ((K : ℝ) ^ 2)⁻¹ := by
          rw [inv_le_inv₀ (by nlinarith : (0 : ℝ) < (n : ℝ) ^ 2) hK2]
          nlinarith
        calc (((n : ℝ) ^ 2)⁻¹ ^ 2) = ((n : ℝ) ^ 2)⁻¹ * ((n : ℝ) ^ 2)⁻¹ := by ring
          _ ≤ ((K : ℝ) ^ 2)⁻¹ * ((n : ℝ) ^ 2)⁻¹ := by nlinarith
    _ = ((K : ℝ) ^ 2)⁻¹ * (∑ n ∈ Finset.Icc K N, (((n : ℝ) ^ 2)⁻¹)) := by rw [Finset.mul_sum]
    _ ≤ ((K : ℝ) ^ 2)⁻¹ * (2 / (K : ℝ)) := by
        have h5 := sum_Icc_inv_sq_le_two_div K N hKpos
        have h6 : (0 : ℝ) ≤ ((K : ℝ) ^ 2)⁻¹ := by positivity
        nlinarith
    _ ≤ 4 / (P : ℝ) := by
        have hK0 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
        have h1 : ((K : ℝ) ^ 2)⁻¹ ≤ ((P : ℝ))⁻¹ := by
          rw [inv_le_inv₀ (by positivity : (0 : ℝ) < (K : ℝ) ^ 2) hP0]
          linarith
        have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hKpos
        have h2 : 2 / (K : ℝ) ≤ 2 := by
          rw [div_le_iff₀ hK0]; linarith
        calc ((K : ℝ) ^ 2)⁻¹ * (2 / (K : ℝ)) ≤ ((P : ℝ))⁻¹ * 2 := by
              apply mul_le_mul h1 h2 (by positivity) (by positivity)
          _ = 2 / (P : ℝ) := by ring
          _ ≤ 4 / (P : ℝ) :=
              div_le_div_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 4) (le_of_lt hP0)

/-- Splitting a double sum over `[0,N]²` into its two axes and the open quadrant. -/
lemma sum_Icc_zero_split (N : ℕ) (h : ℕ → ℕ → ℝ) :
    (∑ m ∈ Finset.Icc 0 N, ∑ n ∈ Finset.Icc 0 N, h m n)
      = (∑ n ∈ Finset.Icc 0 N, h 0 n) + (∑ m ∈ Finset.Icc 1 N, h m 0)
        + (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, h m n) := by
  have hsplit : ∀ m : ℕ,
      (∑ n ∈ Finset.Icc 0 N, h m n) = h m 0 + ∑ n ∈ Finset.Icc 1 N, h m n := by
    intro m
    rw [Icc_zero_eq_insert N, Finset.sum_insert (by simp [Finset.mem_Icc])]
  have h1 : (∑ m ∈ Finset.Icc 0 N, ∑ n ∈ Finset.Icc 0 N, h m n)
      = ∑ m ∈ Finset.Icc 0 N, (h m 0 + ∑ n ∈ Finset.Icc 1 N, h m n) :=
    Finset.sum_congr rfl (fun m _ => hsplit m)
  rw [h1, Finset.sum_add_distrib, hsplit 0, Icc_zero_eq_insert N]
  rw [Finset.sum_insert (by simp [Finset.mem_Icc])]
  rw [Finset.sum_insert (by simp [Finset.mem_Icc])]
  ring

/-! ## 3. The two model quadrant sums -/

/-- The summand of the first (squared) estimate on the quadrant. -/
private def Fsq (P : ℕ) (m n : ℕ) : ℝ :=
  if (P : ℝ) < (m : ℝ) ^ 2 + (n : ℝ) ^ 2 then ((((m : ℝ) ^ 2 + (n : ℝ) ^ 2)⁻¹) ^ 2) else 0

/-- The summand of the second (reciprocal) estimate on the quadrant. -/
private def Frcp (m n : ℕ) : ℝ := ((m : ℝ) ^ 2 + (n : ℝ) ^ 2)⁻¹

private lemma Fsq_nonneg (P m n : ℕ) : 0 ≤ Fsq P m n := by
  unfold Fsq; split <;> positivity

private lemma Fsq_zero_zero (P : ℕ) : Fsq P 0 0 = 0 := by
  have h : ¬ ((P : ℝ) < (0 : ℝ)) := by
    have : (0 : ℝ) ≤ (P : ℝ) := Nat.cast_nonneg P
    linarith
  simp [Fsq, h]

private lemma Fsq_zero_left (P n : ℕ) :
    Fsq P 0 n = (if (P : ℝ) < (n : ℝ) ^ 2 then (((n : ℝ) ^ 2)⁻¹ ^ 2) else 0) := by
  rw [Fsq]; simp

private lemma Fsq_zero_right (P n : ℕ) :
    Fsq P n 0 = (if (P : ℝ) < (n : ℝ) ^ 2 then (((n : ℝ) ^ 2)⁻¹ ^ 2) else 0) := by
  rw [Fsq]; simp

private lemma Frcp_nonneg (m n : ℕ) : 0 ≤ Frcp m n := by
  unfold Frcp; positivity

private lemma Frcp_zero_zero : Frcp 0 0 = 0 := by rw [Frcp]; simp

private lemma Frcp_zero_left (n : ℕ) : Frcp 0 n = (((n : ℝ) ^ 2)⁻¹) := by rw [Frcp]; simp

private lemma Frcp_zero_right (n : ℕ) : Frcp n 0 = (((n : ℝ) ^ 2)⁻¹) := by rw [Frcp]; simp

/-! ## 4. The main theorem -/

attribute [local instance] Classical.propDecidable

theorem gnorm_inv_sums :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℤ) (P : ℕ), 0 ≤ R → 1 ≤ P →
      (∑ d ∈ (Work.FIPlan.gBox R).filter (fun d => P < Work.FIPlan.gnorm d),
          ((Work.FIPlan.gnorm d : ℝ))⁻¹ ^ 2) ≤ C / (P : ℝ)
      ∧ (∑ d ∈ Work.FIPlan.gBox R, ((Work.FIPlan.gnorm d : ℝ))⁻¹)
          ≤ C * (1 + Real.log ((R : ℝ) + 2)) := by
  refine ⟨100, by norm_num, ?_⟩
  intro R P hR hP
  have hP0 : (0 : ℝ) < (P : ℝ) := by
    have : (1 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
    linarith
  constructor
  · -- first conjunct: the squared reciprocal sum
    have hstep : (∑ d ∈ (Work.FIPlan.gBox R).filter (fun d => P < Work.FIPlan.gnorm d),
          ((Work.FIPlan.gnorm d : ℝ))⁻¹ ^ 2)
        = ∑ a ∈ Finset.Icc (-R) R, ∑ b ∈ Finset.Icc (-R) R, Fsq P a.natAbs b.natAbs := by
      rw [Finset.sum_filter, sum_gBox_eq]
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro b _
      simp only [Fsq, gnorm_mk_iff P a b, gnorm_mk_cast a b]
    rw [hstep]
    -- the quadrant estimate
    have hN : (∑ m ∈ Finset.Icc 0 R.natAbs, ∑ n ∈ Finset.Icc 0 R.natAbs, Fsq P m n)
        ≤ 16 / (P : ℝ) := by
      rw [sum_Icc_zero_split]
      have hrow : (∑ n ∈ Finset.Icc 0 R.natAbs, Fsq P 0 n) ≤ 4 / (P : ℝ) := by
        rw [Icc_zero_eq_insert, Finset.sum_insert (by simp [Finset.mem_Icc]),
          Fsq_zero_zero P, zero_add]
        refine le_trans (le_of_eq ?_) (sum_Icc_axis_pow4_le P R.natAbs hP)
        apply Finset.sum_congr rfl; intro n _
        exact Fsq_zero_left P n
      have hcol : (∑ m ∈ Finset.Icc 1 R.natAbs, Fsq P m 0) ≤ 4 / (P : ℝ) := by
        refine le_trans (le_of_eq ?_) (sum_Icc_axis_pow4_le P R.natAbs hP)
        apply Finset.sum_congr rfl; intro n _
        exact Fsq_zero_right P n
      have hcore : (∑ m ∈ Finset.Icc 1 R.natAbs, ∑ n ∈ Finset.Icc 1 R.natAbs, Fsq P m n)
          ≤ 8 / (P : ℝ) := sum_inv_sq_quad_le P R.natAbs hP
      have harith : (4 : ℝ) / (P : ℝ) + 4 / (P : ℝ) + 8 / (P : ℝ) = 16 / (P : ℝ) := by ring
      linarith
    refine le_trans (pair_natAbs_le R hR (Fsq P) (Fsq_nonneg P)) ?_
    have hfin : (4 : ℝ) * (∑ m ∈ Finset.Icc 0 R.natAbs, ∑ n ∈ Finset.Icc 0 R.natAbs, Fsq P m n)
        ≤ 100 / (P : ℝ) := by
      have h4 : (4 : ℝ) * (16 / (P : ℝ)) = 64 / (P : ℝ) := by ring
      have h5 : (64 : ℝ) / (P : ℝ) ≤ 100 / (P : ℝ) :=
        div_le_div_of_nonneg_right (by norm_num : (64 : ℝ) ≤ 100) (le_of_lt hP0)
      linarith [hN]
    exact hfin
  · -- second conjunct: the reciprocal sum
    have hstep : (∑ d ∈ Work.FIPlan.gBox R, ((Work.FIPlan.gnorm d : ℝ))⁻¹)
        = ∑ a ∈ Finset.Icc (-R) R, ∑ b ∈ Finset.Icc (-R) R, Frcp a.natAbs b.natAbs := by
      rw [sum_gBox_eq]
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro b _
      rw [gnorm_mk_cast a b, Frcp]
    rw [hstep]
    have hN : (∑ m ∈ Finset.Icc 0 R.natAbs, ∑ n ∈ Finset.Icc 0 R.natAbs, Frcp m n)
        ≤ 4 + 2 * (1 + Real.log (R.natAbs : ℝ)) := by
      rw [sum_Icc_zero_split]
      have hrow : (∑ n ∈ Finset.Icc 0 R.natAbs, Frcp 0 n) ≤ 2 := by
        rw [Icc_zero_eq_insert, Finset.sum_insert (by simp [Finset.mem_Icc]),
          Frcp_zero_zero, zero_add]
        refine le_trans (le_of_eq ?_) (sum_Icc_inv_sq_le_two R.natAbs)
        apply Finset.sum_congr rfl; intro n _
        exact Frcp_zero_left n
      have hcol : (∑ m ∈ Finset.Icc 1 R.natAbs, Frcp m 0) ≤ 2 := by
        refine le_trans (le_of_eq ?_) (sum_Icc_inv_sq_le_two R.natAbs)
        apply Finset.sum_congr rfl; intro n _
        exact Frcp_zero_right n
      have hcore : (∑ m ∈ Finset.Icc 1 R.natAbs, ∑ n ∈ Finset.Icc 1 R.natAbs, Frcp m n)
          ≤ 2 * (1 + Real.log (R.natAbs : ℝ)) := sum_inv_quad_le R.natAbs
      linarith
    refine le_trans (pair_natAbs_le R hR Frcp Frcp_nonneg) ?_
    have hcast : ((R.natAbs : ℕ) : ℝ) = (R : ℝ) := by
      rw [← Int.cast_natCast (R.natAbs), Int.natAbs_of_nonneg hR]
    have hlog : Real.log (R.natAbs : ℝ) ≤ Real.log ((R : ℝ) + 2) := by
      rw [hcast]
      rcases eq_or_lt_of_le hR with h | h
      · rw [← h]
        simp only [Int.cast_zero, zero_add]
        rw [Real.log_zero]
        exact Real.log_nonneg (by norm_num)
      · exact Real.log_le_log (by exact_mod_cast h) (by linarith)
    have hlog2 : (0 : ℝ) ≤ Real.log ((R : ℝ) + 2) :=
      Real.log_nonneg (by linarith)
    nlinarith [hN, hlog, hlog2]

end

end Work.FIArea1
