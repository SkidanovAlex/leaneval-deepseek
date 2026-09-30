import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Polynomial Finset Real Complex

/-! ## Auxiliary lemmas for the abstract Bessel/large-sieve inequality -/

/-- **Cauchy–Schwarz for finite complex sums.**
`‖∑ aᵢ bᵢ‖² ≤ (∑ ‖aᵢ‖²)(∑ ‖bᵢ‖²)`. -/
private lemma bessel_cs_complex {ι : Type*} (s : Finset ι) (a b : ι → ℂ) :
    ‖∑ i ∈ s, a i * b i‖ ^ 2 ≤ (∑ i ∈ s, ‖a i‖ ^ 2) * (∑ i ∈ s, ‖b i‖ ^ 2) := by
  have h1 : ‖∑ i ∈ s, a i * b i‖ ≤ ∑ i ∈ s, ‖a i‖ * ‖b i‖ := by
    calc ‖∑ i ∈ s, a i * b i‖ ≤ ∑ i ∈ s, ‖a i * b i‖ := norm_sum_le _ _
      _ = ∑ i ∈ s, ‖a i‖ * ‖b i‖ := by simp
  have h3 : (∑ i ∈ s, ‖a i‖ * ‖b i‖) ^ 2 ≤ (∑ i ∈ s, ‖a i‖ ^ 2) * (∑ i ∈ s, ‖b i‖ ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖a i‖) (fun i => ‖b i‖)
  have h2 : 0 ≤ ∑ i ∈ s, ‖a i‖ * ‖b i‖ := Finset.sum_nonneg (fun i _ => by positivity)
  nlinarith [h1, h2, h3, norm_nonneg (∑ i ∈ s, a i * b i)]

/-- **Aggregate expansion bound.** For any complex sequences `w i`
and finite set `I`,
`∑_{n ∈ I} ‖∑_i wᵢ(n)‖² ≤ ∑_{i,j} ‖∑_{n ∈ I} wᵢ(n)·conj(wⱼ(n))‖`.

This is the heart of the argument: the square of the superposition is expanded into
the full double sum *before* taking absolute values, which is what allows the
pairwise-overlap correlations to appear on the right-hand side. -/
private lemma bessel_expand {N : ℕ} (I : Finset ℕ) (w : Fin N → ℕ → ℂ) :
    ∑ n ∈ I, ‖∑ i, w i n‖ ^ 2 ≤ ∑ i, ∑ j, ‖∑ n ∈ I, w i n * star (w j n)‖ := by
  have hterm : ∀ z : ℂ, z * star z = ((‖z‖^2 : ℝ) : ℂ) := by
    intro z; rw [Complex.sq_norm]; exact Complex.mul_conj z
  have hZreal : (∑ n ∈ I, (∑ i, w i n) * star (∑ i, w i n))
      = (((∑ n ∈ I, ‖∑ i, w i n‖ ^ 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl; intro n hn
    exact hterm _
  have hZsum : (∑ n ∈ I, (∑ i, w i n) * star (∑ i, w i n))
      = ∑ i, ∑ j, ∑ n ∈ I, w i n * star (w j n) := by
    have e1 : (∑ n ∈ I, (∑ i, w i n) * star (∑ i, w i n))
        = ∑ n ∈ I, ∑ i, ∑ j, w i n * star (w j n) := by
      apply Finset.sum_congr rfl; intro n hn
      rw [star_sum, Finset.sum_mul_sum]
    rw [e1]
    nth_rewrite 1 [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i hi
    rw [Finset.sum_comm]
  have hrI : (0:ℝ) ≤ ∑ n ∈ I, ‖∑ i, w i n‖ ^ 2 :=
    Finset.sum_nonneg (fun n _ => by positivity)
  have hnorm : ‖(∑ n ∈ I, (∑ i, w i n) * star (∑ i, w i n))‖
      = ∑ n ∈ I, ‖∑ i, w i n‖ ^ 2 := by
    rw [hZreal]
    have h : ‖(((∑ n ∈ I, ‖∑ i, w i n‖ ^ 2):ℝ):ℂ)‖^2 = (∑ n ∈ I, ‖∑ i, w i n‖^2)^2 := by
      rw [Complex.sq_norm, Complex.normSq_ofReal]; ring
    nlinarith [norm_nonneg (((∑ n ∈ I, ‖∑ i, w i n‖ ^ 2):ℝ):ℂ), hrI]
  rw [← hnorm, hZsum]
  calc ‖∑ i, ∑ j, ∑ n ∈ I, w i n * star (w j n)‖
      ≤ ∑ i, ‖∑ j, ∑ n ∈ I, w i n * star (w j n)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖∑ n ∈ I, w i n * star (w j n)‖ := by
        apply Finset.sum_le_sum; intro i hi; exact norm_sum_le _ _

/-- **Abstract Bessel/large-sieve inequality.** Let `I` be a finite set of naturals, `Is i ⊆ I`
finitely many subsets, `f` a sequence with `‖f n‖ ≤ 1`, `g i` arbitrary complex sequences and
`c i` coefficients of modulus `1`. Then the correlation of `f` against the superposition
`G n = Σ_i c i · 1_{Is i}(n) · g i n` is bounded by the total of pairwise overlap correlations:
`‖Σ_i c i · Σ_{n ∈ Is i} f n g i n‖² ≤ #I · Σ_{i,j} ‖Σ_{n ∈ Is i ∩ Is j} g i n · conj(g j n)‖`. -/
theorem large_sieve_bessel
    (N : ℕ) (I : Finset ℕ) (Is : Fin N → Finset ℕ) (hIs : ∀ i, Is i ⊆ I)
    (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (g : Fin N → ℕ → ℂ)
    (c : Fin N → ℂ) (hc : ∀ i, ‖c i‖ = 1) :
    ‖∑ i, c i * (∑ n ∈ Is i, f n * g i n)‖ ^ 2 ≤
      (I.card : ℝ) * ∑ i, ∑ j, ‖∑ n ∈ Is i ∩ Is j, g i n * star (g j n)‖ := by
  classical
  -- the superposition sequence, restricted to `I`
  set w : Fin N → ℕ → ℂ := fun i n => if n ∈ Is i then c i * g i n else 0 with hw
  -- Step A: rewrite the correlation as a single sum over `I` against the superposition.
  have hA : ∑ i, c i * (∑ n ∈ Is i, f n * g i n) = ∑ n ∈ I, f n * (∑ i, w i n) := by
    have hinner : ∀ i, c i * (∑ n ∈ Is i, f n * g i n) = ∑ n ∈ I, f n * w i n := by
      intro i
      calc c i * (∑ n ∈ Is i, f n * g i n)
          = ∑ n ∈ Is i, c i * (f n * g i n) := Finset.mul_sum _ _ _
        _ = ∑ n ∈ Is i, f n * w i n := by
              apply Finset.sum_congr rfl; intro n hn
              simp only [hw, hn, ite_true]; ring
        _ = ∑ n ∈ I, f n * w i n := by
              rw [Finset.sum_subset (hIs i)]
              intro n hnI hnni
              simp only [hw, hnni, ite_false, mul_zero]
    simp only [hinner]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro n hn
    rw [Finset.mul_sum]
  -- Step B: Cauchy–Schwarz against the superposition, and the trivial bound `∑ ‖f‖² ≤ #I`.
  have hCS := bessel_cs_complex I f (fun n => ∑ i, w i n)
  have hf2 : ∑ n ∈ I, ‖f n‖^2 ≤ (I.card:ℝ) := by
    calc ∑ n ∈ I, ‖f n‖^2 ≤ ∑ n ∈ I, (1:ℝ) := by
          apply Finset.sum_le_sum; intro n hn
          nlinarith [hf n, norm_nonneg (f n)]
      _ = (I.card:ℝ) := by simp
  -- Step C: expand the superposition square into the pairwise overlap correlations.
  have hGs := bessel_expand I w
  have hB : ∀ i j, ‖∑ n ∈ I, w i n * star (w j n)‖
      = ‖∑ n ∈ Is i ∩ Is j, g i n * star (g j n)‖ := by
    intro i j
    have hsub : Is i ∩ Is j ⊆ I := fun n hn => hIs i (Finset.mem_of_mem_inter_left hn)
    have hiff : ∑ n ∈ I, w i n * star (w j n)
        = ∑ n ∈ Is i ∩ Is j, w i n * star (w j n) := by
      rw [Finset.sum_subset hsub]
      intro n hnI hnnotin
      have hn : n ∉ Is i ∨ n ∉ Is j := by
        by_contra h
        simp only [not_or, not_not] at h
        exact hnnotin (Finset.mem_inter.mpr h)
      rcases hn with h | h
      · simp only [hw, h, ite_false, zero_mul]
      · simp only [hw, h, ite_false, star_zero, mul_zero]
    have hBij : ∑ n ∈ I, w i n * star (w j n)
        = (c i * star (c j)) * ∑ n ∈ Is i ∩ Is j, g i n * star (g j n) := by
      rw [Finset.mul_sum, hiff]
      apply Finset.sum_congr rfl; intro n hn
      obtain ⟨hni, hnj⟩ := Finset.mem_inter.mp hn
      simp only [hw, hni, hnj, ite_true, star_mul]; ring
    rw [hBij, norm_mul, norm_mul, hc i, norm_star, hc j, one_mul, one_mul]
  rw [hA]
  calc ‖∑ n ∈ I, f n * (∑ i, w i n)‖^2
      ≤ (∑ n ∈ I, ‖f n‖^2) * (∑ n ∈ I, ‖∑ i, w i n‖^2) := hCS
    _ ≤ (I.card:ℝ) * (∑ i, ∑ j, ‖∑ n ∈ I, w i n * star (w j n)‖) := by
          apply mul_le_mul hf2 hGs (by positivity) (by positivity)
    _ = (I.card:ℝ) * ∑ i, ∑ j, ‖∑ n ∈ Is i ∩ Is j, g i n * star (g j n)‖ := by
          rw [show (∑ i, ∑ j, ‖∑ n ∈ I, w i n * star (w j n)‖)
              = ∑ i, ∑ j, ‖∑ n ∈ Is i ∩ Is j, g i n * star (g j n)‖ from by
            apply Finset.sum_congr rfl; intro i hi
            apply Finset.sum_congr rfl; intro j hj
            exact hB i j]

end Work.BMF
