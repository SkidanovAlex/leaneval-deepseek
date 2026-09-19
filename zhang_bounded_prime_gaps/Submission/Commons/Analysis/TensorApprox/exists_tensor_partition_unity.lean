import Mathlib
import Submission.Commons.Analysis.Calculus.exists_contDiff_partition_unity
import Submission.Commons.Analysis.TensorApprox.exists_tensor_localization_orthant_thin_marg_explicit

namespace Commons.Analysis.TensorApprox

open scoped BigOperators
open Finset

/-- One factor of the tensor-product partition of unity: for a bounded `y` and `n` large
enough (relative to `|y|`), the grid sum of a one-dimensional partition of unity is `1`
(the terms outside `Icc (-n) n` that would matter all vanish). -/
theorem sum_partition_unity_eq_one {ψ : ℤ → ℝ → ℝ}
    (hsupp : ∀ m, Function.support (ψ m) ⊆ Set.Icc ((m : ℝ) - 1) ((m : ℝ) + 1))
    (hsum : ∀ y, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (∑ m ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), ψ m y) = 1)
    {y : ℝ} {n : ℕ} (hn : |y| + 2 ≤ (n : ℝ)) :
    (∑ m ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), ψ m y) = 1 := by
  obtain ⟨N, hN⟩ := hsum y
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hle : (n : ℤ) ≤ ((max n N : ℕ) : ℤ) := by
    have : n ≤ max n N := le_max_left n N
    exact_mod_cast this
  have hsub : Finset.Icc (-(n : ℤ)) (n : ℤ) ⊆
      Finset.Icc (-(((max n N : ℕ)) : ℤ)) (((max n N : ℕ)) : ℤ) := by
    intro m hm
    rw [Finset.mem_Icc] at hm ⊢
    constructor <;> omega
  rw [Finset.sum_subset hsub]
  · exact hN _ (le_max_right n N)
  · intro m _ hm
    have hmneg : (n : ℤ) < m ∨ m < -(n : ℤ) := by
      by_contra h
      push Not at h
      exact hm (Finset.mem_Icc.mpr ⟨h.2, h.1⟩)
    have hmgt : (n : ℝ) < |(m : ℝ)| := by
      rcases hmneg with h | h
      · have h' : (n : ℝ) < (m : ℝ) := by exact_mod_cast h
        rw [abs_of_pos (by linarith)]; linarith
      · have h' : (m : ℝ) < -(n : ℝ) := by exact_mod_cast h
        rw [abs_of_neg (by linarith)]; linarith
    by_contra hne
    have hmem := hsupp m hne
    rw [Set.mem_Icc] at hmem
    have h1 : |(m : ℝ) - y| ≤ 1 := by
      rw [abs_le]
      exact ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
    have h2 : |(m : ℝ)| ≤ |y| + 1 := by
      have h3 : |(m : ℝ)| = |((m : ℝ) - y) + y| := by ring_nf
      rw [h3]
      calc |((m : ℝ) - y) + y| ≤ |(m : ℝ) - y| + |y| := abs_add_le _ _
        _ ≤ 1 + |y| := by linarith
        _ = |y| + 1 := by ring
    linarith

/-- For `η > 0` and a set `K` of `Fin k → ℝ` whose coordinates are bounded by `M` in
absolute value, there is a one-variable smooth partition of unity `ψ : ℤ → ℝ → ℝ` with
`support (ψ m) ⊆ [m*η - η, m*η + η]`, `ψ m ≥ 0`, such that the tensor products
`∏ i, ψ (m i) (t i)` over the grid `|m_i| ≤ n` sum to `1` on `K`, for some `n`.
Uses `Commons.Analysis.Calculus.exists_contDiff_partition_unity`. -/
theorem exists_tensor_partition_unity {k : ℕ} {η M : ℝ} (hη : 0 < η) {K : Set (Fin k → ℝ)}
    (hK : ∀ t ∈ K, ∀ i, |t i| ≤ M) :
    ∃ (ψ : ℤ → ℝ → ℝ) (n : ℕ),
      (∀ m, ContDiff ℝ (↑(⊤ : ℕ∞)) (ψ m)) ∧
      (∀ m, Function.support (ψ m) ⊆ Set.Icc ((m : ℝ) * η - η) ((m : ℝ) * η + η)) ∧
      (∀ m x, 0 ≤ ψ m x) ∧
      ∀ t ∈ K, (∑ m ∈ Fintype.piFinset (fun _ : Fin k => Finset.Icc (-(n : ℤ)) (n : ℤ)),
        ∏ i, ψ (m i) (t i)) = 1 := by
  obtain ⟨ψ₀, hψ₀sm, hψ₀supp, hψ₀nn, hψ₀sum⟩ :=
    Commons.Analysis.Calculus.exists_contDiff_partition_unity
  obtain ⟨n₀, hn₀⟩ : ∃ n : ℕ, M / η + 2 ≤ (n : ℝ) := exists_nat_ge (M / η + 2)
  refine ⟨fun m x => ψ₀ m (x / η), n₀, ?_, ?_, ?_, ?_⟩
  · intro m
    exact (hψ₀sm m).comp (by fun_prop)
  · intro m x hx
    have h := hψ₀supp m hx
    rw [Set.mem_Icc] at h ⊢
    constructor
    · have := mul_le_mul_of_nonneg_right h.1 hη.le
      rw [div_mul_cancel₀ x (ne_of_gt hη)] at this
      linarith
    · have := mul_le_mul_of_nonneg_right h.2 hη.le
      rw [div_mul_cancel₀ x (ne_of_gt hη)] at this
      linarith
  · intro m x
    exact hψ₀nn m _
  · intro t ht
    have hfac : (∑ m ∈ Fintype.piFinset (fun _ : Fin k => Finset.Icc (-(n₀ : ℤ)) (n₀ : ℤ)),
          ∏ i, ψ₀ (m i) (t i / η)) =
        ∏ i : Fin k, ∑ j ∈ Finset.Icc (-(n₀ : ℤ)) (n₀ : ℤ), ψ₀ j (t i / η) :=
      Finset.sum_prod_piFinset (s := Finset.Icc (-(n₀ : ℤ)) (n₀ : ℤ))
        (g := fun i j => ψ₀ j (t i / η))
    rw [hfac]
    refine Finset.prod_eq_one fun i _ => sum_partition_unity_eq_one hψ₀supp hψ₀sum ?_
    have hti := hK t ht i
    have hle : |t i| / η ≤ M / η := by
      rw [div_le_div_iff_of_pos_right hη]; exact hti
    have hge : -(M / η) ≤ t i / η := by
      rw [← neg_div, div_le_div_iff_of_pos_right hη]
      exact (abs_le.mp hti).1
    rw [abs_div, abs_of_pos hη]
    linarith

end Commons.Analysis.TensorApprox
