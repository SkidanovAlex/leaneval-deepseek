import Mathlib
import Submission.Work.HP.MDEstimates.Sigma2_44_I_lo_aux.GmdAux.NMulPowLe

set_option autoImplicit false

namespace Work.HP.MDEstimates.Sigma2_44_I_lo_aux

open Finset
open scoped BigOperators

/-- A truncated geometric series with ratio in `[0,1)` is bounded by the full series. -/
private lemma geom_range_le_aux {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (L : ℕ) :
    (∑ m ∈ Finset.range L, x ^ m) ≤ (1 - x)⁻¹ := by
  have hpos : (0 : ℝ) < 1 - x := by linarith
  have hkey : (∑ m ∈ Finset.range L, x ^ m) * (1 - x) = 1 - x ^ L :=
    geom_sum_mul_neg x L
  have hle : (∑ m ∈ Finset.range L, x ^ m) * (1 - x) ≤ 1 := by
    rw [hkey]
    have := pow_nonneg hx0 L
    linarith
  calc (∑ m ∈ Finset.range L, x ^ m)
      = (∑ m ∈ Finset.range L, x ^ m) * (1 - x) / (1 - x) :=
        (mul_div_cancel_right₀ _ (ne_of_gt hpos)).symm
    _ ≤ 1 / (1 - x) := div_le_div_of_nonneg_right hle (le_of_lt hpos)
    _ = (1 - x)⁻¹ := by rw [one_div]

/-- `(a^j)^(-θ) = (a^(-θ))^j` for `a > 0`. -/
lemma rpow_pow_neg (a θ : ℝ) (ha : 0 < a) (j : ℕ) :
    (a ^ j) ^ (-θ) = (a ^ (-θ)) ^ j := by
  rw [← Real.rpow_natCast_mul ha.le j (-θ), mul_comm ((j : ℝ)) (-θ),
    Real.rpow_mul_natCast ha.le]

/-- Finite geometric tail: if every `j ∈ T` satisfies `k ≤ j` then
`∑_{j ∈ T} σ^j ≤ σ^k / (1 - σ)`, for `0 < σ < 1`. -/
lemma geom_tail_le {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (k : ℕ) {T : Finset ℕ}
    (hT : ∀ j ∈ T, k ≤ j) :
    (∑ j ∈ T, σ ^ j) ≤ σ ^ k * (1 - σ)⁻¹ := by
  have hσ : 0 ≤ σ := le_of_lt hσ0
  have h1 : (∑ j ∈ T, σ ^ j) = σ ^ k * ∑ j ∈ T, σ ^ (j - k) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← pow_add, Nat.add_sub_cancel' (hT j hj)]
  have h2 : (∑ j ∈ T, σ ^ (j - k)) ≤ (1 - σ)⁻¹ := by
    have hinj : Set.InjOn (fun j => j - k) ↑T := by
      intro x hx y hy hxy
      have hx' : k ≤ x := hT x hx
      have hy' : k ≤ y := hT y hy
      simp only at hxy
      omega
    rw [← Finset.sum_image (s := T) (f := fun i => σ ^ i) (g := fun j => j - k) hinj]
    calc (∑ i ∈ T.image (fun j => j - k), σ ^ i)
        ≤ ∑ i ∈ Finset.range ((T.image (fun j => j - k)).sup id + 1), σ ^ i := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => pow_nonneg hσ i)
          intro i hi
          rw [Finset.mem_range]
          exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
      _ ≤ (1 - σ)⁻¹ := geom_range_le_aux hσ hσ1 _
  calc (∑ j ∈ T, σ ^ j) = σ ^ k * ∑ j ∈ T, σ ^ (j - k) := h1
    _ ≤ σ ^ k * (1 - σ)⁻¹ := mul_le_mul_of_nonneg_left h2 (pow_nonneg hσ k)

theorem GeomMinDecPart {a θ : ℝ} (ha : 1 < a) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {N C : ℝ} (hN : 0 < N) (hC : 0 < C) {k n : ℕ}
    (hcross : N / C ≤ a ^ k) :
    (∑ j ∈ Finset.range (n+1), (if k ≤ j then N * (a^j)^(-θ) else 0))
      ≤ 1 / (1 - a^(-θ)) * C^θ * N^(1-θ) := by
  have ha0 : 0 < a := by linarith
  set σ : ℝ := a ^ (-θ) with hσdef
  have hσ0 : 0 < σ := by rw [hσdef]; exact Real.rpow_pos_of_pos ha0 _
  have hσ1 : σ < 1 := by
    rw [hσdef, Real.rpow_neg ha0.le]
    exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow ha hθ0)
  have hsummand : ∀ j : ℕ,
      (if k ≤ j then N * (a^j)^(-θ) else 0) = N * (if k ≤ j then σ^j else 0) := by
    intro j
    by_cases h : k ≤ j
    · simp only [h, ↓reduceIte, rpow_pow_neg a θ ha0 j, ← hσdef]
    · simp only [h, ↓reduceIte, mul_zero]
  have hgeom := geom_tail_le hσ0 hσ1 k
    (T := (Finset.range (n+1)).filter (fun j => k ≤ j))
    (fun j hj => (Finset.mem_filter.mp hj).2)
  have harith : N * σ ^ k ≤ C ^ θ * N ^ (1 - θ) := by
    rw [hσdef]
    exact GmdAux.NMulPowLe ha hθ0 hN hC hcross
  calc (∑ j ∈ Finset.range (n+1), (if k ≤ j then N * (a^j)^(-θ) else 0))
      = N * (∑ j ∈ (Finset.range (n+1)).filter (fun j => k ≤ j), σ^j) := by
        simp only [hsummand]
        rw [← Finset.mul_sum, ← Finset.sum_filter]
    _ ≤ N * (σ^k * (1 - σ)⁻¹) := mul_le_mul_of_nonneg_left hgeom hN.le
    _ = (N * σ^k) * (1 - σ)⁻¹ := by rw [mul_assoc]
    _ ≤ (C^θ * N^(1-θ)) * (1 - σ)⁻¹ :=
        mul_le_mul_of_nonneg_right harith (by positivity)
    _ = 1 / (1 - σ) * C^θ * N^(1-θ) := by ring
    _ = 1 / (1 - a^(-θ)) * C^θ * N^(1-θ) := by rw [hσdef]

end Work.HP.MDEstimates.Sigma2_44_I_lo_aux
