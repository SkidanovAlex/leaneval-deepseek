import Mathlib.Analysis.CStarAlgebra.Module.Constructions

namespace Commons.Analysis.Walsh

open Finset

/-- The sum of the constant `1` over all `Bool`-valued functions on `Fin n` is `2 ^ n`. -/
private lemma sum_one_bool_fun (n : ℕ) :
    (∑ _ : Fin n → Bool, (1 : ℝ)) = (2 : ℝ) ^ n := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  simp [nsmul_eq_mul]

/-- Factorisation of a sum of products over a product of `Bool`s:
`∑_{g : ι → Bool} ∏_i f i (g i) = ∏_i ∑_{b : Bool} f i b`. -/
private lemma sum_prod_pi_real {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → Bool → ℝ) :
    (∑ g : ι → Bool, ∏ i, f i (g i)) = ∏ i, ∑ b : Bool, f i b := by
  rw [Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset Bool)) f]
  rw [Fintype.piFinset_univ]

/-- Orthogonality of the Rademacher (sign) functions: the sum over all sign vectors of the
product of two coordinates is `2 ^ n` on the diagonal and `0` off it. -/
private lemma sum_sgn_mul (n : ℕ) (i j : Fin n) :
    (∑ e : Fin n → Bool,
        (if e i then (1 : ℝ) else -1) * (if e j then (1 : ℝ) else -1))
      = if i = j then (2 : ℝ) ^ n else 0 := by
  classical
  by_cases hij : i = j
  · rw [if_pos hij]
    have h1 : ∀ e : Fin n → Bool,
        (if e i then (1 : ℝ) else -1) * (if e j then (1 : ℝ) else -1) = 1 := by
      intro e
      rw [← hij]
      by_cases h : e i <;> simp [h]
    simp_rw [h1]
    exact sum_one_bool_fun n
  · rw [if_neg hij]
    have hrewrite : ∀ e : Fin n → Bool,
        (if e i then (1 : ℝ) else -1) * (if e j then (1 : ℝ) else -1)
          = ∏ k : Fin n,
              (if k = i then (if e k then (1 : ℝ) else -1) else 1)
                * (if k = j then (if e k then (1 : ℝ) else -1) else 1) := by
      intro e
      rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq']
      simp
    simp_rw [hrewrite]
    rw [sum_prod_pi_real (f := fun k b =>
        (if k = i then (if b then (1 : ℝ) else -1) else 1)
          * (if k = j then (if b then (1 : ℝ) else -1) else 1))]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [if_neg hij, mul_one]
    rw [Fintype.sum_bool]
    norm_num

/-- **Rademacher–Parseval identity in an abstract complex inner product space.**
For vectors `x i` in a complex inner product space,
`∑_{e : Fin n → Bool} ‖∑_i ε_e(i) x_i‖^2 = 2^n ∑_i ‖x_i‖^2`, where `ε_e(i) = ±1` is the
Rademacher sign determined by the bit `e i`. -/
theorem rademacher_parseval_inner (n : ℕ) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (x : Fin n → H) :
    (∑ e : Fin n → Bool, ‖∑ i, ((if e i then (1 : ℝ) else -1) : ℂ) • x i‖ ^ (2 : ℕ))
      = 2 ^ n * ∑ i, ‖x i‖ ^ (2 : ℕ) := by
  classical
  have hexp : ∀ e : Fin n → Bool,
      (inner ℂ (∑ i, (((if e i then (1 : ℝ) else -1) : ℂ)) • x i)
                (∑ i, (((if e i then (1 : ℝ) else -1) : ℂ)) • x i)).re
        = ∑ i, ∑ j,
            ((if e i then (1 : ℝ) else -1) * (if e j then (1 : ℝ) else -1))
              * (inner ℂ (x i) (x j)).re := by
    intro e
    rw [sum_inner]
    simp_rw [inner_sum]
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl; intro j _
    rw [inner_smul_left, inner_smul_right]
    cases e i <;> cases e j <;> simp
  have hnorm : ∀ e : Fin n → Bool,
      ‖∑ i, ((if e i then (1 : ℝ) else -1) : ℂ) • x i‖ ^ (2 : ℕ)
        = ∑ i, ∑ j,
            ((if e i then (1 : ℝ) else -1) * (if e j then (1 : ℝ) else -1))
              * (inner ℂ (x i) (x j)).re := by
    intro e
    have h1 : (inner ℂ (∑ i, (((if e i then (1 : ℝ) else -1) : ℂ)) • x i)
                (∑ i, (((if e i then (1 : ℝ) else -1) : ℂ)) • x i)).re
        = ‖∑ i, ((if e i then (1 : ℝ) else -1) : ℂ) • x i‖ ^ (2 : ℕ) := by
      simpa using inner_self_eq_norm_sq (𝕜 := ℂ)
        (∑ i, ((if e i then (1 : ℝ) else -1) : ℂ) • x i)
    rw [← h1]
    exact hexp e
  calc (∑ e : Fin n → Bool, ‖∑ i, ((if e i then (1 : ℝ) else -1) : ℂ) • x i‖ ^ (2 : ℕ))
      = ∑ e : Fin n → Bool, ∑ i, ∑ j,
            ((if e i then (1 : ℝ) else -1) * (if e j then (1 : ℝ) else -1))
              * (inner ℂ (x i) (x j)).re := by
        simp_rw [hnorm]
    _ = ∑ i, ∑ j, ∑ e : Fin n → Bool,
            ((if e i then (1 : ℝ) else -1) * (if e j then (1 : ℝ) else -1))
              * (inner ℂ (x i) (x j)).re := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.sum_comm]
    _ = ∑ i, ∑ j,
            (∑ e : Fin n → Bool,
              (if e i then (1 : ℝ) else -1) * (if e j then (1 : ℝ) else -1))
              * (inner ℂ (x i) (x j)).re := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        rw [Finset.sum_mul]
    _ = ∑ i, ∑ j, (if i = j then (2 : ℝ) ^ n else 0) * (inner ℂ (x i) (x j)).re := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        rw [sum_sgn_mul n i j]
    _ = ∑ i, (2 : ℝ) ^ n * (inner ℂ (x i) (x i)).re := by
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.sum_eq_single i]
        · rw [if_pos rfl]
        · intro j _ hji; rw [if_neg (fun h => hji h.symm), zero_mul]
        · intro hi; exact absurd (Finset.mem_univ i) hi
    _ = (2 : ℝ) ^ n * ∑ i, (inner ℂ (x i) (x i)).re := by
        rw [Finset.mul_sum]
    _ = (2 : ℝ) ^ n * ∑ i, ‖x i‖ ^ (2 : ℕ) := by
        congr 1
        apply Finset.sum_congr rfl; intro i _
        simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (x i)

end Commons.Analysis.Walsh