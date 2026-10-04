import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators

namespace Work.Diff.STE.B3

/-- A continuous multilinear form on `(Fin n → ℝ)^N` is bounded by `n^N` times its bound on the
basis tuples.  Every tuple of vectors expands in the standard basis `Pi.single j 1` of `Fin n → ℝ`;
multilinearity produces the `n^N` terms `∏ i, m i (γ i)` and each coordinate is controlled by the
sup norm on `Fin n → ℝ`. -/
theorem normMultilinear_le_of_basis {n N : ℕ} {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G]
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin N => Fin n → ℝ) G) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ γ : Fin N → Fin n, ‖Φ (fun i => Pi.single (γ i) (1 : ℝ))‖ ≤ B) :
    ‖Φ‖ ≤ (n : ℝ) ^ N * B := by
  classical
  refine ContinuousMultilinearMap.opNorm_le_bound
    (mul_nonneg (pow_nonneg (Nat.cast_nonneg n) N) hB) fun m => ?_
  -- expand each argument of `m` in the standard basis of `Fin n → ℝ`
  have hm : m = fun i : Fin N => ∑ j : Fin n, (m i j) • (Pi.single j (1 : ℝ)) := by
    funext i
    rw [← Finset.univ_sum_single (m i)]
    refine Finset.sum_congr rfl fun j _ => ?_
    funext k
    simp [Pi.single_apply]
  conv_lhs => rw [hm]
  rw [ContinuousMultilinearMap.map_sum]
  calc ‖∑ γ : Fin N → Fin n, Φ (fun i => (m i (γ i)) • Pi.single (γ i) (1 : ℝ))‖
      = ‖∑ γ : Fin N → Fin n, (∏ i, m i (γ i)) • Φ (fun i => Pi.single (γ i) (1 : ℝ))‖ := by
        congr 1
        refine Finset.sum_congr rfl fun γ _ => ?_
        rw [ContinuousMultilinearMap.map_smul_univ]
    _ ≤ ∑ γ : Fin N → Fin n, ‖(∏ i, m i (γ i)) • Φ (fun i => Pi.single (γ i) (1 : ℝ))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ γ : Fin N → Fin n, (∏ i, ‖m i‖) * B := by
        refine Finset.sum_le_sum fun γ _ => ?_
        have hprod : (∏ i : Fin N, ‖m i (γ i)‖) ≤ ∏ i : Fin N, ‖m i‖ :=
          Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => norm_le_pi_norm (m i) (γ i)
        rw [norm_smul, norm_prod]
        exact mul_le_mul hprod (h γ) (norm_nonneg _) (Finset.prod_nonneg fun i _ => norm_nonneg _)
    _ = (n : ℝ) ^ N * B * ∏ i, ‖m i‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
        rw [nsmul_eq_mul]
        push_cast
        ring

end Work.Diff.STE.B3
