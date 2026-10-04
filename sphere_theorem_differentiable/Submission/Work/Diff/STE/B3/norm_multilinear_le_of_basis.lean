import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

/-- A continuous `N`-multilinear map on `(Fin n → ℝ)^N` whose values on the standard
basis `γ ↦ (fun i => Pi.single (γ i) 1)` are bounded by `B ≥ 0` has operator norm at most
`n^N * B`. -/
theorem norm_multilinear_le_of_basis {n N : ℕ} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin N => Fin n → ℝ) G) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ γ : Fin N → Fin n, ‖Φ (fun i => Pi.single (γ i) (1 : ℝ))‖ ≤ B) :
    ‖Φ‖ ≤ (n : ℝ) ^ N * B := by
  classical
  refine Φ.opNorm_le_bound (by positivity) fun m => ?_
  -- Expand `m` in the standard basis of each copy of `Fin n → ℝ`.
  have h1 : Φ m = ∑ r : Fin N → Fin n, Φ (fun i => Pi.single (r i) (m i (r i))) := by
    have key := ContinuousMultilinearMap.map_sum Φ (g := fun i (j : Fin n) => Pi.single j (m i j))
    rwa [show (fun i : Fin N => ∑ j : Fin n, Pi.single j (m i j)) = m from
      funext fun i => Finset.univ_sum_single (m i)] at key
  -- Pull the scalars `m i (r i)` out of `Φ`.
  have h2 : ∀ r : Fin N → Fin n,
      Φ (fun i => Pi.single (r i) (m i (r i)))
        = (∏ i, m i (r i)) • Φ (fun i => Pi.single (r i) (1 : ℝ)) := by
    intro r
    have hfun : (fun i => Pi.single (r i) (m i (r i)))
        = fun i => (m i (r i)) • Pi.single (r i) (1 : ℝ) := by
      funext i
      have hh := Pi.single_smul (I := Fin n) (f := fun _ : Fin n => ℝ) (r i) (m i (r i)) (1 : ℝ)
      simpa using hh
    rw [hfun, ContinuousMultilinearMap.map_smul_univ]
  have hexp : Φ m = ∑ r : Fin N → Fin n,
      (∏ i, m i (r i)) • Φ (fun i => Pi.single (r i) (1 : ℝ)) := by
    rw [h1]
    exact Finset.sum_congr rfl fun r _ => h2 r
  calc ‖Φ m‖ = ‖∑ r : Fin N → Fin n,
        (∏ i, m i (r i)) • Φ (fun i => Pi.single (r i) (1 : ℝ))‖ := by rw [hexp]
    _ ≤ ∑ r : Fin N → Fin n,
          ‖(∏ i, m i (r i)) • Φ (fun i => Pi.single (r i) (1 : ℝ))‖ := norm_sum_le _ _
    _ = ∑ r : Fin N → Fin n,
          (∏ i, ‖m i (r i)‖) * ‖Φ (fun i => Pi.single (r i) (1 : ℝ))‖ := by
        apply Finset.sum_congr rfl; intro r _
        rw [norm_smul, norm_prod]
    _ ≤ ∑ _r : Fin N → Fin n, (∏ i, ‖m i‖) * B := by
        apply Finset.sum_le_sum; intro r _
        exact mul_le_mul
          (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => norm_le_pi_norm (m i) (r i)))
          (h r) (norm_nonneg _) (Finset.prod_nonneg fun i _ => norm_nonneg _)
    _ = (n : ℝ) ^ N * B * ∏ i, ‖m i‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin]
        simp only [nsmul_eq_mul, Nat.cast_pow]
        ring

end Work.Diff.STE.B3
