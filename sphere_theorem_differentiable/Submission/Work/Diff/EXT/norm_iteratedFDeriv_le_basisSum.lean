import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

/-- The coordinate functionals of a basis of a finite-dimensional space are bounded by a
constant times the norm. -/
private lemma basis_coord_norm_le_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E) (j : ι) (x : E) :
    ‖b.coord j x‖ ≤ (∑ i : ι, ‖LinearMap.toContinuousLinearMap (b.coord i)‖) * ‖x‖ := by
  have h1 := ContinuousLinearMap.le_opNorm (LinearMap.toContinuousLinearMap (b.coord j)) x
  rw [LinearMap.coe_toContinuousLinearMap'] at h1
  have h2 : ‖LinearMap.toContinuousLinearMap (b.coord j)‖ ≤
      ∑ i : ι, ‖LinearMap.toContinuousLinearMap (b.coord i)‖ :=
    Finset.single_le_sum (s := Finset.univ)
      (f := fun i => ‖LinearMap.toContinuousLinearMap (b.coord i)‖)
      (fun i _ => norm_nonneg _) (Finset.mem_univ j)
  exact le_trans h1 (mul_le_mul_of_nonneg_right h2 (norm_nonneg x))

/-- Expansion of a continuous multilinear map in a basis: the value at a tuple is the sum over
all tuples of basis vectors, weighted by the product of the coordinates. -/
private lemma continuousMultilinearMap_basis_expansion {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E) (k : ℕ)
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F) (x : Fin k → E) :
    M x = ∑ r : Fin k → ι, (∏ i, b.coord (r i) (x i)) • M (fun i => b (r i)) := by
  have hxs : ∀ i : Fin k, x i = ∑ j, (b.coord j) (x i) • b j := fun i => by
    simp only [Module.Basis.coord_apply]
    exact (Module.Basis.sum_repr b (x i)).symm
  have hfun : (fun i => ∑ j, (b.coord j) (x i) • b j) = x := by
    funext i
    exact (hxs i).symm
  conv_lhs => rw [← hfun]
  rw [ContinuousMultilinearMap.map_sum M (fun i j => (b.coord j) (x i) • b j)]
  refine Finset.sum_congr rfl fun r _ => ?_
  exact ContinuousMultilinearMap.map_smul_univ M (fun i => (b.coord (r i)) (x i)) (fun i => b (r i))

/-- A continuous multilinear map on a finite-dimensional space is bounded, in operator norm, by a
constant times the sum of the norms of its values on tuples of basis vectors. -/
private lemma continuousMultilinearMap_norm_le_basisSum {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F,
      ‖M‖ ≤ C * ∑ r : Fin k → ι, ‖M (fun i => b (r i))‖ := by
  let K : ℝ := ∑ i : ι, ‖LinearMap.toContinuousLinearMap (b.coord i)‖
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact Finset.sum_nonneg (f := fun i => ‖LinearMap.toContinuousLinearMap (b.coord i)‖)
      (fun i _ => norm_nonneg _)
  have hcoord : ∀ (j : ι) (x : E), ‖b.coord j x‖ ≤ K * ‖x‖ := by
    intro j x
    have h := basis_coord_norm_le_const b j x
    dsimp only [K]
    exact h
  refine ⟨K ^ k, pow_nonneg hK k, ?_⟩
  intro M
  have hexpand := continuousMultilinearMap_basis_expansion b k M
  have hmain : ∀ x : Fin k → E, ‖M x‖ ≤
      (K ^ k * ∑ r : Fin k → ι, ‖M (fun i => b (r i))‖) * ∏ i, ‖x i‖ := by
    intro x
    rw [hexpand x]
    have hstep : ∀ r : Fin k → ι,
        ‖(∏ i, (b.coord (r i)) (x i)) • M (fun i => b (r i))‖
          ≤ (K ^ k * ∏ i, ‖x i‖) * ‖M (fun i => b (r i))‖ := by
      intro r
      have heq : ‖(∏ i, (b.coord (r i)) (x i)) • M (fun i => b (r i))‖
          = (∏ i, ‖(b.coord (r i)) (x i)‖) * ‖M (fun i => b (r i))‖ := by
        rw [norm_smul]
        congr 1
        rw [Real.norm_eq_abs, Finset.abs_prod]
        exact Finset.prod_congr rfl fun i _ => (Real.norm_eq_abs _).symm
      rw [heq]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg (M (fun i => b (r i))))
      have hp : ∏ i, ‖(b.coord (r i)) (x i)‖ ≤ ∏ i, (K * ‖x i‖) :=
        Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hcoord (r i) (x i))
      have hp2 : ∏ i, (K * ‖x i‖) = K ^ k * ∏ i, ‖x i‖ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact hp.trans (le_of_eq hp2)
    have h1 : ‖∑ r : Fin k → ι, (∏ i, (b.coord (r i)) (x i)) • M (fun i => b (r i))‖
        ≤ ∑ r : Fin k → ι, ‖(∏ i, (b.coord (r i)) (x i)) • M (fun i => b (r i))‖ :=
      norm_sum_le Finset.univ _
    have h2 : ∑ r : Fin k → ι, ‖(∏ i, (b.coord (r i)) (x i)) • M (fun i => b (r i))‖
        ≤ ∑ r : Fin k → ι, (K ^ k * ∏ i, ‖x i‖) * ‖M (fun i => b (r i))‖ :=
      Finset.sum_le_sum fun r _ => hstep r
    have h3 : ∑ r : Fin k → ι, (K ^ k * ∏ i, ‖x i‖) * ‖M (fun i => b (r i))‖
        = (K ^ k * ∏ i, ‖x i‖) * ∑ r : Fin k → ι, ‖M (fun i => b (r i))‖ := by
      rw [Finset.mul_sum]
    have h4 : (K ^ k * ∏ i, ‖x i‖) * ∑ r : Fin k → ι, ‖M (fun i => b (r i))‖
        = (K ^ k * ∑ r : Fin k → ι, ‖M (fun i => b (r i))‖) * ∏ i, ‖x i‖ := by ring
    exact h1.trans (h2.trans (le_of_eq (h3.trans h4)))
  have hS : 0 ≤ ∑ r : Fin k → ι, ‖M (fun i => b (r i))‖ :=
    Finset.sum_nonneg (f := fun r : Fin k → ι => ‖M (fun i => b (r i))‖) (fun r _ => norm_nonneg _)
  exact ContinuousMultilinearMap.opNorm_le_bound (f := M)
    (M := K ^ k * ∑ r : Fin k → ι, ‖M (fun i => b (r i))‖)
    (mul_nonneg (pow_nonneg hK k) hS) hmain

theorem norm_iteratedFDeriv_le_basisSum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : E → F) (y : E),
      ‖iteratedFDeriv ℝ k f y‖ ≤ C * ∑ (ι : Fin k → Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ k f y fun s : Fin k => (Module.finBasis ℝ E (ι s) : E)‖ := by
  obtain ⟨C, hC, h⟩ :=
    continuousMultilinearMap_norm_le_basisSum (F := F) (Module.finBasis ℝ E) k
  exact ⟨C, hC, fun f y => h (iteratedFDeriv ℝ k f y)⟩

end Work.Diff.EXT
