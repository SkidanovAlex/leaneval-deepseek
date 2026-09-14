import Mathlib.Analysis.InnerProductSpace.Calculus

open scoped BigOperators

set_option autoImplicit false

namespace Commons.Analysis.Calculus

/-- The pairwise kernel `x ↦ ‖xᵢ - xⱼ‖⁻¹` on the configuration space
`EuclideanSpace E (Fin N)` is `Cⁿ`, for every order `n`, on the complement of the
diagonal `{x | xᵢ ≠ xⱼ}`. -/
theorem contDiffOn_pair_inv_dist {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {N : ℕ} {n : WithTop ℕ∞} (i j : Fin N) :
    ContDiffOn ℝ n (fun x : EuclideanSpace E (Fin N) => (dist (x i) (x j))⁻¹)
      {x | x i ≠ x j} := by
  let L : EuclideanSpace E (Fin N) →L[ℝ] E :=
    PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin N => E) i -
      PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin N => E) j
  have hL : ∀ x : EuclideanSpace E (Fin N), L x = x i - x j := by
    intro x; simp [L]
  have hLc : ContDiffOn ℝ n (fun x : EuclideanSpace E (Fin N) => L x)
      {x | x i ≠ x j} := (ContinuousLinearMap.contDiff L).contDiffOn
  have hnorm : ContDiffOn ℝ n (fun x : EuclideanSpace E (Fin N) => ‖L x‖)
      {x | x i ≠ x j} := by
    refine ContDiffOn.norm ℝ hLc ?_
    intro x hx
    rw [hL x]
    exact sub_ne_zero.mpr hx
  have hinv : ContDiffOn ℝ n (fun x : EuclideanSpace E (Fin N) => ‖L x‖⁻¹)
      {x | x i ≠ x j} :=
    ContDiffOn.inv hnorm (by
      intro x hx
      rw [hL x]
      exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx))
  refine hinv.congr ?_
  intro x _
  rw [dist_eq_norm, hL x]

/-- The Newtonian pair potential `∑_{i<j} mᵢ mⱼ / ‖xᵢ - xⱼ‖` on `(EuclideanSpace E (Fin N))` is
smooth on the set of collision-free configurations. -/
theorem contDiffOn_pairSum_inv_dist {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {N : ℕ} {m : Fin N → ℝ} :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace E (Fin N) =>
        Finset.sum Finset.univ fun j => Finset.sum (Finset.Iio j) fun i =>
          m i * m j * (dist (x i) (x j))⁻¹)
      {x | ∀ i j, i ≠ j → x i ≠ x j} := by
  refine ContDiffOn.sum (𝕜 := ℝ) (fun j _ => ?_)
  refine ContDiffOn.sum (𝕜 := ℝ) (fun i hi => ?_)
  have hij : i ≠ j := (Finset.mem_Iio.mp hi).ne
  have hsub : {x : EuclideanSpace E (Fin N) | ∀ i j, i ≠ j → x i ≠ x j} ⊆
      {x | x i ≠ x j} := fun x hx => hx i j hij
  have h := (contDiffOn_pair_inv_dist (E := E)
    (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) i j).mono hsub
  have hconst : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun _ : EuclideanSpace E (Fin N) => m i * m j) {x | ∀ i j, i ≠ j → x i ≠ x j} :=
    contDiffOn_const
  simpa using hconst.mul h

end Commons.Analysis.Calculus