import Mathlib

namespace Work.WilG4c

open scoped Topology

/-- The coordinate projection `z' ↦ z' j` has operator norm at most `1`. -/
private lemma norm_proj_le_one {N : ℕ} (j : Fin N) :
    ‖(ContinuousLinearMap.proj j : (Fin N → ℝ) →L[ℝ] ℝ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
    rw [one_mul, ContinuousLinearMap.proj_apply]
    exact norm_le_pi_norm x j)

/-- The `i`-th iterated derivative of the affine coordinate function `z' ↦ z' j - 1/2` is
bounded by `1` in operator norm, uniformly in `i`.

For `i = 0` this is just the pointwise bound `|z j - 1/2| ≤ 1`. For `i ≥ 1` the map is affine
with linear part `z' ↦ z' j` (a coordinate projection, of operator norm `1`), so its first
derivative is that projection and every higher derivative vanishes. -/
theorem NormIteratedFDerivCoordSubHalf {N : ℕ} (j : Fin N) (z : Fin N → ℝ)
    (hz : ∀ i, z i ∈ Set.Ioo (0 : ℝ) 1) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (fun z' : Fin N → ℝ => z' j - 1 / 2) z‖ ≤ 1 := by
  set L : (Fin N → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj j with hL
  have hLnorm : ‖L‖ ≤ 1 := by
    rw [hL]
    exact norm_proj_le_one j
  -- The coordinate function `z' ↦ z' j` is the continuous linear map `L`.
  have hg : (fun z' : Fin N → ℝ => z' j) = ⇑L := by
    funext y; rw [hL, ContinuousLinearMap.proj_apply]
  -- Subtracting the constant `1/2` does not change the Fréchet derivative.
  have hfderiv : fderiv ℝ (fun z' : Fin N → ℝ => z' j - 1 / 2) = fun _ => L := by
    funext x
    rw [fderiv_sub_const, hg]
    exact (ContinuousLinearMap.hasFDerivAt L (x := x)).fderiv
  rcases Nat.eq_zero_or_pos i with hi | hi
  · -- Case `i = 0`: the value itself, bounded by `1/2`.
    subst hi
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [(hz j).1, (hz j).2], by linarith [(hz j).1, (hz j).2]⟩
  · -- Case `i ≥ 1`: reduce to the derivative of the linear part.
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    rw [← norm_iteratedFDeriv_fderiv (𝕜 := ℝ)
      (f := fun z' : Fin N → ℝ => z' j - 1 / 2) (x := z) (n := n)]
    rw [hfderiv]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · -- Case `n = 0`: the norm is `‖L‖ ≤ 1`.
      subst hn
      rw [norm_iteratedFDeriv_zero]
      exact hLnorm
    · -- Case `n ≥ 1`: the derivative of a constant function vanishes.
      have hz0 : iteratedFDeriv ℝ n (fun _ : Fin N → ℝ => L) z = 0 := by
        rw [iteratedFDeriv_const_of_ne (by omega : n ≠ 0) L]
        rfl
      rw [hz0, norm_zero]
      norm_num

end Work.WilG4c
