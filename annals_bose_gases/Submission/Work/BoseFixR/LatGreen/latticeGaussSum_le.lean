import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseFixR.LatGreen.MadelungBound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.LatGreen.latticeGaussSum_le`

The uniform bound on the `ℤ³` lattice Gaussian sum

`Σ_{n ∈ ℤ³} exp(−(5/2)‖u − n‖²) ≤ 1.65`  for every `u : ℝ³`.

The sum is the value at the "time" `t = 1/10` of the periodised heat kernel
`heatPeriod t u = Σ_n p_t(u − n)`, `p_t(x) = (4πt)^{−3/2} e^{−‖x‖²/(4t)}`, rescaled:

`Σ_n exp(−(5/2)‖u − n‖²) = (2π/5)^{3/2} · heatPeriod (1/10) u`.

The point is that the *Poisson/Jacobi summation identity* (used here in its one-dimensional form
`PoissonGauss1D` together with the product decomposition `md_heatPeriod_eq_prod`) converts the
periodised kernel into its Fourier series

`heatPeriod t u = Σ_{k ∈ ℤ³} e^{−4π²t‖k‖²} cos(2π k·u)`,

whose terms are bounded **uniformly in `u`** by dropping the cosine (and thereby giving up all
of the sharp `u`-dependence — in particular there is no need to know that the maximum of the
lattice Gaussian sum is attained at a lattice point).  At `t = 1/10` the resulting tail
parameter `rhoZ (1/10) = 2 Σ_{j ≥ 1} e^{−(2π²/5) j²}` is at most `0.05`, so

`heatPeriod (1/10) u ≤ (1 + 0.05)³ = 1.157625`  and
`Σ_n e^{−(5/2)‖u−n‖²} ≤ 1.41 · 1.157625 ≤ 1.65`.

The numerical ingredients are `e^{−3.94} ≤ 1/48` (Taylor's theorem at `x = 3.94`, eight terms)
and `(2π/5)^{3/2} ≤ 1.41` (from `π < 3.14159265358979323847`).
-/

noncomputable section

open scoped Real BigOperators

namespace Work.BoseFixR.LatGreen

/-! ### The numerical ingredients -/

/-- `e^{−3.94} ≤ 1/48`, from the eight-term Taylor lower bound `Σ_{i<8} 3.94^i/i! ≤ e^{3.94}`
(which already exceeds `48`). -/
private lemma exp_neg_394_le : Real.exp (-(3.94 : ℝ)) ≤ 1 / 48 := by
  have hkey : (48 : ℝ) ≤ ∑ i ∈ Finset.range 8, ((3.94 : ℝ) ^ i / (i.factorial : ℝ)) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hsum := Real.sum_le_exp_of_nonneg (x := (3.94 : ℝ)) (by norm_num) 8
  have h : (48 : ℝ) ≤ Real.exp (3.94 : ℝ) := le_trans hkey hsum
  rw [Real.exp_neg]
  calc (Real.exp (3.94 : ℝ))⁻¹ ≤ (48 : ℝ)⁻¹ := by
        rw [inv_le_inv₀ (Real.exp_pos _) (by norm_num)]; exact h
    _ = 1 / 48 := by norm_num

/-- The Fourier tail parameter at `t = 1/10` is at most `1/47`: each term of
`SZ (1/10) = Σ_{j ≥ 0} e^{−(2π²/5)(j+1)²}` is bounded by `(1/48)^{j+1}`, using
`2π²/5 ≥ 3.94` and `(j+1)² ≥ j+1`. -/
private lemma SZ_tenth_le : SZ (1 / 10) ≤ 1 / 47 := by
  have hc : (3.94 : ℝ) ≤ 2 * Real.pi ^ 2 / 5 := by
    nlinarith [Real.pi_gt_d2, Real.pi_pos]
  have h4 : 4 * Real.pi ^ 2 * (1 / 10 : ℝ) = 2 * Real.pi ^ 2 / 5 := by ring
  have hterm : ∀ j : ℕ, Real.exp (-(2 * Real.pi ^ 2 / 5) * ((j : ℝ) + 1) ^ 2)
      ≤ (1 / 48 : ℝ) ^ (j + 1) := by
    intro j
    have hj : (1 : ℝ) ≤ (j : ℝ) + 1 := by
      have h : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    have hj2 : (j : ℝ) + 1 ≤ ((j : ℝ) + 1) ^ 2 := by
      have hy : (0 : ℝ) ≤ (j : ℝ) + 1 := by linarith
      nlinarith [hj, hy]
    have hs1 : -(2 * Real.pi ^ 2 / 5) * ((j : ℝ) + 1) ^ 2
        ≤ -(3.94 : ℝ) * ((j : ℝ) + 1) ^ 2 := by
      have h0 : (0 : ℝ) ≤ ((j : ℝ) + 1) ^ 2 := sq_nonneg ((j : ℝ) + 1)
      nlinarith [hc, h0]
    have hs2 : -(3.94 : ℝ) * ((j : ℝ) + 1) ^ 2 ≤ -(3.94 : ℝ) * ((j : ℝ) + 1) := by
      nlinarith [hj2]
    calc Real.exp (-(2 * Real.pi ^ 2 / 5) * ((j : ℝ) + 1) ^ 2)
        ≤ Real.exp (-(3.94 : ℝ) * ((j : ℝ) + 1) ^ 2) := Real.exp_le_exp.mpr hs1
      _ ≤ Real.exp (-(3.94 : ℝ) * ((j : ℝ) + 1)) := Real.exp_le_exp.mpr hs2
      _ = Real.exp (-(3.94 : ℝ)) ^ (j + 1) := by
          rw [show -(3.94 : ℝ) * ((j : ℝ) + 1) = ((j + 1 : ℕ) : ℝ) * (-(3.94 : ℝ)) by
            push_cast; ring]
          rw [Real.exp_nat_mul]
      _ ≤ (1 / 48 : ℝ) ^ (j + 1) := pow_le_pow_left₀ (Real.exp_nonneg _) exp_neg_394_le (j + 1)
  rw [SZ, h4]
  have hgeo : Summable (fun j : ℕ => (1 / 48 : ℝ) ^ (j + 1)) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 48)
      (by norm_num : (1 / 48 : ℝ) < 1)).comp_injective Nat.succ_injective
  have hsumE : Summable (fun j : ℕ => Real.exp (-(2 * Real.pi ^ 2 / 5) * ((j : ℝ) + 1) ^ 2)) :=
    Summable.of_nonneg_of_le (fun j => Real.exp_nonneg _) hterm hgeo
  calc (∑' j : ℕ, Real.exp (-(2 * Real.pi ^ 2 / 5) * ((j : ℝ) + 1) ^ 2))
      ≤ ∑' j : ℕ, (1 / 48 : ℝ) ^ (j + 1) :=
        Summable.tsum_le_tsum hterm hsumE hgeo
    _ = 1 / 47 := by
        rw [show (fun j : ℕ => (1 / 48 : ℝ) ^ (j + 1)) = fun j => (1 / 48 : ℝ) ^ j * (1 / 48) by
              funext j; rw [pow_succ]]
        rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        norm_num

/-- `(2π/5)^{3/2} ≤ 1.41`, written as `(2π/5)·√(2π/5)` and bounded with
`π < 3.14159265358979323847` and `1.121² = 1.256641 ≥ 1.25664 ≥ 2π/5`. -/
private lemma scale_pow_le : (2 * Real.pi / 5) ^ (3 / 2 : ℝ) ≤ 1.41 := by
  have h1 : 2 * Real.pi / 5 ≤ 1.25664 := by nlinarith [Real.pi_lt_d20, Real.pi_pos]
  have hs1 : 2 * Real.pi / 5 ≤ (1.121 : ℝ) ^ 2 := by
    have h2 : (1.121 : ℝ) ^ 2 = 1.256641 := by norm_num
    nlinarith [h1]
  have hsq : Real.sqrt (2 * Real.pi / 5) ≤ 1.121 :=
    le_trans (Real.sqrt_le_sqrt hs1) (le_of_eq (Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1.121)))
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add (by positivity : (0 : ℝ) < 2 * Real.pi / 5), Real.rpow_one, ← Real.sqrt_eq_rpow]
  have h := mul_le_mul h1 hsq (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 1.25664)
  have hnum : (1.25664 : ℝ) * 1.121 ≤ 1.41 := by norm_num
  linarith [h, hnum]

/-- The Gaussian `e^{−(5/2)‖x‖²}` is the rescaled heat kernel at time `t = 1/10`. -/
private lemma exp_neg_scale (x : EuclideanSpace ℝ (Fin 3)) :
    Real.exp (-(5 / 2 : ℝ) * ‖x‖ ^ 2)
      = (2 * Real.pi / 5) ^ (3 / 2 : ℝ) * heatK3 (1 / 10) x := by
  unfold heatK3
  rw [show (4 * Real.pi * (1 / 10 : ℝ)) = 2 * Real.pi / 5 by ring]
  rw [show -‖x‖ ^ 2 / (4 * (1 / 10 : ℝ)) = -(5 / 2 : ℝ) * ‖x‖ ^ 2 by ring]
  rw [← mul_assoc, ← Real.rpow_add (by positivity : (0 : ℝ) < 2 * Real.pi / 5)]
  norm_num

/-! ### The lattice Gaussian sum -/

/-- **The lattice Gaussian sum is bounded uniformly by `1.65`.** -/
theorem latticeGaussSum_le (u : EuclideanSpace ℝ (Fin 3)) :
    (∑' n : Fin 3 → ℤ, Real.exp (-(5 / 2 : ℝ) * ‖u - latVec n‖ ^ 2)) ≤ 1.65 := by
  -- Step 1: identify the sum with the rescaled periodised heat kernel at time `1/10`.
  have hS : (∑' n : Fin 3 → ℤ, Real.exp (-(5 / 2 : ℝ) * ‖u - latVec n‖ ^ 2))
      = (2 * Real.pi / 5) ^ (3 / 2 : ℝ) * heatPeriod (1 / 10) u := by
    rw [heatPeriod]
    rw [show (∑' n : Fin 3 → ℤ, Real.exp (-(5 / 2 : ℝ) * ‖u - latVec n‖ ^ 2))
        = ∑' n : Fin 3 → ℤ, (2 * Real.pi / 5) ^ (3 / 2 : ℝ) * heatK3 (1 / 10) (u - latVec n)
        from tsum_congr (fun n => exp_neg_scale (u - latVec n))]
    rw [tsum_mul_left]
  rw [hS]
  -- Step 2: the Poisson (one-dimensional) tail bound for each coordinate.
  have ht : (0 : ℝ) < 1 / 10 := by norm_num
  have hQ1le : ∀ i : Fin 3, (∑' m : ℤ, heatK1 (1 / 10) (u i - m)) ≤ 1 + rhoZ (1 / 10) := by
    intro i
    have h := (PoissonGauss1D ht (u i)).2
    have h' : |Q1 (1 / 10) (u i) - 1| ≤ rhoZ (1 / 10) := by
      simpa only [Q1, rhoZ, SZ] using h
    have h2 : Q1 (1 / 10) (u i) - 1 ≤ rhoZ (1 / 10) := le_trans (le_abs_self _) h'
    have h3 : Q1 (1 / 10) (u i) = ∑' m : ℤ, heatK1 (1 / 10) (u i - m) := rfl
    linarith [h2, h3]
  have hQ1nn : ∀ i : Fin 3, (0 : ℝ) ≤ ∑' m : ℤ, heatK1 (1 / 10) (u i - m) :=
    fun i => tsum_nonneg (fun m => heatK1_nonneg ht _)
  -- Step 3: multiply the three factors.
  have hh : heatPeriod (1 / 10) u ≤ (1 + rhoZ (1 / 10)) ^ 3 := by
    have hprod := md_heatPeriod_eq_prod ht u
    rw [hprod, Fin.prod_univ_three]
    have hρ : (0 : ℝ) ≤ 1 + rhoZ (1 / 10) := by linarith [rhoZ_nonneg (1 / 10)]
    have h01 : (∑' m : ℤ, heatK1 (1 / 10) (u 0 - m)) * (∑' m : ℤ, heatK1 (1 / 10) (u 1 - m))
        ≤ (1 + rhoZ (1 / 10)) * (1 + rhoZ (1 / 10)) :=
      mul_le_mul (hQ1le 0) (hQ1le 1) (hQ1nn 1) hρ
    have h2 : (∑' m : ℤ, heatK1 (1 / 10) (u 0 - m)) * (∑' m : ℤ, heatK1 (1 / 10) (u 1 - m))
          * (∑' m : ℤ, heatK1 (1 / 10) (u 2 - m))
        ≤ (1 + rhoZ (1 / 10)) * (1 + rhoZ (1 / 10)) * (1 + rhoZ (1 / 10)) :=
      mul_le_mul h01 (hQ1le 2) (hQ1nn 2) (by positivity)
    calc _ ≤ (1 + rhoZ (1 / 10)) * (1 + rhoZ (1 / 10)) * (1 + rhoZ (1 / 10)) := h2
      _ = (1 + rhoZ (1 / 10)) ^ 3 := by ring
  have hHPnn : (0 : ℝ) ≤ heatPeriod (1 / 10) u := by
    rw [heatPeriod]; exact tsum_nonneg (fun n => heatK3_nonneg (by norm_num) _)
  -- Step 4: the numerical ledger.
  have hρ : rhoZ (1 / 10) ≤ 0.05 := by
    rw [rhoZ]; linarith [SZ_tenth_le]
  have hhp : heatPeriod (1 / 10) u ≤ 1.157625 := by
    have h1 : 1 + rhoZ (1 / 10) ≤ 1.05 := by linarith
    have h0 : (0 : ℝ) ≤ 1 + rhoZ (1 / 10) := by linarith [rhoZ_nonneg (1 / 10)]
    have hp := pow_le_pow_left₀ h0 h1 3
    have h3 : (1.05 : ℝ) ^ 3 = 1.157625 := by norm_num
    rw [h3] at hp
    linarith [hh, hp]
  calc (2 * Real.pi / 5) ^ (3 / 2 : ℝ) * heatPeriod (1 / 10) u
      ≤ 1.41 * 1.157625 := mul_le_mul scale_pow_le hhp hHPnn (by norm_num)
    _ ≤ 1.65 := by norm_num

end Work.BoseFixR.LatGreen
