import Mathlib

namespace Work.Rigidity

open UpperHalfPlane Filter Topology
open scoped MatrixGroups ModularForm Modular Manifold Bundle

/-- **Vanishing of the low `q`-expansion coefficients of a periodic function forces decay.**
Let `f : ℍ → ℂ` be `1`-periodic, holomorphic and bounded at `i∞`, and suppose that the first `m`
coefficients of its `q`-expansion at `i∞` vanish. Then `f τ = O(q ^ m)`: there are `A` and `B ≥ 0`
with `‖f τ‖ ≤ B * exp (-(2π m Im τ))` for `Im τ ≥ A`.

This is the converse of `Work.Rigidity.ExpDecayCoeffZero`
(`Submission/Work/Rigidity/ExpDecayCoeffZero.lean`), and is proved the same way: by
`UpperHalfPlane.hasSum_qExpansion` the `q`-expansion of `f` sums to `f`; deleting the first `m`
(vanishing) terms and dividing by `q ^ m` exhibits `τ ↦ f τ / q ^ m` as a function given by a
convergent `q`-expansion with non-negative exponents, hence bounded at `i∞` by
`UpperHalfPlane.isBoundedAtImInfty_of_hasSum_qExpansion`. -/
theorem decay_of_qExpansion_coeff_zero {f : UpperHalfPlane → Complex} {m : ℕ}
    (hper : Function.Periodic (fun w : ℂ => f (UpperHalfPlane.ofComplex w)) 1)
    (hfhol : MDiff f) (hbdd : UpperHalfPlane.IsBoundedAtImInfty f)
    (hcoeff : ∀ n : ℕ, n < m → (UpperHalfPlane.qExpansion 1 f).coeff n = 0) :
    ∃ A B : ℝ, 0 ≤ B ∧ ∀ τ : UpperHalfPlane, A ≤ τ.im →
      ‖f τ‖ ≤ B * Real.exp (-(2 * Real.pi * (m : ℝ) * τ.im)) := by
  -- The coefficients of the `q`-expansion at `i∞`, and the local parameter `q = 𝕢 1 τ`.
  let c : ℕ → ℂ := fun k => (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff k
  let g : UpperHalfPlane → ℂ := fun τ => f τ / (Function.Periodic.qParam 1 (τ : ℂ)) ^ m
  -- Step 1: `g = f / q ^ m` has a convergent `q`-expansion with non-negative exponents.
  have hg : ∀ τ : UpperHalfPlane,
      HasSum (fun k => c (k + m) • Function.Periodic.qParam 1 (τ : ℂ) ^ k) (g τ) := by
    intro τ
    have hq0 : Function.Periodic.qParam 1 (τ : ℂ) ≠ 0 := Function.Periodic.qParam_ne_zero _
    -- the `q`-expansion of `f` sums to `f τ`.
    have h1 : HasSum (fun k => c k • Function.Periodic.qParam 1 (τ : ℂ) ^ k) (f τ) :=
      UpperHalfPlane.hasSum_qExpansion (h := (1 : ℝ)) one_pos hper hfhol hbdd τ
    -- the first `m` terms vanish, by hypothesis.
    have hsum0 : (∑ i ∈ Finset.range m, c i • Function.Periodic.qParam 1 (τ : ℂ) ^ i) = 0 := by
      refine Finset.sum_eq_zero (fun i hi => ?_)
      rw [Finset.mem_range] at hi
      rw [show c i = 0 from hcoeff i hi, zero_smul]
    -- deleting the vanishing terms: `f τ = ∑_{k ≥ m} c k • q ^ k`.
    have hshift : HasSum (fun k => c (k + m) • Function.Periodic.qParam 1 (τ : ℂ) ^ (k + m))
        (f τ) :=
      ((hasSum_nat_add_iff (f := fun k => c k • Function.Periodic.qParam 1 (τ : ℂ) ^ k)
        m).mpr (by rw [hsum0, add_zero]; exact h1))
    -- dividing by `q ^ m` (nonzero) gives the `q`-expansion of `g`.
    have key : HasSum (fun k => c (k + m) • Function.Periodic.qParam 1 (τ : ℂ) ^ k)
        (f τ / Function.Periodic.qParam 1 (τ : ℂ) ^ m) := by
      refine (hasSum_mul_right_iff (a₂ := Function.Periodic.qParam 1 (τ : ℂ) ^ m)
        (a₁ := f τ / Function.Periodic.qParam 1 (τ : ℂ) ^ m) (pow_ne_zero _ hq0)).mp ?_
      rw [div_mul_cancel₀ _ (pow_ne_zero _ hq0)]
      simpa [smul_eq_mul, pow_add, mul_assoc] using hshift
    simpa [g] using key
  -- Step 2: hence `g` is bounded at `i∞`.
  have hgbdd : UpperHalfPlane.IsBoundedAtImInfty g :=
    UpperHalfPlane.isBoundedAtImInfty_of_hasSum_qExpansion (h := (1 : ℝ)) one_pos hg
  rw [UpperHalfPlane.isBoundedAtImInfty_iff] at hgbdd
  obtain ⟨M, A, hM⟩ := hgbdd
  refine ⟨A, max M 0, le_max_right _ _, fun τ hτ => ?_⟩
  -- Step 3: `‖f τ‖ = ‖g τ‖ * ‖q ^ m‖ = ‖g τ‖ * exp (-(2π m Im τ))`.
  have hgτ : ‖g τ‖ ≤ M := hM τ hτ
  have hfτ : f τ = g τ * Function.Periodic.qParam 1 (τ : ℂ) ^ m := by
    rw [show g τ = f τ / Function.Periodic.qParam 1 (τ : ℂ) ^ m from rfl,
      div_mul_cancel₀ _ (pow_ne_zero _ (Function.Periodic.qParam_ne_zero _))]
  rw [hfτ, norm_mul]
  have hqnorm : ‖Function.Periodic.qParam 1 (τ : ℂ) ^ m‖
      = Real.exp (-(2 * Real.pi * (m : ℝ) * τ.im)) := by
    rw [norm_pow, Function.Periodic.norm_qParam, div_one, ← Real.exp_nat_mul]
    congr 1
    rw [UpperHalfPlane.coe_im]
    ring
  rw [hqnorm]
  exact mul_le_mul_of_nonneg_right (le_trans hgτ (le_max_left _ _)) (Real.exp_nonneg _)

end Work.Rigidity
