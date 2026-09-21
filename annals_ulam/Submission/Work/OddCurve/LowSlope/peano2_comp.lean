import Mathlib
import Submission.Work.OddCurve.LowSlope.Peano2

namespace Work.OddCurve.LowSlope

noncomputable section

open Filter Asymptotics
open scoped Topology

/-- For real `x`, `x ^ m = o (x ^ n)` at `0` whenever `n < m`. -/
lemma isLittleO_pow_pow_nhds_zero {m n : ℕ} (h : n < m) :
    (fun x : ℝ => x ^ m) =o[𝓝 (0 : ℝ)] fun x => x ^ n := by
  have h0 := isLittleO_pow_sub_pow_sub (0 : ℝ) (n := n) (m := m) h
  rw [show (fun x : ℝ => ‖x - 0‖ ^ m) = (fun x : ℝ => ‖x ^ m‖) from by
        funext x; simp [norm_pow],
      show (fun x : ℝ => ‖x - 0‖ ^ n) = (fun x : ℝ => ‖x ^ n‖) from by
        funext x; simp [norm_pow]] at h0
  exact isLittleO_norm_right.mp (isLittleO_norm_left.mp h0)

/-- For real `x`, `x ^ m = O (x ^ n)` at `0` whenever `n ≤ m`. -/
lemma isBigO_pow_pow_nhds_zero {m n : ℕ} (h : n ≤ m) :
    (fun x : ℝ => x ^ m) =O[𝓝 (0 : ℝ)] fun x => x ^ n := by
  rcases lt_or_eq_of_le h with hlt | heq
  · exact (isLittleO_pow_pow_nhds_zero hlt).isBigO
  · subst heq; exact isBigO_refl _ _

/-- **Chain rule for second-order Peano expansions.**  If `f` has the second order expansion
`f (x₀ + h) = f x₀ + b₁ h + b₂/2 h² + o (h²)` and `X` has the expansion
`X (u + k) = x₀ + a₁ k + a₂/2 k² + o (k²)` with `X u = x₀`, then `f ∘ X` has the expansion
`b₁ a₁ k + (b₂ a₁² + b₁ a₂)/2 k² + o (k²)` at `u`. -/
theorem peano2_comp {f X : ℝ → ℝ} {x₀ u a₁ a₂ b₁ b₂ : ℝ}
    (hf : Work.OddCurve.LowSlope.Peano2 f x₀ b₁ b₂)
    (hX : Work.OddCurve.LowSlope.Peano2 X u a₁ a₂) (hXx : X u = x₀) :
    Work.OddCurve.LowSlope.Peano2 (fun v : ℝ => f (X v)) u (b₁ * a₁) (b₂ * a₁ ^ 2 + b₁ * a₂) := by
  simp only [Work.OddCurve.LowSlope.Peano2] at hf hX ⊢
  have hk2 : (fun k : ℝ => k ^ 2) =O[𝓝 0] (fun k : ℝ => k) := by
    simpa using isBigO_pow_pow_nhds_zero (m := 2) (n := 1) (by norm_num)
  have hk3 : (fun k : ℝ => k ^ 3) =O[𝓝 0] (fun k : ℝ => k ^ 2) :=
    isBigO_pow_pow_nhds_zero (m := 3) (n := 2) (by norm_num)
  have hk4 : (fun k : ℝ => k ^ 4) =O[𝓝 0] (fun k : ℝ => k ^ 2) :=
    isBigO_pow_pow_nhds_zero (m := 4) (n := 2) (by norm_num)
  have hk3o : (fun k : ℝ => k ^ 3) =o[𝓝 0] (fun k : ℝ => k ^ 2) :=
    isLittleO_pow_pow_nhds_zero (m := 3) (n := 2) (by norm_num)
  have hk4o : (fun k : ℝ => k ^ 4) =o[𝓝 0] (fun k : ℝ => k ^ 2) :=
    isLittleO_pow_pow_nhds_zero (m := 4) (n := 2) (by norm_num)
  -- the inner map `k ↦ X (u + k) - x₀` tends to `0`
  have hw_tend : Tendsto (fun k : ℝ => X (u + k) - x₀) (𝓝 0) (𝓝 0) := by
    have hp : Tendsto (fun k : ℝ => k ^ 2) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_pow 2).tendsto (0 : ℝ)
    have hφ : Tendsto (fun k : ℝ => X (u + k) - X u - a₁ * k - a₂ / 2 * k ^ 2) (𝓝 0) (𝓝 0) :=
      hX.tendsto_zero_of_tendsto hp
    have h2 : Tendsto (fun k : ℝ => a₁ * k + a₂ / 2 * k ^ 2) (𝓝 0) (𝓝 0) := by
      have hc : Continuous fun k : ℝ => a₁ * k + a₂ / 2 * k ^ 2 := by continuity
      simpa using hc.tendsto (0 : ℝ)
    have hsum := hφ.add h2
    have heq : (fun k : ℝ => (X (u + k) - X u - a₁ * k - a₂ / 2 * k ^ 2)
        + (a₁ * k + a₂ / 2 * k ^ 2)) = fun k : ℝ => X (u + k) - x₀ := by
      funext k; rw [hXx]; ring
    rw [heq] at hsum
    simpa using hsum
  -- the second-order error of `X` at `u`, shifted by `hXx`
  have hd : (fun k : ℝ => X (u + k) - x₀ - (a₁ * k + a₂ / 2 * k ^ 2)) =o[𝓝 0]
      (fun k : ℝ => k ^ 2) := by
    refine hX.congr' ?_ EventuallyEq.rfl
    filter_upwards with k
    rw [hXx]; ring
  -- the quadratic part `k ↦ a₁ k + a₂/2 k²` is `O (k)`
  have heO : (fun k : ℝ => a₁ * k + a₂ / 2 * k ^ 2) =O[𝓝 0] (fun k : ℝ => k) := by
    have h1 : (fun k : ℝ => a₁ * k) =O[𝓝 0] (fun k : ℝ => k) :=
      (isBigO_refl (fun k : ℝ => k) (𝓝 0)).const_mul_left a₁
    have h2 : (fun k : ℝ => a₂ / 2 * k ^ 2) =O[𝓝 0] (fun k : ℝ => k) :=
      hk2.const_mul_left (a₂ / 2)
    exact h1.add h2
  have hWO : (fun k : ℝ => X (u + k) - x₀) =O[𝓝 0] (fun k : ℝ => k) := by
    have h1 : (fun k : ℝ => X (u + k) - x₀ - (a₁ * k + a₂ / 2 * k ^ 2)) =O[𝓝 0]
        (fun k : ℝ => k) := (hd.trans_isBigO hk2).isBigO
    have hsum : (fun k : ℝ => (X (u + k) - x₀ - (a₁ * k + a₂ / 2 * k ^ 2))
        + (a₁ * k + a₂ / 2 * k ^ 2)) =O[𝓝 0] (fun k : ℝ => k) := h1.add heO
    have heq : (fun k : ℝ => (X (u + k) - x₀ - (a₁ * k + a₂ / 2 * k ^ 2))
        + (a₁ * k + a₂ / 2 * k ^ 2)) = fun k : ℝ => X (u + k) - x₀ := by
      funext k; ring
    rwa [heq] at hsum
  have hW2 : (fun k : ℝ => (X (u + k) - x₀) ^ 2) =O[𝓝 0] (fun k : ℝ => k ^ 2) := hWO.pow 2
  -- the composition error `f (X (u + k)) - (f x₀ + b₁ (X (u+k) - x₀) + b₂/2 (…)²)`
  have hA : (fun k : ℝ => f (x₀ + (X (u + k) - x₀)) - f x₀ - b₁ * (X (u + k) - x₀)
      - b₂ / 2 * (X (u + k) - x₀) ^ 2) =o[𝓝 0] (fun k : ℝ => k ^ 2) := by
    have h := hf.comp_tendsto hw_tend
    exact h.trans_isBigO hW2
  have hd2 : (fun k : ℝ => (X (u + k) - x₀ - (a₁ * k + a₂ / 2 * k ^ 2)) ^ 2) =o[𝓝 0]
      (fun k : ℝ => k ^ 2) := by
    have h := hd.pow (n := 2) (by norm_num)
    have h4 : (fun k : ℝ => (k ^ 2) ^ 2) =O[𝓝 0] (fun k : ℝ => k ^ 2) := by
      rw [show (fun k : ℝ => k ^ 4) = (fun k : ℝ => (k ^ 2) ^ 2) from by funext k; ring] at hk4
      exact hk4
    exact h.trans_isBigO h4
  have hmix : (fun k : ℝ => (a₁ * k + a₂ / 2 * k ^ 2)
      * (X (u + k) - x₀ - (a₁ * k + a₂ / 2 * k ^ 2))) =o[𝓝 0] (fun k : ℝ => k ^ 2) := by
    have h := IsBigO.mul_isLittleO heO hd
    have h3 : (fun k : ℝ => k * k ^ 2) =O[𝓝 0] (fun k : ℝ => k ^ 2) := by
      rw [show (fun k : ℝ => k ^ 3) = (fun k : ℝ => k * k ^ 2) from by funext k; ring] at hk3
      exact hk3
    exact h.trans_isBigO h3
  have hP : (fun k : ℝ => b₂ * a₁ * a₂ / 2 * k ^ 3 + b₂ * a₂ ^ 2 / 8 * k ^ 4) =o[𝓝 0]
      (fun k : ℝ => k ^ 2) := by
    have h3 : (fun k : ℝ => b₂ * a₁ * a₂ / 2 * k ^ 3) =o[𝓝 0] (fun k : ℝ => k ^ 2) :=
      hk3o.const_mul_left (b₂ * a₁ * a₂ / 2)
    have h4 : (fun k : ℝ => b₂ * a₂ ^ 2 / 8 * k ^ 4) =o[𝓝 0] (fun k : ℝ => k ^ 2) :=
      hk4o.const_mul_left (b₂ * a₂ ^ 2 / 8)
    exact h3.add h4
  -- the polynomial part of the composite expansion
  have hB : (fun k : ℝ => b₁ * (X (u + k) - x₀) + b₂ / 2 * (X (u + k) - x₀) ^ 2
      - (b₁ * a₁) * k - (b₂ * a₁ ^ 2 + b₁ * a₂) / 2 * k ^ 2) =o[𝓝 0] (fun k : ℝ => k ^ 2) := by
    have h1 : (fun k : ℝ => b₁ * (X (u + k) - x₀ - (a₁ * k + a₂ / 2 * k ^ 2))) =o[𝓝 0]
        (fun k : ℝ => k ^ 2) := hd.const_mul_left b₁
    have h2 : (fun k : ℝ => b₂ * ((a₁ * k + a₂ / 2 * k ^ 2)
        * (X (u + k) - x₀ - (a₁ * k + a₂ / 2 * k ^ 2)))) =o[𝓝 0] (fun k : ℝ => k ^ 2) :=
      hmix.const_mul_left b₂
    have h3 : (fun k : ℝ => b₂ / 2 * (X (u + k) - x₀ - (a₁ * k + a₂ / 2 * k ^ 2)) ^ 2) =o[𝓝 0]
        (fun k : ℝ => k ^ 2) := hd2.const_mul_left (b₂ / 2)
    have hsum : (fun k : ℝ => b₁ * (X (u + k) - x₀ - (a₁ * k + a₂ / 2 * k ^ 2))
        + b₂ * ((a₁ * k + a₂ / 2 * k ^ 2) * (X (u + k) - x₀ - (a₁ * k + a₂ / 2 * k ^ 2)))
        + b₂ / 2 * (X (u + k) - x₀ - (a₁ * k + a₂ / 2 * k ^ 2)) ^ 2
        + (b₂ * a₁ * a₂ / 2 * k ^ 3 + b₂ * a₂ ^ 2 / 8 * k ^ 4)) =o[𝓝 0] (fun k : ℝ => k ^ 2) :=
      ((h1.add h2).add h3).add hP
    refine hsum.congr' ?_ EventuallyEq.rfl
    filter_upwards with k
    ring
  have hAB := hA.add hB
  refine hAB.congr' ?_ EventuallyEq.rfl
  filter_upwards with k
  rw [hXx]
  rw [show x₀ + (X (u + k) - x₀) = X (u + k) from by ring]
  ring

end

end Work.OddCurve.LowSlope
