import Mathlib

namespace Work.RPB.B1

/-- If a continuous real-valued function `ψ` satisfies `exp (ψ s * I) = 1` for all `s`,
then `ψ` is constant. Indeed every value of `ψ` is an integer multiple of `2π`, and a
continuous integer-valued function on a connected interval is constant. -/
theorem eq_const_of_exp_mul_I_eq_one {ψ : ℝ → ℝ} (hψ : Continuous ψ)
    (h : ∀ s, Complex.exp ((ψ s : ℂ) * Complex.I) = 1) : ∀ s, ψ s = ψ 0 := by
  -- Every value of `ψ` is an integer multiple of `2 * π`.
  have hmem : ∀ s, ∃ n : ℤ, ψ s = 2 * Real.pi * n := by
    intro s
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp (h s)
    refine ⟨n, ?_⟩
    have h2 : (ψ s : ℂ) * Complex.I = ((n : ℂ) * (2 * Real.pi)) * Complex.I := by
      rw [hn]; ring
    have h3 : (ψ s : ℂ) = (n : ℂ) * (2 * Real.pi) :=
      mul_right_cancel₀ Complex.I_ne_zero h2
    have h4 : (ψ s : ℂ) = Complex.ofReal ((n : ℝ) * (2 * Real.pi)) := by
      rw [h3]; push_cast; ring
    have h5 := Complex.ofReal_injective h4
    rw [h5]; ring
  -- Divide by `2 * π`: now the function is continuous and takes integer values.
  let u : ℝ → ℝ := fun s => ψ s / (2 * Real.pi)
  have hucont : Continuous u := hψ.div_const _
  have huint : ∀ s, ∃ n : ℤ, u s = (n : ℝ) := by
    intro s
    obtain ⟨n, hn⟩ := hmem s
    refine ⟨n, ?_⟩
    show ψ s / (2 * Real.pi) = (n : ℝ)
    rw [hn]
    have h2π : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    field_simp
  -- An integer-valued continuous function on an interval cannot be strictly increasing.
  have no_lt : ∀ {a b : ℝ}, a ≤ b → ¬ (u a < u b) := by
    intro a b hab hlt
    obtain ⟨n0, hn0⟩ := huint a
    obtain ⟨n1, hn1⟩ := huint b
    have hnat : n0 < n1 := by
      by_contra hc
      push_neg at hc
      have : (n1 : ℝ) ≤ (n0 : ℝ) := by exact_mod_cast hc
      linarith
    have hstep : u a + 1 ≤ u b := by
      have hz : n0 + 1 ≤ n1 := by omega
      have : (n0 : ℝ) + 1 ≤ (n1 : ℝ) := by exact_mod_cast hz
      linarith
    have hy1 : u a + 1 / 2 ∈ Set.Icc (u a) (u b) := ⟨by linarith, by linarith⟩
    obtain ⟨t, ht, hty⟩ := intermediate_value_Icc hab hucont.continuousOn hy1
    obtain ⟨n2, hn2⟩ := huint t
    have key : (n2 : ℝ) = (n0 : ℝ) + 1 / 2 := by linarith
    have h3 : (2 * n2 : ℤ) = 2 * n0 + 1 := by
      have : ((2 * n2 : ℤ) : ℝ) = ((2 * n0 + 1 : ℤ) : ℝ) := by push_cast; linarith
      exact Int.cast_injective this
    omega
  -- Nor strictly decreasing.
  have no_gt : ∀ {a b : ℝ}, a ≤ b → ¬ (u b < u a) := by
    intro a b hab hlt
    obtain ⟨n0, hn0⟩ := huint a
    obtain ⟨n1, hn1⟩ := huint b
    have hnat : n1 < n0 := by
      by_contra hc
      push_neg at hc
      have : (n0 : ℝ) ≤ (n1 : ℝ) := by exact_mod_cast hc
      linarith
    have hstep : u b + 1 ≤ u a := by
      have hz : n1 + 1 ≤ n0 := by omega
      have : (n1 : ℝ) + 1 ≤ (n0 : ℝ) := by exact_mod_cast hz
      linarith
    have hy1 : u b + 1 / 2 ∈ Set.Icc (u b) (u a) := ⟨by linarith, by linarith⟩
    obtain ⟨t, ht, hty⟩ := intermediate_value_Icc' hab hucont.continuousOn hy1
    obtain ⟨n2, hn2⟩ := huint t
    have key : (n2 : ℝ) = (n1 : ℝ) + 1 / 2 := by linarith
    have h3 : (2 * n2 : ℤ) = 2 * n1 + 1 := by
      have : ((2 * n2 : ℤ) : ℝ) = ((2 * n1 + 1 : ℤ) : ℝ) := by push_cast; linarith
      exact Int.cast_injective this
    omega
  have le_all : ∀ a b : ℝ, u a ≤ u b := by
    intro a b
    rcases le_total a b with hle | hle
    · exact le_of_not_gt (no_gt hle)
    · exact le_of_not_gt (no_lt hle)
  intro s
  have huv : u s = u 0 := le_antisymm (le_all s 0) (le_all 0 s)
  have h2π : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hdiv : ψ s / (2 * Real.pi) = ψ 0 / (2 * Real.pi) := huv
  exact mul_right_cancel₀ (inv_ne_zero h2π) (by simpa only [div_eq_mul_inv] using hdiv)

end Work.RPB.B1
