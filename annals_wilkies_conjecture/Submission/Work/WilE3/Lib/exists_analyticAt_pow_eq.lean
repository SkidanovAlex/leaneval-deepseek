import Mathlib

namespace Work.WilE3.Lib

/-- A function analytic at `z₀` with nonzero value has an `N`-th root `v` (for `N ≠ 0`)
which is analytic at `z₀` with `v z₀ ≠ 0`.

The root is produced globally through `Complex.cpow`: writing `u z = m * (1 + g z)` with
`m = u z₀ ≠ 0` and `g z = u z / m - 1` (so `g z₀ = 0` and `1 + g z₀ = 1` lies in the slit
plane), the function `v z = a * (1 + g z) ^ ((N:ℂ)⁻¹)` with `a^N = m` satisfies `v z ^ N = u z`
for *every* `z`, while its analyticity at `z₀` follows from `AnalyticAt.cpow`. -/
theorem exists_analyticAt_pow_eq {u : ℂ → ℂ} {z₀ : ℂ} (hu : AnalyticAt ℂ u z₀)
    (hu0 : u z₀ ≠ 0) {N : ℕ} (hN : N ≠ 0) :
    ∃ v : ℂ → ℂ, AnalyticAt ℂ v z₀ ∧ v z₀ ≠ 0 ∧ ∀ z : ℂ, v z ^ N = u z := by
  set m : ℂ := u z₀ with hm
  have hm0 : m ≠ 0 := by rw [hm]; exact hu0
  set a : ℂ := m ^ ((N : ℂ)⁻¹) with ha
  have haN : a ^ N = m := by rw [ha]; exact Complex.cpow_nat_inv_pow m hN
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, zero_pow hN] at haN
    exact hm0 haN.symm
  set g : ℂ → ℂ := fun z => u z / m - 1 with hg
  have hg_an : AnalyticAt ℂ g z₀ := by
    rw [hg]; exact (hu.div_const).sub analyticAt_const
  have hgz : g z₀ = 0 := by
    rw [hg]; simp only; rw [← hm, div_self hm0]; ring
  have hgs : 1 + g z₀ ∈ Complex.slitPlane := by
    rw [hgz, add_zero]; exact Complex.one_mem_slitPlane
  refine ⟨fun z => a * (1 + g z) ^ ((N : ℂ)⁻¹), ?_, ?_, ?_⟩
  · exact analyticAt_const.mul (((analyticAt_const.add hg_an).cpow analyticAt_const) hgs)
  · show a * (1 + g z₀) ^ ((N : ℂ)⁻¹) ≠ 0
    rw [hgz, add_zero, Complex.one_cpow, mul_one]
    exact ha0
  · intro z
    calc (a * (1 + g z) ^ ((N : ℂ)⁻¹)) ^ N
        = a ^ N * ((1 + g z) ^ ((N : ℂ)⁻¹)) ^ N := by rw [mul_pow]
      _ = m * (1 + g z) := by rw [haN, Complex.cpow_nat_inv_pow _ hN]
      _ = u z := by
        rw [hg]; simp only
        field_simp
        ring

end Work.WilE3.Lib
