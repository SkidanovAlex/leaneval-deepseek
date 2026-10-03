import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.NumberTheory.LSeries.Nonvanishing

set_option linter.unusedVariables false

namespace Commons.NumberTheory.DirichletCharacter

open Filter Set Metric
open scoped Topology

/-- The set of non-trivial zeros of a primitive non-trivial Dirichlet L-function with
`|Im rho| <= T` is finite, so the corresponding `finsum` over the set of zeros is an honest
finite sum. -/
theorem lFunction_zeroSet_box_finite {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (T : ℝ) :
    ({ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}).Finite := by
  set f : ℂ → ℂ := DirichletCharacter.LFunction χ with hf
  set S : Set ℂ := {ρ : ℂ | f ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} with hS
  rw [← Set.not_infinite]
  intro hInf
  -- The zero set lies in a closed ball, which is compact.
  have hsub : S ⊆ Metric.closedBall (0 : ℂ) (1 + |T|) := by
    intro z hz
    obtain ⟨hz0, hre0, hre1, him⟩ := hz
    rw [Metric.mem_closedBall, dist_zero_right]
    have hT : 0 ≤ T := le_trans (abs_nonneg _) him
    have h1 : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    have hre : |z.re| ≤ 1 := by
      rw [abs_of_pos hre0]; exact le_of_lt hre1
    have him' : |z.im| ≤ |T| := by rw [abs_of_nonneg hT]; exact him
    linarith
  -- An infinite subset of a compact set has an accumulation point.
  obtain ⟨x, -, hacc⟩ := hInf.exists_accPt_of_subset_isCompact
    (isCompact_closedBall (0 : ℂ) (1 + |T|)) hsub
  rw [accPt_iff_frequently_nhdsNE] at hacc
  have hfreq : ∃ᶠ y in 𝓝[≠] x, f y = 0 := hacc.mono fun y hy => hy.1
  -- By the identity theorem, `f` vanishes identically on `ℂ`.
  have hf_an : AnalyticOnNhd ℂ f Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (by rw [hf]; exact DirichletCharacter.differentiable_LFunction hχ)
  have hzero : Set.EqOn f 0 Set.univ :=
    AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero hf_an isPreconnected_univ
      (mem_univ x) hfreq
  have h2 : f 2 = 0 := by simpa using hzero (mem_univ 2)
  have hne : f 2 ≠ 0 := by
    rw [hf]
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by norm_num)
  exact hne h2

end Commons.NumberTheory.DirichletCharacter