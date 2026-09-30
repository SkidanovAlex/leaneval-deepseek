import Mathlib
import Submission.Commons.NumberTheory.Linnik.completedL_pf_identity_rect

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Complex DirichletCharacter Metric Filter Topology
open scoped Real BigOperators Topology
set_option autoImplicit false
noncomputable section

namespace Commons.NumberTheory.Linnik

/-- `1/(0-u) + 1/u = 0` for every `u : ℂ` (field convention `1/0 = 0`). -/
private lemma kernel_at_zero (u : ℂ) : (1 : ℂ) / ((0 : ℂ) - u) + 1 / u = 0 := by
  by_cases h : u = 0
  · subst u
    simp
  · have hu : u ≠ 0 := h
    field_simp [hu]
    ring

/-- The divisor sum at `s = 0` vanishes identically (each summand has factor `0`). -/
private lemma divSum_zero_apply {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (R : ℝ) :
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / ((0 : ℂ) - u) + 1 / u)) = 0 := by
  classical
  have hterm : ∀ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / ((0 : ℂ) - u) + 1 / u) = 0 := by
    intro u
    rw [kernel_at_zero u]
    simp
  rw [show (fun u : ℂ => (((MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
        (1 / ((0 : ℂ) - u) + 1 / u)) = fun _ : ℂ => (0 : ℂ) by
      funext u
      exact hterm u]
  simp

/--
**Partial-fraction identity for the completed Dirichlet L-function.**  For a primitive
non-trivial character `χ` (with `Λ = completedLFunction χ`), the divisor-weighted sums

    Σ_{|u| ≤ R} ord_Λ(u) · (1/(s-u) + 1/u)

converge as `R → ∞` to the logarithmic-derivative difference
`Λ'(s)/Λ(s) − Λ'(0)/Λ(0)` whenever `Λ(s) ≠ 0`.

This is the exact-value form of the Hadamard partial-fraction expansion
(`completedL_pf_identity_rect` gives the same limit with an unknown constant `B`;
evaluating at `s = 0` — where every divisor sum vanishes — identifies
`B = Λ'(0)/Λ(0)`).
-/
theorem partialFraction_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (s : ℂ) :
    DirichletCharacter.completedLFunction χ s ≠ 0 →
      Tendsto (fun R : ℝ =>
        (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) + 1 / u)))
        atTop (nhds (deriv (DirichletCharacter.completedLFunction χ) s /
          DirichletCharacter.completedLFunction χ s -
          deriv (DirichletCharacter.completedLFunction χ) 0 /
            DirichletCharacter.completedLFunction χ 0)) := by
  intro hΛs
  -- partial-fraction identity with an unknown constant B (Hadamard, genus one)
  rcases Commons.NumberTheory.Linnik.completedL_pf_identity_rect χ hχ hχprim with ⟨B, hpf⟩
  have hΛ0 : DirichletCharacter.completedLFunction χ 0 ≠ 0 :=
    Commons.NumberTheory.Linnik.completedLFunction_zero_ne_zero χ hχ hχprim
  -- evaluate the identity at s = 0; the divisor sum is then identically 0
  have hpf0 : Tendsto (fun R : ℝ =>
        (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / ((0 : ℂ) - u) + 1 / u)))
      atTop (𝓝 (deriv (DirichletCharacter.completedLFunction χ) 0 /
          DirichletCharacter.completedLFunction χ 0 - B)) := by
    simpa using hpf 0 hΛ0
  have hz0 : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop
      (𝓝 (deriv (DirichletCharacter.completedLFunction χ) 0 /
        DirichletCharacter.completedLFunction χ 0 - B)) := by
    refine hpf0.congr' ?_
    filter_upwards with R
    exact divSum_zero_apply χ R
  have hident0 : deriv (DirichletCharacter.completedLFunction χ) 0 /
        DirichletCharacter.completedLFunction χ 0 - B = 0 := by
    exact tendsto_nhds_unique hz0 (tendsto_const_nhds (x := (0 : ℂ)))
  have hB : B = deriv (DirichletCharacter.completedLFunction χ) 0 /
      DirichletCharacter.completedLFunction χ 0 := (eq_of_sub_eq_zero hident0).symm
  -- the identity at the given point s, with the constant identified
  have hpf_s : Tendsto (fun R : ℝ =>
        (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) + 1 / u)))
      atTop (𝓝 (deriv (DirichletCharacter.completedLFunction χ) s /
        DirichletCharacter.completedLFunction χ s - B)) := by
    simpa using hpf s hΛs
  simpa [hB] using hpf_s

end Commons.NumberTheory.Linnik
