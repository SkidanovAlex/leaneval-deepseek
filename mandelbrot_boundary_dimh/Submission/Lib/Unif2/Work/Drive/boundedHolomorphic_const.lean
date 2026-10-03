import Mathlib
import Submission.Lib.Unif2.Work.Drive.Interfaces
import Submission.Lib.Unif2.Work.Drive.unit_log_pole_at_every_point

namespace Work.Drive

/-- **Liouville for bounded holomorphic functions in the no-weak-Green case.** If `X` carries no
positive harmonic function with a unit logarithmic pole, then every bounded holomorphic function on
`X` is constant.

Route: given a bounded holomorphic `g`, normalise it (divide by `sup‖g‖ + 1`), choose a point `x₀`
where the chart derivative of `g` does not vanish (it exists unless `g` is constant) and compose
with the Möbius automorphism of the disc sending the value at `x₀` to `0`. The result `ψ` is a
member of `Submission.extremalFamily x₀`, non-zero, with a *simple* zero at `x₀`
(`Submission.HasLogPoleAt x₀ ψ`, from a non-vanishing chart derivative:
`Work.SimplyConnected.ABS.hasLogPoleAt_of_deriv_ne_zero`). Then
`Work.SimplyConnected.ABS.exists_posHarmonic_logPole_dominating'` (which is axiom-clean) produces a
positive harmonic function on `X ∖ {x₀}` with a unit log pole at `x₀`, i.e. `HasWeakGreen X`,
contradicting `hO`.

**Route actually formalised here** (no simple zero is needed, hence no Möbius transform and no
search for a point with non-vanishing chart derivative): if `g` is not constant, take any `y : X`
and put `h := (2K)⁻¹ · (g - g y)` with `K := max M 0 + 1`.  Then `h` is holomorphic, `h y = 0` and
`‖h‖ ≤ 1` (because `‖g - g y‖ ≤ 2 max M 0 ≤ 2K`), so `h ∈ Submission.extremalFamily y`, and `h` is
not the zero function because non-constancy gives an `x` with `g x ≠ g y`.  The member
`Work.Drive.unit_log_pole_at_every_point` — which handles a zero of *arbitrary* order `k ≥ 1` by
the local factorization `h ∘ c.symm = (· - c y)^k · ψ` and the barrier `-(1/k) log ‖h‖` — then
produces a positive harmonic function on `X ∖ {y}` with a unit logarithmic pole at `y`, i.e.
`HasWeakGreen X`, contradicting `hO`. -/
theorem boundedHolomorphic_const {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hO : ¬ Work.Drive.HasWeakGreen X) {g : X → ℂ}
    (hg : Submission.HolomorphicOnX g Set.univ) (hb : ∃ M : ℝ, ∀ x : X, ‖g x‖ ≤ M) :
    ∃ c : ℂ, ∀ x : X, g x = c := by
  by_contra hcon
  push Not at hcon
  -- `hcon : ∀ c : ℂ, ∃ x : X, g x ≠ c`
  obtain ⟨M, hM⟩ := hb
  obtain ⟨y⟩ : Nonempty X := inferInstance
  set K : ℝ := max M 0 + 1 with hKdef
  have hKpos : 0 < K := by rw [hKdef]; linarith [le_max_right M 0]
  have hMle : M ≤ max M 0 := le_max_left M 0
  have hMleK : max M 0 ≤ K := by rw [hKdef]; linarith
  have h2Kpos : (0 : ℝ) < 2 * K := by linarith
  -- the normalised translate `h` of `g`, a member of the extremal family at `y`
  let h : X → ℂ := fun x => (((2 * K : ℝ)) : ℂ)⁻¹ * (g x - g y)
  have hhne : ∃ x : X, h x ≠ 0 := by
    obtain ⟨x, hx⟩ := hcon (g y)
    refine ⟨x, ?_⟩
    have h1 : g x - g y ≠ 0 := sub_ne_zero.mpr hx
    have h2 : (((2 * K : ℝ)) : ℂ)⁻¹ ≠ 0 := by
      have h3 : (2 * K : ℝ) ≠ 0 := ne_of_gt h2Kpos
      simp only [ne_eq, inv_eq_zero, Complex.ofReal_eq_zero]
      exact h3
    exact mul_ne_zero h2 h1
  have hh0 : h y = 0 := by
    show (((2 * K : ℝ)) : ℂ)⁻¹ * (g y - g y) = 0
    rw [sub_self, mul_zero]
  have hhhol : Submission.HolomorphicOnX h Set.univ := by
    intro x hx
    have hsub : Submission.HolomorphicOnXAt (fun z => g z - g y) x :=
      (hg x hx).sub (Submission.holomorphicOnXAt_const (g y) x)
    exact Submission.HolomorphicOnXAt.const_mul _ hsub
  have hhb : ∀ x : X, ‖h x‖ ≤ 1 := by
    intro x
    have h1 : ‖g x - g y‖ ≤ 2 * K := by
      have hx1 : ‖g x‖ ≤ max M 0 := le_trans (hM x) hMle
      have hy1 : ‖g y‖ ≤ max M 0 := le_trans (hM y) hMle
      calc ‖g x - g y‖ ≤ ‖g x‖ + ‖g y‖ := norm_sub_le _ _
        _ ≤ max M 0 + max M 0 := add_le_add hx1 hy1
        _ = 2 * max M 0 := by ring
        _ ≤ 2 * K := by linarith
    have h2 : ‖h x‖ = (2 * K)⁻¹ * ‖g x - g y‖ := by
      show ‖(((2 * K : ℝ)) : ℂ)⁻¹ * (g x - g y)‖ = _
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h2Kpos]
    rw [h2]
    calc (2 * K)⁻¹ * ‖g x - g y‖ ≤ (2 * K)⁻¹ * (2 * K) :=
          mul_le_mul_of_nonneg_left h1 (le_of_lt (inv_pos.mpr h2Kpos))
      _ = 1 := inv_mul_cancel₀ (ne_of_gt h2Kpos)
  have hmem : h ∈ Submission.extremalFamily y := ⟨hhhol, hhb, hh0⟩
  obtain ⟨E, hEpos, hEharm, hEpole⟩ := Work.Drive.unit_log_pole_at_every_point hmem hhne
  exact hO ⟨y, E, hEpos, hEharm, hEpole⟩

end Work.Drive
