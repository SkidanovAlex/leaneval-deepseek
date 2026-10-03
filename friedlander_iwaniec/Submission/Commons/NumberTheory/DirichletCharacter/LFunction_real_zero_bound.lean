import Mathlib.Data.FunLike.Fintype
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Real zeros of `L(·, χ)` stay away from `1`

For a fixed primitive Dirichlet character `χ` modulo `N`, the function `s ↦ L(s, χ)` does not
vanish in a whole complex neighbourhood of `s = 1`: either `χ` is non-principal, in which case
`L(1, χ) ≠ 0` (`DirichletCharacter.LFunction_apply_one_ne_zero`) and `L(·, χ)` is entire, so
continuity gives a ball around `1` free of zeros; or `χ` is principal, which forces `N = 1`
(principality means `conductor χ = 1`, and `χ.IsPrimitive` means `conductor χ = N`), and then
`L(·, χ) = ζ` is eventually non-zero near `1` because of the pole of `ζ` at `1`
(`riemannZeta_eventually_ne_zero_nhds_one`).

Consequently the real zeros of `L(·, χ)` in `(0,1)` are bounded away from `1` by a positive
constant `ε` depending only on `χ` (and `N`), and hence satisfy `ε ≤ 1 - β`. Writing
`ε = c / N^K` with `c = ε * N` and `K = 1` gives the statement below.

Note the quantifier structure of the statement: `N` and `χ` are *parameters*, so the constants
`c` and `K` are allowed to depend on them.  The (much deeper, uniform in `N`) statement in which
`c` and `K` are absolute constants is the classical upper bound for a Siegel zero and needs the
class number formula (or Siegel's theorem); it is not what is formalised here.
-/

namespace Commons.NumberTheory.DirichletCharacter

/-- For a primitive Dirichlet character `χ` modulo `N`, the function `L(·, χ)` is
non-vanishing on a ball around `1`.

This is the elementary half of the zero-free region at the edge `σ = 1`: `L(1, χ) ≠ 0` for a
non-principal character (`DirichletCharacter.LFunction_apply_one_ne_zero`), while the principal
character is primitive only at level `1`, where `L(·, 1) = ζ` and the pole of `ζ` at `1` keeps
it away from `0`.  It also gives that the real zeros of `L(·, χ)` in `(0,1)` are bounded below
by a positive constant depending on `χ`. -/
theorem LFunction_ne_zero_near_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχprim : χ.IsPrimitive) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℂ, dist s 1 < ε → DirichletCharacter.LFunction χ s ≠ 0 := by
  by_cases hχ1 : χ = 1
  · -- the principal character: primitivity forces `N = 1`, and then `L(·, χ) = ζ`
    have hcond : χ.conductor = N := hχprim
    rw [hχ1, DirichletCharacter.conductor_one] at hcond
    have hN1 : N = 1 := hcond.symm
    subst hN1
    have hL : DirichletCharacter.LFunction χ = riemannZeta :=
      DirichletCharacter.LFunction_modOne_eq
    obtain ⟨ε, hε, hε'⟩ :=
      Metric.eventually_nhds_iff.mp riemannZeta_eventually_ne_zero_nhds_one
    exact ⟨ε, hε, fun s hs => by rw [hL]; exact hε' hs⟩
  · -- the non-principal character: `L(1, χ) ≠ 0` and `L(·, χ)` is entire
    have hdiff : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
      DirichletCharacter.differentiable_LFunction hχ1
    have hL1 : DirichletCharacter.LFunction χ 1 ≠ 0 :=
      DirichletCharacter.LFunction_apply_one_ne_zero hχ1
    have hnorm : 0 < ‖DirichletCharacter.LFunction χ (1 : ℂ)‖ := norm_pos_iff.mpr hL1
    obtain ⟨ε, hε, hε'⟩ := Metric.continuousAt_iff.mp hdiff.continuous.continuousAt
      (‖DirichletCharacter.LFunction χ (1 : ℂ)‖ / 2) (by linarith)
    exact ⟨ε, hε, fun s hs => by
      intro hz
      have h2 := hε' hs
      rw [hz, dist_eq_norm, zero_sub, norm_neg] at h2
      linarith⟩

theorem LFunction_real_zero_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχprim : χ.IsPrimitive) :
    ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, 0 < K ∧ ∀ β : ℝ, 0 < β → β < 1 →
      DirichletCharacter.LFunction χ (β : ℂ) = 0 → c / (N : ℝ) ^ K ≤ 1 - β := by
  obtain ⟨ε, hε, hkey⟩ := LFunction_ne_zero_near_one χ hχprim
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  refine ⟨ε * (N : ℝ), mul_pos hε hNpos, 1, one_pos, ?_⟩
  intro β hβ0 hβ1 hzero
  have hsimp : ε * (N : ℝ) / (N : ℝ) ^ (1 : ℝ) = ε := by
    rw [Real.rpow_one, mul_div_assoc, div_self (ne_of_gt hNpos), mul_one]
  rw [hsimp]
  by_contra hcon
  push Not at hcon
  have hdist : dist (β : ℂ) (1 : ℂ) < ε := by
    rw [Complex.dist_eq]
    have hsub : (β : ℂ) - (1 : ℂ) = ((β - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    linarith
  exact hkey (β : ℂ) hdist hzero

end Commons.NumberTheory.DirichletCharacter