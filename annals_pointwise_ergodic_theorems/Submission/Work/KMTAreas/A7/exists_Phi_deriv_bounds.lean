import Mathlib

/-!
# `C²`-bounds for a `C²` function of one real variable vanishing off `[-1,1]`

For the KMT areas we repeatedly need the following elementary analytic fact: a `C²` function
`Φ : ℝ → ℂ` which vanishes for `|u| ≥ 1` is bounded, together with its first two derivatives,
by nonnegative constants `M₀, M₁, M₂`, and its first two derivatives themselves vanish for
`|u| ≥ 1`.

* Boundedness on `[-1,1]` is compactness (`IsCompact.exists_bound_of_continuousOn`) applied to
  the three continuous functions `Φ`, `deriv Φ = iteratedDeriv 1 Φ` and
  `iteratedDeriv 2 Φ`; outside `[-1,1]` everything is `0`.
* The vanishing of `deriv Φ` at the *boundary* points `u = ±1` (where `Φ` is not locally zero, so
  the usual `EventuallyEq.deriv_eq` does not apply) is handled by the one-sided argument
  `HasDerivWithinAt.deriv_eq_zero` on the halfline `Set.Ici u` (for `u ≥ 1`) and `Set.Iic u`
  (for `u ≤ -1`): `Φ` vanishes on the halfline on the side where it is forced to, and a function
  vanishing on a halfline starting at `u` has derivative `0` there.
* The same one-sided argument applied to `deriv Φ` gives the vanishing of `iteratedDeriv 2 Φ`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.KMTAreas.A7

/-- A function `f : ℝ → ℂ` which vanishes on the halfline `[1, ∞)` *and* on `(-∞, -1]` has
`deriv f y = 0` for every `|y| ≥ 1`.  (Choosing the halfline on the appropriate side of `y` and
using `HasDerivWithinAt.deriv_eq_zero` avoids any differentiability hypothesis.) -/
private lemma deriv_eq_zero_of_one_le_abs {f : ℝ → ℂ} (h : ∀ z : ℝ, 1 ≤ |z| → f z = 0) :
    ∀ y : ℝ, 1 ≤ |y| → deriv f y = 0 := by
  intro y hy
  rcases le_or_gt 0 y with hy0 | hy0
  · have hy1 : (1 : ℝ) ≤ y := by rwa [abs_of_nonneg hy0] at hy
    refine HasDerivWithinAt.deriv_eq_zero ?_ (uniqueDiffWithinAt_Ici y)
    refine (hasDerivWithinAt_const y (Set.Ici y) (0 : ℂ)).congr (fun z hz => ?_) (h y hy)
    have hzy : y ≤ z := hz
    exact h z (by rw [abs_of_nonneg (by linarith)]; linarith)
  · have hy1 : y ≤ -1 := by
      have hy' : |y| = -y := abs_of_neg hy0
      linarith
    refine HasDerivWithinAt.deriv_eq_zero ?_ (uniqueDiffWithinAt_Iic y)
    refine (hasDerivWithinAt_const y (Set.Iic y) (0 : ℂ)).congr (fun z hz => ?_) (h y hy)
    have hzy : z ≤ y := hz
    exact h z (by rw [abs_of_nonpos (by linarith)]; linarith)

/-- **A `C²` function of one real variable vanishing off `[-1,1]` is bounded, together with its
first two derivatives, and its first two derivatives vanish off `[-1,1]`.**

The bounds come from compactness of `[-1,1]` (where the three functions are continuous) combined
with the vanishing outside it. -/
theorem exists_Phi_deriv_bounds {Φ : ℝ → ℂ} (hΦcd : ContDiff ℝ 2 Φ)
    (hΦsupp : ∀ u : ℝ, 1 ≤ |u| → Φ u = 0) :
    ∃ M0 M1 M2 : ℝ, 0 ≤ M0 ∧ 0 ≤ M1 ∧ 0 ≤ M2 ∧
      (∀ u : ℝ, ‖Φ u‖ ≤ M0) ∧ (∀ u : ℝ, ‖deriv Φ u‖ ≤ M1) ∧
      (∀ u : ℝ, ‖iteratedDeriv 2 Φ u‖ ≤ M2) ∧
      (∀ u : ℝ, 1 ≤ |u| → deriv Φ u = 0) ∧ (∀ u : ℝ, 1 ≤ |u| → iteratedDeriv 2 Φ u = 0) := by
  have hcont0 : Continuous Φ := hΦcd.continuous
  have hcont1 : Continuous (deriv Φ) := hΦcd.continuous_deriv (by norm_num)
  have hcont2 : Continuous (iteratedDeriv 2 Φ) := hΦcd.continuous_iteratedDeriv 2 (by norm_num)
  -- bound the three functions on the compact set `[-1,1]`
  obtain ⟨C0, hC0⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc (-1 : ℝ) 1) hcont0.continuousOn
  obtain ⟨C1, hC1⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc (-1 : ℝ) 1) hcont1.continuousOn
  obtain ⟨C2, hC2⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc (-1 : ℝ) 1) hcont2.continuousOn
  -- the first derivative vanishes off `[-1,1]`
  have hz1 : ∀ y : ℝ, 1 ≤ |y| → deriv Φ y = 0 := deriv_eq_zero_of_one_le_abs hΦsupp
  -- `iteratedDeriv 2 Φ = deriv (deriv Φ)`
  have hiter : iteratedDeriv 2 Φ = deriv (deriv Φ) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hz2 : ∀ y : ℝ, 1 ≤ |y| → iteratedDeriv 2 Φ y = 0 := by
    intro y hy
    rw [hiter]
    exact deriv_eq_zero_of_one_le_abs (fun z hzp => hz1 z hzp) y hy
  refine ⟨max C0 0, max C1 0, max C2 0, le_max_right _ _, le_max_right _ _, le_max_right _ _,
    ?_, ?_, ?_, hz1, hz2⟩
  · intro u
    by_cases hu : 1 ≤ |u|
    · rw [hΦsupp u hu, norm_zero]; exact le_max_right _ _
    · exact le_trans (hC0 u (Set.mem_Icc.mpr (abs_le.mp (le_of_lt (not_le.mp hu)))))
        (le_max_left _ _)
  · intro u
    by_cases hu : 1 ≤ |u|
    · rw [hz1 u hu, norm_zero]; exact le_max_right _ _
    · exact le_trans (hC1 u (Set.mem_Icc.mpr (abs_le.mp (le_of_lt (not_le.mp hu)))))
        (le_max_left _ _)
  · intro u
    by_cases hu : 1 ≤ |u|
    · rw [hz2 u hu, norm_zero]; exact le_max_right _ _
    · exact le_trans (hC2 u (Set.mem_Icc.mpr (abs_le.mp (le_of_lt (not_le.mp hu)))))
        (le_max_left _ _)

end Work.KMTAreas.A7
