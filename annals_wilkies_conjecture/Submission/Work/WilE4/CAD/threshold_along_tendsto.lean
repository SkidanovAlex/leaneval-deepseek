/-
  WilE4 / CAD — the sign threshold of a family of real polynomials is uniform along a converging
  sequence of parameters.

  Given a family `Q : X → ℝ[y]` whose coefficients depend continuously on the parameter, a point
  `x₀`, and a sequence `a n → x₀`, suppose the degree of `Q x₀` and of every `Q (a n)` is the same
  `d`.  Then the single threshold `R` of "the sign of the value is the sign of the leading term"
  works for `x₀` and, eventually in `n`, for every `Q (a n)` simultaneously.

  The mathematical content is the classical domination of the leading term for large arguments.
  It is supplied by `sign_eval_of_coeff_bound` (in `CAD/sign_eval_abs_large.lean`), which needs a
  uniform coefficient upper bound `C` together with a uniform lower bound `ε` on the leading
  coefficient.  Such `C, ε` exist at `x₀` and eventually along the sequence by continuity of the
  coefficients (`eventually_coeff_bounds`, proved in `CAD/eventually_coeff_bounds.lean`).  The
  degree-`0` case is immediate, since then the polynomial is the constant `coeff 0`.
-/
import Mathlib
import Submission.Work.WilE4.CAD.sign_eval_abs_large
import Submission.Work.WilE4.CAD.eventually_coeff_bounds

namespace Work.WilE4.CAD

theorem threshold_along_tendsto {X : Type*} [TopologicalSpace X]
    (Q : X → Polynomial ℝ) (hcont : ∀ j, Continuous fun x => (Q x).coeff j)
    {x₀ : X} {a : ℕ → X} (ha : Filter.Tendsto a Filter.atTop (nhds x₀)) {d : ℕ}
    (hdeg₀ : (Q x₀).natDegree = d) (hdeg : ∀ n, (Q (a n)).natDegree = d) :
    ∃ R > 0,
      (∀ y : ℝ, R ≤ |y| → SignType.sign ((Q x₀).eval y)
        = SignType.sign ((Q x₀).coeff d) * SignType.sign y ^ d) ∧
      (∀ᶠ n in Filter.atTop, ∀ y : ℝ, R ≤ |y| →
        SignType.sign ((Q (a n)).eval y)
          = SignType.sign ((Q (a n)).coeff d) * SignType.sign y ^ d) := by
  by_cases hd0 : d = 0
  · -- Degree `0`: `Q z` is the constant polynomial `coeff 0`, for every `z`.  Any threshold works.
    subst hd0
    refine ⟨1, one_pos, ?_, ?_⟩
    · intro y _
      have hev : (Q x₀).eval y = (Q x₀).coeff 0 := by
        have h := Polynomial.eval_eq_sum_range (p := Q x₀) y
        rw [hdeg₀] at h
        simpa using h
      rw [hev, pow_zero, mul_one]
    · refine Filter.Eventually.of_forall fun n => ?_
      intro y _
      have hev : (Q (a n)).eval y = (Q (a n)).coeff 0 := by
        have h := Polynomial.eval_eq_sum_range (p := Q (a n)) y
        rw [hdeg n] at h
        simpa using h
      rw [hev, pow_zero, mul_one]
  · -- Degree `d ≥ 1`.
    have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd0
    -- The `d`-th coefficient at `x₀` is the leading coefficient, hence nonzero.
    have hne : (Q x₀).coeff d ≠ 0 := by
      have hp0 : Q x₀ ≠ 0 := by
        intro h0
        rw [h0, Polynomial.natDegree_zero] at hdeg₀
        omega
      rw [← hdeg₀, Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hp0
    -- Uniform coefficient bounds at `x₀` and eventually along the sequence.
    obtain ⟨C, ε, hC, hεpos, hbd₀, hc₀, hev⟩ := eventually_coeff_bounds Q hcont ha hne
    refine ⟨max 1 (2 * (d : ℝ) * C / ε),
      lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_, ?_⟩
    · -- At `x₀`.
      intro y hy
      exact sign_eval_of_coeff_bound hd1 hdeg₀ hC hεpos hbd₀ hc₀ hy
    · -- Eventually along the sequence.
      filter_upwards [hev] with n hn
      intro y hy
      exact sign_eval_of_coeff_bound hd1 (hdeg n) hC hεpos hn.1 hn.2 hy

end Work.WilE4.CAD
