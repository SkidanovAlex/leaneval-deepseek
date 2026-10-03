import Mathlib

open Filter
open scoped Topology

namespace Work.FIArea6Hecke.R

/-- **The real zeros of a nonzero entire function in `(0,1)` are bounded away from `1`.**  Unlike
the classical *quantitative* real-zero bounds this needs no arithmetic: the zero set of a nonzero
entire function is discrete, so the zeros in `(0,1)` cannot accumulate at `1`.  It is what turns
`ZFRrealAxis`'s case analysis into a valid `c`: for the exceptional character `χ₁` one takes for
`β₁` the largest real zero of its completion in `(0,1)`, and the statement supplies the strict
positivity `1 - β₁ > 0` of the gap.  (Used together with `Work.FIArea6Hecke.R.Lam_one_ne_zero`,
which excludes a zero at `s = 1` itself, so that no real zero of `Lam` lies in `(β₁, 1]`.)
A proof: if the zeros of `Lam` in `(0,1)` had no strict upper bound, there would be a
point `p ∈ [0,1]` where `Lam` vanishes to infinite order; by
`AnalyticAt.eventually_eq_zero_or_eventually_ne_zero` and the uniqueness of analytic functions
this forces `Lam ≡ 0`, contradicting `hne`; hence the (closed, discrete) zero set meets `(0,1)` in
a finite set whose maximum is `< 1`. -/
theorem real_zeros_bounded_above {Lam : ℂ → ℂ} (hAn : AnalyticOn ℂ Lam Set.univ)
    (hne : ∃ s : ℂ, 0 < s.re ∧ Lam s ≠ 0) :
    ∃ β₁ : ℝ, β₁ < 1 ∧ ∀ β : ℝ, 0 < β → β < 1 → Lam (β : ℂ) = 0 → β ≤ β₁ := by
  -- Argue by contradiction: if no strict upper bound exists, zeros of `Lam` accumulate at `1`.
  by_contra h
  push Not at h
  -- `h : ∀ β₁ < 1, ∃ β, 0 < β ∧ β < 1 ∧ Lam ↑β = 0 ∧ β₁ < β`
  -- Hence `Lam` vanishes frequently in the punctured neighbourhood of `1`.
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ), Lam z = 0 := by
    by_contra hcon
    rw [not_frequently] at hcon
    rw [eventually_nhdsWithin_iff] at hcon
    rw [Metric.eventually_nhds_iff] at hcon
    obtain ⟨ε, hεpos, hε⟩ := hcon
    -- A zero strictly to the right of `1 - ε/4` lies within distance `ε` of `1`.
    obtain ⟨β, _hβ0, hβlt1, hβzero, hβgt⟩ := h (1 - ε / 4) (by linarith)
    have hdist : dist (β : ℂ) 1 < ε := by
      have h1 : (1 : ℂ) = ((1 : ℝ) : ℂ) := by simp
      rw [h1, Complex.isometry_ofReal.dist_eq, Real.dist_eq]
      rw [abs_of_neg (by linarith : β - 1 < 0)]
      linarith
    have hne1 : (β : ℂ) ≠ 1 := by
      intro hh
      have : β = 1 := by exact_mod_cast hh
      linarith
    exact hε hdist (by simpa using hne1) hβzero
  obtain ⟨s, _hsre, hsne⟩ := hne
  -- The identity theorem upgrades frequent vanishing near `1` to `Lam ≡ 0`.
  have hzero : Lam = 0 := by
    have hNhd : AnalyticOnNhd ℂ Lam Set.univ :=
      (isOpen_univ.analyticOn_iff_analyticOnNhd).mp hAn
    have hEqOn := hNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero
      isPreconnected_univ (trivial : (1 : ℂ) ∈ (Set.univ : Set ℂ)) hfreq
    funext z
    exact hEqOn (trivial : z ∈ (Set.univ : Set ℂ))
  exact hsne (congrFun hzero s)

end Work.FIArea6Hecke.R
