/-
# `C¹`/`C²` bounds for the fixed `g`-side profile `gProfile d k₂`

`Work.KMTAreas.A7.gProfile d k₂` is the fixed frequency profile of the `g`-side bump: for `k₂ = 0`
it is the KMT cutoff `η = kmtEta`, and for `k₂ ≥ 1` it is the differenced dilation
`η - η(2^d ·)`.  Both shapes are `C²` and vanish identically off `[-1,1]`.

This module records the consequences of that single structural fact, uniformly in `k₂`:

* `gProfile d k₂` is `C²`;
* `gProfile d k₂` and its first two derivatives are bounded by constants `M₀, M₁, M₂` independent
  of `k₂`;
* `gProfile d k₂` and its first two derivatives vanish for `|u| ≥ 1`;
* `gProfile d k₂` and `deriv (gProfile d k₂)` are differentiable everywhere with the expected
  derivatives (`deriv` and `iteratedDeriv 2`).

The work is done once and for all by the abstract lemma
`deriv_bounds_of_contDiff_vanishes`: a `C²` function of one real variable with compact support is
bounded with its first two derivatives, its derivatives vanish where the function does, and it is
differentiable with the expected iterated derivatives.  Uniformity in `k₂` is then free, because
the *set* of profiles `{gProfile d k₂ : k₂}` has just two elements: `η` and `η - η(2^d ·)`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.kmtEta_deriv_bounds
import Submission.Work.KMTAreas.A7.gProfile_facts

set_option autoImplicit false

namespace Work.KMTAreas.A7

open Work.KMTContract

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
first two derivatives; its first two derivatives vanish off `[-1,1]`; and it, and its derivative,
are differentiable everywhere with the expected derivatives.**

The bounds come from compactness of `[-1,1]` (where the three functions are continuous) combined
with the vanishing outside it. -/
private theorem deriv_bounds_of_contDiff_vanishes (g : ℝ → ℂ) (hcd : ContDiff ℝ 2 g)
    (hz : ∀ u : ℝ, 1 ≤ |u| → g u = 0) :
    ∃ (M0 M1 M2 : ℝ), 0 ≤ M0 ∧ 0 ≤ M1 ∧ 0 ≤ M2 ∧
      (∀ u : ℝ, ‖g u‖ ≤ M0) ∧
      (∀ u : ℝ, ‖deriv g u‖ ≤ M1) ∧
      (∀ u : ℝ, ‖iteratedDeriv 2 g u‖ ≤ M2) ∧
      (∀ u : ℝ, 1 ≤ |u| → deriv g u = 0) ∧
      (∀ u : ℝ, 1 ≤ |u| → iteratedDeriv 2 g u = 0) ∧
      (∀ u : ℝ, HasDerivAt g (deriv g u) u) ∧
      (∀ u : ℝ, HasDerivAt (deriv g) (iteratedDeriv 2 g u) u) := by
  have hcont0 : Continuous g := hcd.continuous
  have hcont1 : Continuous (deriv g) := hcd.continuous_deriv (by norm_num)
  have hcont2 : Continuous (iteratedDeriv 2 g) := hcd.continuous_iteratedDeriv 2 (by norm_num)
  obtain ⟨C0, hC0⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc (-1 : ℝ) 1) hcont0.continuousOn
  obtain ⟨C1, hC1⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc (-1 : ℝ) 1) hcont1.continuousOn
  obtain ⟨C2, hC2⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc (-1 : ℝ) 1) hcont2.continuousOn
  have hdiff : Differentiable ℝ g := hcd.differentiable (by norm_num)
  have hdiff1 : Differentiable ℝ (deriv g) := hcd.differentiable_deriv_two
  have hz1 : ∀ y : ℝ, 1 ≤ |y| → deriv g y = 0 := deriv_eq_zero_of_one_le_abs hz
  have hiter : iteratedDeriv 2 g = deriv (deriv g) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hz2 : ∀ y : ℝ, 1 ≤ |y| → iteratedDeriv 2 g y = 0 := by
    intro y hy
    rw [hiter]
    exact deriv_eq_zero_of_one_le_abs (fun z hzp => hz1 z hzp) y hy
  refine ⟨max C0 0, max C1 0, max C2 0, le_max_right _ _, le_max_right _ _, le_max_right _ _,
    ?_, ?_, ?_, hz1, hz2, ?_, ?_⟩
  · intro u
    by_cases hu : 1 ≤ |u|
    · rw [hz u hu, norm_zero]; exact le_max_right _ _
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
  · intro u
    exact (hdiff.differentiableAt (x := u)).hasDerivAt
  · intro u
    have h := (hdiff1.differentiableAt (x := u)).hasDerivAt
    rwa [← hiter] at h

/-- The KMT cutoff `η = kmtEta` is `C²`, being the complexification of a `ContDiffBump`. -/
private lemma contDiff_kmtEta : ContDiff ℝ 2 kmtEta := by
  show ContDiff ℝ 2 fun x : ℝ => ((kmtBump x : ℝ) : ℂ)
  exact Complex.ofRealCLM.contDiff.comp kmtBump.contDiff

/-- The differenced dilation `η - η(2^d ·)` is `C²`. -/
private lemma contDiff_kmtEta_diff (d : ℕ) :
    ContDiff ℝ 2 (fun u : ℝ => kmtEta u - kmtEta ((2 : ℝ) ^ d * u)) :=
  contDiff_kmtEta.sub (contDiff_kmtEta.comp (contDiff_const.mul contDiff_id))

/-- The differenced dilation `η - η(2^d ·)` vanishes for `|u| ≥ 1`. -/
private lemma kmtEta_diff_eq_zero (d : ℕ) :
    ∀ u : ℝ, 1 ≤ |u| → kmtEta u - kmtEta ((2 : ℝ) ^ d * u) = 0 := by
  intro u hu
  have hc1 : (1 : ℝ) ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
  have hcu : 1 ≤ |(2 : ℝ) ^ d * u| := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ d)]
    nlinarith [hc1, hu, abs_nonneg u]
  rw [kmtEta_zero hu, kmtEta_zero hcu, sub_self]

/-- **The profiles `gProfile d k₂` are uniformly `C²`, uniformly bounded with their first two
derivatives, vanish with their first two derivatives off `[-1,1]`, and are differentiable
everywhere with the expected derivatives.**

(The uniformity is free: `{gProfile d k₂ : k₂}` has just two elements, `η` and `η - η(2^d ·)`,
so the two sets of constants obtained from `deriv_bounds_of_contDiff_vanishes` are combined by
taking maxima.) -/
theorem gProfile_deriv_bounds (d : ℕ) :
    ∃ (M0 M1 M2 : ℝ), 0 ≤ M0 ∧ 0 ≤ M1 ∧ 0 ≤ M2 ∧
      ∀ k₂ : ℕ,
        ContDiff ℝ 2 (gProfile d k₂) ∧
        (∀ u : ℝ, ‖gProfile d k₂ u‖ ≤ M0) ∧
        (∀ u : ℝ, ‖deriv (gProfile d k₂) u‖ ≤ M1) ∧
        (∀ u : ℝ, ‖iteratedDeriv 2 (gProfile d k₂) u‖ ≤ M2) ∧
        (∀ u : ℝ, 1 ≤ |u| → gProfile d k₂ u = 0) ∧
        (∀ u : ℝ, 1 ≤ |u| → deriv (gProfile d k₂) u = 0) ∧
        (∀ u : ℝ, 1 ≤ |u| → iteratedDeriv 2 (gProfile d k₂) u = 0) ∧
        (∀ u : ℝ, HasDerivAt (gProfile d k₂) (deriv (gProfile d k₂) u) u) ∧
        (∀ u : ℝ, HasDerivAt (deriv (gProfile d k₂)) (iteratedDeriv 2 (gProfile d k₂) u) u) := by
  obtain ⟨A0, A1, A2, hA0nn, hA1nn, hA2nn, hAb0, hAb1, hAb2, hAz1, hAz2, hAd1, hAd2⟩ :=
    deriv_bounds_of_contDiff_vanishes kmtEta contDiff_kmtEta (fun u hu => kmtEta_zero hu)
  obtain ⟨B0, B1, B2, hB0nn, hB1nn, hB2nn, hBb0, hBb1, hBb2, hBz1, hBz2, hBd1, hBd2⟩ :=
    deriv_bounds_of_contDiff_vanishes (fun u : ℝ => kmtEta u - kmtEta ((2 : ℝ) ^ d * u))
      (contDiff_kmtEta_diff d) (kmtEta_diff_eq_zero d)
  refine ⟨max A0 B0, max A1 B1, max A2 B2, le_max_of_le_left hA0nn, le_max_of_le_left hA1nn,
    le_max_of_le_left hA2nn, ?_⟩
  intro k₂
  by_cases hk : k₂ = 0
  · subst hk
    have hg : gProfile d 0 = kmtEta := by
      rw [show gProfile d 0 = (if (0 : ℕ) = 0 then kmtEta else
          fun u : ℝ => kmtEta u - kmtEta ((2 : ℝ) ^ d * u)) from rfl, if_pos rfl]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hg]; exact contDiff_kmtEta
    · intro u; rw [hg]; exact le_trans (hAb0 u) (le_max_left A0 B0)
    · intro u; rw [hg]; exact le_trans (hAb1 u) (le_max_left A1 B1)
    · intro u; rw [hg]; exact le_trans (hAb2 u) (le_max_left A2 B2)
    · intro u hu; rw [hg]; exact kmtEta_zero hu
    · intro u hu; rw [hg]; exact hAz1 u hu
    · intro u hu; rw [hg]; exact hAz2 u hu
    · intro u; rw [hg]; exact hAd1 u
    · intro u; rw [hg]; exact hAd2 u
  · have hg : gProfile d k₂ = fun u : ℝ => kmtEta u - kmtEta ((2 : ℝ) ^ d * u) := by
      rw [show gProfile d k₂ = (if k₂ = 0 then kmtEta else
          fun u : ℝ => kmtEta u - kmtEta ((2 : ℝ) ^ d * u)) from rfl, if_neg hk]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hg]; exact contDiff_kmtEta_diff d
    · intro u; rw [hg]; exact le_trans (hBb0 u) (le_max_right A0 B0)
    · intro u; rw [hg]; exact le_trans (hBb1 u) (le_max_right A1 B1)
    · intro u; rw [hg]; exact le_trans (hBb2 u) (le_max_right A2 B2)
    · intro u hu; rw [hg]; exact kmtEta_diff_eq_zero d u hu
    · intro u hu; rw [hg]; exact hBz1 u hu
    · intro u hu; rw [hg]; exact hBz2 u hu
    · intro u; rw [hg]; exact hBd1 u
    · intro u; rw [hg]; exact hBd2 u

end Work.KMTAreas.A7
