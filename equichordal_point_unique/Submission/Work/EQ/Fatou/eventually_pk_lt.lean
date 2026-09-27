import Mathlib
import Submission.Work.EQ.FatouDefs

/-!
# Uniform smallness of the angle Poisson kernel away from `ψ = 0`

`Work.EQ.pk r ψ = (1 - r²)/(1 - 2 r cos ψ + r²)` is the Poisson kernel for the unit disc in
its angular form.  As `r → 1⁻` the numerator tends to `0` while, for `ψ` bounded away from `0`,
the denominator stays bounded below by `2 (1 - cos δ) > 0`.  Hence `pk r ψ → 0` **uniformly**
for `ψ ∈ [δ, π]`, `δ > 0`: this is the lemma `eventually_pk_lt` below.

This is the "concentration of the Poisson kernel near `ψ = 0`" input used in the Fatou /
F. and M. Riesz development: outside any neighbourhood of the singular direction the kernel is
eventually smaller than any prescribed `ε`.
-/

namespace Work.EQ.Fatou

open Filter Set

/-- `1 - cos δ > 0` for `δ ∈ (0, π]`. -/
private lemma one_sub_cos_pos {δ : ℝ} (hδ : 0 < δ) (hδπ : δ ≤ Real.pi) :
    0 < 1 - Real.cos δ := by
  have h : Real.cos δ < Real.cos 0 :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl (0:ℝ)) hδπ hδ
  simpa using h

/-- **Uniform smallness of the Poisson kernel off the singular direction.**
For every `δ > 0` and every `ε > 0`, for all `r` close enough to `1` from below and every
`ψ ∈ [δ, π]` one has `pk r ψ < ε`. -/
theorem eventually_pk_lt (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ r in (nhdsWithin (1:ℝ) (Set.Iio 1)), ∀ ψ ∈ Set.Icc δ Real.pi, Work.EQ.pk r ψ < ε := by
  by_cases hcase : Real.pi < δ
  · -- the interval `[δ, π]` is empty
    have hempty : Set.Icc δ Real.pi = ∅ := Set.Icc_eq_empty (not_le.mpr hcase)
    simp [hempty]
  · push Not at hcase
    have hcpos : 0 < 1 - Real.cos δ := one_sub_cos_pos hδ hcase
    -- the threshold: `1 - r < m` forces `pk r ψ < ε` for every `ψ ∈ [δ, π]`
    set m : ℝ := min (1/2) (ε * (1 - Real.cos δ) / 4) with hm
    have hmpos : 0 < m := lt_min (by norm_num) (by positivity)
    have hmle1 : m ≤ (1:ℝ)/2 := min_le_left _ _
    have hmle2 : m ≤ ε * (1 - Real.cos δ) / 4 := min_le_right _ _
    rw [eventually_nhdsWithin_iff]
    refine Filter.mem_of_superset
      (isOpen_Ioo.mem_nhds
        (show (1:ℝ) ∈ Set.Ioo (1-m) (1+m) from ⟨by linarith, by linarith⟩)) ?_
    · intro r hr hrlt
      have hr1 : r < 1 := hrlt
      have hrpos : 0 < r := by linarith [hr.1, hmle1]
      have hr12 : (1:ℝ)/2 < r := by linarith [hr.1, hmle1]
      have hrm : 1 - r < m := by linarith [hr.1]
      intro ψ hψ
      have hψ1 : δ ≤ ψ := hψ.1
      have hψ2 : ψ ≤ Real.pi := hψ.2
      -- monotonicity of `cos` on `[0, π]`
      have hcos : Real.cos ψ ≤ Real.cos δ :=
        Real.cos_le_cos_of_nonneg_of_le_pi (le_of_lt hδ) hψ2 hψ1
      unfold Work.EQ.pk
      set D : ℝ := 1 - 2 * r * Real.cos ψ + r ^ 2 with hD
      -- the denominator is bounded below by `2 r (1 - cos δ)`, hence by `1 - cos δ`
      have hDgt : 1 - Real.cos δ < D := by
        have h1 : 1 - 2 * r * Real.cos δ + r ^ 2 ≤ 1 - 2 * r * Real.cos ψ + r ^ 2 := by
          nlinarith [hcos, hrpos]
        have h2 : 2 * r * (1 - Real.cos δ) ≤ 1 - 2 * r * Real.cos δ + r ^ 2 := by
          nlinarith [sq_nonneg (1 - r)]
        have h3 : 1 - Real.cos δ < 2 * r * (1 - Real.cos δ) := by
          nlinarith [hcpos, hr12]
        rw [hD]
        linarith
      have hDpos : 0 < D := by linarith [hDgt, hcpos]
      -- the numerator is bounded by `ε (1 - cos δ)`
      have hnum : 1 - r ^ 2 < ε * (1 - Real.cos δ) := by
        have h2r : 1 - r ^ 2 = (1 - r) * (1 + r) := by ring
        rw [h2r]
        have hmm : (1 - r) * (1 + r) < m * 2 := by nlinarith [hrm, hr1, hmpos]
        nlinarith [hmm, hmle2, hε]
      have hthis : (1 - r ^ 2) / D < ε := by
        rw [div_lt_iff₀ hDpos]
        have : ε * (1 - Real.cos δ) < ε * D := mul_lt_mul_of_pos_left hDgt hε
        linarith
      exact hthis

end Work.EQ.Fatou
