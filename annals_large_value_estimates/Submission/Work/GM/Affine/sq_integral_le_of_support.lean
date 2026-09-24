import Mathlib

namespace Work.GM.Affine

open MeasureTheory

/-- **Cauchy–Schwarz on an interval.** For a continuous `f` on `[a,b]`,
`(∫_a^b f)² ≤ (b - a) ∫_a^b f²`. -/
private lemma interval_sq_integral_le {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) :
    (∫ x in a..b, f x) ^ 2 ≤ (b - a) * ∫ x in a..b, f x ^ 2 := by
  have hfu : ContinuousOn f (Set.uIcc a b) := by rwa [Set.uIcc_of_le hab]
  have hf2u : ContinuousOn (fun x => f x ^ 2) (Set.uIcc a b) := hfu.pow 2
  have hfI : IntervalIntegrable f volume a b := hfu.intervalIntegrable
  have hf2I : IntervalIntegrable (fun x => f x ^ 2) volume a b := hf2u.intervalIntegrable
  -- the quadratic `t ↦ ∫ (t - f)²` is nonnegative
  have hQuad : ∀ t : ℝ, 0 ≤ t ^ 2 * (b - a) - 2 * t * (∫ x in a..b, f x)
      + ∫ x in a..b, f x ^ 2 := by
    intro t
    have hnonneg : 0 ≤ ∫ x in a..b, (t - f x) ^ 2 :=
      intervalIntegral.integral_nonneg hab (fun x _ => sq_nonneg _)
    have hexp : ∫ x in a..b, (t - f x) ^ 2
        = t ^ 2 * (b - a) - 2 * t * (∫ x in a..b, f x) + ∫ x in a..b, f x ^ 2 := by
      have h1 : IntervalIntegrable (fun x : ℝ => t ^ 2) volume a b := intervalIntegrable_const
      have h2 : IntervalIntegrable (fun x : ℝ => 2 * t * f x) volume a b :=
        (continuousOn_const.mul hfu).intervalIntegrable
      calc ∫ x in a..b, (t - f x) ^ 2
          = ∫ x in a..b, (t ^ 2 - 2 * t * f x + f x ^ 2) := by
            apply intervalIntegral.integral_congr
            intro x _; ring
        _ = (∫ x in a..b, (t ^ 2 - 2 * t * f x)) + ∫ x in a..b, f x ^ 2 :=
            intervalIntegral.integral_add (h1.sub h2) hf2I
        _ = ((∫ x in a..b, t ^ 2) - ∫ x in a..b, 2 * t * f x) + ∫ x in a..b, f x ^ 2 := by
            rw [intervalIntegral.integral_sub h1 h2]
        _ = t ^ 2 * (b - a) - 2 * t * (∫ x in a..b, f x) + ∫ x in a..b, f x ^ 2 := by
            rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
            simp only [smul_eq_mul]
            ring
    rw [hexp] at hnonneg
    exact hnonneg
  rcases eq_or_lt_of_le (sub_nonneg.mpr hab) with hB | hBpos
  · -- degenerate case `b = a`
    have hba : b = a := by linarith
    rw [hba, intervalIntegral.integral_same, intervalIntegral.integral_same]
    simp
  · -- evaluate the quadratic at `t = (∫ f) / (b - a)`
    have h := hQuad ((∫ x in a..b, f x) / (b - a))
    have he : ((∫ x in a..b, f x) / (b - a)) ^ 2 * (b - a)
          - 2 * ((∫ x in a..b, f x) / (b - a)) * (∫ x in a..b, f x)
          + ∫ x in a..b, f x ^ 2
        = (∫ x in a..b, f x ^ 2) - (∫ x in a..b, f x) ^ 2 / (b - a) := by
      field_simp
      ring
    rw [he] at h
    have hle : (∫ x in a..b, f x) ^ 2 / (b - a) ≤ ∫ x in a..b, f x ^ 2 := by linarith
    rw [div_le_iff₀ hBpos] at hle
    linarith

/-- A set integral over `Set.Icc a b` is an interval integral (`a ≤ b`). -/
private lemma setIntegral_Icc_eq_intervalIntegral {a b : ℝ} (hab : a ≤ b) (g : ℝ → ℝ) :
    ∫ x in Set.Icc a b, g x = ∫ x in a..b, g x := by
  rw [intervalIntegral.integral_of_le hab]
  exact (MeasureTheory.setIntegral_congr_set Ioc_ae_eq_Icc).symm

/-- **Cauchy–Schwarz for a nonnegative continuous function of bounded support.**
If `f : ℝ → ℝ` is continuous, nonnegative, and vanishes off `[a,b]` (`a ≤ b`), then
`(∫ f)² ≤ (b - a) ∫ f²`.  (The support hypothesis makes the whole-line integral a
`[a,b]`-integral, and the interval form of Cauchy–Schwarz gives the bound.) -/
theorem sq_integral_le_of_support {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ} (hf : Continuous f)
    (hnn : ∀ u : ℝ, 0 ≤ f u) (hsupp : ∀ u : ℝ, f u ≠ 0 → u ∈ Set.Icc a b) :
    (∫ u : ℝ, f u) ^ 2 ≤ (b - a) * ∫ u : ℝ, (f u) ^ 2 := by
  -- The nonnegativity hypothesis is not needed for this direction of Cauchy–Schwarz;
  -- we record it so that the proof does not silently drop an assumption.
  have _hnn_nonneg : 0 ≤ f 0 := hnn 0
  -- `f` vanishes off `[a,b]`
  have hsupp' : ∀ u : ℝ, u ∉ Set.Icc a b → f u = 0 := by
    intro u hu
    by_contra h
    exact hu (hsupp u h)
  have hsupp2 : ∀ u : ℝ, u ∉ Set.Icc a b → (f u) ^ 2 = 0 := by
    intro u hu
    rw [hsupp' u hu]
    ring
  -- pass to the set integrals over `[a,b]`
  have h1 : (∫ u : ℝ, f u) = ∫ u in Set.Icc a b, f u :=
    (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hsupp').symm
  have h2 : (∫ u : ℝ, (f u) ^ 2) = ∫ u in Set.Icc a b, (f u) ^ 2 :=
    (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hsupp2).symm
  rw [h1, h2, setIntegral_Icc_eq_intervalIntegral hab f,
    setIntegral_Icc_eq_intervalIntegral hab (fun x => (f x) ^ 2)]
  exact interval_sq_integral_le hab hf.continuousOn

end Work.GM.Affine
