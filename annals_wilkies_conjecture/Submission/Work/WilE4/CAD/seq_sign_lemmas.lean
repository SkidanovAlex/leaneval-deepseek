import Mathlib
import Submission.Work.WilE4.CAD.seq_prelim

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

open Classical Filter
open scoped Topology

namespace Work.WilE4.CAD

open MvPolynomial Polynomial
open Work.WilE4 (spec)

variable {m k : ℕ}

/-! ## Sign constancy on an interval without roots -/

/-- A continuous real function with no zero on `[a,b]` has the same sign at any two points of
`[a,b]`. -/
theorem sign_eq_of_no_root_Icc {g : ℝ → ℝ} (hg : Continuous g) {a b : ℝ} (hab : a ≤ b)
    (hne : ∀ t ∈ Set.Icc a b, g t ≠ 0) {y y' : ℝ} (hy : y ∈ Set.Icc a b)
    (hy' : y' ∈ Set.Icc a b) : SignType.sign (g y) = SignType.sign (g y') := by
  have hsub : Set.uIcc y y' ⊆ Set.Icc a b := by
    rcases le_total y y' with hle | hle
    · rw [Set.uIcc_of_le hle]
      exact Set.Icc_subset_Icc hy.1 hy'.2
    · rw [Set.uIcc_of_ge hle]
      exact Set.Icc_subset_Icc hy'.1 hy.2
  rcases lt_trichotomy (g y) 0 with hy0 | hy0 | hy0
  · rcases lt_trichotomy (g y') 0 with hy1 | hy1 | hy1
    · rw [sign_neg hy0, sign_neg hy1]
    · exact absurd hy1 (hne y' hy')
    · have hmem : (0 : ℝ) ∈ Set.uIcc (g y) (g y') := by
        rw [Set.mem_uIcc]
        exact Or.inl ⟨le_of_lt hy0, le_of_lt hy1⟩
      obtain ⟨t, ht, ht0⟩ := intermediate_value_uIcc hg.continuousOn hmem
      exact absurd ht0 (hne t (hsub ht))
  · exact absurd hy0 (hne y hy)
  · rcases lt_trichotomy (g y') 0 with hy1 | hy1 | hy1
    · have hmem : (0 : ℝ) ∈ Set.uIcc (g y) (g y') := by
        rw [Set.mem_uIcc]
        exact Or.inr ⟨le_of_lt hy1, le_of_lt hy0⟩
      obtain ⟨t, ht, ht0⟩ := intermediate_value_uIcc hg.continuousOn hmem
      exact absurd ht0 (hne t (hsub ht))
    · exact absurd hy1 (hne y' hy')
    · rw [sign_pos hy0, sign_pos hy1]

/-- Two reals with positive product have the same sign. -/
theorem sign_eq_of_mul_pos {a b : ℝ} (h : 0 < a * b) : SignType.sign a = SignType.sign b := by
  rcases mul_pos_iff.mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [sign_pos ha, sign_pos hb]
  · rw [sign_neg ha, sign_neg hb]

/-! ## Sign transfer across the unique root in a disk -/

/-- If `z` is the only root of the non-zero polynomial `f` in the disk of radius `ρ` around `z`,
then `f` has the same sign at two points of that disk lying strictly on the same side of `z`. -/
theorem sign_eq_of_unique_root {f : Polynomial ℝ} {z t₀ : ℝ} {ρ : ℝ} (hf : f ≠ 0)
    (hroot : f.eval z = 0) (huniq : ∀ w : ℝ, f.eval w = 0 → |w - t₀| < ρ → w = z)
    {y y' : ℝ} (hy : |y - t₀| < ρ) (hy' : |y' - t₀| < ρ) (hs : 0 < (y - z) * (y' - z)) :
    SignType.sign (f.eval y) = SignType.sign (f.eval y') := by
  obtain ⟨q, hq, hndvd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd f hf z
  have hqeval : q.eval z ≠ 0 := fun h0 => hndvd ((Polynomial.dvd_iff_isRoot).mpr h0)
  -- `q` has no root in the disk
  have hqne : ∀ w : ℝ, |w - t₀| < ρ → q.eval w ≠ 0 := by
    intro w hw h0
    have hfw : f.eval w = 0 := by
      rw [hq, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, h0, mul_zero]
    have hwz : w = z := huniq w hfw hw
    rw [hwz] at h0
    exact hqeval h0
  -- the interval between `y` and `y'` lies in the disk, where `q` has no root
  have hball : Set.Icc (min y y') (max y y') ⊆ Metric.ball t₀ ρ := by
    have h1 : y ∈ Metric.ball t₀ ρ := by simpa [Metric.mem_ball, Real.dist_eq] using hy
    have h2 : y' ∈ Metric.ball t₀ ρ := by simpa [Metric.mem_ball, Real.dist_eq] using hy'
    rw [← segment_eq_Icc' y y']
    exact (convex_ball t₀ ρ).segment_subset h1 h2
  have hqsign : SignType.sign (q.eval y) = SignType.sign (q.eval y') := by
    refine sign_eq_of_no_root_Icc (Polynomial.continuous q) (min_le_max) (fun t ht => ?_)
      (show y ∈ Set.Icc (min y y') (max y y') from ⟨min_le_left _ _, le_max_left _ _⟩)
      (show y' ∈ Set.Icc (min y y') (max y y') from ⟨min_le_right _ _, le_max_right _ _⟩)
    exact hqne t (by simpa [Metric.mem_ball, Real.dist_eq] using hball ht)
  -- the power factors have the same sign
  have hpow : SignType.sign ((y - z) ^ f.rootMultiplicity z)
      = SignType.sign ((y' - z) ^ f.rootMultiplicity z) := by
    rw [sign_pow_eq, sign_pow_eq, sign_eq_of_mul_pos hs]
  have hform : ∀ w : ℝ, f.eval w = (w - z) ^ f.rootMultiplicity z * q.eval w := by
    intro w
    conv_lhs => rw [hq]
    rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C]
  rw [hform y, hform y', sign_mul, sign_mul, hpow, hqsign]

end Work.WilE4.CAD
