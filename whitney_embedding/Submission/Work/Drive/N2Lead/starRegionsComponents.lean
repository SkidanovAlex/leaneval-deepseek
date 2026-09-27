import Mathlib
import Submission.Work.Drive.N2C.defs
import Submission.Work.Drive.N2Lead.twistDefs
import Submission.Work.Drive.N2Lead.starShapedRadial
import Submission.Work.Drive.N2Lead.starShapedComponents
import Submission.Work.Drive.N2Lead.smoothArgLiftCinf
import Submission.Work.Drive.N2Lead.smoothArgLiftComplex
import Submission.Work.Drive.N2Lead.isLevelIsotopy_squash
import Submission.Work.Drive.N2Lead.isCertifiedAt_of_roundImage
import Submission.Work.Drive.N2.exists_levelComponentCurves
import Submission.Work.Drive.N2Lead.starRegionsCore

set_option maxHeartbeats 1000000

/-!
# The star-regions certificate: the component analysis of the level

The level `f = u` is a finite disjoint union of circles; on each component the planar projection
`proj2 ∘ g` has a strictly monotone argument about the centre of the region it occupies, so that the
component is a *radial graph* about that centre.  This file proves the abstract real-analysis facts
about the argument lift (`Circle.exp ∘ θ`) and assembles them into
`isRadialGraph_of_starRegion`.
-/

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Function Filter

noncomputable section

/-! ## The argument lift, abstractly -/

/-- **The linear growth of the parameter under integer shifts.**  If `θ (t + 1) = θ t + m * 2π`
then `θ (t + n) = θ t + n * (m * 2π)` for every integer `n`. -/
theorem add_int_mul_period {θ : ℝ → ℝ} {m : ℤ}
    (hper : ∀ t : ℝ, θ (t + 1) = θ t + (m : ℝ) * (2 * Real.pi)) (t : ℝ) (n : ℤ) :
    θ (t + n) = θ t + (n : ℝ) * ((m : ℝ) * (2 * Real.pi)) := by
  have hg : Function.Periodic (fun x : ℝ => θ x - x * ((m : ℝ) * (2 * Real.pi))) 1 := by
    intro x
    show θ (x + 1) - (x + 1) * ((m : ℝ) * (2 * Real.pi))
      = θ x - x * ((m : ℝ) * (2 * Real.pi))
    rw [hper x]
    ring
  have h := hg.int_mul n t
  simp only [mul_one] at h
  linarith [h]

/-- The exponential of the argument is invariant under integer shifts of the parameter. -/
theorem circle_exp_add_int {θ : ℝ → ℝ} {m : ℤ}
    (hper : ∀ t : ℝ, θ (t + 1) = θ t + (m : ℝ) * (2 * Real.pi)) (t : ℝ) (n : ℤ) :
    Circle.exp (θ (t + n)) = Circle.exp (θ t) := by
  rw [add_int_mul_period hper t n]
  have hcast : (n : ℝ) * ((m : ℝ) * (2 * Real.pi)) = ((n * m : ℤ) : ℝ) * (2 * Real.pi) := by
    push_cast
    ring
  rw [hcast, Circle.exp_add, Circle.exp_int_mul_two_pi, mul_one]

/-- The exponential of the argument only depends on the argument modulo `2π`. -/
theorem circle_exp_eq_of_eq_add_int {s t : ℝ} (h : ∃ j : ℤ, s = t + j * (2 * Real.pi)) :
    Circle.exp s = Circle.exp t := by
  obtain ⟨j, hj⟩ := h
  rw [hj, Circle.exp_eq_exp]
  exact ⟨j, by ring⟩

/-- **The direction map of the lift is surjective.**  If `θ` is continuous with
`θ (t + 1) = θ t + m * 2π`, `m ≠ 0`, and `θ` is either strictly monotone increasing with `m > 0` or
strictly monotone decreasing with `m < 0`, then every point of the circle is
`Circle.exp (θ t)` for some `t ∈ [0, 1)`. -/
theorem exists_circle_exp_eq_of_shift {θ : ℝ → ℝ} {m : ℤ} (hm : m ≠ 0) (hcont : Continuous θ)
    (hper : ∀ t : ℝ, θ (t + 1) = θ t + (m : ℝ) * (2 * Real.pi))
    (hincr : (0 < m ∧ StrictMono θ) ∨ (m < 0 ∧ StrictAnti θ)) (u : Circle) :
    ∃ t : ℝ, t ∈ Set.Ico 0 1 ∧ Circle.exp (θ t) = u := by
  obtain ⟨α, hα⟩ := Circle.exp_surjective u
  have hc : 0 < 2 * Real.pi := Real.two_pi_pos
  have hθ1 : θ 1 = θ 0 + (m : ℝ) * (2 * Real.pi) := by simpa using hper 0
  have hrange : Set.Icc (θ 0) (θ 1) ⊆ θ '' Set.Icc (0 : ℝ) 1 :=
    intermediate_value_Icc (by norm_num) hcont.continuousOn
  have hrange' : Set.Icc (θ 1) (θ 0) ⊆ θ '' Set.Icc (0 : ℝ) 1 :=
    intermediate_value_Icc' (by norm_num) hcont.continuousOn
  rcases hincr with ⟨hmpos, hmono⟩ | ⟨hmneg, hmono⟩
  · -- `m ≥ 1`: choose `β ∈ [θ 0, θ 0 + 2π)` congruent to `α`
    have hm1 : (1 : ℤ) ≤ m := by omega
    have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    set y : ℝ := (θ 0 - α) / (2 * Real.pi) with hy
    set β : ℝ := α + (⌈y⌉ : ℝ) * (2 * Real.pi) with hβ
    have hβge : θ 0 ≤ β := by
      have h1 : y ≤ (⌈y⌉ : ℝ) := Int.le_ceil y
      have h2 : θ 0 - α ≤ (⌈y⌉ : ℝ) * (2 * Real.pi) := by
        have := mul_le_mul_of_nonneg_right h1 (le_of_lt hc)
        rwa [hy, div_mul_cancel₀ _ hc.ne'] at this
      rw [hβ]; linarith
    have hβlt : β < θ 0 + 2 * Real.pi := by
      have h1 : (⌈y⌉ : ℝ) < y + 1 := Int.ceil_lt_add_one y
      have h2 : (⌈y⌉ : ℝ) * (2 * Real.pi) < (y + 1) * (2 * Real.pi) :=
        mul_lt_mul_of_pos_right h1 hc
      have h3 : (y + 1) * (2 * Real.pi) = (θ 0 - α) + 2 * Real.pi := by
        rw [hy]; field_simp
      rw [hβ]; linarith
    have h2πle : θ 0 + 2 * Real.pi ≤ θ 1 := by
      rw [hθ1]
      nlinarith
    have hβrange : β ∈ Set.Icc (θ 0) (θ 1) :=
      ⟨hβge, by linarith⟩
    obtain ⟨t, ht, htv⟩ := hrange hβrange
    have htne : t ≠ 1 := by
      intro h1
      have h2 : β = θ 1 := by rw [← htv, h1]
      linarith
    refine ⟨t, ⟨ht.1, lt_of_le_of_ne ht.2 htne⟩, ?_⟩
    rw [htv, hβ]
    exact (circle_exp_eq_of_eq_add_int ⟨⌈y⌉, by ring⟩).trans hα
  · -- `m ≤ -1`: choose `β ∈ (θ 0 - 2π, θ 0]` congruent to `α`
    have hm1 : m ≤ (-1 : ℤ) := by omega
    have hm1R : (m : ℝ) ≤ -1 := by exact_mod_cast hm1
    set y : ℝ := (θ 0 - α) / (2 * Real.pi) with hy
    set β : ℝ := α + (⌊y⌋ : ℝ) * (2 * Real.pi) with hβ
    have hβle : β ≤ θ 0 := by
      have h1 : (⌊y⌋ : ℝ) ≤ y := Int.floor_le y
      have h2 : (⌊y⌋ : ℝ) * (2 * Real.pi) ≤ θ 0 - α := by
        have := mul_le_mul_of_nonneg_right h1 (le_of_lt hc)
        rwa [hy, div_mul_cancel₀ _ hc.ne'] at this
      rw [hβ]; linarith
    have hβgt : θ 0 - 2 * Real.pi < β := by
      have h1 : y < (⌊y⌋ : ℝ) + 1 := Int.lt_floor_add_one y
      have h2 : (y - 1) * (2 * Real.pi) < (⌊y⌋ : ℝ) * (2 * Real.pi) := by
        have := mul_lt_mul_of_pos_right (by linarith : y - 1 < (⌊y⌋ : ℝ)) hc
        linarith
      have h3 : (y - 1) * (2 * Real.pi) = (θ 0 - α) - 2 * Real.pi := by
        rw [hy]; field_simp
      rw [hβ]; linarith
    have hle : θ 1 ≤ θ 0 - 2 * Real.pi := by
      rw [hθ1]
      nlinarith
    have hβrange : β ∈ Set.Icc (θ 1) (θ 0) := ⟨by linarith, hβle⟩
    obtain ⟨t, ht, htv⟩ := hrange' hβrange
    have htne : t ≠ 1 := by
      intro h1
      have h2 : β = θ 1 := by rw [← htv, h1]
      linarith
    refine ⟨t, ⟨ht.1, lt_of_le_of_ne ht.2 htne⟩, ?_⟩
    rw [htv, hβ]
    exact (circle_exp_eq_of_eq_add_int ⟨⌊y⌋, by ring⟩).trans hα


/-- **The increment is `±2π`.**  If the direction map `Circle.exp ∘ θ` takes the value `u₀` at most
once on `[0, 1)`, then the increment of `θ` (a multiple of `2π`, non-zero) is `±2π`. -/
theorem eq_one_or_neg_one_of_unique {θ : ℝ → ℝ} {m : ℤ} (hm : m ≠ 0) (hcont : Continuous θ)
    (hper : ∀ t : ℝ, θ (t + 1) = θ t + (m : ℝ) * (2 * Real.pi))
    (hincr : (0 < m ∧ StrictMono θ) ∨ (m < 0 ∧ StrictAnti θ)) {u₀ : Circle}
    (huniq : ∀ s t : ℝ, s ∈ Set.Ico 0 1 → t ∈ Set.Ico 0 1 →
      Circle.exp (θ s) = u₀ → Circle.exp (θ t) = u₀ → s = t) :
    m = 1 ∨ m = -1 := by
  have htwopi : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  -- the `fract` of the second parameter
  have key : ∀ s s' : ℝ, s ∈ Set.Ico 0 1 → s < s' → s' < s + 1 → θ s' = θ s + (2 * Real.pi) →
      Circle.exp (θ (Int.fract s')) = Circle.exp (θ s) := by
    intro s s' hs hlt hlt' hv
    have hs'eq : s' = Int.fract s' + (⌊s'⌋ : ℝ) := (Int.fract_add_floor s').symm
    have h1 := add_int_mul_period hper (Int.fract s') ⌊s'⌋
    rw [← hs'eq] at h1
    have h2 : θ (Int.fract s') = θ s' - (⌊s'⌋ : ℝ) * ((m : ℝ) * (2 * Real.pi)) := by linarith
    rw [h2, hv]
    have h3 : Circle.exp (θ s + 2 * Real.pi - (⌊s'⌋ : ℝ) * ((m : ℝ) * (2 * Real.pi)))
        = Circle.exp (θ s) := by
      rw [Circle.exp_eq_exp]
      refine ⟨1 - ⌊s'⌋ * m, ?_⟩
      push_cast
      ring
    exact h3
  have key' : ∀ s s' : ℝ, s ∈ Set.Ico 0 1 → s < s' → s' < s + 1 → θ s' = θ s - (2 * Real.pi) →
      Circle.exp (θ (Int.fract s')) = Circle.exp (θ s) := by
    intro s s' hs hlt hlt' hv
    have hs'eq : s' = Int.fract s' + (⌊s'⌋ : ℝ) := (Int.fract_add_floor s').symm
    have h1 := add_int_mul_period hper (Int.fract s') ⌊s'⌋
    rw [← hs'eq] at h1
    have h2 : θ (Int.fract s') = θ s' - (⌊s'⌋ : ℝ) * ((m : ℝ) * (2 * Real.pi)) := by linarith
    rw [h2, hv]
    have h3 : Circle.exp (θ s - 2 * Real.pi - (⌊s'⌋ : ℝ) * ((m : ℝ) * (2 * Real.pi)))
        = Circle.exp (θ s) := by
      rw [Circle.exp_eq_exp]
      refine ⟨-1 - ⌊s'⌋ * m, ?_⟩
      push_cast
      ring
    exact h3
  have hfract_ne : ∀ s s' : ℝ, s < s' → s' < s + 1 → Int.fract s' ≠ s := by
    intro s s' hlt hlt' hcontra
    have h1 : s' - s = (⌊s'⌋ : ℝ) := by
      have h2 : s' = Int.fract s' + (⌊s'⌋ : ℝ) := (Int.fract_add_floor s').symm
      rw [hcontra] at h2
      linarith
    have h2 : (0 : ℝ) < (⌊s'⌋ : ℝ) := by linarith
    have h3 : (⌊s'⌋ : ℝ) < 1 := by linarith
    have h4 : (0 : ℤ) < ⌊s'⌋ := by exact_mod_cast h2
    have h5 : ⌊s'⌋ < (1 : ℤ) := by exact_mod_cast h3
    omega
  rcases hincr with ⟨hmpos, hmono⟩ | ⟨hmneg, hmono⟩
  · -- `m ≥ 1`
    have hm1 : (1 : ℤ) ≤ m := by omega
    by_contra hne
    have hm2 : (2 : ℤ) ≤ m := by omega
    have hm2R : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
    obtain ⟨s, hs, hsu⟩ := exists_circle_exp_eq_of_shift hm hcont hper (Or.inl ⟨hmpos, hmono⟩) u₀
    have hθs1 : θ (s + 1) = θ s + (m : ℝ) * (2 * Real.pi) := by simpa using hper s
    have hmem : θ s + 2 * Real.pi ∈ Set.Icc (θ s) (θ (s + 1)) := by
      refine ⟨by linarith, ?_⟩
      rw [hθs1]
      nlinarith
    obtain ⟨s', hs', hs'v⟩ :=
      (intermediate_value_Icc (by linarith : s ≤ s + 1) hcont.continuousOn) hmem
    have hs'lt : s' < s + 1 := by
      rcases lt_or_eq_of_le hs'.2 with h | h
      · exact h
      · exfalso
        rw [h, hθs1] at hs'v
        nlinarith
    have hs'gt : s < s' := by
      rcases lt_or_eq_of_le hs'.1 with h | h
      · exact h
      · exfalso
        rw [← h] at hs'v
        linarith
    refine (hfract_ne s s' hs'gt hs'lt) (huniq s (Int.fract s') hs
      ⟨Int.fract_nonneg s', Int.fract_lt_one s'⟩ hsu
      ((key s s' hs hs'gt hs'lt hs'v).trans hsu)).symm
  · -- `m ≤ -1`
    have hm1 : m ≤ (-1 : ℤ) := by omega
    by_contra hne
    have hm2 : m ≤ (-2 : ℤ) := by omega
    have hm2R : (m : ℝ) ≤ -2 := by exact_mod_cast hm2
    obtain ⟨s, hs, hsu⟩ := exists_circle_exp_eq_of_shift hm hcont hper (Or.inr ⟨hmneg, hmono⟩) u₀
    have hθs1 : θ (s + 1) = θ s + (m : ℝ) * (2 * Real.pi) := by simpa using hper s
    have hmem : θ s - 2 * Real.pi ∈ Set.Icc (θ (s + 1)) (θ s) := by
      refine ⟨?_, by linarith⟩
      rw [hθs1]
      nlinarith
    obtain ⟨s', hs', hs'v⟩ :=
      (intermediate_value_Icc' (by linarith : s ≤ s + 1) hcont.continuousOn) hmem
    have hs'lt : s' < s + 1 := by
      rcases lt_or_eq_of_le hs'.2 with h | h
      · exact h
      · exfalso
        rw [h, hθs1] at hs'v
        nlinarith
    have hs'gt : s < s' := by
      rcases lt_or_eq_of_le hs'.1 with h | h
      · exact h
      · exfalso
        rw [← h] at hs'v
        linarith
    refine (hfract_ne s s' hs'gt hs'lt) (huniq s (Int.fract s') hs
      ⟨Int.fract_nonneg s', Int.fract_lt_one s'⟩ hsu
      ((key' s s' hs hs'gt hs'lt hs'v).trans hsu)).symm

/-- **Injectivity of the direction map modulo the period.**  If the increment of `θ` is `±2π` and
`θ` is strictly monotone, then `Circle.exp ∘ θ` only identifies parameters differing by an
integer. -/
theorem exists_int_sub_of_circle_exp_eq {θ : ℝ → ℝ} {m : ℤ} (hm : m = 1 ∨ m = -1)
    (hper : ∀ t : ℝ, θ (t + 1) = θ t + (m : ℝ) * (2 * Real.pi))
    (hmono : StrictMono θ ∨ StrictAnti θ) :
    ∀ s t : ℝ, Circle.exp (θ s) = Circle.exp (θ t) → ∃ j : ℤ, s = t + j := by
  intro s t hst
  obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp hst
  have hm2 : (m : ℝ) * (2 * Real.pi) = 2 * Real.pi ∨ (m : ℝ) * (2 * Real.pi) = -(2 * Real.pi) := by
    rcases hm with h | h
    · left; rw [h]; norm_num
    · right; rw [h]; norm_num
  set j : ℤ := ⌊s - t⌋ with hj
  set s' : ℝ := s - j with hs'
  have hs'Icc : s' ∈ Set.Icc t (t + 1) := by
    refine ⟨?_, ?_⟩
    · have := Int.floor_le (s - t); dsimp only [s', j]; linarith
    · have := Int.lt_floor_add_one (s - t); dsimp only [s', j]; linarith
  have hs'circle : Circle.exp (θ s') = Circle.exp (θ s) := by
    have h2 : s = s' + (j : ℝ) := by rw [hs']; ring
    rw [h2, circle_exp_add_int hper s' j]
  have hs'val : θ s' = θ s - (j : ℝ) * ((m : ℝ) * (2 * Real.pi)) := by
    have h1 := add_int_mul_period hper s' j
    have h2 : s' + (j : ℝ) = s := by rw [hs']; ring
    rw [h2] at h1
    linarith
  have hkey : θ s' - θ t = ((n - j * m : ℤ) : ℝ) * (2 * Real.pi) := by
    rw [hs'val]
    have hjm : (j : ℝ) * ((m : ℝ) * (2 * Real.pi)) = ((j * m : ℤ) : ℝ) * (2 * Real.pi) := by
      push_cast; ring
    rw [hjm, hn]
    push_cast
    ring
  rcases lt_or_eq_of_le hs'Icc.1 with hlt | heq
  · -- `s' > t`: the interval is non-degenerate
    have hlt' : s' < t + 1 := by
      have h := Int.lt_floor_add_one (s - t)
      simp only [s', j] at h ⊢
      linarith
    have hbound : |θ s' - θ t| < 2 * Real.pi := by
      have h1 : |θ (t + 1) - θ t| = 2 * Real.pi := by
        rw [show θ (t + 1) = θ t + (m : ℝ) * (2 * Real.pi) from by simpa using hper t]
        rcases hm2 with h | h <;> rw [h] <;> simp [abs_of_pos Real.two_pi_pos]
      have h2 : |θ s' - θ t| < |θ (t + 1) - θ t| := by
        rcases hmono with hm | hm
        · have h3 : θ t < θ s' := hm hlt
          have h4 : θ s' < θ (t + 1) := hm hlt'
          rw [abs_of_pos (by linarith : (0:ℝ) < θ s' - θ t),
            abs_of_pos (by linarith : (0:ℝ) < θ (t + 1) - θ t)]
          linarith
        · have h3 : θ s' < θ t := hm hlt
          have h4 : θ (t + 1) < θ s' := hm hlt'
          rw [abs_of_neg (by linarith : θ s' - θ t < 0),
            abs_of_neg (by linarith : θ (t + 1) - θ t < 0)]
          linarith
      linarith [h1]
    have hzero : (n - j * m : ℤ) = 0 := by
      rw [hkey] at hbound
      have h2 : |((n - j * m : ℤ) : ℝ)| * (2 * Real.pi) < 2 * Real.pi := by
        rwa [abs_mul, abs_of_pos Real.two_pi_pos] at hbound
      have h3 : |((n - j * m : ℤ) : ℝ)| < 1 := by nlinarith [h2, Real.two_pi_pos]
      have h4 : |(n - j * m : ℤ)| < 1 := by exact_mod_cast h3
      have h5 := abs_lt.mp h4
      omega
    have hsub : θ s' - θ t = 0 := by
      rw [hkey, hzero]; push_cast; ring
    have : θ s' = θ t := by linarith
    have hst' : s' = t := by
      rcases hmono with hm | hm
      · exact hm.injective this
      · exact hm.injective this
    exact ⟨j, by linarith⟩
  · exact ⟨j, by linarith⟩


/-! ## The component analysis -/

/-- **A complex number is a real multiple of `a` iff its product with `conj a` is real.** -/
lemma exists_smul_of_im_conj_mul_eq_zero {a b : ℂ} (ha : a ≠ 0) (h : (star a * b).im = 0) :
    ∃ t : ℝ, b = t • a := by
  have hreal : star a * b = ((star a * b).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using h
  have hnorm : a * star a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    have h1 := Complex.mul_conj a
    rw [Complex.normSq_eq_norm_sq] at h1
    exact h1
  have hne : ((‖a‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have h2 : ‖a‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr ha)
    intro hc
    exact h2 (by exact_mod_cast hc)
  have hb : ((‖a‖ ^ 2 : ℝ) : ℂ) * b = ((star a * b).re : ℂ) * a := by
    rw [← hnorm]
    calc (a * star a) * b = a * (star a * b) := by rw [mul_assoc]
      _ = a * ((star a * b).re : ℂ) := congrArg (fun z : ℂ => a * z) hreal
      _ = ((star a * b).re : ℂ) * a := by rw [mul_comm]
  refine ⟨(star a * b).re / ‖a‖ ^ 2, ?_⟩
  rw [Complex.real_smul]
  have hcast : (((star a * b).re / ‖a‖ ^ 2 : ℝ) : ℂ)
      = ((star a * b).re : ℂ) * (((‖a‖ ^ 2 : ℝ) : ℂ))⁻¹ := by
    push_cast
    ring
  rw [hcast]
  calc b = (((‖a‖ ^ 2 : ℝ) : ℂ))⁻¹ * ((((‖a‖ ^ 2 : ℝ) : ℂ)) * b) := by
        rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    _ = (((‖a‖ ^ 2 : ℝ) : ℂ))⁻¹ * (((star a * b).re : ℂ) * a) := by rw [hb]
    _ = ((star a * b).re : ℂ) * (((‖a‖ ^ 2 : ℝ) : ℂ))⁻¹ * a := by ring

/-- **A plane curve is a radial graph about `c`.**  No point of the curve is `c`, two parameters
whose points lie on a common ray from `c` differ by an integer, and every ray from `c` (in a
non-zero direction) is met. -/
def IsRadialGraph (z : ℝ → ℂ) (c : ℂ) : Prop :=
  (∀ t : ℝ, z t ≠ c) ∧
  (∀ s t : ℝ, (∃ a : ℝ, 0 < a ∧ z s - c = a • (z t - c)) → ∃ j : ℤ, s = t + j) ∧
  (∀ w : ℂ, w ≠ 0 → ∃ t : ℝ, ∃ a : ℝ, 0 < a ∧ z t - c = a • w)

/-- The complex number `⟨a, b⟩` as a real linear combination of `1` and `I`. -/
lemma complex_mk_eq_add (a b : ℝ) : (⟨a, b⟩ : ℂ) = (a : ℂ) + (b : ℂ) * Complex.I := by
  apply Complex.ext <;> simp

/-- The coercion of `Circle.exp t` to `ℂ` is the point `⟨cos t, sin t⟩`. -/
lemma coe_circle_exp (t : ℝ) : ((Circle.exp t : Circle) : ℂ) = ⟨Real.cos t, Real.sin t⟩ := by
  rw [Circle.coe_exp, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  exact (complex_mk_eq_add _ _).symm

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- **The component analysis of the star-regions certificate.**  On a component `γ` of the level
`f = u` whose planar projection lies in the region `Ω k`, the picture's planar projection
`t ↦ proj2 (g (γ t))` is a radial graph about the centre `o k`: the angular rate about `o k` never
vanishes (`hrate`), so the argument is strictly monotone; the single ray of `hhit` forces the
increment of the argument to be exactly one full turn, which gives injectivity modulo the period;
and the strict monotonicity gives surjectivity onto the circle of directions. -/
theorem isRadialGraph_of_starRegion
    {f : M → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) tpC f) {u : ℝ} {g : M → E3}
    {K : ℕ} {Ω : Fin K → Set ℂ} {o : Fin K → ℂ}
    (hsmg : ∀ y : M, f y = u → ContMDiffAt (𝓡 2) (𝓡 3) tpC g y)
    (hrate : ∀ (y : M) (k : Fin K), f y = u → proj2 (g y) ∈ Ω k →
      proj2 (g y) ≠ o k ∧
      ∀ v : TangentSpace (𝓡 2) y, mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f y v = 0 → v ≠ 0 →
      ¬ (∃ t : ℝ, mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun z : M => proj2 (g z)) y v
          = t • (proj2 (g y) - o k)))
    (hhit : ∀ k : Fin K, ∃ e : ℂ, e ≠ 0 ∧ ∀ x y : M, f x = u → f y = u →
      (∃ s : ℝ, 0 < s ∧ proj2 (g x) = o k + s • e) →
      (∃ s : ℝ, 0 < s ∧ proj2 (g y) = o k + s • e) → x = y)
    {γ : ℝ → M} (hγsm : ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) tpC γ)
    (hγper : ∀ t : ℝ, γ (t + 1) = γ t)
    (hγinj : Set.InjOn γ (Set.Ico 0 1))
    (hγimm : ∀ t : ℝ, mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1 ≠ 0)
    (hγval : ∀ t : ℝ, f (γ t) = u)
    {k : Fin K} (hk : ∀ t : ℝ, proj2 (g (γ t)) ∈ Ω k) :
    IsRadialGraph (fun t => proj2 (g (γ t))) (o k) := by
  classical
  have hne_all : ∀ t : ℝ, proj2 (g (γ t)) ≠ o k :=
    fun t => (hrate (γ t) k (hγval t) (hk t)).1
  -- ### smoothness, periodicity and the angular rate of the planar projection
  have hgsm : ContDiff ℝ tpC (fun t : ℝ => g (γ t)) := by
    rw [contDiff_iff_contDiffAt]
    intro t
    rw [← contMDiffAt_iff_contDiffAt]
    exact (hsmg (γ t) (hγval t)).comp t (hγsm.contMDiffAt)
  have hzsm' : ContDiff ℝ tpC (fun t : ℝ => proj2 (g (γ t))) := proj2CLM.contDiff.comp hgsm
  have hzsm : ContDiff ℝ tpC (fun t : ℝ => proj2 (g (γ t)) - o k) := hzsm'.sub contDiff_const
  have hzper : ∀ t : ℝ, proj2 (g (γ (t + 1))) - o k = proj2 (g (γ t)) - o k := by
    intro t
    rw [hγper t]
  -- the derivative in terms of the manifold calculus
  have hderiv : ∀ t : ℝ, deriv (fun s : ℝ => proj2 (g (γ s)) - o k) t
      = mfderiv (𝓡 2) 𝓘(ℝ,ℂ) (fun y : M => proj2 (g y)) (γ t)
          (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ t 1) := by
    intro t
    have hgm : MDifferentiableAt (𝓡 2) 𝓘(ℝ,ℂ) (fun y : M => proj2 (g y)) (γ t) :=
      (proj2CLM.mdifferentiableAt).comp (γ t) ((hsmg (γ t) (hγval t)).mdifferentiableAt (by simp))
    have hγm : MDifferentiableAt 𝓘(ℝ,ℝ) (𝓡 2) γ t := hγsm.mdifferentiableAt (by simp)
    have hchain := mfderiv_comp_apply (I := 𝓘(ℝ,ℝ)) (I' := 𝓡 2) (I'' := 𝓘(ℝ,ℂ)) t
      (f := γ) (g := fun y : M => proj2 (g y)) hgm hγm 1
    have hdiff : DifferentiableAt ℝ (fun s : ℝ => proj2 (g (γ s))) t :=
      hzsm'.differentiable (by simp) t
    have h5 : deriv (fun s : ℝ => proj2 (g (γ s))) t
        = fderiv ℝ (fun s : ℝ => proj2 (g (γ s))) t 1 :=
      (hdiff.hasFDerivAt.hasDerivAt).deriv
    have h6 : (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℂ) (fun s : ℝ => proj2 (g (γ s))) t) 1
        = fderiv ℝ (fun s : ℝ => proj2 (g (γ s))) t 1 :=
      congrArg (fun (L : ℝ →L[ℝ] ℂ) => L 1) mfderiv_eq_fderiv
    have h3 : deriv (fun s : ℝ => proj2 (g (γ s)) - o k) t
        = (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℂ) (fun s : ℝ => proj2 (g (γ s))) t) 1 := by
      rw [deriv_sub_const, h5, ← h6]
    rw [h3]
    exact hchain
  -- the tangent vector lies in the kernel of `df`
  have hker : ∀ t : ℝ, mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (γ t) (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ t 1) = 0 := by
    intro t
    have hfm : MDifferentiableAt (𝓡 2) 𝓘(ℝ,ℝ) f (γ t) := hf.mdifferentiableAt (by simp)
    have hγm : MDifferentiableAt 𝓘(ℝ,ℝ) (𝓡 2) γ t := hγsm.mdifferentiableAt (by simp)
    have hchain := mfderiv_comp_apply (I := 𝓘(ℝ,ℝ)) (I' := 𝓡 2) (I'' := 𝓘(ℝ,ℝ)) t
      (f := γ) (g := f) hfm hγm 1
    have hfun : (f ∘ γ) = fun _ : ℝ => u := funext fun s => hγval s
    have h0 : (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (f ∘ γ) t) 1 = 0 := by
      rw [hfun, mfderiv_const]
      rfl
    rw [← hchain]
    exact h0
  -- the angular rate never vanishes
  have hmul : ∀ t : ℝ, ¬ ∃ a : ℝ,
      deriv (fun s : ℝ => proj2 (g (γ s)) - o k) t = a • (proj2 (g (γ t)) - o k) := by
    intro t hab
    obtain ⟨a, ha⟩ := hab
    have h1 := (hrate (γ t) k (hγval t) (hk t)).2 (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ t 1)
      (hker t) (hγimm t)
    refine h1 ⟨a, ?_⟩
    rw [← hderiv t]
    exact ha
  have homega : ∀ t : ℝ,
      (star (proj2 (g (γ t)) - o k) * deriv (fun s : ℝ => proj2 (g (γ s)) - o k) t).im ≠ 0 := by
    intro t h
    exact hmul t (exists_smul_of_im_conj_mul_eq_zero (sub_ne_zero.mpr (hne_all t)) h)
  -- ### the argument lift
  obtain ⟨θ, m, hθsm, hmne, hθder, hθval, hθper⟩ :=
    smoothArgLiftComplex hzsm hzper (fun t => sub_ne_zero.mpr (hne_all t)) homega
  have hθcont : Continuous θ := hθsm.continuous
  -- ### monotonicity of the argument
  have hmono : StrictMono θ ∨ StrictAnti θ := by
    have hcont' : Continuous (deriv θ) := hθsm.continuous_deriv (by simp)
    have hopenS : IsOpen {x : ℝ | 0 < deriv θ x} :=
      isOpen_lt continuous_const hcont'
    have hclopenS : IsClopen {x : ℝ | 0 < deriv θ x} := by
      refine ⟨?_, hopenS⟩
      rw [← isOpen_compl_iff]
      have hcompl : {x : ℝ | 0 < deriv θ x}ᶜ = {x : ℝ | deriv θ x < 0} := by
        ext x
        simp only [mem_compl_iff, mem_setOf_eq, not_lt]
        exact ⟨fun h => lt_of_le_of_ne h (hθder x), fun h => le_of_lt h⟩
      rw [hcompl]
      exact isOpen_lt hcont' continuous_const
    rcases isClopen_iff.mp hclopenS with h0 | h0
    · right
      refine strictAnti_of_deriv_neg fun x => ?_
      have hx : ¬ (0 < deriv θ x) := by
        have : x ∉ ({x : ℝ | 0 < deriv θ x} : Set ℝ) := by rw [h0]; exact notMem_empty x
        simpa using this
      exact lt_of_le_of_ne (le_of_not_gt hx) (hθder x)
    · left
      exact strictMono_of_deriv_pos fun x => by
        have : x ∈ ({x : ℝ | 0 < deriv θ x} : Set ℝ) := by rw [h0]; trivial
        simpa using this
  -- the sign of the increment matches the monotonicity
  have hsign : (0 < m ∧ StrictMono θ) ∨ (m < 0 ∧ StrictAnti θ) := by
    have hθ1 : θ (0 + 1) = θ 0 + (m : ℝ) * (2 * Real.pi) := hθper 0
    simp only [zero_add] at hθ1
    rcases hmono with hm | hm
    · left
      have h1 : θ 0 < θ 1 := hm (by norm_num)
      have h2 : 0 < (m : ℝ) * (2 * Real.pi) := by linarith [hθ1]
      have h2' : 0 < (m : ℝ) := by nlinarith [Real.two_pi_pos, h2]
      exact ⟨Int.cast_pos.mp h2', hm⟩
    · right
      have h1 : θ 1 < θ 0 := hm (by norm_num)
      have h2 : (m : ℝ) * (2 * Real.pi) < 0 := by linarith [hθ1]
      have h2' : (m : ℝ) < 0 := by nlinarith [Real.two_pi_pos, h2]
      exact ⟨Int.cast_lt_zero.mp h2', hm⟩
  -- ### the value relation and the direction
  have hval' : ∀ t : ℝ, proj2 (g (γ t)) - o k
      = ((‖proj2 (g (γ t)) - o k‖ : ℝ) : ℂ) * (Circle.exp (θ t) : ℂ) := by
    intro t
    rw [coe_circle_exp]
    exact (hθval t).symm
  -- ### the increment is one full turn
  have hm_one : m = 1 ∨ m = -1 := by
    have hhitk := hhit k
    obtain ⟨e, hene, hhe⟩ := hhitk
    have hepos : (0 : ℝ) < ‖e‖ := norm_pos_iff.mpr hene
    set u₀ : Circle := ⟨(‖e‖⁻¹ : ℝ) • e, by
      change (‖e‖⁻¹ : ℝ) • e ∈ Metric.sphere (0 : ℂ) 1
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg e)), inv_mul_cancel₀ hepos.ne']⟩ with hu₀
    have hu₀coe : ((u₀ : Circle) : ℂ) = (‖e‖⁻¹ : ℝ) • e := rfl
    refine eq_one_or_neg_one_of_unique hmne hθcont hθper hsign (u₀ := u₀) ?_
    intro s t hs ht hsu htu
    have key : ∀ u : ℝ, Circle.exp (θ u) = u₀ →
        proj2 (g (γ u)) = o k + (‖proj2 (g (γ u)) - o k‖ * ‖e‖⁻¹) • e := by
      intro u hu
      have h : proj2 (g (γ u)) - o k = (‖proj2 (g (γ u)) - o k‖ * ‖e‖⁻¹) • e := by
        have h' := hval' u
        rw [hu] at h'
        conv_lhs => rw [h']
        rw [hu₀coe]
        simp only [Complex.real_smul]
        rw [Complex.ofReal_mul]
        ring
      calc proj2 (g (γ u)) = o k + (proj2 (g (γ u)) - o k) := by abel
        _ = o k + (‖proj2 (g (γ u)) - o k‖ * ‖e‖⁻¹) • e :=
              congrArg (fun z : ℂ => o k + z) h
    have hs' : 0 < ‖proj2 (g (γ s)) - o k‖ * ‖e‖⁻¹ :=
      mul_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hne_all s))) (inv_pos.mpr hepos)
    have ht' : 0 < ‖proj2 (g (γ t)) - o k‖ * ‖e‖⁻¹ :=
      mul_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hne_all t))) (inv_pos.mpr hepos)
    have heq := hhe (γ s) (γ t) (hγval s) (hγval t) ⟨_, hs', key s hsu⟩ ⟨_, ht', key t htu⟩
    exact hγinj hs ht heq
  -- ### the conclusion
  have hinj_dir : ∀ s t : ℝ, Circle.exp (θ s) = Circle.exp (θ t) → ∃ j : ℤ, s = t + j :=
    exists_int_sub_of_circle_exp_eq hm_one hθper hmono
  refine ⟨hne_all, ?_, ?_⟩
  · -- two parameters on a common ray differ by an integer
    intro s t hsmu
    obtain ⟨a, ha, haval⟩ := hsmu
    have hnorm : ‖proj2 (g (γ s)) - o k‖ = a * ‖proj2 (g (γ t)) - o k‖ := by
      have h := congrArg norm haval
      rwa [norm_smul, Real.norm_eq_abs, abs_of_pos ha] at h
    have hdir : Circle.exp (θ s) = Circle.exp (θ t) := by
      have hs0 : ((‖proj2 (g (γ s)) - o k‖ : ℝ) : ℂ) ≠ 0 := by
        intro hc
        have h0 : (‖proj2 (g (γ s)) - o k‖ : ℝ) = 0 := Complex.ofReal_injective (by simpa using hc)
        exact (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hne_all s))) h0
      have h1 : ((‖proj2 (g (γ s)) - o k‖ : ℝ) : ℂ) * (Circle.exp (θ s) : ℂ)
          = (a : ℂ) * (((‖proj2 (g (γ t)) - o k‖ : ℝ) : ℂ) * (Circle.exp (θ t) : ℂ)) := by
        rw [← hval' s, ← hval' t, haval, Complex.real_smul]
      have h2 : ((‖proj2 (g (γ s)) - o k‖ : ℝ) : ℂ) * (Circle.exp (θ s) : ℂ)
          = ((‖proj2 (g (γ s)) - o k‖ : ℝ) : ℂ) * (Circle.exp (θ t) : ℂ) := by
        have h3 : (a : ℂ) * (((‖proj2 (g (γ t)) - o k‖ : ℝ) : ℂ) * (Circle.exp (θ t) : ℂ))
            = ((‖proj2 (g (γ s)) - o k‖ : ℝ) : ℂ) * (Circle.exp (θ t) : ℂ) := by
          rw [← mul_assoc, ← Complex.ofReal_mul, ← hnorm]
        rw [h1, h3]
      have h3 : (((Circle.exp (θ s) : Circle)) : ℂ) = (((Circle.exp (θ t) : Circle)) : ℂ) :=
        mul_left_cancel₀ hs0 h2
      exact Subtype.coe_injective h3
    exact hinj_dir s t hdir
  · -- every ray is met
    intro w hw
    have hwpos : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
    set u₀ : Circle := ⟨(‖w‖⁻¹ : ℝ) • w, by
      change (‖w‖⁻¹ : ℝ) • w ∈ Metric.sphere (0 : ℂ) 1
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg w)), inv_mul_cancel₀ hwpos.ne']⟩ with hu₀
    have hu₀coe : ((u₀ : Circle) : ℂ) = (‖w‖⁻¹ : ℝ) • w := rfl
    obtain ⟨t, -, ht⟩ := exists_circle_exp_eq_of_shift hmne hθcont hθper hsign u₀
    refine ⟨t, ‖proj2 (g (γ t)) - o k‖ * ‖w‖⁻¹, ?_, ?_⟩
    · exact mul_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hne_all t))) (inv_pos.mpr hwpos)
    · have h : (‖proj2 (g (γ t)) - o k‖ * ‖w‖⁻¹) • w = proj2 (g (γ t)) - o k := by
        rw [Complex.real_smul, Complex.ofReal_mul, mul_assoc]
        rw [show (((‖w‖⁻¹ : ℝ) : ℂ)) * w = ((Circle.exp (θ t) : Circle) : ℂ) from by
          rw [ht]; exact hu₀coe.symm]
        exact (hval' t).symm
      exact h.symm
end

end Work.Drive.N2Lead
