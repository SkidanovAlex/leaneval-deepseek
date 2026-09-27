import Mathlib

/-!
# The Birkhoff average is an `L²` contraction

For a probability measure `ν`, a measure-preserving map `T`, and `g ∈ L²(ν)`, the
`n`-th Birkhoff average of `g` along the orbit of `T` has `L²`-norm at most that of `g`:

`√(∫ (birkhoffAverage ℝ T g n)² ∂ν) ≤ √(∫ g² ∂ν)`.

This is the elementary consequence of Jensen's inequality applied to the (discrete)
convex combination `(1/n) ∑_{k<n} g(T^k x)`, together with the invariance
`∫ (g ∘ T^k)² ∂ν = ∫ g² ∂ν` coming from `T` preserving `ν`.
-/

open MeasureTheory

namespace Work.EKLC6Core

/-- Pointwise **Jensen / Cauchy–Schwarz** inequality behind the `L²`-contraction of the
Birkhoff average: the square of the arithmetic mean of `n` reals is at most the mean
of their squares. Holds for `n = 0` as well, where both sides vanish. -/
theorem L2_birkhoff_sq_inv_sum_le (n : ℕ) (a : ℕ → ℝ) :
    ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, a k)^2
      ≤ (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (a k)^2 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h.ne'
    have hCS : (∑ k ∈ Finset.range n, a k)^2 ≤ (n : ℝ) * ∑ k ∈ Finset.range n, (a k)^2 := by
      simpa using sq_sum_le_card_mul_sum_sq (f := a) (s := Finset.range n)
    calc ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, a k)^2
        = (n : ℝ)⁻¹ * ((n : ℝ)⁻¹ * (∑ k ∈ Finset.range n, a k)^2) := by ring
      _ ≤ (n : ℝ)⁻¹ * ((n : ℝ)⁻¹ * ((n : ℝ) * ∑ k ∈ Finset.range n, (a k)^2)) := by
            gcongr
      _ = (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (a k)^2 := by
            congr 1
            rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

/-- Integrals are invariant under a measure-preserving map: `∫ f (T^[k] x) ∂ν = ∫ f x ∂ν`. -/
theorem L2_birkhoff_integral_iterate {X : Type*} [MeasurableSpace X]
    (ν : MeasureTheory.Measure X) (T : X → X) (hν : MeasureTheory.MeasurePreserving T ν ν)
    (f : X → ℝ) (hf : MeasureTheory.AEStronglyMeasurable f ν) (k : ℕ) :
    ∫ x, f (T^[k] x) ∂ν = ∫ x, f x ∂ν := by
  have hmp := hν.iterate k
  have h := integral_map (μ := ν) (φ := T^[k]) hmp.aemeasurable
    (f := f) (by rw [hmp.map_eq]; exact hf)
  rw [hmp.map_eq] at h
  exact h.symm

/-- Integral of the mean of the squares along an orbit: for `g ∈ L²(ν)` and `T` preserving
the probability measure `ν`,
`∫ (1/n ∑_{k<n} (g ∘ T^k)²) ∂ν = (1/n) · n · ∫ g² ∂ν` (the factor `1/n · n` is `1` for
`n ≥ 1` and `0` for `n = 0`, where the integrand vanishes). -/
theorem L2_birkhoff_integral_sum_sq {X : Type*} [MeasurableSpace X]
    (ν : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure ν]
    (T : X → X) (hν : MeasureTheory.MeasurePreserving T ν ν)
    (g : X → ℝ) (hg : MeasureTheory.MemLp g 2 ν) (n : ℕ) :
    ∫ x, ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (g (T^[k] x))^2) ∂ν
      = (n : ℝ)⁻¹ * n * ∫ x, (g x)^2 ∂ν := by
  have hInt : ∀ k ∈ Finset.range n, Integrable (fun x => (g (T^[k] x))^2) ν := by
    intro k _
    exact (hg.comp_measurePreserving (hν.iterate k)).integrable_sq
  rw [integral_const_mul]
  rw [integral_finsetSum _ hInt]
  have hconst : ∀ k, ∫ x, (g (T^[k] x))^2 ∂ν = ∫ x, (g x)^2 ∂ν := by
    intro k
    exact L2_birkhoff_integral_iterate ν T hν (fun x => (g x)^2)
      (hg.aestronglyMeasurable.pow 2) k
  simp_rw [hconst]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

theorem L2_birkhoffAverage_le {X : Type*} [MeasurableSpace X]
    (ν : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure ν]
    (T : X → X) (hν : MeasureTheory.MeasurePreserving T ν ν)
    (g : X → ℝ) (hg : MeasureTheory.MemLp g 2 ν) (n : ℕ) :
    Real.sqrt (∫ x, (birkhoffAverage ℝ T g n x)^2 ∂ν)
      ≤ Real.sqrt (∫ x, (g x)^2 ∂ν) := by
  apply Real.sqrt_le_sqrt
  have hpt : ∀ x, birkhoffAverage ℝ T g n x = (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, g (T^[k] x) := by
    intro x; simp [birkhoffAverage, birkhoffSum, smul_eq_mul]
  have hJens : ∀ x, (birkhoffAverage ℝ T g n x)^2
      ≤ (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (g (T^[k] x))^2 := by
    intro x
    rw [hpt x]
    exact L2_birkhoff_sq_inv_sum_le n (fun k => g (T^[k] x))
  have hBint : Integrable (fun x => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (g (T^[k] x))^2) ν := by
    refine Integrable.const_mul ?_ _
    exact integrable_finsetSum _
      (fun k _ => (hg.comp_measurePreserving (hν.iterate k)).integrable_sq)
  have hAB : ∫ x, (birkhoffAverage ℝ T g n x)^2 ∂ν
      ≤ ∫ x, (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (g (T^[k] x))^2 ∂ν :=
    integral_mono_of_nonneg (ae_of_all _ (fun x => sq_nonneg _)) hBint (ae_of_all _ hJens)
  have hBval := L2_birkhoff_integral_sum_sq ν T hν g hg n
  have hgnn : 0 ≤ ∫ x, (g x)^2 ∂ν := integral_nonneg_of_ae (ae_of_all _ (fun x => sq_nonneg _))
  have hle1 : (n : ℝ)⁻¹ * n ≤ 1 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · rw [inv_mul_cancel₀ (Nat.cast_ne_zero.mpr h.ne')]
  calc ∫ x, (birkhoffAverage ℝ T g n x)^2 ∂ν
      ≤ ∫ x, (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (g (T^[k] x))^2 ∂ν := hAB
    _ = (n : ℝ)⁻¹ * n * ∫ x, (g x)^2 ∂ν := hBval
    _ ≤ ∫ x, (g x)^2 ∂ν := by
          simpa using mul_le_mul_of_nonneg_right hle1 hgnn

end Work.EKLC6Core
