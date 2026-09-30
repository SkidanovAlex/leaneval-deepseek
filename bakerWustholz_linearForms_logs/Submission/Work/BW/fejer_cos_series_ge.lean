import Mathlib
import Submission.Work.BW.mvdefs
import Submission.Work.BW.fejer_cross_nonneg

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Fejér/positivity lower bound for a cosine series

For a nonnegative summable coefficient sequence `c`, an arbitrary phase `a` and an arbitrary
frequency family `ψ`, the Fejér-weighted pairing of `cos (2πka)` with the cosine series
`∑_m c_m cos (2πk ψ_m)` is bounded below by `-(1/2) ∑_m c_m`.

This is the special case of the Fejér cross-correlation inequality `Work.BW.fejer_cross_nonneg`
in which the second cosine series is the single point mass at `0`.
-/

namespace Work.BW

open Finset

theorem fejer_cos_series_ge (c : ℕ → ℝ) (hc0 : ∀ m, 0 ≤ c m) (hcS : Summable c)
    (K : ℕ) (a : ℝ) (ψ : ℕ → ℝ) :
    -(1/2) * (∑' m, c m) ≤
      ∑ k ∈ Finset.Icc 1 K, fejerW K k * Real.cos (2*Real.pi*k*a) *
        (∑' m, c m * Real.cos (2*Real.pi*k*ψ m)) := by
  classical
  -- The point mass at `0`, used as the second cosine series with constant phase `a`.
  set d : ℕ → ℝ := fun m => if m = 0 then 1 else 0 with hd
  have hd0 : ∀ m, 0 ≤ d m := by
    intro m; rw [hd]; by_cases h : m = 0 <;> simp [h]
  have hds : Summable d := by
    refine summable_of_ne_finset_zero (s := ({0} : Finset ℕ)) ?_
    intro m hm
    rw [hd]
    simp only [Finset.mem_singleton] at hm
    simp [hm]
  -- `∑_m d_m = 1`.
  have hd_sum : (∑' m, d m) = 1 := by
    rw [tsum_eq_single 0]
    · rw [hd]; simp
    · intro b hb; rw [hd]; simp [hb]
  -- `∑_m d_m cos (k · (2πa)) = cos (2πka)`.
  have hd_cos : ∀ k : ℕ, (∑' m, d m * Real.cos ((k:ℝ) * (2*Real.pi*a)))
      = Real.cos (2*Real.pi*k*a) := by
    intro k
    rw [tsum_eq_single 0]
    · rw [hd]
      simp only [ite_true, one_mul]
      congr 1; ring
    · intro b hb; rw [hd]; simp [hb]
  -- The `c`-series with frequency `2πψ_m` is the statement's cosine series.
  have hc_cos : ∀ k : ℕ, (∑' m, c m * Real.cos ((k:ℝ) * (2*Real.pi*ψ m)))
      = (∑' m, c m * Real.cos (2*Real.pi*k*ψ m)) := by
    intro k
    apply tsum_congr; intro m
    congr 1; ring_nf
  -- The two Fejér weights coincide.
  have hW : ∀ k : ℕ, lmW K k = fejerW K k := by
    intro k; simp only [lmW, fejerW]
  -- The general Fejér cross-correlation inequality.
  have hcross := fejer_cross_nonneg K c d (fun m => 2*Real.pi*ψ m) (fun _ => 2*Real.pi*a)
      hc0 hd0 hcS hds
  -- Rewrite it into the shape of the statement.
  have hrewrite : (∑ k ∈ Finset.Icc 1 K, lmW K k *
        ((∑' m, c m * Real.cos ((k:ℝ) * (2*Real.pi*ψ m))) *
         (∑' m, d m * Real.cos ((k:ℝ) * (2*Real.pi*a)))))
      = ∑ k ∈ Finset.Icc 1 K, fejerW K k * Real.cos (2*Real.pi*k*a) *
          (∑' m, c m * Real.cos (2*Real.pi*k*ψ m)) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [hd_cos k, hc_cos k, hW k]
    ring
  rw [hrewrite, hd_sum, mul_one] at hcross
  linarith

end Work.BW
