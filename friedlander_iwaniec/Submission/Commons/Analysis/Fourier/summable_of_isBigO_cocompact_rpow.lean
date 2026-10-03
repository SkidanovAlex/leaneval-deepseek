import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.PSeries

namespace Commons.Analysis.Fourier

open Filter Asymptotics
open scoped Topology

/-- If `d > 0` then `|x / d| ^ (-b) = d ^ b * |x| ^ (-b)`. -/
theorem abs_div_rpow_neg (x d b : ℝ) (hd : 0 < d) :
    |x / d| ^ (-b) = d ^ b * |x| ^ (-b) := by
  rw [abs_div, abs_of_pos hd, div_eq_mul_inv,
    Real.mul_rpow (abs_nonneg x) (inv_nonneg.mpr hd.le),
    Real.inv_rpow hd.le (-b), Real.rpow_neg hd.le b, inv_inv]
  ring

/-- If `G : ℝ → ℂ` decays like `|x| ^ (-b)` along the cocompact filter with `b > 1`, then the
sequence `k ↦ G (k / d)` is summable over `ℤ` for every `d > 0`. -/
theorem summable_of_isBigO_cocompact_rpow {G : ℝ → ℂ} {b : ℝ} (hb : 1 < b)
    (hG : Asymptotics.IsBigO (Filter.cocompact ℝ) G (fun x : ℝ => |x| ^ (-b)))
    {d : ℝ} (hd : 0 < d) :
    Summable fun k : ℤ => G ((k:ℝ) / d) := by
  obtain ⟨c, hcpos, hc⟩ := hG.exists_pos
  -- Extract a threshold beyond which the decay bound holds.
  have hS : {x : ℝ | ‖G x‖ ≤ c * ‖|x| ^ (-b)‖} ∈ Filter.cocompact ℝ := hc.bound
  rw [Metric.mem_cocompact_iff_closedBall_compl_subset (0 : ℝ)] at hS
  obtain ⟨R, hR⟩ := hS
  have hbound : ∀ x : ℝ, R < ‖x‖ → ‖G x‖ ≤ c * ‖|x| ^ (-b)‖ := by
    intro x hx
    refine hR ?_
    simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right]
    exact not_le.mpr hx
  -- Only finitely many lattice points satisfy `‖k / d‖ ≤ R`.
  have hfin : ({k : ℤ | ‖(k:ℝ) / d‖ ≤ R}).Finite := by
    set n : ℕ := Nat.ceil (max (R * d) 0) with hn
    refine Set.Finite.subset (Set.finite_Icc (-(n:ℤ)) (n:ℤ)) ?_
    intro k hk
    simp only [Set.mem_ofPred_eq] at hk
    rw [Set.mem_Icc]
    have hnorm : ‖(k:ℝ) / d‖ = |(k:ℝ)| / d := by
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hd]
    rw [hnorm] at hk
    have hRd : |(k:ℝ)| ≤ R * d := (div_le_iff₀ hd).mp hk
    have hmax : |(k:ℝ)| ≤ (max (R * d) 0 : ℝ) := le_trans hRd (le_max_left _ _)
    have hnge : (max (R * d) 0 : ℝ) ≤ (n : ℝ) := by
      rw [hn]; exact Nat.le_ceil _
    have hn2 : |(k:ℝ)| ≤ (n : ℝ) := le_trans hmax hnge
    have hn3 : (|k| : ℤ) ≤ (n : ℤ) := by
      have h : (((|k| : ℤ)) : ℝ) ≤ ((n : ℤ) : ℝ) := by
        simpa only [Int.cast_abs, Int.cast_natCast] using hn2
      exact_mod_cast h
    exact abs_le.mp hn3
  have hev : ∀ᶠ k : ℤ in cofinite, R < ‖(k:ℝ) / d‖ := by
    rw [Filter.eventually_cofinite]
    exact hfin.subset fun k hk => by
      simp only [Set.mem_ofPred_eq] at hk ⊢
      exact not_lt.mp hk
  -- Comparison series: `c * d ^ b * |k| ^ (-b)`.
  have hg : Summable fun k : ℤ => c * d ^ b * |(k:ℝ)| ^ (-b) :=
    (Real.summable_abs_int_rpow hb).mul_left (c * d ^ b)
  refine Summable.of_norm_bounded_eventually hg ?_
  filter_upwards [hev] with k hk
  have h1 : ‖G ((k:ℝ) / d)‖ ≤ c * ‖|(k:ℝ) / d| ^ (-b)‖ := hbound _ hk
  have h2 : ‖|(k:ℝ) / d| ^ (-b)‖ = |(k:ℝ) / d| ^ (-b) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  rw [h2, abs_div_rpow_neg (k:ℝ) d b hd] at h1
  calc ‖G ((k:ℝ) / d)‖ ≤ c * (d ^ b * |(k:ℝ)| ^ (-b)) := h1
    _ = c * d ^ b * |(k:ℝ)| ^ (-b) := by ring

end Commons.Analysis.Fourier