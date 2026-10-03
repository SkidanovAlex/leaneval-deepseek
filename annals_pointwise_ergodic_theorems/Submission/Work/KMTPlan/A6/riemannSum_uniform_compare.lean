import Mathlib
import Submission.Work.KMTPlan.A6.sum_inv_sq_linear_int_le
import Submission.Work.KMTPlan.A6.min_le_eight_mul_inv_sq
import Submission.Work.KMTPlan.A6.inv_sq_bound_arith

namespace Work.KMTPlan.A6

open MeasureTheory Filter Finset
open scoped ENNReal BigOperators Topology

/-- **The Riemann-sum bound.**  If `g ≥ 0` is bounded by `min ε (2A/(1+t²))`, then the Riemann sum
of `g` on the lattice `(Q/R)ℤ` with mesh weight `1/R` is at most `100(√(Aε)/Q + ε/R)`.

The proof dominates `min ε (2A/(1+t²))` by `8A/(T+|x|)²` with `T = √(2A/ε)`
(`min_le_eight_mul_inv_sq`), sums the latter over `ℤ` using the telescoping bound
`sum_inv_sq_linear_int_le`, and evaluates the resulting elementary expression
(`inv_sq_bound_arith`). -/
theorem riemann_tsum_bound (Q : ℕ) (hQ : 0 < Q) (R : ℕ) (hR : 1 ≤ R)
    (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε)
    (g : ℝ → ℝ) (hg0 : ∀ t, 0 ≤ g t) (hg : ∀ t, g t ≤ min ε (2 * A / (1 + t ^ 2))) :
    (∑' m : ℤ, (R : ℝ)⁻¹ * g ((Q : ℝ) * (m : ℝ) / (R : ℝ)))
      ≤ 100 * (Real.sqrt (A * ε) / (Q : ℝ) + ε / (R : ℝ)) := by
  set T : ℝ := Real.sqrt (2 * A / ε) with hTdef
  have hTpos : 0 < T := by
    rw [hTdef]; exact Real.sqrt_pos.mpr (by positivity)
  have hT2 : T ^ 2 = 2 * A / ε := by
    rw [hTdef]; exact Real.sq_sqrt (by positivity)
  have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hRpos : (0 : ℝ) < (R : ℝ) := by
    have h : (0 : ℕ) < R := lt_of_lt_of_le Nat.zero_lt_one hR
    exact_mod_cast h
  have hcpos : 0 < (Q : ℝ) / (R : ℝ) := div_pos hQpos hRpos
  refine Real.tsum_le_of_sum_le (f := fun m : ℤ =>
      (R : ℝ)⁻¹ * g ((Q : ℝ) * (m : ℝ) / (R : ℝ))) ?_ ?_
  · intro m
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg R)) (hg0 _)
  · intro u
    have hpt : ∀ m : ℤ, (R : ℝ)⁻¹ * g ((Q : ℝ) * (m : ℝ) / (R : ℝ))
        ≤ (R : ℝ)⁻¹ * (8 * A / (T + ((Q : ℝ) / (R : ℝ)) * |(m : ℝ)|) ^ 2) := by
      intro m
      have habs : |((Q : ℝ) * (m : ℝ) / (R : ℝ))| = ((Q : ℝ) / (R : ℝ)) * |(m : ℝ)| := by
        rw [abs_div, abs_mul, abs_of_pos hQpos, abs_of_pos hRpos]
        ring
      have h1 : g ((Q : ℝ) * (m : ℝ) / (R : ℝ))
          ≤ 8 * A / (T + |((Q : ℝ) * (m : ℝ) / (R : ℝ))|) ^ 2 := by
        rw [hTdef]
        exact le_trans (hg _)
          (min_le_eight_mul_inv_sq (A := A) (ε := ε) (x := (Q : ℝ) * (m : ℝ) / (R : ℝ)) hA hε)
      rw [habs] at h1
      exact mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr (Nat.cast_nonneg R))
    calc ∑ m ∈ u, (R : ℝ)⁻¹ * g ((Q : ℝ) * (m : ℝ) / (R : ℝ))
        ≤ ∑ m ∈ u, (R : ℝ)⁻¹ * (8 * A / (T + ((Q : ℝ) / (R : ℝ)) * |(m : ℝ)|) ^ 2) :=
          Finset.sum_le_sum (fun m _ => hpt m)
      _ = (R : ℝ)⁻¹ * (8 * A) * ∑ m ∈ u, 1 / (T + ((Q : ℝ) / (R : ℝ)) * |(m : ℝ)|) ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun m _ => by ring)
      _ ≤ (R : ℝ)⁻¹ * (8 * A) * (1 / T ^ 2 + 2 / (((Q : ℝ) / (R : ℝ)) * T)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact (sum_inv_sq_linear_int_le T ((Q : ℝ) / (R : ℝ)) hTpos hcpos).1 u
      _ = 8 * A / ((R : ℝ) * T ^ 2) + 16 * A / ((Q : ℝ) * T) := by
          field_simp
          ring
      _ ≤ 100 * (Real.sqrt (A * ε) / (Q : ℝ) + ε / (R : ℝ)) :=
          inv_sq_bound_arith (A := A) (ε := ε) (T := T) (Q := (Q : ℝ)) (R := (R : ℝ))
            hA hε hTpos hT2 hQpos hRpos

theorem riemannSum_uniform_compare (Q : ℕ) (hQ : 0 < Q) (Φ : ℕ → ℝ → ℂ) (Ψ : ℝ → ℝ)
    (A : ℝ) (hA : 0 ≤ A)
    (hΦ : ∀ R t, ‖Φ R t‖ ≤ A / (1 + |t|) ^ 2)
    (hΨ : ∀ t : ℝ, |Ψ t| ≤ A / (1 + |t|) ^ 2)
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∀ t : ℝ, |‖Φ R t‖ - Ψ t| ≤ ε) :
    Filter.Tendsto (fun R : ℕ => ∑' m : ℤ,
        (R : ℝ)⁻¹ * |‖Φ R (((Q : ℝ) * (m : ℝ)) / (R : ℝ))‖ - Ψ (((Q : ℝ) * (m : ℝ)) / (R : ℝ))|)
      Filter.atTop (nhds 0) := by
  let f : ℕ → ℝ → ℝ := fun R t => |‖Φ R t‖ - Ψ t|
  change Filter.Tendsto (fun R : ℕ => ∑' m : ℤ,
      (R : ℝ)⁻¹ * f R (((Q : ℝ) * (m : ℝ)) / (R : ℝ))) Filter.atTop (nhds 0)
  have hf0 : ∀ R t, 0 ≤ f R t := fun R t => abs_nonneg _
  have hf2 : ∀ R t, f R t ≤ 2 * A / (1 + |t|) ^ 2 := by
    intro R t
    have hcase : f R t ≤ A / (1 + |t|) ^ 2 + A / (1 + |t|) ^ 2 := by
      simp only [f]
      rw [abs_sub_le_iff]
      constructor
      · have h1 := hΦ R t
        have h2 := hΨ t
        have h3 : -Ψ t ≤ |Ψ t| := neg_le_abs (Ψ t)
        linarith
      · have h1 := hΦ R t
        have h2 := hΨ t
        have h3 : Ψ t ≤ |Ψ t| := le_abs_self (Ψ t)
        have h4 : (0 : ℝ) ≤ A / (1 + |t|) ^ 2 := by positivity
        have h5 : -‖Φ R t‖ ≤ 0 := neg_nonpos.mpr (norm_nonneg _)
        linarith
    calc f R t ≤ A / (1 + |t|) ^ 2 + A / (1 + |t|) ^ 2 := hcase
      _ = 2 * A / (1 + |t|) ^ 2 := by ring
  have hfA : ∀ R t, f R t ≤ 2 * A / (1 + t ^ 2) := by
    intro R t
    refine le_trans (hf2 R t) ?_
    have hden : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by
      nlinarith [abs_nonneg t, sq_abs t]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · have hzero : ∀ R t, f R t = 0 := by
      intro R t
      have hA0' : A = 0 := hA0.symm
      have h1 : ‖Φ R t‖ = 0 := by
        have h := hΦ R t
        rw [hA0', zero_div] at h
        exact le_antisymm h (norm_nonneg _)
      have h2 : Ψ t = 0 := by
        have h := hΨ t
        rw [hA0', zero_div] at h
        exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
      simp [f, h1, h2]
    have hfun : (fun R : ℕ => ∑' m : ℤ, (R : ℝ)⁻¹ * f R (((Q : ℝ) * (m : ℝ)) / (R : ℝ)))
        = fun _ => 0 := by
      funext R
      simp only [hzero R, mul_zero]
      exact tsum_zero
    rw [hfun]
    exact tendsto_const_nhds
  · rw [Metric.tendsto_atTop]
    intro δ hδ
    have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
    set ε : ℝ := δ ^ 2 * (Q : ℝ) ^ 2 / (160000 * A) with hεdef
    have hεpos : 0 < ε := by
      rw [hεdef]
      exact div_pos (by positivity) (by positivity)
    obtain ⟨R₀, hR₀⟩ := hconv ε hεpos
    obtain ⟨R₁, hR₁⟩ : ∃ R₁ : ℕ, 400 * ε / δ < (R₁ : ℝ) := exists_nat_gt _
    refine ⟨max R₀ (max R₁ 1), fun R hR => ?_⟩
    have hRR0 : R₀ ≤ R := le_trans (le_max_left _ _) hR
    have hRR1 : R₁ ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hR
    have hR1 : 1 ≤ R := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hR
    have hfet : ∀ t : ℝ, f R t ≤ ε := fun t => by
      have h := hR₀ R hRR0 t
      simpa [f] using h
    have hmin : ∀ t : ℝ, f R t ≤ min ε (2 * A / (1 + t ^ 2)) :=
      fun t => le_min (hfet t) (hfA R t)
    have hkey := riemann_tsum_bound Q hQ R hR1 A ε hApos hεpos (f R) (hf0 R) hmin
    have hnonneg : 0 ≤ ∑' m : ℤ, (R : ℝ)⁻¹ * f R (((Q : ℝ) * (m : ℝ)) / (R : ℝ)) :=
      tsum_nonneg (fun m => mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg R)) (hf0 R _))
    have hsqrt_eq : 100 * Real.sqrt (A * ε) / (Q : ℝ) = δ / 4 := by
      have hAε : A * ε = (δ * (Q : ℝ) / 400) ^ 2 := by
        rw [hεdef]
        field_simp
        ring
      have hsqrt : Real.sqrt (A * ε) = δ * (Q : ℝ) / 400 := by
        rw [hAε]
        exact Real.sqrt_sq (by positivity)
      rw [hsqrt]
      field_simp
      ring
    have hdiv_lt : 100 * ε / (R : ℝ) < δ / 4 := by
      have hR₁pos : (0 : ℝ) < (R₁ : ℝ) := lt_of_le_of_lt (by positivity) hR₁
      have hRpos : (0 : ℝ) < (R : ℝ) := lt_of_lt_of_le hR₁pos (by exact_mod_cast hRR1)
      have hle : 100 * ε / (R : ℝ) ≤ 100 * ε / (R₁ : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) hR₁pos (by exact_mod_cast hRR1)
      have hlt : 100 * ε / (R₁ : ℝ) < δ / 4 := by
        have hpos : (0 : ℝ) < 400 * ε / δ := by positivity
        calc 100 * ε / (R₁ : ℝ) < 100 * ε / (400 * ε / δ) :=
              div_lt_div_of_pos_left (by positivity) hpos hR₁
          _ = δ / 4 := by field_simp; ring
      linarith
    have hfin : 100 * (Real.sqrt (A * ε) / (Q : ℝ) + ε / (R : ℝ)) < δ := by
      have : 100 * (Real.sqrt (A * ε) / (Q : ℝ) + ε / (R : ℝ))
          = 100 * Real.sqrt (A * ε) / (Q : ℝ) + 100 * ε / (R : ℝ) := by ring
      rw [this]; linarith
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
    linarith

end Work.KMTPlan.A6
