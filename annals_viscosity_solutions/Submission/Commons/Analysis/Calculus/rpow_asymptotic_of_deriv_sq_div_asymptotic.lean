import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open Filter Set MeasureTheory
open scoped Topology

set_option linter.unusedVariables false

namespace Commons.Analysis.Calculus

theorem tendsto_div_sub_of_tendsto_deriv_nhdsGT {f f' : ℝ → ℝ} {c l ε : ℝ} (hε : 0 < ε)
    (hf : ∀ t ∈ Set.Ioo (0:ℝ) ε, HasDerivAt f (f' t) t)
    (hl : Filter.Tendsto f' (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds l))
    (hc : Filter.Tendsto f (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds c)) :
    Filter.Tendsto (fun t : ℝ => (f t - c) / t) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds l) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro γ hγ
  set γ' : ℝ := γ / 2 with hγ'def
  have hγ'pos : 0 < γ' := by rw [hγ'def]; linarith
  have hγ'lt : γ' < γ := by rw [hγ'def]; linarith
  obtain ⟨δ1, hδ1pos, hδ1⟩ := (Metric.tendsto_nhdsWithin_nhds.mp hl) γ' hγ'pos
  refine ⟨min δ1 ε, lt_min hδ1pos hε, ?_⟩
  intro t htpos htδ
  have htδ' : t < min δ1 ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos htpos] at htδ; exact htδ
  have ht1 : t < δ1 := lt_of_lt_of_le htδ' (min_le_left _ _)
  have htε : t < ε := lt_of_lt_of_le htδ' (min_le_right _ _)
  have hlimψ : Tendsto (fun s : ℝ => (f t - f s) / (t - s) - l)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((f t - c) / t - l)) := by
    have h1 : Tendsto (fun s : ℝ => f t - f s) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (f t - c)) :=
      tendsto_const_nhds.sub hc
    have hid : Tendsto (fun s : ℝ => s) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun s : ℝ => t - s) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds t) := by
      simpa using (tendsto_const_nhds.sub hid : Tendsto (fun s : ℝ => t - s)
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (t - 0)))
    exact (h1.div h2 (ne_of_gt htpos)).sub_const l
  have hstep : ∀ᶠ s in nhdsWithin (0:ℝ) (Ioi 0),
      |(f t - f s) / (t - s) - l| < γ' := by
    refine eventually_nhdsWithin_iff.mpr ?_
    filter_upwards [Iio_mem_nhds htpos] with s hst hsIoi
    have hs0 : 0 < s := hsIoi
    obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope f f' hst
      (by
        apply DifferentiableOn.continuousOn (𝕜 := ℝ)
        intro x hx
        exact (hf x ⟨lt_of_lt_of_le hs0 hx.1, lt_of_le_of_lt hx.2 htε⟩).differentiableAt.differentiableWithinAt)
      (by intro x hx; exact hf x ⟨lt_trans hs0 hx.1, lt_trans hx.2 htε⟩)
    have hξ0 : 0 < ξ := lt_trans hs0 hξ.1
    have hξδ1 : ξ < δ1 := lt_trans hξ.2 ht1
    have hdist : dist ξ 0 < δ1 := by rw [Real.dist_eq, sub_zero, abs_of_pos hξ0]; exact hξδ1
    have hb : |f' ξ - l| < γ' := by
      have := hδ1 hξ0 hdist
      rwa [Real.dist_eq] at this
    rw [← hξeq]
    exact hb
  have hbdd1 : ∀ᶠ s in nhdsWithin (0:ℝ) (Ioi 0), (f t - f s) / (t - s) - l ≤ γ' := by
    filter_upwards [hstep] with s hs
    exact le_of_lt (abs_lt.mp hs).2
  have hbdd2 : ∀ᶠ s in nhdsWithin (0:ℝ) (Ioi 0), -γ' ≤ (f t - f s) / (t - s) - l := by
    filter_upwards [hstep] with s hs
    exact le_of_lt (abs_lt.mp hs).1
  have hle1 : (f t - c) / t - l ≤ γ' := le_of_tendsto hlimψ hbdd1
  have hle2 : -γ' ≤ (f t - c) / t - l := ge_of_tendsto hlimψ hbdd2
  rw [Real.dist_eq]
  have : |(f t - c) / t - l| ≤ γ' := abs_le.mpr ⟨hle2, hle1⟩
  linarith


theorem rpow_asymptotic_of_deriv_sq_div_asymptotic {f : ℝ → ℝ} {b η ε : ℝ}
    (hε : 0 < ε) (hb : 1 < b) (hη : 0 < η)
    (hf1 : ∀ t ∈ Set.Ioo (0:ℝ) ε, HasDerivAt f (deriv f t) t)
    (hfint : ∀ a u : ℝ, 0 < a → a ≤ u → u < ε → IntervalIntegrable (deriv f) MeasureTheory.volume a u)
    (hfpos : ∀ t ∈ Set.Ioo (0:ℝ) ε, 0 < f t)
    (hmono : ∀ t ∈ Set.Ioo (0:ℝ) ε, 0 ≤ deriv f t)
    (hlim : Filter.Tendsto f (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0))
    (hηlim : Filter.Tendsto (fun t : ℝ => (deriv f t) ^ (2:ℕ) / (f t) ^ (2 / b))
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds η)) :
    Filter.Tendsto (fun t : ℝ => f t / t ^ (b / (b - 1)))
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds ((((b - 1) / b) * Real.sqrt η) ^ (b / (b - 1)))) := by
  have hbpos : 0 < b := by linarith
  let r : ℝ := (b - 1) / b
  let p : ℝ := b / (b - 1)
  have hrpos : 0 < r := by
    show 0 < (b - 1) / b
    exact div_pos (by linarith) hbpos
  have hb1ne : (b:ℝ) - 1 ≠ 0 := by linarith
  have hrp : r * p = 1 := by
    show (b - 1) / b * (b / (b - 1)) = 1
    rw [div_mul_div_comm, mul_comm b (b - 1)]
    exact div_self (mul_ne_zero hb1ne (ne_of_gt hbpos))
  have hexp : (r - 1) * (2:ℝ) = -(2 / b) := by
    show ((b - 1) / b - 1) * 2 = -(2 / b)
    field_simp
    ring
  let g : ℝ → ℝ := fun t => (f t) ^ r
  have hevlt : ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0), t < ε := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds hε] with t ht _
    exact ht
  have hderivg : ∀ t ∈ Set.Ioo (0:ℝ) ε, HasDerivAt g (deriv f t * r * (f t) ^ (r - 1)) t := by
    intro t ht
    have hft : 0 < f t := hfpos t ht
    exact (hf1 t ht).rpow_const (Or.inl (ne_of_gt hft))
  have hderivg_eq : ∀ t ∈ Set.Ioo (0:ℝ) ε, deriv g t = deriv f t * r * (f t) ^ (r - 1) :=
    fun t ht => (hderivg t ht).deriv
  have hderivg' : ∀ t ∈ Set.Ioo (0:ℝ) ε, HasDerivAt g (deriv g t) t := by
    intro t ht
    rw [hderivg_eq t ht]
    exact hderivg t ht
  have hnng : ∀ t ∈ Set.Ioo (0:ℝ) ε, 0 ≤ deriv g t := by
    intro t ht
    rw [hderivg_eq t ht]
    exact mul_nonneg (mul_nonneg (hmono t ht) (le_of_lt hrpos))
      (le_of_lt (Real.rpow_pos_of_pos (hfpos t ht) (r - 1)))
  have hsq : ∀ t ∈ Set.Ioo (0:ℝ) ε,
      (deriv g t) ^ (2:ℕ) = r ^ 2 * ((deriv f t) ^ (2:ℕ) / (f t) ^ (2 / b)) := by
    intro t ht
    have hft : 0 < f t := hfpos t ht
    rw [hderivg_eq t ht]
    have hpp : ((f t) ^ (r - 1)) ^ (2:ℕ) = (f t) ^ (-(2 / b)) := by
      calc ((f t) ^ (r - 1)) ^ (2:ℕ)
          = ((f t) ^ (r - 1)) ^ (2:ℝ) := (Real.rpow_natCast ((f t) ^ (r - 1)) 2).symm
        _ = (f t) ^ ((r - 1) * (2:ℝ)) := (Real.rpow_mul (le_of_lt hft) (r - 1) (2:ℝ)).symm
        _ = (f t) ^ (-(2 / b)) := by rw [hexp]
    rw [mul_pow, mul_pow, hpp, Real.rpow_neg (le_of_lt hft) (2 / b), div_eq_mul_inv]
    ring
  have hsqlim : Filter.Tendsto (fun t : ℝ => (deriv g t) ^ (2:ℕ))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (r ^ 2 * η)) := by
    have hmul : Filter.Tendsto (fun t : ℝ => r ^ 2 * ((deriv f t) ^ (2:ℕ) / (f t) ^ (2 / b)))
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (r ^ 2 * η)) := hηlim.const_mul (r ^ 2)
    refine Filter.Tendsto.congr' ?_ hmul
    filter_upwards [self_mem_nhdsWithin, hevlt] with t ht hlt
    exact (hsq t ⟨ht, hlt⟩).symm
  have hlimg : Filter.Tendsto g (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
    have h := hlim.rpow_const (Or.inr (le_of_lt hrpos))
    simpa [Real.zero_rpow (ne_of_gt hrpos)] using h
  have hderivglim : Filter.Tendsto (deriv g) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (r * Real.sqrt η)) := by
    have hsqroot : Real.sqrt (r ^ 2 * η) = r * Real.sqrt η := by
      rw [Real.sqrt_mul (sq_nonneg r) η, Real.sqrt_sq (le_of_lt hrpos)]
    have hsqrtlim : Filter.Tendsto (fun t : ℝ => Real.sqrt ((deriv g t) ^ (2:ℕ)))
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (Real.sqrt (r ^ 2 * η))) := hsqlim.sqrt
    rw [hsqroot] at hsqrtlim
    refine Filter.Tendsto.congr' ?_ hsqrtlim
    filter_upwards [self_mem_nhdsWithin, hevlt] with t ht hlt
    exact Real.sqrt_sq (hnng t ⟨ht, hlt⟩)
  have hlhop : Filter.Tendsto (fun t : ℝ => g t / t)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (r * Real.sqrt η)) := by
    have h := tendsto_div_sub_of_tendsto_deriv_nhdsGT hε hderivg' hderivglim hlimg
    simpa using h
  have hrsqrtη : 0 < r * Real.sqrt η := mul_pos hrpos (Real.sqrt_pos_of_pos hη)
  have hpowlim : Filter.Tendsto (fun t : ℝ => (g t / t) ^ p)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((r * Real.sqrt η) ^ p)) :=
    hlhop.rpow_const (Or.inl (ne_of_gt hrsqrtη))
  refine Filter.Tendsto.congr' ?_ hpowlim
  filter_upwards [self_mem_nhdsWithin, hevlt] with t ht hlt
  have hft : 0 < f t := hfpos t ⟨ht, hlt⟩
  show (g t / t) ^ p = f t / t ^ p
  have hgt : g t = (f t) ^ r := rfl
  rw [hgt, Real.div_rpow (le_of_lt (Real.rpow_pos_of_pos hft r)) (le_of_lt ht) p,
    ← Real.rpow_mul (le_of_lt hft) r p, hrp, Real.rpow_one]

end Commons.Analysis.Calculus