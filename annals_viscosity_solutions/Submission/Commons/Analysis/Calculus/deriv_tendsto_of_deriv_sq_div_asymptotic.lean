import Mathlib
import Submission.Commons.Analysis.Calculus.rpow_asymptotic_of_deriv_sq_div_asymptotic

open Filter Set
open scoped Topology

set_option autoImplicit false

namespace Commons.Analysis.Calculus

/-- Companion of `rpow_asymptotic_of_deriv_sq_div_asymptotic`: from `(f')²/f^(2/b) → η` one gets
the asymptotic behaviour of `f'` itself, `f'(t)/t^(1/(b-1)) → √η · ((b-1)/b · √η)^(1/(b-1))`. -/
theorem deriv_tendsto_of_deriv_sq_div_asymptotic {f : ℝ → ℝ} {b η ε : ℝ} (hε : 0 < ε) (hb : 1 < b)
    (hη : 0 < η)
    (hf1 : ∀ t ∈ Set.Ioo (0:ℝ) ε, HasDerivAt f (deriv f t) t)
    (hfpos : ∀ t ∈ Set.Ioo (0:ℝ) ε, 0 < f t)
    (hmono : ∀ t ∈ Set.Ioo (0:ℝ) ε, 0 ≤ deriv f t)
    (hlim : Filter.Tendsto f (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0))
    (hηlim : Filter.Tendsto (fun t : ℝ => (deriv f t) ^ (2:ℕ) / (f t) ^ (2 / b))
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds η)) :
    Filter.Tendsto (fun t : ℝ => deriv f t / t ^ (1 / (b - 1)))
      (nhdsWithin (0:ℝ) (Set.Ioi 0))
      (nhds (Real.sqrt η * (((b - 1) / b) * Real.sqrt η) ^ (1 / (b - 1)))) := by
  have hb1ne : (b : ℝ) - 1 ≠ 0 := by linarith
  have hbpos : 0 < b := by linarith
  have hbne : b ≠ 0 := ne_of_gt hbpos
  have hevlt : ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0), t < ε := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds hε] with t ht _
    exact ht
  set r : ℝ := (b - 1) / b with hrdef
  set q : ℝ := 1 / (b - 1) with hqdef
  have hrpos : 0 < r := by rw [hrdef]; exact div_pos (by linarith) hbpos
  have hqpos : 0 < q := by rw [hqdef]; exact div_pos one_pos (by linarith)
  have hrq : r * q = 1 / b := by rw [hrdef, hqdef]; field_simp; try ring
  have hrm1 : r - 1 = -(1 / b) := by rw [hrdef]; field_simp; try ring
  have hApos : 0 < r * Real.sqrt η := mul_pos hrpos (Real.sqrt_pos_of_pos hη)
  -- first factor: f' / f^{1/b} → √η
  have hHlim : Filter.Tendsto (fun t : ℝ => deriv f t / (f t) ^ (1 / b))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (Real.sqrt η)) := by
    have hsqrt := hηlim.sqrt
    refine Filter.Tendsto.congr' ?_ hsqrt
    filter_upwards [self_mem_nhdsWithin, hevlt] with t ht hlt
    have ht' : t ∈ Ioo (0:ℝ) ε := ⟨ht, hlt⟩
    have hfp : 0 < f t := hfpos t ht'
    have hgb : 0 ≤ deriv f t := hmono t ht'
    have hkey : Real.sqrt ((deriv f t) ^ (2:ℕ) / (f t) ^ (2 / b))
        = deriv f t / (f t) ^ (1 / b) := by
      rw [Real.sqrt_div (sq_nonneg (deriv f t)), Real.sqrt_sq hgb]
      rw [show (2:ℝ) / b = (1 / b) * 2 by ring]
      rw [Real.rpow_mul (le_of_lt hfp) (1 / b) (2:ℝ), Real.rpow_two]
      rw [Real.sqrt_sq (le_of_lt (Real.rpow_pos_of_pos hfp (1 / b)))]
    exact hkey
  -- F t = f t ^ r, its derivative tends to r * √η, and F → 0
  have hFderiv : ∀ t ∈ Ioo (0:ℝ) ε,
      HasDerivAt (fun s : ℝ => (f s) ^ r) (deriv f t * r * (f t) ^ (r - 1)) t := by
    intro t ht
    exact (hf1 t ht).rpow_const (Or.inl (ne_of_gt (hfpos t ht)))
  have hF'lim : Filter.Tendsto (fun t : ℝ => deriv f t * r * (f t) ^ (r - 1))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (r * Real.sqrt η)) := by
    have hmul := hHlim.const_mul r
    refine Filter.Tendsto.congr' ?_ hmul
    filter_upwards [self_mem_nhdsWithin, hevlt] with t ht hlt
    have ht' : t ∈ Ioo (0:ℝ) ε := ⟨ht, hlt⟩
    have hfp : 0 < f t := hfpos t ht'
    have hkey : deriv f t * r * (f t) ^ (r - 1)
        = r * (deriv f t / (f t) ^ (1 / b)) := by
      rw [hrm1, Real.rpow_neg (le_of_lt hfp) (1 / b), div_eq_mul_inv]
      ring
    exact hkey.symm
  have hFlim : Filter.Tendsto (fun s : ℝ => (f s) ^ r)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
    have h := hlim.rpow_const (Or.inr (le_of_lt hrpos))
    simpa [Real.zero_rpow (ne_of_gt hrpos)] using h
  have hdivlim : Filter.Tendsto (fun s : ℝ => (f s) ^ r / s)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (r * Real.sqrt η)) := by
    have h := tendsto_div_sub_of_tendsto_deriv_nhdsGT hε hFderiv hF'lim hFlim
    simpa using h
  -- second factor: f^{1/b} / t^q → (r√η)^q
  have hsec : Filter.Tendsto (fun t : ℝ => (f t) ^ (1 / b) / t ^ q)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((r * Real.sqrt η) ^ q)) := by
    have hpow : Filter.Tendsto (fun t : ℝ => ((f t) ^ r / t) ^ q)
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((r * Real.sqrt η) ^ q)) :=
      hdivlim.rpow_const (Or.inl (ne_of_gt hApos))
    refine Filter.Tendsto.congr' ?_ hpow
    filter_upwards [self_mem_nhdsWithin, hevlt] with t ht hlt
    have ht' : t ∈ Ioo (0:ℝ) ε := ⟨ht, hlt⟩
    have hfp : 0 < f t := hfpos t ht'
    have hkey : ((f t) ^ r / t) ^ q = (f t) ^ (1 / b) / t ^ q := by
      rw [Real.div_rpow (le_of_lt (Real.rpow_pos_of_pos hfp r)) (le_of_lt ht) q,
        ← Real.rpow_mul (le_of_lt hfp) r q, hrq]
    exact hkey
  -- product
  have hprod : Filter.Tendsto
      (fun t : ℝ => (deriv f t / (f t) ^ (1 / b)) * ((f t) ^ (1 / b) / t ^ q))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (Real.sqrt η * (r * Real.sqrt η) ^ q)) :=
    hHlim.mul hsec
  have hmain : Filter.Tendsto (fun t : ℝ => deriv f t / t ^ q)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (Real.sqrt η * (r * Real.sqrt η) ^ q)) := by
    refine Filter.Tendsto.congr' ?_ hprod
    filter_upwards [self_mem_nhdsWithin, hevlt] with t ht hlt
    have ht' : t ∈ Ioo (0:ℝ) ε := ⟨ht, hlt⟩
    have hfp : 0 < f t := hfpos t ht'
    have hpowne : (f t) ^ (1 / b) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hfp (1 / b))
    field_simp
  exact hmain

end Commons.Analysis.Calculus
