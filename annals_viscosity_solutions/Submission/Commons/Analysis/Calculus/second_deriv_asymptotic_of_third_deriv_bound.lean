import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Submission.Commons.Analysis.Calculus.tendsto_of_tendsto_average_of_deriv_bound
import Submission.Commons.Analysis.Calculus.rpow_asymptotic_of_deriv_sq_div_asymptotic

namespace Commons.Analysis.Calculus

set_option maxHeartbeats 4000000

open Filter Set MeasureTheory intervalIntegral
open scoped Topology

/-- Derivative of `s ↦ (deriv f s) ^ r` at a point where `deriv f` is differentiable with positive
value. -/
private lemma hasDerivAt_deriv_rpow {f : ℝ → ℝ} {r t : ℝ}
    (h : HasDerivAt (deriv f) (deriv (deriv f) t) t) (ht : 0 < deriv f t) :
    HasDerivAt (fun s => (deriv f s) ^ r) (r * (deriv f t) ^ (r - 1) * deriv (deriv f) t) t := by
  simpa [Function.comp_def, mul_assoc] using
    (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt ht)) (p := r)).comp t h

/-- **The `es:fs` refinement of the Sundman asymptotic analysis** (Ferrario–Terracini, `lemma:bach`):
if in addition to the two Sundman inequalities the third derivative of `f` is controlled by a power
of the second derivative `|f'''| ≤ e (f'')^((2b-3)/(b-2))`, then the second derivative itself has the
asymptotic behaviour `f'' · f^((b-2)/b) → η/b`, where `η = lim (f')²/f^(2/b)`. -/
theorem second_deriv_asymptotic_of_third_deriv_bound {f : ℝ → ℝ} {b c d e η ε : ℝ}
    (hε : 0 < ε) (hb : 2 < b) (hd : 0 < d) (he : 0 < e) (hη : 0 < η)
    (hf1 : ∀ t ∈ Set.Ioo (0:ℝ) ε, HasDerivAt f (deriv f t) t)
    (hf2 : ∀ t ∈ Set.Ioo (0:ℝ) ε, HasDerivAt (deriv f) (deriv (deriv f) t) t)
    (hf3 : ∀ t ∈ Set.Ioo (0:ℝ) ε,
      HasDerivAt (deriv (deriv f)) (deriv (deriv (deriv f)) t) t)
    (hfpos : ∀ t ∈ Set.Ioo (0:ℝ) ε, 0 < f t)
    (hineq : ∀ t ∈ Set.Ioo (0:ℝ) ε,
      (deriv f t) ^ (2:ℕ) ≤ b * f t * deriv (deriv f) t + c * f t)
    (hmono : ∀ t ∈ Set.Ioo (0:ℝ) ε, 0 ≤ deriv f t)
    (hlim : Filter.Tendsto f (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0))
    (hbound : ∀ t ∈ Set.Ioo (0:ℝ) ε, d ≤ deriv (deriv f) t * (f t) ^ ((b - 2) / b))
    (hthird : ∀ t ∈ Set.Ioo (0:ℝ) ε,
      |deriv (deriv (deriv f)) t| ≤ e * (deriv (deriv f) t) ^ ((2 * b - 3) / (b - 2)))
    (hηlim : Filter.Tendsto (fun t : ℝ => (deriv f t) ^ (2:ℕ) / (f t) ^ (2 / b))
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds η)) :
    Filter.Tendsto (fun t : ℝ => deriv (deriv f) t * (f t) ^ ((b - 2) / b))
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (η / b)) := by
  have hb0 : (0:ℝ) < b := by linarith
  have hb1 : (0:ℝ) < b - 1 := by linarith
  have hb2 : (0:ℝ) < b - 2 := by linarith
  set q : ℝ := (b - 2) / b with hq_def
  set p : ℝ := 2 / b with hp_def
  set r : ℝ := (b - 1) / b with hr_def
  have hqpos : 0 < q := by rw [hq_def]; positivity
  have hppos : 0 < p := by rw [hp_def]; positivity
  have hrpos : 0 < r := by rw [hr_def]; positivity
  have hevε : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), t ∈ Set.Ioo (0:ℝ) ε :=
    Ioo_mem_nhdsGT hε
  -- Step 0a: second derivative is strictly positive
  have hf2pos : ∀ t ∈ Set.Ioo (0:ℝ) ε, 0 < deriv (deriv f) t := by
    intro t ht
    have hbnd := hbound t ht
    have hpow : 0 < (f t) ^ q := Real.rpow_pos_of_pos (hfpos t ht) q
    have : 0 < d / (f t) ^ q := div_pos hd hpow
    have hrw : d / (f t) ^ q ≤ deriv (deriv f) t := by
      rw [div_le_iff₀ hpow]
      calc d ≤ deriv (deriv f) t * (f t) ^ ((b - 2) / b) := hbnd
        _ = deriv (deriv f) t * (f t) ^ q := by rw [hq_def]
    linarith
  -- Step 0b: eventually f' > 0
  have hevpos1 : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), 0 < deriv f t := by
    have hgt : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0),
        η / 2 < (deriv f t) ^ (2:ℕ) / (f t) ^ (2 / b) :=
      hηlim.eventually (isOpen_Ioi.mem_nhds (by linarith : η / 2 < η))
    filter_upwards [hgt, hevε] with t hgt' hmem
    have hnum : 0 < (deriv f t) ^ (2:ℕ) := by
      by_contra hcon
      rw [not_lt] at hcon
      have h0 : (deriv f t) ^ (2:ℕ) = 0 := le_antisymm hcon (by positivity)
      rw [h0] at hgt'
      simp only [zero_div] at hgt'
      linarith
    have hne : deriv f t ≠ 0 := by
      rintro h; rw [h] at hnum; simp at hnum
    exact lt_of_le_of_ne (hmono t hmem) (Ne.symm hne)
  -- Step 1: f' / f^(1/b) → sqrt η
  have hratio : Tendsto (fun t : ℝ => deriv f t / (f t) ^ (1 / b))
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (Real.sqrt η)) := by
    have hsq : Tendsto (fun t : ℝ => Real.sqrt ((deriv f t) ^ (2:ℕ) / (f t) ^ (2 / b)))
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (Real.sqrt η)) := hηlim.sqrt
    refine hsq.congr' ?_
    filter_upwards [hevε] with t ht
    have hft : 0 < f t := hfpos t ht
    have hft1 : 0 < (f t) ^ (1 / b) := Real.rpow_pos_of_pos hft (1 / b)
    have hdf : 0 ≤ deriv f t := hmono t ht
    have hBsq : ((f t) ^ (1 / b)) ^ (2:ℕ) = (f t) ^ (2 / b) := by
      rw [show ((f t) ^ (1 / b) : ℝ) ^ (2:ℕ) = ((f t) ^ (1 / b)) ^ (2:ℝ) from
        (Real.rpow_natCast ((f t) ^ (1 / b)) 2).symm]
      rw [← Real.rpow_mul (le_of_lt hft) (1 / b) (2:ℝ)]
      congr 1
      ring
    have hsq2 : (deriv f t / (f t) ^ (1 / b)) ^ (2:ℕ)
        = (deriv f t) ^ (2:ℕ) / (f t) ^ (2 / b) := by
      rw [div_pow, hBsq]
    rw [← hsq2, Real.sqrt_sq_eq_abs, abs_of_nonneg (div_nonneg hdf (le_of_lt hft1))]
  -- Step 2: w(t)/t → (b-1)/b sqrt η  where w = f^((b-1)/b)
  have hwlimit : Tendsto (fun t : ℝ => (f t) ^ r / t)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (r * Real.sqrt η)) := by
    have hderivw : ∀ t ∈ Set.Ioo (0:ℝ) ε,
        HasDerivAt (fun s => (f s) ^ r) (deriv f t * r * (f t) ^ (r - 1)) t := by
      intro t ht
      exact (hf1 t ht).rpow_const (Or.inl (ne_of_gt (hfpos t ht)))
    have hderivw_eq : ∀ t ∈ Set.Ioo (0:ℝ) ε,
        deriv (fun s => (f s) ^ r) t = deriv f t * r * (f t) ^ (r - 1) :=
      fun t ht => (hderivw t ht).deriv
    have hderivw' : ∀ t ∈ Set.Ioo (0:ℝ) ε,
        HasDerivAt (fun s => (f s) ^ r) (deriv (fun s => (f s) ^ r) t) t := by
      intro t ht
      rw [hderivw_eq t ht]
      exact hderivw t ht
    have hdlim : Tendsto (deriv (fun s => (f s) ^ r))
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (r * Real.sqrt η)) := by
      have heq : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0),
          deriv (fun s => (f s) ^ r) t = deriv f t * r * (f t) ^ (r - 1) := by
        filter_upwards [hevε] with t ht
        exact hderivw_eq t ht
      have h1 : Tendsto (fun t : ℝ => deriv f t * r * (f t) ^ (r - 1))
          (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (r * Real.sqrt η)) := by
        have hpowlim : Tendsto (fun t : ℝ => (f t) ^ (r - 1) * deriv f t)
            (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (Real.sqrt η)) := by
          have heq2 : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0),
              (f t) ^ (r - 1) * deriv f t = deriv f t / (f t) ^ (1 / b) := by
            filter_upwards [hevε] with t ht
            have hft : 0 < f t := hfpos t ht
            have hrm1 : r - 1 = -(1 / b) := by
              rw [hr_def, ← neg_div, eq_div_iff (ne_of_gt hb0)]
              field_simp
              ring
            rw [hrm1, Real.rpow_neg (le_of_lt hft) (1 / b), div_eq_mul_inv]
            ring
          exact hratio.congr' (by filter_upwards [heq2] with t ht; exact ht.symm)
        simpa [mul_comm, mul_assoc, mul_left_comm] using hpowlim.const_mul r
      exact (Tendsto.congr' (by filter_upwards [heq] with t ht; exact ht.symm) h1)
    have hw0 : Tendsto (fun s : ℝ => (f s) ^ r) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
      have h := hlim.rpow_const (Or.inr (le_of_lt hrpos))
      simpa [Real.zero_rpow (ne_of_gt hrpos)] using h
    have := tendsto_div_sub_of_tendsto_deriv_nhdsGT hε hderivw' hdlim hw0
    simpa using this
  -- Step 3: F(t)/t → Λ := (b-1)/b * η^(b/2)
  have hFlimit : Tendsto (fun t : ℝ => (deriv f t) ^ (b - 1) / t)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (((b - 1) / b) * η ^ (b / 2))) := by
    have hval : (r * Real.sqrt η) * (Real.sqrt η) ^ (b - 1)
        = ((b - 1) / b) * η ^ (b / 2) := by
      have hsqrt : Real.sqrt η = η ^ (1/2 : ℝ) := Real.sqrt_eq_rpow η
      rw [hsqrt]
      have hsq : (η ^ (1/2:ℝ)) ^ (b - 1) = η ^ ((b-1)/2) := by
        rw [← Real.rpow_mul (le_of_lt hη) (1/2) (b-1)]; congr 1; ring
      rw [hsq, hr_def, mul_assoc, ← Real.rpow_add hη (1/2) ((b-1)/2)]
      rw [show (1:ℝ)/2 + (b-1)/2 = b/2 by ring]
    have hprod : Tendsto (fun t : ℝ => ((f t) ^ r / t) * (deriv f t / (f t) ^ (1 / b)) ^ (b - 1))
        (nhdsWithin (0:ℝ) (Set.Ioi 0))
        (nhds (((b - 1) / b) * η ^ (b / 2))) := by
      have hm := hwlimit.mul (hratio.rpow_const (Or.inr (le_of_lt hb1)))
      rwa [hval] at hm
    refine hprod.congr' ?_
    filter_upwards [hevε] with t ht
    have hft : 0 < f t := hfpos t ht
    have hft1 : 0 < (f t) ^ (1 / b) := Real.rpow_pos_of_pos hft (1 / b)
    have hBs : ((f t) ^ (1 / b)) ^ (b - 1) = (f t) ^ r := by
      rw [← Real.rpow_mul (le_of_lt hft) (1 / b) (b - 1), hr_def]
      congr 1
      field_simp
    rw [Real.div_rpow (hmono t ht) (le_of_lt hft1) (b - 1), hBs]
    field_simp [ne_of_gt hft, ne_of_gt ht.1, ne_of_gt (Real.rpow_pos_of_pos hft r)]
  set Lam : ℝ := ((b - 1) / b) * η ^ (b / 2) with hLam_def
  have hLampos : 0 < Lam := by
    rw [hLam_def]; exact mul_pos (by positivity) (Real.rpow_pos_of_pos hη _)
  -- extract a small interval δ on which f' > 0 and F t ≥ (Lam/2) t
  obtain ⟨δ1, hδ1pos, hδ1⟩ := (nhdsGT_basis (0:ℝ)).eventually_iff.mp hevpos1
  have hevF : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0),
      Lam / 2 * t ≤ (deriv f t) ^ (b - 1) := by
    have h := hFlimit.eventually (isOpen_Ioi.mem_nhds (by linarith : Lam / 2 < Lam))
    filter_upwards [h, hevε] with t ht htε
    have ht0 : 0 < t := htε.1
    rw [lt_div_iff₀ ht0] at ht
    linarith
  obtain ⟨δ2, hδ2pos, hδ2⟩ := (nhdsGT_basis (0:ℝ)).eventually_iff.mp hevF
  set δ : ℝ := min (min δ1 δ2) ε with hδ_def
  have hδpos : 0 < δ := by
    rw [hδ_def]; exact lt_min (lt_min hδ1pos hδ2pos) hε
  have hδle_eps : δ ≤ ε := by rw [hδ_def]; exact min_le_right _ _
  have hδle1 : δ ≤ δ1 := by rw [hδ_def]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hδle2 : δ ≤ δ2 := by rw [hδ_def]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hδf1 : ∀ t ∈ Set.Ioo (0:ℝ) δ, 0 < deriv f t := fun t ht =>
    hδ1 (x := t) ⟨ht.1, lt_of_lt_of_le ht.2 hδle1⟩
  have hδFt : ∀ t ∈ Set.Ioo (0:ℝ) δ, Lam / 2 * t ≤ (deriv f t) ^ (b - 1) := fun t ht =>
    hδ2 (x := t) ⟨ht.1, lt_of_lt_of_le ht.2 hδle2⟩
  have hδeps : ∀ t ∈ Set.Ioo (0:ℝ) δ, t ∈ Set.Ioo (0:ℝ) ε := fun t ht =>
    ⟨ht.1, lt_of_lt_of_le ht.2 hδle_eps⟩
  -- The auxiliary function F = f'^{b-1}, its derivative G and H
  set F : ℝ → ℝ := fun s => (deriv f s) ^ (b - 1) with hF_def
  set G : ℝ → ℝ := fun s => (b - 1) * (deriv f s) ^ (b - 2) * deriv (deriv f) s with hG_def
  set H : ℝ → ℝ := fun s => (b - 1) * (b - 2) * (deriv f s) ^ (b - 3) * (deriv (deriv f) s) ^ (2:ℕ)
      + (b - 1) * (deriv f s) ^ (b - 2) * deriv (deriv (deriv f)) s with hH_def
  have hF_deriv : ∀ s ∈ Set.Ioo (0:ℝ) δ, HasDerivAt F (G s) s := by
    intro s hs
    have h := hasDerivAt_deriv_rpow (f := f) (r := b - 1) (hf2 s (hδeps s hs)) (hδf1 s hs)
    have h' : (b - 1) * (deriv f s) ^ (b - 1 - 1) * deriv (deriv f) s = G s := by
      rw [show b - 1 - 1 = b - 2 by ring]
    rw [h'] at h
    simpa [F] using h
  have hG_deriv : ∀ s ∈ Set.Ioo (0:ℝ) δ, HasDerivAt G (H s) s := by
    intro s hs
    have hsε : s ∈ Set.Ioo (0:ℝ) ε := hδeps s hs
    have hpos : 0 < deriv f s := hδf1 s hs
    have hpow2 : HasDerivAt (fun u => (deriv f u) ^ (b - 2))
        ((b - 2) * (deriv f s) ^ (b - 2 - 1) * deriv (deriv f) s) s :=
      hasDerivAt_deriv_rpow (f := f) (r := b - 2) (hf2 s hsε) hpos
    have hmul : HasDerivAt (fun u => (deriv f u) ^ (b - 2) * deriv (deriv f) u)
        (((b - 2) * (deriv f s) ^ (b - 2 - 1) * deriv (deriv f) s) * deriv (deriv f) s
          + (deriv f s) ^ (b - 2) * deriv (deriv (deriv f)) s) s :=
      hpow2.mul (hf3 s hsε)
    have hG_eq : G = fun u => (b - 1) * ((deriv f u) ^ (b - 2) * deriv (deriv f) u) := by
      funext u; simp only [G]; ring
    rw [hG_eq]
    have hres := hmul.const_mul (b - 1)
    have hval : (b - 1) * (((b - 2) * (deriv f s) ^ (b - 2 - 1) * deriv (deriv f) s)
          * deriv (deriv f) s + (deriv f s) ^ (b - 2) * deriv (deriv (deriv f)) s) = H s := by
      rw [show b - 2 - 1 = b - 3 by ring]
      simp only [H]
      ring
    rw [hval] at hres
    exact hres
  have hFpos : ∀ s ∈ Set.Ioo (0:ℝ) δ, 0 < F s := by
    intro s hs; simp only [F]; exact Real.rpow_pos_of_pos (hδf1 s hs) (b - 1)
  have hGnonneg : ∀ s ∈ Set.Ioo (0:ℝ) δ, 0 ≤ G s := by
    intro s hs
    simp only [G]
    have h1 : 0 < (deriv f s) ^ (b - 2) := Real.rpow_pos_of_pos (hδf1 s hs) (b - 2)
    have h2 : 0 < deriv (deriv f) s := hf2pos s (hδeps s hs)
    positivity
  -- Constants for the bound
  set pt : ℝ := (2 * b - 3) / (b - 2) with hpt_def
  have hptpos : 0 < pt := by rw [hpt_def]; exact div_pos (by linarith) hb2
  set c1 : ℝ := (b - 2) / (b - 1) with hc1_def
  have hc1pos : 0 < c1 := by rw [hc1_def]; positivity
  set c2 : ℝ := e * (b - 1) ^ (1 - pt) with hc2_def
  have hc2pos : 0 < c2 := by
    rw [hc2_def]; exact mul_pos he (Real.rpow_pos_of_pos hb1 _)
  set Acomp : ℝ → ℝ := fun x => (2 / Lam) * (c1 * x^2 + c2 * |x| ^ pt) + 1 with hAcomp_def
  have hAcont : Continuous Acomp := by
    rw [hAcomp_def]
    refine (continuous_const.mul ?_).add continuous_const
    exact (continuous_const.mul (continuous_id.pow 2)).add
      (continuous_const.mul (continuous_abs.rpow_const (fun x => Or.inr (le_of_lt hptpos))))
  have hp2 : (b - 2) * pt = 2 * b - 3 := by
    rw [hpt_def, mul_comm, div_mul_cancel₀ _ (ne_of_gt hb2)]
  -- The bound on `deriv G = H` in terms of `G`
  have hHbound : ∀ s ∈ Set.Ioo (0:ℝ) δ, |H s| < Acomp (G s) / s := by
    intro s hs
    have hsε : s ∈ Set.Ioo (0:ℝ) ε := hδeps s hs
    have ha : 0 < deriv f s := hδf1 s hs
    have hB : 0 < deriv (deriv f) s := hf2pos s hsε
    have hFspos : 0 < F s := hFpos s hs
    have hGs : 0 ≤ G s := hGnonneg s hs
    have ha2b3 : 0 ≤ (deriv f s) ^ (2 * b - 3) := Real.rpow_nonneg (le_of_lt ha) _
    have hBpt : 0 ≤ (deriv (deriv f) s) ^ pt := Real.rpow_nonneg (le_of_lt hB) _
    have hGpt : (G s) ^ pt = (b - 1) ^ pt * (deriv f s) ^ (2 * b - 3) * (deriv (deriv f) s) ^ pt := by
      simp only [G]
      rw [Real.mul_rpow (by positivity) (le_of_lt hB),
          Real.mul_rpow (le_of_lt hb1) (Real.rpow_nonneg (le_of_lt ha) _),
          ← Real.rpow_mul (le_of_lt ha) (b - 2) pt, hp2]
    have hG2 : (G s)^2 = (b - 1)^2 * (deriv f s)^(2*b-4) * (deriv (deriv f) s)^2 := by
      have hA2 : ((deriv f s)^(b - 2)) ^ (2:ℕ) = (deriv f s)^(2*b-4) := by
        rw [show ((deriv f s)^(b - 2)) ^ (2:ℕ) = ((deriv f s)^(b - 2)) ^ (2:ℝ) from
          (Real.rpow_natCast _ 2).symm]
        rw [← Real.rpow_mul (le_of_lt ha) (b - 2) (2:ℝ)]
        congr 1; ring
      have h1 : (G s)^2 = ((b - 1) * (deriv f s)^(b - 2)*deriv (deriv f) s)^2 := by simp only [G]
      rw [h1]
      have h2 : ((b - 1) * (deriv f s)^(b - 2) * deriv (deriv f) s)^2
          = (b - 1)^2 * ((deriv f s)^(b - 2))^2 * (deriv (deriv f) s)^2 := by ring
      rw [h2, hA2]
    have hA1 : (deriv f s)^(b - 1) * (deriv f s)^(b - 3) = (deriv f s)^(2*b-4) := by
      rw [← Real.rpow_add ha (b - 1) (b - 3)]; congr 1; ring
    have hA1' : (deriv f s)^(b - 1) * (deriv f s)^(b - 2) = (deriv f s)^(2*b-3) := by
      rw [← Real.rpow_add ha (b - 1) (b - 2)]; congr 1; ring
    have hdecomp : F s * H s = c1 * (G s)^2
        + (b - 1) * (deriv f s)^(2*b-3) * deriv (deriv (deriv f)) s := by
      have hexp : F s * H s
          = (b-1)*(b-2)*((deriv f s)^(b-1)*(deriv f s)^(b-3))*(deriv (deriv f) s)^2
            + (b-1)*((deriv f s)^(b-1)*(deriv f s)^(b-2))*deriv (deriv (deriv f)) s := by
        simp only [F, H]; ring
      rw [hexp, hA1, hA1', hG2]
      simp only [c1]
      field_simp
    have hterm2 : |(b - 1) * (deriv f s)^(2*b-3) * deriv (deriv (deriv f)) s| ≤ c2 * (G s)^pt := by
      have hthird' : |deriv (deriv (deriv f)) s| ≤ e * (deriv (deriv f) s) ^ pt := by
        have h := hthird s hsε
        rwa [hpt_def] at h
      have epos : (0:ℝ) ≤ e := le_of_lt he
      calc |(b - 1) * (deriv f s)^(2*b-3) * deriv (deriv (deriv f)) s|
          = (b - 1) * (deriv f s)^(2*b-3) * |deriv (deriv (deriv f)) s| := by
            rw [abs_mul, abs_mul, abs_of_pos hb1, abs_of_nonneg ha2b3]
        _ ≤ (b - 1) * (deriv f s)^(2*b-3) * (e * (deriv (deriv f) s)^pt) := by
            apply mul_le_mul_of_nonneg_left hthird'
            positivity
        _ = c2 * (G s)^pt := by
            rw [hGpt, hc2_def]
            rw [show e * (b-1)^(1-pt) * ((b-1)^pt * (deriv f s)^(2*b-3) * (deriv (deriv f) s)^pt)
                = e * ((b-1)^(1-pt) * (b-1)^pt) * (deriv f s)^(2*b-3) * (deriv (deriv f) s)^pt
                by ring]
            rw [← Real.rpow_add hb1 (1-pt) pt, show 1-pt+pt = 1 by ring, Real.rpow_one]
            ring_nf
    have hFHbound : |F s * H s| ≤ c1 * (G s)^2 + c2 * (G s)^pt := by
      have h1 : |c1 * (G s)^2| = c1 * (G s)^2 :=
        abs_of_nonneg (by positivity)
      calc |F s * H s| = |c1 * (G s)^2 + (b-1)*(deriv f s)^(2*b-3)*deriv (deriv (deriv f)) s| := by
            rw [hdecomp]
        _ ≤ |c1 * (G s)^2| + |(b-1)*(deriv f s)^(2*b-3)*deriv (deriv (deriv f)) s| := abs_add_le _ _
        _ ≤ c1 * (G s)^2 + c2 * (G s)^pt := by rw [h1]; linarith [hterm2]
    have h1F : 1 / F s ≤ 2 / (Lam * s) := by
      rw [div_le_div_iff₀ hFspos (mul_pos hLampos hs.1)]
      have hthis := hδFt s hs
      simp only [F]
      nlinarith [hthis, hLampos]
    have hstep1 : |H s| ≤ (c1 * (G s)^2 + c2 * (G s)^pt) * (2 / (Lam * s)) := by
      rw [show |H s| = |F s * H s| / F s by
        rw [abs_mul, abs_of_pos hFspos, mul_div_cancel_left₀ _ (ne_of_gt hFspos)]]
      calc |F s * H s| / F s = |F s * H s| * (1 / F s) := by rw [div_eq_mul_inv]; ring
        _ ≤ |F s * H s| * (2 / (Lam * s)) := mul_le_mul_of_nonneg_left h1F (abs_nonneg _)
        _ ≤ (c1 * (G s)^2 + c2 * (G s)^pt) * (2 / (Lam * s)) :=
            mul_le_mul_of_nonneg_right hFHbound (div_nonneg (by norm_num) (le_of_lt (mul_pos hLampos hs.1)))
    have hAcompG : Acomp (G s) = (2 / Lam) * (c1 * (G s)^2 + c2 * (G s)^pt) + 1 := by
      rw [hAcomp_def]; simp only []; rw [abs_of_nonneg hGs]
    have hstep2 : (c1 * (G s)^2 + c2 * (G s)^pt) * (2 / (Lam * s))
        = (2 / Lam) * (c1 * (G s)^2 + c2 * (G s)^pt) / s := by ring_nf
    have hstep3 : (2 / Lam) * (c1 * (G s)^2 + c2 * (G s)^pt) / s < Acomp (G s) / s := by
      rw [hAcompG]
      apply div_lt_div_of_pos_right _ hs.1
      linarith
    linarith [hstep1, hstep2, hstep3]
  -- The continuous extension of F at 0
  set Fext : ℝ → ℝ := fun s => if s ≤ 0 then 0 else F s with hFext_def
  have hFext_zero : Fext 0 = 0 := by simp only [Fext]; rw [if_pos le_rfl]
  have hFlim0 : Tendsto F (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h := (tendsto_id.mono_left nhdsWithin_le_nhds).mul hFlimit
    rw [zero_mul] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    change t * (deriv f t ^ (b - 1) / t) = deriv f t ^ (b - 1)
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ (ne_of_gt ht)]
  have hFext_tendsto : Tendsto Fext (nhds (0:ℝ)) (nhds 0) := by
    have hdecomp : nhds (0:ℝ) = nhdsWithin (0:ℝ) (Set.Ioi 0) ⊔ nhdsWithin (0:ℝ) (Set.Iic 0) := by
      have hunion : Set.Ioi (0:ℝ) ∪ Set.Iic 0 = Set.univ := by
        ext x; simp only [Set.mem_union, Set.mem_Ioi, Set.mem_Iic, Set.mem_univ]
        exact ⟨fun _ => trivial, fun _ => by
          rcases lt_trichotomy x 0 with h | h | h
          · exact Or.inr (le_of_lt h)
          · exact Or.inr (le_of_eq h)
          · exact Or.inl h⟩
      rw [← nhdsWithin_univ (a := (0:ℝ)), ← hunion, nhdsWithin_union]
    have h1 : Tendsto Fext (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
      have heq : Fext =ᶠ[nhdsWithin (0:ℝ) (Set.Ioi 0)] F := by
        filter_upwards [self_mem_nhdsWithin] with x hx
        simp only [Fext]; rw [if_neg (not_le.mpr hx)]
      exact hFlim0.congr' heq.symm
    have h2 : Tendsto Fext (nhdsWithin (0:ℝ) (Set.Iic 0)) (nhds 0) := by
      have heq : Fext =ᶠ[nhdsWithin (0:ℝ) (Set.Iic 0)] (fun _ => (0:ℝ)) := by
        filter_upwards [self_mem_nhdsWithin] with x hx
        rw [mem_Iic] at hx
        simp only [Fext]; rw [if_pos hx]
      exact tendsto_const_nhds.congr' heq.symm
    have hsup := tendsto_sup.mpr ⟨h1, h2⟩
    rwa [← hdecomp] at hsup
  have hFext_cont0 : ContinuousAt Fext 0 := by
    show Tendsto Fext (nhds (0:ℝ)) (nhds (Fext 0))
    rw [hFext_zero]; exact hFext_tendsto
  have hFmono : MonotoneOn F (Set.Ioo (0:ℝ) δ) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioo 0 δ) ?_ ?_ ?_
    · intro x hx
      have hx' : x ∈ Set.Ioo (0:ℝ) δ := by simpa only [interior_Ioo] using hx
      exact (hF_deriv x hx').continuousAt.continuousWithinAt
    · intro x hx
      have hx' : x ∈ Set.Ioo (0:ℝ) δ := by simpa only [interior_Ioo] using hx
      exact (hF_deriv x hx').differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Set.Ioo (0:ℝ) δ := by simpa only [interior_Ioo] using hx
      rw [(hF_deriv x hx').deriv]
      exact hGnonneg x hx'
  have hFext_mono : ∀ t ∈ Set.Ioo (0:ℝ) δ, MonotoneOn Fext (Set.Icc 0 t) := by
    intro t ht x hx y hy hxy
    rw [mem_Icc] at hx hy
    rcases eq_or_lt_of_le hx.1 with hx0 | hxpos
    · rw [← hx0, hFext_zero]
      by_cases hy0 : y = 0
      · rw [hy0, hFext_zero]
      · have hypos : 0 < y := lt_of_le_of_ne hy.1 (Ne.symm hy0)
        have hFy : Fext y = F y := by simp only [Fext]; rw [if_neg (not_le.mpr hypos)]
        rw [hFy]
        exact le_of_lt (hFpos y ⟨hypos, lt_of_le_of_lt hy.2 ht.2⟩)
    · have hypos : 0 < y := lt_of_lt_of_le hxpos hxy
      have hxδ : x ∈ Set.Ioo (0:ℝ) δ := ⟨hxpos, lt_of_le_of_lt hx.2 ht.2⟩
      have hyδ : y ∈ Set.Ioo (0:ℝ) δ := ⟨hypos, lt_of_le_of_lt hy.2 ht.2⟩
      have hxF : Fext x = F x := by simp only [Fext]; rw [if_neg (not_le.mpr hxpos)]
      have hyF : Fext y = F y := by simp only [Fext]; rw [if_neg (not_le.mpr hypos)]
      rw [hxF, hyF]
      exact hFmono hxδ hyδ hxy
  have hFext_hasderiv : ∀ x ∈ Set.Ioo (0:ℝ) δ, HasDerivAt Fext (G x) x := by
    intro x hx
    have hfun : Fext =ᶠ[nhds x] F := by
      filter_upwards [isOpen_Ioi.mem_nhds hx.1] with u hu
      simp only [Fext]; rw [if_neg (not_le.mpr hu)]
    exact (hF_deriv x hx).congr_of_eventuallyEq hfun
  have hint0 : ∀ t ∈ Set.Ioo (0:ℝ) δ, IntervalIntegrable G volume 0 t := by
    intro t ht
    have hmono : MonotoneOn Fext (Set.uIcc (0:ℝ) t) := by
      rw [Set.uIcc_of_le (le_of_lt ht.1)]; exact hFext_mono t ht
    have hInt := MonotoneOn.intervalIntegrable_deriv hmono
    refine hInt.congr ?_
    intro x hx
    rw [Set.uIoc_of_le (le_of_lt ht.1)] at hx
    exact (hFext_hasderiv x ⟨hx.1, lt_of_le_of_lt hx.2 ht.2⟩).deriv
  have hFext_cont : ∀ t ∈ Set.Ioo (0:ℝ) δ, ContinuousOn Fext (Set.Icc 0 t) := by
    intro t ht x hx
    rw [mem_Icc] at hx
    rcases eq_or_lt_of_le hx.1 with hx0 | hxpos
    · rw [← hx0]; exact hFext_cont0.continuousWithinAt
    · have hxδ : x ∈ Set.Ioo (0:ℝ) δ := ⟨hxpos, lt_of_le_of_lt hx.2 ht.2⟩
      have hfun : Fext =ᶠ[nhds x] F := by
        filter_upwards [isOpen_Ioi.mem_nhds hxpos] with u hu
        simp only [Fext]; rw [if_neg (not_le.mpr hu)]
      exact (((hF_deriv x hxδ).continuousAt).congr hfun.symm).continuousWithinAt
  have hFTC : ∀ t ∈ Set.Ioo (0:ℝ) δ, ∫ s in (0:ℝ)..t, G s = F t := by
    intro t ht
    have hmono : MonotoneOn Fext (Set.uIcc (0:ℝ) t) := by
      rw [Set.uIcc_of_le (le_of_lt ht.1)]; exact hFext_mono t ht
    have hInt := MonotoneOn.intervalIntegrable_deriv hmono
    have hderiv : ∀ x ∈ Set.Ioo (0:ℝ) t, HasDerivAt Fext (deriv Fext x) x := by
      intro x hx
      have hd := hFext_hasderiv x ⟨hx.1, lt_trans hx.2 ht.2⟩
      rw [hd.deriv]; exact hd
    have hftc := integral_eq_sub_of_hasDerivAt_of_le (le_of_lt ht.1) (hFext_cont t ht) hderiv hInt
    rw [hFext_zero, sub_zero] at hftc
    have hcongr : ∫ s in (0:ℝ)..t, G s = ∫ s in (0:ℝ)..t, deriv Fext s := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards with x hx
      rw [Set.uIoc_of_le (le_of_lt ht.1)] at hx
      exact (hFext_hasderiv x ⟨hx.1, lt_of_le_of_lt hx.2 ht.2⟩).deriv.symm
    rw [hcongr, hftc]
    simp only [Fext]; rw [if_neg (not_le.mpr ht.1)]
  have havg : Tendsto (fun t : ℝ => t⁻¹ * ∫ s in (0:ℝ)..t, G s)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds Lam) := by
    have heq : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0),
        (deriv f t)^(b-1) / t = t⁻¹ * ∫ s in (0:ℝ)..t, G s := by
      filter_upwards [Ioo_mem_nhdsGT hδpos] with t ht
      rw [hFTC t ht]
      simp only [F]
      rw [div_eq_mul_inv, mul_comm]
    exact hFlimit.congr' heq
  have hint : ∀ l u : ℝ, 0 < l → l ≤ u → u < δ → IntervalIntegrable (deriv G) volume l u := by
    intro l u hl hlu hu
    have hsub : Set.Icc l u ⊆ Set.Ioo (0:ℝ) ε := fun x hx =>
      ⟨lt_of_lt_of_le hl hx.1, lt_of_le_of_lt hx.2 (lt_of_lt_of_le hu hδle_eps)⟩
    have hdiff : DifferentiableOn ℝ (deriv f) (Set.Icc l u) := fun x hx =>
      (hf2 x (hsub hx)).differentiableAt.differentiableWithinAt
    have hcont1 : ContinuousOn (deriv f) (Set.Icc l u) := hdiff.continuousOn
    have hdiff2 : DifferentiableOn ℝ (deriv (deriv f)) (Set.Icc l u) := fun x hx =>
      (hf3 x (hsub hx)).differentiableAt.differentiableWithinAt
    have hcont2 : ContinuousOn (deriv (deriv f)) (Set.Icc l u) := hdiff2.continuousOn
    have hGcont : ContinuousOn G (Set.Icc l u) := by
      have h2 : ContinuousOn (fun x => (deriv f x) ^ (b - 2)) (Set.Icc l u) :=
        hcont1.rpow_const (fun x hx => Or.inr (le_of_lt hb2))
      have h3 : ContinuousOn
          (fun x => (b - 1) * (deriv f x) ^ (b - 2) * deriv (deriv f) x) (Set.Icc l u) :=
        (continuousOn_const.mul h2).mul hcont2
      simpa only [G] using h3
    obtain ⟨MG, hMG⟩ := isCompact_Icc.exists_bound_of_continuousOn hGcont
    set M : ℝ := max MG 0 + 1 with hM_def
    have hMpos : 0 < M := by rw [hM_def]; positivity
    set CA : ℝ := (2 / Lam) * (c1 * M ^ 2 + c2 * M ^ pt) + 1 with hCA_def
    have hCAnn : 0 ≤ CA := by
      rw [hCA_def]
      have h : 0 ≤ (2 / Lam) * (c1 * M ^ 2 + c2 * M ^ pt) := by positivity
      linarith
    have hAMpos : 0 < 2 / Lam := by positivity
    have hHle : ∀ x ∈ Set.uIoc l u, ‖deriv G x‖ < CA / l := by
      intro x hx
      rw [Set.uIoc_of_le hlu] at hx
      have hxδ : x ∈ Set.Ioo (0:ℝ) δ := ⟨lt_trans hl hx.1, lt_of_le_of_lt hx.2 hu⟩
      have hxpos : 0 < x := lt_trans hl hx.1
      have hdx : deriv G x = H x := (hG_deriv x hxδ).deriv
      have hbnd := hHbound x hxδ
      rw [hdx, Real.norm_eq_abs]
      have hMGx : |G x| ≤ M := by
        have h1 := hMG x ⟨le_of_lt hx.1, hx.2⟩
        rw [Real.norm_eq_abs] at h1
        rw [hM_def]
        exact le_trans h1 (le_trans (le_max_left MG 0) (le_add_of_nonneg_right zero_le_one))
      have hAcomp_le : Acomp (G x) ≤ CA := by
        rw [hAcomp_def, hCA_def]
        have h1 : (G x) ^ 2 ≤ M ^ 2 := by
          have habs := abs_le.mp hMGx
          exact sq_le_sq' habs.1 habs.2
        have h2 : |G x| ^ pt ≤ M ^ pt := Real.rpow_le_rpow (abs_nonneg _) hMGx (le_of_lt hptpos)
        have h3 : c1 * (G x) ^ 2 + c2 * |G x| ^ pt ≤ c1 * M ^ 2 + c2 * M ^ pt := by
          have h3a := mul_le_mul_of_nonneg_left h1 (le_of_lt hc1pos)
          have h3b := mul_le_mul_of_nonneg_left h2 (le_of_lt hc2pos)
          linarith
        have h4 : (0:ℝ) ≤ 2 / Lam := le_of_lt hAMpos
        linarith [mul_le_mul_of_nonneg_left h3 h4]
      calc |H x| < Acomp (G x) / x := hbnd
        _ ≤ CA / x := div_le_div_of_nonneg_right hAcomp_le (le_of_lt hxpos)
        _ ≤ CA / l := div_le_div_of_nonneg_left hCAnn hl (le_of_lt hx.1)
    refine intervalIntegrable_iff.mpr ?_
    refine IntegrableOn.of_bound (by rw [Set.uIoc_of_le hlu]; exact measure_Ioc_lt_top) ?_ (CA / l) ?_
    · exact (measurable_deriv G).aestronglyMeasurable
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
      exact Filter.Eventually.of_forall (fun x hx => le_of_lt (hHle x hx))
  have hderivG : ∀ t ∈ Set.Ioo (0:ℝ) δ, HasDerivAt G (deriv G t) t := by
    intro t ht
    have hd := hG_deriv t ht
    rw [hd.deriv]; exact hd
  have hHbound' : ∀ t ∈ Set.Ioo (0:ℝ) δ, |deriv G t| < Acomp (G t) / t := by
    intro t ht
    rw [(hG_deriv t ht).deriv]
    exact hHbound t ht
  have hGlim : Tendsto G (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds Lam) :=
    tendsto_of_tendsto_average_of_deriv_bound hδpos hderivG hint hint0 havg ⟨Acomp, hAcont, hHbound'⟩
  -- Convert the limit of `G` into the limit of `f'' f^((b-2)/b)`
  have hDt : Tendsto (fun t : ℝ => (deriv f t / (f t) ^ (1 / b)) ^ (b - 2))
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (η ^ ((b - 2) / 2))) := by
    have h := hratio.rpow_const (p := b - 2) (Or.inl (ne_of_gt (Real.sqrt_pos_of_pos hη)))
    have hval : (Real.sqrt η) ^ (b - 2) = η ^ ((b - 2) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hη) (1/2) (b-2)]
      congr 1; ring
    rwa [hval] at h
  have hden : Tendsto (fun t : ℝ => (b - 1) * (deriv f t / (f t) ^ (1 / b)) ^ (b - 2))
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds ((b - 1) * η ^ ((b - 2) / 2))) :=
    hDt.const_mul (b - 1)
  have hden_ne : (b - 1) * η ^ ((b - 2) / 2) ≠ 0 :=
    mul_ne_zero (ne_of_gt hb1) (ne_of_gt (Real.rpow_pos_of_pos hη _))
  have hquot := hGlim.div hden hden_ne
  have hquotval : Lam / ((b - 1) * η ^ ((b - 2) / 2)) = η / b := by
    rw [hLam_def]
    have hsplit : η ^ (b / 2) = η ^ ((b - 2) / 2) * η := by
      rw [show b / 2 = (b - 2) / 2 + 1 by ring, Real.rpow_add hη, Real.rpow_one]
    rw [hsplit]
    field_simp
  rw [hquotval] at hquot
  have key : ∀ t ∈ Set.Ioo (0:ℝ) δ,
      G t / ((b - 1) * (deriv f t / (f t) ^ (1 / b)) ^ (b - 2))
        = deriv (deriv f) t * (f t) ^ ((b - 2) / b) := by
    intro t ht
    have hft : 0 < f t := hfpos t ⟨ht.1, lt_of_lt_of_le ht.2 hδle_eps⟩
    have hf1 : 0 < deriv f t := hδf1 t ht
    have hftb : 0 < (f t) ^ (1 / b) := Real.rpow_pos_of_pos hft (1 / b)
    have hGval : G t = (b - 1) * (deriv f t) ^ (b - 2) * deriv (deriv f) t := by simp only [G]
    have hBs : ((f t) ^ (1 / b)) ^ (b - 2) = (f t) ^ ((b - 2) / b) := by
      rw [← Real.rpow_mul (le_of_lt hft) (1 / b) (b - 2)]
      congr 1; ring
    have hdiv : (deriv f t / (f t) ^ (1 / b)) ^ (b - 2)
        = (deriv f t) ^ (b - 2) / (f t) ^ ((b - 2) / b) := by
      rw [Real.div_rpow (le_of_lt hf1) (le_of_lt hftb) (b - 2), hBs]
    rw [hGval, hdiv]
    field_simp [ne_of_gt hb1, ne_of_gt (Real.rpow_pos_of_pos hf1 (b - 2)),
      ne_of_gt (Real.rpow_pos_of_pos hft ((b - 2) / b))]
  refine hquot.congr' ?_
  exact (Filter.eventually_iff_exists_mem.mpr ⟨Set.Ioo (0:ℝ) δ, Ioo_mem_nhdsGT hδpos,
    fun t ht => key t ht⟩)


end Commons.Analysis.Calculus