import Mathlib
import Submission.Work.FIArea2.SmoothSec6Defs
import Submission.Work.FIArea2.lemma_7_1
import Submission.Work.FIArea2.G8Defs

namespace Work.FIArea2

/-! ## Elementary summability facts for the §9 frequency tail

The `h ≠ 0` tail of (6.9) is compared with the absolutely convergent weight series of (9.2),
so the first thing needed is that `∑_{t ∈ ℤ} (1 + c t²)⁻¹` converges for every `c > 0`. -/

lemma base_summable_inv_one_add_sq : Summable (fun t : ℤ => (1 + (t:ℝ)^2)⁻¹) := by
  apply Summable.of_nonneg_of_le (f := fun t : ℤ => 2 * ((t:ℝ)^2)⁻¹ + (if t = 0 then (1:ℝ) else 0))
  · intro t; positivity
  · intro t
    by_cases h : t = 0
    · simp [h]
    · rw [if_neg h]
      have h1 : (1 + (t:ℝ)^2)⁻¹ ≤ 2 * ((t:ℝ)^2)⁻¹ := by
        rw [show (2:ℝ) * ((t:ℝ)^2)⁻¹ = ((t:ℝ)^2/2)⁻¹ by field_simp]
        rw [inv_le_inv₀ (by positivity) (by positivity)]
        linarith [sq_nonneg (t:ℝ)]
      linarith [h1]
  · apply Summable.add
    · have h1 : Summable (fun n : ℤ => 1 / (n:ℝ)^2) := Real.summable_one_div_int_pow.mpr (by norm_num)
      have h2 : Summable (fun n : ℤ => ((n:ℝ)^2)⁻¹) := by simpa [one_div] using h1
      exact h2.mul_left 2
    · apply summable_of_ne_finset_zero (s := {0})
      intro b hb
      simp only [Finset.mem_singleton] at hb
      simp [hb]

/-- `∑_{t ∈ ℤ} (1 + c t²)⁻¹` converges for every `c > 0`, with the comparison
`(1 + c t²)⁻¹ ≤ max(1, c⁻¹)(1 + t²)⁻¹`. -/
lemma summable_inv_one_add_mul_sq (c : ℝ) (hc : 0 < c) :
    Summable (fun t : ℤ => (1 + c * (t:ℝ)^2)⁻¹) := by
  have hbase := base_summable_inv_one_add_sq
  have hkey : ∀ t : ℤ, (1 + c * (t:ℝ)^2)⁻¹ ≤ max 1 c⁻¹ * (1 + (t:ℝ)^2)⁻¹ := by
    intro t
    set m : ℝ := max 1 c⁻¹ with hm
    have hmpos : 0 < m := by rw [hm]; positivity
    have h1 : (1 + (t:ℝ)^2) ≤ m * (1 + c * (t:ℝ)^2) := by
      rcases le_total 1 c with hc1 | hc1
      · have hle : c⁻¹ ≤ (1:ℝ) := by rw [inv_le_one₀ hc]; exact hc1
        have hm1 : m = 1 := by rw [hm]; exact max_eq_left hle
        rw [hm1, one_mul]; nlinarith
      · have hge : (1:ℝ) ≤ c⁻¹ := by rw [one_le_inv₀ hc]; exact hc1
        have hm1 : m = c⁻¹ := by rw [hm]; exact max_eq_right hge
        rw [hm1]
        have hcalc : c⁻¹ * (1 + c * (t:ℝ)^2) = c⁻¹ + (t:ℝ)^2 := by field_simp
        linarith
    have hpos : 0 < 1 + c * (t:ℝ)^2 := by nlinarith
    have hpos2 : 0 < 1 + (t:ℝ)^2 := by nlinarith
    have hA : 0 < m * (1 + c * (t:ℝ)^2) := by positivity
    have step : (m * (1 + c * (t:ℝ)^2))⁻¹ ≤ (1 + (t:ℝ)^2)⁻¹ :=
      (inv_le_inv₀ hA hpos2).mpr h1
    rw [mul_inv] at step
    calc (1 + c * (t:ℝ)^2)⁻¹ = m * (m⁻¹ * (1 + c * (t:ℝ)^2)⁻¹) := by field_simp
      _ ≤ m * (1 + (t:ℝ)^2)⁻¹ := mul_le_mul_of_nonneg_left step hmpos.le
  exact Summable.of_nonneg_of_le (fun t => by positivity) hkey (hbase.mul_left _)

/-! ## Arithmetic and geometric side conditions

`Δ ≠ 0` forces `z₁ ≠ 0 ≠ z₂`, so `|Δ| > 0` and both `|z_j| > 0`; the `(Λ,Δ)` of (9.5) divides
`|Δ|`, whence `(Λ,Δ) ≤ |Δ|`. -/

lemma gcdDelta_cast_le_absDelta (z1 z2 : GaussianInt) (hΔ : Work.FIPlan.Delta z1 z2 ≠ 0)
    (h1 h2 : ℤ) :
    (gcdDelta z1 z2 h1 h2 : ℝ) ≤ ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by
  have hpos : 0 < Work.FIPlan.absDelta z1 z2 := by
    rw [Work.FIPlan.absDelta, Int.natAbs_pos]; exact hΔ
  rw [gcdDelta]
  exact_mod_cast Nat.gcd_le_right _ hpos

lemma absDelta_pos (z1 z2 : GaussianInt) (hΔ : Work.FIPlan.Delta z1 z2 ≠ 0) :
    0 < Work.FIPlan.absDelta z1 z2 := by
  rw [Work.FIPlan.absDelta, Int.natAbs_pos]; exact hΔ

lemma gnorm_pos_of_ne_zero (z : GaussianInt) (hz : z ≠ 0) : 0 < Work.FIPlan.gnorm z := by
  rw [Work.FIPlan.gnorm, Int.natAbs_pos]
  exact fun h => hz ((Zsqrtd.norm_eq_zero (d := -1) (by intro n; nlinarith [sq_nonneg n]) z).mp h)

lemma delta_eq_zero_of_fst_eq_zero (z1 z2 : GaussianInt) (h : z1 = 0) :
    Work.FIPlan.Delta z1 z2 = 0 := by
  simp [Work.FIPlan.Delta, h]

lemma delta_eq_zero_of_snd_eq_zero (z1 z2 : GaussianInt) (h : z2 = 0) :
    Work.FIPlan.Delta z1 z2 = 0 := by
  rw [Work.FIPlan.Delta, h]; simp

/-! ## The weights of (9.2) as `(1 + c h²)⁻¹`

`u_j = h_j/√(|Δ||z_j|)`, so `u_j²δ√M = c_j h_j²` with `c_j = δ√M/(|Δ||z_j|)`; the weight
`(1 + u_j²δ√M)⁻¹` of Lemma 7.1 is therefore `(1 + c_j h_j²)⁻¹`, to which the summability
lemma above applies. -/

lemma secFreq₁_weight_eq (z1 z2 : GaussianInt) (h : ℤ) (δ S : ℝ)
    (hA : 0 < ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ))
    (hG : 0 < ((Work.FIPlan.gnorm z2 : ℕ) : ℝ)) :
    (1 + secFreq₁ z1 z2 h ^ 2 * δ * S)⁻¹
      = (1 + (δ * S / (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
            * Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ) : ℝ)))) * (h : ℝ) ^ 2)⁻¹ := by
  have hspos : 0 < Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ) : ℝ)) := Real.sqrt_pos.mpr hG
  have hAG : (0:ℝ) < ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
      * Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ) : ℝ)) := mul_pos hA hspos
  have hsq : secFreq₁ z1 z2 h ^ 2
      = (h:ℝ)^2 / (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
          * Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ) : ℝ))) := by
    rw [secFreq₁, div_pow, Real.sq_sqrt hAG.le]
  rw [hsq]
  congr 1
  field_simp

lemma secFreq₂_weight_eq (z1 z2 : GaussianInt) (h : ℤ) (δ S : ℝ)
    (hA : 0 < ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ))
    (hG : 0 < ((Work.FIPlan.gnorm z1 : ℕ) : ℝ)) :
    (1 + secFreq₂ z1 z2 h ^ 2 * δ * S)⁻¹
      = (1 + (δ * S / (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
            * Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ)))) * (h : ℝ) ^ 2)⁻¹ := by
  have hspos : 0 < Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ)) := Real.sqrt_pos.mpr hG
  have hAG : (0:ℝ) < ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
      * Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ)) := mul_pos hA hspos
  have hsq : secFreq₂ z1 z2 h ^ 2
      = (h:ℝ)^2 / (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
          * Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ))) := by
    rw [secFreq₂, div_pow, Real.sq_sqrt hAG.le]
  rw [hsq]
  congr 1
  field_simp

/-! ## A termwise bound by a summable family gives a `tsum` bound -/

lemma norm_tsum_pair_le (K : ℝ) (g : ℤ × ℤ → ℝ) (T : ℤ × ℤ → ℂ)
    (hg : Summable g) (hT : ∀ p, ‖T p‖ ≤ K * g p) :
    ‖∑' p, T p‖ ≤ K * ∑' p, g p := by
  have hKg : Summable (fun p : ℤ × ℤ => K * g p) := hg.mul_left K
  have hn : Summable (fun p : ℤ × ℤ => ‖T p‖) :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => hT p) hKg
  calc ‖∑' p, T p‖ ≤ ∑' p, ‖T p‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' p, K * g p := Summable.tsum_le_tsum (fun p => hT p) hn hKg
    _ = K * ∑' p, g p := tsum_mul_left

/-- **The `h != 0` tail of (6.9) is `O(tau^3 |Delta|^{-1} H(z1,z2) sqrt M log N)`** -- the analytic
content of FI (9.1), isolated from the Poisson summation (6.9) that produces it.

`lemma_7_1` bounds the Fourier integral `Fint` by
`10^6 (1+u1^2 delta sqrt M)^{-1} (1+u2^2 delta sqrt M)^{-1} sqrt M log(2+delta^{-2})`,
`delta = sqrt(1-gamma^2)`, and the hypothesis `hG` below is `Gsum_bound`, i.e. Lemma 8.1's (8.5),
`|G(h1,h2)| <= 4 tau(|Delta|)^3 (Lambda,Delta)/|Delta|` with `(Lambda,Delta) = gcdDelta`.  Multiplying
the two term-by-term and summing over `h != 0` gives the displayed bound; the sum on the right is
the paper's `H(z1,z2)` of (9.2).  It is the bound that, together with `Ccount_smooth_eq_poisson`
and the `h = 0` term `|z1 z2|^{-1/2} F(0,0) G_0` (i.e. (6.13)), yields (9.1). -/
theorem sec9_frequency_sum_bound (Pa : Work.FITop.Params) (F : ℝ → ℝ) (z1 z2 : GaussianInt)
    (hF : ContDiff ℝ 4 F)
    (hfsupp : ∀ u : ℝ, F u ≠ 0 → Pa.M / 4 ≤ u ∧ u ≤ 4 * Pa.M)
    (hfd : ∀ j : ℕ, j ≤ 4 → ∀ u : ℝ, |iteratedDeriv j F u| ≤ Pa.M ^ (-(j : ℝ)))
    (hM : 1 ≤ Pa.M)
    (hγ0 : 0 ≤ Work.FIArea2.gamOf z1 z2) (hγ1 : Work.FIArea2.gamOf z1 z2 < 1)
    (hΔ : Work.FIPlan.Delta z1 z2 ≠ 0)
    (hG : ∀ h1 h2 : ℤ, ‖Work.FIArea2.Gsum z1 z2 h1 h2‖
        ≤ 4 * (((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) ^ 3)
            * (Work.FIArea2.gcdDelta z1 z2 h1 h2 : ℝ) / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)) :
    ‖∑' h : ℤ × ℤ, (if h = (0, 0) then 0 else
        Work.FIArea2.Fint F (Work.FIArea2.gamOf z1 z2)
          (-(Work.FIArea2.secFreq₁ z1 z2 h.1)) (-(Work.FIArea2.secFreq₂ z1 z2 h.2))
        * Work.FIArea2.Gsum z1 z2 h.1 h.2)‖
      ≤ 4 * 10 ^ 6 * (((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) ^ 3)
          / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) * Real.sqrt Pa.M
          * Real.log (2 + 1 / (1 - (Work.FIArea2.gamOf z1 z2) ^ 2))
          * ∑' h : ℤ × ℤ, (if h = (0, 0) then 0 else
              (Work.FIArea2.gcdDelta z1 z2 h.1 h.2 : ℝ)
                * (1 + (Work.FIArea2.secFreq₁ z1 z2 h.1) ^ 2
                    * Real.sqrt (1 - (Work.FIArea2.gamOf z1 z2) ^ 2) * Real.sqrt Pa.M)⁻¹
                * (1 + (Work.FIArea2.secFreq₂ z1 z2 h.2) ^ 2
                    * Real.sqrt (1 - (Work.FIArea2.gamOf z1 z2) ^ 2) * Real.sqrt Pa.M)⁻¹) := by
  set γ : ℝ := Work.FIArea2.gamOf z1 z2 with hγdef
  have h1γ : 0 < 1 - γ ^ 2 := by nlinarith [sq_nonneg γ]
  have hδpos : 0 < Real.sqrt (1 - γ ^ 2) := Real.sqrt_pos.mpr h1γ
  have hSpos : 0 < Real.sqrt Pa.M := Real.sqrt_pos.mpr (lt_of_lt_of_le one_pos hM)
  have hApos : 0 < ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by
    exact_mod_cast absDelta_pos z1 z2 hΔ
  have hz1 : z1 ≠ 0 := fun h => hΔ (delta_eq_zero_of_fst_eq_zero z1 z2 h)
  have hz2 : z2 ≠ 0 := fun h => hΔ (delta_eq_zero_of_snd_eq_zero z1 z2 h)
  have hg1pos : (0:ℝ) < ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) := by
    exact_mod_cast gnorm_pos_of_ne_zero z1 hz1
  have hg2pos : (0:ℝ) < ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) := by
    exact_mod_cast gnorm_pos_of_ne_zero z2 hz2
  have hlogpos : 0 < Real.log (2 + 1 / (1 - γ ^ 2)) := by
    apply Real.log_pos
    have h1 : 0 < 1 / (1 - γ ^ 2) := by positivity
    linarith
  have hwnn1 : ∀ t : ℤ, 0 ≤ (1 + secFreq₁ z1 z2 t ^ 2 * Real.sqrt (1 - γ ^ 2)
      * Real.sqrt Pa.M)⁻¹ := by
    intro t
    exact inv_nonneg.mpr (by
      have h1 : 0 ≤ secFreq₁ z1 z2 t ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M :=
        mul_nonneg (mul_nonneg (sq_nonneg _) hδpos.le) hSpos.le
      linarith)
  have hwnn2 : ∀ t : ℤ, 0 ≤ (1 + secFreq₂ z1 z2 t ^ 2 * Real.sqrt (1 - γ ^ 2)
      * Real.sqrt Pa.M)⁻¹ := by
    intro t
    exact inv_nonneg.mpr (by
      have h1 : 0 ≤ secFreq₂ z1 z2 t ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M :=
        mul_nonneg (mul_nonneg (sq_nonneg _) hδpos.le) hSpos.le
      linarith)
  have hsum1 : Summable (fun t : ℤ =>
      (1 + secFreq₁ z1 z2 t ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹) := by
    have hc : 0 < Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M
        / (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
            * Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ) : ℝ))) :=
      div_pos (mul_pos hδpos hSpos) (mul_pos hApos (Real.sqrt_pos.mpr hg2pos))
    refine (summable_inv_one_add_mul_sq _ hc).congr (fun t => ?_)
    exact (secFreq₁_weight_eq z1 z2 t _ _ hApos hg2pos).symm
  have hsum2 : Summable (fun t : ℤ =>
      (1 + secFreq₂ z1 z2 t ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹) := by
    have hc : 0 < Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M
        / (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
            * Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ))) :=
      div_pos (mul_pos hδpos hSpos) (mul_pos hApos (Real.sqrt_pos.mpr hg1pos))
    refine (summable_inv_one_add_mul_sq _ hc).congr (fun t => ?_)
    exact (secFreq₂_weight_eq z1 z2 t _ _ hApos hg1pos).symm
  have hsumprod : Summable (fun p : ℤ × ℤ =>
      (1 + secFreq₁ z1 z2 p.1 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
        * (1 + secFreq₂ z1 z2 p.2 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹) := by
    refine Summable.mul_of_nonneg hsum1 hsum2 ?_ ?_
    · intro t; exact hwnn1 t
    · intro t; exact hwnn2 t
  have hg : Summable (fun p : ℤ × ℤ => (if p = (0, 0) then 0 else
      (gcdDelta z1 z2 p.1 p.2 : ℝ)
        * (1 + secFreq₁ z1 z2 p.1 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
        * (1 + secFreq₂ z1 z2 p.2 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹)) := by
    have hsumMaj : Summable (fun p : ℤ × ℤ => ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) *
        ((1 + secFreq₁ z1 z2 p.1 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
          * (1 + secFreq₂ z1 z2 p.2 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹)) :=
      hsumprod.mul_left _
    refine Summable.of_nonneg_of_le (f := fun p : ℤ × ℤ => ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) *
        ((1 + secFreq₁ z1 z2 p.1 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
          * (1 + secFreq₂ z1 z2 p.2 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹)) ?_ ?_ hsumMaj
    · intro p
      by_cases hp : p = (0, 0)
      · simp [hp]
      · rw [if_neg hp]
        exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hwnn1 p.1)) (hwnn2 p.2)
    · intro p
      by_cases hp : p = (0, 0)
      · rw [if_pos hp]
        exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hwnn1 p.1) (hwnn2 p.2))
      · rw [if_neg hp]
        calc (gcdDelta z1 z2 p.1 p.2 : ℝ)
              * (1 + secFreq₁ z1 z2 p.1 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
              * (1 + secFreq₂ z1 z2 p.2 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
            ≤ ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
              * (1 + secFreq₁ z1 z2 p.1 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
              * (1 + secFreq₂ z1 z2 p.2 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹ := by
              apply mul_le_mul_of_nonneg_right _ (hwnn2 p.2)
              exact mul_le_mul_of_nonneg_right (gcdDelta_cast_le_absDelta z1 z2 hΔ p.1 p.2)
                (hwnn1 p.1)
          _ = ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
              * ((1 + secFreq₁ z1 z2 p.1 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
              * (1 + secFreq₂ z1 z2 p.2 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹) := by
              ring
  have hT : ∀ p : ℤ × ℤ, ‖(if p = (0, 0) then 0 else
      Fint F γ (-(secFreq₁ z1 z2 p.1)) (-(secFreq₂ z1 z2 p.2))
        * Gsum z1 z2 p.1 p.2)‖
      ≤ (4 * 10 ^ 6 * (((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) ^ 3)
          / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) * Real.sqrt Pa.M
          * Real.log (2 + 1 / (1 - γ ^ 2)))
        * (if p = (0, 0) then 0 else
            (gcdDelta z1 z2 p.1 p.2 : ℝ)
              * (1 + secFreq₁ z1 z2 p.1 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
              * (1 + secFreq₂ z1 z2 p.2 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹) := by
    intro p
    by_cases hp : p = (0, 0)
    · simp [hp]
    · rw [if_neg hp, if_neg hp]
      have hsq1 : (-(secFreq₁ z1 z2 p.1)) ^ 2 = (secFreq₁ z1 z2 p.1) ^ 2 := by ring
      have hsq2 : (-(secFreq₂ z1 z2 p.2)) ^ 2 = (secFreq₂ z1 z2 p.2) ^ 2 := by ring
      have hf := lemma_7_1 Pa.M hM F γ hγ0 hγ1 hF hfsupp hfd
        (-(secFreq₁ z1 z2 p.1)) (-(secFreq₂ z1 z2 p.2))
      rw [hsq1, hsq2] at hf
      have hgg := hG p.1 p.2
      have hbpos : 0 ≤ 10 ^ 6
          * (1 + secFreq₁ z1 z2 p.1 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
          * (1 + secFreq₂ z1 z2 p.2 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
          * Real.sqrt Pa.M * Real.log (2 + 1 / (1 - γ ^ 2)) :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hwnn1 p.1))
          (hwnn2 p.2)) hSpos.le) hlogpos.le
      calc ‖Fint F γ (-(secFreq₁ z1 z2 p.1)) (-(secFreq₂ z1 z2 p.2))
              * Gsum z1 z2 p.1 p.2‖
          = ‖Fint F γ (-(secFreq₁ z1 z2 p.1)) (-(secFreq₂ z1 z2 p.2))‖
              * ‖Gsum z1 z2 p.1 p.2‖ := norm_mul _ _
        _ ≤ (10 ^ 6
              * (1 + secFreq₁ z1 z2 p.1 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
              * (1 + secFreq₂ z1 z2 p.2 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
              * Real.sqrt Pa.M * Real.log (2 + 1 / (1 - γ ^ 2)))
            * (4 * (((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) ^ 3)
                * (gcdDelta z1 z2 p.1 p.2 : ℝ) / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)) :=
            mul_le_mul hf hgg (norm_nonneg _) hbpos
        _ = (4 * 10 ^ 6 * (((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) ^ 3)
              / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) * Real.sqrt Pa.M
              * Real.log (2 + 1 / (1 - γ ^ 2)))
            * ((gcdDelta z1 z2 p.1 p.2 : ℝ)
              * (1 + secFreq₁ z1 z2 p.1 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹
              * (1 + secFreq₂ z1 z2 p.2 ^ 2 * Real.sqrt (1 - γ ^ 2) * Real.sqrt Pa.M)⁻¹) := by
            ring
  exact norm_tsum_pair_le _ _ _ hg hT

end Work.FIArea2
