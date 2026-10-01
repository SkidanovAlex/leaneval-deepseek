import Mathlib

/-!
# The Euler–Maclaurin integral representation of `ζ`

For `0 < re s`, `s ≠ 1` and `N ≥ 1`,

`ζ s = ∑_{n ≤ N} n^{-s} + N^{1-s}/(s-1) - N^{-s}/2 - s ∫_N^∞ ({u} - 1/2) u^{-s-1} du`.

The proof proceeds in three steps:

* Euler–Maclaurin summation for the *truncated* sum `∑_{n ≤ N} n^{-s}` (Abel summation, together
  with the evaluations of `∫ t^{-z}` and `∫ t^{-z-1}`);
* the same formula in the limit `N → ∞` for `1 < re s`, i.e. the half-plane representation
  `ζ s = 1/(s-1) + 1/2 - s ∫_1^∞ ({u} - 1/2) u^{-s-1} du`;
* analytic continuation: the *entire* function `riemannZeta₀ s = ζ s - (s-1)⁻¹` agrees with
  `1/2 - s ∫_1^∞ ({u} - 1/2) u^{-s-1} du` on `re s > 1`, and the latter is holomorphic on
  `re s > 0` (differentiation under the integral sign), so the identity propagates to the whole
  half-plane by the identity theorem.
-/

open scoped Topology ENNReal
open Filter MeasureTheory

set_option maxHeartbeats 1000000

namespace Work.ZeroDensity.Ingham

/-! ### Elementary bounds for the fractional part -/

lemma norm_fract_cast_le (t : ℝ) : ‖((Int.fract t : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg t)]
  linarith [Int.fract_lt_one t]

lemma norm_fractCast_sub_half_le (t : ℝ) : ‖(((Int.fract t : ℝ) : ℂ) - 1 / 2)‖ ≤ 1 / 2 := by
  have hcast : (((Int.fract t : ℝ) : ℂ) - 1 / 2) = ((Int.fract t - 1 / 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith [Int.fract_nonneg t, Int.fract_lt_one t]

/-- For `1 ≤ t ≤ N` and any real exponent `a`, `t ^ a ≤ max 1 (N ^ a)`. -/
lemma rpow_le_max_one (a : ℝ) {t N : ℝ} (ht : 1 ≤ t) (htN : t ≤ N) : t ^ a ≤ max 1 (N ^ a) := by
  rcases le_or_gt a 0 with h | h
  · calc t ^ a ≤ t ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le ht h
      _ = 1 := Real.rpow_zero t
      _ ≤ max 1 (N ^ a) := le_max_left _ _
  · calc t ^ a ≤ N ^ a :=
        Real.rpow_le_rpow (le_of_lt (lt_of_lt_of_le one_pos ht)) htN h.le
      _ ≤ max 1 (N ^ a) := le_max_right _ _

lemma norm_cpow_le_max (e : ℂ) {t N : ℝ} (ht : 1 ≤ t) (htN : t ≤ N) :
    ‖(t : ℂ) ^ e‖ ≤ max 1 (N ^ e.re) := by
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0]
  exact rpow_le_max_one _ ht htN

/-- `⌊t⌋₊ = t - {t}` for `t ≥ 0` (as complex numbers). -/
lemma natFloor_cast_eq_sub_fract {t : ℝ} (ht : 0 ≤ t) :
    ((⌊t⌋₊ : ℕ) : ℂ) = (t : ℂ) - ((Int.fract t : ℝ) : ℂ) := by
  have hfloor : (⌊t⌋ : ℤ) = (⌊t⌋₊ : ℤ) := by
    rw [Int.floor_eq_iff]
    exact ⟨by exact_mod_cast Nat.floor_le ht, by exact_mod_cast Nat.lt_floor_add_one t⟩
  have hreal : ((⌊t⌋₊ : ℕ) : ℝ) = t - Int.fract t := by
    have h := Int.fract_add_floor t
    rw [hfloor] at h
    push_cast at h
    linarith
  calc ((⌊t⌋₊ : ℕ) : ℂ) = (((⌊t⌋₊ : ℕ) : ℝ) : ℂ) := by push_cast; ring
    _ = ((t - Int.fract t : ℝ) : ℂ) := by rw [hreal]
    _ = (t : ℂ) - ((Int.fract t : ℝ) : ℂ) := by push_cast; ring

/-- `∑_{k=0}^{m} [k ≠ 0] = m`. -/
lemma sum_Icc_zero_ite (m : ℕ) :
    (∑ k ∈ Finset.Icc 0 m, (if k = 0 then (0 : ℂ) else 1)) = (m : ℂ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (Nat.zero_le (m + 1))
      (fun k => if k = 0 then (0 : ℂ) else 1), ih]
    simp only [Nat.succ_ne_zero, if_false]
    push_cast
    ring

/-! ### Integrability of the Euler–Maclaurin kernel on `(1, ∞)` -/

lemma integrableOn_fract_cpow_local {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun u : ℝ => (((Int.fract u : ℝ) : ℂ) - 1 / 2) * (u : ℂ) ^ (-z - 1))
      (Set.Ioi 1) := by
  have hr : -z.re - 1 < -1 := by linarith
  have hdom : IntegrableOn (fun u : ℝ => (1 / 2 : ℝ) * u ^ (-z.re - 1)) (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt hr one_pos).const_mul (1 / 2)
  refine Integrable.mono' hdom ?_ ?_
  · have hB : AEStronglyMeasurable (fun u : ℝ => (((Int.fract u : ℝ) : ℂ) - 1 / 2))
        (volume.restrict (Set.Ioi (1 : ℝ))) :=
      ((Complex.measurable_ofReal.comp measurable_fract).sub measurable_const).aestronglyMeasurable
    have hcont : ContinuousOn (fun u : ℝ => (u : ℂ) ^ (-z - 1)) (Set.Ioi 1) :=
      continuousOn_of_forall_continuousAt (fun x hx =>
        Complex.continuousAt_ofReal_cpow_const x (-z - 1)
          (Or.inr (by have h : (1:ℝ) < x := hx; linarith)))
    exact hB.mul (hcont.aestronglyMeasurable measurableSet_Ioi)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu1 : (0 : ℝ) < u := lt_trans one_pos hu
    have hnorm : ‖(u : ℂ) ^ (-z - 1)‖ = u ^ (-z.re - 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hu1, Complex.sub_re, Complex.neg_re, Complex.one_re]
    rw [norm_mul, hnorm]
    exact mul_le_mul_of_nonneg_right (norm_fractCast_sub_half_le u) (Real.rpow_nonneg hu1.le _)

/-- Integrability of `(t : ℂ) ^ e` on `(1, N]`. -/
lemma integrableOn_cpow_Icc (e : ℂ) (N : ℕ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ e) (Set.Icc 1 (N : ℝ)) := by
  have hvol : volume (Set.Icc (1 : ℝ) (N : ℝ)) ≠ ∞ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  refine Integrable.mono' (g := fun _ : ℝ => max 1 ((N:ℝ) ^ e.re))
    (integrableOn_const hvol) ?_ ?_
  · exact (continuousOn_of_forall_continuousAt (fun x hx =>
      Complex.continuousAt_ofReal_cpow_const x e
        (Or.inr (by
          have h : (1:ℝ) ≤ x := by simpa using hx.1
          linarith)))).aestronglyMeasurable
      measurableSet_Icc
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact norm_cpow_le_max e ht.1 ht.2

/-- Integrability of `(t : ℂ) ^ e * {t}` on `(1, N]`. -/
lemma integrableOn_cpow_mul_fract_Icc (e : ℂ) (N : ℕ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ e * ((Int.fract t : ℝ) : ℂ)) (Set.Icc 1 (N : ℝ)) := by
  have hvol : volume (Set.Icc (1 : ℝ) (N : ℝ)) ≠ ∞ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  refine Integrable.mono' (g := fun _ : ℝ => max 1 ((N:ℝ) ^ e.re))
    (integrableOn_const hvol) ?_ ?_
  · exact ((continuousOn_of_forall_continuousAt (fun x hx =>
        Complex.continuousAt_ofReal_cpow_const x e
          (Or.inr (by
            have h : (1:ℝ) ≤ x := by simpa using hx.1
            linarith)))).aestronglyMeasurable
        measurableSet_Icc).mul
      ((Complex.measurable_ofReal.comp measurable_fract).aestronglyMeasurable)
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have h2 : ‖(t : ℂ) ^ e‖ ≤ max 1 ((N:ℝ) ^ e.re) := norm_cpow_le_max e ht.1 ht.2
    have h3 : (0 : ℝ) ≤ max 1 ((N:ℝ) ^ e.re) := le_trans zero_le_one (le_max_left _ _)
    rw [norm_mul]
    have h1 : ‖((Int.fract t : ℝ) : ℂ)‖ ≤ 1 := norm_fract_cast_le t
    nlinarith [norm_nonneg ((t : ℂ) ^ e), norm_nonneg (((Int.fract t : ℝ) : ℂ)), h1, h2, h3]

/-! ### Euler–Maclaurin summation -/

/-- **Euler–Maclaurin summation.** For `0 < re z`, `z ≠ 1` and `1 ≤ N`,
`∑_{n=1}^{N} n^{-z} = (N^{1-z} - 1)/(1-z) + (1 + N^{-z})/2 - z ∫_1^N ({u} - 1/2) u^{-z-1} du`. -/
lemma emFiniteSum_local {z : ℂ} (hz : 0 < z.re) (hz1 : z ≠ 1) {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-z)) = (((N : ℂ) ^ (1 - z) - 1) / (1 - z))
      + (1 + (N : ℂ) ^ (-z)) / 2
      - z * ∫ u in (1 : ℝ)..(N : ℝ), (((Int.fract u : ℝ) : ℂ) - 1 / 2) * (u : ℂ) ^ (-z - 1) := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have h1z : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hzero : (0:ℝ) ∉ Set.uIcc (1:ℝ) (N:ℝ) := by
    rw [Set.uIcc_of_le hN1]
    simp only [Set.mem_Icc, not_and, not_le]
    intro _
    linarith
  have hcondJ : -1 < (-z).re ∨ (-z) ≠ -1 ∧ (0:ℝ) ∉ Set.uIcc (1:ℝ) (N:ℝ) :=
    Or.inr ⟨by intro h; exact hz1 (neg_inj.mp h), hzero⟩
  have hcondP : -1 < (-z-1).re ∨ (-z-1) ≠ -1 ∧ (0:ℝ) ∉ Set.uIcc (1:ℝ) (N:ℝ) :=
    Or.inr ⟨by intro h; exact hz0 (by linear_combination -h), hzero⟩
  have hJval : ∫ t in Set.Ioc (1 : ℝ) (N : ℝ), (t : ℂ) ^ (-z)
      = ((N : ℂ) ^ (1 - z) - 1) / (1 - z) := by
    rw [← intervalIntegral.integral_of_le hN1, integral_cpow (r := -z) hcondJ]
    simp only [Complex.ofReal_natCast, Complex.ofReal_one, Complex.one_cpow]
    rw [show -z + 1 = 1 - z by ring]
  have hPval : ∫ t in Set.Ioc (1 : ℝ) (N : ℝ), (t : ℂ) ^ (-z - 1)
      = (1 - (N : ℂ) ^ (-z)) / z := by
    rw [← intervalIntegral.integral_of_le hN1, integral_cpow (r := -z - 1) hcondP]
    simp only [Complex.ofReal_natCast, Complex.ofReal_one, Complex.one_cpow]
    rw [show -z - 1 + 1 = -z by ring, div_eq_div_iff (neg_ne_zero.mpr hz0) hz0]
    ring
  have hIntPow : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-z)) (Set.Ioc 1 (N : ℝ)) :=
    (integrableOn_cpow_Icc (-z) N).mono_set Set.Ioc_subset_Icc_self
  have hIntPow1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-z - 1)) (Set.Ioc 1 (N : ℝ)) :=
    (integrableOn_cpow_Icc (-z - 1) N).mono_set Set.Ioc_subset_Icc_self
  have hIntFract : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-z - 1) * ((Int.fract t : ℝ) : ℂ))
      (Set.Ioc 1 (N : ℝ)) :=
    (integrableOn_cpow_mul_fract_Icc (-z - 1) N).mono_set Set.Ioc_subset_Icc_self
  have hderivIoc : ∫ t in Set.Ioc (1 : ℝ) (N : ℝ),
        deriv (fun t : ℝ => (t : ℂ) ^ (-z)) t * ((⌊t⌋₊ : ℕ) : ℂ)
      = ∫ t in Set.Ioc (1 : ℝ) (N : ℝ),
          (-z * (t : ℂ) ^ (-z) + z * ((t : ℂ) ^ (-z - 1) * ((Int.fract t : ℝ) : ℂ))) := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
    have ht1 : (1 : ℝ) < t := ht.1
    have ht0 : (0 : ℝ) < t := lt_trans one_pos ht1
    have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht0
    rw [Complex.deriv_ofReal_cpow_const (ne_of_gt ht0) (neg_ne_zero.mpr hz0),
      natFloor_cast_eq_sub_fract (le_of_lt ht0)]
    have hu : (t : ℂ) ^ (-z) = (t : ℂ) ^ (-z - 1) * (t : ℂ) := by
      conv_lhs => rw [show (-z : ℂ) = (-z - 1) + 1 by ring]
      rw [Complex.cpow_add (-z - 1) 1 htc, Complex.cpow_one]
    rw [hu]
    ring
  have hsplitIoc : ∫ t in Set.Ioc (1 : ℝ) (N : ℝ),
        (-z * (t : ℂ) ^ (-z) + z * ((t : ℂ) ^ (-z - 1) * ((Int.fract t : ℝ) : ℂ)))
      = -z * (∫ t in Set.Ioc (1 : ℝ) (N : ℝ), (t : ℂ) ^ (-z))
        + z * (∫ t in Set.Ioc (1 : ℝ) (N : ℝ),
            (t : ℂ) ^ (-z - 1) * ((Int.fract t : ℝ) : ℂ)) := by
    rw [integral_add (hIntPow.const_mul (-z)) (hIntFract.const_mul z),
      integral_const_mul, integral_const_mul]
  have hfracfun : ∫ t in Set.Ioc (1 : ℝ) (N : ℝ),
        (((Int.fract t : ℝ) : ℂ) - 1 / 2) * (t : ℂ) ^ (-z - 1)
      = (∫ t in Set.Ioc (1 : ℝ) (N : ℝ), (t : ℂ) ^ (-z - 1) * ((Int.fract t : ℝ) : ℂ))
        - (1 / 2) * ∫ t in Set.Ioc (1 : ℝ) (N : ℝ), (t : ℂ) ^ (-z - 1) := by
    rw [← integral_const_mul (1 / 2 : ℂ) (fun t : ℝ => (t : ℂ) ^ (-z - 1)),
      ← integral_sub hIntFract (hIntPow1.const_mul (1 / 2))]
    refine setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
    ring
  have hf_diff : ∀ t ∈ Set.Icc ((1:ℕ):ℝ) (N : ℝ),
      DifferentiableAt ℝ (fun t : ℝ => (t : ℂ) ^ (-z)) t := by
    intro t ht
    have ht0 : (0 : ℝ) < t := by
      have h1 : ((1:ℕ):ℝ) ≤ t := ht.1
      have h2 : (0 : ℝ) < ((1:ℕ):ℝ) := by norm_num
      linarith
    exact (hasDerivAt_ofReal_cpow_const (ne_of_gt ht0) (neg_ne_zero.mpr hz0)).differentiableAt
  have hf_int : IntegrableOn (deriv (fun t : ℝ => (t : ℂ) ^ (-z))) (Set.Icc ((1:ℕ):ℝ) (N : ℝ)) := by
    have hbase : IntegrableOn (fun t : ℝ => -z * (t : ℂ) ^ (-z - 1))
        (Set.Icc ((1:ℕ):ℝ) (N : ℝ)) := by
      rw [Nat.cast_one]
      exact (integrableOn_cpow_Icc (-z - 1) N).const_mul (-z)
    refine hbase.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have ht0 : (0 : ℝ) < t := by
      have h1 : (1:ℝ) ≤ t := by simpa using ht.1
      linarith
    exact (Complex.deriv_ofReal_cpow_const (ne_of_gt ht0) (neg_ne_zero.mpr hz0)).symm
  have hAbel := sum_mul_eq_sub_sub_integral_mul'
      (c := fun k : ℕ => if k = 0 then (0 : ℂ) else 1)
      (f := fun t : ℝ => (t : ℂ) ^ (-z)) (n := 1) (m := N) hN hf_diff hf_int
  have hL : (∑ k ∈ Finset.Ioc 1 N, ((k : ℂ) ^ (-z)) * (if k = 0 then (0 : ℂ) else 1))
      = ∑ k ∈ Finset.Ioc 1 N, (k : ℂ) ^ (-z) := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk0 : k ≠ 0 := by
      simp only [Finset.mem_Ioc] at hk
      omega
    rw [if_neg hk0, mul_one]
  have hA1 : (∑ k ∈ Finset.Icc 0 N, (if k = 0 then (0 : ℂ) else 1)) = (N : ℂ) :=
    sum_Icc_zero_ite N
  have hA2 : (∑ k ∈ Finset.Icc 0 1, (if k = 0 then (0 : ℂ) else 1)) = 1 := by
    simpa using sum_Icc_zero_ite 1
  have hone : (((1:ℕ) : ℂ)) = 1 := by norm_num
  have hcastN : (N : ℂ) ^ (-z) * (N : ℂ) = (N : ℂ) ^ (1 - z) := by
    have hNc : (N : ℂ) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    rw [show (1 : ℂ) - z = -z + 1 by ring, Complex.cpow_add (-z) 1 hNc, Complex.cpow_one]
  have hsum_eq : ∀ t : ℝ,
      (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (if k = 0 then (0 : ℂ) else 1)) = ((⌊t⌋₊ : ℕ) : ℂ) :=
    fun t => sum_Icc_zero_ite ⌊t⌋₊
  have hInt : (∫ t in Set.Ioc (1 : ℝ) (N : ℝ), deriv (fun t : ℝ => (t : ℂ) ^ (-z)) t *
        (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (if k = 0 then (0 : ℂ) else 1)))
      = ∫ t in Set.Ioc (1 : ℝ) (N : ℝ),
          deriv (fun t : ℝ => (t : ℂ) ^ (-z)) t * ((⌊t⌋₊ : ℕ) : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
    rw [hsum_eq t]
  have hAbel' : (∑ k ∈ Finset.Ioc 1 N, (k : ℂ) ^ (-z))
      = (N : ℂ) ^ (1 - z) - 1
        - ∫ t in Set.Ioc (1 : ℝ) (N : ℝ),
            deriv (fun t : ℝ => (t : ℂ) ^ (-z)) t * ((⌊t⌋₊ : ℕ) : ℂ) := by
    have hA := hAbel
    push_cast at hA
    rw [hL] at hA
    rw [hA1, hA2, hcastN, hInt] at hA
    rw [hA, Complex.one_cpow]
    ring_nf
  have hcons : (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-z))
      = 1 + ∑ n ∈ Finset.Ioc 1 N, (n : ℂ) ^ (-z) := by
    rw [Finset.Icc_eq_cons_Ioc hN, Finset.sum_cons]
    simp only [Complex.ofReal_natCast, hone, Complex.one_cpow]
  have hInt1 : ∫ t in Set.Ioc (1 : ℝ) (N : ℝ),
        (t : ℂ) ^ (-z - 1) * ((Int.fract t : ℝ) : ℂ)
      = ∫ t in Set.Ioc (1 : ℝ) (N : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1) := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
    ring
  rw [intervalIntegral.integral_of_le hN1, hfracfun, hcons, hAbel', hderivIoc, hsplitIoc, hJval,
    hPval]
  field_simp [h1z, hz0]
  ring

/-! ### The half-plane representation of `ζ` -/

/-- `N ↦ N^w → 0` as `N → ∞` through the naturals, for `re w < 0`. -/
lemma tendsto_natCast_cpow_zero {w : ℂ} (hw : w.re < 0) :
    Tendsto (fun N : ℕ => (N : ℂ) ^ w) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h1 : Tendsto (fun N : ℕ => (N : ℝ) ^ (w.re)) atTop (𝓝 0) := by
    have h := tendsto_rpow_neg_atTop (y := -w.re) (by linarith)
    have h2 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(-w.re))) atTop (𝓝 0) :=
      h.comp tendsto_natCast_atTop_atTop
    simpa only [neg_neg] using h2
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  exact (Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hN) w).symm

/-- Reindexing `∑_{n=1}^{N}` as a sum over `range N`. -/
lemma sum_Icc_one_eq_sum_range_cpow (z : ℂ) : ∀ N : ℕ,
    (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-z)) = ∑ i ∈ Finset.range N, (((i : ℂ) + 1) ^ (-z)) := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    have h1 : (∑ n ∈ Finset.Icc 1 (N + 1), (n : ℂ) ^ (-z))
        = (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-z)) + (((N : ℂ) + 1) ^ (-z)) := by
      rw [Finset.sum_Icc_succ_top (Nat.le_add_left 1 N)]
      rw [Nat.cast_add, Nat.cast_one]
    rw [h1, ih, Finset.sum_range_succ]

/-- The truncated zeta sums converge to `ζ z` for `1 < re z`. -/
lemma hasSum_cpow_zeta {z : ℂ} (hz : 1 < z.re) :
    HasSum (fun n : ℕ => (((n : ℂ) + 1) ^ (-z))) (riemannZeta z) := by
  have hbase : Summable (fun m : ℕ => 1 / (m : ℂ) ^ z) := Complex.summable_one_div_nat_cpow.mpr hz
  have hsumm : Summable (fun n : ℕ => 1 / (↑(n + 1) : ℂ) ^ z) :=
    (summable_nat_add_iff (f := fun m : ℕ => 1 / (m : ℂ) ^ z) 1).mpr hbase
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hz]
  simpa only [Complex.cpow_neg, one_div, Nat.cast_add, Nat.cast_one] using hsumm.hasSum

/-- **The Euler–Maclaurin representation of `ζ` in the half-plane `re z > 1`.** -/
lemma riemannZeta_eq_halfPlane_local {z : ℂ} (hz : 1 < z.re) :
    riemannZeta z = (z - 1)⁻¹ + 1 / 2
      - z * ∫ u in Set.Ioi (1 : ℝ), (((Int.fract u : ℝ) : ℂ) - 1 / 2) * (u : ℂ) ^ (-z - 1) := by
  have hz1 : z ≠ 1 := by intro h; rw [h] at hz; norm_num at hz
  have hint : IntegrableOn
      (fun u : ℝ => (((Int.fract u : ℝ) : ℂ) - 1 / 2) * (u : ℂ) ^ (-z - 1)) (Set.Ioi 1) :=
    integrableOn_fract_cpow_local (by linarith)
  have hlim1 : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-z)) atTop
      (𝓝 (riemannZeta z)) := by
    refine (hasSum_cpow_zeta hz).tendsto_sum_nat.congr' ?_
    filter_upwards with N
    exact (sum_Icc_one_eq_sum_range_cpow z N).symm
  have h0a : Tendsto (fun N : ℕ => (N : ℂ) ^ (1 - z)) atTop (𝓝 0) :=
    tendsto_natCast_cpow_zero (by simp only [Complex.sub_re, Complex.one_re]; linarith)
  have hA : Tendsto (fun N : ℕ => (((N : ℂ) ^ (1 - z) - 1) / (1 - z))) atTop (𝓝 ((z - 1)⁻¹)) := by
    have h1 : Tendsto (fun N : ℕ => (((N : ℂ) ^ (1 - z) - 1) / (1 - z))) atTop
        (𝓝 (((0 : ℂ) - 1) / (1 - z))) := (h0a.sub_const 1).div_const (1 - z)
    have hval : (((0 : ℂ) - 1) / (1 - z)) = (z - 1)⁻¹ := by
      have hsub : (1 : ℂ) - z = -(z - 1) := by ring
      rw [zero_sub, div_eq_mul_inv, hsub, inv_neg]
      ring
    rw [hval] at h1
    exact h1
  have hB : Tendsto (fun N : ℕ => (1 + (N : ℂ) ^ (-z)) / 2) atTop (𝓝 (1 / 2)) := by
    have h0 := tendsto_natCast_cpow_zero (w := -z) (by simp only [Complex.neg_re]; linarith)
    simpa using ((h0.const_add 1).div_const 2)
  have hC : Tendsto (fun N : ℕ => ∫ u in (1 : ℝ)..(N : ℝ),
        (((Int.fract u : ℝ) : ℂ) - 1 / 2) * (u : ℂ) ^ (-z - 1)) atTop
      (𝓝 (∫ u in Set.Ioi (1 : ℝ), (((Int.fract u : ℝ) : ℂ) - 1 / 2) * (u : ℂ) ^ (-z - 1))) :=
    intervalIntegral_tendsto_integral_Ioi 1 hint tendsto_natCast_atTop_atTop
  have hlim2 : Tendsto (fun N : ℕ => (((N : ℂ) ^ (1 - z) - 1) / (1 - z))
        + (1 + (N : ℂ) ^ (-z)) / 2
        - z * ∫ u in (1 : ℝ)..(N : ℝ),
            (((Int.fract u : ℝ) : ℂ) - 1 / 2) * (u : ℂ) ^ (-z - 1)) atTop
      (𝓝 ((z - 1)⁻¹ + 1 / 2
        - z * ∫ u in Set.Ioi (1 : ℝ),
            (((Int.fract u : ℝ) : ℂ) - 1 / 2) * (u : ℂ) ^ (-z - 1))) :=
    (hA.add hB).sub (hC.const_mul z)
  have hev : (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-z)) =ᶠ[atTop]
      (fun N : ℕ => (((N : ℂ) ^ (1 - z) - 1) / (1 - z)) + (1 + (N : ℂ) ^ (-z)) / 2
        - z * ∫ u in (1 : ℝ)..(N : ℝ),
            (((Int.fract u : ℝ) : ℂ) - 1 / 2) * (u : ℂ) ^ (-z - 1)) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact emFiniteSum_local (by linarith) hz1 hN
  have hlim1' : Tendsto (fun N : ℕ => (((N : ℂ) ^ (1 - z) - 1) / (1 - z))
        + (1 + (N : ℂ) ^ (-z)) / 2
        - z * ∫ u in (1 : ℝ)..(N : ℝ),
            (((Int.fract u : ℝ) : ℂ) - 1 / 2) * (u : ℂ) ^ (-z - 1)) atTop
      (𝓝 (riemannZeta z)) :=
    hlim1.congr' hev
  exact tendsto_nhds_unique hlim1' hlim2

/-! ### Analyticity of the Euler–Maclaurin integral -/

/-- Integrability of `log u * u^a` on `(1, ∞)` for `a < -1`. -/
lemma integrableOn_log_mul_rpow {a : ℝ} (ha : a < -1) :
    IntegrableOn (fun u : ℝ => Real.log u * u ^ a) (Set.Ioi 1) := by
  have hε : (0 : ℝ) < -(a + 1) / 2 := by linarith
  have hb : a + (-(a + 1) / 2) < -1 := by linarith
  have hdom : IntegrableOn (fun u : ℝ => (1 / (-(a + 1) / 2)) * u ^ (a + (-(a + 1) / 2)))
      (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt hb one_pos).const_mul _
  refine Integrable.mono' hdom ?_ ?_
  · refine (ContinuousOn.mul ?_ ?_).aestronglyMeasurable measurableSet_Ioi
    · exact continuousOn_of_forall_continuousAt (fun x hx =>
        Real.continuousAt_log (by have h : (1:ℝ) < x := hx; linarith))
    · exact continuousOn_of_forall_continuousAt (fun x hx =>
        Real.continuousAt_rpow_const x a (Or.inl (by have h : (1:ℝ) < x := hx; linarith)))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu1 : (1 : ℝ) < u := hu
    have hu0 : (0 : ℝ) < u := lt_trans one_pos hu1
    have hlog0 : 0 ≤ Real.log u := Real.log_nonneg hu1.le
    have hua : 0 ≤ u ^ a := Real.rpow_nonneg hu0.le a
    have hlog_le : Real.log u ≤ u ^ (-(a + 1) / 2) / (-(a + 1) / 2) :=
      Real.log_le_rpow_div hu0.le hε
    have hrw : u ^ (a + (-(a + 1) / 2)) = u ^ a * u ^ (-(a + 1) / 2) :=
      Real.rpow_add hu0 a _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hlog0, abs_of_nonneg hua]
    calc Real.log u * u ^ a
        ≤ (u ^ (-(a + 1) / 2) / (-(a + 1) / 2)) * u ^ a :=
          mul_le_mul_of_nonneg_right hlog_le hua
      _ = (1 / (-(a + 1) / 2)) * (u ^ a * u ^ (-(a + 1) / 2)) := by ring
      _ = (1 / (-(a + 1) / 2)) * u ^ (a + (-(a + 1) / 2)) := by rw [hrw]

/-- Differentiability of the Euler–Maclaurin integral at `z` (differentiation under the integral). -/
lemma differentiableAt_integral_fract_cpow_local {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ (fun w : ℂ => ∫ u in Set.Ioi (1 : ℝ),
      (((Int.fract u : ℝ) : ℂ) - 1 / 2) * (u : ℂ) ^ (-w - 1)) z := by
  have hρ0 : 0 < z.re / 2 := by linarith
  have hbound_int : Integrable (fun u : ℝ => Real.log u * u ^ (-(z.re / 2) - 1))
      (volume.restrict (Set.Ioi (1 : ℝ))) :=
    integrableOn_log_mul_rpow (a := -(z.re / 2) - 1) (by linarith)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi (1 : ℝ)))
    (F := fun w u => (((Int.fract u : ℝ) : ℂ) - 1 / 2) * (u : ℂ) ^ (-w - 1))
    (F' := fun w u => (((Int.fract u : ℝ) : ℂ) - 1 / 2) *
        ((Real.log u : ℂ) * (-1) * (u : ℂ) ^ (-w - 1)))
    (x₀ := z) (s := Metric.ball z (z.re / 2))
    (bound := fun u : ℝ => Real.log u * u ^ (-(z.re / 2) - 1))
    (Metric.ball_mem_nhds z hρ0) ?_ ?_ ?_ ?_ hbound_int ?_).2.differentiableAt
  · refine Eventually.of_forall (fun w => ?_)
    have hB : AEStronglyMeasurable (fun u : ℝ => (((Int.fract u : ℝ) : ℂ) - 1 / 2))
        (volume.restrict (Set.Ioi (1 : ℝ))) :=
      ((Complex.measurable_ofReal.comp measurable_fract).sub measurable_const).aestronglyMeasurable
    exact hB.mul ((continuousOn_of_forall_continuousAt (fun x hx =>
      Complex.continuousAt_ofReal_cpow_const x (-w - 1)
        (Or.inr (by have h : (1:ℝ) < x := hx; linarith)))).aestronglyMeasurable measurableSet_Ioi)
  · exact integrableOn_fract_cpow_local hz
  · have hB : AEStronglyMeasurable (fun u : ℝ => (((Int.fract u : ℝ) : ℂ) - 1 / 2))
        (volume.restrict (Set.Ioi (1 : ℝ))) :=
      ((Complex.measurable_ofReal.comp measurable_fract).sub measurable_const).aestronglyMeasurable
    have hG : AEStronglyMeasurable
        (fun u : ℝ => ((Real.log u : ℂ) * (-1)) * (u : ℂ) ^ (-z - 1))
        (volume.restrict (Set.Ioi (1 : ℝ))) := by
      refine (ContinuousOn.mul (ContinuousOn.mul ?_ continuousOn_const) ?_).aestronglyMeasurable
        measurableSet_Ioi
      · exact (Complex.continuous_ofReal.comp_continuousOn
          (continuousOn_of_forall_continuousAt
            (fun x hx => Real.continuousAt_log (by have h : (1:ℝ) < x := hx; linarith))))
      · exact continuousOn_of_forall_continuousAt (fun x hx =>
          Complex.continuousAt_ofReal_cpow_const x (-z - 1)
            (Or.inr (by have h : (1:ℝ) < x := hx; linarith)))
    exact hB.mul hG
  · refine (ae_restrict_mem measurableSet_Ioi).mono (fun u hu w hw => ?_)
    have hu1 : (1 : ℝ) < u := hu
    have hu0 : (0 : ℝ) < u := lt_trans one_pos hu1
    have hlog0 : 0 ≤ Real.log u := Real.log_nonneg hu1.le
    have hwre : z.re / 2 < w.re := by
      have h1 : |(w - z).re| ≤ ‖w - z‖ := Complex.abs_re_le_norm (w - z)
      rw [Complex.sub_re, abs_le] at h1
      have h2 : ‖w - z‖ < z.re / 2 := by
        rwa [Metric.mem_ball, dist_eq_norm] at hw
      linarith [h1.1]
    have hpow : u ^ (-w.re - 1) ≤ u ^ (-(z.re / 2) - 1) :=
      Real.rpow_le_rpow_of_exponent_le hu1.le (by linarith)
    have hnorm2 : ‖(Real.log u : ℂ) * (-1) * (u : ℂ) ^ (-w - 1)‖
        = Real.log u * u ^ (-w.re - 1) := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog0, norm_neg,
        norm_one, one_mul, mul_one, Complex.norm_cpow_eq_rpow_re_of_pos hu0, Complex.sub_re,
        Complex.neg_re, Complex.one_re]
    calc ‖(((Int.fract u : ℝ) : ℂ) - 1 / 2) * ((Real.log u : ℂ) * (-1) * (u : ℂ) ^ (-w - 1))‖
        = ‖(((Int.fract u : ℝ) : ℂ) - 1 / 2)‖ *
          ‖(Real.log u : ℂ) * (-1) * (u : ℂ) ^ (-w - 1)‖ := norm_mul _ _
      _ ≤ (1 / 2) * (Real.log u * u ^ (-w.re - 1)) := by
          rw [hnorm2]
          exact mul_le_mul_of_nonneg_right (norm_fractCast_sub_half_le u)
            (mul_nonneg hlog0 (Real.rpow_nonneg hu0.le _))
      _ ≤ Real.log u * u ^ (-w.re - 1) := by
          nlinarith [hlog0, Real.rpow_nonneg hu0.le (-w.re - 1)]
      _ ≤ Real.log u * u ^ (-(z.re / 2) - 1) := mul_le_mul_of_nonneg_left hpow hlog0
  · refine (ae_restrict_mem measurableSet_Ioi).mono (fun u hu w _ => ?_)
    have hu0 : (0 : ℝ) < u := lt_trans one_pos hu
    have hune : (u : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hu0
    have h1 : HasDerivAt (fun y : ℂ => (u : ℂ) ^ (-y - 1))
        ((u : ℂ) ^ (-w - 1) * Complex.log (u : ℂ) * (-1)) w :=
      ((hasDerivAt_id w).neg.sub_const 1).const_cpow (Or.inl hune)
    have h2 : HasDerivAt (fun y : ℂ => (((Int.fract u : ℝ) : ℂ) - 1 / 2) * (u : ℂ) ^ (-y - 1))
        ((((Int.fract u : ℝ) : ℂ) - 1 / 2) *
          ((u : ℂ) ^ (-w - 1) * Complex.log (u : ℂ) * (-1))) w := h1.const_mul _
    refine h2.congr_deriv ?_
    rw [← Complex.ofReal_log (le_of_lt hu0)]
    ring

/-- The parametric integral `w ↦ ∫_{(1,∞)} ({u} - 1/2) u^{-w-1} du` is complex-analytic at every
point `z` with `0 < re z`. -/
lemma analyticAt_integral_fract_cpow_local {z : ℂ} (hz : 0 < z.re) :
    AnalyticAt ℂ (fun w : ℂ => ∫ u in Set.Ioi (1 : ℝ),
        (((Int.fract u : ℝ) : ℂ) - 1 / 2) * (u : ℂ) ^ (-w - 1)) z := by
  have hρ0 : 0 < z.re / 2 := by linarith
  have hd : DifferentiableOn ℂ
      (fun w : ℂ => ∫ u in Set.Ioi (1 : ℝ),
        (((Int.fract u : ℝ) : ℂ) - 1 / 2) * (u : ℂ) ^ (-w - 1))
      (Metric.ball z (z.re / 2)) := by
    intro w hw
    have hwre : 0 < w.re := by
      have h1 : |(w - z).re| ≤ ‖w - z‖ := Complex.abs_re_le_norm (w - z)
      rw [Complex.sub_re, abs_le] at h1
      have h2 : ‖w - z‖ < z.re / 2 := by
        rwa [Metric.mem_ball, dist_eq_norm] at hw
      linarith [h1.1]
    exact (differentiableAt_integral_fract_cpow_local hwre).differentiableWithinAt
  exact (hd.analyticOnNhd Metric.isOpen_ball) z (Metric.mem_ball_self hρ0)

/-! ### Analytic continuation -/

/-- `riemannZeta₀ s = ζ s - (s-1)⁻¹` agrees with the closed Euler–Maclaurin form on `re s > 0`. -/
lemma riemannZeta₀_eq_integral_local {z : ℂ} (hz : 0 < z.re) :
    riemannZeta₀ z = 1 / 2 - z * ∫ u in Set.Ioi (1 : ℝ),
        (((Int.fract u : ℝ) : ℂ) - 1 / 2) * (u : ℂ) ^ (-z - 1) := by
  have hpre : IsPreconnected {w : ℂ | 0 < w.re} := by
    have hconv : Convex ℝ {w : ℂ | 0 < w.re} := by
      intro x hx y hy a b ha hb hab
      simp only [Set.mem_ofPred_eq] at hx hy ⊢
      rw [Complex.add_re, Complex.smul_re, Complex.smul_re, smul_eq_mul, smul_eq_mul]
      rcases eq_or_lt_of_le ha with ha0 | ha0
      · have hb1 : b = 1 := by linarith
        have haz : a = 0 := ha0.symm
        rw [haz, hb1, zero_mul, one_mul]
        linarith
      · have h1 : 0 < a * x.re := mul_pos ha0 hx
        have h2 : 0 ≤ b * y.re := mul_nonneg hb hy.le
        linarith
    exact hconv.isPreconnected
  set I : ℂ → ℂ := fun w => ∫ u in Set.Ioi (1 : ℝ),
      (((Int.fract u : ℝ) : ℂ) - 1 / 2) * (u : ℂ) ^ (-w - 1) with hI
  have hf : AnalyticOnNhd ℂ riemannZeta₀ {w : ℂ | 0 < w.re} := fun w _ =>
    (differentiable_riemannZeta₀.differentiableOn.analyticOnNhd isOpen_univ) w trivial
  have hg : AnalyticOnNhd ℂ (fun w => 1 / 2 - w * I w) {w : ℂ | 0 < w.re} := by
    have hI' : AnalyticOnNhd ℂ I {w : ℂ | 0 < w.re} :=
      fun w hw => analyticAt_integral_fract_cpow_local hw
    have hid : AnalyticOnNhd ℂ (fun w : ℂ => w * I w) {w : ℂ | 0 < w.re} :=
      (analyticOnNhd_id (𝕜 := ℂ) (E := ℂ)).mul hI'
    exact (analyticOnNhd_const (v := (1 / 2 : ℂ))).sub hid
  have hev : riemannZeta₀ =ᶠ[𝓝 (2 : ℂ)] (fun w => 1 / 2 - w * I w) := by
    have hopen1 : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen1.mem_nhds (by norm_num : (2 : ℂ) ∈ {w : ℂ | 1 < w.re})] with w hw
    have hw1 : w ≠ 1 := by intro h; rw [h] at hw; norm_num at hw
    have h2 : riemannZeta w = (w - 1)⁻¹ + (1 / 2 - w * I w) := by
      rw [riemannZeta_eq_halfPlane_local hw]
      simp only [hI]
      ring
    have h1 := riemannZeta_eq_inv_sub_add hw1
    rw [h2] at h1
    exact (add_left_cancel h1).symm
  have hEqOn := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hf hg hpre
    (z₀ := (2 : ℂ)) (by norm_num) hev
  have h := hEqOn hz
  simpa only [hI] using h

theorem zetaEMIntegral {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) (N : ℕ) (hN : 1 ≤ N) :
    riemannZeta s =
      (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) + ((N : ℂ) ^ (1 - s)) / (s - 1)
      - (N : ℂ) ^ (-s) / 2
      - s * ∫ u in Set.Ioi (N : ℝ), (((Int.fract u : ℝ) : ℂ) - 1 / 2) * (u : ℂ) ^ (-s - 1) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hint : IntegrableOn
      (fun u : ℝ => (((Int.fract u : ℝ) : ℂ) - 1 / 2) * (u : ℂ) ^ (-s - 1)) (Set.Ioi 1) :=
    integrableOn_fract_cpow_local hs0
  have hintN : IntegrableOn
      (fun u : ℝ => (((Int.fract u : ℝ) : ℂ) - 1 / 2) * (u : ℂ) ^ (-s - 1)) (Set.Ioi (N : ℝ)) :=
    hint.mono_set (Set.Ioi_subset_Ioi hN1)
  have hsplit : ∫ u in Set.Ioi (1 : ℝ), (((Int.fract u : ℝ) : ℂ) - 1 / 2) * (u : ℂ) ^ (-s - 1)
      = (∫ u in (1 : ℝ)..(N : ℝ), (((Int.fract u : ℝ) : ℂ) - 1 / 2) * (u : ℂ) ^ (-s - 1))
        + ∫ u in Set.Ioi (N : ℝ), (((Int.fract u : ℝ) : ℂ) - 1 / 2) * (u : ℂ) ^ (-s - 1) := by
    rw [← intervalIntegral.integral_interval_add_Ioi hint hintN]
  have hzeta : riemannZeta s = (s - 1)⁻¹ + 1 / 2
      - s * ∫ u in Set.Ioi (1 : ℝ), (((Int.fract u : ℝ) : ℂ) - 1 / 2) * (u : ℂ) ^ (-s - 1) := by
    rw [riemannZeta_eq_inv_sub_add hs1, riemannZeta₀_eq_integral_local hs0]
    ring
  rw [hzeta, emFiniteSum_local hs0 hs1 hN, hsplit]
  have hsub : (1 : ℂ) - s = -(s - 1) := by ring
  rw [div_eq_mul_inv, div_eq_mul_inv, hsub, inv_neg]
  ring

end Work.ZeroDensity.Ingham
