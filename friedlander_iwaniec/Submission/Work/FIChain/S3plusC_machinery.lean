import Mathlib
import Submission.Work.FIChain.Defs
import Submission.Work.FIChain.S3plusC_aux2
import Submission.Work.FIChain.s3InnerInt_eq_split
import Submission.Work.FIChain.S3plusC_uIntegral_reduce
import Submission.Work.FIChain.s3RemPlus_defs
import Submission.Work.FIChain.S3plusC_eq_main_add_rem
import Submission.Work.FIChain.scale_factsC
import Submission.Work.FIChain.s3RemPlus_cutfree_defs
import Submission.Work.FIChain.s3RemPlus_le_cutfree
import Submission.Work.FIChain.measurable_s3halves
import Submission.Work.FIChain.s3Rem_fibre_pt_le
import Submission.Work.FIChain.cfRsum_le
import Submission.Work.FIChain.zc_sharp_bounds

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset MeasureTheory
open scoped Interval BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The `z`-substitution `(z,u) ↦ (ℓz, ℓu)` of the companion's §8.4 -/

/-- `∫_p^q F (c·u)/u du = ∫_{cp}^{cq} F w / w dw` for `c > 0` (substitution `w = c·u`; the
measure `du/u` is exactly the invariant one). -/
lemma integral_comp_mul_div_self (F : ℝ → ℝ) {c : ℝ} (hc : 0 < c) (p q : ℝ) :
    (∫ u in p..q, F (c * u) / u) = ∫ w in (c * p)..(c * q), F w / w := by
  have hG : ∀ u : ℝ, F (c * u) / u = c * (F (c * u) / (c * u)) := by
    intro u
    rcases eq_or_ne u 0 with rfl | hu
    · simp
    · field_simp
  rw [intervalIntegral.integral_congr (fun u _ => hG u)]
  rw [intervalIntegral.integral_const_mul]
  have h1 : (∫ u in p..q, F (c * u) / (c * u)) = c⁻¹ * ∫ w in c * p..c * q, F w / w := by
    have := intervalIntegral.integral_comp_mul_left (a := p) (b := q) (c := c)
      (fun w : ℝ => F w / w) hc.ne'
    simpa using this
  rw [h1]
  field_simp

/-- `∫_a^b J z / z dz = ∫_{ℓa}^{ℓb} J (v/ℓ) / v dv` for `ℓ > 0` (substitution `v = ℓ z`). -/
lemma zavg_outer_subst (J : ℝ → ℝ) {a b ℓ : ℝ} (hℓ : 0 < ℓ) :
    (∫ z in a..b, J z / z) = ∫ v in ℓ*a..ℓ*b, J (v/ℓ) / v := by
  have h := intervalIntegral.integral_comp_mul_left (a := a) (b := b) (c := ℓ)
      (fun v : ℝ => J (v/ℓ)/v) hℓ.ne'
  rw [smul_eq_mul] at h
  have hL : (∫ x in a..b, J (ℓ*x/ℓ)/(ℓ*x)) = ∫ z in a..b, J z / (ℓ*z) := by
    refine intervalIntegral.integral_congr (fun z _ => ?_)
    rw [show ℓ*z/ℓ = z by field_simp]
  rw [hL] at h
  have hR : (∫ z in a..b, J z / (ℓ*z)) = (∫ z in a..b, J z/z) * ℓ⁻¹ := by
    rw [← intervalIntegral.integral_mul_const]
    refine intervalIntegral.integral_congr (fun z _ => ?_)
    rcases eq_or_ne z 0 with rfl | hz
    · simp
    · field_simp
  rw [hR] at h
  have hfin : (∫ z in a..b, J z/z) * ℓ⁻¹ * ℓ = ∫ v in ℓ*a..ℓ*b, J (v/ℓ)/v := by
    rw [h]; field_simp
  rw [← hfin, mul_assoc, inv_mul_cancel₀ hℓ.ne', mul_one]

/-- The two-variable substitution `(z,u) ↦ (ℓz, ℓu)` of an iterated integral over the domain
`{a < z < b, 1 < u < U z}`. -/
lemma zavg_two_subst {F : ℝ → ℝ → ℝ} {a b : ℝ} {U : ℝ → ℝ} {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (∫ z in a..b, (∫ u in (1 : ℝ)..(U z), F (ℓ * z) (ℓ * u) / (z * u)))
      = ∫ v in (ℓ * a)..(ℓ * b), (∫ w in ℓ..(ℓ * U (v / ℓ)), F v w / (v * w)) := by
  have h1 : ∀ z : ℝ, (∫ u in (1 : ℝ)..(U z), F (ℓ * z) (ℓ * u) / (z * u))
      = (∫ w in ℓ..(ℓ * U z), F (ℓ * z) w / w) / z := by
    intro z
    have hcongr : (∫ u in (1 : ℝ)..(U z), F (ℓ * z) (ℓ * u) / (z * u))
        = (∫ u in (1 : ℝ)..(U z), (F (ℓ * z) (ℓ * u) / u) / z) := by
      refine intervalIntegral.integral_congr (fun u _ => ?_)
      rw [div_div, mul_comm z u]
    rw [hcongr, intervalIntegral.integral_div,
      integral_comp_mul_div_self (fun w => F (ℓ * z) w) hℓ 1 (U z), mul_one]
  rw [intervalIntegral.integral_congr (fun z _ => h1 z)]
  have h := zavg_outer_subst (a := a) (b := b) (fun z => ∫ w in ℓ..(ℓ*U z), F (ℓ*z) w / w) hℓ
  rw [h]
  refine intervalIntegral.integral_congr (fun v _ => ?_)
  rw [mul_div_cancel₀ v hℓ.ne']
  rw [← intervalIntegral.integral_div]
  refine intervalIntegral.integral_congr (fun w _ => ?_)
  rw [div_div, mul_comm v w]

/-! ## 2. The `d`-majorant of the `λ⁺` remainder integrand -/

/-- The pointwise majorant of `s3RemI`: the `d`-sum of the absolute values of the two `r̃`'s. -/
def s3RemMaj (x Cm ℓ : ℕ) (z sz u : ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 ⌊u⌋₊,
    (|cfR (ℓ * d) ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊|
      + |cfR (ℓ * d) ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊|)

/-- The substituted form of the majorant (`v = ℓ·z`, `t = ℓ·u`). -/
def s3RemSub (x Cm ℓ : ℕ) (sc v t : ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 ⌊t / (ℓ : ℝ)⌋₊,
    (|cfR (ℓ * d) ⌊min (sc * v) (x : ℝ)⌋₊| + |cfR (ℓ * d) ⌊max v ((Cm : ℝ) * t)⌋₊|)

/-- `g̃ d ≤ 1`.  For squarefree `d` this is the product of the Euler factors `g̃ p < 1`; for
non-squarefree `d` it is `g̃ d = 0`. -/
lemma FIgtil_le_one (d : ℕ) : Submission.ASP.FIgtil d ≤ 1 := by
  rw [Submission.ASP.FIgtil]
  by_cases h : Squarefree d
  · rw [if_pos h]
    calc ∏ p ∈ d.primeFactors, Submission.ASP.gtilVal Submission.ASP.FIg p
        ≤ ∏ _p ∈ d.primeFactors, (1 : ℝ) := by
          refine Finset.prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_)
          · have hp1 : p.Prime := (Nat.mem_primeFactors.mp hp).1
            have h1 : 0 ≤ Submission.ASP.FIgtil p := Submission.ASP.FIgtil_nonneg p
            rwa [Submission.ASP.FIgtil_prime hp1] at h1
          · have hp1 : p.Prime := (Nat.mem_primeFactors.mp hp).1
            have h1 : Submission.ASP.FIgtil p ≤ 1 :=
              le_of_lt (Submission.ASP.FIgtil_lt_one hp1)
            rwa [Submission.ASP.FIgtil_prime hp1] at h1
      _ = 1 := by simp
  · rw [if_neg h]; norm_num

/-- The honest remainder of `ã` is bounded by `2·Ã(m)`. -/
lemma abs_cfR_le (ζ m : ℕ) : |cfR ζ m| ≤ 2 * AcountAtilC m := by
  have h := abs_rtildeFull_le_mul ζ m
  have h1 : Submission.ASP.FIgtil ζ ≤ 1 := FIgtil_le_one ζ
  have h2 : |Submission.ASP.FIgtil ζ| ≤ 1 := by
    rw [abs_of_nonneg (Submission.ASP.FIgtil_nonneg ζ)]; exact h1
  calc |cfR ζ m| ≤ (1 + |Submission.ASP.FIgtil ζ|) * AcountAtilC m := h
    _ ≤ (1 + 1) * AcountAtilC m := by
        refine mul_le_mul_of_nonneg_right (by linarith) (AcountAtilC_nonneg m)
    _ = 2 * AcountAtilC m := by ring

/-- **The pointwise majorant**: `|s3RemI| ≤ s3RemMaj` (triangle inequality, `|μ d| ≤ 1`). -/
lemma abs_s3RemI_le_s3RemMaj (x Cm ℓ : ℕ) (z sz u : ℝ) :
    |s3RemI x z sz Cm ℓ u| ≤ s3RemMaj x Cm ℓ z sz u := by
  rw [s3RemI, s3RemMaj]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun d _ => ?_))
  have hμ : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
    have := ArithmeticFunction.abs_moebius_le_one (n := d)
    exact_mod_cast this
  have hsub : |cfR (ℓ * d) ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊
        - cfR (ℓ * d) ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊|
      ≤ |cfR (ℓ * d) ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊|
        + |cfR (ℓ * d) ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊| := by
    have := abs_add_le (cfR (ℓ * d) ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊)
      (-cfR (ℓ * d) ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊)
    rw [abs_neg] at this
    simpa [sub_eq_add_neg] using this
  rw [abs_mul]
  calc |(ArithmeticFunction.moebius d : ℝ)|
        * |cfR (ℓ * d) ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊
            - cfR (ℓ * d) ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊|
      ≤ 1 * (|cfR (ℓ * d) ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊|
          + |cfR (ℓ * d) ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊|) :=
        mul_le_mul hμ hsub (abs_nonneg _) (by norm_num)
    _ = _ := one_mul _

/-- The substituted majorant at `(ℓz, ℓu)` is the majorant at `(z,u)` with `sz = sc·z`. -/
lemma s3RemSub_mul (x Cm ℓ : ℕ) (sc z u : ℝ) (hℓ : (0 : ℝ) < (ℓ : ℝ)) :
    s3RemSub x Cm ℓ sc ((ℓ : ℝ) * z) ((ℓ : ℝ) * u) = s3RemMaj x Cm ℓ z (sc * z) u := by
  have hdiv : (ℓ : ℝ) * u / (ℓ : ℝ) = u := by field_simp
  have h1 : sc * ((ℓ : ℝ) * z) = (ℓ : ℝ) * (sc * z) := by ring
  have h2 : (Cm : ℝ) * ((ℓ : ℝ) * u) = (ℓ : ℝ) * (Cm : ℝ) * u := by ring
  rw [s3RemSub, s3RemMaj, hdiv, h1, h2]

/-- `ℓ · U_ℓ(v/ℓ) = min (sc·v/Cm) (x/Cm)`: the two `(1.7)`-scales are `ℓ`-free after the
substitution. -/
lemma s3SplitU_mul (x Cm ℓ : ℕ) (sc v : ℝ) (hℓ : (0 : ℝ) < (ℓ : ℝ)) (hCm : (0 : ℝ) < (Cm : ℝ)) :
    (ℓ : ℝ) * s3SplitU x (v / (ℓ : ℝ)) (sc * (v / (ℓ : ℝ))) Cm ℓ
      = min (sc * v / (Cm : ℝ)) ((x : ℝ) / (Cm : ℝ)) := by
  have hℓne : (ℓ : ℝ) ≠ 0 := ne_of_gt hℓ
  have hCmne : (Cm : ℝ) ≠ 0 := ne_of_gt hCm
  rw [s3SplitU, mul_min_of_nonneg _ _ hℓ.le]
  congr 1
  · field_simp
  · field_simp

/-! ## 3. Measurability and boundedness of the majorant

`u ↦ s3RemMaj … u` is a finite sum over the `u`-dependent range `Icc 1 ⌊u⌋₊`; on any interval
`u ≤ N` that range sits inside the *fixed* range `Icc 1 N`, so the function is a finite sum of
measurable step functions there.  This gives the interval integrability of `u ↦ s3RemMaj … u / u`
(by `IntegrableOn.of_bound`), which is what the monotonicity `|s3RemI| ≤ s3RemMaj` needs. -/

/-- On `0 ≤ u ≤ N` the majorant is the fixed-range sum over `Icc 1 N` with an indicator. -/
lemma s3RemMaj_eq_fixed (x Cm ℓ : ℕ) (z sz : ℝ) (N : ℕ) {u : ℝ} (hu0 : 0 ≤ u)
    (huN : u ≤ (N : ℝ)) :
    s3RemMaj x Cm ℓ z sz u
      = ∑ d ∈ Finset.Icc 1 N,
          (if (d : ℝ) ≤ u then
            (|cfR (ℓ * d) ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊|
              + |cfR (ℓ * d) ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊|)
          else 0) := by
  rw [s3RemMaj]
  have hstep1 : (∑ d ∈ Finset.Icc 1 ⌊u⌋₊,
        (|cfR (ℓ * d) ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊|
          + |cfR (ℓ * d) ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊|))
      = ∑ d ∈ Finset.Icc 1 ⌊u⌋₊,
          (if (d : ℝ) ≤ u then
            (|cfR (ℓ * d) ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊|
              + |cfR (ℓ * d) ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊|)
          else 0) := by
    refine Finset.sum_congr rfl (fun d hd => ?_)
    rw [Finset.mem_Icc] at hd
    rw [if_pos (le_trans (by exact_mod_cast hd.2) (Nat.floor_le hu0))]
  rw [hstep1]
  refine Finset.sum_subset (M := ℝ) (s₁ := Finset.Icc 1 ⌊u⌋₊) (s₂ := Finset.Icc 1 N)
    (fun d hd => ?_) (fun d hd hdnot => ?_)
  · rw [Finset.mem_Icc] at hd ⊢
    exact ⟨hd.1, le_trans hd.2 (by simpa using Nat.floor_mono huN)⟩
  · rw [Finset.mem_Icc] at hd
    have hdgt : ⌊u⌋₊ < d := by
      by_contra hc
      exact hdnot (Finset.mem_Icc.mpr ⟨hd.1, not_lt.mp hc⟩)
    have hlt : u < (d : ℝ) := by
      have h2 : ((d : ℕ) : ℝ) ≥ ((⌊u⌋₊ : ℕ) : ℝ) + 1 := by exact_mod_cast hdgt
      have h3 := Nat.lt_floor_add_one u
      linarith
    exact if_neg (not_le.mpr hlt)

/-- The fixed-range sum is a measurable function of `u`. -/
lemma measurable_s3RemMaj_fixed (x Cm ℓ : ℕ) (z sz : ℝ) (N : ℕ) :
    Measurable (fun u : ℝ => ∑ d ∈ Finset.Icc 1 N,
          (if (d : ℝ) ≤ u then
            (|cfR (ℓ * d) ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊|
              + |cfR (ℓ * d) ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊|)
          else 0)) := by
  refine Finset.measurable_sum _ (fun d _ => ?_)
  refine Measurable.ite (measurableSet_le measurable_const measurable_id) ?_ measurable_const
  refine Measurable.add measurable_const ?_
  exact (measurable_of_countable (fun m : ℕ => |cfR (ℓ * d) m|)).comp
    (((measurable_const : Measurable (fun _ : ℝ => (ℓ : ℝ) * z)).max
      ((measurable_const : Measurable (fun _ : ℝ => (ℓ : ℝ) * (Cm : ℝ))).mul
        measurable_id)).nat_floor)

/-- `u ↦ s3RemMaj … u` is a.e. strongly measurable on `Ioc a b` (for `0 ≤ a`, `b ≤ N`). -/
lemma aestronglyMeasurable_s3RemMaj_Ioc (x Cm ℓ : ℕ) (z sz : ℝ) (N : ℕ) {a b : ℝ}
    (ha : 0 ≤ a) (hN : b ≤ (N : ℝ)) :
    AEStronglyMeasurable (fun u : ℝ => s3RemMaj x Cm ℓ z sz u)
      (volume.restrict (Set.Ioc a b)) := by
  refine ((measurable_s3RemMaj_fixed x Cm ℓ z sz N).aestronglyMeasurable).congr ?_
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
  exact Filter.Eventually.of_forall (fun u hu =>
    (s3RemMaj_eq_fixed x Cm ℓ z sz N (le_trans ha hu.1.le) (le_trans hu.2 hN)).symm)

/-- `u ↦ s3RemMaj … u / u` is integrable on `Ioc a b` (`1 ≤ a ≤ b`), provided the two `(1.7)`
arguments stay `≤ x`. -/
lemma integrableOn_s3RemMaj_div (x Cm ℓ : ℕ) (z sz : ℝ) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b)
    (hℓ1 : 1 ≤ ℓ) (hCm1 : 1 ≤ Cm) (hzx : (ℓ : ℝ) * z ≤ (x : ℝ))
    (hbx : b ≤ (x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ))) :
    IntegrableOn (fun u => s3RemMaj x Cm ℓ z sz u / u) (Set.Ioc a b) volume := by
  have hℓ0 : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hℓ1)
  have hCm0 : (0 : ℝ) < (Cm : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hCm1)
  have hAnn := AcountAtilC_nonneg x
  refine MeasureTheory.IntegrableOn.of_bound
    (measure_Ioc_lt_top) ?_ (4 * ((⌈b⌉₊ : ℕ) : ℝ) * AcountAtilC x) ?_
  · have h2 : (fun u : ℝ => s3RemMaj x Cm ℓ z sz u * u⁻¹) = (fun u : ℝ => s3RemMaj x Cm ℓ z sz u / u) := by
      funext u; rw [div_eq_mul_inv]
    rw [← h2]
    refine (aestronglyMeasurable_s3RemMaj_Ioc x Cm ℓ z sz ⌈b⌉₊
      (le_trans zero_le_one ha) (Nat.le_ceil b)).mul ?_
    exact (measurable_inv (G := ℝ)).aestronglyMeasurable
  · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall (fun u hu => ?_)
    have hu0 : (0 : ℝ) < u := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one ha) hu.1.le
    have hu1 : (1 : ℝ) ≤ u := le_trans ha hu.1.le
    have huN : u ≤ ((⌈b⌉₊ : ℕ) : ℝ) := le_trans hu.2 (Nat.le_ceil b)
    have hm1 : ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊ ≤ x := by
      refine le_trans (Nat.floor_mono (min_le_right _ _)) ?_
      simp
    have hm2 : ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊ ≤ x := by
      have hzu : (ℓ : ℝ) * (Cm : ℝ) * u ≤ (x : ℝ) := by
        have hle : u ≤ (x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)) := le_trans hu.2 hbx
        have := (le_div_iff₀ (mul_pos hℓ0 hCm0)).mp hle
        linarith [this]
      refine le_trans (Nat.floor_mono (max_le hzx hzu)) ?_
      simp
    have hterm : ∀ d ∈ Finset.Icc 1 ⌊u⌋₊,
        |(|cfR (ℓ * d) ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊|
          + |cfR (ℓ * d) ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊|)|
          ≤ 4 * AcountAtilC x := by
      intro d _
      rw [abs_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))]
      have h1 : |cfR (ℓ * d) ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊|
          ≤ 2 * AcountAtilC (⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊) := abs_cfR_le _ _
      have h2 : |cfR (ℓ * d) ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊|
          ≤ 2 * AcountAtilC (⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊) := abs_cfR_le _ _
      have e1 := AcountAtilC_mono_nat hm1
      have e2 := AcountAtilC_mono_nat hm2
      linarith
    have hmaj : |s3RemMaj x Cm ℓ z sz u| ≤ 4 * ((⌈b⌉₊ : ℕ) : ℝ) * AcountAtilC x := by
      rw [s3RemMaj]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have hsum : (∑ d ∈ Finset.Icc 1 ⌊u⌋₊,
          |(|cfR (ℓ * d) ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊|
            + |cfR (ℓ * d) ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊|)|)
          ≤ ∑ _d ∈ Finset.Icc 1 ⌊u⌋₊, (4 * AcountAtilC x) := Finset.sum_le_sum hterm
      have hcast : ((⌊u⌋₊ : ℕ) : ℝ) ≤ ((⌈b⌉₊ : ℕ) : ℝ) := by
        have h := Nat.floor_mono huN
        simp only [Nat.floor_natCast] at h
        exact_mod_cast h
      have hcard : (Finset.Icc 1 ⌊u⌋₊).card ≤ ⌊u⌋₊ := by
        have hsub : Finset.Icc 1 ⌊u⌋₊ ⊆ (Finset.range ⌊u⌋₊).image (fun k => k + 1) := by
          intro d hd
          rw [Finset.mem_Icc] at hd
          exact Finset.mem_image.mpr ⟨d - 1, by rw [Finset.mem_range]; omega, by omega⟩
        calc (Finset.Icc 1 ⌊u⌋₊).card ≤ ((Finset.range ⌊u⌋₊).image (fun k => k + 1)).card :=
              Finset.card_le_card hsub
          _ ≤ (Finset.range ⌊u⌋₊).card := Finset.card_image_le
          _ = ⌊u⌋₊ := Finset.card_range ⌊u⌋₊
      calc _ ≤ ∑ _d ∈ Finset.Icc 1 ⌊u⌋₊, (4 * AcountAtilC x) := hsum
        _ = ((Finset.Icc 1 ⌊u⌋₊).card : ℝ) * (4 * AcountAtilC x) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((⌊u⌋₊ : ℕ) : ℝ) * (4 * AcountAtilC x) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact_mod_cast hcard
        _ ≤ ((⌈b⌉₊ : ℕ) : ℝ) * (4 * AcountAtilC x) := by
            refine mul_le_mul_of_nonneg_right hcast (by positivity)
        _ = 4 * ((⌈b⌉₊ : ℕ) : ℝ) * AcountAtilC x := by ring
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hu0]
    rw [div_le_iff₀ hu0]
    have h4 : 0 ≤ 4 * ((⌈b⌉₊ : ℕ) : ℝ) * AcountAtilC x := by positivity
    calc |s3RemMaj x Cm ℓ z sz u| ≤ 4 * ((⌈b⌉₊ : ℕ) : ℝ) * AcountAtilC x := hmaj
      _ = (4 * ((⌈b⌉₊ : ℕ) : ℝ) * AcountAtilC x) * 1 := (mul_one _).symm
      _ ≤ (4 * ((⌈b⌉₊ : ℕ) : ℝ) * AcountAtilC x) * u := mul_le_mul_of_nonneg_left hu1 h4

/-! # State of this file (see the session handoff for the full account)

* §1 the substitutions of the companion's §8.4 (`integral_comp_mul_div_self`, `zavg_outer_subst`,
  `zavg_two_subst`) — PROVED;
* §2 the `d`-majorant of the remainder integrand (`s3RemMaj`, `s3RemSub`) and its basic properties
  (`FIgtil_le_one`, `abs_cfR_le`, `abs_s3RemI_le_s3RemMaj`, `s3RemSub_mul`, `s3SplitU_mul`) — PROVED;
* §3 measurability and integrability of the majorant (`s3RemMaj_eq_fixed`,
  `measurable_s3RemMaj_fixed`, `aestronglyMeasurable_s3RemMaj_Ioc`, `integrableOn_s3RemMaj_div`) —
  PROVED;
* the target `S3plusC_zavg_le` reduces to the two companion estimates `Work.FIChain.s3MainPlus_pt_le`
  (§8.3, pointwise, rate `(log x)^{-1}`) and `Work.FIChain.s3RemPlus_zavg_le` (§8.4, `z`-averaged,
  rate `(log x)^{-1}`) — both stated and reviewed in the session handoff — together with
  `S3plusC = s3MainPlus + s3RemPlus` (`S3plusC_eq_main_add_rem`) and the measure bookkeeping
  `∫ dy/y = ∫ dz/z = 1`, which gives the target with `K = K₁ + K₂`. -/

/-! ## 4. A crude pointwise bound for the REM half

The assembly below needs the two halves to be *integrable* on the `(y,z)`-window; the MAIN half is
bounded by its pointwise estimate, but for the REM half only the averaged estimate is available, so
we record here the companion's trivial pointwise bound. -/

lemma card_Icc_one_le (n : ℕ) : (Finset.Icc 1 n).card ≤ n := by
  have hsub : Finset.Icc 1 n ⊆ (Finset.range n).image (fun k => k + 1) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    exact Finset.mem_image.mpr ⟨d - 1, by rw [Finset.mem_range]; omega, by omega⟩
  calc (Finset.Icc 1 n).card ≤ ((Finset.range n).image (fun k => k + 1)).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.range n).card := Finset.card_image_le
    _ = n := Finset.card_range n

lemma abs_s3RemI_le_crude (x Cm ℓ : ℕ) (z sz u : ℝ)
    (hℓz : (ℓ : ℝ) * z ≤ (x : ℝ)) (hu : (ℓ : ℝ) * (Cm : ℝ) * u ≤ (x : ℝ)) :
    |s3RemI x z sz Cm ℓ u| ≤ 4 * AcountAtilC x * ((⌊u⌋₊ : ℕ) : ℝ) := by
  have hm1 : ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊ ≤ x :=
    le_trans (Nat.floor_mono (min_le_right _ _)) (by simp)
  have hm2 : ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊ ≤ x :=
    le_trans (Nat.floor_mono (max_le hℓz hu)) (by simp)
  have hAnn : 0 ≤ AcountAtilC x := AcountAtilC_nonneg x
  rw [s3RemI]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ d ∈ Finset.Icc 1 ⌊u⌋₊,
      |(ArithmeticFunction.moebius d : ℝ) *
        (cfR (ℓ * d) ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊
          - cfR (ℓ * d) ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊)|
        ≤ 4 * AcountAtilC x := by
    intro d _
    have hμ : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
      have h := ArithmeticFunction.abs_moebius_le_one (n := d)
      exact_mod_cast h
    have h1 : |cfR (ℓ * d) ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊| ≤ 2 * AcountAtilC x := by
      refine le_trans (abs_cfR_le _ _) ?_
      have h := AcountAtilC_mono_nat hm1
      linarith
    have h2 : |cfR (ℓ * d) ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊|
        ≤ 2 * AcountAtilC x := by
      refine le_trans (abs_cfR_le _ _) ?_
      have h := AcountAtilC_mono_nat hm2
      linarith
    have h3 : |cfR (ℓ * d) ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊
          - cfR (ℓ * d) ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊|
        ≤ |cfR (ℓ * d) ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊|
          + |cfR (ℓ * d) ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊| := by
      have h := abs_add_le (cfR (ℓ * d) ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊)
        (-cfR (ℓ * d) ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊)
      rw [abs_neg] at h
      simpa [sub_eq_add_neg] using h
    rw [abs_mul]
    calc |(ArithmeticFunction.moebius d : ℝ)| *
          |cfR (ℓ * d) ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊
            - cfR (ℓ * d) ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊|
        ≤ 1 * (2 * AcountAtilC x + 2 * AcountAtilC x) :=
          mul_le_mul hμ (le_trans h3 (by linarith)) (abs_nonneg _) (by norm_num)
      _ = 4 * AcountAtilC x := by ring
  calc ∑ d ∈ Finset.Icc 1 ⌊u⌋₊,
        |(ArithmeticFunction.moebius d : ℝ) *
          (cfR (ℓ * d) ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊
            - cfR (ℓ * d) ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊)|
      ≤ ∑ _d ∈ Finset.Icc 1 ⌊u⌋₊, (4 * AcountAtilC x) := Finset.sum_le_sum hterm
    _ ≤ ((⌊u⌋₊ : ℕ) : ℝ) * (4 * AcountAtilC x) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast card_Icc_one_le ⌊u⌋₊
    _ = 4 * AcountAtilC x * ((⌊u⌋₊ : ℕ) : ℝ) := by ring

/-- The `u`-integral of the REM integrand over `[1,U]` is `≪ Ã(x)·(U+1)`. -/
lemma abs_intervalIntegral_s3RemI_le (x Cm ℓ : ℕ) (z sz U : ℝ) (hU0 : 0 ≤ U) (hℓ1 : 1 ≤ ℓ)
    (hℓz : (ℓ : ℝ) * z ≤ (x : ℝ)) (hUx : U ≤ (x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ))) :
    |∫ u in (1 : ℝ)..U, s3RemI x z sz Cm ℓ u / u| ≤ 4 * AcountAtilC x * (U + 1) := by
  have hAnn : 0 ≤ AcountAtilC x := AcountAtilC_nonneg x
  have hC : (0 : ℝ) ≤ 4 * AcountAtilC x := by positivity
  have hnorm : ‖∫ u in (1 : ℝ)..U, s3RemI x z sz Cm ℓ u / u‖
      ≤ 4 * AcountAtilC x * |U - 1| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const_ae ?_
    rw [MeasureTheory.ae_iff]
    refine measure_mono_null (fun u hu => ?_) (measure_singleton (1 : ℝ))
    push_neg at hu
    obtain ⟨huI, hbig⟩ := hu
    rcases Set.mem_uIoc.mp huI with ⟨h1u, huU⟩ | ⟨hUu, hu1⟩
    · have hu0 : 0 < u := by linarith
      have hux : (ℓ : ℝ) * (Cm : ℝ) * u ≤ (x : ℝ) := by
        rcases Nat.eq_zero_or_pos Cm with h | h
        · subst h
          simp only [Nat.cast_zero, mul_zero, div_zero] at hUx ⊢
          linarith
        · have hpos : (0 : ℝ) < (ℓ : ℝ) * (Cm : ℝ) :=
            mul_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hℓ1))
              (by exact_mod_cast h)
          have h1 : (ℓ : ℝ) * (Cm : ℝ) * u ≤ (ℓ : ℝ) * (Cm : ℝ) * U :=
            mul_le_mul_of_nonneg_left huU hpos.le
          have h2 : (ℓ : ℝ) * (Cm : ℝ) * U ≤ (x : ℝ) := by
            have h3 := (le_div_iff₀ hpos).mp hUx
            simpa [mul_comm] using h3
          linarith
      have hcrude := abs_s3RemI_le_crude x Cm ℓ z sz u hℓz hux
      have hfloor : ((⌊u⌋₊ : ℕ) : ℝ) ≤ u := Nat.floor_le (by linarith)
      have hgoal : ‖s3RemI x z sz Cm ℓ u / u‖ ≤ 4 * AcountAtilC x := by
        rw [Real.norm_eq_abs, abs_div, abs_of_pos hu0, div_le_iff₀ hu0]
        calc |s3RemI x z sz Cm ℓ u| ≤ 4 * AcountAtilC x * ((⌊u⌋₊ : ℕ) : ℝ) := hcrude
          _ ≤ 4 * AcountAtilC x * u := mul_le_mul_of_nonneg_left hfloor hC
          _ = (4 * AcountAtilC x) * u := by ring
      exact absurd hgoal (not_le.mpr hbig)
    · by_cases hu1' : u = 1
      · exact hu1'
      · have hu_lt : u < 1 := lt_of_le_of_ne hu1 hu1'
        have hfl : ⌊u⌋₊ = 0 := Nat.floor_eq_zero.mpr hu_lt
        have hzero : s3RemI x z sz Cm ℓ u = 0 := by
          rw [s3RemI, hfl]
          simp
        rw [hzero, zero_div, norm_zero] at hbig
        exact absurd ((le_refl (0 : ℝ)).trans hC) (not_le.mpr hbig)
  rw [Real.norm_eq_abs] at hnorm
  have h1 : |U - 1| ≤ U + 1 := by
    rw [abs_sub_le_iff]
    constructor <;> linarith
  calc |∫ u in (1 : ℝ)..U, s3RemI x z sz Cm ℓ u / u|
      ≤ 4 * AcountAtilC x * |U - 1| := hnorm
    _ ≤ 4 * AcountAtilC x * (U + 1) := mul_le_mul_of_nonneg_left h1 hC

/-- The trivial pointwise bound for the REM half. -/
lemma abs_s3RemPlus_le_crude (lam : ℕ → ℝ) (x : ℕ) (z sy sz : ℝ) (Cm : ℕ)
    (hlam : ∀ ν : ℕ, |lam ν| ≤ 1) (hsz0 : 0 ≤ sz) :
    |s3RemPlus lam x z sy sz Cm|
      ≤ 4 * AcountAtilC x * (((x : ℝ) ^ 3) + 1) * (((x : ℝ) / (Cm : ℝ)) + 1) := by
  have hAnn : 0 ≤ AcountAtilC x := AcountAtilC_nonneg x
  have hC : (0 : ℝ) ≤ 4 * AcountAtilC x := by positivity
  have hxm : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
  rw [s3RemPlus]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ ℓ ∈ Finset.Icc 1 x,
      |(if ((ℓ : ℕ) : ℝ) * z ≤ (x : ℝ) then
        (∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
            (ArithmeticFunction.moebius b : ℝ)) * Submission.ASP.rhoOf lam ℓ *
          ∫ u in (1 : ℝ)..(min (sz / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))),
            (∑ d ∈ Finset.Icc 1 ⌊u⌋₊, (ArithmeticFunction.moebius d : ℝ) *
              (cfR (ℓ * d) ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊
                - cfR (ℓ * d) ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊)) / u
      else 0)| ≤ ((ℓ.divisors.card : ℝ)) ^ 2 * (4 * AcountAtilC x * ((x : ℝ) / (Cm : ℝ) + 1)) := by
    intro ℓ hℓ
    have hℓ1 : 1 ≤ ℓ := (Finset.mem_Icc.mp hℓ).1
    by_cases hc : ((ℓ : ℕ) : ℝ) * z ≤ (x : ℝ)
    · rw [if_pos hc]
      have hW : |(∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
            (ArithmeticFunction.moebius b : ℝ)) * Submission.ASP.rhoOf lam ℓ|
          ≤ ((ℓ.divisors.card : ℝ)) ^ 2 := cfWeight_abs_le lam sy ℓ hlam
      have hU0 : 0 ≤ min (sz / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ))) :=
        le_min (div_nonneg hsz0 (Nat.cast_nonneg Cm))
          (div_nonneg hxm (by positivity))
      have hUx : min (sz / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))
          ≤ (x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)) := min_le_right _ _
      have hint := abs_intervalIntegral_s3RemI_le x Cm ℓ z sz
        (min (sz / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))) hU0 hℓ1 hc hUx
      have hUm : min (sz / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))
          ≤ (x : ℝ) / (Cm : ℝ) := by
        refine le_trans (min_le_right _ _) ?_
        rcases Nat.eq_zero_or_pos Cm with h | h
        · subst h
          simp
        · have hCmpos : (0 : ℝ) < (Cm : ℝ) := by exact_mod_cast h
          have hℓ1R : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ1
          have hden : (Cm : ℝ) ≤ (ℓ : ℝ) * (Cm : ℝ) := by nlinarith
          exact div_le_div_of_nonneg_left hxm hCmpos hden
      have hint' : |∫ u in (1 : ℝ)..(min (sz / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))),
            (∑ d ∈ Finset.Icc 1 ⌊u⌋₊, (ArithmeticFunction.moebius d : ℝ) *
              (cfR (ℓ * d) ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊
                - cfR (ℓ * d) ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊)) / u|
          ≤ 4 * AcountAtilC x * ((x : ℝ) / (Cm : ℝ) + 1) := by
        refine le_trans hint ?_
        refine mul_le_mul_of_nonneg_left ?_ hC
        linarith
      rw [abs_mul]
      calc |(∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
              (ArithmeticFunction.moebius b : ℝ)) * Submission.ASP.rhoOf lam ℓ|
            * |∫ u in (1 : ℝ)..(min (sz / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))),
              (∑ d ∈ Finset.Icc 1 ⌊u⌋₊, (ArithmeticFunction.moebius d : ℝ) *
                (cfR (ℓ * d) ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊
                  - cfR (ℓ * d) ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊)) / u|
          ≤ ((ℓ.divisors.card : ℝ)) ^ 2 * (4 * AcountAtilC x * ((x : ℝ) / (Cm : ℝ) + 1)) :=
            mul_le_mul hW hint' (abs_nonneg _) (by positivity)
        _ = ((ℓ.divisors.card : ℝ)) ^ 2 * (4 * AcountAtilC x * ((x : ℝ) / (Cm : ℝ) + 1)) := rfl
    · rw [if_neg hc]
      simp only [abs_zero]
      exact mul_nonneg (by positivity) (by positivity)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have hcard : ∑ ℓ ∈ Finset.Icc 1 x, ((ℓ.divisors.card : ℝ)) ^ 2 ≤ ((x : ℝ) ^ 3 + 1) := by
    have h1 : ∀ ℓ ∈ Finset.Icc 1 x, ((ℓ.divisors.card : ℝ)) ^ 2 ≤ (x : ℝ) ^ 2 := by
      intro ℓ hℓ
      have hℓx : ℓ ≤ x := (Finset.mem_Icc.mp hℓ).2
      have hcard_le : (ℓ.divisors.card : ℝ) ≤ (ℓ : ℝ) := by
        have h := Nat.card_divisors_le_self ℓ
        exact_mod_cast h
      have hℓxR : (ℓ : ℝ) ≤ (x : ℝ) := by exact_mod_cast hℓx
      calc ((ℓ.divisors.card : ℝ)) ^ 2 ≤ ((ℓ : ℝ)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) hcard_le 2
        _ ≤ (x : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hℓxR 2
    calc ∑ ℓ ∈ Finset.Icc 1 x, ((ℓ.divisors.card : ℝ)) ^ 2
        ≤ ∑ _ℓ ∈ Finset.Icc 1 x, (x : ℝ) ^ 2 := Finset.sum_le_sum h1
      _ = ((Finset.Icc 1 x).card : ℝ) * (x : ℝ) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (x : ℝ) * (x : ℝ) ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact_mod_cast card_Icc_one_le x
      _ ≤ (x : ℝ) ^ 3 + 1 := by
          have h3 : (x : ℝ) * (x : ℝ) ^ 2 = (x : ℝ) ^ 3 := by ring
          rw [h3]
          linarith [pow_nonneg hxm 3]
  calc ∑ ℓ ∈ Finset.Icc 1 x,
        ((ℓ.divisors.card : ℝ)) ^ 2 * (4 * AcountAtilC x * ((x : ℝ) / (Cm : ℝ) + 1))
      = (∑ ℓ ∈ Finset.Icc 1 x, ((ℓ.divisors.card : ℝ)) ^ 2)
          * (4 * AcountAtilC x * ((x : ℝ) / (Cm : ℝ) + 1)) := by
        rw [Finset.sum_mul]
    _ ≤ ((x : ℝ) ^ 3 + 1) * (4 * AcountAtilC x * ((x : ℝ) / (Cm : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 4 * AcountAtilC x * ((x : ℝ) ^ 3 + 1) * ((x : ℝ) / (Cm : ℝ) + 1) := by ring

/-! ## 5. The assembly

The target is reduced to the two halves by a single clean chain: the `y`-average of the two halves is
split, the MAIN half is bounded pointwise, and the REM half by the averaged estimate. -/

lemma eventually_restrict_Ioc {a b : ℝ} {P : ℝ → Prop} (h : ∀ y ∈ Set.Ioc a b, P y) :
    ∀ᵐ y ∂(volume.restrict (Set.Ioc a b)), P y :=
  (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall h)

/-- `1/y` is integrable on a positive interval. -/
lemma integrableOn_one_div_Ioc (a b : ℝ) (ha : 0 < a) :
    IntegrableOn (fun y : ℝ => 1 / y) (Set.Ioc a b) volume := by
  refine MeasureTheory.IntegrableOn.of_bound (measure_Ioc_lt_top) ?_ (1 / a) ?_
  · exact (measurable_const.div measurable_id).aestronglyMeasurable
  · refine eventually_restrict_Ioc (fun y hy => ?_)
    have hy0 : 0 < y := lt_of_lt_of_le ha hy.1.le
    rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hy0)]
    exact one_div_le_one_div_of_le ha hy.1.le

lemma integrable_const_div_Ioc (c a b : ℝ) (ha : 0 < a) :
    Integrable (fun y : ℝ => c / y) (volume.restrict (Set.Ioc a b)) := by
  have h1 : Integrable (fun y : ℝ => 1 / y) (volume.restrict (Set.Ioc a b)) :=
    integrableOn_one_div_Ioc a b ha
  simpa only [mul_one_div] using h1.const_mul c

/-- `∫_a^{e·a} c/y dy = c` for `a > 0` (the window average `∫ dy/y = 1`). -/
lemma intervalIntegral_const_div_exp (c a : ℝ) (ha : 0 < a) :
    (∫ y in a..(Real.exp 1 * a), c / y) = c := by
  have hfun : (fun y : ℝ => c / y) = fun y : ℝ => c * (1 / y) := by
    funext y; rw [mul_one_div]
  rw [hfun, intervalIntegral.integral_const_mul,
    integral_one_div_of_pos ha (by positivity)]
  rw [show Real.exp 1 * a / a = Real.exp 1 by field_simp]
  rw [Real.log_exp, mul_one]

/-- `∫_a^b c/y dy = c · ∫_a^b dy/y`. -/
lemma intervalIntegral_const_div_eq (c a b : ℝ) :
    (∫ y in a..b, c / y) = c * (∫ y in a..b, (1 : ℝ) / y) := by
  have hfun : (fun y : ℝ => c / y) = fun y : ℝ => c * (1 / y) := by
    funext y; rw [mul_one_div]
  rw [hfun, intervalIntegral.integral_const_mul]

/-- **The measure-theoretic core of the assembly.**  For two jointly measurable families
`main`, `rem` on a rectangle `[p,q] × [a,b]` (`p, a > 0`), a pointwise bound `|main| ≤ M`, a
pointwise crude bound `|rem| ≤ Cr` and an averaged bound `R` for `rem`, the `z`-average of the
`y`-average of `|main + rem|` is at most `M·(∫dy/y)·(∫dz/z)` plus the averaged `rem`-bound. -/
lemma zavg_main_plus_rem_le {main rem : ℝ → ℝ → ℝ} {p q a b M R Cr : ℝ}
    (hpq : p ≤ q) (hMnn : 0 ≤ M) (hCrnn : 0 ≤ Cr)
    (hmainM : ∀ z ∈ Set.Icc p q, ∀ y ∈ Set.Icc a b, |main z y| ≤ M)
    (hremCr : ∀ z ∈ Set.Icc p q, ∀ y ∈ Set.Icc a b, |rem z y| ≤ Cr)
    (hremR : (∫ z in p..q, (∫ y in a..b, |rem z y| / y) / z) ≤ R)
    (hmeas : Measurable (fun t : ℝ × ℝ => |main t.1 t.2|) ∧
      Measurable (fun t : ℝ × ℝ => |rem t.1 t.2|))
    (ha : 0 < a) (hab : a ≤ b) (hp : 0 < p) :
    (∫ z in p..q, (∫ y in a..b, |main z y + rem z y| / y) / z)
      ≤ M * (∫ y in a..b, (1 : ℝ) / y) * (∫ z in p..q, (1 : ℝ) / z) + R := by
  have hIyz : (0 : ℝ) ≤ ∫ y in a..b, (1 : ℝ) / y :=
    intervalIntegral.integral_nonneg hab (fun y hy =>
      div_nonneg zero_le_one (le_of_lt (lt_of_lt_of_le ha hy.1)))
  have hslice : ∀ z : ℝ, AEStronglyMeasurable (fun y : ℝ => |main z y|)
        (volume.restrict (Set.Ioc a b)) ∧
      AEStronglyMeasurable (fun y : ℝ => |rem z y|) (volume.restrict (Set.Ioc a b)) := by
    intro z
    exact ⟨((hmeas.1.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable).mono_measure
        Measure.restrict_le_self,
      ((hmeas.2.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable).mono_measure
        Measure.restrict_le_self⟩
  have hslice_div : ∀ z : ℝ,
      AEStronglyMeasurable (fun y : ℝ => |main z y| / y) (volume.restrict (Set.Ioc a b)) ∧
      AEStronglyMeasurable (fun y : ℝ => |rem z y| / y) (volume.restrict (Set.Ioc a b)) ∧
      AEStronglyMeasurable (fun y : ℝ => (|main z y| + |rem z y|) / y)
        (volume.restrict (Set.Ioc a b)) := by
    intro z
    refine ⟨?_, ?_, ?_⟩
    · exact (((hmeas.1.comp (measurable_const.prodMk measurable_id)).div measurable_id
        ).aestronglyMeasurable).mono_measure Measure.restrict_le_self
    · exact (((hmeas.2.comp (measurable_const.prodMk measurable_id)).div measurable_id
        ).aestronglyMeasurable).mono_measure Measure.restrict_le_self
    · exact ((((hmeas.1.comp (measurable_const.prodMk measurable_id)).add
        (hmeas.2.comp (measurable_const.prodMk measurable_id))).div measurable_id
        ).aestronglyMeasurable).mono_measure Measure.restrict_le_self
  have hparam : Measurable (fun z : ℝ => ∫ y in a..b, |main z y| / y) ∧
      Measurable (fun z : ℝ => ∫ y in a..b, |rem z y| / y) :=
    ⟨measurable_intervalIntegral_param a (hmeas.1.div measurable_snd) measurable_const,
      measurable_intervalIntegral_param a (hmeas.2.div measurable_snd) measurable_const⟩
  -- integrability of the `y`-integrands on the window
  have hint_y : ∀ z ∈ Set.Icc p q,
      Integrable (fun y : ℝ => |main z y| / y) (volume.restrict (Set.Ioc a b)) ∧
      Integrable (fun y : ℝ => |rem z y| / y) (volume.restrict (Set.Ioc a b)) := by
    intro z hz
    have hmaj : Integrable (fun y : ℝ => (M + Cr) / y) (volume.restrict (Set.Ioc a b)) :=
      integrable_const_div_Ioc (M + Cr) a b ha
    constructor
    · refine Integrable.mono' hmaj (hslice_div z).1 ?_
      refine eventually_restrict_Ioc (fun y hy => ?_)
      have hy0 : 0 < y := lt_of_lt_of_le ha hy.1.le
      have h1 : |main z y| ≤ M := hmainM z hz y (Set.Ioc_subset_Icc_self hy)
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (abs_nonneg _) hy0.le)]
      exact div_le_div_of_nonneg_right (by linarith [h1, hCrnn]) hy0.le
    · refine Integrable.mono' hmaj (hslice_div z).2.1 ?_
      refine eventually_restrict_Ioc (fun y hy => ?_)
      have hy0 : 0 < y := lt_of_lt_of_le ha hy.1.le
      have h1 : |rem z y| ≤ Cr := hremCr z hz y (Set.Ioc_subset_Icc_self hy)
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (abs_nonneg _) hy0.le)]
      exact div_le_div_of_nonneg_right (by linarith [h1, hMnn]) hy0.le
  -- the inner (`y`-)comparison at a fixed `z`
  have hinner : ∀ z ∈ Set.Icc p q, (∫ y in a..b, |main z y + rem z y| / y)
      ≤ M * (∫ y in a..b, (1 : ℝ) / y) + ∫ y in a..b, |rem z y| / y := by
    intro z hz
    have hA : (∫ y in a..b, |main z y + rem z y| / y)
        = ∫ y in Set.Ioc a b, (|main z y + rem z y| / y) :=
      intervalIntegral.integral_of_le hab
    have hC : (∫ y in a..b, |main z y| / y)
        = ∫ y in Set.Ioc a b, (|main z y| / y) := intervalIntegral.integral_of_le hab
    have hD : (∫ y in a..b, |rem z y| / y)
        = ∫ y in Set.Ioc a b, (|rem z y| / y) := intervalIntegral.integral_of_le hab
    have hm_int : Integrable (fun y : ℝ => |main z y| / y) (volume.restrict (Set.Ioc a b)) :=
      (hint_y z hz).1
    have hr_int : Integrable (fun y : ℝ => |rem z y| / y) (volume.restrict (Set.Ioc a b)) :=
      (hint_y z hz).2
    have hmaj : Integrable (fun y : ℝ => (M + Cr) / y) (volume.restrict (Set.Ioc a b)) :=
      integrable_const_div_Ioc (M + Cr) a b ha
    have hmono : (∫ y in Set.Ioc a b, (|main z y + rem z y| / y))
        ≤ ∫ y in Set.Ioc a b, ((|main z y| + |rem z y|) / y) := by
      refine MeasureTheory.integral_mono_of_nonneg
        (eventually_restrict_Ioc (fun y hy =>
          div_nonneg (abs_nonneg _) (le_of_lt (lt_of_lt_of_le ha hy.1.le))))
        (by
          refine Integrable.mono' hmaj (hslice_div z).2.2 ?_
          refine eventually_restrict_Ioc (fun y hy => ?_)
          have hy0 : 0 < y := lt_of_lt_of_le ha hy.1.le
          have h1 : |main z y| ≤ M := hmainM z hz y (Set.Ioc_subset_Icc_self hy)
          have h2 : |rem z y| ≤ Cr := hremCr z hz y (Set.Ioc_subset_Icc_self hy)
          rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by positivity) hy0.le)]
          exact div_le_div_of_nonneg_right (by linarith) hy0.le)
        (eventually_restrict_Ioc (fun y hy =>
          div_le_div_of_nonneg_right (abs_add_le _ _) (le_of_lt (lt_of_lt_of_le ha hy.1.le))))
    have hmain_set : (∫ y in Set.Ioc a b, (|main z y| / y))
        ≤ M * (∫ y in Set.Ioc a b, (1 : ℝ) / y) := by
      have hg' : Integrable (fun y : ℝ => M / y) (volume.restrict (Set.Ioc a b)) :=
        integrable_const_div_Ioc M a b ha
      refine le_trans (MeasureTheory.integral_mono_of_nonneg ?_ hg' ?_) ?_
      · exact eventually_restrict_Ioc (fun y hy =>
          div_nonneg (abs_nonneg _) (le_of_lt (lt_of_lt_of_le ha hy.1.le)))
      · refine eventually_restrict_Ioc (fun y hy => ?_)
        have hy0 : 0 < y := lt_of_lt_of_le ha hy.1.le
        have h1 : |main z y| ≤ M := hmainM z hz y (Set.Ioc_subset_Icc_self hy)
        exact div_le_div_of_nonneg_right h1 hy0.le
      · rw [← intervalIntegral.integral_of_le hab, ← intervalIntegral.integral_of_le hab,
          intervalIntegral_const_div_eq M a b]
    have hmain_le : (∫ y in a..b, |main z y| / y) ≤ M * (∫ y in a..b, (1 : ℝ) / y) := by
      rw [hC, intervalIntegral.integral_of_le hab]
      exact hmain_set
    have hadd : (∫ y in Set.Ioc a b, ((|main z y| + |rem z y|) / y))
        = (∫ y in Set.Ioc a b, (|main z y| / y)) + (∫ y in Set.Ioc a b, (|rem z y| / y)) := by
      have h1 : (∫ y in Set.Ioc a b, ((|main z y| + |rem z y|) / y))
          = ∫ y in Set.Ioc a b, ((fun y => |main z y| / y) + fun y => |rem z y| / y) y :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => by
          simp only [Pi.add_apply]; ring))
      rw [h1]
      have := MeasureTheory.integral_add hm_int hr_int
      simpa only [Pi.add_apply] using this
    rw [hA]
    calc (∫ y in Set.Ioc a b, |main z y + rem z y| / y)
        ≤ ∫ y in Set.Ioc a b, ((|main z y| + |rem z y|) / y) := hmono
      _ = (∫ y in Set.Ioc a b, (|main z y| / y)) + (∫ y in Set.Ioc a b, (|rem z y| / y)) := hadd
      _ = (∫ y in a..b, |main z y| / y) + (∫ y in a..b, |rem z y| / y) := by rw [hC, hD]
      _ ≤ M * (∫ y in a..b, (1 : ℝ) / y) + (∫ y in a..b, |rem z y| / y) := by linarith [hmain_le]
  have hAnnn : ∀ z ∈ Set.Icc p q, (0 : ℝ) ≤ ∫ y in a..b, |main z y + rem z y| / y := by
    intro z _
    exact intervalIntegral.integral_nonneg hab (fun y hy =>
      div_nonneg (abs_nonneg _) (le_of_lt (lt_of_lt_of_le ha hy.1)))
  have hBz : Measurable (fun z : ℝ => (∫ y in a..b, |rem z y| / y) / z) :=
    hparam.2.div measurable_id
  have hBcrude : ∀ z ∈ Set.Icc p q,
      (∫ y in a..b, |rem z y| / y) ≤ Cr * (∫ y in a..b, (1 : ℝ) / y) := by
    intro z hz
    rw [intervalIntegral.integral_of_le hab, ← intervalIntegral_const_div_eq Cr a b,
      intervalIntegral.integral_of_le hab]
    refine MeasureTheory.integral_mono_of_nonneg ?_ (integrable_const_div_Ioc Cr a b ha) ?_
    · exact eventually_restrict_Ioc (fun y hy =>
        div_nonneg (abs_nonneg _) (le_of_lt (lt_of_lt_of_le ha hy.1.le)))
    · refine eventually_restrict_Ioc (fun y hy => ?_)
      have hy0 : 0 < y := lt_of_lt_of_le ha hy.1.le
      have h2 : |rem z y| ≤ Cr := hremCr z hz y (Set.Ioc_subset_Icc_self hy)
      exact div_le_div_of_nonneg_right h2 hy0.le
  have hBnn : ∀ z ∈ Set.Icc p q, (0 : ℝ) ≤ ∫ y in a..b, |rem z y| / y := by
    intro z _
    exact intervalIntegral.integral_nonneg hab (fun y hy =>
      div_nonneg (abs_nonneg _) (le_of_lt (lt_of_lt_of_le ha hy.1)))
  set Cb : ℝ := Cr * (∫ y in a..b, (1 : ℝ) / y) + 1 with hCb
  have hCbnn : (0 : ℝ) < Cb := by rw [hCb]; linarith [mul_nonneg hCrnn hIyz]
  have hremint : Integrable (fun z : ℝ => (∫ y in a..b, |rem z y| / y) / z)
      (volume.restrict (Set.Ioc p q)) := by
    refine Integrable.mono' (integrable_const_div_Ioc Cb p q hp) hBz.aestronglyMeasurable ?_
    refine eventually_restrict_Ioc (fun z hz => ?_)
    have hz0 : 0 < z := lt_of_lt_of_le hp hz.1.le
    have h3 : (∫ y in a..b, |rem z y| / y) ≤ Cr * (∫ y in a..b, (1 : ℝ) / y) :=
      hBcrude z (Set.Ioc_subset_Icc_self hz)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hBnn z (Set.Ioc_subset_Icc_self hz)) hz0.le)]
    refine div_le_div_of_nonneg_right ?_ hz0.le
    rw [hCb]
    linarith
  have hconstint : Integrable (fun z : ℝ => (M * (∫ y in a..b, (1 : ℝ) / y)) / z)
      (volume.restrict (Set.Ioc p q)) :=
    integrable_const_div_Ioc (M * (∫ y in a..b, (1 : ℝ) / y)) p q hp
  -- the `z`-monotonicity
  have hstep1 : (∫ z in p..q, (∫ y in a..b, |main z y + rem z y| / y) / z)
      ≤ ∫ z in p..q,
          (M * (∫ y in a..b, (1 : ℝ) / y) + (∫ y in a..b, |rem z y| / y)) / z := by
    rw [intervalIntegral.integral_of_le hpq, intervalIntegral.integral_of_le hpq]
    have hmajz : Integrable
        (fun z : ℝ => (M * (∫ y in a..b, (1 : ℝ) / y) + (∫ y in a..b, |rem z y| / y)) / z)
        (volume.restrict (Set.Ioc p q)) := by
      refine Integrable.mono' (integrable_const_div_Ioc
        (M * (∫ y in a..b, (1 : ℝ) / y) + Cr * (∫ y in a..b, (1 : ℝ) / y) + 1) p q hp) ?_ ?_
      · exact ((Measurable.add measurable_const hparam.2).div measurable_id).aestronglyMeasurable.mono_measure Measure.restrict_le_self
      · refine eventually_restrict_Ioc (fun z hz => ?_)
        have hz0 : 0 < z := lt_of_lt_of_le hp hz.1.le
        have hc1 : (0 : ℝ) ≤ M * (∫ y in a..b, (1 : ℝ) / y) := mul_nonneg hMnn hIyz
        have hc2 : (0 : ℝ) ≤ (∫ y in a..b, |rem z y| / y) := hBnn z (Set.Ioc_subset_Icc_self hz)
        have h3 : (∫ y in a..b, |rem z y| / y) ≤ Cr * (∫ y in a..b, (1 : ℝ) / y) :=
          hBcrude z (Set.Ioc_subset_Icc_self hz)
        rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by linarith) hz0.le)]
        refine div_le_div_of_nonneg_right ?_ hz0.le
        linarith [mul_nonneg hCrnn hIyz]
    refine MeasureTheory.integral_mono_of_nonneg
      (eventually_restrict_Ioc (fun z hz =>
        div_nonneg (hAnnn z (Set.Ioc_subset_Icc_self hz))
          (le_of_lt (lt_of_lt_of_le hp hz.1.le))))
      hmajz
      (eventually_restrict_Ioc (fun z hz =>
        div_le_div_of_nonneg_right (hinner z (Set.Ioc_subset_Icc_self hz))
          (le_of_lt (lt_of_lt_of_le hp hz.1.le))))
  have hsplit : (∫ z in p..q,
          (M * (∫ y in a..b, (1 : ℝ) / y) + (∫ y in a..b, |rem z y| / y)) / z)
      = (∫ z in p..q, (M * (∫ y in a..b, (1 : ℝ) / y)) / z)
        + (∫ z in p..q, (∫ y in a..b, |rem z y| / y) / z) := by
    rw [intervalIntegral.integral_of_le hpq, intervalIntegral.integral_of_le hpq,
      intervalIntegral.integral_of_le hpq, ← MeasureTheory.integral_add hconstint hremint]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    simp only [Pi.add_apply]
    ring
  have hconstval : (∫ z in p..q, (M * (∫ y in a..b, (1 : ℝ) / y)) / z)
      = M * (∫ y in a..b, (1 : ℝ) / y) * (∫ z in p..q, (1 : ℝ) / z) := by
    rw [intervalIntegral_const_div_eq (M * (∫ y in a..b, (1 : ℝ) / y)) p q]
  calc (∫ z in p..q, (∫ y in a..b, |main z y + rem z y| / y) / z)
      ≤ ∫ z in p..q,
          (M * (∫ y in a..b, (1 : ℝ) / y) + (∫ y in a..b, |rem z y| / y)) / z := hstep1
    _ = (∫ z in p..q, (M * (∫ y in a..b, (1 : ℝ) / y)) / z)
        + (∫ z in p..q, (∫ y in a..b, |rem z y| / y) / z) := hsplit
    _ = M * (∫ y in a..b, (1 : ℝ) / y) * (∫ z in p..q, (1 : ℝ) / z)
        + (∫ z in p..q, (∫ y in a..b, |rem z y| / y) / z) := by rw [hconstval]
    _ ≤ M * (∫ y in a..b, (1 : ℝ) / y) * (∫ z in p..q, (1 : ℝ) / z) + R := by
        linarith [hremR]

/-- **The target follows from the two halves** (`Work.FIChain.s3MainPlus_pt_le` and
`Work.FIChain.s3RemPlus_zavg_le`), by the measure-theoretic assembly
`Work.FIChain.zavg_main_plus_rem_le`. -/
theorem S3plusC_zavg_le_of_children (h : Work.FIChain.Prop41Stmt)
    (hmain : ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ, 0 < B → ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      (x : ℝ) ^ ((1 : ℝ) / 4 + 1 / 64) + 2 < Work.FIChain.Yc x B / (Work.FIChain.Deltac x : ℝ) →
      ∀ lam : ℕ → ℝ, ∀ C_sieve : ℝ,
        Work.FIChain.SieveInput Submission.ASP.FIgtil (Work.FIChain.Deltac x) lam C_sieve →
      ∀ z : ℝ, z ∈ Set.Icc (Work.FIChain.zc x B) (Real.exp 1 * Work.FIChain.zc x B) →
      ∀ y : ℝ, y ∈ Set.Icc (Work.FIChain.Yc x B) (Real.exp 1 * Work.FIChain.Yc x B) →
        |Work.FIChain.s3MainPlus lam x z (Work.FIChain.sc x B * y) (Work.FIChain.sc x B * z)
          (⌊(Work.FIChain.zc x B) ^ (1 - Work.FIChain.etac)⌋₊)|
          ≤ C * Work.FIChain.AcountAtilC x * (Real.log (x : ℝ)) ^ (-(1 : ℤ)))
    (hrem : ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ, 0 < B → ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      (x : ℝ) ^ ((1 : ℝ) / 4 + 1 / 64) + 2 < Work.FIChain.Yc x B / (Work.FIChain.Deltac x : ℝ) →
      2 ≤ Work.FIChain.sc x B →
      ∀ lam : ℕ → ℝ, ∀ C_sieve : ℝ,
        Work.FIChain.SieveInput Submission.ASP.FIgtil (Work.FIChain.Deltac x) lam C_sieve →
      (∫ z in Work.FIChain.zc x B..(Real.exp 1 * Work.FIChain.zc x B),
          (∫ y in Work.FIChain.Yc x B..(Real.exp 1 * Work.FIChain.Yc x B),
            |Work.FIChain.s3RemPlus lam x z (Work.FIChain.sc x B * y) (Work.FIChain.sc x B * z)
              (⌊(Work.FIChain.zc x B) ^ (1 - Work.FIChain.etac)⌋₊)| / y) / z)
        ≤ C * Work.FIChain.AcountAtilC x * (Real.log (x : ℝ)) ^ (-(1 : ℤ))) :
    ∃ B K : ℝ, ∃ x₀ : ℕ, 0 < B ∧ 0 < K ∧ ∀ x : ℕ, x₀ ≤ x →
      (x : ℝ) ^ ((1 : ℝ) / 4 + 1 / 64) + 2 < Work.FIChain.Yc x B / (Work.FIChain.Deltac x : ℝ) →
      ∀ lam : ℕ → ℝ, ∀ C_sieve : ℝ,
        Work.FIChain.SieveInput Submission.ASP.FIgtil (Work.FIChain.Deltac x) lam C_sieve →
        (∫ z in Work.FIChain.zc x B..(Real.exp 1 * Work.FIChain.zc x B),
            (∫ y in Work.FIChain.Yc x B..(Real.exp 1 * Work.FIChain.Yc x B),
              |Work.FIChain.S3plusC Work.FIChain.atilc lam x z
                (Work.FIChain.sc x B * y) (Work.FIChain.sc x B * z)
                (((⌊(Work.FIChain.zc x B) ^ (1 - Work.FIChain.etac)⌋₊ : ℕ) : ℝ))| / y) / z)
          ≤ K * Work.FIChain.AcountAtilC x * (Real.log (x : ℝ)) ^ (-(1 : ℤ)) := by
  obtain ⟨C₁, hC₁pos, hmain⟩ := hmain
  obtain ⟨C₂, hC₂pos, hrem⟩ := hrem
  obtain ⟨xm, hm⟩ := hmain 1 one_pos
  obtain ⟨xr, hr⟩ := hrem 1 one_pos
  obtain ⟨xs, hs⟩ := Filter.eventually_atTop.mp (scale_factsC (1 : ℝ) one_pos)
  obtain ⟨xu, hu⟩ := Filter.eventually_atTop.mp
    (Work.FITop.FI_ev_log_rpow_le_nat (b := (1 : ℝ) + 2) (ε := (3 : ℝ) / 16) (C := 1 / 4)
      (by norm_num) (by norm_num))
  obtain ⟨xL, hL⟩ := Filter.eventually_atTop.mp (Work.FITop.FI_ev_log_ge_nat 32)
  obtain ⟨x2, hx2⟩ := Filter.eventually_atTop.mp (Filter.eventually_ge_atTop 256)
  refine ⟨1, C₁ + C₂, max (max xm xr) (max xs (max xu (max xL x2))) + 1,
    one_pos, by positivity, ?_⟩
  intro x hx hYc lam C_sieve hSie
  have hxm : xm ≤ x := by omega
  have hxr : xr ≤ x := by omega
  have hxs : xs ≤ x := by omega
  have hxux : xu ≤ x := by omega
  have hxLx : xL ≤ x := by omega
  have hx2x : x2 ≤ x := by omega
  have hx256 : 256 ≤ x := hx2 x hx2x
  have hx1 : (1 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 1 < x)
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hL32 : (32 : ℝ) ≤ Real.log (x : ℝ) := hL x hxLx
  have hLpos : 0 < Real.log (x : ℝ) := by linarith
  have hAnn : 0 ≤ AcountAtilC x := AcountAtilC_nonneg x
  obtain ⟨hYc256, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hs x hxs
  have hlam : ∀ ν : ℕ, |lam ν| ≤ 1 := fun ν => hSie.2.2.2.1 ν
  set Cm : ℕ := ⌊(Work.FIChain.zc x 1) ^ (1 - Work.FIChain.etac)⌋₊ with hCmdef
  set main : ℝ → ℝ → ℝ := fun z y =>
    Work.FIChain.s3MainPlus lam x z (Work.FIChain.sc x 1 * y) (Work.FIChain.sc x 1 * z) Cm
    with hmaindef
  set rem : ℝ → ℝ → ℝ := fun z y =>
    Work.FIChain.s3RemPlus lam x z (Work.FIChain.sc x 1 * y) (Work.FIChain.sc x 1 * z) Cm
    with hremdef
  have hYcf_pos : 0 < Work.FIChain.Yc x 1 := by
    rw [Work.FIChain.Yc]
    exact div_pos (Real.sqrt_pos.mpr hxpos)
      (mul_pos (pow_pos (by norm_num) _) (Real.rpow_pos_of_pos hLpos _))
  have hYcf_le : Work.FIChain.Yc x 1 ≤ Real.exp 1 * Work.FIChain.Yc x 1 :=
    le_mul_of_one_le_left hYcf_pos.le (Real.one_le_exp (by norm_num))
  have hZc256 : 256 ≤ Work.FIChain.Zc x 1 := hYc256
  have hzcf_pos : 0 < Work.FIChain.zc x 1 := by
    have h1 : (1 : ℝ) ≤ (Work.FIChain.Zc x 1 : ℝ) := by
      have h2 : (256 : ℝ) ≤ (Work.FIChain.Zc x 1 : ℝ) := by exact_mod_cast hZc256
      linarith
    have h3 : (0 : ℝ) < (Work.FIChain.Zc x 1 : ℝ) := by linarith
    simpa [Work.FIChain.zc] using h3
  have hzc256 : (256 : ℝ) ≤ Work.FIChain.zc x 1 := by
    have h2 : (256 : ℝ) ≤ (Work.FIChain.Zc x 1 : ℝ) := by exact_mod_cast hZc256
    simpa [Work.FIChain.zc] using h2
  have hzcf_le : Work.FIChain.zc x 1 ≤ Real.exp 1 * Work.FIChain.zc x 1 :=
    le_mul_of_one_le_left hzcf_pos.le (Real.one_le_exp (by norm_num))
  have hsc1 : (1 : ℝ) ≤ Work.FIChain.sc x 1 := by
    rw [Work.FIChain.sc]
    exact one_le_pow₀ (by norm_num)
  have hexp_eq : (1 : ℝ) / 4 - 2 * Work.FIChain.etac = (3 : ℝ) / 16 := by
    norm_num [Work.FIChain.etac]
  have hsc2 : (2 : ℝ) ≤ Work.FIChain.sc x 1 := by
    have hu1 : (2 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * Work.FIChain.etac)
        / (2 * (Real.log (x : ℝ)) ^ ((1 : ℝ) + 2)) := by
      have hhu := hu x hxux
      rw [hexp_eq, le_div_iff₀ (by positivity)]
      linarith
    rw [Work.FIChain.sc, Work.FIChain.Jc]
    have hJ1 : (1 : ℕ) ≤ ⌈Real.log ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * Work.FIChain.etac)
        / (2 * (Real.log (x : ℝ)) ^ ((1 : ℝ) + 2))) / Real.log 2⌉₊ := by
      have h1 : (1 : ℝ) ≤ Real.log ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * Work.FIChain.etac)
          / (2 * (Real.log (x : ℝ)) ^ ((1 : ℝ) + 2))) / Real.log 2 := by
        rw [le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
        have h3 : Real.log 2 ≤ Real.log ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * Work.FIChain.etac)
            / (2 * (Real.log (x : ℝ)) ^ ((1 : ℝ) + 2))) :=
          Real.log_le_log (by norm_num) hu1
        linarith
      have h4 : (1 : ℝ) ≤ ((⌈Real.log ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * Work.FIChain.etac)
          / (2 * (Real.log (x : ℝ)) ^ ((1 : ℝ) + 2))) / Real.log 2⌉₊ : ℕ) : ℝ) :=
        le_trans h1 (Nat.le_ceil _)
      exact_mod_cast h4
    calc (2 : ℝ) = 2 ^ (1 : ℕ) := by norm_num
      _ ≤ 2 ^ (⌈Real.log ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * Work.FIChain.etac)
          / (2 * (Real.log (x : ℝ)) ^ ((1 : ℝ) + 2))) / Real.log 2⌉₊) :=
          pow_le_pow_right₀ (by norm_num) hJ1
  have hCm1 : 1 ≤ Cm := by
    rw [hCmdef]
    refine Nat.le_floor ?_
    have h1 : (1 : ℝ) ≤ Work.FIChain.zc x 1 := by linarith
    have h2 : (0 : ℝ) < 1 - Work.FIChain.etac := by norm_num [Work.FIChain.etac]
    have h3 : (1 : ℝ) ^ (1 - Work.FIChain.etac)
        ≤ (Work.FIChain.zc x 1) ^ (1 - Work.FIChain.etac) :=
      Real.rpow_le_rpow zero_le_one h1 h2.le
    simpa using h3
  have hCm_lt : (Cm : ℝ) < Work.FIChain.zc x 1 := by
    have h1 : (Cm : ℝ) ≤ (Work.FIChain.zc x 1) ^ (1 - Work.FIChain.etac) := by
      rw [hCmdef]
      exact Nat.floor_le (Real.rpow_nonneg hzcf_pos.le _)
    have h2 : (Work.FIChain.zc x 1) ^ (1 - Work.FIChain.etac) < Work.FIChain.zc x 1 :=
      Real.rpow_lt_self_of_one_lt (by linarith) (by norm_num [Work.FIChain.etac])
    linarith
  have hmainM : ∀ z ∈ Set.Icc (Work.FIChain.zc x 1) (Real.exp 1 * Work.FIChain.zc x 1),
      ∀ y ∈ Set.Icc (Work.FIChain.Yc x 1) (Real.exp 1 * Work.FIChain.Yc x 1),
      |main z y| ≤ C₁ * AcountAtilC x * (Real.log (x : ℝ)) ^ (-(1 : ℤ)) := by
    intro z hz y hy
    rw [hmaindef]
    exact hm x hxm hYc lam C_sieve hSie z hz y hy
  have hremCr : ∀ z ∈ Set.Icc (Work.FIChain.zc x 1) (Real.exp 1 * Work.FIChain.zc x 1),
      ∀ y ∈ Set.Icc (Work.FIChain.Yc x 1) (Real.exp 1 * Work.FIChain.Yc x 1),
      |rem z y| ≤ 4 * AcountAtilC x * (((x : ℝ) ^ 3) + 1) * (((x : ℝ) / (Cm : ℝ)) + 1) + 1 := by
    intro z hz y _
    rw [hremdef]
    have hsz0 : (0 : ℝ) ≤ Work.FIChain.sc x 1 * z :=
      mul_nonneg (by linarith) (by linarith [hz.1, hzc256])
    have hh := abs_s3RemPlus_le_crude lam x z (Work.FIChain.sc x 1 * y)
      (Work.FIChain.sc x 1 * z) Cm hlam hsz0
    linarith
  have hremR : (∫ z in Work.FIChain.zc x 1..(Real.exp 1 * Work.FIChain.zc x 1),
      (∫ y in Work.FIChain.Yc x 1..(Real.exp 1 * Work.FIChain.Yc x 1), |rem z y| / y) / z)
      ≤ C₂ * AcountAtilC x * (Real.log (x : ℝ)) ^ (-(1 : ℤ)) := by
    rw [hremdef, hCmdef]
    exact hr x hxr hYc hsc2 lam C_sieve hSie
  have hmeas : Measurable (fun t : ℝ × ℝ => |main t.1 t.2|) ∧
      Measurable (fun t : ℝ × ℝ => |rem t.1 t.2|) := by
    rw [hmaindef, hremdef, hCmdef]
    exact measurable_s3halves_joint x 1 lam ⌊(Work.FIChain.zc x 1) ^ (1 - Work.FIChain.etac)⌋₊
  have hIy : (∫ y in Work.FIChain.Yc x 1..(Real.exp 1 * Work.FIChain.Yc x 1), (1 : ℝ) / y) = 1 :=
    intervalIntegral_const_div_exp 1 (Work.FIChain.Yc x 1) hYcf_pos
  have hIz : (∫ z in Work.FIChain.zc x 1..(Real.exp 1 * Work.FIChain.zc x 1), (1 : ℝ) / z) = 1 :=
    intervalIntegral_const_div_exp 1 (Work.FIChain.zc x 1) hzcf_pos
  have hpt : ∀ z ∈ Set.Icc (Work.FIChain.zc x 1) (Real.exp 1 * Work.FIChain.zc x 1),
      ∀ y, |Work.FIChain.S3plusC Work.FIChain.atilc lam x z (Work.FIChain.sc x 1 * y)
          (Work.FIChain.sc x 1 * z) ((Cm : ℕ) : ℝ)| = |main z y + rem z y| := by
    intro z hz y
    rw [hmaindef, hremdef]
    have hz1 : (1 : ℝ) ≤ z := by linarith [hz.1, hzc256]
    have hsz1 : (1 : ℝ) ≤ Work.FIChain.sc x 1 * z := by
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ Work.FIChain.sc x 1 * z := mul_le_mul hsc1 hz1 (by norm_num) (by linarith)
    have hzsz : z ≤ Work.FIChain.sc x 1 * z := le_mul_of_one_le_left (by linarith) hsc1
    have hT : (1 : ℝ) ≤ Work.FIChain.sc x 1 * z / (Cm : ℝ) := by
      rw [le_div_iff₀ (by positivity), one_mul]
      calc (Cm : ℝ) ≤ Work.FIChain.zc x 1 := le_of_lt hCm_lt
        _ ≤ z := hz.1
        _ ≤ Work.FIChain.sc x 1 * z := hzsz
    rw [S3plusC_eq_main_add_rem lam x z (Work.FIChain.sc x 1 * y) (Work.FIChain.sc x 1 * z) Cm
      hCm1 (by linarith [hz.1, hzc256]) (lt_of_lt_of_le hCm_lt hz.1) hsz1 hzsz hT]
  have hkey := zavg_main_plus_rem_le (main := main) (rem := rem)
    (p := Work.FIChain.zc x 1) (q := Real.exp 1 * Work.FIChain.zc x 1)
    (a := Work.FIChain.Yc x 1) (b := Real.exp 1 * Work.FIChain.Yc x 1)
    (M := C₁ * AcountAtilC x * (Real.log (x : ℝ)) ^ (-(1 : ℤ)))
    (R := C₂ * AcountAtilC x * (Real.log (x : ℝ)) ^ (-(1 : ℤ)))
    (Cr := 4 * AcountAtilC x * (((x : ℝ) ^ 3) + 1) * (((x : ℝ) / (Cm : ℝ)) + 1) + 1)
    hzcf_le (by positivity) (by positivity) hmainM hremCr hremR hmeas
    hYcf_pos hYcf_le hzcf_pos
  have hgoal_eq : (∫ z in Work.FIChain.zc x 1..(Real.exp 1 * Work.FIChain.zc x 1),
        (∫ y in Work.FIChain.Yc x 1..(Real.exp 1 * Work.FIChain.Yc x 1),
          |Work.FIChain.S3plusC Work.FIChain.atilc lam x z (Work.FIChain.sc x 1 * y)
            (Work.FIChain.sc x 1 * z) ((Cm : ℕ) : ℝ)| / y) / z)
      = (∫ z in Work.FIChain.zc x 1..(Real.exp 1 * Work.FIChain.zc x 1),
        (∫ y in Work.FIChain.Yc x 1..(Real.exp 1 * Work.FIChain.Yc x 1),
          |main z y + rem z y| / y) / z) := by
    refine intervalIntegral.integral_congr (fun z hz => ?_)
    congr 1
    refine intervalIntegral.integral_congr (fun y _ => ?_)
    have hzIcc : z ∈ Set.Icc (Work.FIChain.zc x 1) (Real.exp 1 * Work.FIChain.zc x 1) := by
      have h := hz
      rwa [Set.uIcc_of_le hzcf_le] at h
    rw [hpt z hzIcc y]
  rw [hgoal_eq]
  refine le_trans hkey ?_
  rw [hIy, hIz]
  have hfin : C₁ * AcountAtilC x * (Real.log (x : ℝ)) ^ (-(1 : ℤ)) * 1 * 1
      + C₂ * AcountAtilC x * (Real.log (x : ℝ)) ^ (-(1 : ℤ))
      = (C₁ + C₂) * AcountAtilC x * (Real.log (x : ℝ)) ^ (-(1 : ℤ)) := by ring
  linarith [hfin]
end

end Work.FIChain
