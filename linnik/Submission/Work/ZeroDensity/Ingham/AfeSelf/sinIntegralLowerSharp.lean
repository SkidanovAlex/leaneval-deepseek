import Mathlib
import Submission.Work.ZeroDensity.Ingham.cosMulCpowIntegral
import Submission.Work.ZeroDensity.Ingham.sinMulCpowIntegral

/-!
# A sharp bound for `∫₀ᴬ sin v · v^{-s-1} dv` when `A < |Im s|`

This file proves

`‖∫₀ᴬ sin v · v^{-s-1} dv‖ ≤ 8 A^{-Re s}/(|Im s| - A)`  for `0 < Re s`, `1 ≤ A`, `A < |Im s|`.

The mechanism is the *Kummer recursion*.  Put

`P_m = ∫₀ᴬ cos v · v^{m-s} dv`,  `Q_m = ∫₀ᴬ sin v · v^{m-s} dv`,  `T_m = ‖P_m‖ + ‖Q_m‖`.

One integration by parts gives `(m+1-s) P_m = cos A · A^{m+1-s} + Q_{m+1}` and
`(m+1-s) Q_m = sin A · A^{m+1-s} - P_{m+1}` (the boundary term at `0` vanishes because
`Re (m+1-s) > 0`).  Unwinding the chain `T_0`, successive *deep* terms are divided by
`∏_{j≤m}(j-s)` (each factor has modulus `≥ |Im s|`), while the boundary contributions are
`≍ A^{m+1-Re s}/|Im s|^m = A^{-Re s}·(A/|Im s|)^m`.  Since `A/|Im s| < 1` the geometric series
sums to `≍ A^{-Re s}|Im s|/(|Im s| - A)`: this is where the denominator `|Im s| - A` comes from.

The target integral `∫₀ᴬ sin v·v^{-s-1}dv` is `Q_{-1}`; one further integration by parts
(`s Q_{-1} = P_0 - sin A·A^{-s}`, whose boundary term at `0` vanishes because `Re s < 1`)
relates it to `P_0`.  For `Re s ≥ 1` the Bochner integral vanishes because the integrand is not
integrable at `0`.
-/

namespace Work.ZeroDensity.Ingham.AfeSelf

open MeasureTheory Set Filter

open scoped Topology

noncomputable section

set_option maxHeartbeats 1600000

/-! ## Definitions -/

/-- `∏_{j<k} ((j+1) - s)`, the product of the recursion denominators. -/
def sdd (s : ℂ) (k : ℕ) : ℂ :=
  Finset.prod (Finset.range k) (fun j => (((j + 1 : ℕ) : ℂ) - s))

/-- `∫₀ᴬ cos v · v^{m-s} dv`. -/
def sPP (s : ℂ) (A : ℝ) (m : ℕ) : ℂ :=
  ∫ v in Set.Ioc 0 A, ((Real.cos v : ℝ) : ℂ) * (v : ℂ) ^ ((m : ℂ) - s)

/-- `∫₀ᴬ sin v · v^{m-s} dv`. -/
def sQQ (s : ℂ) (A : ℝ) (m : ℕ) : ℂ :=
  ∫ v in Set.Ioc 0 A, ((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ ((m : ℂ) - s)

/-- `‖P_m‖ + ‖Q_m‖`. -/
def sTT (s : ℂ) (A : ℝ) (m : ℕ) : ℝ := ‖sPP s A m‖ + ‖sQQ s A m‖

/-- The monotone family driving the recursion. -/
def sKK (s : ℂ) (A : ℝ) (M : ℕ) : ℝ :=
  Finset.sum (Finset.range M) (fun k => 2 * A ^ (-s.re) * (A / |s.im|) ^ (k + 1))
    + sTT s A M / ‖sdd s M‖

/-! ## Elementary facts -/

lemma sdd_zero (s : ℂ) : sdd s 0 = 1 := by simp [sdd]

lemma sdd_succ (s : ℂ) (k : ℕ) :
    sdd s (k + 1) = sdd s k * (((k + 1 : ℕ) : ℂ) - s) := by
  simp [sdd, Finset.prod_range_succ]

lemma norm_sdd_succ (s : ℂ) (k : ℕ) :
    ‖sdd s (k + 1)‖ = ‖sdd s k‖ * ‖(((k + 1 : ℕ) : ℂ) - s)‖ := by
  rw [sdd_succ, norm_mul]

lemma complex_norm_ofReal (x : ℝ) : ‖((x : ℝ) : ℂ)‖ = |x| := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)]
  rw [Complex.sq_norm, Complex.normSq_ofReal, sq_abs]
  ring

lemma factor_ne_zero {s : ℂ} (hs1 : s.re < 1) {j : ℕ} (hj : 1 ≤ j) :
    (((j : ℕ) : ℂ) - s) ≠ 0 := by
  intro h
  have hre : ((j : ℝ)) - s.re = 0 := by
    have := congrArg Complex.re h
    simpa [Complex.sub_re] using this
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  linarith

lemma sdd_ne_zero {s : ℂ} (hs1 : s.re < 1) (k : ℕ) : sdd s k ≠ 0 := by
  rw [sdd, Finset.prod_ne_zero_iff]
  intro j hj
  rw [Finset.mem_range] at hj
  exact factor_ne_zero hs1 (by omega)

lemma norm_sdd_pos {s : ℂ} (hs1 : s.re < 1) (k : ℕ) : 0 < ‖sdd s k‖ :=
  norm_pos_iff.mpr (sdd_ne_zero hs1 k)

lemma norm_factor_ge (s : ℂ) (j : ℕ) :
    |s.im| ≤ ‖(((j : ℕ) : ℂ) - s)‖ := by
  have h := Complex.abs_im_le_norm (((j : ℕ) : ℂ) - s)
  simpa [Complex.sub_im] using h

lemma norm_sdd_ge (s : ℂ) (k : ℕ) : |s.im| ^ k ≤ ‖sdd s k‖ := by
  have h1 : ‖sdd s k‖
      = Finset.prod (Finset.range k) (fun j => ‖(((j + 1 : ℕ) : ℂ) - s)‖) := by
    rw [sdd, norm_prod]
  rw [h1]
  have h2 : |s.im| ^ k = Finset.prod (Finset.range k) (fun _j => |s.im|) := by simp
  rw [h2]
  exact Finset.prod_le_prod₀ (fun j _ => abs_nonneg _) (fun j _ => norm_factor_ge s (j + 1))

lemma geom_shift_le {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ < 1) (M : ℕ) :
    Finset.sum (Finset.range M) (fun k => ρ ^ (k + 1)) ≤ ρ / (1 - ρ) := by
  have hmul : Finset.sum (Finset.range M) (fun k => ρ ^ (k + 1))
      = ρ * Finset.sum (Finset.range M) (fun k => ρ ^ k) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by rw [pow_succ]; ring)
  rw [hmul]
  have hg : Finset.sum (Finset.range M) (fun k => ρ ^ k) ≤ 1 / (1 - ρ) := by
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 1 - ρ)]
    have hm := geom_sum_mul_neg ρ M
    have hp : (0 : ℝ) ≤ ρ ^ M := pow_nonneg h0.le M
    linarith [hm]
  calc ρ * Finset.sum (Finset.range M) (fun k => ρ ^ k) ≤ ρ * (1 / (1 - ρ)) :=
        mul_le_mul_of_nonneg_left hg h0.le
    _ = ρ / (1 - ρ) := by ring

/-! ## The integral of an `rpow` on `(0,A]` and a norm bound -/

lemma integral_rpow_Ioc {A r : ℝ} (hA : 0 ≤ A) (hr : -1 < r) :
    ∫ v in Set.Ioc 0 A, v ^ r = A ^ (r + 1) / (r + 1) := by
  rw [← intervalIntegral.integral_of_le hA, integral_rpow (Or.inl hr),
    Real.zero_rpow (by linarith : r + 1 ≠ 0), sub_zero]

lemma integral_norm_le_rpow {A : ℝ} (hA : 0 ≤ A) {f : ℝ → ℂ} {r : ℝ} (hr : -1 < r)
    (hcont : ContinuousOn f (Set.Ioc 0 A))
    (hf : ∀ v ∈ Set.Ioc 0 A, ‖f v‖ ≤ v ^ r) :
    ∫ v in Set.Ioc 0 A, ‖f v‖ ≤ A ^ (r + 1) / (r + 1) := by
  have hintg : IntegrableOn (fun v : ℝ => v ^ r) (Set.Ioc 0 A) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hA]
    exact intervalIntegral.intervalIntegrable_rpow' hr
  have hintg' : Integrable (fun v : ℝ => v ^ r) (volume.restrict (Set.Ioc 0 A)) := hintg
  have hmeas : AEStronglyMeasurable f (volume.restrict (Set.Ioc 0 A)) :=
    hcont.aestronglyMeasurable measurableSet_Ioc
  have hbound : ∀ᵐ v ∂(volume.restrict (Set.Ioc 0 A)), ‖f v‖ ≤ v ^ r := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with v hv
    exact hf v hv
  have hintf : Integrable f (volume.restrict (Set.Ioc 0 A)) :=
    Integrable.mono' hintg' hmeas hbound
  have hintfn : Integrable (fun v => ‖f v‖) (volume.restrict (Set.Ioc 0 A)) := hintf.norm
  calc ∫ v in Set.Ioc 0 A, ‖f v‖ ≤ ∫ v in Set.Ioc 0 A, v ^ r :=
        integral_mono_ae hintfn hintg' hbound
    _ = A ^ (r + 1) / (r + 1) := integral_rpow_Ioc hA hr

/-! ## Bounds on the pieces `P_m`, `Q_m` -/

lemma sPP_le {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) {A : ℝ} (hA : 0 < A) (m : ℕ) :
    ‖sPP s A m‖ ≤ A ^ ((m : ℝ) + 1 - s.re) / ((m : ℝ) + 1 - s.re) := by
  have hr : (-1 : ℝ) < (m : ℝ) - s.re := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hcont : ContinuousOn
      (fun v : ℝ => ((Real.cos v : ℝ) : ℂ) * (v : ℂ) ^ ((m : ℂ) - s)) (Set.Ioc 0 A) := by
    apply ContinuousOn.mul ((Complex.continuous_ofReal.comp Real.continuous_cos).continuousOn)
    intro v hv
    exact (Complex.continuousAt_ofReal_cpow_const v ((m : ℂ) - s) (Or.inr (by
      have h0 : (0 : ℝ) < v := hv.1
      exact_mod_cast (ne_of_gt h0)))).continuousWithinAt
  have hbound : ∀ v ∈ Set.Ioc 0 A,
      ‖((Real.cos v : ℝ) : ℂ) * (v : ℂ) ^ ((m : ℂ) - s)‖ ≤ v ^ ((m : ℝ) - s.re) := by
    intro v hv
    rw [norm_mul, complex_norm_ofReal, Complex.norm_cpow_eq_rpow_re_of_pos hv.1]
    have hre : (((m : ℂ) - s)).re = (m : ℝ) - s.re := by
      simp only [Complex.sub_re, Complex.natCast_re]
    rw [hre]
    have hc : |Real.cos v| ≤ 1 := Real.abs_cos_le_one v
    have hv0 : (0 : ℝ) ≤ v ^ ((m : ℝ) - s.re) := Real.rpow_nonneg (le_of_lt hv.1) _
    nlinarith
  calc ‖sPP s A m‖
      ≤ ∫ v in Set.Ioc 0 A, ‖((Real.cos v : ℝ) : ℂ) * (v : ℂ) ^ ((m : ℂ) - s)‖ := by
        rw [sPP]; exact MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ A ^ ((m : ℝ) + 1 - s.re) / ((m : ℝ) + 1 - s.re) := by
        have h := integral_norm_le_rpow (A := A) hA.le (r := (m : ℝ) - s.re) hr hcont hbound
        have he : (m : ℝ) - s.re + 1 = (m : ℝ) + 1 - s.re := by ring
        rwa [he] at h

lemma sQQ_le {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) {A : ℝ} (hA : 0 < A) (m : ℕ) :
    ‖sQQ s A m‖ ≤ A ^ ((m : ℝ) + 1 - s.re) / ((m : ℝ) + 1 - s.re) := by
  have hr : (-1 : ℝ) < (m : ℝ) - s.re := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hcont : ContinuousOn
      (fun v : ℝ => ((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ ((m : ℂ) - s)) (Set.Ioc 0 A) := by
    apply ContinuousOn.mul ((Complex.continuous_ofReal.comp Real.continuous_sin).continuousOn)
    intro v hv
    exact (Complex.continuousAt_ofReal_cpow_const v ((m : ℂ) - s) (Or.inr (by
      have h0 : (0 : ℝ) < v := hv.1
      exact_mod_cast (ne_of_gt h0)))).continuousWithinAt
  have hbound : ∀ v ∈ Set.Ioc 0 A,
      ‖((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ ((m : ℂ) - s)‖ ≤ v ^ ((m : ℝ) - s.re) := by
    intro v hv
    rw [norm_mul, complex_norm_ofReal, Complex.norm_cpow_eq_rpow_re_of_pos hv.1]
    have hre : (((m : ℂ) - s)).re = (m : ℝ) - s.re := by
      simp only [Complex.sub_re, Complex.natCast_re]
    rw [hre]
    have hc : |Real.sin v| ≤ 1 := Real.abs_sin_le_one v
    have hv0 : (0 : ℝ) ≤ v ^ ((m : ℝ) - s.re) := Real.rpow_nonneg (le_of_lt hv.1) _
    nlinarith
  calc ‖sQQ s A m‖
      ≤ ∫ v in Set.Ioc 0 A, ‖((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ ((m : ℂ) - s)‖ := by
        rw [sQQ]; exact MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ A ^ ((m : ℝ) + 1 - s.re) / ((m : ℝ) + 1 - s.re) := by
        have h := integral_norm_le_rpow (A := A) hA.le (r := (m : ℝ) - s.re) hr hcont hbound
        have he : (m : ℝ) - s.re + 1 = (m : ℝ) + 1 - s.re := by ring
        rwa [he] at h

lemma sTT_le {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) {A : ℝ} (hA : 0 < A) (m : ℕ) :
    sTT s A m ≤ 2 * (A ^ ((m : ℝ) + 1 - s.re) / ((m : ℝ) + 1 - s.re)) := by
  have h1 := sPP_le (s := s) hs0 hs1 hA m
  have h2 := sQQ_le (s := s) hs0 hs1 hA m
  have hsum : ‖sPP s A m‖ + ‖sQQ s A m‖
      ≤ A ^ ((m : ℝ) + 1 - s.re) / ((m : ℝ) + 1 - s.re)
        + A ^ ((m : ℝ) + 1 - s.re) / ((m : ℝ) + 1 - s.re) := add_le_add h1 h2
  have heq : A ^ ((m : ℝ) + 1 - s.re) / ((m : ℝ) + 1 - s.re)
        + A ^ ((m : ℝ) + 1 - s.re) / ((m : ℝ) + 1 - s.re)
      = 2 * (A ^ ((m : ℝ) + 1 - s.re) / ((m : ℝ) + 1 - s.re)) := by ring
  simp only [sTT]
  linarith [hsum, heq.le, heq.ge]

/-! ## The recurrences -/

lemma recPP {s : ℂ} (hs1 : s.re < 1) {A : ℝ} (hA : 0 < A) (m : ℕ) :
    (((m + 1 : ℕ) : ℂ) - s) * sPP s A m =
      ((Real.cos A : ℝ) : ℂ) * (A : ℂ) ^ (((m + 1 : ℕ) : ℂ) - s) + sQQ s A (m + 1) := by
  have hc : 0 < ((((m + 1 : ℕ) : ℂ) - s)).re := by
    have h : ((((m + 1 : ℕ) : ℂ) - s)).re = (m : ℝ) + 1 - s.re := by
      rw [Complex.sub_re, Complex.natCast_re]; push_cast; ring
    rw [h]
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have h := cosMulCpowIntegral (c := (((m + 1 : ℕ) : ℂ) - s)) hc hA
  rw [show ((((m + 1 : ℕ) : ℂ) - s) - 1) = ((m : ℂ) - s) by push_cast; ring] at h
  simpa only [sPP, sQQ] using h

lemma recQQ {s : ℂ} (hs1 : s.re < 1) {A : ℝ} (hA : 0 < A) (m : ℕ) :
    (((m + 1 : ℕ) : ℂ) - s) * sQQ s A m =
      ((Real.sin A : ℝ) : ℂ) * (A : ℂ) ^ (((m + 1 : ℕ) : ℂ) - s) - sPP s A (m + 1) := by
  have hc : 0 < ((((m + 1 : ℕ) : ℂ) - s)).re := by
    have h : ((((m + 1 : ℕ) : ℂ) - s)).re = (m : ℝ) + 1 - s.re := by
      rw [Complex.sub_re, Complex.natCast_re]; push_cast; ring
    rw [h]
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have h := sinMulCpowIntegral (c := (((m + 1 : ℕ) : ℂ) - s)) hc hA
  rw [show ((((m + 1 : ℕ) : ℂ) - s) - 1) = ((m : ℂ) - s) by push_cast; ring] at h
  simpa only [sPP, sQQ] using h

lemma T_rec {s : ℂ} (hs1 : s.re < 1) {A : ℝ} (hA : 0 < A) (m : ℕ) :
    sTT s A m ≤ 2 * A ^ ((m : ℝ) + 1 - s.re) / ‖(((m + 1 : ℕ) : ℂ) - s)‖
      + sTT s A (m + 1) / ‖(((m + 1 : ℕ) : ℂ) - s)‖ := by
  have hδ : (0 : ℝ) < ‖(((m + 1 : ℕ) : ℂ) - s)‖ :=
    norm_pos_iff.mpr (factor_ne_zero hs1 (by omega))
  have hre : ((((m + 1 : ℕ) : ℂ)) - s).re = (m : ℝ) + 1 - s.re := by
    rw [Complex.sub_re, Complex.natCast_re]; push_cast; ring
  have hcb : ‖((Real.cos A : ℝ) : ℂ) * (A : ℂ) ^ (((m + 1 : ℕ) : ℂ) - s)‖
      ≤ A ^ ((m : ℝ) + 1 - s.re) := by
    rw [norm_mul, complex_norm_ofReal, Complex.norm_cpow_eq_rpow_re_of_pos hA, hre]
    have hc : |Real.cos A| ≤ 1 := Real.abs_cos_le_one A
    have hv0 : (0 : ℝ) ≤ A ^ ((m : ℝ) + 1 - s.re) := Real.rpow_nonneg hA.le _
    nlinarith
  have hsb : ‖((Real.sin A : ℝ) : ℂ) * (A : ℂ) ^ (((m + 1 : ℕ) : ℂ) - s)‖
      ≤ A ^ ((m : ℝ) + 1 - s.re) := by
    rw [norm_mul, complex_norm_ofReal, Complex.norm_cpow_eq_rpow_re_of_pos hA, hre]
    have hc : |Real.sin A| ≤ 1 := Real.abs_sin_le_one A
    have hv0 : (0 : ℝ) ≤ A ^ ((m : ℝ) + 1 - s.re) := Real.rpow_nonneg hA.le _
    nlinarith
  have n1 : ‖sPP s A m‖ * ‖(((m + 1 : ℕ) : ℂ) - s)‖
      ≤ A ^ ((m : ℝ) + 1 - s.re) + ‖sQQ s A (m + 1)‖ := by
    have h := congrArg norm (recPP (s := s) hs1 hA m)
    rw [norm_mul] at h
    calc ‖sPP s A m‖ * ‖(((m + 1 : ℕ) : ℂ) - s)‖
        = ‖(((m + 1 : ℕ) : ℂ) - s)‖ * ‖sPP s A m‖ := by ring
      _ = ‖((Real.cos A : ℝ) : ℂ) * (A : ℂ) ^ (((m + 1 : ℕ) : ℂ) - s) + sQQ s A (m + 1)‖ := h
      _ ≤ ‖((Real.cos A : ℝ) : ℂ) * (A : ℂ) ^ (((m + 1 : ℕ) : ℂ) - s)‖ + ‖sQQ s A (m + 1)‖ :=
          norm_add_le _ _
      _ ≤ A ^ ((m : ℝ) + 1 - s.re) + ‖sQQ s A (m + 1)‖ := add_le_add hcb le_rfl
  have n2 : ‖sQQ s A m‖ * ‖(((m + 1 : ℕ) : ℂ) - s)‖
      ≤ A ^ ((m : ℝ) + 1 - s.re) + ‖sPP s A (m + 1)‖ := by
    have h := congrArg norm (recQQ (s := s) hs1 hA m)
    rw [norm_mul] at h
    calc ‖sQQ s A m‖ * ‖(((m + 1 : ℕ) : ℂ) - s)‖
        = ‖(((m + 1 : ℕ) : ℂ) - s)‖ * ‖sQQ s A m‖ := by ring
      _ = ‖((Real.sin A : ℝ) : ℂ) * (A : ℂ) ^ (((m + 1 : ℕ) : ℂ) - s) - sPP s A (m + 1)‖ := h
      _ ≤ ‖((Real.sin A : ℝ) : ℂ) * (A : ℂ) ^ (((m + 1 : ℕ) : ℂ) - s)‖ + ‖sPP s A (m + 1)‖ :=
          norm_sub_le _ _
      _ ≤ A ^ ((m : ℝ) + 1 - s.re) + ‖sPP s A (m + 1)‖ := add_le_add hsb le_rfl
  have key : sTT s A m * ‖(((m + 1 : ℕ) : ℂ) - s)‖
      ≤ 2 * A ^ ((m : ℝ) + 1 - s.re) + sTT s A (m + 1) := by
    simp only [sTT]
    linarith
  have hcomb : 2 * A ^ ((m : ℝ) + 1 - s.re) / ‖(((m + 1 : ℕ) : ℂ) - s)‖
        + sTT s A (m + 1) / ‖(((m + 1 : ℕ) : ℂ) - s)‖
      = (2 * A ^ ((m : ℝ) + 1 - s.re) + sTT s A (m + 1)) / ‖(((m + 1 : ℕ) : ℂ) - s)‖ := by
    ring
  rw [hcomb, le_div_iff₀ hδ]
  linarith [key]

/-! ## Monotonicity of the family `sKK` -/

lemma rpow_shift_div {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (n : ℕ) (x : ℝ) :
    A ^ ((n : ℝ) - x) / B ^ n = A ^ (-x) * (A / B) ^ n := by
  have h1 : A ^ ((n : ℝ) - x) = A ^ (n : ℝ) * A ^ (-x) := by
    rw [← Real.rpow_add hA]; ring_nf
  rw [h1, Real.rpow_natCast, div_pow]
  have hBne : B ≠ 0 := ne_of_gt hB
  field_simp

lemma sKK_mono {s : ℂ} (hs1 : s.re < 1) {A : ℝ} (hA : 0 < A) (ht : 0 < |s.im|) (M : ℕ) :
    sKK s A M ≤ sKK s A (M + 1) := by
  have hrec := T_rec (s := s) hs1 hA M
  have hδ : (0 : ℝ) < ‖(((M + 1 : ℕ) : ℂ) - s)‖ :=
    norm_pos_iff.mpr (factor_ne_zero hs1 (by omega))
  have hD : 0 < ‖sdd s M‖ := norm_sdd_pos hs1 M
  have hD1 : ‖sdd s (M + 1)‖ = ‖sdd s M‖ * ‖(((M + 1 : ℕ) : ℂ) - s)‖ := norm_sdd_succ s M
  have hDne : ‖sdd s M‖ ≠ 0 := ne_of_gt hD
  have hδne : ‖(((M + 1 : ℕ) : ℂ) - s)‖ ≠ 0 := ne_of_gt hδ
  have step1 : sTT s A M / ‖sdd s M‖
      ≤ (2 * A ^ ((M : ℝ) + 1 - s.re) + sTT s A (M + 1)) / ‖sdd s (M + 1)‖ := by
    rw [div_le_iff₀ hD]
    have heq : ((2 * A ^ ((M : ℝ) + 1 - s.re) + sTT s A (M + 1)) / ‖sdd s (M + 1)‖)
        * ‖sdd s M‖
        = 2 * A ^ ((M : ℝ) + 1 - s.re) / ‖(((M + 1 : ℕ) : ℂ) - s)‖
          + sTT s A (M + 1) / ‖(((M + 1 : ℕ) : ℂ) - s)‖ := by
      rw [hD1]; field_simp
    rw [heq]
    exact hrec
  have hEq : A ^ ((M : ℝ) + 1 - s.re) / |s.im| ^ (M + 1)
      = A ^ (-s.re) * (A / |s.im|) ^ (M + 1) := by
    have h := rpow_shift_div (A := A) (B := |s.im|) hA ht (M + 1) (s.re)
    convert h using 3 <;> push_cast <;> ring_nf
  have step2 : (2 * A ^ ((M : ℝ) + 1 - s.re) + sTT s A (M + 1)) / ‖sdd s (M + 1)‖
      ≤ 2 * A ^ (-s.re) * (A / |s.im|) ^ (M + 1) + sTT s A (M + 1) / ‖sdd s (M + 1)‖ := by
    have hmain : 2 * A ^ ((M : ℝ) + 1 - s.re) / ‖sdd s (M + 1)‖
        ≤ 2 * A ^ (-s.re) * (A / |s.im|) ^ (M + 1) := by
      have hstep : 2 * A ^ ((M : ℝ) + 1 - s.re) / ‖sdd s (M + 1)‖
          ≤ 2 * A ^ ((M : ℝ) + 1 - s.re) / |s.im| ^ (M + 1) := by
        apply div_le_div_of_nonneg_left (by positivity) (pow_pos ht _)
        exact norm_sdd_ge s (M + 1)
      have hEq2 : 2 * (A ^ ((M : ℝ) + 1 - s.re) / |s.im| ^ (M + 1))
          = 2 * (A ^ (-s.re) * (A / |s.im|) ^ (M + 1)) := by rw [hEq]
      calc 2 * A ^ ((M : ℝ) + 1 - s.re) / ‖sdd s (M + 1)‖
          ≤ 2 * A ^ ((M : ℝ) + 1 - s.re) / |s.im| ^ (M + 1) := hstep
        _ = 2 * (A ^ ((M : ℝ) + 1 - s.re) / |s.im| ^ (M + 1)) := by rw [mul_div_assoc]
        _ = 2 * (A ^ (-s.re) * (A / |s.im|) ^ (M + 1)) := hEq2
        _ = 2 * A ^ (-s.re) * (A / |s.im|) ^ (M + 1) := by ring
    rw [add_div]
    exact add_le_add hmain le_rfl
  have step := le_trans step1 step2
  rw [sKK, sKK, Finset.sum_range_succ]
  linarith [step]

lemma sKK_le {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) {A : ℝ} (hA : 0 < A)
    (ht : 0 < |s.im|) (M : ℕ) :
    sKK s A M ≤ 2 * A ^ (-s.re) * (Finset.sum (Finset.range M) (fun k => (A / |s.im|) ^ (k + 1)))
      + 2 * A ^ (-s.re) * ((A / ((M : ℝ) + 1 - s.re)) * (A / |s.im|) ^ M) := by
  have h1 := sTT_le (s := s) hs0 hs1 hA M
  have hge : |s.im| ^ M ≤ ‖sdd s M‖ := norm_sdd_ge s M
  have hAσ : (0 : ℝ) < A ^ (-s.re) := Real.rpow_pos_of_pos hA _
  have hMpos : (0 : ℝ) < (M : ℝ) + 1 - s.re := by
    have : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    linarith
  have hEq : A ^ ((M : ℝ) + 1 - s.re) / |s.im| ^ M
      = A * (A ^ (-s.re) * (A / |s.im|) ^ M) := by
    have h2 := rpow_shift_div (A := A) (B := |s.im|) hA ht M (s.re)
    have h3 : A ^ ((M : ℝ) + 1 - s.re) = A * A ^ ((M : ℝ) - s.re) := by
      rw [show (M : ℝ) + 1 - s.re = 1 + ((M : ℝ) - s.re) by ring, Real.rpow_add hA,
        Real.rpow_one]
    rw [h3, mul_div_assoc, h2]
  have h2 : sTT s A M / ‖sdd s M‖
      ≤ 2 * A ^ (-s.re) * ((A / ((M : ℝ) + 1 - s.re)) * (A / |s.im|) ^ M) := by
    have hNN : (0 : ℝ) ≤ sTT s A M := by
      simp only [sTT]; positivity
    have hstep : sTT s A M / ‖sdd s M‖ ≤ sTT s A M / |s.im| ^ M :=
      div_le_div_of_nonneg_left hNN (pow_pos ht M) hge
    have hstep2 : sTT s A M / |s.im| ^ M
        ≤ (2 * A ^ ((M : ℝ) + 1 - s.re) / ((M : ℝ) + 1 - s.re)) / |s.im| ^ M := by
      refine div_le_div_of_nonneg_right ?_ (pow_nonneg ht.le M)
      rw [mul_div_assoc]
      exact h1
    refine le_trans hstep ?_
    refine le_trans hstep2 ?_
    have h3 : (2 * A ^ ((M : ℝ) + 1 - s.re) / ((M : ℝ) + 1 - s.re)) / |s.im| ^ M
        = 2 * (A ^ ((M : ℝ) + 1 - s.re) / |s.im| ^ M) / ((M : ℝ) + 1 - s.re) := by ring
    rw [h3, hEq]
    have h4 : 2 * (A * (A ^ (-s.re) * (A / |s.im|) ^ M)) / ((M : ℝ) + 1 - s.re)
        = 2 * A ^ (-s.re) * ((A / ((M : ℝ) + 1 - s.re)) * (A / |s.im|) ^ M) := by
      field_simp
    rw [h4]
  rw [sKK, Finset.mul_sum]
  exact add_le_add le_rfl h2

/-! ## Elementary geometric estimates -/

lemma geom_pow_mul {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (M : ℕ) :
    ((M : ℝ) + 1) * ((1 - t) * t ^ M) ≤ 1 := by
  have hterm : ∀ k ∈ Finset.range (M + 1), t ^ M ≤ t ^ k := by
    intro k hk
    rw [Finset.mem_range] at hk
    exact pow_le_pow_of_le_one ht0 ht1 (by omega)
  have h1 : Finset.sum (Finset.range (M + 1)) (fun _ => t ^ M)
      ≤ Finset.sum (Finset.range (M + 1)) (fun k => t ^ k) := Finset.sum_le_sum hterm
  have h2 : Finset.sum (Finset.range (M + 1)) (fun _ => t ^ M) = ((M : ℝ) + 1) * t ^ M := by
    simp [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
  have hsum : ((M : ℝ) + 1) * t ^ M ≤ Finset.sum (Finset.range (M + 1)) (fun k => t ^ k) := by
    rw [← h2]; exact h1
  have h3 : (1 - t) * Finset.sum (Finset.range (M + 1)) (fun k => t ^ k) ≤ 1 := by
    have hm := geom_sum_mul_neg t (M + 1)
    have hp : (0 : ℝ) ≤ t ^ (M + 1) := pow_nonneg ht0 _
    calc (1 - t) * Finset.sum (Finset.range (M + 1)) (fun k => t ^ k)
        = Finset.sum (Finset.range (M + 1)) (fun k => t ^ k) * (1 - t) := by ring
      _ = 1 - t ^ (M + 1) := hm
      _ ≤ 1 := by linarith
  calc ((M : ℝ) + 1) * ((1 - t) * t ^ M) = (1 - t) * (((M : ℝ) + 1) * t ^ M) := by ring
    _ ≤ (1 - t) * Finset.sum (Finset.range (M + 1)) (fun k => t ^ k) :=
        mul_le_mul_of_nonneg_left hsum (by linarith)
    _ ≤ 1 := h3

lemma two_mul_pow_le_one {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {M : ℕ} (hM : 1 ≤ M) :
    2 * ((1 - t) * t ^ M) ≤ 1 := by
  have h := geom_pow_mul ht0 ht1 M
  have hM2 : (2 : ℝ) ≤ (M : ℝ) + 1 := by
    have : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    linarith
  have h1t : 0 ≤ 1 - t := by linarith
  have htM : 0 ≤ t ^ M := pow_nonneg ht0 M
  calc 2 * ((1 - t) * t ^ M) ≤ ((M : ℝ) + 1) * ((1 - t) * t ^ M) :=
        mul_le_mul_of_nonneg_right hM2 (mul_nonneg h1t htM)
    _ ≤ 1 := h

lemma norm_cpow_le_pi_div_two_mul {s : ℂ} {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    ‖((v : ℂ) ^ (-s))‖ ≤ (Real.pi / 2) * ‖((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (-s - 1)‖ := by
  have hvpi : v ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hsin : 2 / Real.pi * v ≤ Real.sin v := Real.mul_le_sin hv0.le hvpi
  have hsinpos : 0 < Real.sin v := Real.sin_pos_of_pos_of_lt_pi hv0 (by linarith [Real.pi_gt_three])
  have hL : ‖((v : ℂ) ^ (-s))‖ = v ^ (-s.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hv0]
    simp
  have hre : ((-s - 1 : ℂ)).re = -s.re - 1 := by simp
  have hR : ‖((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (-s - 1)‖ = Real.sin v * v ^ (-s.re - 1) := by
    rw [norm_mul, complex_norm_ofReal, abs_of_pos hsinpos,
      Complex.norm_cpow_eq_rpow_re_of_pos hv0, hre]
  rw [hL, hR]
  have hvpow : v ^ (-s.re) = v ^ (-s.re - 1) * v := by
    have hsplit : v ^ (-s.re) = v ^ (-s.re - 1) * v ^ (1 : ℝ) := by
      rw [← Real.rpow_add hv0]
      congr 1
      ring
    rw [hsplit, Real.rpow_one]
  rw [hvpow]
  have h3 : v ≤ Real.pi / 2 * Real.sin v := by
    have h4 : 2 / Real.pi * v * Real.pi ≤ Real.sin v * Real.pi :=
      mul_le_mul_of_nonneg_right hsin Real.pi_pos.le
    have h5 : 2 / Real.pi * v * Real.pi = 2 * v := by
      field_simp
    rw [h5] at h4
    linarith
  have h2 : (0 : ℝ) ≤ v ^ (-s.re - 1) := Real.rpow_nonneg hv0.le _
  calc v ^ (-s.re - 1) * v ≤ v ^ (-s.re - 1) * (Real.pi / 2 * Real.sin v) :=
        mul_le_mul_of_nonneg_left h3 h2
    _ = Real.pi / 2 * (Real.sin v * v ^ (-s.re - 1)) := by ring

/-! ## The entry identity: one integration by parts from `Q_{-1}` to `P_0` -/

lemma intervalIntegrable_cos_mul_cpow_neg {s : ℂ} (hs1 : s.re < 1) {A : ℝ} (hA : 0 < A) :
    IntervalIntegrable (fun x : ℝ => ((Real.cos x : ℝ) : ℂ) * (x : ℂ) ^ (-s)) volume 0 A := by
  have hr : (-1 : ℝ) < -s.re := by linarith
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hA.le]
  have hbase : IntegrableOn (fun x : ℝ => x ^ (-s.re)) (Set.Ioc 0 A) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hA.le]
    exact intervalIntegral.intervalIntegrable_rpow' hr
  refine Integrable.mono' hbase ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    intro x hx
    exact (((Complex.continuous_ofReal.comp Real.continuous_cos).continuousAt).mul
      (Complex.continuousAt_ofReal_cpow_const x (-s)
        (Or.inr (by exact_mod_cast (ne_of_gt hx.1))))).continuousWithinAt
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with x hx
    rw [norm_mul, complex_norm_ofReal, Complex.norm_cpow_eq_rpow_re_of_pos hx.1]
    have hre : ((-s : ℂ)).re = -s.re := by simp
    rw [hre]
    have hc : |Real.cos x| ≤ 1 := Real.abs_cos_le_one x
    have hx0 : (0 : ℝ) ≤ x ^ (-s.re) := Real.rpow_nonneg hx.1.le _
    nlinarith

lemma intervalIntegrable_sin_mul_cpow_neg {s : ℂ} (hs1 : s.re < 1) {A : ℝ} (hA : 0 < A) :
    IntervalIntegrable (fun x : ℝ => ((Real.sin x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) volume 0 A := by
  have hr : (-1 : ℝ) < -s.re := by linarith
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hA.le]
  have hbase : IntegrableOn (fun x : ℝ => x ^ (-s.re)) (Set.Ioc 0 A) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hA.le]
    exact intervalIntegral.intervalIntegrable_rpow' hr
  refine Integrable.mono' hbase ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    intro x hx
    exact (((Complex.continuous_ofReal.comp Real.continuous_sin).continuousAt).mul
      (Complex.continuousAt_ofReal_cpow_const x (-s - 1)
        (Or.inr (by exact_mod_cast (ne_of_gt hx.1))))).continuousWithinAt
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with x hx
    rw [norm_mul, complex_norm_ofReal, Complex.norm_cpow_eq_rpow_re_of_pos hx.1]
    have hre : ((-s - 1 : ℂ)).re = -s.re - 1 := by simp
    rw [hre]
    have h1 : |Real.sin x| ≤ x := by
      have := Real.abs_sin_le_abs (x := x)
      rwa [abs_of_pos hx.1] at this
    have h2 : x * x ^ (-s.re - 1) = x ^ (-s.re) := by
      calc x * x ^ (-s.re - 1) = x ^ (1 : ℝ) * x ^ (-s.re - 1) := by rw [Real.rpow_one]
        _ = x ^ ((1 : ℝ) + (-s.re - 1)) := by rw [Real.rpow_add hx.1]
        _ = x ^ (-s.re) := by congr 1; ring
    have h3 : (0 : ℝ) ≤ x ^ (-s.re - 1) := Real.rpow_nonneg hx.1.le _
    calc |Real.sin x| * x ^ (-s.re - 1) ≤ x * x ^ (-s.re - 1) :=
          mul_le_mul_of_nonneg_right h1 h3
      _ = x ^ (-s.re) := h2

lemma sinCpowNegIntegral_ibp {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) {A : ℝ}
    (hA : 0 < A) :
    s * (∫ v in Set.Ioc 0 A, ((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (-s - 1)) =
      - ((Real.sin A : ℝ) : ℂ) * (A : ℂ) ^ (-s) +
        ∫ v in Set.Ioc 0 A, ((Real.cos v : ℝ) : ℂ) * (v : ℂ) ^ (-s) := by
  have hsne : s ≠ 0 := by
    intro h
    rw [h] at hs0
    simp at hs0
  have hI1 := intervalIntegrable_cos_mul_cpow_neg (s := s) hs1 hA
  have hI2 := intervalIntegrable_sin_mul_cpow_neg (s := s) hs1 hA
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) A,
      HasDerivAt (fun v : ℝ => ((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (-s))
        (((Real.cos x : ℝ) : ℂ) * (x : ℂ) ^ (-s)
          - s * (((Real.sin x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))) x := by
    intro x hx
    have h1 : HasDerivAt (fun v : ℝ => ((Real.sin v : ℝ) : ℂ)) ((Real.cos x : ℝ) : ℂ) x :=
      (Real.hasDerivAt_sin x).ofReal_comp
    have h2 : HasDerivAt (fun v : ℝ => (v : ℂ) ^ (-s)) ((-s) * (x : ℂ) ^ (-s - 1)) x :=
      hasDerivAt_ofReal_cpow_const hx.1.ne' (neg_ne_zero.mpr hsne)
    have h3 := h1.mul h2
    have hval : ((Real.cos x : ℝ) : ℂ) * (x : ℂ) ^ (-s)
          + ((Real.sin x : ℝ) : ℂ) * ((-s) * (x : ℂ) ^ (-s - 1))
        = ((Real.cos x : ℝ) : ℂ) * (x : ℂ) ^ (-s)
          - s * (((Real.sin x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) := by
      ring
    rw [hval] at h3
    exact h3
  have hlim0 : Filter.Tendsto (fun v : ℝ => ((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (-s))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hrpow : Filter.Tendsto (fun v : ℝ => v ^ (1 - s.re)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h := (Real.continuousAt_rpow_const (0 : ℝ) (1 - s.re) (Or.inr (by linarith))).tendsto
      have h0 : (0 : ℝ) ^ (1 - s.re) = 0 := Real.zero_rpow (by linarith)
      rw [h0] at h
      exact h.mono_left nhdsWithin_le_nhds
    have hbound : ∀ᶠ v in 𝓝[>] (0 : ℝ),
        ‖((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (-s)‖ ≤ v ^ (1 - s.re) := by
      filter_upwards [self_mem_nhdsWithin] with v hv
      have hv0 : (0 : ℝ) < v := Set.mem_Ioi.mp hv
      rw [norm_mul, complex_norm_ofReal, Complex.norm_cpow_eq_rpow_re_of_pos hv0]
      have hre : ((-s : ℂ)).re = -s.re := by simp
      rw [hre]
      have h1 : |Real.sin v| ≤ v := by
        have := Real.abs_sin_le_abs (x := v)
        rwa [abs_of_pos hv0] at this
      have h2 : v ^ (-s.re) * v = v ^ (1 - s.re) := by
        calc v ^ (-s.re) * v = v ^ (-s.re) * v ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = v ^ ((-s.re) + 1) := by rw [Real.rpow_add hv0]
          _ = v ^ (1 - s.re) := by congr 1; ring
      calc |Real.sin v| * v ^ (-s.re) ≤ v * v ^ (-s.re) :=
            mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hv0.le _)
        _ = v ^ (-s.re) * v := by ring
        _ = v ^ (1 - s.re) := h2
    exact tendsto_zero_iff_norm_tendsto_zero.mpr
      (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hrpow
        (Filter.Eventually.of_forall fun _ => norm_nonneg _) hbound)
  have hlimA : Filter.Tendsto (fun v : ℝ => ((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (-s))
      (𝓝[<] A) (𝓝 (((Real.sin A : ℝ) : ℂ) * (A : ℂ) ^ (-s))) := by
    have hc : ContinuousAt (fun v : ℝ => ((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (-s)) A :=
      ((Complex.continuous_ofReal.comp Real.continuous_sin).continuousAt).mul
        (Complex.continuousAt_ofReal_cpow_const A (-s) (Or.inr (by exact_mod_cast hA.ne')))
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have hint : IntervalIntegrable (fun x : ℝ => ((Real.cos x : ℝ) : ℂ) * (x : ℂ) ^ (-s)
      - s * (((Real.sin x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))) volume 0 A :=
    hI1.sub (hI2.const_mul s)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (a := (0 : ℝ)) (b := A)
    hA hderiv hint hlim0 hlimA
  have hsplit : (∫ y in (0 : ℝ)..A, (((Real.cos y : ℝ) : ℂ) * (y : ℂ) ^ (-s)
      - s * (((Real.sin y : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1))))
      = (∫ y in (0 : ℝ)..A, ((Real.cos y : ℝ) : ℂ) * (y : ℂ) ^ (-s))
        - s * (∫ y in (0 : ℝ)..A, ((Real.sin y : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1)) := by
    rw [intervalIntegral.integral_sub hI1 (hI2.const_mul s), intervalIntegral.integral_const_mul]
  rw [hsplit, intervalIntegral.integral_of_le hA.le, intervalIntegral.integral_of_le hA.le,
    sub_zero] at hFTC
  have hfin : s * (∫ v in Set.Ioc 0 A, ((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (-s - 1))
      = (∫ v in Set.Ioc 0 A, ((Real.cos v : ℝ) : ℂ) * (v : ℂ) ^ (-s))
        - ((Real.sin A : ℝ) : ℂ) * (A : ℂ) ^ (-s) := by
    have h1 : s * (∫ v in Set.Ioc 0 A, ((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (-s - 1))
        + ((Real.sin A : ℝ) : ℂ) * (A : ℂ) ^ (-s)
        = ∫ v in Set.Ioc 0 A, ((Real.cos v : ℝ) : ℂ) * (v : ℂ) ^ (-s) := by
      have h := hFTC
      rw [sub_eq_iff_eq_add] at h
      rw [h]
      ring
    exact (eq_sub_iff_add_eq).mpr h1
  rw [hfin]
  ring

/-! ## The main theorem -/

theorem sinIntegralLowerSharp {s : ℂ} (hs0 : 0 < s.re) {A : ℝ} (hA1 : 1 ≤ A)
    (hAt : A < |s.im|) :
    ‖∫ v in Set.Ioc 0 A, ((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (-s - 1)‖ ≤
      8 * A ^ (-s.re) / (|s.im| - A) := by
  have hApos : (0 : ℝ) < A := by linarith
  have htpos : (0 : ℝ) < |s.im| := by linarith
  have htA : (0 : ℝ) < |s.im| - A := by linarith
  have hAσ : (0 : ℝ) < A ^ (-s.re) := Real.rpow_pos_of_pos hApos _
  rcases lt_or_ge s.re 1 with hs1 | hs1
  · ------------------------------------------------------------------
    -- Case `Re s < 1`: the Kummer recursion
    ------------------------------------------------------------------
    have hR1 : A / |s.im| < 1 := (div_lt_one htpos).mpr hAt
    have hR0 : (0 : ℝ) < A / |s.im| := by positivity
    set M : ℕ := ⌈A⌉₊ with hM
    have hMA : A ≤ (M : ℝ) := Nat.le_ceil A
    have hM1 : 1 ≤ M := by
      have : (1 : ℝ) ≤ (M : ℝ) := by linarith
      exact_mod_cast this
    have h1msub : (1 : ℝ) - A / |s.im| ≠ 0 := by linarith
    have hMpos : (0 : ℝ) < (M : ℝ) + 1 - s.re := by linarith
    -- geometric estimates
    have hgeom := two_mul_pow_le_one (t := A / |s.im|) hR0.le hR1.le hM1
    have hsum := geom_shift_le hR0 hR1 M
    have hAM : A / ((M : ℝ) + 1 - s.re) ≤ 1 := by
      rw [div_le_one hMpos]
      linarith
    -- `sKK s A 0 ≤ sKK s A M`
    have hmono : ∀ n, sKK s A n ≤ sKK s A (n + 1) := fun n => sKK_mono hs1 hApos htpos n
    have h0M : sKK s A 0 ≤ sKK s A M := by
      induction M with
      | zero => exact le_rfl
      | succ n ih => exact le_trans ih (hmono n)
    have hKKle := sKK_le (s := s) hs0 hs1 hApos htpos M
    -- ratio identities
    have hratio : (A / |s.im|) / (1 - A / |s.im|) = A / (|s.im| - A) := by
      field_simp <;> ring
    have hratio2 : 1 / (1 - A / |s.im|) = |s.im| / (|s.im| - A) := by
      field_simp <;> ring
    -- the two pieces of `sKK_le`
    have hpiece1 : 2 * A ^ (-s.re) * (Finset.sum (Finset.range M)
        (fun k => (A / |s.im|) ^ (k + 1))) ≤ 2 * A ^ (-s.re) * (A / (|s.im| - A)) := by
      have h2 := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ 2 * A ^ (-s.re))
      rwa [hratio] at h2
    have hpiece2 : 2 * A ^ (-s.re) * ((A / ((M : ℝ) + 1 - s.re)) * (A / |s.im|) ^ M)
        ≤ A ^ (-s.re) * (|s.im| / (|s.im| - A)) := by
      have hrpow : (0 : ℝ) ≤ (A / |s.im|) ^ M := pow_nonneg hR0.le M
      have hB1 : (A / ((M : ℝ) + 1 - s.re)) * (A / |s.im|) ^ M ≤ (A / |s.im|) ^ M := by
        simpa using mul_le_mul_of_nonneg_right hAM hrpow
      have hB2 : 2 * (A / |s.im|) ^ M ≤ |s.im| / (|s.im| - A) := by
        have h3 : 2 * (A / |s.im|) ^ M ≤ 1 / (1 - A / |s.im|) := by
          rw [le_div_iff₀ (by linarith : (0 : ℝ) < 1 - A / |s.im|)]
          linarith [hgeom]
        rwa [hratio2] at h3
      calc 2 * A ^ (-s.re) * ((A / ((M : ℝ) + 1 - s.re)) * (A / |s.im|) ^ M)
          ≤ 2 * A ^ (-s.re) * (A / |s.im|) ^ M :=
            mul_le_mul_of_nonneg_left hB1 (by positivity)
        _ = A ^ (-s.re) * (2 * (A / |s.im|) ^ M) := by ring
        _ ≤ A ^ (-s.re) * (|s.im| / (|s.im| - A)) := mul_le_mul_of_nonneg_left hB2 (le_of_lt hAσ)
    -- combine
    have hfinal3 : 2 * A ^ (-s.re) * (A / (|s.im| - A)) + A ^ (-s.re) * (|s.im| / (|s.im| - A))
        ≤ 3 * A ^ (-s.re) * |s.im| / (|s.im| - A) := by
      have key : A ^ (-s.re) * (2 * A + |s.im|) ≤ 3 * A ^ (-s.re) * |s.im| := by
        have h6 : 2 * A + |s.im| ≤ 3 * |s.im| := by linarith [hAt.le]
        calc A ^ (-s.re) * (2 * A + |s.im|) ≤ A ^ (-s.re) * (3 * |s.im|) :=
              mul_le_mul_of_nonneg_left h6 (le_of_lt hAσ)
          _ = 3 * A ^ (-s.re) * |s.im| := by ring
      have hL : 2 * A ^ (-s.re) * (A / (|s.im| - A)) + A ^ (-s.re) * (|s.im| / (|s.im| - A))
          = A ^ (-s.re) * (2 * A + |s.im|) / (|s.im| - A) := by
        field_simp <;> ring
      rw [hL]
      exact div_le_div_of_nonneg_right key htA.le
    have hKK : sKK s A M ≤ 3 * A ^ (-s.re) * |s.im| / (|s.im| - A) :=
      calc sKK s A M
          ≤ 2 * A ^ (-s.re) * (Finset.sum (Finset.range M) (fun k => (A / |s.im|) ^ (k + 1)))
            + 2 * A ^ (-s.re) * ((A / ((M : ℝ) + 1 - s.re)) * (A / |s.im|) ^ M) := hKKle
        _ ≤ 2 * A ^ (-s.re) * (A / (|s.im| - A)) + A ^ (-s.re) * (|s.im| / (|s.im| - A)) :=
            add_le_add hpiece1 hpiece2
        _ ≤ 3 * A ^ (-s.re) * |s.im| / (|s.im| - A) := hfinal3
    -- consequently `‖P_0‖` is bounded
    have hP0 : ‖sPP s A 0‖ ≤ 3 * A ^ (-s.re) * |s.im| / (|s.im| - A) := by
      have h00 : sKK s A 0 = sTT s A 0 := by simp [sKK, sdd_zero]
      have hle : ‖sPP s A 0‖ ≤ sTT s A 0 := by
        simp only [sTT]
        linarith [norm_nonneg (sQQ s A 0)]
      linarith [h0M, hKK]
    -- the entry identity
    have hentry := sinCpowNegIntegral_ibp (s := s) hs0 hs1 hApos
    have hsPP0 : sPP s A 0 = ∫ v in Set.Ioc 0 A, ((Real.cos v : ℝ) : ℂ) * (v : ℂ) ^ (-s) := by
      simp [sPP]
    rw [hsPP0] at hP0
    have hsin : ‖((Real.sin A : ℝ) : ℂ) * (A : ℂ) ^ (-s)‖ ≤ A ^ (-s.re) := by
      rw [norm_mul, complex_norm_ofReal, Complex.norm_cpow_eq_rpow_re_of_pos hApos]
      have hre : ((-s : ℂ)).re = -s.re := by simp
      rw [hre]
      have hc : |Real.sin A| ≤ 1 := Real.abs_sin_le_one A
      have hv0 : (0 : ℝ) ≤ A ^ (-s.re) := Real.rpow_nonneg hApos.le _
      nlinarith
    -- `‖s * T‖ ≤ 4 A^{-σ}|Im s|/(|Im s| - A)`
    have hmul : ‖s * (∫ v in Set.Ioc 0 A, ((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (-s - 1))‖
        ≤ 4 * A ^ (-s.re) * |s.im| / (|s.im| - A) := by
      rw [hentry]
      have h1 : ‖-((Real.sin A : ℝ) : ℂ) * (A : ℂ) ^ (-s)
          + ∫ v in Set.Ioc 0 A, ((Real.cos v : ℝ) : ℂ) * (v : ℂ) ^ (-s)‖
          ≤ A ^ (-s.re) + 3 * A ^ (-s.re) * |s.im| / (|s.im| - A) := by
        refine le_trans (norm_add_le _ _) ?_
        exact add_le_add (by rw [neg_mul, norm_neg]; exact hsin) hP0
      refine le_trans h1 ?_
      have hlt : (1 : ℝ) + 3 * |s.im| / (|s.im| - A) ≤ 4 * |s.im| / (|s.im| - A) := by
        have h7 : (1 : ℝ) + 3 * |s.im| / (|s.im| - A)
            = ((|s.im| - A) + 3 * |s.im|) / (|s.im| - A) := by
          field_simp <;> ring
        rw [h7]
        apply div_le_div_of_nonneg_right _ htA.le
        linarith [hAt.le]
      calc A ^ (-s.re) + 3 * A ^ (-s.re) * |s.im| / (|s.im| - A)
          = A ^ (-s.re) * (1 + 3 * |s.im| / (|s.im| - A)) := by ring
        _ ≤ A ^ (-s.re) * (4 * |s.im| / (|s.im| - A)) := mul_le_mul_of_nonneg_left hlt (le_of_lt hAσ)
        _ = 4 * A ^ (-s.re) * |s.im| / (|s.im| - A) := by ring
    -- divide by `‖s‖ ≥ |Im s|`
    have hnorm_s : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
    have hnormpos : (0 : ℝ) < ‖s‖ := by
      refine norm_pos_iff.mpr ?_
      intro h
      rw [h] at hs0
      simp at hs0
    have hstep1 : ‖(∫ v in Set.Ioc 0 A, ((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (-s - 1))‖ * ‖s‖
        ≤ 4 * A ^ (-s.re) * |s.im| / (|s.im| - A) := by
      have h := hmul
      rw [mul_comm s (∫ v in Set.Ioc 0 A, ((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (-s - 1)),
        norm_mul] at h
      exact h
    have hstep2 : ‖(∫ v in Set.Ioc 0 A, ((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (-s - 1))‖
        * (|s.im| - A) ≤ 4 * A ^ (-s.re) := by
      have haux : ‖(∫ v in Set.Ioc 0 A, ((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (-s - 1))‖
          * (|s.im| - A) * ‖s‖ ≤ 4 * A ^ (-s.re) * ‖s‖ := by
        have h1 : ‖(∫ v in Set.Ioc 0 A, ((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (-s - 1))‖ * ‖s‖
            * (|s.im| - A) ≤ (4 * A ^ (-s.re) * |s.im| / (|s.im| - A)) * (|s.im| - A) :=
          mul_le_mul_of_nonneg_right hstep1 htA.le
        have h2 : (4 * A ^ (-s.re) * |s.im| / (|s.im| - A)) * (|s.im| - A) = 4 * A ^ (-s.re) * |s.im| := by
          field_simp
        rw [h2] at h1
        calc ‖(∫ v in Set.Ioc 0 A, ((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (-s - 1))‖
              * (|s.im| - A) * ‖s‖
            = ‖(∫ v in Set.Ioc 0 A, ((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (-s - 1))‖ * ‖s‖
              * (|s.im| - A) := by ring
          _ ≤ 4 * A ^ (-s.re) * |s.im| := h1
          _ ≤ 4 * A ^ (-s.re) * ‖s‖ := mul_le_mul_of_nonneg_left hnorm_s (by positivity)
      exact le_of_mul_le_mul_right haux hnormpos
    have hfinal : ‖(∫ v in Set.Ioc 0 A, ((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (-s - 1))‖
        ≤ 4 * A ^ (-s.re) / (|s.im| - A) := by
      rw [le_div_iff₀ htA]
      exact hstep2
    calc ‖∫ v in Set.Ioc 0 A, ((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (-s - 1)‖
        ≤ 4 * A ^ (-s.re) / (|s.im| - A) := hfinal
      _ ≤ 8 * A ^ (-s.re) / (|s.im| - A) := by
          apply div_le_div_of_nonneg_right _ htA.le
          linarith [hAσ]
  · ------------------------------------------------------------------
    -- Case `1 ≤ Re s`: the integrand is not integrable at `0`
    ------------------------------------------------------------------
    have hnotint : ¬ Integrable
        (fun v : ℝ => ((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (-s - 1))
        (volume.restrict (Set.Ioc 0 A)) := by
      intro hint
      have hnorm : IntegrableOn
          (fun v : ℝ => ‖((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (-s - 1)‖) (Set.Ioc 0 A) := hint.norm
      have hsub : Set.Ioo (0 : ℝ) 1 ⊆ Set.Ioc 0 A := by
        intro x hx
        exact ⟨hx.1, by linarith [hx.2]⟩
      have hnorm1 : IntegrableOn
          (fun v : ℝ => ‖((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (-s - 1)‖) (Set.Ioo 0 1) :=
        hnorm.mono_set hsub
      have hnorm2 : IntegrableOn
          (fun v : ℝ => (Real.pi / 2)
            * ‖((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (-s - 1)‖) (Set.Ioo 0 1) :=
        hnorm1.const_mul (Real.pi / 2)
      have hbound : ∀ᵐ v : ℝ ∂(volume.restrict (Set.Ioo 0 1)),
          ‖((v : ℂ) ^ (-s))‖ ≤ (Real.pi / 2) *
            ‖((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (-s - 1)‖ := by
        filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with v hv
        exact norm_cpow_le_pi_div_two_mul hv.1 hv.2
      have hmeas : AEStronglyMeasurable (fun v : ℝ => (v : ℂ) ^ (-s))
          (volume.restrict (Set.Ioo 0 1)) := by
        refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
        intro v hv
        exact (Complex.continuousAt_ofReal_cpow_const v (-s)
          (Or.inr (by exact_mod_cast (ne_of_gt hv.1)))).continuousWithinAt
      have hint2 : IntegrableOn (fun v : ℝ => (v : ℂ) ^ (-s)) (Set.Ioo 0 1) :=
        Integrable.mono' hnorm2 hmeas hbound
      have hcontra :=
        (intervalIntegral.integrableOn_Ioo_cpow_iff (s := -s) (t := 1) one_pos).mp hint2
      simp only [Complex.neg_re] at hcontra
      linarith
    rw [MeasureTheory.integral_undef hnotint, norm_zero]
    exact div_nonneg (by positivity) (by linarith)

end

end Work.ZeroDensity.Ingham.AfeSelf
