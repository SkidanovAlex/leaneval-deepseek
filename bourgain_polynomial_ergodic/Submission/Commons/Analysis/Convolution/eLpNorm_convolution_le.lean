import Mathlib
import Submission.Commons.Analysis.Convolution.lintegral_rpow_le_of_forall_mul_le
import Submission.Commons.MeasureTheory.Function.eLpNorm_lintegral_le_lintegral_eLpNorm_sfinite

namespace Commons.Analysis.Convolution

open _root_.MeasureTheory
open scoped ENNReal

set_option linter.unusedVariables false

/-! ### Small `eLpNorm` helpers for `ℝ≥0∞`-valued functions -/

/-- Multiplying an `ℝ≥0∞`-valued function by a constant scales its `ℒp` seminorm. -/
theorem eLpNorm_const_mul_ennreal_of_pos {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (c : ℝ≥0∞) {s : ℝ} (hs : 0 < s) :
    eLpNorm (fun x => c * f x) (ENNReal.ofReal s) μ = c * eLpNorm f (ENNReal.ofReal s) μ := by
  have hs0 : ENNReal.ofReal s ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hs
  have hst : ENNReal.ofReal s ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hs0 hst (hf.const_mul c).aestronglyMeasurable,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hs0 hst hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofReal hs.le, enorm_eq_self]
  rw [show (∫⁻ x, (c * f x) ^ s ∂μ) = ∫⁻ x, c ^ s * f x ^ s ∂μ from
        lintegral_congr fun x => ENNReal.mul_rpow_of_nonneg c (f x) hs.le]
  rw [lintegral_const_mul'' _ (hf.pow_const s)]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1 / s)]
  rw [← ENNReal.rpow_mul, mul_one_div_cancel (ne_of_gt hs), ENNReal.rpow_one]

/-- Translation invariance of the `ℒp` seminorm of `ℝ≥0∞`-valued functions. -/
theorem eLpNorm_sub_right_ennreal {G : Type*} [MeasurableSpace G] [AddGroup G]
    [MeasurableAdd G] {μ : Measure G} [μ.IsAddRightInvariant] (f : G → ℝ≥0∞) (y : G)
    {s : ℝ} (hs : 0 < s) :
    eLpNorm (fun x => f (x - y)) (ENNReal.ofReal s) μ = eLpNorm f (ENNReal.ofReal s) μ := by
  have hs0 : ENNReal.ofReal s ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hs
  have hst : ENNReal.ofReal s ≠ ⊤ := ENNReal.ofReal_ne_top
  by_cases hf : AEStronglyMeasurable f μ
  swap
  · have hfy : ¬ AEStronglyMeasurable (fun x => f (x - y)) μ := by
      intro h
      apply hf
      have h2 := h.comp_measurePreserving (measurePreserving_add_right μ y)
      refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
      simp
    rw [eLpNorm_of_not_aestronglyMeasurable hf, eLpNorm_of_not_aestronglyMeasurable hfy]
  have hfy : AEStronglyMeasurable (fun x => f (x - y)) μ :=
    hf.comp_measurePreserving (measurePreserving_sub_right μ y)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hs0 hst hfy,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hs0 hst hf]
  simp only [ENNReal.toReal_ofReal hs.le, enorm_eq_self]
  rw [show (∫⁻ x, (fun w : G => f w ^ s) (x - y) ∂μ) = ∫⁻ x, f x ^ s ∂μ from
        lintegral_sub_right_eq_self (fun w => f w ^ s) y]

section Algebra

private lemma rpow_decomp {a b c : ℝ≥0∞} {p q r : ℝ} (hp : 1 < p) (hq : 1 < q) (hr : 1 < r)
    (hpqr : 1 / p + 1 / r = 1 + 1 / q) :
    a * b * c = (a ^ p * b ^ r) ^ (1 / q) * (b ^ r * c ^ (q / (q - 1))) ^ ((p - 1) / p)
      * (c ^ (q / (q - 1)) * a ^ p) ^ ((r - 1) / r) := by
  have hp0 : (0:ℝ) < p := by linarith
  have hr0 : (0:ℝ) < r := by linarith
  have hq0 : (0:ℝ) < q := by linarith
  have hp' : (p - 1) / p = 1 - 1 / p := by rw [sub_div, div_self (ne_of_gt hp0)]
  have hr' : (r - 1) / r = 1 - 1 / r := by rw [sub_div, div_self (ne_of_gt hr0)]
  have hq' : (q - 1) / q = 1 - 1 / q := by rw [sub_div, div_self (ne_of_gt hq0)]
  have h1q : (0:ℝ) ≤ 1 / q := by positivity
  have hpp : (0:ℝ) ≤ (p - 1) / p := by positivity
  have hrr : (0:ℝ) ≤ (r - 1) / r := by positivity
  have hsum : (p - 1) / p + (r - 1) / r = (q - 1) / q := by
    rw [hp', hr', hq']; linarith
  have hp1 : p * (1 / q) + p * ((r - 1) / r) = 1 := by
    rw [hr', ← mul_add]
    have : 1 / q + (1 - 1 / r) = 1 / p := by linarith
    rw [this, mul_one_div, div_self (ne_of_gt hp0)]
  have hr1 : r * (1 / q) + r * ((p - 1) / p) = 1 := by
    rw [hp', ← mul_add]
    have : 1 / q + (1 - 1 / p) = 1 / r := by linarith
    rw [this, mul_one_div, div_self (ne_of_gt hr0)]
  have hq1 : (q / (q - 1)) * ((p - 1) / p) + (q / (q - 1)) * ((r - 1) / r) = 1 := by
    rw [← mul_add, hsum, div_mul_div_comm, mul_comm (q - 1) q, div_self (by positivity)]
  have ha : a ^ (p * (1 / q)) * a ^ (p * ((r - 1) / r)) = a := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity), hp1, ENNReal.rpow_one]
  have hb : b ^ (r * (1 / q)) * b ^ (r * ((p - 1) / p)) = b := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity), hr1, ENNReal.rpow_one]
  have hc : c ^ ((q / (q - 1)) * ((p - 1) / p)) * c ^ ((q / (q - 1)) * ((r - 1) / r)) = c := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity), hq1, ENNReal.rpow_one]
  have hdecomp :
      (a ^ p * b ^ r) ^ (1 / q) * (b ^ r * c ^ (q / (q - 1))) ^ ((p - 1) / p)
        * (c ^ (q / (q - 1)) * a ^ p) ^ ((r - 1) / r)
      = (a ^ (p * (1 / q)) * a ^ (p * ((r - 1) / r)))
        * (b ^ (r * (1 / q)) * b ^ (r * ((p - 1) / p)))
        * (c ^ ((q / (q - 1)) * ((p - 1) / p)) * c ^ ((q / (q - 1)) * ((r - 1) / r))) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ h1q, ENNReal.mul_rpow_of_nonneg _ _ hpp,
      ENNReal.mul_rpow_of_nonneg _ _ hrr]
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    ac_rfl
  rw [hdecomp, ha, hb, hc]

private lemma rpow_combine {P R S : ℝ≥0∞} {p q r : ℝ} (hp : 1 < p) (hq : 1 < q) (hr : 1 < r)
    (hpqr : 1 / p + 1 / r = 1 + 1 / q) :
    (P * R) ^ (1 / q) * (R * S) ^ ((p - 1) / p) * (S * P) ^ ((r - 1) / r)
      = P ^ (1 / p) * R ^ (1 / r) * S ^ ((q - 1) / q) := by
  have hp0 : (0:ℝ) < p := by linarith
  have hr0 : (0:ℝ) < r := by linarith
  have hq0 : (0:ℝ) < q := by linarith
  have hp' : (p - 1) / p = 1 - 1 / p := by rw [sub_div, div_self (ne_of_gt hp0)]
  have hr' : (r - 1) / r = 1 - 1 / r := by rw [sub_div, div_self (ne_of_gt hr0)]
  have hq' : (q - 1) / q = 1 - 1 / q := by rw [sub_div, div_self (ne_of_gt hq0)]
  have h1q : (0:ℝ) ≤ 1 / q := by positivity
  have hpp : (0:ℝ) ≤ (p - 1) / p := by positivity
  have hrr : (0:ℝ) ≤ (r - 1) / r := by positivity
  have h1 : 1 / q + (r - 1) / r = 1 / p := by rw [hr']; linarith
  have h2 : 1 / q + (p - 1) / p = 1 / r := by rw [hp']; linarith
  have h3 : (p - 1) / p + (r - 1) / r = (q - 1) / q := by rw [hp', hr', hq']; linarith
  have hP : P ^ (1 / q) * P ^ ((r - 1) / r) = P ^ (1 / p) := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity), h1]
  have hR : R ^ (1 / q) * R ^ ((p - 1) / p) = R ^ (1 / r) := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity), h2]
  have hS : S ^ ((p - 1) / p) * S ^ ((r - 1) / r) = S ^ ((q - 1) / q) := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity), h3]
  have hdecomp :
      (P * R) ^ (1 / q) * (R * S) ^ ((p - 1) / p) * (S * P) ^ ((r - 1) / r)
      = (P ^ (1 / q) * P ^ ((r - 1) / r)) * (R ^ (1 / q) * R ^ ((p - 1) / p))
        * (S ^ ((p - 1) / p) * S ^ ((r - 1) / r)) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ h1q, ENNReal.mul_rpow_of_nonneg _ _ hpp,
      ENNReal.mul_rpow_of_nonneg _ _ hrr]
    ac_rfl
  rw [hdecomp, hP, hR, hS]

end Algebra

section Prod

private lemma lintegral_prod_snd_mul_sub {G : Type*} [MeasurableSpace G] [AddGroup G]
    [MeasurableAdd₂ G] [MeasurableNeg G] {μ : Measure G} [SFinite μ] [μ.IsAddRightInvariant]
    {u v : G → ℝ≥0∞} (hu : AEMeasurable u μ) (hv : AEMeasurable v μ) :
    ∫⁻ z : G × G, u z.2 * v (z.1 - z.2) ∂(μ.prod μ) = (∫⁻ y, u y ∂μ) * (∫⁻ y, v y ∂μ) := by
  have hsub : AEMeasurable (fun z : G × G => v (z.1 - z.2)) (μ.prod μ) :=
    hv.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_of_right_invariant μ μ)
  have hmeas : AEMeasurable (Function.uncurry fun x y => u y * v (x - y)) (μ.prod μ) :=
    (hu.comp_snd).mul hsub
  rw [← lintegral_lintegral (μ := μ) (ν := μ) (f := fun x y => u y * v (x - y)) hmeas]
  rw [lintegral_lintegral_swap hmeas]
  have h1 : ∀ y, ∫⁻ x, u y * v (x - y) ∂μ = u y * ∫⁻ x, v x ∂μ := by
    intro y
    rw [lintegral_sub_right_eq_self (fun w => u y * v w) y]
    rw [lintegral_const_mul'' (u y) hv]
  simp_rw [h1]
  rw [lintegral_mul_const'' _ hu]

private lemma lintegral_prod_sub_mul {G : Type*} [MeasurableSpace G] [AddGroup G]
    [MeasurableAdd₂ G] [MeasurableNeg G] {μ : Measure G} [SFinite μ] [μ.IsAddRightInvariant]
    [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
    {u v : G → ℝ≥0∞} (hu : AEMeasurable u μ) (hv : AEMeasurable v μ) :
    ∫⁻ z : G × G, v (z.1 - z.2) * u z.1 ∂(μ.prod μ) = (∫⁻ y, v y ∂μ) * (∫⁻ y, u y ∂μ) := by
  have hsub : AEMeasurable (fun z : G × G => v (z.1 - z.2)) (μ.prod μ) :=
    hv.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_of_right_invariant μ μ)
  have hmeas : AEMeasurable (Function.uncurry fun x y => v (x - y) * u x) (μ.prod μ) :=
    hsub.mul hu.comp_fst
  rw [← lintegral_lintegral (μ := μ) (ν := μ) (f := fun x y => v (x - y) * u x) hmeas]
  have h1 : ∀ x, ∫⁻ y, v (x - y) * u x ∂μ = (∫⁻ y, v y ∂μ) * u x := by
    intro x
    have hstep : ∫⁻ y, v (x - y) * u x ∂μ = ∫⁻ y, v y * u x ∂μ := by
      simpa using lintegral_sub_left_eq_self (fun t => v t * u x) x
    rw [hstep, lintegral_mul_const'' (u x) hv]
  simp_rw [h1]
  rw [lintegral_const_mul'' _ hu]

private lemma lintegral_prod_mul {G : Type*} [MeasurableSpace G] {μ : Measure G} [SFinite μ]
    {u v : G → ℝ≥0∞} (hu : AEMeasurable u μ) (hv : AEMeasurable v μ) :
    ∫⁻ z : G × G, u z.1 * v z.2 ∂(μ.prod μ) = (∫⁻ y, u y ∂μ) * (∫⁻ y, v y ∂μ) := by
  have hmeas : AEMeasurable (Function.uncurry fun x y => u x * v y) (μ.prod μ) :=
    hu.comp_fst.mul hv.comp_snd
  rw [← lintegral_lintegral (μ := μ) (ν := μ) (f := fun x y => u x * v y) hmeas]
  have h1 : ∀ x, ∫⁻ y, u x * v y ∂μ = u x * ∫⁻ y, v y ∂μ := by
    intro x
    rw [lintegral_const_mul'' (u x) hv]
  simp_rw [h1]
  rw [lintegral_mul_const'' _ hu]

end Prod


section Trilinear

private lemma lintegral_convolution_mul_le {G : Type*} [MeasurableSpace G] [AddGroup G]
    [MeasurableAdd₂ G] [MeasurableNeg G] {μ : Measure G} [SFinite μ]
    [μ.IsAddRightInvariant] [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
    {p q r : ℝ} (hp : 1 < p) (hq : 1 < q) (hr : 1 < r)
    (hpqr : 1 / p + 1 / r = 1 + 1 / q)
    {φ ψ h : G → ℝ≥0∞} (hφ : AEMeasurable φ μ) (hψ : AEMeasurable ψ μ) (hh : AEMeasurable h μ) :
    ∫⁻ x, (∫⁻ y, φ y * ψ (x - y) ∂μ) * h x ∂μ ≤
      (∫⁻ x, φ x ^ p ∂μ) ^ (1 / p) * (∫⁻ x, ψ x ^ r ∂μ) ^ (1 / r)
        * (∫⁻ x, h x ^ (q / (q - 1)) ∂μ) ^ ((q - 1) / q) := by
  have hp0 : (0:ℝ) < p := by linarith
  have hq0 : (0:ℝ) < q := by linarith
  have hr0 : (0:ℝ) < r := by linarith
  have h1qpos : (0:ℝ) < 1 / q := by positivity
  have hppos : (0:ℝ) < (p - 1) / p := by positivity
  have hrpos : (0:ℝ) < (r - 1) / r := by positivity
  have hsubψ : AEMeasurable (fun z : G × G => ψ (z.1 - z.2)) (μ.prod μ) :=
    hψ.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_of_right_invariant μ μ)
  let F : Fin 3 → G × G → ℝ≥0∞ := ![fun z => φ z.2 ^ p * ψ (z.1 - z.2) ^ r,
      fun z => ψ (z.1 - z.2) ^ r * h z.1 ^ (q / (q - 1)),
      fun z => h z.1 ^ (q / (q - 1)) * φ z.2 ^ p]
  let P : Fin 3 → ℝ := ![1 / q, (p - 1) / p, (r - 1) / r]
  have hF0 : F 0 = fun z : G × G => φ z.2 ^ p * ψ (z.1 - z.2) ^ r := rfl
  have hF1 : F 1 = fun z : G × G => ψ (z.1 - z.2) ^ r * h z.1 ^ (q / (q - 1)) := rfl
  have hF2 : F 2 = fun z : G × G => h z.1 ^ (q / (q - 1)) * φ z.2 ^ p := rfl
  have hP0 : P 0 = 1 / q := rfl
  have hP1 : P 1 = (p - 1) / p := rfl
  have hP2 : P 2 = (r - 1) / r := rfl
  have hsum : ∑ i, P i = 1 := by
    have hp' : (p - 1) / p = 1 - 1 / p := by rw [sub_div, div_self (ne_of_gt hp0)]
    have hr' : (r - 1) / r = 1 - 1 / r := by rw [sub_div, div_self (ne_of_gt hr0)]
    rw [Fin.sum_univ_three, hP0, hP1, hP2, hp', hr']
    linarith
  have hnonneg : ∀ i ∈ Finset.univ, 0 ≤ P i := by
    intro i _
    fin_cases i
    · show 0 ≤ P 0; rw [hP0]; positivity
    · show 0 ≤ P 1; rw [hP1]; positivity
    · show 0 ≤ P 2; rw [hP2]; positivity
  have hmeasF : ∀ i ∈ Finset.univ, AEMeasurable (F i) (μ.prod μ) := by
    intro i _
    fin_cases i
    · show AEMeasurable (F 0) (μ.prod μ); rw [hF0]
      exact (hφ.comp_snd.pow_const p).mul (hsubψ.pow_const r)
    · show AEMeasurable (F 1) (μ.prod μ); rw [hF1]
      exact (hsubψ.pow_const r).mul (hh.comp_fst.pow_const (q / (q - 1)))
    · show AEMeasurable (F 2) (μ.prod μ); rw [hF2]
      exact (hh.comp_fst.pow_const (q / (q - 1))).mul (hφ.comp_snd.pow_const p)
  have hHolder := ENNReal.lintegral_prod_norm_pow_le (μ := μ.prod μ) (s := Finset.univ)
    (f := F) hmeasF hsum hnonneg
  have hLHS : ∫⁻ z, ∏ i, F i z ^ P i ∂(μ.prod μ)
      = ∫⁻ z, φ z.2 * ψ (z.1 - z.2) * h z.1 ∂(μ.prod μ) := by
    apply lintegral_congr
    intro z
    simp only [Fin.prod_univ_three, hF0, hF1, hF2, hP0, hP1, hP2]
    exact (rpow_decomp hp hq hr hpqr).symm
  have hRHS : ∏ i, (∫⁻ z, F i z ∂(μ.prod μ)) ^ P i
      = (∫⁻ x, φ x ^ p ∂μ) ^ (1 / p) * (∫⁻ x, ψ x ^ r ∂μ) ^ (1 / r)
        * (∫⁻ x, h x ^ (q / (q - 1)) ∂μ) ^ ((q - 1) / q) := by
    simp only [Fin.prod_univ_three, hF0, hF1, hF2, hP0, hP1, hP2]
    rw [lintegral_prod_snd_mul_sub (hφ.pow_const p) (hψ.pow_const r),
      lintegral_prod_sub_mul (hh.pow_const (q / (q - 1))) (hψ.pow_const r),
      lintegral_prod_mul (hh.pow_const (q / (q - 1))) (hφ.pow_const p)]
    exact rpow_combine hp hq hr hpqr
  have hconv : ∫⁻ x, (∫⁻ y, φ y * ψ (x - y) ∂μ) * h x ∂μ
      = ∫⁻ z : G × G, φ z.2 * ψ (z.1 - z.2) * h z.1 ∂(μ.prod μ) := by
    have hmeas : AEMeasurable (Function.uncurry fun x y => φ y * ψ (x - y) * h x) (μ.prod μ) :=
      ((hφ.comp_snd).mul hsubψ).mul hh.comp_fst
    rw [← lintegral_lintegral (μ := μ) (ν := μ) (f := fun x y => φ y * ψ (x - y) * h x) hmeas]
    apply lintegral_congr
    intro x
    have hinner : AEMeasurable (fun y => φ y * ψ (x - y)) μ :=
      hφ.mul (hψ.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_left_of_right_invariant μ x))
    exact (lintegral_mul_const'' (h x) hinner).symm
  calc ∫⁻ x, (∫⁻ y, φ y * ψ (x - y) ∂μ) * h x ∂μ
      = ∫⁻ z : G × G, φ z.2 * ψ (z.1 - z.2) * h z.1 ∂(μ.prod μ) := hconv
    _ = ∫⁻ z, ∏ i, F i z ^ P i ∂(μ.prod μ) := hLHS.symm
    _ ≤ ∏ i, (∫⁻ z, F i z ∂(μ.prod μ)) ^ P i := hHolder
    _ = (∫⁻ x, φ x ^ p ∂μ) ^ (1 / p) * (∫⁻ x, ψ x ^ r ∂μ) ^ (1 / r)
        * (∫⁻ x, h x ^ (q / (q - 1)) ∂μ) ^ ((q - 1) / q) := hRHS

end Trilinear



/-! ### Young's inequality for `ℝ≥0∞`-valued functions -/

/-- Young's convolution inequality for `ℝ≥0∞`-valued functions on a group with an invariant
measure, in the form needed for the convolution of an `L^r` kernel with an `L^p` function. -/
theorem eLpNorm_convolution_le_ennreal {G : Type*} [MeasurableSpace G] [AddCommGroup G]
    [MeasurableAdd₂ G] [MeasurableNeg G] [MeasurableAdd G]
    {μ : Measure G} [SigmaFinite μ]
    [μ.IsAddLeftInvariant] [μ.IsAddRightInvariant] [μ.IsNegInvariant]
    {K Φ : G → ℝ≥0∞} {p q r : ℝ} (hp : 1 ≤ p) (hr : 1 ≤ r)
    (hpqr : 1 / q = 1 / p + 1 / r - 1) (hK : AEMeasurable K μ) (hΦ : AEMeasurable Φ μ) :
    eLpNorm (fun x => ∫⁻ y, K (x - y) * Φ y ∂μ) (ENNReal.ofReal q) μ
      ≤ eLpNorm K (ENNReal.ofReal r) μ * eLpNorm Φ (ENNReal.ofReal p) μ := by
  have hWae0 : AEMeasurable (fun x => ∫⁻ y, K (x - y) * Φ y ∂μ) μ := by
    have hAM : AEMeasurable (fun z : G × G => K (z.1 - z.2) * Φ z.2) (μ.prod μ) :=
      (hK.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_of_right_invariant μ μ)).mul hΦ.comp_snd
    exact hAM.lintegral_prod_right'
  by_cases hqle : q ≤ 0
  · rw [ENNReal.ofReal_eq_zero.mpr hqle, eLpNorm_exponent_zero hWae0.aestronglyMeasurable]
    positivity
  · have hqpos : 0 < q := lt_of_not_ge hqle
    rcases eq_or_lt_of_le hp with hp1 | hp1
    · -- Case `p = 1`; then `q = r`.
      have hp1' : p = 1 := hp1.symm
      subst hp1'
      have h : (1:ℝ) / q = 1 / r := by rw [hpqr]; ring_nf
      have hqr : q = r := inv_inj.mp (by simpa only [one_div] using h)
      rw [hqr]
      have hr0 : 0 < r := by linarith
      have hAM : AEMeasurable (Function.uncurry fun x y : G => K (x - y) * Φ y) (μ.prod μ) :=
        (hK.comp_quasiMeasurePreserving
          (quasiMeasurePreserving_sub_of_right_invariant μ μ)).mul hΦ.comp_snd
      have hmin := _root_.Commons.MeasureTheory.Function.eLpNorm_lintegral_le_lintegral_eLpNorm_sfinite
        (μ := μ) (ν := μ)
        (p := ENNReal.ofReal r) (ENNReal.one_le_ofReal.mpr hr) ENNReal.ofReal_ne_top hAM
      refine hmin.trans ?_
      have hinner : ∀ y : G, eLpNorm (fun x : G => K (x - y) * Φ y) (ENNReal.ofReal r) μ
          = Φ y * eLpNorm K (ENNReal.ofReal r) μ := by
        intro y
        have hky : AEMeasurable (fun x : G => K (x - y)) μ :=
          hK.comp_quasiMeasurePreserving
            (measurePreserving_sub_right μ y).quasiMeasurePreserving
        have h1 : eLpNorm (fun x : G => Φ y * K (x - y)) (ENNReal.ofReal r) μ
            = Φ y * eLpNorm K (ENNReal.ofReal r) μ := by
          have h0 := eLpNorm_const_mul_ennreal_of_pos (f := fun x : G => K (x - y)) hky (Φ y) hr0
          rw [eLpNorm_sub_right_ennreal K y hr0] at h0
          simpa using h0
        rw [show (fun x : G => K (x - y) * Φ y) = (fun x : G => Φ y * K (x - y)) from
              funext fun x => mul_comm _ _]
        exact h1
      have hRHS : eLpNorm Φ (ENNReal.ofReal 1) μ = ∫⁻ y, Φ y ∂μ := by
        rw [ENNReal.ofReal_one, eLpNorm_one_eq_lintegral_enorm hΦ.aestronglyMeasurable]
        exact lintegral_congr fun x => enorm_eq_self _
      rw [lintegral_congr hinner, lintegral_mul_const'' _ hΦ, hRHS]
      exact le_of_eq (mul_comm _ _)
    · rcases eq_or_lt_of_le hr with hr1 | hr1
      · -- Case `r = 1`; then `q = p`.
        have hr1' : r = 1 := hr1.symm
        subst hr1'
        have h : (1:ℝ) / q = 1 / p := by rw [hpqr]; ring_nf
        have hqp : q = p := inv_inj.mp (by simpa only [one_div] using h)
        rw [hqp]
        have hp0 : 0 < p := by linarith
        have hsub : (fun x : G => ∫⁻ y, K (x - y) * Φ y ∂μ)
            = fun x => ∫⁻ y, K y * Φ (x - y) ∂μ := by
          funext x
          have h := lintegral_sub_left_eq_self (μ := μ) (fun t => K t * Φ (x - t)) x
          have h2 : (∫⁻ y, K (x - y) * Φ (x - (x - y)) ∂μ) = ∫⁻ y, K (x - y) * Φ y ∂μ :=
            lintegral_congr fun y => by rw [show x - (x - y) = y from sub_sub_cancel x y]
          rw [h2] at h
          exact h
        rw [hsub]
        have hAM : AEMeasurable (Function.uncurry fun x y : G => K y * Φ (x - y)) (μ.prod μ) :=
          hK.comp_snd.mul (hΦ.comp_quasiMeasurePreserving
            (quasiMeasurePreserving_sub_of_right_invariant μ μ))
        have hmin := _root_.Commons.MeasureTheory.Function.eLpNorm_lintegral_le_lintegral_eLpNorm_sfinite
          (μ := μ) (ν := μ)
          (p := ENNReal.ofReal p) (ENNReal.one_le_ofReal.mpr hp) ENNReal.ofReal_ne_top hAM
        refine hmin.trans ?_
        have hinner : ∀ y : G, eLpNorm (fun x : G => K y * Φ (x - y)) (ENNReal.ofReal p) μ
            = K y * eLpNorm Φ (ENNReal.ofReal p) μ := by
          intro y
          have hfy : AEMeasurable (fun x : G => Φ (x - y)) μ :=
            hΦ.comp_quasiMeasurePreserving
              (measurePreserving_sub_right μ y).quasiMeasurePreserving
          have h0 := eLpNorm_const_mul_ennreal_of_pos (f := fun x : G => Φ (x - y)) hfy (K y) hp0
          rw [eLpNorm_sub_right_ennreal Φ y hp0] at h0
          simpa using h0
        have hL : eLpNorm K (ENNReal.ofReal 1) μ = ∫⁻ y, K y ∂μ := by
          rw [ENNReal.ofReal_one, eLpNorm_one_eq_lintegral_enorm hK.aestronglyMeasurable]
          exact lintegral_congr fun x => enorm_eq_self _
        rw [lintegral_congr hinner, lintegral_mul_const'' _ hK, hL]
      · -- Main case `1 < p`, `1 < r`.
        have hq1 : 1 < q := by
          have hlt : (1:ℝ) / q < 1 := by
            rw [hpqr]
            have h1 : (1:ℝ) / p < 1 := (div_lt_one (by linarith : (0:ℝ) < p)).mpr hp1
            have h2 : (1:ℝ) / r < 1 := (div_lt_one (by linarith : (0:ℝ) < r)).mpr hr1
            linarith
          exact (div_lt_one hqpos).mp hlt
        have hp0 : 0 < p := by linarith
        have hr0 : 0 < r := by linarith
        set W : G → ℝ≥0∞ := fun x => ∫⁻ y, K (x - y) * Φ y ∂μ with hWdef
        have hWae : AEMeasurable W μ := by
          have hAM : AEMeasurable (fun z : G × G => K (z.1 - z.2) * Φ z.2) (μ.prod μ) :=
            (hK.comp_quasiMeasurePreserving
              (quasiMeasurePreserving_sub_of_right_invariant μ μ)).mul hΦ.comp_snd
          have h := hAM.lintegral_prod_right'
          simpa only [hWdef] using h
        have hdual : ∀ g : G → ℝ≥0∞, AEMeasurable g μ →
            ∫⁻ x, W x * g x ∂μ ≤ ((∫⁻ x, K x ^ r ∂μ) ^ (1 / r) * (∫⁻ x, Φ x ^ p ∂μ) ^ (1 / p))
              * (∫⁻ x, g x ^ (q / (q - 1)) ∂μ) ^ ((q - 1) / q) := by
          intro g hg
          have hpqr' : 1 / p + 1 / r = 1 + 1 / q := by linarith [hpqr]
          have hA := lintegral_convolution_mul_le (μ := μ) hp1 hq1 hr1 hpqr'
            (φ := Φ) (ψ := K) hΦ hK hg
          calc ∫⁻ x, W x * g x ∂μ
              = ∫⁻ x, (∫⁻ y, Φ y * K (x - y) ∂μ) * g x ∂μ := by
                apply lintegral_congr; intro x
                rw [hWdef]
                congr 1
                exact lintegral_congr fun y => mul_comm (K (x - y)) (Φ y)
            _ ≤ (∫⁻ x, Φ x ^ p ∂μ) ^ (1 / p) * (∫⁻ x, K x ^ r ∂μ) ^ (1 / r)
                  * (∫⁻ x, g x ^ (q / (q - 1)) ∂μ) ^ ((q - 1) / q) := hA
            _ = ((∫⁻ x, K x ^ r ∂μ) ^ (1 / r) * (∫⁻ x, Φ x ^ p ∂μ) ^ (1 / p))
                  * (∫⁻ x, g x ^ (q / (q - 1)) ∂μ) ^ ((q - 1) / q) := by ring
        have hbound : (∫⁻ x, W x ^ q ∂μ) ^ (1 / q)
            ≤ (∫⁻ x, K x ^ r ∂μ) ^ (1 / r) * (∫⁻ x, Φ x ^ p ∂μ) ^ (1 / p) :=
          lintegral_rpow_le_of_forall_mul_le hq1 hWae hdual
        have hq0 : ENNReal.ofReal q ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hqpos
        have hqt : ENNReal.ofReal q ≠ ⊤ := ENNReal.ofReal_ne_top
        have hr0' : ENNReal.ofReal r ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hr0
        have hrt : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
        have hp0' : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
        have hpt : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
        change eLpNorm W (ENNReal.ofReal q) μ
          ≤ eLpNorm K (ENNReal.ofReal r) μ * eLpNorm Φ (ENNReal.ofReal p) μ
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqt hWae.aestronglyMeasurable,
            eLpNorm_eq_lintegral_rpow_enorm_toReal hr0' hrt hK.aestronglyMeasurable,
            eLpNorm_eq_lintegral_rpow_enorm_toReal hp0' hpt hΦ.aestronglyMeasurable]
        simp only [ENNReal.toReal_ofReal hqpos.le, ENNReal.toReal_ofReal hr0.le,
          ENNReal.toReal_ofReal hp0.le, enorm_eq_self]
        exact hbound



/-! ### Young's inequality for convolutions -/

theorem eLpNorm_convolution_le {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (k : E → ℝ) (f : E → F) (p q r : ℝ) (hp : 1 ≤ p) (hr : 1 ≤ r) (hq : 1 ≤ q)
    (hpqr : 1 / q = 1 / p + 1 / r - 1)
    (hk : MeasureTheory.MemLp k (ENNReal.ofReal r) MeasureTheory.volume)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal p) MeasureTheory.volume) :
    MeasureTheory.eLpNorm (fun x : E => ∫ y, k (x - y) • f y) (ENNReal.ofReal q) MeasureTheory.volume
      ≤ MeasureTheory.eLpNorm k (ENNReal.ofReal r) MeasureTheory.volume
        * MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.volume := by
  set K : E → ℝ≥0∞ := fun z => ‖k z‖ₑ with hKdef
  set Φ : E → ℝ≥0∞ := fun y => ‖f y‖ₑ with hΦdef
  have hKae : AEMeasurable K volume := by
    rw [hKdef]; exact hk.aestronglyMeasurable.enorm
  have hFae : AEMeasurable Φ volume := by
    rw [hΦdef]; exact hf.aestronglyMeasurable.enorm
  have h1 : ∀ x : E, ‖(∫ y, k (x - y) • f y)‖ₑ ≤ ∫⁻ y, K (x - y) * Φ y := by
    intro x
    refine (enorm_integral_le_lintegral_enorm (fun y => k (x - y) • f y)).trans (le_of_eq ?_)
    apply lintegral_congr; intro y
    rw [enorm_smul, hKdef, hΦdef]
  have hconv_meas : AEStronglyMeasurable (fun x : E => ∫ y, k (x - y) • f y) volume := by
    have hF : AEStronglyMeasurable (fun z : E × E => k (z.1 - z.2) • f z.2)
        ((volume : Measure E).prod volume) :=
      (hk.aestronglyMeasurable.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_of_right_invariant volume volume)).smul
        hf.aestronglyMeasurable.comp_snd
    exact hF.integral_prod_right'
  calc MeasureTheory.eLpNorm (fun x : E => ∫ y, k (x - y) • f y) (ENNReal.ofReal q)
          MeasureTheory.volume
      ≤ MeasureTheory.eLpNorm (fun x : E => ∫⁻ y, K (x - y) * Φ y) (ENNReal.ofReal q)
          MeasureTheory.volume :=
        eLpNorm_mono_enorm_ae hconv_meas (Filter.Eventually.of_forall h1)
    _ ≤ MeasureTheory.eLpNorm K (ENNReal.ofReal r) MeasureTheory.volume
          * MeasureTheory.eLpNorm Φ (ENNReal.ofReal p) MeasureTheory.volume :=
        eLpNorm_convolution_le_ennreal hp hr hpqr hKae hFae
    _ = MeasureTheory.eLpNorm k (ENNReal.ofReal r) MeasureTheory.volume
          * MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.volume := by
        simp only [hKdef, hΦdef, MeasureTheory.eLpNorm_enorm _ hk.aestronglyMeasurable,
          MeasureTheory.eLpNorm_enorm _ hf.aestronglyMeasurable]


end Commons.Analysis.Convolution
