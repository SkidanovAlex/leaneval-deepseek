import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Commons.Analysis.Integral.eLpNorm_integral_le_lintegral_eLpNorm_sfinite
import Submission.Commons.Analysis.Measure.lp_norm_log_convex

namespace Commons.Measure.Integral

open MeasureTheory
open scoped ENNReal

/-!
# Young's inequality for convolutions with real exponents

This file proves `Commons.Measure.Integral.integral_convolution_rpow_le`, i.e. Young's
inequality for convolutions on `ℝ^k` with real exponents `p, q, r > 1` satisfying
`1/p + 1/r = 1 + 1/q`, together with the auxilliary lemmas used on the way.
-/

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

private lemma iSup_inf_natCast_eq_self (a : ℝ≥0∞) : (⨆ n : ℕ, a ⊓ (n : ℝ≥0∞)) = a := by
  rcases eq_or_ne a ⊤ with rfl | ha
  · rw [show (⨆ n : ℕ, (⊤ : ℝ≥0∞) ⊓ (n : ℝ≥0∞)) = ⨆ n : ℕ, (n : ℝ≥0∞) from
      iSup_congr fun n => by simp]
    exact ENNReal.iSup_natCast
  · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt ha
    refine le_antisymm (iSup_le fun m => inf_le_left) ?_
    refine le_trans (le_of_eq (inf_eq_left.mpr hn.le).symm) ?_
    exact le_iSup (fun m : ℕ => a ⊓ (m : ℝ≥0∞)) n

private lemma iSup_inf_natCast_rpow {a : ℝ≥0∞} {q : ℝ} (hq : 0 < q) :
    (⨆ n : ℕ, (a ⊓ (n : ℝ≥0∞)) ^ q) = a ^ q := by
  conv_rhs => rw [← iSup_inf_natCast_eq_self a]
  exact (Commons.Analysis.Integral.ENNReal.iSup_rpow hq).symm

private lemma lintegral_rpow_le_of_forall_mul_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [SigmaFinite μ] {q : ℝ} (hq : 1 < q) {F : α → ℝ≥0∞} (hF : AEMeasurable F μ) {C : ℝ≥0∞}
    (h : ∀ g : α → ℝ≥0∞, AEMeasurable g μ →
      ∫⁻ x, F x * g x ∂μ ≤ C * (∫⁻ x, g x ^ (q / (q - 1)) ∂μ) ^ ((q - 1) / q)) :
    (∫⁻ x, F x ^ q ∂μ) ^ (1 / q) ≤ C := by
  have hq0 : 0 < q := by linarith
  have hq1 : 0 < q - 1 := by linarith
  have hq' : 0 < q / (q - 1) := by positivity
  have hexp : (q - 1) * (q / (q - 1)) = q := by field_simp
  set T : ℕ → α → ℝ≥0∞ :=
    fun n => (spanningSets μ n).indicator (fun x => (F x ⊓ (n : ℝ≥0∞)) ^ q) with hTdef
  set G : ℕ → α → ℝ≥0∞ :=
    fun n => (spanningSets μ n).indicator (fun x => (F x ⊓ (n : ℝ≥0∞)) ^ (q - 1)) with hGdef
  have hTmeas : ∀ n, AEMeasurable (T n) μ := fun n => by
    rw [hTdef]
    exact ((hF.inf aemeasurable_const).pow_const q).indicator (measurableSet_spanningSets μ n)
  have hGmeas : ∀ n, AEMeasurable (G n) μ := fun n => by
    rw [hGdef]
    exact ((hF.inf aemeasurable_const).pow_const (q - 1)).indicator
      (measurableSet_spanningSets μ n)
  have hTleFG : ∀ n, T n ≤ F * G n := by
    intro n x
    by_cases hx : x ∈ spanningSets μ n
    · simp only [hTdef, hGdef, Set.indicator_of_mem hx, Pi.mul_apply]
      have h1 : (F x ⊓ (n : ℝ≥0∞)) ^ q
          = (F x ⊓ (n : ℝ≥0∞)) ^ (q - 1) * (F x ⊓ (n : ℝ≥0∞)) := by
        have hqeq : q = (q - 1) + 1 := by ring
        conv_lhs => rw [hqeq]
        rw [ENNReal.rpow_add_of_nonneg (q - 1) 1 (by linarith) (by norm_num),
          ENNReal.rpow_one]
      calc (F x ⊓ (n : ℝ≥0∞)) ^ q
          = (F x ⊓ (n : ℝ≥0∞)) ^ (q - 1) * (F x ⊓ (n : ℝ≥0∞)) := h1
        _ ≤ (F x ⊓ (n : ℝ≥0∞)) ^ (q - 1) * F x := mul_le_mul' le_rfl inf_le_left
        _ = F x * (F x ⊓ (n : ℝ≥0∞)) ^ (q - 1) := mul_comm _ _
    · simp only [hTdef, hGdef, Set.indicator_of_notMem hx, Pi.mul_apply, mul_zero,
        le_refl]
  have hGpow : ∀ n x, G n x ^ (q / (q - 1)) = T n x := by
    intro n x
    by_cases hx : x ∈ spanningSets μ n
    · simp only [hTdef, hGdef, Set.indicator_of_mem hx, ← ENNReal.rpow_mul, hexp]
    · simp only [hTdef, hGdef, Set.indicator_of_notMem hx, ENNReal.zero_rpow_of_pos hq']
  have hTmono : ∀ᵐ x ∂μ, Monotone fun n => T n x := by
    refine Filter.Eventually.of_forall fun x n m hnm => ?_
    by_cases hx : x ∈ spanningSets μ n
    · have hx' : x ∈ spanningSets μ m := monotone_spanningSets μ hnm hx
      simp only [hTdef, Set.indicator_of_mem hx, Set.indicator_of_mem hx']
      exact ENNReal.rpow_le_rpow (inf_le_inf_left _ (by exact_mod_cast hnm)) hq0.le
    · simp only [hTdef, Set.indicator_of_notMem hx]
      exact zero_le
  have hTsup : ∀ x, (⨆ n, T n x) = F x ^ q := by
    intro x
    refine le_antisymm (iSup_le fun n => ?_) ?_
    · by_cases hx : x ∈ spanningSets μ n
      · simp only [hTdef, Set.indicator_of_mem hx]
        exact ENNReal.rpow_le_rpow inf_le_left hq0.le
      · simp only [hTdef, Set.indicator_of_notMem hx]
        exact zero_le
    · have hxu : x ∈ ⋃ i, spanningSets μ i := by
        rw [iUnion_spanningSets μ]
        trivial
      rw [Set.mem_iUnion] at hxu
      obtain ⟨k, hk⟩ := hxu
      have hbig : ∀ n : ℕ, (F x ⊓ (n : ℝ≥0∞)) ^ q ≤ ⨆ m, T m x := by
        intro n
        have hx' : x ∈ spanningSets μ (max n k) := monotone_spanningSets μ (le_max_right n k) hk
        have hTeq : T (max n k) x = (F x ⊓ ((max n k : ℕ) : ℝ≥0∞)) ^ q := by
          simp only [hTdef, Set.indicator_of_mem hx']
        calc (F x ⊓ (n : ℝ≥0∞)) ^ q
            ≤ (F x ⊓ ((max n k : ℕ) : ℝ≥0∞)) ^ q :=
              ENNReal.rpow_le_rpow (inf_le_inf_left _ (by exact_mod_cast le_max_left n k)) hq0.le
          _ = T (max n k) x := hTeq.symm
          _ ≤ ⨆ m, T m x := le_iSup (fun m : ℕ => T m x) (max n k)
      rw [← iSup_inf_natCast_rpow hq0]
      exact iSup_le hbig
  have hfin : ∀ n, ∫⁻ x, T n x ∂μ < ⊤ := by
    intro n
    have hle : ∫⁻ x, T n x ∂μ ≤ (n : ℝ≥0∞) ^ q * μ (spanningSets μ n) := by
      have h1 : ∫⁻ x, T n x ∂μ
          ≤ ∫⁻ x, (spanningSets μ n).indicator (fun _ => (n : ℝ≥0∞) ^ q) x ∂μ :=
        lintegral_mono fun x => by
          by_cases hx : x ∈ spanningSets μ n
          · rw [Set.indicator_of_mem hx]
            simp only [hTdef, Set.indicator_of_mem hx]
            exact ENNReal.rpow_le_rpow inf_le_right hq0.le
          · rw [Set.indicator_of_notMem hx]
            simp only [hTdef, Set.indicator_of_notMem hx, le_refl]
      rw [lintegral_indicator_const (measurableSet_spanningSets μ n)] at h1
      exact h1
    exact lt_of_le_of_lt hle (ENNReal.mul_lt_top
      (lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_nonneg hq0.le (ENNReal.natCast_lt_top n).ne))
      (measure_spanningSets_lt_top μ n))
  have key : ∀ n, ∫⁻ x, T n x ∂μ ≤ C * (∫⁻ x, T n x ∂μ) ^ ((q - 1) / q) := by
    intro n
    calc ∫⁻ x, T n x ∂μ ≤ ∫⁻ x, F x * G n x ∂μ := lintegral_mono (hTleFG n)
      _ ≤ C * (∫⁻ x, G n x ^ (q / (q - 1)) ∂μ) ^ ((q - 1) / q) := h (G n) (hGmeas n)
      _ = C * (∫⁻ x, T n x ∂μ) ^ ((q - 1) / q) := by
          rw [lintegral_congr fun x => hGpow n x]
  have key' : ∀ n, (∫⁻ x, T n x ∂μ) ^ (1 / q) ≤ C := by
    intro n
    rcases eq_or_ne (∫⁻ x, T n x ∂μ) 0 with h0 | h0
    · rw [h0, ENNReal.zero_rpow_of_pos (by positivity : (0:ℝ) < 1 / q)]
      exact zero_le
    · have hne : (∫⁻ x, T n x ∂μ) ≠ ⊤ := (hfin n).ne
      have hpos : 0 < ∫⁻ x, T n x ∂μ := lt_of_le_of_ne zero_le h0.symm
      have hA : (∫⁻ x, T n x ∂μ) ^ (1 / q) * (∫⁻ x, T n x ∂μ) ^ ((q - 1) / q)
          = ∫⁻ x, T n x ∂μ := by
        rw [← ENNReal.rpow_add_of_nonneg (1 / q) ((q - 1) / q) (by positivity) (by positivity)]
        have h1 : 1 / q + (q - 1) / q = 1 := by
          rw [← add_div, add_sub_cancel, div_self (ne_of_gt hq0)]
        rw [h1, ENNReal.rpow_one]
      have hgoal : (∫⁻ x, T n x ∂μ) ^ (1 / q) * (∫⁻ x, T n x ∂μ) ^ ((q - 1) / q)
          ≤ C * (∫⁻ x, T n x ∂μ) ^ ((q - 1) / q) := by
        rw [hA]
        exact key n
      exact (ENNReal.mul_le_mul_iff_left (ENNReal.rpow_pos hpos hne).ne'
        (ENNReal.rpow_ne_top_of_nonneg (by positivity) hne)).mp hgoal
  calc (∫⁻ x, F x ^ q ∂μ) ^ (1 / q)
      = (⨆ n, ∫⁻ x, T n x ∂μ) ^ (1 / q) := by
        rw [← lintegral_iSup' hTmeas hTmono, lintegral_congr fun x => hTsup x]
    _ = ⨆ n, (∫⁻ x, T n x ∂μ) ^ (1 / q) :=
        Commons.Analysis.Integral.ENNReal.iSup_rpow (by positivity)
    _ ≤ C := iSup_le key'


/-- **Young's inequality for convolutions** with real exponents on `ℝᵏ`: if
`1/p + 1/r = 1 + 1/q` with `p, q, r > 1`, and `f, g` are AEStronglyMeasurable (this
hypothesis is necessary: `Integrable (fun x => ‖f x‖^p)` alone does not give
measurability of `f`), then `f ⋆ g` is `L^q` with `‖f ⋆ g‖_q ≤ ‖f‖_p ‖g‖_r`. -/
theorem integral_convolution_rpow_le {k : ℕ} {p q r : ℝ} (hp : 1 < p) (hq : 1 < q) (hr : 1 < r)
    (hpqr : 1 / p + 1 / r = 1 + 1 / q)
    {f g : EuclideanSpace ℝ (Fin k) → ℂ}
    (hfm : AEStronglyMeasurable f volume) (hgm : AEStronglyMeasurable g volume)
    (hf : Integrable (fun x => ‖f x‖ ^ p) volume)
    (hg : Integrable (fun x => ‖g x‖ ^ r) volume) :
    Integrable (fun x => ‖∫ y, f y * g (x - y)‖ ^ q) volume ∧
      (∫ x, ‖∫ y, f y * g (x - y)‖ ^ q) ^ (1 / q)
        ≤ (∫ x, ‖f x‖ ^ p) ^ (1 / p) * (∫ x, ‖g x‖ ^ r) ^ (1 / r) := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hr0 : 0 < r := by linarith
  set F : EuclideanSpace ℝ (Fin k) → ℂ := fun x => ∫ y, f y * g (x - y) with hFdef
  change Integrable (fun x => ‖F x‖ ^ q) volume ∧
      (∫ x, ‖F x‖ ^ q) ^ (1 / q)
        ≤ (∫ x, ‖f x‖ ^ p) ^ (1 / p) * (∫ x, ‖g x‖ ^ r) ^ (1 / r)
  have hFmeas : AEStronglyMeasurable F volume := by
    have h1 : AEStronglyMeasurable
        (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) =>
          f p.2 * g (p.1 - p.2)) (volume.prod volume) := by
      simpa only [ContinuousLinearMap.mul_apply'] using
        (hfm.convolution_integrand (L := ContinuousLinearMap.mul ℂ ℂ) hgm)
    simpa only [hFdef] using h1.integral_prod_right'
  set φ : EuclideanSpace ℝ (Fin k) → ℝ≥0∞ := fun x => ‖f x‖ₑ with hφdef
  set ψ : EuclideanSpace ℝ (Fin k) → ℝ≥0∞ := fun x => ‖g x‖ₑ with hψdef
  set W : EuclideanSpace ℝ (Fin k) → ℝ≥0∞ := fun x => ∫⁻ y, φ y * ψ (x - y) ∂volume
    with hWdef
  have hφ : AEMeasurable φ volume := by
    rw [hφdef]; exact hfm.aemeasurable.enorm
  have hψ : AEMeasurable ψ volume := by
    rw [hψdef]; exact hgm.aemeasurable.enorm
  have hsubψ : AEMeasurable
      (fun z : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) => ψ (z.1 - z.2))
      (volume.prod volume) :=
    hψ.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_of_right_invariant volume volume)
  have hWmeas : AEMeasurable W volume := by
    have huncurry : AEMeasurable
        (fun z : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) =>
          φ z.2 * ψ (z.1 - z.2)) (volume.prod volume) := hφ.comp_snd.mul hsubψ
    have h := huncurry.lintegral_prod_right'
    simpa only [hWdef] using h
  have hFW : ∀ x, ‖F x‖ₑ ≤ W x := by
    intro x
    have h := enorm_integral_le_lintegral_enorm (μ := volume) (fun y => f y * g (x - y))
    simp only [enorm_mul] at h
    simpa only [hFdef, hφdef, hψdef, hWdef] using h
  have htri : ∀ h : EuclideanSpace ℝ (Fin k) → ℝ≥0∞, AEMeasurable h volume →
      ∫⁻ x, W x * h x ∂volume ≤
        (∫⁻ x, φ x ^ p ∂volume) ^ (1 / p) * (∫⁻ x, ψ x ^ r ∂volume) ^ (1 / r)
          * (∫⁻ x, h x ^ (q / (q - 1)) ∂volume) ^ ((q - 1) / q) := by
    intro h hh
    have h1 := lintegral_convolution_mul_le (μ := volume) hp hq hr hpqr hφ hψ hh
    simpa only [hWdef] using h1
  have hbound : (∫⁻ x, W x ^ q ∂volume) ^ (1 / q) ≤
      (∫⁻ x, φ x ^ p ∂volume) ^ (1 / p) * (∫⁻ x, ψ x ^ r ∂volume) ^ (1 / r) :=
    lintegral_rpow_le_of_forall_mul_le hq hWmeas htri
  have hmain : (∫⁻ x, ‖F x‖ₑ ^ q ∂volume) ^ (1 / q) ≤
      (∫⁻ x, φ x ^ p ∂volume) ^ (1 / p) * (∫⁻ x, ψ x ^ r ∂volume) ^ (1 / r) := by
    have h2 : (∫⁻ x, ‖F x‖ₑ ^ q ∂volume) ≤ ∫⁻ x, W x ^ q ∂volume :=
      lintegral_mono fun x => ENNReal.rpow_le_rpow (hFW x) hq0.le
    exact (ENNReal.rpow_le_rpow h2 (by positivity)).trans hbound
  have hA0 : 0 ≤ ∫ x, ‖f x‖ ^ p ∂volume :=
    integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) p
  have hB0 : 0 ≤ ∫ x, ‖g x‖ ^ r ∂volume :=
    integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) r
  have hA : ∫⁻ x, φ x ^ p ∂volume = ENNReal.ofReal (∫ x, ‖f x‖ ^ p ∂volume) := by
    simpa only [hφdef] using
      Commons.Analysis.Measure.lintegral_enorm_rpow_eq_ofReal volume hp0 (f := f) hf
  have hB : ∫⁻ x, ψ x ^ r ∂volume = ENNReal.ofReal (∫ x, ‖g x‖ ^ r ∂volume) := by
    simpa only [hψdef] using
      Commons.Analysis.Measure.lintegral_enorm_rpow_eq_ofReal volume hr0 (f := g) hg
  have hC : (∫⁻ x, φ x ^ p ∂volume) ^ (1 / p) * (∫⁻ x, ψ x ^ r ∂volume) ^ (1 / r)
      = ENNReal.ofReal ((∫ x, ‖f x‖ ^ p ∂volume) ^ (1 / p)
          * (∫ x, ‖g x‖ ^ r ∂volume) ^ (1 / r)) := by
    rw [hA, hB, ENNReal.ofReal_rpow_of_nonneg hA0 (by positivity),
      ENNReal.ofReal_rpow_of_nonneg hB0 (by positivity),
      ENNReal.ofReal_mul (p := (∫ x, ‖f x‖ ^ p ∂volume) ^ (1 / p))
        (q := (∫ x, ‖g x‖ ^ r ∂volume) ^ (1 / r))
        (Real.rpow_nonneg hA0 (1 / p))]
  have hmain' : (∫⁻ x, ‖F x‖ₑ ^ q ∂volume) ^ (1 / q) ≤
      ENNReal.ofReal ((∫ x, ‖f x‖ ^ p ∂volume) ^ (1 / p)
          * (∫ x, ‖g x‖ ^ r ∂volume) ^ (1 / r)) := by
    rw [← hC]; exact hmain
  have hFq_lt : ∫⁻ x, ‖F x‖ₑ ^ q ∂volume < ⊤ := by
    have hle := ENNReal.rpow_le_rpow hmain' hq0.le
    have he : ((∫⁻ x, ‖F x‖ₑ ^ q ∂volume) ^ (1 / q)) ^ q
        = ∫⁻ x, ‖F x‖ₑ ^ q ∂volume := by
      rw [← ENNReal.rpow_mul, one_div_mul_cancel (ne_of_gt hq0), ENNReal.rpow_one]
    rw [he] at hle
    refine lt_of_le_of_lt hle ?_
    exact lt_top_iff_ne_top.mpr
      (ENNReal.rpow_ne_top_of_nonneg hq0.le ENNReal.ofReal_lt_top.ne)
  have hms : AEStronglyMeasurable (fun x => ‖F x‖ ^ q) volume :=
    ((Real.continuous_rpow_const hq0.le).measurable.comp_aemeasurable
      hFmeas.norm.aemeasurable).aestronglyMeasurable
  have hInt : Integrable (fun x => ‖F x‖ ^ q) volume := by
    refine ⟨hms, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have heq : (fun x => ‖‖F x‖ ^ q‖ₑ) = fun x => ‖F x‖ₑ ^ q := by
      funext x
      have h1 : ‖‖F x‖ ^ q‖ₑ = ENNReal.ofReal (‖F x‖ ^ q) := by
        rw [← ofReal_norm, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) q)]
      have h2 : ‖F x‖ₑ ^ q = ENNReal.ofReal (‖F x‖ ^ q) := by
        rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq0.le]
      rw [h1, h2]
    rw [heq]
    exact hFq_lt
  have htoReal : (∫⁻ x, ‖F x‖ₑ ^ q ∂volume).toReal = ∫ x, ‖F x‖ ^ q ∂volume := by
    have heq : (fun x => ‖F x‖ₑ ^ q) = fun x => ENNReal.ofReal (‖F x‖ ^ q) := by
      funext x
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq0.le]
    rw [heq]
    exact (integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) q) hms).symm
  refine ⟨hInt, ?_⟩
  calc (∫ x, ‖F x‖ ^ q ∂volume) ^ (1 / q)
      = ((∫⁻ x, ‖F x‖ₑ ^ q ∂volume) ^ (1 / q)).toReal := by
        rw [← ENNReal.toReal_rpow, htoReal]
    _ ≤ (ENNReal.ofReal ((∫ x, ‖f x‖ ^ p ∂volume) ^ (1 / p)
          * (∫ x, ‖g x‖ ^ r ∂volume) ^ (1 / r))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_lt_top.ne hmain'
    _ = (∫ x, ‖f x‖ ^ p ∂volume) ^ (1 / p)
          * (∫ x, ‖g x‖ ^ r ∂volume) ^ (1 / r) :=
        ENNReal.toReal_ofReal (mul_nonneg (Real.rpow_nonneg hA0 _) (Real.rpow_nonneg hB0 _))

end Commons.Measure.Integral