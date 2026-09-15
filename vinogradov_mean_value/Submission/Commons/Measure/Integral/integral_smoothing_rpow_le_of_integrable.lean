import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique

namespace Commons.Measure.Integral

open MeasureTheory
open scoped ENNReal

section Helpers

/-- If `u ↦ (1 + u/R)^{-s}` with `s > 0`, rewrite as `R^s * (R+u)^{-s}`. -/
private lemma one_add_div_rpow_neg {R u s : ℝ} (hR : 0 < R) (hu : 0 ≤ u) :
    (1 + u / R) ^ (-s) = R ^ s * (R + u) ^ (-s) := by
  have h1 : (1 + u / R) = (R + u) / R := by field_simp
  have hRu : 0 < R + u := by linarith
  rw [h1, Real.div_rpow hRu.le hR.le, Real.rpow_neg hR.le, div_eq_mul_inv, inv_inv]
  ring

private lemma rpow_s_mul_inv_pow {R s : ℝ} (hR : 0 < R) (n : ℕ) :
    R ^ s * (R ^ n)⁻¹ = R ^ (s - n) := by
  rw [← Real.rpow_natCast R n, ← Real.rpow_neg hR.le (n : ℝ), ← Real.rpow_add hR s (-(n : ℝ))]
  congr 1

/-- The scaled smoothing kernel `z ↦ (1 + ‖z‖/R)^{-s}/R^n` (with `n = dim`) is integrable when
`s` exceeds the dimension. -/
theorem integrable_one_add_norm_div_pow {n : ℕ} {s R : ℝ} (hs : (n : ℝ) < s) (hR : 0 < R) :
    Integrable (fun z : EuclideanSpace ℝ (Fin n) => (1 + ‖z‖ / R) ^ (-s) / R ^ n)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hs0 : 0 < s := lt_of_le_of_lt (Nat.cast_nonneg n) hs
  have hfk : Integrable (fun z : EuclideanSpace ℝ (Fin n) => (1 + ‖z‖) ^ (-s)) volume := by
    have h := integrable_one_add_norm (E := EuclideanSpace ℝ (Fin n))
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) (r := s) ?_
    · simpa using h
    · simpa [finrank_euclideanSpace] using hs
  have hm0 : 0 < min R 1 := lt_min hR one_pos
  refine (hfk.const_mul (R ^ (s - n) * (min R 1) ^ (-s))).mono' ?_ ?_
  · apply Measurable.aestronglyMeasurable
    fun_prop
  · refine Filter.Eventually.of_forall (fun z => ?_)
    have hzpos : 0 < 1 + ‖z‖ := by positivity
    have hRpos : 0 ≤ (1 + ‖z‖ / R) ^ (-s) / R ^ n := by positivity
    rw [Real.norm_of_nonneg hRpos]
    have hfac : (1 + ‖z‖ / R) ^ (-s) / R ^ n = R ^ (s - n) * (R + ‖z‖) ^ (-s) := by
      rw [one_add_div_rpow_neg hR (norm_nonneg z), div_eq_mul_inv]
      rw [show R ^ s * (R + ‖z‖) ^ (-s) * (R ^ n)⁻¹
            = (R ^ s * (R ^ n)⁻¹) * (R + ‖z‖) ^ (-s) by ring,
        rpow_s_mul_inv_pow hR n]
    rw [hfac]
    have hge : min R 1 * (1 + ‖z‖) ≤ R + ‖z‖ := by
      rcases le_total R 1 with h | h
      · rw [min_eq_left h]
        nlinarith [norm_nonneg z]
      · rw [min_eq_right h]
        linarith
    have hgepos : 0 < min R 1 * (1 + ‖z‖) := mul_pos hm0 hzpos
    have step : (R + ‖z‖) ^ (-s) ≤ (min R 1 * (1 + ‖z‖)) ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos hgepos hge (neg_nonpos.mpr hs0.le)
    have hsplit : (min R 1 * (1 + ‖z‖)) ^ (-s) = (min R 1) ^ (-s) * (1 + ‖z‖) ^ (-s) := by
      rw [Real.mul_rpow hm0.le hzpos.le]
    rw [hsplit] at step
    calc R ^ (s - n) * (R + ‖z‖) ^ (-s)
        ≤ R ^ (s - n) * ((min R 1) ^ (-s) * (1 + ‖z‖) ^ (-s)) := by
          exact mul_le_mul_of_nonneg_left step (Real.rpow_nonneg hR.le _)
      _ = R ^ (s - n) * (min R 1) ^ (-s) * (1 + ‖z‖) ^ (-s) := by ring

/-- Scaling identity for the smoothing kernel. -/
theorem integral_one_add_norm_div_pow {n : ℕ} {s R : ℝ} (hR : 0 < R) :
    (∫ z : EuclideanSpace ℝ (Fin n), (1 + ‖z‖ / R) ^ (-s) / R ^ n)
      = ∫ v : EuclideanSpace ℝ (Fin n), (1 + ‖v‖) ^ (-s) := by
  have hcomp := Measure.integral_comp_inv_smul_of_nonneg
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (f := fun v : EuclideanSpace ℝ (Fin n) => (1 + ‖v‖) ^ (-s)) hR.le
  simp only [finrank_euclideanSpace, Fintype.card_fin] at hcomp
  have hnorm : ∀ x : EuclideanSpace ℝ (Fin n), (1 + ‖R⁻¹ • x‖) ^ (-s) = (1 + ‖x‖ / R) ^ (-s) := by
    intro x
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ R⁻¹), inv_mul_eq_div]
  simp only [hnorm] at hcomp
  rw [smul_eq_mul] at hcomp
  have hfun : (fun z : EuclideanSpace ℝ (Fin n) => (1 + ‖z‖ / R) ^ (-s) / R ^ n)
      = fun z => (R ^ n)⁻¹ * (1 + ‖z‖ / R) ^ (-s) := by
    funext z; rw [div_eq_inv_mul]
  rw [hfun, MeasureTheory.integral_const_mul, hcomp]
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero n hR.ne'), one_mul]

/-- `ℝ≥0∞.ofReal` of a Bochner integral of a nonnegative function is bounded by the lower
Lebesgue integral of the `ofReal`. -/
private lemma ofReal_integral_le_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : AEStronglyMeasurable f μ) (h : 0 ≤ᵐ[μ] f) :
    ENNReal.ofReal (∫ a, f a ∂μ) ≤ ∫⁻ a, ENNReal.ofReal (f a) ∂μ := by
  rw [integral_eq_lintegral_of_nonneg_ae h hf]
  exact ENNReal.ofReal_toReal_le

/-- Weighted Hölder inequality in `ℝ≥0∞`: for `q ≥ 1`,
`(∫ f g)^q ≤ (∫ f^q g) * (∫ g)^(q-1)`. -/
lemma lintegral_mul_pow_le {α} [MeasurableSpace α] {ν : Measure α} {q : ℝ} (hq : 1 ≤ q)
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f ν) (hg : AEMeasurable g ν) :
    (∫⁻ u, f u * g u ∂ν) ^ q ≤ (∫⁻ u, f u ^ q * g u ∂ν) * (∫⁻ u, g u ∂ν) ^ (q - 1) := by
  rcases eq_or_lt_of_le hq with h1 | hq1
  · subst h1
    simp
  · have hq0 : 0 < q := by linarith
    have hp : 0 ≤ 1 / q := by positivity
    have hr : 0 ≤ (q - 1) / q := by positivity
    have hpq : 1 / q + (q - 1) / q = 1 := by field_simp; ring
    have hF : AEMeasurable (fun u => f u ^ q * g u) ν := (hf.pow_const q).mul hg
    have hHolder := ENNReal.lintegral_mul_norm_pow_le hF hg hp hr hpq
    have hreal : (fun u => (f u ^ q * g u) ^ (1 / q) * g u ^ ((q - 1) / q))
        = fun u => f u * g u := by
      funext u
      rw [ENNReal.mul_rpow_of_nonneg _ _ hp]
      rw [← ENNReal.rpow_mul, show q * (1 / q) = 1 by field_simp, ENNReal.rpow_one]
      rw [mul_assoc, ← ENNReal.rpow_add_of_nonneg (1 / q) ((q - 1) / q) (by positivity) hr, hpq,
        ENNReal.rpow_one]
    rw [hreal] at hHolder
    have h2 := ENNReal.rpow_le_rpow hHolder hq0.le
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ q)] at h2
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at h2
    rw [show (1 / q) * q = 1 by field_simp, show ((q - 1) / q) * q = q - 1 by field_simp] at h2
    rw [ENNReal.rpow_one] at h2
    exact h2

/-- Pointwise comparison of the smoothing weights. -/
lemma weight_rpow_le_smoothing {n : ℕ} {M R q : ℝ} (hR : 0 < R) (hM : 0 ≤ M) (hq : 1 ≤ q)
    (x u c : EuclideanSpace ℝ (Fin n)) :
    (1 + ‖x - c‖ / R) ^ (-M / q) ≤ (1 + ‖u - c‖ / R) ^ (-M / q) * (1 + ‖x - u‖ / R) ^ (M / q) := by
  rw [neg_div]
  set X : ℝ := 1 + ‖x - c‖ / R with hX
  set Y : ℝ := 1 + ‖u - c‖ / R with hY
  set Z : ℝ := 1 + ‖x - u‖ / R with hZ
  have hX0 : 0 < X := by
    rw [hX]; have : (0 : ℝ) ≤ ‖x - c‖ / R := div_nonneg (norm_nonneg (x - c)) hR.le; linarith
  have hY0 : 0 < Y := by
    rw [hY]; have : (0 : ℝ) ≤ ‖u - c‖ / R := div_nonneg (norm_nonneg (u - c)) hR.le; linarith
  have hZ0 : 0 < Z := by
    rw [hZ]; have : (0 : ℝ) ≤ ‖x - u‖ / R := div_nonneg (norm_nonneg (x - u)) hR.le; linarith
  have hux : ‖u - c‖ ≤ ‖x - u‖ + ‖x - c‖ := by
    have h : u - c = (u - x) + (x - c) := by abel
    rw [h]
    calc ‖u - x + (x - c)‖ ≤ ‖u - x‖ + ‖x - c‖ := norm_add_le _ _
      _ = ‖x - u‖ + ‖x - c‖ := by rw [norm_sub_rev u x]
  have hYX : Y / X ≤ Z := by
    rw [div_le_iff₀ hX0, hZ, hX, hY]
    have h1 : ‖u - c‖ / R ≤ (‖x - u‖ + ‖x - c‖) / R := div_le_div_of_nonneg_right hux hR.le
    have h2 : (‖x - u‖ + ‖x - c‖) / R = ‖x - u‖ / R + ‖x - c‖ / R := by ring
    have hnu : 0 ≤ ‖x - u‖ / R := div_nonneg (norm_nonneg (x - u)) hR.le
    have hnc : 0 ≤ ‖x - c‖ / R := div_nonneg (norm_nonneg (x - c)) hR.le
    nlinarith [h1, h2, mul_nonneg hnu hnc]
  have hexp : 0 ≤ M / q := div_nonneg hM (by linarith)
  have hYXpow : (Y / X) ^ (M / q) ≤ Z ^ (M / q) :=
    Real.rpow_le_rpow (by positivity) hYX hexp
  have hsplit : (Y / X) ^ (M / q) = Y ^ (M / q) * X ^ (-(M / q)) := by
    rw [Real.div_rpow hY0.le hX0.le, Real.rpow_neg hX0.le, div_eq_mul_inv]
  rw [hsplit] at hYXpow
  have hgoal : X ^ (-(M / q)) ≤ Y ^ (-(M / q)) * Z ^ (M / q) := by
    have hmul := mul_le_mul_of_nonneg_left hYXpow (Real.rpow_nonneg hY0.le (-(M / q)))
    rw [← mul_assoc, ← Real.rpow_add hY0, neg_add_cancel, Real.rpow_zero, one_mul] at hmul
    exact hmul
  exact hgoal

private lemma continuous_kernel_pair {n : ℕ} {R A : ℝ} (hR : 0 < R) :
    Continuous (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      (1 + ‖p.1 - p.2‖ / R) ^ (-A) / R ^ n) := by
  have hb : Continuous (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      1 + ‖p.1 - p.2‖ / R) := by fun_prop
  exact (hb.rpow_const (fun p => Or.inl (by
    have : (0 : ℝ) ≤ ‖p.1 - p.2‖ / R := div_nonneg (norm_nonneg _) hR.le
    linarith))).div_const _

private lemma continuous_kernel_left {n : ℕ} {R A : ℝ} (hR : 0 < R) (x : EuclideanSpace ℝ (Fin n)) :
    Continuous (fun u : EuclideanSpace ℝ (Fin n) => (1 + ‖x - u‖ / R) ^ (-A) / R ^ n) := by
  have hb : Continuous (fun u : EuclideanSpace ℝ (Fin n) => 1 + ‖x - u‖ / R) := by fun_prop
  exact (hb.rpow_const (fun u => Or.inl (by
    have : (0 : ℝ) ≤ ‖x - u‖ / R := div_nonneg (norm_nonneg _) hR.le
    linarith))).div_const _

private lemma continuous_kernel_right {n : ℕ} {R A : ℝ} (hR : 0 < R) (u : EuclideanSpace ℝ (Fin n)) :
    Continuous (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x - u‖ / R) ^ (-A) / R ^ n) := by
  have hb : Continuous (fun x : EuclideanSpace ℝ (Fin n) => 1 + ‖x - u‖ / R) := by fun_prop
  exact (hb.rpow_const (fun x => Or.inl (by
    have : (0 : ℝ) ≤ ‖x - u‖ / R := div_nonneg (norm_nonneg _) hR.le
    linarith))).div_const _

end Helpers

open MeasureTheory in
theorem integral_smoothing_rpow_le_of_integrable {n : ℕ} (hn : 1 ≤ n) {A M : ℝ} (hM : 0 ≤ M)
    (hAM : M + (n : ℝ) < A) {q : ℝ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ) (hR : 0 < R) (c : EuclideanSpace ℝ (Fin n))
      (G : EuclideanSpace ℝ (Fin n) → ℝ), Measurable G → (∀ x, 0 ≤ G x) →
        Integrable (fun x => (G x) ^ q * (1 + ‖x - c‖ / R) ^ (-M))
          (volume : Measure (EuclideanSpace ℝ (Fin n))) →
        (∫ x, (∫ u, G u * ((1 + ‖x - u‖ / R) ^ (-A) / R ^ n)) ^ q
            * (1 + ‖x - c‖ / R) ^ (-M))
          ≤ C * ∫ x, (G x) ^ q * (1 + ‖x - c‖ / R) ^ (-M) := by
  have hq0 : 0 < q := by linarith
  set s : ℝ := A - M / q with hsdef
  have hs_gt : (n : ℝ) < s := by
    have hq1 : 1 / q ≤ 1 := (div_le_one hq0).mpr hq
    have hMt : 0 ≤ M * (1 - 1 / q) := mul_nonneg hM (by linarith)
    have hkey : M - M / q = M * (1 - 1 / q) := by ring
    rw [hsdef]
    have : (n : ℝ) + M * (1 - 1 / q) < A - M / q := by rw [← hkey]; linarith
    linarith
  refine ⟨max ((∫ v : EuclideanSpace ℝ (Fin n), (1 + ‖v‖) ^ (-s)) ^ q) 1,
    lt_of_lt_of_le zero_lt_one (le_max_right _ 1), ?_⟩
  intro R hR c G hG hGnn hInt
  set K : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x u => (1 + ‖x - u‖ / R) ^ (-A) / R ^ n with hK
  set w : EuclideanSpace ℝ (Fin n) → ℝ := fun x => (1 + ‖x - c‖ / R) ^ (-M) with hw
  set Wr : EuclideanSpace ℝ (Fin n) → ℝ := fun x => (1 + ‖x - c‖ / R) ^ (-M / q) with hWr
  set Zr : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x u => (1 + ‖x - u‖ / R) ^ (M / q) with hZr
  set L : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x u => (1 + ‖x - u‖ / R) ^ (-s) / R ^ n with hL
  set a : EuclideanSpace ℝ (Fin n) → ℝ := fun x => ∫ u, G u * K x u with ha
  set J : ℝ := ∫ v : EuclideanSpace ℝ (Fin n), (1 + ‖v‖) ^ (-s) with hJ
  have hbase_c : ∀ x : EuclideanSpace ℝ (Fin n), 0 < 1 + ‖x - c‖ / R := fun x => by
    have : (0:ℝ) ≤ ‖x - c‖ / R := div_nonneg (norm_nonneg _) hR.le; linarith
  have hbase_u : ∀ x u : EuclideanSpace ℝ (Fin n), 0 < 1 + ‖x - u‖ / R := fun x u => by
    have : (0:ℝ) ≤ ‖x - u‖ / R := div_nonneg (norm_nonneg _) hR.le; linarith
  have hKnn : ∀ x u : EuclideanSpace ℝ (Fin n), 0 ≤ K x u := fun x u =>
    div_nonneg (Real.rpow_nonneg (hbase_u x u).le _) (pow_nonneg hR.le n)
  have hWrnn : ∀ x : EuclideanSpace ℝ (Fin n), 0 ≤ Wr x := fun x => Real.rpow_nonneg (hbase_c x).le _
  have hwnn : ∀ x : EuclideanSpace ℝ (Fin n), 0 ≤ w x := fun x => Real.rpow_nonneg (hbase_c x).le _
  have hLnn : ∀ x u : EuclideanSpace ℝ (Fin n), 0 ≤ L x u := fun x u =>
    div_nonneg (Real.rpow_nonneg (hbase_u x u).le _) (pow_nonneg hR.le n)
  have hWrpow : ∀ x : EuclideanSpace ℝ (Fin n), Wr x ^ q = w x := by
    intro x
    simp only [hWr, hw]
    rw [← Real.rpow_mul (hbase_c x).le]
    congr 1
    field_simp
  have hKL : ∀ x u : EuclideanSpace ℝ (Fin n), K x u * Zr x u = L x u := by
    intro x u
    simp only [hK, hZr, hL]
    rw [div_mul_eq_mul_div, ← Real.rpow_add (hbase_u x u) (-A) (M/q)]
    rw [show -A + M / q = -s by rw [hsdef]; ring]
  have hWrle : ∀ x u : EuclideanSpace ℝ (Fin n), Wr x ≤ Wr u * Zr x u := by
    intro x u
    simp only [hWr, hZr]
    exact weight_rpow_le_smoothing hR hM hq x u c
  have hIntL : ∀ x : EuclideanSpace ℝ (Fin n), Integrable (fun u => L x u) (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    intro x
    have h0 := integrable_one_add_norm_div_pow (n := n) (s := s) (R := R) hs_gt hR
    have h1 := h0.comp_sub_left x
    simpa only [hL] using h1
  have hLval : ∀ x : EuclideanSpace ℝ (Fin n), ∫ u, L x u ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = J := by
    intro x
    calc ∫ u, L x u ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))
        = ∫ u, (fun z : EuclideanSpace ℝ (Fin n) => (1 + ‖z‖ / R) ^ (-s) / R ^ n) (x - u)
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
          apply integral_congr_ae; filter_upwards with u; simp only [hL]
      _ = ∫ z, (fun z : EuclideanSpace ℝ (Fin n) => (1 + ‖z‖ / R) ^ (-s) / R ^ n) z
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) :=
          MeasureTheory.integral_sub_left_eq_self (fun z : EuclideanSpace ℝ (Fin n) => (1 + ‖z‖ / R) ^ (-s) / R ^ n) (volume : Measure (EuclideanSpace ℝ (Fin n))) x
      _ = ∫ z, (1 + ‖z‖ / R) ^ (-s) / R ^ n ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by simp
      _ = J := by rw [hJ]; exact integral_one_add_norm_div_pow (n := n) (s := s) (R := R) hR
  have hIntL2 : ∀ u : EuclideanSpace ℝ (Fin n), Integrable (fun x => L x u) (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    intro u
    have h0 := integrable_one_add_norm_div_pow (n := n) (s := s) (R := R) hs_gt hR
    have h1 := h0.comp_sub_right u
    simpa only [hL] using h1
  have hLval2 : ∀ u : EuclideanSpace ℝ (Fin n), ∫ x, L x u ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = J := by
    intro u
    calc ∫ x, L x u ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))
        = ∫ x, (fun z : EuclideanSpace ℝ (Fin n) => (1 + ‖z‖ / R) ^ (-s) / R ^ n) (x - u)
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
          apply integral_congr_ae; filter_upwards with x; simp only [hL]
      _ = ∫ z, (fun z : EuclideanSpace ℝ (Fin n) => (1 + ‖z‖ / R) ^ (-s) / R ^ n) z
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) :=
          MeasureTheory.integral_sub_right_eq_self (fun z : EuclideanSpace ℝ (Fin n) => (1 + ‖z‖ / R) ^ (-s) / R ^ n) u
      _ = ∫ z, (1 + ‖z‖ / R) ^ (-s) / R ^ n ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by simp
      _ = J := by rw [hJ]; exact integral_one_add_norm_div_pow (n := n) (s := s) (R := R) hR
  have hlinL : ∀ x : EuclideanSpace ℝ (Fin n),
      ∫⁻ u, ENNReal.ofReal (L x u) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))
        = ENNReal.ofReal J := by
    intro x
    rw [← ofReal_integral_eq_lintegral_ofReal (hIntL x)
      (Filter.Eventually.of_forall (fun u => hLnn x u))]
    rw [hLval x]
  have hlinL2 : ∀ u : EuclideanSpace ℝ (Fin n),
      ∫⁻ x, ENNReal.ofReal (L x u) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))
        = ENNReal.ofReal J := by
    intro u
    rw [← ofReal_integral_eq_lintegral_ofReal (hIntL2 u)
      (Filter.Eventually.of_forall (fun x => hLnn x u))]
    rw [hLval2 u]
  have hWrm : Measurable Wr := by
    have : Continuous Wr := by
      simp only [hWr]
      exact ((by fun_prop : Continuous (fun x : EuclideanSpace ℝ (Fin n) => 1 + ‖x - c‖ / R)).rpow_const
        (fun x => Or.inl (by
          have h2 : (0 : ℝ) ≤ ‖x - c‖ / R := div_nonneg (norm_nonneg _) hR.le
          linarith)))
    exact this.measurable
  have hwm : Measurable w := by
    have : Continuous w := by
      simp only [hw]
      exact ((by fun_prop : Continuous (fun x : EuclideanSpace ℝ (Fin n) => 1 + ‖x - c‖ / R)).rpow_const
        (fun x => Or.inl (by
          have h2 : (0 : ℝ) ≤ ‖x - c‖ / R := div_nonneg (norm_nonneg _) hR.le
          linarith)))
    exact this.measurable
  have ha_nonneg : ∀ x : EuclideanSpace ℝ (Fin n), 0 ≤ a x := by
    intro x
    simp only [ha]
    exact integral_nonneg (fun u => mul_nonneg (hGnn u) (hKnn x u))
  have ha_meas : AEStronglyMeasurable a (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hcont := continuous_kernel_pair (n := n) (A := A) hR
    have hprod : AEStronglyMeasurable
        (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => G p.2 * K p.1 p.2)
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).prod volume) :=
      ((hG.comp measurable_snd).mul hcont.measurable).aestronglyMeasurable
    simpa only [ha] using hprod.integral_prod_right'
  have hA : ∀ x : EuclideanSpace ℝ (Fin n),
      ENNReal.ofReal (a x * Wr x) ≤
        ∫⁻ u, ENNReal.ofReal (G u) * ENNReal.ofReal (Wr u) * ENNReal.ofReal (L x u)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    intro x
    have hKxm : Measurable (fun u : EuclideanSpace ℝ (Fin n) => G u * K x u) :=
      hG.mul (continuous_kernel_left (n := n) (A := A) hR x).measurable
    have h1 : a x * Wr x
        = ∫ u, Wr x * (G u * K x u) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      simp only [ha]
      rw [mul_comm, ← MeasureTheory.integral_const_mul]
    rw [h1]
    refine le_trans (ofReal_integral_le_lintegral ?_ ?_) (lintegral_mono (fun u => ?_))
    · exact (measurable_const.mul hKxm).aestronglyMeasurable
    · exact Filter.Eventually.of_forall
        (fun u => mul_nonneg (hWrnn x) (mul_nonneg (hGnn u) (hKnn x u)))
    · have hpt : Wr x * (G u * K x u) ≤ G u * Wr u * L x u := by
        have h1' : Wr x * K x u ≤ Wr u * L x u := by
          have h2 := mul_le_mul_of_nonneg_right (hWrle x u) (hKnn x u)
          rwa [show Wr u * Zr x u * K x u = Wr u * L x u by rw [← hKL x u]; ring] at h2
        have h3 := mul_le_mul_of_nonneg_left h1' (hGnn u)
        calc Wr x * (G u * K x u) = G u * (Wr x * K x u) := by ring
          _ ≤ G u * (Wr u * L x u) := h3
          _ = G u * Wr u * L x u := by ring
      calc ENNReal.ofReal (Wr x * (G u * K x u))
          ≤ ENNReal.ofReal (G u * Wr u * L x u) := ENNReal.ofReal_le_ofReal hpt
        _ = ENNReal.ofReal (G u) * ENNReal.ofReal (Wr u) * ENNReal.ofReal (L x u) := by
            rw [ENNReal.ofReal_mul (mul_nonneg (hGnn u) (hWrnn u)), ENNReal.ofReal_mul (hGnn u)]
  have hWrE_pow : ∀ x : EuclideanSpace ℝ (Fin n),
      ENNReal.ofReal (Wr x) ^ q = ENNReal.ofReal (w x) := by
    intro x
    rw [ENNReal.ofReal_rpow_of_nonneg (hWrnn x) hq0.le, hWrpow x]
  set FF : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ≥0∞ :=
    fun x u => ENNReal.ofReal ((G u)^q) * ENNReal.ofReal (w u) * ENNReal.ofReal (L x u) with hFF
  have hB : ∀ x : EuclideanSpace ℝ (Fin n),
      ENNReal.ofReal ((a x)^q * w x) ≤
        (∫⁻ u, FF x u ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
          * ENNReal.ofReal J ^ (q - 1) := by
    intro x
    have hGum : AEMeasurable (fun u : EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal (G u) * ENNReal.ofReal (Wr u)) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      (hG.ennreal_ofReal.mul hWrm.ennreal_ofReal).aemeasurable
    have hLum : AEMeasurable (fun u : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (L x u))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      (continuous_kernel_left (n := n) (A := s) hR x).measurable.ennreal_ofReal.aemeasurable
    have h1 : ENNReal.ofReal (a x * Wr x) ^ q = ENNReal.ofReal ((a x)^q * w x) := by
      rw [ENNReal.ofReal_mul (ha_nonneg x), ENNReal.mul_rpow_of_nonneg _ _ hq0.le,
        ENNReal.ofReal_rpow_of_nonneg (ha_nonneg x) hq0.le, hWrE_pow x,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (ha_nonneg x) q)]
    rw [← h1]
    have hH := lintegral_mul_pow_le (ν := (volume : Measure (EuclideanSpace ℝ (Fin n)))) hq
      (f := fun u => ENNReal.ofReal (G u) * ENNReal.ofReal (Wr u))
      (g := fun u => ENNReal.ofReal (L x u)) hGum hLum
    have hcong : (fun u : EuclideanSpace ℝ (Fin n) =>
          (ENNReal.ofReal (G u) * ENNReal.ofReal (Wr u))^q * ENNReal.ofReal (L x u))
        = fun u => ENNReal.ofReal ((G u)^q) * ENNReal.ofReal (w u) * ENNReal.ofReal (L x u) := by
      funext u
      rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le,
        ENNReal.ofReal_rpow_of_nonneg (hGnn u) hq0.le, hWrE_pow u]
    rw [hcong, hlinL x] at hH
    exact le_trans (ENNReal.rpow_le_rpow (hA x) hq0.le) hH
  have hFFm : Measurable (Function.uncurry FF) := by
    have h1 : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal ((G p.2)^q)) :=
      (((Real.continuous_rpow_const hq0.le).measurable.comp hG).comp measurable_snd).ennreal_ofReal
    have h2 : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal (w p.2)) := (hwm.comp measurable_snd).ennreal_ofReal
    have h3 : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal (L p.1 p.2)) :=
      (continuous_kernel_pair (n := n) (A := s) hR).measurable.ennreal_ofReal
    have h := (h1.mul h2).mul h3
    have heq : Function.uncurry FF = fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal ((G p.2)^q) * ENNReal.ofReal (w p.2) * ENNReal.ofReal (L p.1 p.2) := by
      funext p; rfl
    rw [heq]; exact h
  have hIntMeas : AEMeasurable (fun x : EuclideanSpace ℝ (Fin n) => ∫⁻ u, FF x u
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hFFm.lintegral_prod_right.aemeasurable
  have hGqwm : AEMeasurable (fun u : EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal ((G u)^q) * ENNReal.ofReal (w u)) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    ((((Real.continuous_rpow_const hq0.le).measurable.comp hG).ennreal_ofReal).mul hwm.ennreal_ofReal).aemeasurable
  have hJnn : 0 ≤ J := by
    rw [hJ]; exact integral_nonneg (fun v => Real.rpow_nonneg (by positivity) _)
  have hRHSnn : 0 ≤ ∫ x, (G x)^q * w x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    integral_nonneg (fun x => mul_nonneg (Real.rpow_nonneg (hGnn x) q) (hwnn x))
  have hmain : ∫⁻ x, ENNReal.ofReal ((a x)^q * w x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))
      ≤ ENNReal.ofReal (J^q * ∫ x, (G x)^q * w x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    have hrpow : ENNReal.ofReal J * ENNReal.ofReal J ^ (q - 1) = ENNReal.ofReal J ^ q := by
      conv_rhs => rw [show (q:ℝ) = 1 + (q - 1) by ring]
      rw [ENNReal.rpow_add_of_nonneg 1 (q - 1) (by norm_num) (by linarith), ENNReal.rpow_one]
    have hstep1 : ∫⁻ x, ENNReal.ofReal ((a x)^q * w x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))
        ≤ (∫⁻ x, ∫⁻ u, FF x u ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))
              ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
            * ENNReal.ofReal J ^ (q - 1) := by
      calc ∫⁻ x, ENNReal.ofReal ((a x)^q * w x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))
          ≤ ∫⁻ x, ((∫⁻ u, FF x u ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
              * ENNReal.ofReal J ^ (q - 1)) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) :=
            lintegral_mono (fun x => hB x)
        _ = (∫⁻ x, ∫⁻ u, FF x u ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))
              ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
            * ENNReal.ofReal J ^ (q - 1) :=
            lintegral_mul_const'' _ hIntMeas
    have hstep2 : (∫⁻ x, ∫⁻ u, FF x u ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))
              ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
        = (∫⁻ u, ∫⁻ x, FF x u ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))
              ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) :=
      lintegral_lintegral_swap hFFm.aemeasurable
    have hGW : (∫⁻ u, ENNReal.ofReal ((G u)^q) * ENNReal.ofReal (w u)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
        = ENNReal.ofReal (∫ x, (G x)^q * w x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
      have hEq : (∫⁻ u, ENNReal.ofReal ((G u)^q) * ENNReal.ofReal (w u)
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
          = ∫⁻ u, ENNReal.ofReal ((G u)^q * w u) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
        apply lintegral_congr; intro u
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg (hGnn u) q)]
      rw [hEq, ← ofReal_integral_eq_lintegral_ofReal hInt
        (Filter.Eventually.of_forall (fun x => mul_nonneg (Real.rpow_nonneg (hGnn x) q) (hwnn x)))]
    have hstep3 : (∫⁻ u, ∫⁻ x, FF x u ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))
              ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
        = ENNReal.ofReal (∫ x, (G x)^q * w x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
            * ENNReal.ofReal J := by
      have hinner : ∀ u : EuclideanSpace ℝ (Fin n),
          (∫⁻ x, FF x u ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
            = ENNReal.ofReal ((G u)^q) * ENNReal.ofReal (w u) * ENNReal.ofReal J := by
        intro u
        have hLum : AEMeasurable (fun x : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (L x u))
            (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
          (continuous_kernel_right (n := n) (A := s) hR u).measurable.ennreal_ofReal.aemeasurable
        rw [hFF]
        rw [lintegral_const_mul'' _ hLum, hlinL2 u]
      simp_rw [hinner]
      rw [lintegral_mul_const'' _ hGqwm, hGW]
    calc ∫⁻ x, ENNReal.ofReal ((a x)^q * w x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))
        ≤ (∫⁻ x, ∫⁻ u, FF x u ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))
              ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
            * ENNReal.ofReal J ^ (q - 1) := hstep1
      _ = (∫⁻ u, ∫⁻ x, FF x u ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))
              ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
            * ENNReal.ofReal J ^ (q - 1) := by rw [hstep2]
      _ = (ENNReal.ofReal (∫ x, (G x)^q * w x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
              * ENNReal.ofReal J) * ENNReal.ofReal J ^ (q - 1) := by rw [hstep3]
      _ = ENNReal.ofReal (∫ x, (G x)^q * w x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
              * ENNReal.ofReal J ^ q := by rw [mul_assoc, hrpow]
      _ = ENNReal.ofReal (∫ x, (G x)^q * w x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
              * ENNReal.ofReal (J^q) := by rw [ENNReal.ofReal_rpow_of_nonneg hJnn hq0.le]
      _ = ENNReal.ofReal ((∫ x, (G x)^q * w x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) * J^q) := by
            rw [← ENNReal.ofReal_mul hRHSnn]
      _ = ENNReal.ofReal (J^q * ∫ x, (G x)^q * w x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
            congr 1; ring
  have hLHS_meas : AEStronglyMeasurable (fun x : EuclideanSpace ℝ (Fin n) => (a x)^q * w x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have h1 : AEStronglyMeasurable (fun x : EuclideanSpace ℝ (Fin n) => (a x)^q)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      (Real.continuous_rpow_const hq0.le).comp_aestronglyMeasurable ha_meas
    exact h1.mul hwm.aestronglyMeasurable
  have hLHS_eq : (∫ x, (a x)^q * w x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
      = (∫⁻ x, ENNReal.ofReal ((a x)^q * w x)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae]
    · exact Filter.Eventually.of_forall
        (fun x => mul_nonneg (Real.rpow_nonneg (ha_nonneg x) q) (hwnn x))
    · exact hLHS_meas
  change (∫ x, (a x)^q * w x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
      ≤ max (J^q) 1 * ∫ x, (G x)^q * w x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))
  rw [hLHS_eq]
  calc (∫⁻ x, ENNReal.ofReal ((a x)^q * w x)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))).toReal
      ≤ (ENNReal.ofReal (J^q * ∫ x, (G x)^q * w x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hmain
    _ = J^q * ∫ x, (G x)^q * w x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) :=
        ENNReal.toReal_ofReal (mul_nonneg (Real.rpow_nonneg hJnn q) hRHSnn)
    _ ≤ max (J^q) 1 * ∫ x, (G x)^q * w x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hRHSnn


end Commons.Measure.Integral