import Mathlib
import Submission.Work.Horn.fatouQ_defs
import Submission.Work.Horn.FatouQ.inv_pow_sub_linear
import Submission.Work.Horn.FatouQ.inv_pow_sub_quadratic

namespace Work.Horn.FatouQ

open Work.Horn.Flower Filter
open scoped Topology

noncomputable section

set_option maxHeartbeats 2000000

/-- The principal logarithm is additive on the open right half plane. -/
lemma log_mul_of_re_pos {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    Complex.log (x * y) = Complex.log x + Complex.log y := by
  have hx0 : x ≠ 0 := fun h => by rw [h] at hx; simp at hx
  have hy0 : y ≠ 0 := fun h => by rw [h] at hy; simp at hy
  have hxle : |x.arg| ≤ Real.pi / 2 := Complex.abs_arg_le_pi_div_two_iff.mpr hx.le
  have hyle : |y.arg| ≤ Real.pi / 2 := Complex.abs_arg_le_pi_div_two_iff.mpr hy.le
  have hxa : -(Real.pi / 2) < x.arg ∧ x.arg < Real.pi / 2 := by
    obtain ⟨h1, h2⟩ := abs_le.mp hxle
    refine ⟨lt_of_le_of_ne h1 (fun h => ?_), lt_of_le_of_ne h2 (fun h => ?_)⟩
    · exact absurd (Complex.arg_eq_neg_pi_div_two_iff.mp h.symm).1 (ne_of_gt hx)
    · exact absurd (Complex.arg_eq_pi_div_two_iff.mp h).1 (ne_of_gt hx)
  have hya : -(Real.pi / 2) < y.arg ∧ y.arg < Real.pi / 2 := by
    obtain ⟨h1, h2⟩ := abs_le.mp hyle
    refine ⟨lt_of_le_of_ne h1 (fun h => ?_), lt_of_le_of_ne h2 (fun h => ?_)⟩
    · exact absurd (Complex.arg_eq_neg_pi_div_two_iff.mp h.symm).1 (ne_of_gt hy)
    · exact absurd (Complex.arg_eq_pi_div_two_iff.mp h).1 (ne_of_gt hy)
  refine Complex.log_mul hx0 hy0 ⟨?_, ?_⟩
  · linarith [hxa.1, hya.1]
  · linarith [hxa.2, hya.2]

/-- The germ factor `Hfun f q a` is analytic at `0`. -/
lemma analyticAt_hfun {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {a : ℂ} {ρ : ℝ}
    (hS : Setup f D q a) (hρ : 0 < ρ) (hb : Bounds f D q a ρ) :
    AnalyticAt ℂ (Hfun f q a) 0 := by
  refine Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_
  · rw [eventually_nhdsWithin_iff]
    filter_upwards [Metric.ball_mem_nhds 0 hρ] with z hz hz0
    have hz0' : z ≠ 0 := by simpa using hz0
    have hzD : z ∈ D := hb.hsub hz
    have hfd : DifferentiableAt ℂ f z := hS.hf.differentiableAt (hS.hD.mem_nhds hzD)
    have h1 : Hfun f q a =ᶠ[𝓝 z] fun w => (f w - w) / w ^ (q + 1) := by
      filter_upwards [isOpen_ne.mem_nhds hz0'] with w hw
      simp only [Hfun]; rw [ite_eq_right hw]
    exact h1.differentiableAt_iff.mpr
      ((hfd.sub differentiableAt_id).div (differentiableAt_pow (q + 1)) (pow_ne_zero _ hz0'))
  · rw [← continuousWithinAt_compl_self, ContinuousWithinAt]
    have hH0 : Hfun f q a 0 = a := by simp [Hfun]
    rw [hH0]
    have h3 : Tendsto (fun z => (f z - z - a * z ^ (q + 1)) / z ^ (q + 1) + a)
        (𝓝[≠] (0 : ℂ)) (𝓝 a) := by
      simpa using hS.hgerm.add_const a
    refine h3.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz0
    have hz0' : z ≠ 0 := by simpa using hz0
    have hHz : Hfun f q a z = (f z - z) / z ^ (q + 1) := by
      simp only [Hfun]; rw [ite_eq_right hz0']
    rw [hHz]
    field_simp
    ring

/-- `Lbranch` is a branch of the logarithm on the petal: the difference of the `Lbranch`
values at `f z` and at `z` is `log u` when `f z = z * u`, `u` is in the right half plane
and `z^q/cc` is in the right half plane. -/
lemma lbranch_sub {f : ℂ → ℂ} {q : ℕ} {a z u : ℂ} (hq : 1 ≤ q)
    (hunit : u ≠ 0)
    (hrez : 0 < (z ^ q / cc q a).re)
    (hreu : 0 < (u ^ q).re)
    (harg : |u.arg| * (q : ℝ) < Real.pi)
    (hfz : f z = z * u) :
    Lbranch q a (f z) - Lbranch q a z = Complex.log u := by
  have hfzq : (f z) ^ q = z ^ q * u ^ q := by rw [hfz, mul_pow]
  have h1 : Complex.log ((f z) ^ q / cc q a) =
      Complex.log (z ^ q / cc q a) + Complex.log (u ^ q) := by
    have hEq : (f z) ^ q / cc q a = (z ^ q / cc q a) * u ^ q := by rw [hfzq]; ring
    rw [hEq]; exact log_mul_of_re_pos hrez hreu
  have h2 : Complex.log (u ^ q) = (q : ℂ) * Complex.log u := log_pow_eq hq hunit harg
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  simp only [Lbranch]
  rw [h1, h2]
  field_simp
  ring

/-- Splitting the defect `Acorr (f z) - Acorr z` into the `u`-chart. -/
lemma Acorr_sub {f : ℂ → ℂ} {q : ℕ} {a z u : ℂ}
    (hfz : f z = z * u)
    (hlog : Lbranch q a (f z) - Lbranch q a z = Complex.log u) :
    Acorr f q a (f z) - Acorr f q a z =
      cc q a * (z ^ q)⁻¹ * ((u⁻¹) ^ q - 1)
      + (∑ i ∈ Finset.Icc 1 (q - 1),
          gcoef f q a i / ((i : ℂ) - (q : ℂ)) * (z⁻¹) ^ (q - i) * ((u⁻¹) ^ (q - i) - 1))
      + (gcoef f q a q + ((q : ℂ) + 1) / 2) * Complex.log u := by
  have e1 : cc q a / (f z) ^ q = cc q a / z ^ q + cc q a * (z ^ q)⁻¹ * ((u⁻¹) ^ q - 1) := by
    rw [div_eq_mul_inv, div_eq_mul_inv, hfz, mul_pow, mul_inv, inv_pow]; ring
  have e2 : (∑ i ∈ Finset.Icc 1 (q - 1),
        gcoef f q a i / ((i : ℂ) - (q : ℂ)) * ((f z)⁻¹) ^ (q - i))
      = (∑ i ∈ Finset.Icc 1 (q - 1), gcoef f q a i / ((i : ℂ) - (q : ℂ)) * (z⁻¹) ^ (q - i))
        + ∑ i ∈ Finset.Icc 1 (q - 1), gcoef f q a i / ((i : ℂ) - (q : ℂ)) *
            (z⁻¹) ^ (q - i) * ((u⁻¹) ^ (q - i) - 1) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hfz, mul_inv, mul_pow]; ring
  have e3 : Lbranch q a (f z) = Lbranch q a z + Complex.log u := by
    rw [← hlog]; ring
  simp only [Acorr]
  rw [e1, e2, e3]
  ring

/-- `gcoef f q a 0 = a⁻¹`. -/
lemma gcoef_zero {f : ℂ → ℂ} {q : ℕ} {a : ℂ} (h : Hfun f q a 0 = a) :
    gcoef f q a 0 = a⁻¹ := by
  simp only [gcoef, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one, h]

/-- `‖log z‖ ≤ |log ‖z‖| + π`. -/
private lemma norm_log_le (z : ℂ) : ‖Complex.log z‖ ≤ |Real.log ‖z‖| + Real.pi := by
  have h : Complex.log z = (Real.log ‖z‖ : ℂ) + (z.arg : ℂ) * Complex.I := by
    rw [Complex.ext_iff]; constructor <;> simp [Complex.log_re, Complex.log_im]
  rw [h]
  calc ‖(Real.log ‖z‖ : ℂ) + (z.arg : ℂ) * Complex.I‖
      ≤ ‖(Real.log ‖z‖ : ℂ)‖ + ‖(z.arg : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |Real.log ‖z‖| + |z.arg| := by simp
    _ ≤ |Real.log ‖z‖| + Real.pi := by
        have := Complex.abs_arg_le_pi z; linarith

/-- `-q * cc q a = a⁻¹`. -/
lemma neg_q_cc {q : ℕ} {a : ℂ} (hq : 1 ≤ q) (ha : a ≠ 0) :
    -((q : ℂ) * cc q a) = a⁻¹ := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  simp only [cc]
  field_simp

/-- Splitting `∑_{i<q}` as the `i = 0` term plus the sum over `1 ≤ i ≤ q-1`. -/
lemma sum_range_eq_zero_add_Icc {q : ℕ} (hq : 1 ≤ q) (f : ℕ → ℂ) :
    (∑ i ∈ Finset.range q, f i) = f 0 + ∑ i ∈ Finset.Icc 1 (q-1), f i := by
  conv_lhs => rw [show q = (q-1)+1 from by omega]
  rw [Finset.sum_range_succ']
  have h1 : (∑ k ∈ Finset.range (q-1), f (k+1)) = ∑ i ∈ Finset.Icc 1 (q-1), f i := by
    rw [show (fun k => f (k+1)) = (fun k => f (1+k)) from by funext k; rw [add_comm]]
    rw [← Finset.sum_Ico_eq_sum_range]
    rw [show Finset.Ico 1 q = Finset.Icc 1 (q-1) from by ext i; simp; omega]
  rw [h1, add_comm]

/-- For `z` in a petal, `z^q / cc q a` has positive real part. -/
lemma petal_re_div_cc {q : ℕ} {a : ℂ} {M : ℝ} (hgeo : PetalFacts q a M) (hM : 0 < M)
    {j : Fin q} {z : ℂ} (hz : z ∈ petal q a M j) :
    0 < (z ^ q / cc q a).re := by
  have hw : z ^ q ∈ DM q a M := ((hgeo.mem_petal_iff j z).mp hz).2.1
  rw [hgeo.DM_eq_ball] at hw
  simp only [Metric.mem_ball, dist_eq_norm] at hw
  have hcc : cc q a ≠ 0 := hgeo.cc_ne_zero
  have hccpos : 0 < ‖cc q a‖ := norm_pos_iff.mpr hcc
  have hM2 : (0:ℝ) < 2*M := by linarith
  rw [div_eq_mul_inv] at hw
  have h1 : ‖(z^q - cc q a*(2*(M:ℂ))⁻¹)/cc q a‖ < (2*M)⁻¹ := by
    rw [norm_div, div_lt_iff₀ hccpos, mul_comm (2*M)⁻¹]
    exact hw
  have h3 : (z^q/cc q a).re = ((z^q - cc q a*(2*(M:ℂ))⁻¹)/cc q a).re + (2*M)⁻¹ := by
    have heq : z^q/cc q a = (z^q - cc q a*(2*(M:ℂ))⁻¹)/cc q a + (((2*M)⁻¹ : ℝ) : ℂ) := by
      field_simp
      push_cast
      ring
    rw [heq]; simp
  rw [h3]
  have h4 := (abs_le.mp (Complex.abs_re_le_norm ((z^q - cc q a*(2*(M:ℂ))⁻¹)/cc q a))).1
  linarith

/-- The Taylor expansion of `G = (Hfun f q a)⁻¹` at `0`, truncated at order `q`. -/
lemma G_expansion {f : ℂ → ℂ} {q : ℕ} {a : ℂ} (hA : AnalyticAt ℂ (Hfun f q a) 0)
    (ha : Hfun f q a 0 ≠ 0) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F 0 ∧ ∀ z : ℂ,
      (Hfun f q a z)⁻¹ =
        (∑ i ∈ Finset.range q, gcoef f q a i * z^i) + gcoef f q a q * z^q
          + z^(q+1) * F z := by
  have hGA : AnalyticAt ℂ (fun z => (Hfun f q a z)⁻¹) 0 := hA.inv ha
  obtain ⟨F, hFA, hF⟩ := hGA.exists_eq_sum_add_pow_mul (q+1)
  refine ⟨F, hFA, fun z => ?_⟩
  have hsum : (∑ i ∈ Finset.range q,
        (z^i / (i.factorial:ℂ)) • iteratedDeriv i (fun z => (Hfun f q a z)⁻¹) 0)
      = ∑ i ∈ Finset.range q, gcoef f q a i * z^i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [smul_eq_mul, gcoef]
    ring
  have hlast : (z^q / (q.factorial:ℂ)) • iteratedDeriv q (fun z => (Hfun f q a z)⁻¹) 0
      = gcoef f q a q * z^q := by
    simp only [smul_eq_mul, gcoef]
    ring
  rw [hF z, Finset.sum_range_succ, hsum, hlast, smul_eq_mul]

/-- The Taylor expansion of `Hfun f q a` at `0` up to order `1`. -/
lemma H_expansion {f : ℂ → ℂ} {q : ℕ} {a : ℂ} (hA : AnalyticAt ℂ (Hfun f q a) 0) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F 0 ∧ ∀ z : ℂ, Hfun f q a z = Hfun f q a 0 + z * F z := by
  obtain ⟨F, hFA, hF⟩ := hA.exists_eq_sum_add_pow_mul 1
  refine ⟨F, hFA, fun z => ?_⟩
  rw [hF z]
  simp only [Finset.sum_range_one, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one,
    pow_zero, pow_one, smul_eq_mul, one_mul]
/-- `‖(z⁻¹)^n‖ = (‖z‖^n)⁻¹`. -/
lemma norm_inv_pow (z : ℂ) (n : ℕ) : ‖(z⁻¹)^n‖ = (‖z‖^n)⁻¹ := by
  rw [norm_pow, norm_inv, inv_pow]

lemma pow_twoq_le {q : ℕ} (hq : 1 ≤ q) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x^(2*q) ≤ x^(q+1) := by
  have h : 2*q = (q+1) + (q-1) := by omega
  rw [h, pow_add]
  exact mul_le_of_le_one_right (pow_nonneg hx0 _) (pow_le_one₀ hx0 hx1)

lemma pow_qi_le {q i : ℕ} (hi : 1 ≤ i) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x^(q+i) ≤ x^(q+1) := by
  have h : q+i = (q+1) + (i-1) := by omega
  rw [h, pow_add]
  exact mul_le_of_le_one_right (pow_nonneg hx0 _) (pow_le_one₀ hx0 hx1)

lemma inv_pow_mul_cube_le {q : ℕ} (hq : 1 ≤ q) {x B : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hB : 0 ≤ B) : (x^q)⁻¹ * (x^q * B)^3 ≤ x^(q+1) * B^3 := by
  have hxne : x ≠ 0 := ne_of_gt hx0
  have hxq : x^q ≠ 0 := pow_ne_zero _ hxne
  have heq : (x^q)⁻¹ * x^(3*q) = x^(2*q) := by
    rw [inv_mul_eq_div, div_eq_iff hxq, ← pow_add]
    congr 1; omega
  calc (x^q)⁻¹ * (x^q * B)^3 = ((x^q)⁻¹ * x^(3*q)) * B^3 := by
        rw [mul_pow, ← pow_mul, show q*3 = 3*q from by omega]; ring
    _ = x^(2*q) * B^3 := by rw [heq]
    _ ≤ x^(q+1) * B^3 := by
        exact mul_le_mul_of_nonneg_right (pow_twoq_le hq hx0.le hx1) (by positivity)

lemma inv_pow_mul_sq_le {q i : ℕ} (hi : 1 ≤ i) (hiq : i ≤ q) {x B : ℝ} (hx0 : 0 < x)
    (hx1 : x ≤ 1) (hB : 0 ≤ B) : (x^(q-i))⁻¹ * (x^q * B)^2 ≤ x^(q+1) * B^2 := by
  have hxne : x ≠ 0 := ne_of_gt hx0
  have hxq : x^(q-i) ≠ 0 := pow_ne_zero _ hxne
  have heq : (x^(q-i))⁻¹ * x^(2*q) = x^(q+i) := by
    rw [inv_mul_eq_div, div_eq_iff hxq, ← pow_add]
    congr 1; omega
  calc (x^(q-i))⁻¹ * (x^q * B)^2 = ((x^(q-i))⁻¹ * x^(2*q)) * B^2 := by
        rw [mul_pow, ← pow_mul, show q*2 = 2*q from by omega]; ring
    _ = x^(q+i) * B^2 := by rw [heq]
    _ ≤ x^(q+1) * B^2 := by
        exact mul_le_mul_of_nonneg_right (pow_qi_le hi hx0.le hx1) (by positivity)

lemma sq_le {q : ℕ} (hq : 1 ≤ q) {x B : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hB : 0 ≤ B) :
    (x^q * B)^2 ≤ x^(q+1) * B^2 := by
  rw [mul_pow, ← pow_mul, show q*2 = 2*q from by omega]
  exact mul_le_mul_of_nonneg_right (pow_twoq_le hq hx0 hx1) (by positivity)




lemma near_bound {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {a : ℂ} {ρ M : ℝ}
    (hd : PetalDatum f D q a ρ M) (j : Fin q) :
    ∃ (δ C : ℝ), 0 < δ ∧ 0 ≤ C ∧ ∀ z ∈ petal q a M j, ‖z‖ < δ →
      ‖Acorr f q a (f z) - Acorr f q a z - 1‖ ≤ C * ‖z‖ ^ (q + 1) := by
  obtain ⟨hS, hρ, hb, hM, hRM, hgeo⟩ := hd
  have hq : 1 ≤ q := hb.hq
  have ha : a ≠ 0 := hb.ha
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hH0 : Hfun f q a 0 = a := by simp [Hfun]
  have hA : AnalyticAt ℂ (Hfun f q a) 0 := analyticAt_hfun hS hρ hb
  obtain ⟨F, hFA, hF⟩ := G_expansion hA (by rw [hH0]; exact ha)
  obtain ⟨FH, hFHA, hFH⟩ := H_expansion hA
  obtain ⟨C1, hC1nn, hC1⟩ := inv_pow_sub_linear q
  obtain ⟨C2, hC2nn, hC2⟩ := inv_pow_sub_quadratic q
  set BH : ℝ := ‖a‖ + 1 with hBH
  set BF : ℝ := ‖F 0‖ + 1 with hBF
  set BFH : ℝ := ‖FH 0‖ + 1 with hBFH
  have hBHnn : 0 ≤ BH := by rw [hBH]; linarith [norm_nonneg a]
  have hBFnn : 0 ≤ BF := by rw [hBF]; linarith [norm_nonneg (F 0)]
  have hBFHnn : 0 ≤ BFH := by rw [hBFH]; linarith [norm_nonneg (FH 0)]
  have hEvH : ∀ᶠ z in 𝓝 (0:ℂ), ‖Hfun f q a z‖ ≤ BH := by
    have h1 : ∀ᶠ z in 𝓝 (0:ℂ), ‖Hfun f q a z - Hfun f q a 0‖ < 1 := by
      have := Metric.tendsto_nhds.mp hA.continuousAt 1 one_pos
      filter_upwards [this] with z hz
      simpa [dist_eq_norm] using hz
    filter_upwards [h1] with z hz
    rw [hH0] at hz
    have h2 := norm_add_le (Hfun f q a z - a) a
    rw [sub_add_cancel] at h2
    rw [hBH]
    linarith
  have hEvF : ∀ᶠ z in 𝓝 (0:ℂ), ‖F z‖ ≤ BF := by
    have h1 : ∀ᶠ z in 𝓝 (0:ℂ), ‖F z - F 0‖ < 1 := by
      have := Metric.tendsto_nhds.mp hFA.continuousAt 1 one_pos
      filter_upwards [this] with z hz
      simpa [dist_eq_norm] using hz
    filter_upwards [h1] with z hz
    have h2 := norm_add_le (F z - F 0) (F 0)
    rw [sub_add_cancel] at h2
    rw [hBF]
    linarith
  have hEvFH : ∀ᶠ z in 𝓝 (0:ℂ), ‖FH z‖ ≤ BFH := by
    have h1 : ∀ᶠ z in 𝓝 (0:ℂ), ‖FH z - FH 0‖ < 1 := by
      have := Metric.tendsto_nhds.mp hFHA.continuousAt 1 one_pos
      filter_upwards [this] with z hz
      simpa [dist_eq_norm] using hz
    filter_upwards [h1] with z hz
    have h2 := norm_add_le (FH z - FH 0) (FH 0)
    rw [sub_add_cancel] at h2
    rw [hBFH]
    linarith
  have hEvs : ∀ᶠ z in 𝓝 (0:ℂ), ‖z^q * Hfun f q a z‖ ≤ 1/2 := by
    have hcont : ContinuousAt (fun z : ℂ => z^q * Hfun f q a z) 0 :=
      (continuous_pow q).continuousAt.mul hA.continuousAt
    have hval : (0:ℂ)^q * Hfun f q a 0 = 0 := by
      rw [zero_pow (by omega : q ≠ 0), zero_mul]
    have h1 := Metric.tendsto_nhds.mp hcont (1/2) (by norm_num)
    filter_upwards [h1] with z hz
    rw [hval, dist_zero_right] at hz
    linarith
  have hEvne : ∀ᶠ z in 𝓝 (0:ℂ), Hfun f q a z ≠ 0 := by
    have h1 := Metric.tendsto_nhds.mp hA.continuousAt ‖a‖ hapos
    filter_upwards [h1] with z hz
    rw [dist_eq_norm, hH0] at hz
    intro h0
    rw [h0] at hz
    simp only [zero_sub, norm_neg] at hz
    exact absurd hz (lt_irrefl _)
  have hEvρ : ∀ᶠ z in 𝓝 (0:ℂ), ‖z‖ < ρ := by
    filter_upwards [Metric.ball_mem_nhds (0:ℂ) hρ] with z hz
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hEv1 : ∀ᶠ z in 𝓝 (0:ℂ), ‖z‖ ≤ 1 := by
    filter_upwards [Metric.ball_mem_nhds (0:ℂ) one_pos] with z hz
    simp only [Metric.mem_ball, dist_zero_right] at hz
    exact le_of_lt hz
  have hEv : ∀ᶠ z in 𝓝 (0:ℂ), ‖Hfun f q a z‖ ≤ BH ∧ ‖F z‖ ≤ BF ∧ ‖FH z‖ ≤ BFH ∧
      ‖z^q * Hfun f q a z‖ ≤ 1/2 ∧ Hfun f q a z ≠ 0 ∧ ‖z‖ < ρ ∧ ‖z‖ ≤ 1 := by
    filter_upwards [hEvH, hEvF, hEvFH, hEvs, hEvne, hEvρ, hEv1] with z h1 h2 h3 h4 h5 h6 h7
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp hEv
  have hδ' : ∀ z : ℂ, ‖z‖ < δ → ‖Hfun f q a z‖ ≤ BH ∧ ‖F z‖ ≤ BF ∧ ‖FH z‖ ≤ BFH ∧
      ‖z^q * Hfun f q a z‖ ≤ 1/2 ∧ Hfun f q a z ≠ 0 ∧ ‖z‖ < ρ ∧ ‖z‖ ≤ 1 :=
    fun z hz => hδ (by simpa [Metric.mem_ball, dist_zero_right] using hz)
  set CT : ℝ := ∑ i ∈ Finset.Icc 1 (q-1),
      ‖gcoef f q a i / ((i:ℂ)-(q:ℂ))‖ * C1 * BH^2 with hCT
  set A1 : ℝ := (q+1)/(2*‖a‖) * BH * BFH + BF * BH with hA1
  set A2 : ℝ := ‖cc q a‖ * C2 * BH^3 + CT + ‖gcoef f q a q + ((q:ℂ)+1)/2‖ * BH^2 with hA2
  set C : ℝ := A1 + A2 with hCdef
  have hCTnn : 0 ≤ CT := by
    rw [hCT]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (norm_nonneg _) hC1nn) (sq_nonneg BH)
  have hA1nn : 0 ≤ A1 := by
    rw [hA1]
    have h1 : 0 ≤ (q+1 : ℝ)/(2*‖a‖) := div_nonneg (by positivity) (by positivity)
    have h2 : 0 ≤ (q+1 : ℝ)/(2*‖a‖) * BH * BFH := mul_nonneg (mul_nonneg h1 hBHnn) hBFHnn
    have h3 : 0 ≤ BF * BH := mul_nonneg hBFnn hBHnn
    linarith
  have hA2nn : 0 ≤ A2 := by
    rw [hA2]
    have h1 : 0 ≤ ‖cc q a‖ * C2 * BH^3 := mul_nonneg (mul_nonneg (norm_nonneg _) hC2nn) (by positivity)
    have h2 : 0 ≤ ‖gcoef f q a q + ((q:ℂ)+1)/2‖ * BH^2 := mul_nonneg (norm_nonneg _) (by positivity)
    linarith
  refine ⟨δ, C, hδpos, ?_, ?_⟩
  · rw [hCdef]; linarith
  · intro z hzV hzδ
    obtain ⟨hHle, hFle, hFHle, hsle, hHz, hzρ, hz1⟩ := hδ' z hzδ
    obtain ⟨hzpos, _, _⟩ := (hgeo.mem_petal_iff j z).mp hzV
    have hz0 : z ≠ 0 := norm_pos_iff.mp hzpos
    have hzqne : z^q ≠ 0 := pow_ne_zero _ hz0
    have hzball : z ∈ Metric.ball (0:ℂ) ρ := by
      simpa [Metric.mem_ball, dist_zero_right] using hzρ
    have hrez : 0 < (z^q/cc q a).re := petal_re_div_cc hgeo hM hzV
    set s : ℂ := z^q * Hfun f q a z with hs
    have hfz : f z = z * (1+s) := by rw [hs]; exact hb.hf_eq z
    have hune : (1+s) ≠ 0 := by rw [hs]; exact hb.hunit_ne z hzball
    have hure : 0 < ((1+s)^q).re := by rw [hs]; exact hb.hunit_re z hzball
    have harg : |(1+s).arg| * (q:ℝ) < Real.pi := by rw [hs]; exact hb.hunit_arg z hzball
    have hlog := lbranch_sub hq hune hrez hure harg hfz
    have hsplit := Acorr_sub hfz hlog
    set ε₂ : ℂ := ((1+s)⁻¹)^q - 1 + (q:ℂ)*s - ((q:ℂ)*((q:ℂ)+1)/2)*s^2 with hε₂def
    have hε₂b : ‖ε₂‖ ≤ C2 * ‖s‖^3 := by rw [hε₂def]; exact hC2 s hsle
    have hε₂eq : ((1+s)⁻¹)^q - 1 = -((q:ℂ)*s) + ((q:ℂ)*((q:ℂ)+1)/2)*s^2 + ε₂ := by
      rw [hε₂def]; ring
    set ε₁ : ℕ → ℂ := fun i => ((1+s)⁻¹)^(q-i) - 1 + ((q:ℂ)-(i:ℂ))*s with hε₁def
    have hε₁b : ∀ i ∈ Finset.Icc 1 (q-1), ‖ε₁ i‖ ≤ C1 * ‖s‖^2 := by
      intro i hi
      rw [Finset.mem_Icc] at hi
      have hi1 : 1 ≤ q - i := by omega
      have hi2 : q - i ≤ q := Nat.sub_le _ _
      have h := hC1 (q-i) s hi1 hi2 hsle
      have hcast : (((q-i : ℕ)) : ℂ) = (q:ℂ) - (i:ℂ) := by
        rw [Nat.cast_sub (by omega : i ≤ q)]
      have h' : ‖((1+s)⁻¹)^(q-i) - 1 + ((q:ℂ)-(i:ℂ))*s‖ ≤ C1 * ‖s‖^2 := by
        rw [← hcast]; exact h
      rw [hε₁def]
      exact h'
    have hε₁eq : ∀ i, ((1+s)⁻¹)^(q-i) - 1 = ((i:ℂ)-(q:ℂ))*s + ε₁ i := by
      intro i; rw [hε₁def]; ring
    set ε₃ : ℂ := Complex.log (1+s) - s with hε₃def
    have hε₃eq : Complex.log (1+s) = s + ε₃ := by rw [hε₃def]; ring
    have hε₃b : ‖ε₃‖ ≤ ‖s‖^2 := by
      rw [hε₃def]
      have h1 : ‖s‖ < 1 := lt_of_le_of_lt hsle (by norm_num)
      have h2 := Complex.norm_log_one_add_sub_self_le h1
      have h3 : (1 - ‖s‖)⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ (by linarith) (by norm_num : (0:ℝ) < 2)]
        linarith [hsle]
      calc ‖Complex.log (1+s) - s‖ ≤ ‖s‖^2 * (1 - ‖s‖)⁻¹ / 2 := h2
        _ ≤ ‖s‖^2 * 2 / 2 := by gcongr
        _ = ‖s‖^2 := by ring
    set SS : ℂ := ∑ i ∈ Finset.Icc 1 (q-1), gcoef f q a i * z^i with hSSdef
    set MSε : ℂ := ∑ i ∈ Finset.Icc 1 (q-1),
      gcoef f q a i / ((i:ℂ)-(q:ℂ)) * (z⁻¹)^(q-i) * ε₁ i with hMSεdef
    set Tz : ℂ := ∑ i ∈ Finset.range q, gcoef f q a i * z^i with hTzdef
    set A : ℂ := -(((q:ℂ)+1)/(2*a)) * Hfun f q a z * FH z - F z * Hfun f q a z with hAdef
    set ERR : ℂ := cc q a * (z^q)⁻¹ * ε₂ + MSε + (gcoef f q a q + ((q:ℂ)+1)/2) * ε₃ with hERRdef
    have hzq1 : (z^q)⁻¹ * s = Hfun f q a z := by
      rw [hs, ← mul_assoc, inv_mul_cancel₀ hzqne, one_mul]
    have hzq2 : (z^q)⁻¹ * s^2 = z^q * (Hfun f q a z)^2 := by
      have hsq : (z^q)⁻¹ * (z^q)^2 = z^q := by
        rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hzqne, one_mul]
      rw [hs, mul_pow, ← mul_assoc, hsq]
    have hzi : ∀ i, i ≤ q → (z⁻¹)^(q-i) * s = z^i * Hfun f q a z := by
      intro i hi
      have hq1 : (z^(q-i))⁻¹ * z^q = z^i := by
        rw [inv_mul_eq_div, div_eq_iff (pow_ne_zero _ hz0), ← pow_add]
        congr 1; omega
      rw [hs, inv_pow, ← mul_assoc, hq1]
    have hms : (∑ i ∈ Finset.Icc 1 (q-1),
          gcoef f q a i / ((i:ℂ)-(q:ℂ)) * (z⁻¹)^(q-i) * (((1+s)⁻¹)^(q-i) - 1))
        = SS * Hfun f q a z + MSε := by
      rw [hSSdef, hMSεdef, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_Icc] at hi
      have hK : gcoef f q a i / ((i:ℂ)-(q:ℂ)) * ((i:ℂ)-(q:ℂ)) = gcoef f q a i := by
        have hneq : ((i:ℂ)-(q:ℂ)) ≠ 0 := by
          simp only [sub_ne_zero]; exact_mod_cast (by omega : i ≠ q)
        field_simp
      rw [hε₁eq i]
      linear_combination (gcoef f q a i) * (hzi i (by omega)) +
        ((z⁻¹)^(q-i) * s) * hK
    have hTH : Tz * Hfun f q a z = 1 - gcoef f q a q * (z^q * Hfun f q a z)
        - z^q * z * F z * Hfun f q a z := by
      have h1 : (Hfun f q a z)⁻¹ * Hfun f q a z = 1 := inv_mul_cancel₀ hHz
      rw [hF z, add_mul, add_mul, pow_succ] at h1
      rw [hTzdef]
      linear_combination h1
    have hTsp : Tz = gcoef f q a 0 + SS := by
      rw [hTzdef, hSSdef]
      simpa using sum_range_eq_zero_add_Icc hq (fun i => gcoef f q a i * z^i)
    have hcombine : -((q:ℂ)*cc q a) * Hfun f q a z + SS * Hfun f q a z
        = Tz * Hfun f q a z := by
      rw [hTsp, add_mul, neg_q_cc hq ha, gcoef_zero hH0]
    have hcc2 : cc q a * ((q:ℂ)*((q:ℂ)+1)/2) = -(((q:ℂ)+1)/(2*a)) := by
      have hq0 : (q:ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
      simp only [cc]
      field_simp
    have hFH' : Hfun f q a z = a + z * FH z := by rw [hFH z, hH0]
    have hfirst : cc q a * (z^q)⁻¹ * (((1+s)⁻¹)^q - 1)
        = -((q:ℂ)*cc q a) * Hfun f q a z
          + (cc q a * ((q:ℂ)*((q:ℂ)+1)/2)) * (z^q * (Hfun f q a z)^2)
          + cc q a * (z^q)⁻¹ * ε₂ := by
      rw [hε₂eq]
      linear_combination (-((q:ℂ)*cc q a)) * hzq1 + (cc q a * ((q:ℂ)*((q:ℂ)+1)/2)) * hzq2
    have hlast : (gcoef f q a q + ((q:ℂ)+1)/2) * Complex.log (1+s)
        = (gcoef f q a q + ((q:ℂ)+1)/2) * (z^q * Hfun f q a z)
          + (gcoef f q a q + ((q:ℂ)+1)/2) * ε₃ := by
      rw [hε₃eq]
      linear_combination (gcoef f q a q + ((q:ℂ)+1)/2) * hs
    have hBig : -((q:ℂ)*cc q a) * Hfun f q a z + SS * Hfun f q a z
          + (cc q a * ((q:ℂ)*((q:ℂ)+1)/2)) * (z^q * (Hfun f q a z)^2)
          + (gcoef f q a q + ((q:ℂ)+1)/2) * (z^q * Hfun f q a z) - 1
        = z^q * z * A := by
      rw [hAdef, hcombine, hTH, hcc2]
      rw [show (1 - gcoef f q a q * (z^q * Hfun f q a z) - z^q * z * F z * Hfun f q a z
            + (-(((q:ℂ)+1)/(2*a))) * (z^q * (Hfun f q a z)^2)
            + (gcoef f q a q + ((q:ℂ)+1)/2) * (z^q * Hfun f q a z) - 1)
          = (((q:ℂ)+1)/2) * (z^q * Hfun f q a z)
            - (((q:ℂ)+1)/(2*a)) * (z^q * (Hfun f q a z)^2)
            - z^q * z * F z * Hfun f q a z from by ring]
      rw [show Hfun f q a z = a + z * FH z from hFH']
      field_simp
      ring
    have hE : Acorr f q a (f z) - Acorr f q a z - 1 = z^q * z * A + ERR := by
      rw [hsplit, hms, hfirst, hlast, hERRdef]
      linear_combination hBig
    have hsn : ‖s‖ ≤ ‖z‖^q * BH := by
      rw [hs, norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left hHle (pow_nonneg (norm_nonneg z) q)
    have hAnorm : ‖A‖ ≤ A1 := by
      rw [hAdef, hA1]
      have hc : ‖-(((q:ℂ)+1)/(2*a))‖ = (q+1)/(2*‖a‖) := by
        have hcast : ((q:ℂ)+1) = ((q+1 : ℕ) : ℂ) := by rw [Nat.cast_add, Nat.cast_one]
        have h1 : ‖((q:ℂ)+1)‖ = (q+1 : ℝ) := by
          rw [hcast, Complex.norm_natCast, Nat.cast_add, Nat.cast_one]
        have h2 : ‖(2:ℂ)‖ = (2:ℝ) := by norm_num
        rw [norm_neg, norm_div, norm_mul, h1, h2]
      calc ‖-(((q:ℂ)+1)/(2*a)) * Hfun f q a z * FH z - F z * Hfun f q a z‖
          ≤ ‖-(((q:ℂ)+1)/(2*a)) * Hfun f q a z * FH z‖ + ‖F z * Hfun f q a z‖ := norm_sub_le _ _
        _ = (q+1)/(2*‖a‖) * ‖Hfun f q a z‖ * ‖FH z‖ + ‖F z‖ * ‖Hfun f q a z‖ := by
            rw [norm_mul, norm_mul, norm_mul, hc]
        _ ≤ (q+1)/(2*‖a‖) * BH * BFH + BF * BH := by
            have hc1 : 0 ≤ (q+1)/(2*‖a‖) := div_nonneg (by positivity) (by positivity)
            gcongr
    have hERRnorm : ‖ERR‖ ≤ A2 * ‖z‖^(q+1) := by
      rw [hERRdef, hA2]
      have hs3 : ‖s‖^3 ≤ (‖z‖^q * BH)^3 := by gcongr
      have h1 : ‖cc q a * (z^q)⁻¹ * ε₂‖ ≤ ‖cc q a‖ * C2 * BH^3 * ‖z‖^(q+1) := by
        calc ‖cc q a * (z^q)⁻¹ * ε₂‖ ≤ ‖cc q a‖ * ‖(z^q)⁻¹‖ * ‖ε₂‖ := by rw [norm_mul, norm_mul]
          _ = ‖cc q a‖ * ((‖z‖^q)⁻¹ * ‖ε₂‖) := by rw [norm_inv, norm_pow]; ring
          _ ≤ ‖cc q a‖ * ((‖z‖^q)⁻¹ * (C2 * ‖s‖^3)) := by gcongr
          _ ≤ ‖cc q a‖ * ((‖z‖^q)⁻¹ * (C2 * (‖z‖^q*BH)^3)) := by gcongr
          _ = ‖cc q a‖ * C2 * ((‖z‖^q)⁻¹ * (‖z‖^q*BH)^3) := by ring
          _ ≤ ‖cc q a‖ * C2 * (‖z‖^(q+1)*BH^3) := by
              refine mul_le_mul_of_nonneg_left (inv_pow_mul_cube_le hq hzpos hz1 hBHnn) ?_
              exact mul_nonneg (norm_nonneg _) hC2nn
          _ = ‖cc q a‖ * C2 * BH^3 * ‖z‖^(q+1) := by ring
      have h2 : ‖MSε‖ ≤ CT * ‖z‖^(q+1) := by
        rw [hMSεdef, hCT]
        calc ‖∑ i ∈ Finset.Icc 1 (q-1), gcoef f q a i / ((i:ℂ)-(q:ℂ)) * (z⁻¹)^(q-i) * ε₁ i‖
            ≤ ∑ i ∈ Finset.Icc 1 (q-1),
                ‖gcoef f q a i / ((i:ℂ)-(q:ℂ)) * (z⁻¹)^(q-i) * ε₁ i‖ := norm_sum_le _ _
          _ ≤ ∑ i ∈ Finset.Icc 1 (q-1),
                ‖gcoef f q a i / ((i:ℂ)-(q:ℂ))‖ * C1 * BH^2 * ‖z‖^(q+1) := by
              refine Finset.sum_le_sum fun i hi => ?_
              rw [Finset.mem_Icc] at hi
              have hi1 : 1 ≤ i := by omega
              have hi2 : i ≤ q := by omega
              have hε := hε₁b i (by rw [Finset.mem_Icc]; omega)
              have hs2 : ‖s‖^2 ≤ (‖z‖^q*BH)^2 := by gcongr
              calc ‖gcoef f q a i / ((i:ℂ)-(q:ℂ)) * (z⁻¹)^(q-i) * ε₁ i‖
                  = ‖gcoef f q a i / ((i:ℂ)-(q:ℂ))‖ * ‖(z⁻¹)^(q-i)‖ * ‖ε₁ i‖ := by
                    rw [norm_mul, norm_mul]
                _ ≤ ‖gcoef f q a i / ((i:ℂ)-(q:ℂ))‖ * ‖(z⁻¹)^(q-i)‖ * (C1*‖s‖^2) := by gcongr
                _ = ‖gcoef f q a i / ((i:ℂ)-(q:ℂ))‖ * C1 * ((‖z‖^(q-i))⁻¹ * ‖s‖^2) := by
                    rw [norm_inv_pow]; ring
                _ ≤ ‖gcoef f q a i / ((i:ℂ)-(q:ℂ))‖ * C1 * (‖z‖^(q+1) * BH^2) := by
                    have hb1 : (‖z‖^(q-i))⁻¹ * ‖s‖^2 ≤ (‖z‖^(q-i))⁻¹ * (‖z‖^q*BH)^2 := by
                      gcongr
                    have hb2 : (‖z‖^(q-i))⁻¹ * (‖z‖^q*BH)^2 ≤ ‖z‖^(q+1)*BH^2 :=
                      inv_pow_mul_sq_le hi1 hi2 hzpos hz1 hBHnn
                    have hb3 : 0 ≤ ‖gcoef f q a i / ((i:ℂ)-(q:ℂ))‖ * C1 :=
                      mul_nonneg (norm_nonneg _) hC1nn
                    nlinarith [hb1, hb2, hb3, sq_nonneg BH, pow_nonneg (norm_nonneg z) (q+1)]
                _ = ‖gcoef f q a i / ((i:ℂ)-(q:ℂ))‖ * C1 * BH^2 * ‖z‖^(q+1) := by ring
          _ = (∑ i ∈ Finset.Icc 1 (q-1),
                  ‖gcoef f q a i / ((i:ℂ)-(q:ℂ))‖ * C1 * BH^2) * ‖z‖^(q+1) := by
              rw [Finset.sum_mul]
      have h3 : ‖(gcoef f q a q + ((q:ℂ)+1)/2) * ε₃‖
          ≤ ‖gcoef f q a q + ((q:ℂ)+1)/2‖ * BH^2 * ‖z‖^(q+1) := by
        calc ‖(gcoef f q a q + ((q:ℂ)+1)/2) * ε₃‖
            ≤ ‖gcoef f q a q + ((q:ℂ)+1)/2‖ * ‖ε₃‖ := by rw [norm_mul]
          _ ≤ ‖gcoef f q a q + ((q:ℂ)+1)/2‖ * ‖s‖^2 := by gcongr
          _ ≤ ‖gcoef f q a q + ((q:ℂ)+1)/2‖ * ((‖z‖^q*BH)^2) := by gcongr
          _ ≤ ‖gcoef f q a q + ((q:ℂ)+1)/2‖ * (‖z‖^(q+1)*BH^2) := by
              gcongr; exact sq_le hq (norm_nonneg z) hz1 hBHnn
          _ = ‖gcoef f q a q + ((q:ℂ)+1)/2‖ * BH^2 * ‖z‖^(q+1) := by ring
      calc ‖cc q a * (z^q)⁻¹ * ε₂ + MSε + (gcoef f q a q + ((q:ℂ)+1)/2) * ε₃‖
          ≤ ‖cc q a * (z^q)⁻¹ * ε₂ + MSε‖ + ‖(gcoef f q a q + ((q:ℂ)+1)/2) * ε₃‖ := norm_add_le _ _
        _ ≤ (‖cc q a * (z^q)⁻¹ * ε₂‖ + ‖MSε‖) + ‖(gcoef f q a q + ((q:ℂ)+1)/2) * ε₃‖ := by
            gcongr; exact norm_add_le _ _
        _ ≤ (‖cc q a‖ * C2 * BH^3 * ‖z‖^(q+1) + CT * ‖z‖^(q+1))
              + ‖gcoef f q a q + ((q:ℂ)+1)/2‖ * BH^2 * ‖z‖^(q+1) := by
            gcongr
        _ = (‖cc q a‖ * C2 * BH^3 + CT + ‖gcoef f q a q + ((q:ℂ)+1)/2‖ * BH^2) * ‖z‖^(q+1) := by
            ring
    calc ‖Acorr f q a (f z) - Acorr f q a z - 1‖ = ‖z^q * z * A + ERR‖ := by rw [hE]
      _ ≤ ‖z^q * z * A‖ + ‖ERR‖ := norm_add_le _ _
      _ = ‖z‖^q * ‖z‖ * ‖A‖ + ‖ERR‖ := by simp only [norm_mul, norm_pow]
      _ = ‖z‖^(q+1) * ‖A‖ + ‖ERR‖ := by
          rw [show ‖z‖^q * ‖z‖ = ‖z‖^(q+1) from by rw [pow_succ]]
      _ ≤ ‖z‖^(q+1) * A1 + A2 * ‖z‖^(q+1) := by
          gcongr
      _ = C * ‖z‖^(q+1) := by rw [hCdef]; ring




/-- If `A ≤ x ≤ B` with `A > 0` then `|log x| ≤ |log A| + |log B|`. -/
lemma abs_log_le_of_mem {x A B : ℝ} (hA : 0 < A) (hxB : x ≤ B) (hAx : A ≤ x) :
    |Real.log x| ≤ |Real.log A| + |Real.log B| := by
  have h1 : Real.log A ≤ Real.log x := Real.log_le_log hA hAx
  have h2 : Real.log x ≤ Real.log B := Real.log_le_log (lt_of_lt_of_le hA hAx) hxB
  rw [abs_le]
  constructor <;> linarith [neg_abs_le (Real.log A), le_abs_self (Real.log B),
    abs_nonneg (Real.log A), abs_nonneg (Real.log B)]

lemma far_bound {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {a : ℂ} {ρ M : ℝ}
    (hd : PetalDatum f D q a ρ M) (hMeps : ‖cc q a‖ / M ≤ (1/4)^q) (j : Fin q)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1/4) :
    ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ z ∈ petal q a M j, δ ≤ ‖z‖ →
      ‖Acorr f q a (f z) - Acorr f q a z - 1‖ ≤ M₀ := by
  obtain ⟨hS, hρ, hb, hM, hRM, hgeo⟩ := hd
  have hq : 1 ≤ q := hb.hq
  have ha : a ≠ 0 := hb.ha
  have hcc : cc q a ≠ 0 := hgeo.cc_ne_zero
  have hccpos : 0 < ‖cc q a‖ := norm_pos_iff.mpr hcc
  have hMpos : 0 < M := hM
  have hmaps := petal_mapsTo hb hM hRM hgeo (fun u hu h => log_pow_eq hq hu h)
  set Bu : ℝ := 1 + 5/(4*M) with hBu
  set U : ℝ := (1/4)/δ with hU
  have hBu1 : 1 ≤ Bu := by
    rw [hBu]
    have h : 0 ≤ 5/(4*M) := by positivity
    linarith
  have hBunn : 0 ≤ Bu := le_trans zero_le_one hBu1
  have hUge1 : 1 ≤ U := by
    rw [hU, le_div_iff₀ hδ]
    linarith
  have hUnn : 0 ≤ U := le_trans zero_le_one hUge1
  set Mo : ℝ := ‖cc q a‖ * (1/δ)^q * (Bu + 1)
      + (∑ i ∈ Finset.Icc 1 (q-1),
          ‖gcoef f q a i / ((i:ℂ)-(q:ℂ))‖ * (1/δ)^(q-1) * (Bu * U^(q-1) + 1))
      + ‖gcoef f q a q + ((q:ℂ)+1)/2‖ * (|Real.log Bu| + |Real.log U| + Real.pi)
      + 1 with hMo
  refine ⟨Mo, ?_, ?_⟩
  · rw [hMo]
    have h1 : 0 ≤ ‖cc q a‖ * (1/δ)^q * (Bu + 1) := by positivity
    have h2 : 0 ≤ ∑ i ∈ Finset.Icc 1 (q-1),
        ‖gcoef f q a i / ((i:ℂ)-(q:ℂ))‖ * (1/δ)^(q-1) * (Bu * U^(q-1) + 1) :=
      Finset.sum_nonneg fun i _ => by positivity
    have h3 : 0 ≤ ‖gcoef f q a q + ((q:ℂ)+1)/2‖ * (|Real.log Bu| + |Real.log U| + Real.pi) := by
      positivity
    linarith
  · intro z hzV hzδ
    obtain ⟨hzpos, _, _⟩ := (hgeo.mem_petal_iff j z).mp hzV
    have hz0 : z ≠ 0 := norm_pos_iff.mp hzpos
    have hzρ : ‖z‖ < ρ := by
      have h1 : ‖z‖^q < ρ^q := lt_trans (hgeo.petal_norm_pow_lt j z hzV) hRM
      exact lt_of_pow_lt_pow_left₀ q hρ.le h1
    have hzball : z ∈ Metric.ball (0:ℂ) ρ := by
      simpa [Metric.mem_ball, dist_zero_right] using hzρ
    have hrez : 0 < (z^q/cc q a).re := petal_re_div_cc hgeo hM hzV
    set s : ℂ := z^q * Hfun f q a z with hs
    set u : ℂ := 1 + s with hu
    have hune : u ≠ 0 := by rw [hu, hs]; exact hb.hunit_ne z hzball
    have hure : 0 < (u^q).re := by rw [hu, hs]; exact hb.hunit_re z hzball
    have harg : |u.arg| * (q:ℝ) < Real.pi := by rw [hu, hs]; exact hb.hunit_arg z hzball
    have hfz : f z = z * u := by rw [hu, hs]; exact hb.hf_eq z
    have hlog := lbranch_sub hq hune hrez hure harg hfz
    have hsplit := Acorr_sub hfz hlog
    -- `f z` is again in the petal
    have hfzV : f z ∈ petal q a M j := by
      rcases hmaps j hzV with h | h
      · exact h
      · exact absurd h (by rw [hfz]; exact mul_ne_zero hz0 hune)
    have hfznorm : ‖f z‖ < 1/4 := by
      have h1 : ‖f z‖^q < (1/4)^q :=
        lt_of_lt_of_le (hgeo.petal_norm_pow_lt j (f z) hfzV) hMeps
      exact lt_of_pow_lt_pow_left₀ q (by norm_num) h1
    have hu_le : ‖u‖ ≤ U := by
      have h1 : u = f z / z := by
        rw [hu]
        show (1:ℂ) + s = f z / z
        rw [hs, hb.hf_eq z]; field_simp
      rw [h1, hU, norm_div]
      have ha1 : ‖f z‖ / ‖z‖ ≤ ‖f z‖ / δ :=
        div_le_div_of_nonneg_left (norm_nonneg _) hδ hzδ
      have ha2 : ‖f z‖ / δ ≤ (1/4)/δ := div_le_div_of_nonneg_right hfznorm.le hδ.le
      linarith
    -- the chart bound for `u^{-q}`
    have huq1 : ‖(u⁻¹)^q - 1‖ ≤ 5/(4*M) := by
      have hkey : (u⁻¹)^q - 1 = (z^q/cc q a) * (chartQ q a (f z) - chartQ q a z) := by
        rw [chartQ, chartQ, hfz, mul_pow, inv_pow]
        field_simp
      have hchart := hb.hchart z hzpos hzρ
      have hc1 : ‖chartQ q a (f z) - chartQ q a z‖ ≤ 5/4 := by
        have h3 := norm_add_le (chartQ q a (f z) - chartQ q a z - 1) (1:ℂ)
        rw [sub_add_cancel, norm_one] at h3
        linarith
      rw [hkey, norm_mul, norm_div]
      calc ‖z^q‖ / ‖cc q a‖ * ‖chartQ q a (f z) - chartQ q a z‖
          ≤ (‖cc q a‖/M) / ‖cc q a‖ * (5/4) := by
            gcongr
            simpa [norm_pow] using le_of_lt (hgeo.petal_norm_pow_lt j z hzV)
        _ = 5/(4*M) := by
            field_simp
    have hu_inv : ‖(u⁻¹)^q‖ ≤ Bu := by
      have h3 := norm_add_le ((u⁻¹)^q - 1) (1:ℂ)
      rw [sub_add_cancel, norm_one] at h3
      rw [hBu]
      linarith
    have huq_ge : (Bu)⁻¹ ≤ ‖u^q‖ := by
      have h1 : u^q = ((u⁻¹)^q)⁻¹ := by rw [inv_pow, inv_inv]
      rw [h1, norm_inv]
      exact (inv_le_inv₀ (lt_of_lt_of_le zero_lt_one hBu1)
        (norm_pos_iff.mpr (pow_ne_zero _ (inv_ne_zero hune)))).mpr hu_inv
    have hlog_uq : |Real.log ‖u^q‖| ≤ |Real.log Bu| + q * |Real.log U| := by
      have h1 : 1/Bu ≤ ‖u^q‖ := by rw [one_div]; exact huq_ge
      have h2 : ‖u^q‖ ≤ U^q := by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg u) hu_le q
      have h3 := abs_log_le_of_mem (A := 1/Bu) (B := U^q) (by positivity) h2 h1
      rw [one_div, Real.log_inv, abs_neg, Real.log_pow] at h3
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (q:ℝ))] at h3
      exact h3
    have hlogu : ‖Complex.log u‖ ≤ |Real.log Bu| + |Real.log U| + Real.pi := by
      have h1 : Complex.log (u^q) = (q:ℂ) * Complex.log u := log_pow_eq hq hune harg
      have hq0 : (0:ℝ) < q := by exact_mod_cast hq
      have h2 : ‖Complex.log u‖ * q = ‖Complex.log (u^q)‖ := by
        rw [h1, norm_mul, Complex.norm_natCast, mul_comm]
      have h4 : ‖Complex.log u‖ * q ≤ (|Real.log Bu| + |Real.log U| + Real.pi) * q := by
        rw [h2]
        calc ‖Complex.log (u^q)‖ ≤ |Real.log ‖u^q‖| + Real.pi := norm_log_le _
          _ ≤ |Real.log Bu| + q * |Real.log U| + Real.pi := by linarith [hlog_uq]
          _ ≤ (|Real.log Bu| + |Real.log U| + Real.pi) * q := by
              have hq1 : (1:ℝ) ≤ q := by exact_mod_cast hq
              have hp : 0 ≤ Real.pi := Real.pi_pos.le
              nlinarith [hq1, abs_nonneg (Real.log Bu), abs_nonneg (Real.log U), hp]
      exact le_of_mul_le_mul_right h4 hq0
    -- the sum term
    have hsum : ‖∑ i ∈ Finset.Icc 1 (q-1),
          gcoef f q a i / ((i:ℂ)-(q:ℂ)) * (z⁻¹)^(q-i) * ((u⁻¹)^(q-i) - 1)‖
        ≤ ∑ i ∈ Finset.Icc 1 (q-1),
            ‖gcoef f q a i / ((i:ℂ)-(q:ℂ))‖ * (1/δ)^(q-1) * (Bu * U^(q-1) + 1) := by
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i hi => ?_)
      rw [Finset.mem_Icc] at hi
      have hi1 : 1 ≤ i := hi.1
      have hiq : i ≤ q := by omega
      have hzi : ‖(z⁻¹)^(q-i)‖ ≤ (1/δ)^(q-1) := by
        rw [norm_inv_pow]
        have h1 : δ^(q-1) ≤ ‖z‖^(q-i) := by
          exact le_trans (pow_le_pow_of_le_one hδ.le (le_trans hδ1 (by norm_num)) (by omega))
            (pow_le_pow_left₀ hδ.le hzδ _)
        have h2 : (1/δ)^(q-1) = (δ^(q-1))⁻¹ := by rw [one_div, inv_pow]
        rw [h2]
        exact (inv_le_inv₀ (pow_pos hzpos _) (pow_pos hδ _)).mpr h1
      have hui : ‖(u⁻¹)^(q-i)‖ ≤ Bu * U^(q-1) := by
        have h4 : (u⁻¹)^(q-i) = (u⁻¹)^q * u^i := by
          rw [inv_pow, inv_pow]
          field_simp
          rw [← pow_add, show q - i + i = q from by omega]
        rw [h4, norm_mul]
        have hud : ‖u^i‖ ≤ U^(q-1) := by
          rw [norm_pow]
          exact le_trans (pow_le_pow_left₀ (norm_nonneg u) hu_le i)
            (pow_le_pow_right₀ hUge1 (by omega))
        exact mul_le_mul hu_inv hud (norm_nonneg _) hBunn
      have hu2 : ‖(u⁻¹)^(q-i) - 1‖ ≤ Bu * U^(q-1) + 1 := by
        have h3 := norm_sub_le ((u⁻¹)^(q-i)) (1:ℂ)
        rw [norm_one] at h3
        linarith [hui]
      calc ‖gcoef f q a i / ((i:ℂ)-(q:ℂ)) * (z⁻¹)^(q-i) * ((u⁻¹)^(q-i) - 1)‖
          = ‖gcoef f q a i / ((i:ℂ)-(q:ℂ))‖ * ‖(z⁻¹)^(q-i)‖ * ‖(u⁻¹)^(q-i) - 1‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ ‖gcoef f q a i / ((i:ℂ)-(q:ℂ))‖ * (1/δ)^(q-1) * (Bu * U^(q-1) + 1) := by
            gcongr
    -- assembly
    rw [hsplit]
    set A : ℂ := cc q a * (z^q)⁻¹ * ((u⁻¹)^q - 1) with hAdef
    set B : ℂ := ∑ i ∈ Finset.Icc 1 (q-1),
        gcoef f q a i / ((i:ℂ)-(q:ℂ)) * (z⁻¹)^(q-i) * ((u⁻¹)^(q-i) - 1) with hBdef
    set Cc : ℂ := (gcoef f q a q + ((q:ℂ)+1)/2) * Complex.log u with hCcdef
    have hp1 : ‖A‖ ≤ ‖cc q a‖ * (1/δ)^q * (Bu + 1) := by
      rw [hAdef]
      calc ‖cc q a * (z^q)⁻¹ * ((u⁻¹)^q - 1)‖
          ≤ ‖cc q a‖ * ‖(z^q)⁻¹‖ * ‖(u⁻¹)^q - 1‖ := by rw [norm_mul, norm_mul]
        _ ≤ ‖cc q a‖ * (1/δ)^q * (Bu + 1) := by
            have hz1 : ‖(z^q)⁻¹‖ ≤ (1/δ)^q := by
              rw [norm_inv, norm_pow]
              have hδq : (1/δ)^q = (δ^q)⁻¹ := by rw [one_div, inv_pow]
              rw [hδq]
              exact (inv_le_inv₀ (pow_pos hzpos q) (pow_pos hδ q)).mpr (pow_le_pow_left₀ hδ.le hzδ q)
            have h2 : ‖(u⁻¹)^q - 1‖ ≤ Bu + 1 := by
              have h3 := norm_sub_le ((u⁻¹)^q) (1:ℂ)
              rw [norm_one] at h3
              linarith [hu_inv]
            gcongr
    have hp2 : ‖B‖ ≤ ∑ i ∈ Finset.Icc 1 (q-1),
        ‖gcoef f q a i / ((i:ℂ)-(q:ℂ))‖ * (1/δ)^(q-1) * (Bu * U^(q-1) + 1) := by
      rw [hBdef]; exact hsum
    have hp3 : ‖Cc‖ ≤ ‖gcoef f q a q + ((q:ℂ)+1)/2‖ *
        (|Real.log Bu| + |Real.log U| + Real.pi) := by
      rw [hCcdef, norm_mul]
      exact mul_le_mul_of_nonneg_left hlogu (norm_nonneg _)
    rw [hMo]
    calc ‖A + B + Cc - 1‖
        ≤ ‖A + B + Cc‖ + 1 := by
          have h3 := norm_sub_le (A + B + Cc) 1
          simpa using h3
      _ ≤ (‖A‖ + ‖B‖ + ‖Cc‖) + 1 := by
          have h1 := norm_add_le (A + B) Cc
          have h2 := norm_add_le A B
          linarith
      _ ≤ (‖cc q a‖ * (1/δ)^q * (Bu + 1)
            + (∑ i ∈ Finset.Icc 1 (q-1),
                ‖gcoef f q a i / ((i:ℂ)-(q:ℂ))‖ * (1/δ)^(q-1) * (Bu * U^(q-1) + 1))
            + ‖gcoef f q a q + ((q:ℂ)+1)/2‖ * (|Real.log Bu| + |Real.log U| + Real.pi)) + 1 := by
          linarith [hp1, hp2, hp3]


theorem Acorr_defect {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {a : ℂ} {ρ M : ℝ}
    (hd : Work.Horn.FatouQ.PetalDatum f D q a ρ M)
    (hMeps : ‖Work.Horn.Flower.cc q a‖ / M ≤ (1 / 4) ^ q) (j : Fin q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Work.Horn.Flower.petal q a M j,
      ‖Work.Horn.FatouQ.Acorr f q a (f z) - Work.Horn.FatouQ.Acorr f q a z - 1‖ ≤
        C * ‖z‖ ^ (q + 1) := by
  obtain ⟨δ₀, C₀, hδ₀pos, hC₀nn, hnear⟩ := near_bound hd j
  set δ : ℝ := min δ₀ (1/4) with hδdef
  have hδpos : 0 < δ := lt_min hδ₀pos (by norm_num)
  have hδquarter : δ ≤ 1/4 := min_le_right _ _
  have hδle : δ ≤ δ₀ := min_le_left _ _
  obtain ⟨M₀, hM₀nn, hfar⟩ := far_bound hd hMeps j hδpos hδquarter
  refine ⟨max C₀ (M₀ / δ^(q+1)), le_max_of_le_left hC₀nn, ?_⟩
  intro z hzV
  rcases lt_or_ge ‖z‖ δ with hz | hz
  · refine le_trans (hnear z hzV (lt_of_lt_of_le hz hδle)) ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · have h1 : M₀ ≤ max C₀ (M₀ / δ^(q+1)) * ‖z‖^(q+1) := by
      have hδne : δ^(q+1) ≠ 0 := pow_ne_zero _ (ne_of_gt hδpos)
      have h3 : δ^(q+1) ≤ ‖z‖^(q+1) := pow_le_pow_left₀ hδpos.le hz _
      have h5 : M₀ / δ^(q+1) ≤ max C₀ (M₀ / δ^(q+1)) := le_max_right _ _
      have h6 : 0 ≤ M₀ / δ^(q+1) := div_nonneg hM₀nn (by positivity)
      calc M₀ = (M₀ / δ^(q+1)) * δ^(q+1) := (div_mul_cancel₀ M₀ hδne).symm
        _ ≤ max C₀ (M₀ / δ^(q+1)) * δ^(q+1) :=
            mul_le_mul_of_nonneg_right h5 (by positivity)
        _ ≤ max C₀ (M₀ / δ^(q+1)) * ‖z‖^(q+1) :=
            mul_le_mul_of_nonneg_left h3 (le_trans h6 (le_max_right _ _))
    exact le_trans (hfar z hzV hz) h1

end

end Work.Horn.FatouQ
