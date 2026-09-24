import Mathlib
import Submission.Work.Analysis.Complex.Runge.geometric_pole_push

/-!
# Pushing a pole along a component of the complement

Runge's theorem replaces the poles of a rational function by poles in a prescribed set, and the
elementary step is the following: if `K ⊆ ℂ` is compact, `a ∉ K` and `b` lies in the *same
connected component* of `Kᶜ` as `a`, then `(· - a)⁻¹` is uniformly approximable on `K` by
polynomials in `(· - b)⁻¹`.

The proof is the classical one.  Call `u` *good* if `(· - u)⁻¹` is approximable on `K` by
polynomials in `(· - b)⁻¹`.  The good points form a subset of `Kᶜ` which is clopen in the
subspace `Kᶜ` and contains `b` (there the polynomial `X` is exact), so the connected component
of `b` — which is the component of `a` — lies in it.

* openness: for `u` good and `‖v - u‖` small compared with the distance of `u` to `K`, the
  geometric expansion `(z - v)⁻¹ = Σ_n (v - u)^n (z - u)^{-n-1}` converges uniformly on `K`,
  and every power `(z - u)^{-m}` is approximable (product of approximations); the partial sums
  are therefore approximable to any accuracy, and the tail is small;
* closedness: for `v` close to `u` the uniform estimate
  `‖(z - v)⁻¹ - (z - u)⁻¹‖ ≤ 2 ‖v - u‖ / m²` (`m ≤ ‖z - u‖` on `K`) lets one transport an
  approximation of `(· - u)⁻¹` to one of `(· - v)⁻¹`.

The finite geometric identity is `partialSum_sub_inv` of `Analysis/Complex/Runge/geometric_pole_push`.
-/

open scoped Topology
open Filter Metric

noncomputable section

namespace Work.Analysis.Complex.PolePush

variable {K : Set ℂ} {b : ℂ}

/-- Uniform approximability on `K` by polynomials in `(· - b)⁻¹`. -/
def Approx (K : Set ℂ) (b : ℂ) (f : ℂ → ℂ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ P : Polynomial ℂ, ∀ z ∈ K, ‖f z - P.eval ((z - b)⁻¹)‖ < δ

theorem approx_const (c : ℂ) : Approx K b (fun _ => c) := fun δ hδ =>
  ⟨Polynomial.C c, fun z _ => by rw [Polynomial.eval_C, sub_self, norm_zero]; exact hδ⟩

theorem approx_inv_self : Approx K b (fun z => (z - b)⁻¹) := fun δ hδ =>
  ⟨Polynomial.X, fun z _ => by rw [Polynomial.eval_X, sub_self, norm_zero]; exact hδ⟩

theorem approx_add {f g : ℂ → ℂ} (hf : Approx K b f) (hg : Approx K b g) :
    Approx K b (f + g) := by
  intro δ hδ
  obtain ⟨P, hP⟩ := hf (δ / 2) (by linarith)
  obtain ⟨Q, hQ⟩ := hg (δ / 2) (by linarith)
  refine ⟨P + Q, fun z hz => ?_⟩
  have h1 := hP z hz
  have h2 := hQ z hz
  have hdecomp : f z + g z - (P + Q).eval ((z - b)⁻¹)
      = (f z - P.eval ((z - b)⁻¹)) + (g z - Q.eval ((z - b)⁻¹)) := by
    rw [Polynomial.eval_add]; ring
  show ‖f z + g z - (P + Q).eval ((z - b)⁻¹)‖ < δ
  rw [hdecomp]
  linarith [norm_add_le (f z - P.eval ((z - b)⁻¹)) (g z - Q.eval ((z - b)⁻¹))]

theorem approx_const_mul (c : ℂ) {f : ℂ → ℂ} (hf : Approx K b f) :
    Approx K b (fun z => c * f z) := by
  intro δ hδ
  rcases eq_or_ne c 0 with rfl | hc
  · exact ⟨0, fun z _ => by simp [hδ]⟩
  · obtain ⟨P, hP⟩ := hf (δ / ‖c‖) (by positivity)
    refine ⟨Polynomial.C c * P, fun z hz => ?_⟩
    have h1 := hP z hz
    have hdecomp : c * f z - (Polynomial.C c * P).eval ((z - b)⁻¹)
        = c * (f z - P.eval ((z - b)⁻¹)) := by
      rw [Polynomial.eval_mul, Polynomial.eval_C]; ring
    rw [hdecomp, norm_mul]
    have h2 : ‖c‖ * ‖f z - P.eval ((z - b)⁻¹)‖ < ‖c‖ * (δ / ‖c‖) :=
      mul_lt_mul_of_pos_left h1 (norm_pos_iff.mpr hc)
    rwa [mul_div_cancel₀ _ (norm_ne_zero_iff.mpr hc)] at h2

/-- **Powers of an approximable function are approximable.**  If `(· - u)⁻¹` is approximable on
`K` and bounded by `C ≥ 1` there, then every power `(· - u)^{-(m+1)}` is approximable, with the
error controlled by `min η (C^{m+1})`. -/
theorem approx_pow {u : ℂ} {C : ℝ} (hC : 1 ≤ C) (hbd : ∀ z ∈ K, ‖(z - u)⁻¹‖ ≤ C)
    (h : Approx K b (fun z => (z - u)⁻¹)) :
    ∀ m : ℕ, ∀ η : ℝ, 0 < η → ∃ Q : Polynomial ℂ, ∀ z ∈ K,
      ‖((z - u)⁻¹) ^ (m + 1) - Q.eval ((z - b)⁻¹)‖ < min η (C ^ (m + 1)) := by
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  intro m
  induction m with
  | zero =>
    intro η hη
    obtain ⟨Q, hQ⟩ := h (min η C) (lt_min hη hCpos)
    refine ⟨Q, fun z hz => ?_⟩
    have h1 := hQ z hz
    simpa only [zero_add, pow_one] using h1
  | succ m ih =>
    intro η hη
    have hCp : 0 < C ^ (m + 1) := pow_pos hCpos _
    have hCp2 : 0 < C ^ (m + 2) := pow_pos hCpos _
    obtain ⟨Qm, hQm⟩ := ih (min (η / (4 * C)) (C ^ (m + 1) / 4))
      (lt_min (by positivity) (by positivity))
    obtain ⟨Q1, hQ1⟩ := h (min (η / (8 * C ^ (m + 1))) (C / 4))
      (lt_min (by positivity) (by positivity))
    refine ⟨Qm * Q1, fun z hz => ?_⟩
    have hm := hQm z hz
    have h1 := hQ1 z hz
    have hb := hbd z hz
    have em : ‖((z - u)⁻¹) ^ (m + 1) - Qm.eval ((z - b)⁻¹)‖ < C ^ (m + 1) / 4 :=
      lt_of_lt_of_le hm (le_trans (min_le_left _ _) (min_le_right _ _))
    have em' : ‖((z - u)⁻¹) ^ (m + 1) - Qm.eval ((z - b)⁻¹)‖ < η / (4 * C) :=
      lt_of_lt_of_le hm (le_trans (min_le_left _ _) (min_le_left _ _))
    have e1 : ‖(z - u)⁻¹ - Q1.eval ((z - b)⁻¹)‖ < C / 4 :=
      lt_of_lt_of_le h1 (min_le_right _ _)
    have e1' : ‖(z - u)⁻¹ - Q1.eval ((z - b)⁻¹)‖ < η / (8 * C ^ (m + 1)) :=
      lt_of_lt_of_le h1 (min_le_left _ _)
    have hbm : ‖Qm.eval ((z - b)⁻¹)‖ ≤ (5 / 4) * C ^ (m + 1) := by
      have hdec : Qm.eval ((z - b)⁻¹)
          = (Qm.eval ((z - b)⁻¹) - ((z - u)⁻¹) ^ (m + 1)) + ((z - u)⁻¹) ^ (m + 1) := by ring
      rw [hdec]
      have hAn : ‖((z - u)⁻¹) ^ (m + 1)‖ ≤ C ^ (m + 1) := by
        rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hb _
      have hsub : ‖Qm.eval ((z - b)⁻¹) - ((z - u)⁻¹) ^ (m + 1)‖ < C ^ (m + 1) / 4 := by
        rw [norm_sub_rev]; exact em
      refine le_trans (norm_add_le _ _) ?_
      linarith
    have hkey : ((z - u)⁻¹) ^ (m + 2) - (Qm * Q1).eval ((z - b)⁻¹)
        = (((z - u)⁻¹) ^ (m + 1) - Qm.eval ((z - b)⁻¹)) * (z - u)⁻¹
          + Qm.eval ((z - b)⁻¹) * ((z - u)⁻¹ - Q1.eval ((z - b)⁻¹)) := by
      rw [Polynomial.eval_mul, pow_succ]; ring
    rw [hkey]
    have hbC : 0 < C ^ (m + 1) := hCp
    have t1η : ‖(((z - u)⁻¹) ^ (m + 1) - Qm.eval ((z - b)⁻¹)) * (z - u)⁻¹‖ ≤ η / 4 := by
      rw [norm_mul]
      calc ‖((z - u)⁻¹) ^ (m + 1) - Qm.eval ((z - b)⁻¹)‖ * ‖(z - u)⁻¹‖
          ≤ (η / (4 * C)) * C := mul_le_mul (le_of_lt em') hb (norm_nonneg _) (by positivity)
        _ = η / 4 := by field_simp
    have t1C : ‖(((z - u)⁻¹) ^ (m + 1) - Qm.eval ((z - b)⁻¹)) * (z - u)⁻¹‖
        ≤ C ^ (m + 2) / 4 := by
      rw [norm_mul]
      calc ‖((z - u)⁻¹) ^ (m + 1) - Qm.eval ((z - b)⁻¹)‖ * ‖(z - u)⁻¹‖
          ≤ (C ^ (m + 1) / 4) * C := mul_le_mul (le_of_lt em) hb (norm_nonneg _) (by positivity)
        _ = C ^ (m + 1) * C / 4 := by ring
        _ = C ^ (m + 2) / 4 := by rw [← pow_succ]
    have t2η : ‖Qm.eval ((z - b)⁻¹) * ((z - u)⁻¹ - Q1.eval ((z - b)⁻¹))‖ ≤ 5 / 32 * η := by
      rw [norm_mul]
      calc ‖Qm.eval ((z - b)⁻¹)‖ * ‖(z - u)⁻¹ - Q1.eval ((z - b)⁻¹)‖
          ≤ ((5 / 4) * C ^ (m + 1)) * (η / (8 * C ^ (m + 1))) :=
            mul_le_mul hbm (le_of_lt e1') (norm_nonneg _) (by positivity)
        _ = 5 / 32 * η := by
            field_simp; ring
    have t2C : ‖Qm.eval ((z - b)⁻¹) * ((z - u)⁻¹ - Q1.eval ((z - b)⁻¹))‖
        ≤ 5 / 16 * C ^ (m + 2) := by
      rw [norm_mul]
      calc ‖Qm.eval ((z - b)⁻¹)‖ * ‖(z - u)⁻¹ - Q1.eval ((z - b)⁻¹)‖
          ≤ ((5 / 4) * C ^ (m + 1)) * (C / 4) :=
            mul_le_mul hbm (le_of_lt e1) (norm_nonneg _) (by positivity)
        _ = 5 / 16 * (C ^ (m + 1) * C) := by ring
        _ = 5 / 16 * C ^ (m + 2) := by rw [← pow_succ]
    refine lt_min ?_ ?_
    · have h := le_trans (norm_add_le _ _) (add_le_add t1η t2η); linarith
    · have h := le_trans (norm_add_le _ _) (add_le_add t1C t2C); linarith

/-- If `‖(z - u)⁻¹‖ ≤ C` with `C > 0` then `1 / C ≤ ‖z - u‖`. -/
theorem one_div_le_norm_of_norm_inv_le {z u : ℂ} {C : ℝ} (hC : 0 < C) (hz : z ≠ u)
    (h : ‖(z - u)⁻¹‖ ≤ C) : 1 / C ≤ ‖z - u‖ := by
  have hpos : 0 < ‖z - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  rw [norm_inv] at h
  have hmul : ‖z - u‖ * (‖z - u‖)⁻¹ ≤ ‖z - u‖ * C :=
    mul_le_mul_of_nonneg_left h hpos.le
  rw [mul_inv_cancel₀ (ne_of_gt hpos)] at hmul
  rw [div_le_iff₀ hC]
  exact hmul

/-- If `1 / c ≤ ‖w‖` with `c > 0` then `‖w⁻¹‖ ≤ c`. -/
theorem norm_inv_le_of_one_div_le_norm {w : ℂ} {c : ℝ} (hc : 0 < c)
    (h : 1 / c ≤ ‖w‖) : ‖w⁻¹‖ ≤ c := by
  have hpos : 0 < ‖w‖ := lt_of_lt_of_le (by positivity) h
  rw [norm_inv]
  rw [inv_le_comm₀ hpos hc]
  simpa using h

/-- Pointwise congruence for `Approx`. -/
theorem Approx.congr {f g : ℂ → ℂ} (hf : Approx K b f) (h : ∀ z, f z = g z) : Approx K b g := by
  intro δ hδ
  obtain ⟨P, hP⟩ := hf δ hδ
  exact ⟨P, fun z hz => by rw [← h z]; exact hP z hz⟩

/-- `Approx` of the powers of `(· - u)⁻¹`. -/
theorem approx_pow' {u : ℂ} {C : ℝ} (hC : 1 ≤ C) (hbd : ∀ z ∈ K, ‖(z - u)⁻¹‖ ≤ C)
    (h : Approx K b (fun z => (z - u)⁻¹)) (m : ℕ) :
    Approx K b (fun z => ((z - u)⁻¹) ^ (m + 1)) := by
  intro δ hδ
  obtain ⟨Q, hQ⟩ := approx_pow hC hbd h m δ hδ
  exact ⟨Q, fun z hz => lt_of_lt_of_le (hQ z hz) (min_le_left _ _)⟩

/-- **The partial sums of the geometric expansion are approximable.** -/
theorem approx_geomPartial {u v : ℂ} {C : ℝ} (hC : 1 ≤ C)
    (hbd : ∀ z ∈ K, ‖(z - u)⁻¹‖ ≤ C) (h : Approx K b (fun z => (z - u)⁻¹)) :
    ∀ N : ℕ, Approx K b
      (fun z => ∑ n ∈ Finset.range N, (v - u) ^ n * ((z - u)⁻¹) ^ (n + 1)) := by
  intro N
  induction N with
  | zero => simpa using approx_const (K := K) (b := b) (0 : ℂ)
  | succ N ih =>
    have h1 : Approx K b (fun z => (v - u) ^ N * ((z - u)⁻¹) ^ (N + 1)) :=
      approx_const_mul _ (approx_pow' hC hbd h N)
    refine (approx_add ih h1).congr (fun z => ?_)
    show (∑ n ∈ Finset.range N, (v - u) ^ n * ((z - u)⁻¹) ^ (n + 1))
        + (v - u) ^ N * ((z - u)⁻¹) ^ (N + 1)
      = ∑ n ∈ Finset.range (N + 1), (v - u) ^ n * ((z - u)⁻¹) ^ (n + 1)
    rw [Finset.sum_range_succ]

/-- **The transfer step.**  If `(· - u)⁻¹` is approximable on `K` and `‖v - u‖ ≤ 1/(2C)` where
`C ≥ 1` bounds `(· - u)⁻¹` on `K`, then `(· - v)⁻¹` is approximable on `K` as well. -/
theorem approx_transfer {u v : ℂ} {C : ℝ} (hu : u ∉ K) (hC : 1 ≤ C)
    (hbd : ∀ z ∈ K, ‖(z - u)⁻¹‖ ≤ C) (hρ : ‖v - u‖ ≤ 1 / (2 * C))
    (h : Approx K b (fun z => (z - u)⁻¹)) :
    Approx K b (fun z => (z - v)⁻¹) := by
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hρC : ‖v - u‖ * C ≤ 1 / 2 := by
    have h1 : ‖v - u‖ * C ≤ (1 / (2 * C)) * C :=
      mul_le_mul_of_nonneg_right hρ hCpos.le
    have h2 : (1 / (2 * C)) * C = 1 / 2 := by field_simp
    linarith [h1, h2.le, h2.ge]
  intro δ hδ
  obtain ⟨N, hN1, hN2⟩ : ∃ N : ℕ, 1 ≤ N ∧ (2 * C) * (‖v - u‖ * C) ^ N < δ / 2 := by
    have hρC_lt : ‖v - u‖ * C < 1 := lt_of_le_of_lt hρC (by norm_num)
    have hρC_nn : 0 ≤ ‖v - u‖ * C := mul_nonneg (norm_nonneg _) hCpos.le
    have htend : Tendsto (fun N : ℕ => (2 * C) * (‖v - u‖ * C) ^ N) atTop (nhds 0) := by
      have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hρC_nn hρC_lt
      simpa using hp.const_mul (2 * C)
    obtain ⟨N, hb, h1⟩ := ((htend.eventually (eventually_lt_nhds (by positivity : 0 < δ / 2))).and
      (eventually_ge_atTop 1)).exists
    exact ⟨N, h1, hb⟩
  obtain ⟨Q, hQ⟩ := approx_geomPartial (u := u) (v := v) hC hbd h N (δ / 2) (by linarith)
  refine ⟨Q, fun z hz => ?_⟩
  have hzu : z ≠ u := fun hzu => hu (hzu ▸ hz)
  have hnorm_u : 1 / C ≤ ‖z - u‖ :=
    one_div_le_norm_of_norm_inv_le hCpos hzu (hbd z hz)
  have hρ1 : ‖v - u‖ ≤ 1 / (2 * C) := hρ
  have hnorm_v : 1 / (2 * C) ≤ ‖z - v‖ := by
    have h1 : ‖z - u‖ - ‖v - u‖ ≤ ‖z - v‖ := by
      have h := norm_sub_norm_le (z - u) (v - u)
      rwa [show (z - u) - (v - u) = z - v by ring] at h
    have h2 : 1 / C - 1 / (2 * C) = 1 / (2 * C) := by field_simp; ring
    linarith
  have hzv : z ≠ v := by
    intro hzv
    rw [hzv, sub_self, norm_zero] at hnorm_v
    have : (0:ℝ) < 1 / (2 * C) := by positivity
    linarith
  have hzv_inv : ‖(z - v)⁻¹‖ ≤ 2 * C :=
    norm_inv_le_of_one_div_le_norm (by positivity) hnorm_v
  have htail : ‖(z - v)⁻¹ - ∑ n ∈ Finset.range N, (v - u) ^ n * ((z - u)⁻¹) ^ (n + 1)‖
      ≤ (2 * C) * (‖v - u‖ * C) ^ N := by
    have hsum : ∑ n ∈ Finset.range N, (v - u) ^ n * ((z - u)⁻¹) ^ (n + 1)
        = ∑ n ∈ Finset.range N, (v - u) ^ n / (z - u) ^ (n + 1) := by
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [div_eq_mul_inv, inv_pow]
    have hza : (z - u) ≠ (v - u) := by
      intro h
      apply hzv
      have h' : (z - u) + u = (v - u) + u := by rw [h]
      simpa using h'
    have hbrick := Work.Analysis.Complex.Runge.partialSum_sub_inv (v - u) (z - u)
      (sub_ne_zero.mpr hzu) hza N
    have hzu' : (z - u) ≠ 0 := sub_ne_zero.mpr hzu
    have hzv' : (z - v) ≠ 0 := sub_ne_zero.mpr hzv
    have hpow : ((v - u) * (z - u)⁻¹) ^ N = (v - u) ^ N / (z - u) ^ N := by
      rw [mul_pow, div_eq_mul_inv, inv_pow]
    have hident : (z - v)⁻¹ - ∑ n ∈ Finset.range N, (v - u) ^ n / (z - u) ^ (n + 1)
        = ((v - u) * (z - u)⁻¹) ^ N * (z - v)⁻¹ := by
      rw [hpow, hbrick, show (z - u) - (v - u) = z - v by ring]
      field_simp
      ring
    rw [hsum, hident, norm_mul, norm_pow]
    calc ‖(v - u) * (z - u)⁻¹‖ ^ N * ‖(z - v)⁻¹‖
        = (‖v - u‖ * ‖(z - u)⁻¹‖) ^ N * ‖(z - v)⁻¹‖ := by rw [norm_mul]
      _ ≤ (‖v - u‖ * C) ^ N * (2 * C) := by
          refine mul_le_mul (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left (hbd z hz)
            (norm_nonneg _)) N) hzv_inv (norm_nonneg _) (by positivity)
      _ = (2 * C) * (‖v - u‖ * C) ^ N := by ring
  have hdecomp : (z - v)⁻¹ - Q.eval ((z - b)⁻¹)
      = ((z - v)⁻¹ - ∑ n ∈ Finset.range N, (v - u) ^ n * ((z - u)⁻¹) ^ (n + 1))
        + (∑ n ∈ Finset.range N, (v - u) ^ n * ((z - u)⁻¹) ^ (n + 1)
            - Q.eval ((z - b)⁻¹)) := by ring
  rw [hdecomp]
  have h2 := hQ z hz
  linarith [norm_add_le ((z - v)⁻¹ - ∑ n ∈ Finset.range N, (v - u) ^ n * ((z - u)⁻¹) ^ (n + 1))
      (∑ n ∈ Finset.range N, (v - u) ^ n * ((z - u)⁻¹) ^ (n + 1) - Q.eval ((z - b)⁻¹)),
    htail, hN2]

/-- **Closedness of the good set.**  If arbitrarily close points `v` have `(· - v)⁻¹` approximable
on `K`, then so does `(· - u)⁻¹`. -/
theorem approx_of_near_good {u : ℂ} (hu : u ∉ K) {C : ℝ} (hC : 1 ≤ C)
    (hbd : ∀ z ∈ K, ‖(z - u)⁻¹‖ ≤ C)
    (h : ∀ r : ℝ, 0 < r → ∃ v : ℂ, v ∉ K ∧ ‖v - u‖ < r ∧ Approx K b (fun z => (z - v)⁻¹)) :
    Approx K b (fun z => (z - u)⁻¹) := by
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  intro δ hδ
  obtain ⟨v, _hvK, hvu, hv⟩ :=
    h (min (1 / (2 * C)) (δ / (8 * C ^ 2))) (lt_min (by positivity) (by positivity))
  obtain ⟨Q, hQ⟩ := hv (δ / 2) (by linarith)
  refine ⟨Q, fun z hz => ?_⟩
  have hzu : z ≠ u := fun hzu => hu (hzu ▸ hz)
  have hnorm_u : 1 / C ≤ ‖z - u‖ := one_div_le_norm_of_norm_inv_le hCpos hzu (hbd z hz)
  have hvu' : ‖v - u‖ < 1 / (2 * C) := lt_of_lt_of_le hvu (min_le_left _ _)
  have hvu'' : ‖v - u‖ < δ / (8 * C ^ 2) := lt_of_lt_of_le hvu (min_le_right _ _)
  have hnorm_v : 1 / (2 * C) ≤ ‖z - v‖ := by
    have h1 : ‖z - u‖ - ‖v - u‖ ≤ ‖z - v‖ := by
      have h := norm_sub_norm_le (z - u) (v - u)
      rwa [show (z - u) - (v - u) = z - v by ring] at h
    have h2 : 1 / C - 1 / (2 * C) = 1 / (2 * C) := by field_simp; ring
    linarith [le_of_lt hvu']
  have hzv_inv : ‖(z - v)⁻¹‖ ≤ 2 * C :=
    norm_inv_le_of_one_div_le_norm (by positivity) hnorm_v
  have hzv : z ≠ v := fun hzv => by
    rw [hzv, sub_self, norm_zero] at hnorm_v
    have : (0:ℝ) < 1 / (2 * C) := by positivity
    linarith
  have hclose : ‖(z - u)⁻¹ - (z - v)⁻¹‖ ≤ 2 * C ^ 2 * ‖v - u‖ := by
    have hident : (z - u)⁻¹ - (z - v)⁻¹ = (u - v) * (z - u)⁻¹ * (z - v)⁻¹ := by
      field_simp
      ring
    rw [hident, norm_mul, norm_mul]
    calc ‖u - v‖ * ‖(z - u)⁻¹‖ * ‖(z - v)⁻¹‖
        = ‖v - u‖ * ‖(z - u)⁻¹‖ * ‖(z - v)⁻¹‖ := by rw [norm_sub_rev]
      _ ≤ ‖v - u‖ * C * (2 * C) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left (hbd z hz) (norm_nonneg _)) hzv_inv
            (norm_nonneg _) (by positivity)
      _ = 2 * C ^ 2 * ‖v - u‖ := by ring
  have hdecomp : (z - u)⁻¹ - Q.eval ((z - b)⁻¹)
      = ((z - u)⁻¹ - (z - v)⁻¹) + ((z - v)⁻¹ - Q.eval ((z - b)⁻¹)) := by ring
  rw [hdecomp]
  have h2 := hQ z hz
  have h3 : 2 * C ^ 2 * ‖v - u‖ < δ / 2 := by
    have h4 : 2 * C ^ 2 * ‖v - u‖ < 2 * C ^ 2 * (δ / (8 * C ^ 2)) :=
      mul_lt_mul_of_pos_left hvu'' (by positivity)
    have h5 : 2 * C ^ 2 * (δ / (8 * C ^ 2)) = δ / 4 := by field_simp; ring
    linarith [h4, h5.le, h5.ge]
  linarith [norm_add_le ((z - u)⁻¹ - (z - v)⁻¹) ((z - v)⁻¹ - Q.eval ((z - b)⁻¹)),
    hclose, h3]

/-- **Pushing a pole along a component of the complement.**  Let `K ⊆ ℂ` be compact, `a ∉ K`, and
let `b` lie in the connected component of `a` in `Kᶜ`.  Then `(· - a)⁻¹` is uniformly approximable
on `K` by polynomials in `(· - b)⁻¹`. -/
theorem exists_polynomial_approx_inv {K : Set ℂ} (hK : IsCompact K) {a b : ℂ} (ha : a ∉ K)
    (hb : b ∈ connectedComponentIn Kᶜ a) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Polynomial ℂ, ∀ z ∈ K, ‖(z - a)⁻¹ - P.eval ((z - b)⁻¹)‖ < ε := by
  rcases Set.eq_empty_or_nonempty K with hKempty | hKne
  · subst hKempty
    exact ⟨0, fun z hz => absurd hz (Set.notMem_empty z)⟩
  have hbK : b ∈ Kᶜ := connectedComponentIn_subset Kᶜ a hb
  have haK : a ∈ Kᶜ := connectedComponentIn_nonempty_iff.mp ⟨b, hb⟩
  haveI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK
  set G : Set ↥(Kᶜ) := {u | Approx K b (fun z => (z - (u : ℂ))⁻¹)} with hG
  have hbmem : (⟨b, hbK⟩ : ↥(Kᶜ)) ∈ G := by
    rw [hG]
    exact approx_inv_self
  have hGopen : IsOpen G := by
    rw [isOpen_iff_mem_nhds]
    intro u hu
    rw [hG] at hu
    have huK : (u : ℂ) ∉ K := u.2
    have hd : 0 < Metric.infDist (u : ℂ) K :=
      (hK.isClosed.notMem_iff_infDist_pos hKne).mp huK
    set C : ℝ := max ((Metric.infDist (u : ℂ) K)⁻¹) 1 with hCdef
    have hC1 : 1 ≤ C := le_max_right _ _
    have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC1
    have hbd : ∀ z ∈ K, ‖(z - (u : ℂ))⁻¹‖ ≤ C := by
      intro z hz
      have hle : Metric.infDist (u : ℂ) K ≤ ‖z - (u : ℂ)‖ := by
        have h := Metric.infDist_le_dist_of_mem (x := (u : ℂ)) hz
        rwa [dist_eq_norm, norm_sub_rev] at h
      have hpos : 0 < ‖z - (u : ℂ)‖ := lt_of_lt_of_le hd hle
      rw [norm_inv]
      exact le_trans ((inv_le_inv₀ hpos hd).mpr hle) (le_max_left _ _)
    refine Filter.mem_of_superset (Metric.ball_mem_nhds u
      (show 0 < min (1 / (4 * C)) (Metric.infDist (u : ℂ) K / 4) by positivity)) ?_
    intro v hv
    rw [hG]
    rw [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm] at hv
    have hρ : ‖(v : ℂ) - (u : ℂ)‖ ≤ 1 / (2 * C) := by
      have h1 : ‖(v : ℂ) - (u : ℂ)‖ ≤ 1 / (4 * C) :=
        le_of_lt (lt_of_lt_of_le hv (min_le_left _ _))
      exact le_trans h1 (one_div_le_one_div_of_le (by positivity) (by linarith))
    exact approx_transfer huK hC1 hbd hρ hu
  have hGclosed : IsClosed G := by
    rw [← closure_subset_iff_isClosed]
    intro u hu
    rw [hG]
    have huK : (u : ℂ) ∉ K := u.2
    have hd : 0 < Metric.infDist (u : ℂ) K :=
      (hK.isClosed.notMem_iff_infDist_pos hKne).mp huK
    set C : ℝ := max ((Metric.infDist (u : ℂ) K)⁻¹) 1 with hCdef
    have hC1 : 1 ≤ C := le_max_right _ _
    have hbd : ∀ z ∈ K, ‖(z - (u : ℂ))⁻¹‖ ≤ C := by
      intro z hz
      have hle : Metric.infDist (u : ℂ) K ≤ ‖z - (u : ℂ)‖ := by
        have h := Metric.infDist_le_dist_of_mem (x := (u : ℂ)) hz
        rwa [dist_eq_norm, norm_sub_rev] at h
      have hpos : 0 < ‖z - (u : ℂ)‖ := lt_of_lt_of_le hd hle
      rw [norm_inv]
      exact le_trans ((inv_le_inv₀ hpos hd).mpr hle) (le_max_left _ _)
    refine approx_of_near_good huK hC1 hbd ?_
    intro r hr
    obtain ⟨v, hv, hvu⟩ := Metric.mem_closure_iff.mp hu r hr
    rw [hG] at hv
    refine ⟨(v : ℂ), v.2, ?_, hv⟩
    rwa [Subtype.dist_eq, dist_eq_norm, norm_sub_rev] at hvu
  have hab : (⟨b, hbK⟩ : ↥(Kᶜ)) ∈ connectedComponent (⟨a, haK⟩ : ↥(Kᶜ)) := by
    rw [connectedComponentIn_eq_image haK] at hb
    obtain ⟨y, hy, hyb⟩ := hb
    have hy_eq : y = ⟨b, hbK⟩ := Subtype.ext hyb
    rwa [hy_eq] at hy
  have hsub : connectedComponent (⟨a, haK⟩ : ↥(Kᶜ)) ⊆ G :=
    isPreconnected_connectedComponent.subset_isClopen ⟨hGclosed, hGopen⟩
      ⟨⟨b, hbK⟩, hab, hbmem⟩
  have hamem : (⟨a, haK⟩ : ↥(Kᶜ)) ∈ G := hsub mem_connectedComponent
  rw [hG] at hamem
  exact hamem ε hε

/-- **Pushing the poles of a finite combination of Cauchy kernels into `E`.**  If every connected
component of `Kᶜ` meets `E` and the points `ζ j` lie outside `K`, then the finite combination
`∑ j, c j / (ζ j - z)` is uniformly approximable on `K` by an expression
`∑ i, P i.eval ((z - e i)⁻¹)` whose poles `e i` all lie in `E`. -/
theorem exists_rational_approx_kernels {K : Set ℂ} (hK : IsCompact K) {E : Set ℂ}
    (hEmeet : ∀ x ∈ Kᶜ, (connectedComponentIn Kᶜ x ∩ E).Nonempty)
    {n : ℕ} (c ζ : Fin n → ℂ) (hζ : ∀ j, ζ j ∉ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ (e : Fin n → ℂ) (P : Fin n → Polynomial ℂ), (∀ i, e i ∈ E) ∧
      ∀ z ∈ K, ‖(∑ j, c j / (ζ j - z)) - ∑ i, (P i).eval ((z - e i)⁻¹)‖ < ε := by
  have hζK : ∀ j : Fin n, ζ j ∈ Kᶜ := fun j => by simpa using hζ j
  choose e he using fun j : Fin n => hEmeet (ζ j) (hζK j)
  obtain ⟨P, hP⟩ : ∃ P : Fin n → Polynomial ℂ, ∀ j : Fin n, ∀ z ∈ K,
      ‖(z - ζ j)⁻¹ - (P j).eval ((z - e j)⁻¹)‖ < ε / (2 * (n + 1) * (‖c j‖ + 1)) :=
    ⟨fun j => Classical.choose (exists_polynomial_approx_inv (K := K) hK (hζ j) (he j).1
      (by positivity : 0 < ε / (2 * (n + 1) * (‖c j‖ + 1)))),
     fun j => Classical.choose_spec (exists_polynomial_approx_inv (K := K) hK (hζ j) (he j).1
      (by positivity : 0 < ε / (2 * (n + 1) * (‖c j‖ + 1))))⟩
  refine ⟨e, fun j => Polynomial.C (-(c j)) * P j, fun j => (he j).2, fun z hz => ?_⟩
  have hQeval : ∀ j : Fin n, ∀ w : ℂ,
      (Polynomial.C (-(c j)) * P j).eval ((w - e j)⁻¹)
        = (-(c j)) * (P j).eval ((w - e j)⁻¹) := fun j w => by
    rw [Polynomial.eval_mul, Polynomial.eval_C]
  have hterm : ∀ j : Fin n,
      ‖(Polynomial.C (-(c j)) * P j).eval ((z - e j)⁻¹) - c j / (ζ j - z)‖
        ≤ ‖c j‖ * (ε / (2 * (n + 1) * (‖c j‖ + 1))) := by
    intro j
    have h1 := hP j z hz
    have h1' : ‖(P j).eval ((z - e j)⁻¹) - (z - ζ j)⁻¹‖
        < ε / (2 * (n + 1) * (‖c j‖ + 1)) := by
      rw [norm_sub_rev]; exact h1
    have hinv : (ζ j - z)⁻¹ = -((z - ζ j)⁻¹) := by
      rw [show ζ j - z = -(z - ζ j) by ring, inv_neg]
    have hident : (Polynomial.C (-(c j)) * P j).eval ((z - e j)⁻¹) - c j / (ζ j - z)
        = -(c j) * ((P j).eval ((z - e j)⁻¹) - (z - ζ j)⁻¹) := by
      rw [hQeval j z, div_eq_mul_inv, hinv]; ring
    rw [hident, norm_mul, norm_neg]
    exact mul_le_mul_of_nonneg_left (le_of_lt h1') (norm_nonneg _)
  have hbound : ∀ j : Fin n,
      ‖c j‖ * (ε / (2 * (n + 1) * (‖c j‖ + 1))) ≤ ε / (2 * (n + 1)) := by
    intro j
    have h3 : ‖c j‖ / (‖c j‖ + 1) ≤ 1 := by
      rw [div_le_one (by positivity : (0:ℝ) < ‖c j‖ + 1)]
      linarith [norm_nonneg (c j)]
    calc ‖c j‖ * (ε / (2 * (n + 1) * (‖c j‖ + 1)))
        = ε / (2 * (n + 1)) * (‖c j‖ / (‖c j‖ + 1)) := by field_simp
      _ ≤ ε / (2 * (n + 1)) * 1 := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = ε / (2 * (n + 1)) := by ring
  have hmain : ‖(∑ i : Fin n, (Polynomial.C (-(c i)) * P i).eval ((z - e i)⁻¹))
        - ∑ j : Fin n, c j / (ζ j - z)‖
      ≤ ∑ j : Fin n, ε / (2 * (n + 1)) := by
    rw [← Finset.sum_sub_distrib]
    exact le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun j _ => le_trans (hterm j) (hbound j)))
  have hsum : (∑ j : Fin n, ε / (2 * (n + 1))) ≤ ε / 2 := by
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    have h1 : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
    have h2 : (n : ℝ) * (ε / (2 * ((n : ℝ) + 1)))
        ≤ ((n : ℝ) + 1) * (ε / (2 * ((n : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : ((n : ℝ) + 1) * (ε / (2 * ((n : ℝ) + 1))) = ε / 2 := by field_simp
    linarith [h2, h3.le, h3.ge]
  rw [norm_sub_rev]
  exact lt_of_le_of_lt (le_trans hmain hsum) (by linarith)

/-- Evaluation of a polynomial in an analytic function is analytic. -/
theorem analyticAt_polynomial_comp {g : ℂ → ℂ} {x : ℂ} (hg : AnalyticAt ℂ g x)
    (P : Polynomial ℂ) : AnalyticAt ℂ (fun z => P.eval (g z)) x := by
  simp only [Polynomial.eval_eq_sum_range]
  exact Finset.analyticAt_fun_sum (Finset.range (P.natDegree + 1))
    (f := fun k (z : ℂ) => P.coeff k * (g z) ^ k)
    (fun k _ => analyticAt_const.mul (hg.pow k))

/-- **Runge's approximation theorem, reduced to the kernel-approximation input.**  Assume that
every function holomorphic on a neighbourhood of `K` is uniformly approximable on `K` by finite
combinations `∑ j, c j / (ζ j - z)` of Cauchy kernels with poles `ζ j ∉ K` (the input proved by
discretising Cauchy–Pompeiu, `RungeKernels.approximable_by_kernels`), and assume that every
connected component of `Kᶜ` meets `E ⊆ Ωᶜ`.  Then every `f` holomorphic on a neighbourhood of `K` is
uniformly approximable on `K` by functions holomorphic on `Ω` — namely by `∑ i, P i.eval ((· - e i)⁻¹)`
with `e i ∈ E`, obtained from the kernel approximation by pushing each pole `ζ j` to a point `e j` of
`E` in the same component of `Kᶜ` (`exists_rational_approx_kernels`, hence
`exists_polynomial_approx_inv`). -/
theorem runge_plane_of_kernels {Ω K V E : Set ℂ} (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) (hE : E ⊆ Ωᶜ)
    (hEmeet : ∀ x ∈ Kᶜ, (connectedComponentIn Kᶜ x ∩ E).Nonempty)
    (hker : ∀ {f : ℂ → ℂ}, (∀ x ∈ V, AnalyticAt ℂ f x) → ∀ ε : ℝ, 0 < ε →
      ∃ (n : ℕ) (c ζ : Fin n → ℂ), (∀ j, ζ j ∉ K) ∧
        ∀ z ∈ K, ‖f z - ∑ j, c j / (ζ j - z)‖ < ε)
    {f : ℂ → ℂ} (hf : ∀ x ∈ V, AnalyticAt ℂ f x) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : ℂ → ℂ, (∀ x ∈ Ω, AnalyticAt ℂ F x) ∧ ∀ x ∈ K, ‖F x - f x‖ < ε := by
  obtain ⟨n, c, ζ, hζ, happ⟩ := hker hf (ε / 2) (by linarith)
  obtain ⟨e, P, he, hP⟩ :=
    exists_rational_approx_kernels (K := K) hK hEmeet c ζ hζ (ε := ε / 2) (by linarith)
  refine ⟨fun z => ∑ i, (P i).eval ((z - e i)⁻¹), ?_, ?_⟩
  · intro x hx
    have hterm : ∀ i : Fin n, AnalyticAt ℂ (fun z : ℂ => (P i).eval ((z - e i)⁻¹)) x := by
      intro i
      have hxe : x ≠ e i := fun h => (hE (he i)) (h ▸ hx)
      have hsub : AnalyticAt ℂ (fun z : ℂ => z - e i) x :=
        (analyticAt_id : AnalyticAt ℂ (fun z : ℂ => z) x).sub
          (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => e i) x)
      exact analyticAt_polynomial_comp (hsub.inv (sub_ne_zero.mpr hxe)) (P i)
    exact Finset.analyticAt_fun_sum (Finset.univ : Finset (Fin n))
      (f := fun i (z : ℂ) => (P i).eval ((z - e i)⁻¹)) (fun i _ => hterm i)
  · intro x hx
    have h1 := happ x hx
    have h2 := hP x hx
    have hdecomp : (∑ i, (P i).eval ((x - e i)⁻¹)) - f x
        = ((∑ i, (P i).eval ((x - e i)⁻¹)) - ∑ j, c j / (ζ j - x))
          + ((∑ j, c j / (ζ j - x)) - f x) := by ring
    rw [hdecomp]
    have h1' : ‖(∑ j, c j / (ζ j - x)) - f x‖ < ε / 2 := by rw [norm_sub_rev]; exact h1
    have h2' : ‖(∑ i, (P i).eval ((x - e i)⁻¹)) - ∑ j, c j / (ζ j - x)‖ < ε / 2 := by
      rw [norm_sub_rev]; exact h2
    linarith [norm_add_le ((∑ i, (P i).eval ((x - e i)⁻¹)) - ∑ j, c j / (ζ j - x))
      ((∑ j, c j / (ζ j - x)) - f x), le_of_lt h1', le_of_lt h2']

end Work.Analysis.Complex.PolePush
