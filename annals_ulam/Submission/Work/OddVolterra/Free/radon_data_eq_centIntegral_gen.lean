import Mathlib
import Submission.Work.OddCurve.LowSlope.radon_data_eq_centIntegral_Ioo
import Submission.Work.OddCurve.LowSlope.radon_data_eq_centIntegral_weak

namespace Work.OddVolterra.Free

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval
open Work.OddCurve.LowSlope

/-! Port helpers. -/

/-- `x ^ n * √x = x ^ (n + 1/2)` for `x ≥ 0`. -/
private lemma pow_mul_sqrt_eq_rpow_gen {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    x ^ n * Real.sqrt x = x ^ ((n : ℝ) + 1 / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast x n]
  exact (Real.rpow_add' hx (by positivity)).symm

private lemma key_identity_cent_Ioo_gen (n : ℕ) (hn : 1 ≤ n) {f ρ : ℝ → ℝ} {a b s c ν : ℝ}
    (hs : 0 < s)
    (hc : c = (Real.sqrt (1 + s ^ 2))⁻¹)
    (hfC1 : ContDiffOn ℝ 1 f (Set.Ioo (-a) b))
    (hρC1 : ContDiffOn ℝ 1 ρ (Set.Ioo (-1 : ℝ) 1))
    (hρpos : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u)
    (hρ : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, ρ u * Real.sqrt (1 - u ^ 2) = f (ρ u * u))
    (hν : ν ∈ Set.Ioo (-1 : ℝ) 1)
    (ht1 : ρ (c * ν) * (c * ν) ∈ Set.Ioo (-a) b) :
    (1 - ν ^ 2) ^ (n - 1) * ((c * ν) * ρ (c * ν) ^ (2 * n + 1)) / Real.sqrt (1 - ν ^ 2)
      = (fun t : ℝ => t * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
            Real.sqrt (rad0 f s t)) (ρ (c * ν) * (c * ν))
        * (ρ (c * ν) + (c * ν) * deriv ρ (c * ν)) := by
  have hspos : 0 < Real.sqrt (1 + s ^ 2) := by
    apply Real.sqrt_pos.2
    have hs2 : (0 : ℝ) < s ^ 2 := pow_pos hs 2
    linarith
  have hcpos : 0 < c := by rw [hc]; positivity
  have hclt : c < 1 := by
    rw [hc]
    refine inv_lt_one_of_one_lt₀ ?_
    have hs2 : (0 : ℝ) < s ^ 2 := pow_pos hs 2
    have h : (1 : ℝ) < 1 + s ^ 2 := by linarith
    calc (1 : ℝ) = Real.sqrt 1 := by simp
      _ < Real.sqrt (1 + s ^ 2) := Real.sqrt_lt_sqrt (by norm_num) h
  have hcsq : c ^ 2 * (1 + s ^ 2) = 1 := by
    have h : c * c * (1 + s ^ 2) = 1 := by
      rw [hc]; field_simp; rw [Real.sq_sqrt (by positivity)]
    rwa [pow_two]
  have hcu : c * ν ∈ Set.Ioo (-1 : ℝ) 1 :=
    ⟨by nlinarith [hν.1, hcpos, hclt], by nlinarith [hν.2, hcpos, hclt]⟩
  have h1nu : 0 < 1 - ν ^ 2 := by nlinarith [hν.1, hν.2]
  have hrp : 0 < ρ (c * ν) := hρpos _ hcu
  have hρd : HasDerivAt ρ (deriv ρ (c * ν)) (c * ν) :=
    ((hρC1.differentiableOn (by norm_num)).differentiableAt
      (Filter.mem_of_superset (isOpen_Ioo.mem_nhds hcu) (fun u hu => hu))).hasDerivAt
  have hfd : HasDerivAt f (deriv f (ρ (c * ν) * (c * ν))) (ρ (c * ν) * (c * ν)) :=
    ((hfC1.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds ht1)).hasDerivAt
  have hrad := radial_identity hcu hrp hρd hfd hρ
  have hf_eq : f (ρ (c * ν) * (c * ν)) = ρ (c * ν) * Real.sqrt (1 - (c * ν) ^ 2) :=
    (hρ _ hcu).symm
  have h1mu : 0 < 1 - (c * ν) ^ 2 := by nlinarith [hcu.1, hcu.2]
  have hRu : (c * ν) ^ 2 * (1 + s ^ 2) = ν ^ 2 := by
    rw [mul_pow]
    linear_combination (ν ^ 2) * hcsq
  have hR : rad0 f s (ρ (c * ν) * (c * ν)) = (ρ (c * ν)) ^ 2 * (1 - ν ^ 2) := by
    rw [rad0, hf_eq]
    have h1 : (ρ (c * ν) * Real.sqrt (1 - (c * ν) ^ 2)) ^ 2
        = (ρ (c * ν)) ^ 2 * (1 - (c * ν) ^ 2) := by rw [mul_pow, Real.sq_sqrt h1mu.le]
    have h2 : (s * (ρ (c * ν) * (c * ν))) ^ 2 = s ^ 2 * (ρ (c * ν)) ^ 2 * (c * ν) ^ 2 := by
      ring
    rw [h1, h2]
    nlinarith [hRu]
  have hsqrtR : Real.sqrt (rad0 f s (ρ (c * ν) * (c * ν)))
      = ρ (c * ν) * Real.sqrt (1 - ν ^ 2) := by
    rw [hR, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hrp.le]
  have hwn : Real.sqrt (1 - ν ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 h1nu)
  have hrn : ρ (c * ν) ≠ 0 := ne_of_gt hrp
  beta_reduce
  rw [hsqrtR, hR]
  have hreord : (ρ (c * ν) * (c * ν)) * f (ρ (c * ν) * (c * ν))
        * (f (ρ (c * ν) * (c * ν)) - (ρ (c * ν) * (c * ν)) * deriv f (ρ (c * ν) * (c * ν)))
        * ((ρ (c * ν)) ^ 2 * (1 - ν ^ 2)) ^ (n - 1)
        / (ρ (c * ν) * Real.sqrt (1 - ν ^ 2))
        * (ρ (c * ν) + (c * ν) * deriv ρ (c * ν))
      = (ρ (c * ν) * (c * ν))
          * (f (ρ (c * ν) * (c * ν))
            * (f (ρ (c * ν) * (c * ν)) - (ρ (c * ν) * (c * ν)) * deriv f (ρ (c * ν) * (c * ν)))
            * (ρ (c * ν) + (c * ν) * deriv ρ (c * ν)))
          * ((ρ (c * ν)) ^ 2 * (1 - ν ^ 2)) ^ (n - 1)
          / (ρ (c * ν) * Real.sqrt (1 - ν ^ 2)) := by ring
  rw [hreord, hrad, mul_pow ((ρ (c * ν)) ^ 2) (1 - ν ^ 2) (n - 1), ← pow_mul]
  have hpow4 : (ρ (c * ν)) * (ρ (c * ν)) ^ 3 * (ρ (c * ν)) ^ (2 * (n - 1))
      = (ρ (c * ν)) ^ (2 * n + 2) := by
    rw [show 2 * n + 2 = 1 + 3 + 2 * (n - 1) by omega, pow_add, pow_add]
    ring
  have hpow5 : (ρ (c * ν)) ^ (2 * n + 1) * ρ (c * ν) = (ρ (c * ν)) ^ (2 * n + 2) := by
    rw [← pow_succ (ρ (c * ν)) (2 * n + 1), show (2 * n + 1) + 1 = 2 * n + 2 by omega]
  rw [div_eq_div_iff hwn (mul_ne_zero hrn hwn)]
  have hL : ((1 - ν ^ 2) ^ (n - 1) * ((c * ν) * ρ (c * ν) ^ (2 * n + 1)))
        * (ρ (c * ν) * Real.sqrt (1 - ν ^ 2))
      = (c * ν) * ((ρ (c * ν)) ^ (2 * n + 1) * ρ (c * ν))
        * ((1 - ν ^ 2) ^ (n - 1) * Real.sqrt (1 - ν ^ 2)) := by ring
  have hR' : ((ρ (c * ν) * (c * ν)) * (ρ (c * ν)) ^ 3
        * ((ρ (c * ν)) ^ (2 * (n - 1)) * (1 - ν ^ 2) ^ (n - 1)))
        * Real.sqrt (1 - ν ^ 2)
      = (c * ν) * ((ρ (c * ν)) * (ρ (c * ν)) ^ 3 * (ρ (c * ν)) ^ (2 * (n - 1)))
        * ((1 - ν ^ 2) ^ (n - 1) * Real.sqrt (1 - ν ^ 2)) := by ring
  rw [hL, hR', hpow5, hpow4]


/-- **The centroid integration-by-parts identity** on a general interval. -/
private theorem cent_ibp_Ioo_gen (n : ℕ) (hn : 1 ≤ n) {f : ℝ → ℝ} {x y s a b : ℝ}
    (hs : 0 < s)
    (hf : ContDiffOn ℝ 1 f (Set.Ioo (-a) b))
    (hx : -(x) ∈ Set.Ioo (-a) b) (hy : y ∈ Set.Ioo (-a) b) (hxy : -(x) < y)
    (hfy : f y = s * y) (hfx : f (-(x)) = -(s * (-(x))))
    (hpos : ∀ t ∈ Set.Ioo (-(x)) y, 0 < rad0 f s t)
    (hintA : IntervalIntegrable (fun t : ℝ => t * f t * (f t - t * deriv f t) *
      rad0 f s t ^ (n - 1) / Real.sqrt (rad0 f s t)) volume (-(x)) y)
    (hintB : IntervalIntegrable (fun t : ℝ => t * rad0 f s t ^ (n - 1) *
      Real.sqrt (rad0 f s t)) volume (-(x)) y) :
    (2 * (n : ℝ) - 1) * (∫ t in (-(x))..y, t * f t * (f t - t * deriv f t) *
        rad0 f s t ^ (n - 1) / Real.sqrt (rad0 f s t))
      = (2 * (n : ℝ) + 1) * (∫ t in (-(x))..y, t * rad0 f s t ^ (n - 1) *
        Real.sqrt (rad0 f s t)) := by
  have hfcont : ContinuousOn f (Set.Ioo (-a) b) := hf.continuousOn
  have hx0 : -a < -(x) := hx.1
  have hy1 : y < b := hy.2
  set R : ℝ → ℝ := fun t => rad0 f s t with hR
  have hRy : R y = 0 := by simp only [hR, rad0, hfy]; ring
  have hRx : R (-(x)) = 0 := by simp only [hR, rad0]; rw [hfx]; ring
  have hfd : ∀ t ∈ Set.Ioo (-(x)) y, HasDerivAt f (deriv f t) t := by
    intro t ht
    have ht1 : t ∈ Set.Ioo (-a) b := ⟨lt_trans hx0 ht.1, lt_trans ht.2 hy1⟩
    exact ((hf.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds ht1)).hasDerivAt
  have hRd : ∀ t ∈ Set.Ioo (-(x)) y, HasDerivAt R (2 * f t * deriv f t - 2 * s ^ 2 * t) t := by
    intro t ht
    have h21 : (2 : ℕ) - 1 = 1 := by norm_num
    have h1 : HasDerivAt (fun u : ℝ => f u ^ 2) (2 * f t * deriv f t) t := by
      have hh := (hfd t ht).pow 2
      refine hh.congr_deriv ?_
      rw [h21, pow_one]; ring
    have h2 : HasDerivAt (fun u : ℝ => (s * u) ^ 2) (2 * s ^ 2 * t) t := by
      have hbase : HasDerivAt (fun u : ℝ => s * u) s t := by
        simpa using (hasDerivAt_id t).const_mul s
      have hh : HasDerivAt (fun u : ℝ => (s * u) * (s * u)) (s * (s * t) + (s * t) * s) t :=
        hbase.mul hbase
      have hh2 : HasDerivAt (fun u : ℝ => (s * u) ^ 2) (s * (s * t) + (s * t) * s) t :=
        hh.congr_of_eventuallyEq (Eventually.of_forall (fun u => pow_two (s * u)))
      refine hh2.congr_deriv ?_
      ring
    have h3 : HasDerivAt (fun u : ℝ => f u ^ 2 - (s * u) ^ 2)
        (2 * f t * deriv f t - 2 * s ^ 2 * t) t := h1.sub h2
    have hfun : R = fun u : ℝ => f u ^ 2 - (s * u) ^ 2 := by
      funext u; simp only [hR, rad0]
    rw [hfun]
    exact h3
  have hAeq : (fun t : ℝ => t * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
      Real.sqrt (rad0 f s t))
      = (fun t : ℝ => t * f t * (f t - t * deriv f t) * R t ^ (n - 1) / Real.sqrt (R t)) := by
    funext t; simp only [hR]
  have hBeq : (fun t : ℝ => t * rad0 f s t ^ (n - 1) * Real.sqrt (rad0 f s t))
      = (fun t : ℝ => t * R t ^ (n - 1) * Real.sqrt (R t)) := by
    funext t; simp only [hR]
  rw [hAeq, hBeq]
  have hintA' : IntervalIntegrable (fun t : ℝ => t * f t * (f t - t * deriv f t) *
      R t ^ (n - 1) / Real.sqrt (R t)) volume (-(x)) y := by
    rw [← hAeq]; exact hintA
  have hintB' : IntervalIntegrable (fun t : ℝ => t * R t ^ (n - 1) * Real.sqrt (R t))
      volume (-(x)) y := by
    rw [← hBeq]; exact hintB
  have hp : (((n - 1 : ℕ) : ℝ) + 1 / 2) = (2 * (n : ℝ) - 1) / 2 := by
    rw [Nat.cast_sub hn]; push_cast; ring
  set F : ℝ → ℝ := fun t => t ^ 2 * (R t ^ (n - 1) * Real.sqrt (R t)) with hF
  have hpoint : ∀ t ∈ Set.Ioo (-(x)) y,
      HasDerivAt F ((2 * (n : ℝ) + 1) * (t * R t ^ (n - 1) * Real.sqrt (R t)) -
        (2 * (n : ℝ) - 1) * (t * f t * (f t - t * deriv f t) * R t ^ (n - 1) /
          Real.sqrt (R t))) t := by
    intro t ht
    have hr : 0 < R t := hpos t ht
    have hrne : R t ≠ 0 := ne_of_gt hr
    have hin : HasDerivAt (fun u : ℝ => R u ^ (((n - 1 : ℕ) : ℝ) + 1 / 2))
        ((((n - 1 : ℕ) : ℝ) + 1 / 2) * R t ^ ((((n - 1 : ℕ) : ℝ) + 1 / 2) - 1) *
          (2 * f t * deriv f t - 2 * s ^ 2 * t)) t :=
      (Real.hasDerivAt_rpow_const (Or.inl hrne)).comp t (hRd t ht)
    have hRcontAt : ContinuousAt R t := by
      have h1 : ContinuousAt (fun u : ℝ => f u ^ 2 - (s * u) ^ 2) t :=
        (((hfcont.continuousAt (isOpen_Ioo.mem_nhds
            ⟨lt_trans hx0 ht.1, lt_trans ht.2 hy1⟩)).pow 2).sub
          (((continuous_const.mul continuous_id).continuousAt).pow 2))
      refine h1.congr ?_
      filter_upwards with u
      simp only [hR, rad0]
    have hnear : ∀ᶠ u in 𝓝 t, 0 < R u := hRcontAt.eventually (isOpen_Ioi.mem_nhds hr)
    have hsmooth : HasDerivAt (fun u : ℝ => R u ^ (n - 1) * Real.sqrt (R u))
        ((((n - 1 : ℕ) : ℝ) + 1 / 2) * R t ^ ((((n - 1 : ℕ) : ℝ) + 1 / 2) - 1) *
          (2 * f t * deriv f t - 2 * s ^ 2 * t)) t := by
      refine hin.congr_of_eventuallyEq ?_
      filter_upwards [hnear] with u hu
      exact pow_mul_sqrt_eq_rpow_gen hu.le (n - 1)
    have hFd := (((hasDerivAt_id t).pow 2)).mul hsmooth
    have hFun : F = fun u : ℝ => u ^ 2 * (R u ^ (n - 1) * Real.sqrt (R u)) := by
      funext u; simp only [hF]
    rw [hFun]
    refine hFd.congr_deriv ?_
    have hpow : R t ^ (n - 1) * Real.sqrt (R t) = R t ^ ((2 * (n : ℝ) - 1) / 2) :=
      (pow_mul_sqrt_eq_rpow_gen hr.le (n - 1)).trans (by rw [show ((n - 1 : ℕ) : ℝ) + 1 / 2
        = (2 * (n : ℝ) - 1) / 2 by rw [Nat.cast_sub hn]; push_cast; ring])
    have hpow' : R t ^ (n - 1) / Real.sqrt (R t) = R t ^ ((2 * (n : ℝ) - 1) / 2 - 1) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (R t) (n - 1), ← Real.rpow_sub hr]
      congr 1
      rw [Nat.cast_sub hn]; push_cast; ring
    have hRM : R t * R t ^ ((2 * (n : ℝ) - 1) / 2 - 1) = R t ^ ((2 * (n : ℝ) - 1) / 2) := by
      have h := Real.rpow_add hr (1 : ℝ) ((2 * (n : ℝ) - 1) / 2 - 1)
      rw [Real.rpow_one] at h
      rw [← h]
      congr 1
      ring
    have hkey2 : t * f t * (f t - t * deriv f t)
        = t * (R t - t / 2 * (2 * f t * deriv f t - 2 * s ^ 2 * t)) := by
      simp only [hR, rad0]; ring
    have hB' : t * R t ^ (n - 1) * Real.sqrt (R t) = t * R t ^ ((2 * (n : ℝ) - 1) / 2) := by
      rw [mul_assoc, hpow]
    have hA' : t * f t * (f t - t * deriv f t) * R t ^ (n - 1) / Real.sqrt (R t)
        = t * f t * (f t - t * deriv f t) * R t ^ ((2 * (n : ℝ) - 1) / 2 - 1) := by
      rw [mul_div_assoc, hpow']
    have htarget : (2 * (n : ℝ) + 1) * (t * R t ^ (n - 1) * Real.sqrt (R t)) -
          (2 * (n : ℝ) - 1) * (t * f t * (f t - t * deriv f t) * R t ^ (n - 1) /
            Real.sqrt (R t))
        = 2 * t * R t ^ ((2 * (n : ℝ) - 1) / 2) +
          t ^ 2 * (((2 * (n : ℝ) - 1) / 2) * R t ^ ((2 * (n : ℝ) - 1) / 2 - 1) *
            (2 * f t * deriv f t - 2 * s ^ 2 * t)) := by
      rw [hB', hA', hkey2]
      rw [show t * (R t - t / 2 * (2 * f t * deriv f t - 2 * s ^ 2 * t)) *
            R t ^ ((2 * (n : ℝ) - 1) / 2 - 1)
          = t * (R t * R t ^ ((2 * (n : ℝ) - 1) / 2 - 1))
            - t * (t / 2 * (2 * f t * deriv f t - 2 * s ^ 2 * t)) *
                R t ^ ((2 * (n : ℝ) - 1) / 2 - 1) by ring]
      rw [hRM]
      ring
    have hLHS : (2 * t ^ (2 - 1) * 1) * (R t ^ (n - 1) * Real.sqrt (R t)) +
          t ^ 2 * ((((n - 1 : ℕ) : ℝ) + 1 / 2) * R t ^ ((((n - 1 : ℕ) : ℝ) + 1 / 2) - 1) *
            (2 * f t * deriv f t - 2 * s ^ 2 * t))
        = 2 * t * R t ^ ((2 * (n : ℝ) - 1) / 2) +
          t ^ 2 * (((2 * (n : ℝ) - 1) / 2) * R t ^ ((2 * (n : ℝ) - 1) / 2 - 1) *
            (2 * f t * deriv f t - 2 * s ^ 2 * t)) := by
      rw [hp, hpow]
      ring
    simp only [id_eq, Pi.pow_apply, Nat.cast_ofNat]
    rw [hLHS, ← htarget]
  have hRcontOn : ContinuousOn R (Set.Icc (-(x)) y) := by
    have h1 : ContinuousOn (fun u : ℝ => f u ^ 2 - (s * u) ^ 2) (Set.Icc (-(x)) y) :=
      ((hfcont.mono (by
          intro u hu
          exact ⟨lt_of_lt_of_le hx0 hu.1, lt_of_le_of_lt hu.2 hy1⟩)).pow 2).sub
        (((continuous_const.mul continuous_id).continuousOn).pow 2)
    exact h1.congr (fun u _ => by simp only [hR, rad0])
  have hcontF : ContinuousOn F (Set.Icc (-(x)) y) := by
    have hfun : F = fun t : ℝ => t ^ 2 * (R t ^ (n - 1) * Real.sqrt (R t)) := by
      funext t; simp only [hF]
    rw [hfun]
    exact ((continuous_id.pow 2).continuousOn).mul
      (((continuous_id.pow (n - 1)).mul Real.continuous_sqrt).comp_continuousOn hRcontOn)
  have hintD : IntervalIntegrable (fun t : ℝ =>
      (2 * (n : ℝ) + 1) * (t * R t ^ (n - 1) * Real.sqrt (R t)) -
        (2 * (n : ℝ) - 1) * (t * f t * (f t - t * deriv f t) * R t ^ (n - 1) /
          Real.sqrt (R t))) volume (-(x)) y :=
    (hintB'.const_mul (2 * (n : ℝ) + 1)).sub (hintA'.const_mul (2 * (n : ℝ) - 1))
  have hFTC : (∫ t in (-(x))..y,
      ((2 * (n : ℝ) + 1) * (t * R t ^ (n - 1) * Real.sqrt (R t)) -
        (2 * (n : ℝ) - 1) * (t * f t * (f t - t * deriv f t) * R t ^ (n - 1) /
          Real.sqrt (R t)))) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (le_of_lt hxy) hcontF
      (fun t ht => hpoint t ht) hintD]
    have hFy : F y = 0 := by simp only [hF, hRy, Real.sqrt_zero, mul_zero]
    have hFx : F (-(x)) = 0 := by simp only [hF, hRx, Real.sqrt_zero, mul_zero]
    rw [hFy, hFx, sub_zero]
  have hsplit : (∫ t in (-(x))..y,
      ((2 * (n : ℝ) + 1) * (t * R t ^ (n - 1) * Real.sqrt (R t)) -
        (2 * (n : ℝ) - 1) * (t * f t * (f t - t * deriv f t) * R t ^ (n - 1) /
          Real.sqrt (R t))))
      = (2 * (n : ℝ) + 1) * (∫ t in (-(x))..y, t * R t ^ (n - 1) * Real.sqrt (R t))
        - (2 * (n : ℝ) - 1) * (∫ t in (-(x))..y, t * f t * (f t - t * deriv f t) *
            R t ^ (n - 1) / Real.sqrt (R t)) := by
    rw [intervalIntegral.integral_sub (hintB'.const_mul (2 * (n : ℝ) + 1))
        (hintA'.const_mul (2 * (n : ℝ) - 1)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [hsplit] at hFTC
  linarith [hFTC]



/-- Free-tip / general-interval port of `Work.OddCurve.LowSlope.radon_data_eq_centIntegral_Ioo`
(`Submission/Work/OddCurve/LowSlope/radon_data_eq_centIntegral_Ioo.lean`, proved).

Same identity, with the domain of `f` generalised from `Ioo (-1) 1` to `Ioo (-a) b` (the profile
`f` is a parameter and the source only uses it on the chord `(-(x s), y s)`, which now need not
lie in `(-1,1)`).  The two root-uniqueness hypotheses of the source are unused (grep: they occur
only in the signature) and are dropped here.  The port is: copy the private helper
`key_identity_cent_Ioo` and the body of `radon_data_eq_centIntegral_Ioo`, plus the helper
`Work.OddCurve.LowSlope.cent_ibp_Ioo` from
`Submission/Work/OddCurve/LowSlope/radon_data_eq_centIntegral_weak.lean`, generalising each the
same way (`hf : ContDiffOn ℝ 1 f (Set.Ioo (-1) 1)` becomes `(Set.Ioo (-a) b)`, `hx`/`hy` become
the general memberships `hmx`/`hy`); the placement of the chord point inside the domain of `f`
then uses `hmx`/`hy` instead of `hx.1`/`hy.2`. -/
theorem radon_data_eq_centIntegral_gen (n : ℕ) (hn : 1 ≤ n) {f ρ x y : ℝ → ℝ} {a b s : ℝ}
    (hs : 0 < s)
    (hfC1 : ContDiffOn ℝ 1 f (Set.Ioo (-a) b))
    (hρpos : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u)
    (hρC1 : ContDiffOn ℝ 1 ρ (Set.Ioo (-1 : ℝ) 1))
    (hρmono : StrictMonoOn (fun u : ℝ => ρ u * u) (Set.Ioo (-1 : ℝ) 1))
    (hρ : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, ρ u * Real.sqrt (1 - u ^ 2) = f (ρ u * u))
    (hderivn : ∀ u ∈ Set.Ioo (-(Real.sqrt (1 + s ^ 2))⁻¹) (Real.sqrt (1 + s ^ 2))⁻¹,
      0 ≤ ρ u + u * deriv ρ u)
    (hend_y : ρ ((Real.sqrt (1 + s ^ 2))⁻¹) * ((Real.sqrt (1 + s ^ 2))⁻¹) = y s)
    (hend_x : ρ (-((Real.sqrt (1 + s ^ 2))⁻¹)) * (-((Real.sqrt (1 + s ^ 2))⁻¹)) = -(x s))
    (hmem : ∀ ν ∈ Set.Ioo (-1 : ℝ) 1,
      ρ ((Real.sqrt (1 + s ^ 2))⁻¹ * ν) * ((Real.sqrt (1 + s ^ 2))⁻¹ * ν) ∈ Set.Ioo (-(x s)) (y s))
    (hmx : -(x s) ∈ Set.Ioo (-a) b) (hy : y s ∈ Set.Ioo (-a) b)
    (hfy : f (y s) = s * y s) (hfx : f (-(x s)) = s * x s)
    (hxy : -(x s) < y s)
    (hrad : ∀ t ∈ Set.Ioo (-(x s)) (y s), 0 < Work.OddCurve.LowSlope.rad0 f s t)
    (hintA : IntervalIntegrable (fun t : ℝ => t * f t * (f t - t * deriv f t) *
      Work.OddCurve.LowSlope.rad0 f s t ^ (n - 1) / Real.sqrt (Work.OddCurve.LowSlope.rad0 f s t))
      volume (-(x s)) (y s))
    (hintB : IntervalIntegrable (fun t : ℝ => t * Work.OddCurve.LowSlope.rad0 f s t ^ (n - 1) *
      Real.sqrt (Work.OddCurve.LowSlope.rad0 f s t)) volume (-(x s)) (y s)) :
    Work.OddRadon.radonProfile (2 * n + 1) (fun u : ℝ => u * ρ u ^ (2 * n + 1))
        ((Real.sqrt (1 + s ^ 2))⁻¹) =
      (2 * (n : ℝ) + 1) * Work.OddCurve.LowSlope.ballVol (2 * n - 1) * Real.sqrt (1 + s ^ 2) *
        Work.OddCurve.LowSlope.centIntegral n f x y s := by
  have hcpos : 0 < (Real.sqrt (1 + s ^ 2))⁻¹ := by positivity
  rw [radonProfile_eq_natpow n hn (fun u : ℝ => u * ρ u ^ (2 * n + 1)) hcpos]
  set c : ℝ := (Real.sqrt (1 + s ^ 2))⁻¹ with hc
  have hspos : 0 < Real.sqrt (1 + s ^ 2) := by
    apply Real.sqrt_pos.2
    have hs2 : (0 : ℝ) < s ^ 2 := pow_pos hs 2
    linarith
  have hsc : c * Real.sqrt (1 + s ^ 2) = 1 := by
    rw [hc, inv_mul_cancel₀ (ne_of_gt hspos)]
  have h1c : (1 : ℝ) / c = Real.sqrt (1 + s ^ 2) := by
    rw [one_div]; exact inv_eq_of_mul_eq_one_right hsc
  have hpt : ∀ ν ∈ Set.Ioo (-1 : ℝ) 1,
      (1 - ν ^ 2) ^ (n - 1) * ((c * ν) * ρ (c * ν) ^ (2 * n + 1)) / Real.sqrt (1 - ν ^ 2)
        = (fun t : ℝ => t * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
              Real.sqrt (rad0 f s t)) (ρ (c * ν) * (c * ν))
          * (ρ (c * ν) + (c * ν) * deriv ρ (c * ν)) := by
    intro ν hν
    refine key_identity_cent_Ioo_gen n hn hs hc hfC1 hρC1 hρpos hρ hν ?_
    have hmem' := hmem ν hν
    exact ⟨lt_trans hmx.1 hmem'.1, lt_trans hmem'.2 hy.2⟩
  have hInt1 : (∫ ν in (-1 : ℝ)..1,
        (1 - ν ^ 2) ^ (n - 1) * ((c * ν) * ρ (c * ν) ^ (2 * n + 1)) / Real.sqrt (1 - ν ^ 2))
      = ∫ ν in (-1 : ℝ)..1,
          (fun t : ℝ => t * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
              Real.sqrt (rad0 f s t)) (ρ (c * ν) * (c * ν))
            * (ρ (c * ν) + (c * ν) * deriv ρ (c * ν)) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne (volume : Measure ℝ) (1 : ℝ)] with ν hνne hν
    rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hν
    exact hpt ν ⟨hν.1, lt_of_le_of_ne hν.2 hνne⟩
  have hInt2 : (∫ ν in (-1 : ℝ)..1,
          (fun t : ℝ => t * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
              Real.sqrt (rad0 f s t)) (ρ (c * ν) * (c * ν))
            * (ρ (c * ν) + (c * ν) * deriv ρ (c * ν)))
      = (1 / c) * ∫ ν in (-1 : ℝ)..1,
          (fun t : ℝ => t * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
              Real.sqrt (rad0 f s t)) (ρ (c * ν) * (c * ν))
            * (c * (ρ (c * ν) + (c * ν) * deriv ρ (c * ν))) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro ν _
    have hcne : c ≠ 0 := by rw [hc]; exact inv_ne_zero (ne_of_gt hspos)
    field_simp
  have hchange := radon_change_of_variables_gen
    (fun t : ℝ => t * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) / Real.sqrt (rad0 f s t))
    hs hρC1 hderivn hend_y hend_x
  have hfxe : f (-(x s)) = -(s * (-(x s))) := by rw [hfx]; ring
  have hibp := cent_ibp_Ioo_gen n hn hs hfC1 hmx hy hxy hfy hfxe hrad hintA hintB
  have hmain : (∫ ν in (-1 : ℝ)..1,
        (1 - ν ^ 2) ^ (n - 1) * ((c * ν) * ρ (c * ν) ^ (2 * n + 1)) / Real.sqrt (1 - ν ^ 2))
      = Real.sqrt (1 + s ^ 2) *
        (∫ t in (-(x s))..(y s), t * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
          Real.sqrt (rad0 f s t)) := by
    rw [hInt1, hInt2, h1c, hchange]
  rw [hmain]
  have hsphere := sphereArea_eq_ballVol (2 * n - 2)
  have hcast : (((2 * n - 2 : ℕ) : ℝ) + 1) = 2 * (n : ℝ) - 1 := by
    have h2 : 2 * n - 2 = 2 * (n - 1) := by omega
    rw [h2, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hn]
    ring
  have hbcast : 2 * n - 2 + 1 = 2 * n - 1 := by omega
  rw [hsphere, hbcast, hcast]
  have hBne : (2 * (n : ℝ) - 1) ≠ 0 := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  have hkey : (∫ t in (-(x s))..(y s), t * f t * (f t - t * deriv f t)
        * rad0 f s t ^ (n - 1) / Real.sqrt (rad0 f s t))
      = (2 * (n : ℝ) + 1) / (2 * (n : ℝ) - 1) * centIntegral n f x y s := by
    have hJ : centIntegral n f x y s
        = ∫ t in (-(x s))..(y s), t * rad0 f s t ^ (n - 1) * Real.sqrt (rad0 f s t) := rfl
    rw [hJ, div_mul_eq_mul_div, eq_div_iff hBne]
    linarith [hibp]
  rw [hkey]
  field_simp


end

end Work.OddVolterra.Free
