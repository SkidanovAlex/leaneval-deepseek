import Mathlib
import Submission.SameGrad
import Submission.ShapeDeriv
import Submission.Filtration

open Module Real MeasureTheory Matrix Filter
open scoped Real BigOperators Pointwise Topology
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-!
# Isotropy of the Voronoi cell from a local minimum over the determinant-one locus

Paper §4.3 / Theorem 6.3 (`minima_have_mass`), first half: if the determinant-one locus of
positions of `ℒ` has a local minimum of `γ_{1/t}(V(·))` at the identity, then the Gaussian
second-moment matrix of the scaled Voronoi cell `(1/s)·V(ℒ)` is a scalar multiple of the
identity — i.e. `V(ℒ)` is in *isotropic Gaussian position* at parameter `s`.

Main results:

* `Submission.Isotropic.normCurve` — the determinant-normalized curve
  `t ↦ (det (1 + t•M))^{-1/m} • (1 + t•M)` through the identity, which is a determinant-one
  matrix for every small `t` and whose tangent at `0` is the trace-free part of `M`.
* `normCurve_shapeG_hasDerivAt` — the derivative of the cell-side functional
  `A ↦ γ₁(V(A·ℒ))` (= `shapeG` on determinant-one matrices) along this curve at `0` is the
  S3 matrix pairing `−2π·Σᵢⱼ Mᵢⱼ ·(secondMoment (V(ℒ)))ᵢⱼ`
  (paper `same_grad_VL` combined with `∇g(I) = ∇h(I)`).
* `secondMoment_scalar_of_local_min` — the isotropy conclusion at parameter `1`.
* `secondMoment_scalar_of_local_min_scaled` — the same at an arbitrary parameter `s > 0`
  (via `V(c·ℒ) = c·V(ℒ)` and `γ_s(V(ℒ)) = γ₁(V((1/s)·ℒ))`).
-/

namespace Submission.Isotropic


variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "Mx" => Matrix (Fin m) (Fin m) ℝ

noncomputable def normCurve (M : Mx) (t : ℝ) : Mx :=
  ((1 + t • M).det) ^ (-(1 / (m : ℝ))) • (1 + t • M)

lemma normCurve_apply (M : Mx) (t : ℝ) (j i : Fin m) :
    normCurve M t j i = ((1 + t • M).det) ^ (-(1 / (m : ℝ))) * (1 + t • M) j i := rfl

lemma mvec_smul' (c : ℝ) (A : Mx) : Submission.ShapeDeriv.mvec (c • A) =
    c • Submission.ShapeDeriv.mvec A := by
  simp [Submission.ShapeDeriv.mvec]

lemma normCurve_zero' (M : Mx) : normCurve M 0 = 1 := by
  simp [normCurve]

lemma normCurve_det (M : Mx) (hm : m ≠ 0) (t : ℝ) (hd : 0 < (1 + t • M).det) :
    (normCurve M t).det = 1 := by
  rw [normCurve, Matrix.det_smul, Fintype.card_fin]
  set d : ℝ := (1 + t • M).det with hddef
  have hpow : (d ^ (-(1 / (m : ℝ)))) ^ m = d⁻¹ := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (le_of_lt hd)]
    have hmul : -(1 / (m : ℝ)) * (m : ℝ) = -1 := by field_simp
    rw [hmul, Real.rpow_neg (le_of_lt hd), Real.rpow_one]
  rw [hpow, inv_mul_cancel₀ (ne_of_gt hd)]

/-- The determinant expansion with a continuous quadratic remainder. -/
lemma det_one_add_smul_expansion (M : Mx) :
    ∃ q : ℝ → ℝ, Continuous q ∧ ∀ t : ℝ,
      (1 + t • M).det = 1 + M.trace * t + q t * t ^ 2 := by
  let P : Polynomial ℝ :=
    ((1 : Matrix (Fin m) (Fin m) (Polynomial ℝ)) +
      (Polynomial.X : Polynomial ℝ) • M.map (Polynomial.C : ℝ →+* Polynomial ℝ)).det
  refine ⟨fun t => Polynomial.eval t (P.divX.divX), ?_, ?_⟩
  · exact Polynomial.continuous _
  · intro t
    show (1 + t • M).det = 1 + M.trace * t + Polynomial.eval t (P.divX.divX) * t ^ 2
    rw [Matrix.det_one_add_smul]

/-- Continuity of `t ↦ (1 + t•M).det`. -/
lemma det_one_add_smul_continuous (M : Mx) : Continuous (fun t : ℝ => (1 + t • M).det) := by
  rcases det_one_add_smul_expansion M with ⟨q, hq, hqe⟩
  have hfun : (fun t : ℝ => (1 + t • M).det) = fun t : ℝ => 1 + M.trace * t + q t * t ^ 2 :=
    funext hqe
  rw [hfun]
  have h1 : Continuous (fun t : ℝ => M.trace * t) := continuous_const.mul continuous_id
  have h2 : Continuous (fun t : ℝ => q t * t ^ 2) := hq.mul (continuous_id.pow 2)
  fun_prop

/-- Second-order bound on `det (1 + t•M)` for a trace-free `M`. -/
lemma det_one_add_trace_zero_bound (M : Mx) (hM : M.trace = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |t| ≤ δ → |(1 + t • M).det - 1| ≤ C * t ^ 2 := by
  rcases det_one_add_smul_expansion M with ⟨q, hq, hqe⟩
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hq.continuousAt (1:ℝ) (by norm_num)
  refine ⟨δ / 2, by positivity, |q 0| + 1, by positivity, ?_⟩
  intro t ht
  have htδ : dist t 0 < δ := by rw [Real.dist_eq, sub_zero]; linarith [abs_nonneg t]
  have hqt : dist (q t) (q 0) < 1 := hδ htδ
  rw [Real.dist_eq] at hqt
  have hb : |q t| ≤ |q 0| + 1 := by
    have h1 : |q t| - |q 0| ≤ |q t - q 0| := abs_sub_abs_le_abs_sub _ _
    linarith
  rw [hqe t, hM]
  have hval : 1 + 0 * t + q t * t ^ 2 - 1 = q t * t ^ 2 := by ring
  rw [hval, abs_mul, abs_of_nonneg (sq_nonneg t)]
  exact mul_le_mul_of_nonneg_right hb (sq_nonneg t)

lemma rpow_neg_inv_sub_one_le {m : ℕ} (hm : m ≠ 0) {d : ℝ}
    (hd1 : 1 / 2 ≤ d) (hd2 : d ≤ 3 / 2) :
    |d ^ (-(1 / (m : ℝ))) - 1| ≤ 2 * |d - 1| := by
  have hmR : (0:ℝ) < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hz0 : (0:ℝ) ≤ 1 / (m : ℝ) := by positivity
  have hdle1 : 1 / (m : ℝ) ≤ 1 := by
    rw [div_le_one hmR]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
  have hdpos : 0 < d := by linarith
  have hprod : d ^ (-(1 / (m : ℝ))) * d ^ (1 / (m : ℝ)) = 1 := by
    rw [← Real.rpow_add hdpos]
    have : -(1 / (m : ℝ)) + 1 / (m : ℝ) = 0 := by ring
    rw [this, Real.rpow_zero]
  have hnorm2 : d ^ (-(1 / (m : ℝ))) ≤ 2 := by
    have h1 : d ^ (-(1 / (m : ℝ))) = (d⁻¹) ^ (1 / (m : ℝ)) := by
      rw [Real.rpow_neg (le_of_lt hdpos)]
      exact (Real.inv_rpow (le_of_lt hdpos) (1 / (m : ℝ))).symm
    rw [h1]
    have hinv : d⁻¹ ≤ 2 := by
      have h := (inv_le_inv₀ hdpos (by norm_num : (0:ℝ) < 1/2)).mpr hd1
      norm_num at h
      exact h
    calc (d⁻¹) ^ (1 / (m : ℝ)) ≤ (2:ℝ) ^ (1 / (m : ℝ)) :=
          Real.rpow_le_rpow (by positivity) hinv hz0
      _ ≤ 2 := by
          have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hdle1
          simpa using this
  have hdiff : |d ^ (1 / (m : ℝ)) - 1| ≤ |d - 1| := by
    rcases lt_or_ge (1:ℝ) d with hgt | hle
    · have hge : 1 ≤ d := le_of_lt hgt
      have hle1 : 1 ≤ d ^ (1 / (m : ℝ)) := Real.one_le_rpow hge hz0
      have hle2 : d ^ (1 / (m : ℝ)) ≤ d := by
        have := Real.rpow_le_rpow_of_exponent_le hge hdle1
        rwa [Real.rpow_one] at this
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ d ^ (1/(m:ℝ)) - 1),
        abs_of_nonneg (by linarith : (0:ℝ) ≤ d - 1)]
      linarith
    · have hle1 : d ^ (1 / (m : ℝ)) ≤ 1 := Real.rpow_le_one (le_of_lt hdpos) hle hz0
      have hle2 : d ≤ d ^ (1 / (m : ℝ)) := by
        have := Real.rpow_le_rpow_of_exponent_ge hdpos hle hdle1
        rwa [Real.rpow_one] at this
      rw [abs_of_nonpos (by linarith : d ^ (1/(m:ℝ)) - 1 ≤ 0),
        abs_of_nonpos (by linarith : d - 1 ≤ 0)]
      linarith
  have hval : d ^ (-(1 / (m : ℝ))) - 1 =
      d ^ (-(1 / (m : ℝ))) * (1 - d ^ (1 / (m : ℝ))) := by
    have h2 : d ^ (-(1 / (m : ℝ))) * d ^ (1 / (m : ℝ)) = 1 := hprod
    nlinarith [h2]
  rw [hval, abs_mul, abs_of_nonneg (Real.rpow_nonneg (le_of_lt hdpos) _), abs_sub_comm]
  calc d ^ (-(1 / (m : ℝ))) * |d ^ (1 / (m : ℝ)) - 1|
      ≤ 2 * |d ^ (1 / (m : ℝ)) - 1| := mul_le_mul_of_nonneg_right hnorm2 (abs_nonneg _)
    _ ≤ 2 * |d - 1| := by linarith [hdiff]

/-- The normalization factor `(det (1 + t•M))^{−1/m}` is `1 + O(t²)` for trace-free `M`. -/
lemma normCurve_coeff_bound (M : Mx) (hm : m ≠ 0) (hM : M.trace = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |t| ≤ δ →
      |((1 + t • M).det) ^ (-(1 / (m : ℝ))) - 1| ≤ C * t ^ 2 := by
  rcases det_one_add_trace_zero_bound M hM with ⟨δ₁, hδ₁pos, C₁, hC₁0, hb₁⟩
  have hcont : ContinuousAt (fun t : ℝ => (1 + t • M).det) 0 :=
    (det_one_add_smul_continuous M).continuousAt
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := Metric.continuousAt_iff.mp hcont (1/2) (by norm_num)
  refine ⟨min δ₁ (δ₂/2), lt_min hδ₁pos (by positivity), 2 * C₁, by positivity, ?_⟩
  intro t ht
  have ht₁ : |t| ≤ δ₁ := le_trans ht (min_le_left _ _)
  have ht₂ : |t| ≤ δ₂/2 := le_trans ht (min_le_right _ _)
  have hb1 : |(1 + t • M).det - 1| ≤ C₁ * t ^ 2 := hb₁ t ht₁
  have hclose : dist ((1 + t • M).det) ((1 + (0:ℝ) • M).det) < 1/2 := by
    apply hδ₂
    rw [Real.dist_eq, sub_zero]
    linarith [abs_nonneg t]
  have h0 : (1 + (0:ℝ) • M).det = 1 := by simp
  rw [Real.dist_eq, h0] at hclose
  have hle_half : |(1 + t • M).det - 1| ≤ 1/2 := le_of_lt hclose
  have hd1 : 1/2 ≤ (1 + t • M).det := by have := neg_le_of_abs_le hle_half; linarith
  have hd2 : (1 + t • M).det ≤ 3/2 := by have := le_of_abs_le hle_half; linarith
  calc |((1 + t • M).det) ^ (-(1 / (m : ℝ))) - 1|
      ≤ 2 * |(1 + t • M).det - 1| := rpow_neg_inv_sub_one_le hm hd1 hd2
    _ ≤ 2 * (C₁ * t ^ 2) := mul_le_mul_of_nonneg_left hb1 (by norm_num)
    _ = (2 * C₁) * t ^ 2 := by ring


section PartB

theorem normCurve_sub_linear (M : Mx) (hm : m ≠ 0) (hM : M.trace = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |t| ≤ δ → ∀ w : E,
      ‖Submission.ShapeDeriv.mvec (normCurve M t) w
        - Submission.ShapeDeriv.mvec (1 + t • M) w‖ ≤ C * t ^ 2 * ‖w‖ := by
  rcases normCurve_coeff_bound M hm hM with ⟨δ, hδpos, C₁, hC₁0, hb⟩
  set K : ℝ := ∑ i : Fin m, ∑ j : Fin m, |M i j| with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _))
  refine ⟨δ, hδpos, C₁ * (1 + δ * K), by positivity, ?_⟩
  intro t ht w
  have hcoef : |((1 + t • M).det) ^ (-(1 / (m : ℝ))) - 1| ≤ C₁ * t ^ 2 := hb t ht
  have hkey : Submission.ShapeDeriv.mvec (normCurve M t)
      = (((1 + t • M).det) ^ (-(1 / (m : ℝ)))) • Submission.ShapeDeriv.mvec (1 + t • M) := by
    rw [normCurve, mvec_smul']
  have hA : Submission.ShapeDeriv.mvec (normCurve M t) w
      - Submission.ShapeDeriv.mvec (1 + t • M) w
      = (((1 + t • M).det) ^ (-(1 / (m : ℝ))) - 1) •
        Submission.ShapeDeriv.mvec (1 + t • M) w := by
    rw [hkey]
    simp [sub_smul]
  rw [hA, norm_smul, Real.norm_eq_abs]
  have hpath : Submission.ShapeDeriv.mvec (1 + t • M) w = w + t • Submission.ShapeDeriv.mvec M w :=
    Submission.ShapeDeriv.path_eq M t w
  have hmw : ‖Submission.ShapeDeriv.mvec M w‖ ≤ K * ‖w‖ := by
    rw [hK]; exact Submission.ShapeDeriv.mvec_norm_le_sum_abs M w
  have hbound : ‖Submission.ShapeDeriv.mvec (1 + t • M) w‖ ≤ (1 + δ * K) * ‖w‖ := by
    rw [hpath]
    calc ‖w + t • Submission.ShapeDeriv.mvec M w‖
        ≤ ‖w‖ + ‖t • Submission.ShapeDeriv.mvec M w‖ := norm_add_le _ _
      _ = ‖w‖ + |t| * ‖Submission.ShapeDeriv.mvec M w‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖w‖ + δ * (K * ‖w‖) := by
          have h1 : |t| * ‖Submission.ShapeDeriv.mvec M w‖ ≤ δ * (K * ‖w‖) := by
            refine mul_le_mul ht ?_ (norm_nonneg _) (le_of_lt hδpos) --
            exact hmw
          linarith
      _ = (1 + δ * K) * ‖w‖ := by ring
  calc |((1 + t • M).det) ^ (-(1 / (m : ℝ))) - 1| *
        ‖Submission.ShapeDeriv.mvec (1 + t • M) w‖
      ≤ (C₁ * t ^ 2) * ((1 + δ * K) * ‖w‖) := by
        refine mul_le_mul hcoef hbound (norm_nonneg _) ?_
        exact mul_nonneg hC₁0 (sq_nonneg t)
    _ = (C₁ * (1 + δ * K)) * t ^ 2 * ‖w‖ := by ring

end PartB


section PartC

local notation "VC" => Submission.Voronoi.voronoi

/-- A function vanishing at `0` and bounded by `C t²` near `0` has derivative `0` there. -/
lemma hasDerivAt_zero_of_abs_le_sq {G : ℝ → ℝ} (h0 : G 0 = 0) {C δ : ℝ} (hδ : 0 < δ)
    (h : ∀ t : ℝ, |t| ≤ δ → |G t| ≤ C * t ^ 2) : HasDerivAt G 0 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hD : (0:ℝ) < |C| + 1 := by positivity
  have hsimp : (fun h : ℝ => G (0 + h) - G 0 - h • (0:ℝ)) = G := by
    funext h; rw [h0]; simp
  rw [hsimp]
  refine Asymptotics.IsLittleO.of_bound ?_
  intro c hc
  filter_upwards [Metric.ball_mem_nhds (0:ℝ) (lt_min hδ (div_pos hc hD))] with t ht
  have htδ : |t| ≤ δ := by
    have h1 : dist t 0 < δ := lt_of_lt_of_le (Metric.mem_ball.mp ht) (min_le_left _ _)
    rw [Real.dist_eq, sub_zero] at h1
    exact le_of_lt h1
  have ht2 : |t| < c / (|C| + 1) := by
    have h1 := Metric.mem_ball.mp ht
    rw [dist_zero_right, Real.norm_eq_abs] at h1
    exact lt_of_lt_of_le h1 (min_le_right _ _)
  have hb : |G t| ≤ C * t ^ 2 := h t htδ
  simp only [Real.norm_eq_abs]
  have hsq : |t| * |t| = t ^ 2 := by rw [← sq_abs, sq]
  have hstep : C * t ^ 2 ≤ c * |t| := by
    rw [← hsq]
    have h1 : C ≤ |C| + 1 := by
      have := le_abs_self C; linarith
    have h2 : C * (|t| * |t|) ≤ (|C| + 1) * (|t| * |t|) :=
      mul_le_mul_of_nonneg_right h1 (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have h3 : (|C| + 1) * (|t| * |t|) ≤ c * |t| := by
      have h4 : (|C| + 1) * |t| < c := by
        have := mul_lt_mul_of_pos_left ht2 hD
        rwa [mul_div_cancel₀ _ (ne_of_gt hD)] at this
      calc (|C| + 1) * (|t| * |t|) = ((|C| + 1) * |t|) * |t| := by ring
        _ ≤ c * |t| := mul_le_mul_of_nonneg_right (le_of_lt h4) (abs_nonneg _)
    linarith
  linarith

/-- Integrability of `y ↦ e^{−π‖B y‖²}` on a finite-measure set. -/
lemma integrableOn_exp_norm_mvec {ℒ : Submodule ℤ E} (hVfin : (volume : Measure E) (VC ℒ) ≠ ⊤)
    (B : Mx) :
    IntegrableOn (fun y : E => rexp (-Real.pi * ‖Submission.ShapeDeriv.mvec B y‖ ^ 2))
      (VC ℒ) := by
  refine MeasureTheory.IntegrableOn.of_bound ((lt_top_iff_ne_top).mpr hVfin) ?_ 1 ?_
  · exact (by fun_prop : Continuous
      (fun y : E => rexp (-Real.pi * ‖Submission.ShapeDeriv.mvec B y‖ ^ 2))).aestronglyMeasurable.restrict
  · filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (le_of_lt (Real.exp_pos _)), Real.exp_le_one_iff]
    nlinarith [Real.pi_pos, sq_nonneg ‖Submission.ShapeDeriv.mvec B y‖]

/-- `|e^{−u} − e^{−v}| ≤ |u − v|` for `u, v ≥ 0`. -/
lemma abs_exp_neg_sub_le {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |rexp (-u) - rexp (-v)| ≤ |u - v| := by
  have key : ∀ a b : ℝ, 0 ≤ a → a ≤ b → rexp (-a) - rexp (-b) ≤ b - a := by
    intro a b ha hab
    have hba : 0 ≤ b - a := by linarith
    have h1 : rexp (-a) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
    have h2 : rexp (-b) = rexp (-a) * rexp (-(b - a)) := by
      rw [← Real.exp_add]; ring_nf
    have h3 : 1 - (b - a) ≤ rexp (-(b - a)) := Real.one_sub_le_exp_neg (b - a)
    have h4 : rexp (-(b - a)) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
    have h5 : rexp (-a) - rexp (-b) = rexp (-a) * (1 - rexp (-(b - a))) := by rw [h2]; ring
    rw [h5]
    calc rexp (-a) * (1 - rexp (-(b - a))) ≤ 1 * (1 - rexp (-(b - a))) :=
          mul_le_mul_of_nonneg_right h1 (by linarith)
      _ = 1 - rexp (-(b - a)) := by ring
      _ ≤ b - a := by linarith
  rcases lt_or_ge v u with hvu | huv
  · have hexp : rexp (-u) ≤ rexp (-v) := Real.exp_le_exp.mpr (by linarith)
    have h1 : |u - v| = u - v := by rw [abs_of_nonneg (by linarith)]
    rw [h1, abs_of_nonpos (by linarith)]
    have := key v u hv (le_of_lt hvu)
    linarith
  · have hexp : rexp (-v) ≤ rexp (-u) := Real.exp_le_exp.mpr (by linarith)
    have h1 : |u - v| = v - u := by rw [abs_of_nonpos (by linarith)]; ring
    rw [h1, abs_of_nonneg (by linarith)]
    have := key u v hu huv
    linarith

/-- Pointwise bound on `y ↦ (1+t•M)y` on a ball of radius `R`. -/
lemma mvec_one_add_norm_le (M : Mx) (K : ℝ) (hK : K = ∑ i : Fin m, ∑ j : Fin m, |M i j|)
    (t : ℝ) (w : E) :
    ‖Submission.ShapeDeriv.mvec ((1 : Mx) + t • M) w‖ ≤ (1 + |t| * K) * ‖w‖ := by
  have hpath : Submission.ShapeDeriv.mvec ((1 : Mx) + t • M) w
      = w + t • Submission.ShapeDeriv.mvec M w := Submission.ShapeDeriv.path_eq M t w
  have hmw : ‖Submission.ShapeDeriv.mvec M w‖ ≤ K * ‖w‖ := by
    rw [hK]; exact Submission.ShapeDeriv.mvec_norm_le_sum_abs M w
  rw [hpath]
  calc ‖w + t • Submission.ShapeDeriv.mvec M w‖
      ≤ ‖w‖ + ‖t • Submission.ShapeDeriv.mvec M w‖ := norm_add_le _ _
    _ = ‖w‖ + |t| * ‖Submission.ShapeDeriv.mvec M w‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖w‖ + |t| * (K * ‖w‖) := by
        have := mul_le_mul_of_nonneg_left hmw (abs_nonneg t); linarith
    _ = (1 + |t| * K) * ‖w‖ := by ring

/-- The `h`-side functional along the normalized curve differs from the linear curve by `O(t²)`. -/
lemma shapeH_deviation {ℒ : Submodule ℤ E} (hVfin : (volume : Measure E) (VC ℒ) ≠ ⊤)
    {R : ℝ} (hR0 : 0 ≤ R) (hcell : VC ℒ ⊆ Metric.closedBall (0 : E) R)
    (M : Mx) (hm : m ≠ 0) (hM : M.trace = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |t| ≤ δ →
      |(∫ y in VC ℒ, rexp (-Real.pi * ‖Submission.ShapeDeriv.mvec (normCurve M t) y‖ ^ 2))
        - (∫ y in VC ℒ, rexp (-Real.pi * ‖Submission.ShapeDeriv.mvec ((1 : Mx) + t • M) y‖ ^ 2))|
        ≤ C * t ^ 2 := by
  rcases normCurve_sub_linear M hm hM with ⟨δ₁, hδ₁pos, C₁, hC₁0, hb⟩
  set K : ℝ := ∑ i : Fin m, ∑ j : Fin m, |M i j| with hK
  have hK0 : 0 ≤ K := by
    rw [hK]; exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _))
  refine ⟨δ₁, hδ₁pos, Real.pi * C₁ * 2 * (C₁ * δ₁ ^ 2 + 1 + δ₁ * K) * R ^ 2 *
    (volume : Measure E).real (VC ℒ), by positivity, ?_⟩
  intro t ht
  set D : ℝ := Real.pi * C₁ * 2 * (C₁ * δ₁ ^ 2 + 1 + δ₁ * K) * R ^ 2 with hD
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have htδ : t ^ 2 ≤ δ₁ ^ 2 := by
    have h1 : |t| * |t| ≤ δ₁ * δ₁ := mul_self_le_mul_self (abs_nonneg t) ht
    have h2 : |t| * |t| = t ^ 2 := by rw [← sq_abs, sq]
    have h3 : δ₁ * δ₁ = δ₁ ^ 2 := by rw [sq]
    rwa [h2, h3] at h1
  have hint1 := integrableOn_exp_norm_mvec (ℒ := ℒ) hVfin (normCurve M t)
  have hint2 := integrableOn_exp_norm_mvec (ℒ := ℒ) hVfin ((1 : Mx) + t • M)
  rw [← MeasureTheory.integral_sub hint1 hint2]
  have hpt : ∀ y ∈ VC ℒ, ‖rexp (-Real.pi * ‖Submission.ShapeDeriv.mvec (normCurve M t) y‖ ^ 2)
      - rexp (-Real.pi * ‖Submission.ShapeDeriv.mvec ((1 : Mx) + t • M) y‖ ^ 2)‖ ≤ D * t ^ 2 := by
    intro y hy
    set A : E →ₗ[ℝ] E := Submission.ShapeDeriv.mvec (normCurve M t) with hA
    set B : E →ₗ[ℝ] E := Submission.ShapeDeriv.mvec ((1 : Mx) + t • M) with hB
    have hyR : ‖y‖ ≤ R := by
      have := Metric.mem_closedBall.mp (hcell hy); simpa [dist_eq_norm] using this
    have hdev : ‖A y - B y‖ ≤ C₁ * t ^ 2 * ‖y‖ := by simpa [hA, hB] using hb t ht y
    have hBn : ‖B y‖ ≤ (1 + |t| * K) * ‖y‖ := by
      simpa [hB] using mvec_one_add_norm_le M K hK t y
    have hdevR : ‖A y - B y‖ ≤ C₁ * δ₁ ^ 2 * R := by
      have h4 : C₁ * t ^ 2 ≤ C₁ * δ₁ ^ 2 := mul_le_mul_of_nonneg_left htδ hC₁0
      calc ‖A y - B y‖ ≤ C₁ * t ^ 2 * ‖y‖ := hdev
        _ ≤ (C₁ * δ₁ ^ 2) * R := mul_le_mul h4 hyR (norm_nonneg y) (by positivity)
        _ = C₁ * δ₁ ^ 2 * R := by ring
    have hBnR : ‖B y‖ ≤ (1 + δ₁ * K) * R := by
      have h4 : |t| * K ≤ δ₁ * K := mul_le_mul_of_nonneg_right ht hK0
      calc ‖B y‖ ≤ (1 + |t| * K) * ‖y‖ := hBn
        _ ≤ (1 + δ₁ * K) * R := by
            refine mul_le_mul ?_ hyR (norm_nonneg y) (by positivity)
            linarith
    have hAnR : ‖A y‖ ≤ (C₁ * δ₁ ^ 2 + 1 + δ₁ * K) * R := by
      have h1 : ‖A y‖ ≤ ‖A y - B y‖ + ‖B y‖ := by
        have := norm_add_le (A y - B y) (B y)
        rw [sub_add_cancel] at this
        linarith
      have h2 : ‖A y - B y‖ + ‖B y‖ ≤ (C₁ * δ₁ ^ 2 + 1 + δ₁ * K) * R := by
        have := add_le_add hdevR hBnR
        calc ‖A y - B y‖ + ‖B y‖ ≤ (C₁ * δ₁ ^ 2 * R) + ((1 + δ₁ * K) * R) := this
          _ = (C₁ * δ₁ ^ 2 + 1 + δ₁ * K) * R := by ring
      linarith
    rw [Real.norm_eq_abs]
    simp only [neg_mul]
    refine le_trans (abs_exp_neg_sub_le (u := Real.pi * ‖A y‖ ^ 2)
      (v := Real.pi * ‖B y‖ ^ 2) (by positivity) (by positivity)) ?_
    have h2 : |Real.pi * ‖A y‖ ^ 2 - Real.pi * ‖B y‖ ^ 2|
        = Real.pi * |‖A y‖ ^ 2 - ‖B y‖ ^ 2| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg (le_of_lt Real.pi_pos)]
    rw [h2]
    have h3 : |‖A y‖ ^ 2 - ‖B y‖ ^ 2| = |‖A y‖ - ‖B y‖| * (‖A y‖ + ‖B y‖) := by
      rw [sq_sub_sq, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖A y‖ + ‖B y‖)]
      ring
    rw [h3]
    have h4 : |‖A y‖ - ‖B y‖| ≤ ‖A y - B y‖ := abs_norm_sub_norm_le _ _
    have h5 : ‖A y‖ + ‖B y‖ ≤ 2 * ((C₁ * δ₁ ^ 2 + 1 + δ₁ * K) * R) := by
      calc ‖A y‖ + ‖B y‖ ≤ (C₁ * δ₁ ^ 2 + 1 + δ₁ * K) * R + (1 + δ₁ * K) * R :=
            add_le_add hAnR hBnR
        _ = (C₁ * δ₁ ^ 2 + 2 + 2 * δ₁ * K) * R := by ring
        _ ≤ 2 * ((C₁ * δ₁ ^ 2 + 1 + δ₁ * K) * R) := by
            have h6 : (C₁ * δ₁ ^ 2 + 2 + 2 * δ₁ * K) * R
                ≤ (2 * C₁ * δ₁ ^ 2 + 2 + 2 * δ₁ * K) * R := by
              refine mul_le_mul_of_nonneg_right ?_ hR0
              have : 0 ≤ C₁ * δ₁ ^ 2 := by positivity
              linarith
            calc (C₁ * δ₁ ^ 2 + 2 + 2 * δ₁ * K) * R
                ≤ (2 * C₁ * δ₁ ^ 2 + 2 + 2 * δ₁ * K) * R := h6
              _ = 2 * ((C₁ * δ₁ ^ 2 + 1 + δ₁ * K) * R) := by ring
    have hdevR2 : ‖A y - B y‖ ≤ C₁ * t ^ 2 * R := by
      calc ‖A y - B y‖ ≤ C₁ * t ^ 2 * ‖y‖ := hdev
        _ ≤ C₁ * t ^ 2 * R := by
            refine mul_le_mul_of_nonneg_left hyR (by positivity)
    calc Real.pi * (|‖A y‖ - ‖B y‖| * (‖A y‖ + ‖B y‖))
        ≤ Real.pi * ((C₁ * t ^ 2 * R) * (2 * ((C₁ * δ₁ ^ 2 + 1 + δ₁ * K) * R))) := by
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt Real.pi_pos)
          exact mul_le_mul (le_trans h4 hdevR2) h5 (by positivity) (by positivity)
      _ = D * t ^ 2 := by rw [hD]; ring
  have hfin : (volume : Measure E) (VC ℒ) < ⊤ := (lt_top_iff_ne_top).mpr hVfin
  have hmain := MeasureTheory.norm_setIntegral_le_of_norm_le_const hfin hpt
  rw [show |∫ y in VC ℒ, (rexp (-Real.pi * ‖Submission.ShapeDeriv.mvec (normCurve M t) y‖ ^ 2)
        - rexp (-Real.pi * ‖Submission.ShapeDeriv.mvec ((1 : Mx) + t • M) y‖ ^ 2))|
      = ‖∫ y in VC ℒ, (rexp (-Real.pi * ‖Submission.ShapeDeriv.mvec (normCurve M t) y‖ ^ 2)
        - rexp (-Real.pi * ‖Submission.ShapeDeriv.mvec ((1 : Mx) + t • M) y‖ ^ 2))‖ from
      (Real.norm_eq_abs _).symm]
  calc ‖∫ y in VC ℒ, (rexp (-Real.pi * ‖Submission.ShapeDeriv.mvec (normCurve M t) y‖ ^ 2)
        - rexp (-Real.pi * ‖Submission.ShapeDeriv.mvec ((1 : Mx) + t • M) y‖ ^ 2))‖
      ≤ (D * t ^ 2) * (volume : Measure E).real (VC ℒ) := hmain
    _ = (D * (volume : Measure E).real (VC ℒ)) * t ^ 2 := by ring

/-- The `g`/`h` difference along the normalized curve is `O(t²)` (paper `same_grad` bound). -/
lemma shapeG_deviation (r R : ℝ) (hr : 0 < r) (hR0 : 0 ≤ R)
    {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    (hball : Metric.closedBall (0 : E) r ⊆ VC ℒ)
    (hcell : VC ℒ ⊆ Metric.closedBall (0 : E) R)
    (hlam : ∀ z : ℒ, z ≠ 0 → r ≤ ‖(z : E)‖)
    (hVfin : (volume : Measure E) (VC ℒ) ≠ ⊤)
    (M : Mx) (hm : m ≠ 0) (hM : M.trace = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |t| ≤ δ →
      |Submission.SameGrad.shapeH ℒ (Submission.ShapeDeriv.mvec (normCurve M t))
          Submission.SameGrad.fGauss
        - Submission.SameGrad.shapeG ℒ (Submission.ShapeDeriv.mvec (normCurve M t))
          Submission.SameGrad.fGauss|
        ≤ C * t ^ 2 := by
  rcases normCurve_sub_linear M hm hM with ⟨δ₁, hδ₁pos, C₁, hC₁0, hb⟩
  rcases det_one_add_trace_zero_bound M hM with ⟨δd, hδdpos, Cd, hCd0, hbd⟩
  set K : ℝ := ∑ i : Fin m, ∑ j : Fin m, |M i j| with hK
  have hK0 : 0 ≤ K := by
    rw [hK]; exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _))
  set ν : ℝ := 4 + 4 * (R / r) with hν
  have hν1 : 1 ≤ ν := by
    rw [hν]; have : 0 ≤ R / r := div_nonneg hR0 (le_of_lt hr); linarith
  have hν0 : 0 ≤ ν := by linarith
  set Ef : ℝ := C₁ * δ₁ * (1 + δ₁ * K) + K with hEf
  have hEf0 : 0 ≤ Ef := by rw [hEf]; positivity
  set δd2 : ℝ := 1 / (2 * (Cd + 1)) with hδd2
  have hδd2pos : 0 < δd2 := by rw [hδd2]; positivity
  set ρ : ℝ := 1 / (2 * (ν + 1) * (Ef + 1)) with hρ
  have hρpos : 0 < ρ := by rw [hρ]; positivity
  refine ⟨min (min δ₁ δd) (min δd2 ρ), by positivity,
    32 * Real.pi * (m : ℝ) * (2:ℝ) ^ m * R ^ 2 * ν ^ 2 * (volume : Measure E).real (VC ℒ) * Ef ^ 2,
    by positivity, ?_⟩
  intro t ht
  have ht₁ : |t| ≤ δ₁ := le_trans ht (le_trans (min_le_left _ _) (min_le_left _ _))
  have ht_d : |t| ≤ δd := le_trans ht (le_trans (min_le_left _ _) (min_le_right _ _))
  have ht_2 : |t| ≤ δd2 := le_trans ht (le_trans (min_le_right _ _) (min_le_left _ _))
  have ht_ρ : |t| ≤ ρ := le_trans ht (le_trans (min_le_right _ _) (min_le_right _ _))
  -- det positivity
  have hposd : 0 < (1 + t • M).det := by
    have h1 : |(1 + t • M).det - 1| ≤ Cd * t ^ 2 := hbd t ht_d
    have h2 : Cd * t ^ 2 ≤ Cd * δd2 ^ 2 := by
      have htδ : t ^ 2 ≤ δd2 ^ 2 := by
        have h := mul_self_le_mul_self (abs_nonneg t) ht_2
        rwa [← sq, ← sq, sq_abs] at h
      exact mul_le_mul_of_nonneg_left htδ hCd0
    have hCd1 : (0:ℝ) < 2 * (Cd + 1) := by linarith
    have hCd1sq : (0:ℝ) < (2 * (Cd + 1)) ^ 2 := by positivity
    have h3 : Cd * δd2 ^ 2 ≤ 1 / 2 := by
      rw [hδd2, div_pow, one_pow, mul_one_div, div_le_iff₀ hCd1sq]
      nlinarith [hCd0, sq_nonneg Cd, sq_nonneg (Cd + 1)]
    have hle : |(1 + t • M).det - 1| ≤ 1 / 2 := h1.trans (h2.trans h3)
    have := neg_le_of_abs_le hle
    linarith
  have hdet1 : (normCurve M t).det = 1 := normCurve_det M hm t hposd
  have hdetmv : LinearMap.det (Submission.ShapeDeriv.mvec (normCurve M t)) = (normCurve M t).det := by
    simpa [Submission.ShapeDeriv.fA] using Submission.ShapeDeriv.det_fA (normCurve M t)
  have hdetne : LinearMap.det (Submission.ShapeDeriv.mvec (normCurve M t)) ≠ 0 := by
    rw [hdetmv, hdet1]; exact one_ne_zero
  set ε : ℝ := C₁ * t ^ 2 * (1 + δ₁ * K) + |t| * K with hε
  have hε0 : 0 ≤ ε := by rw [hε]; positivity
  have hEbound : ε ≤ Ef * |t| := by
    have h1 : C₁ * t ^ 2 * (1 + δ₁ * K) ≤ C₁ * δ₁ * (1 + δ₁ * K) * |t| := by
      have htδ : t ^ 2 ≤ δ₁ * |t| := by
        have h := mul_le_mul_of_nonneg_right ht₁ (abs_nonneg t)
        rwa [← sq, sq_abs] at h
      have h2 : 0 ≤ C₁ * (1 + δ₁ * K) := by positivity
      nlinarith [htδ, h2, abs_nonneg t]
    have h3 : |t| * K = K * |t| := mul_comm _ _
    have hexp : Ef * |t| = (C₁ * δ₁ * (1 + δ₁ * K) + K) * |t| := by rw [hEf]
    rw [hε, hexp]
    nlinarith [h1, h3, abs_nonneg t]
  have hEfρ : Ef * ρ ≤ 1 / 2 := by
    rw [hρ, mul_div_assoc', div_le_iff₀ (by positivity : (0:ℝ) < 2 * (ν + 1) * (Ef + 1))]
    nlinarith [hEf0, hν1]
  have hsmallEf : Ef * |t| ≤ 1 / 2 := by
    have h1 : Ef * |t| ≤ Ef * ρ := mul_le_mul_of_nonneg_left ht_ρ hEf0
    linarith
  have hε1 : ε ≤ 1 / 2 := le_trans hEbound hsmallEf
  have hνe : ν * ε < 1 := by
    have h1 : ν * ε ≤ ν * (Ef * |t|) := mul_le_mul_of_nonneg_left hEbound hν0
    have h2 : ν * (Ef * |t|) ≤ ν * (Ef * ρ) := by
      have := mul_le_mul_of_nonneg_left ht_ρ hEf0
      exact mul_le_mul_of_nonneg_left this hν0
    have h3 : ν * (Ef * ρ) < 1 := by
      rw [hρ, ← mul_assoc, mul_one_div,
        div_lt_one (by positivity : (0:ℝ) < 2 * (ν + 1) * (Ef + 1))]
      nlinarith [hEf0, hν0]
    linarith
  have hA : ∀ w : E, ‖Submission.ShapeDeriv.mvec (normCurve M t) w - w‖ ≤ ε * ‖w‖ := by
    intro w
    have hdev : ‖Submission.ShapeDeriv.mvec (normCurve M t) w
        - Submission.ShapeDeriv.mvec ((1 : Mx) + t • M) w‖ ≤ C₁ * t ^ 2 * ‖w‖ := hb t ht₁ w
    have h2 : Submission.ShapeDeriv.mvec ((1 : Mx) + t • M) w - w
        = t • Submission.ShapeDeriv.mvec M w := by
      rw [Submission.ShapeDeriv.path_eq]; abel
    have h3 : ‖Submission.ShapeDeriv.mvec ((1 : Mx) + t • M) w - w‖ ≤ |t| * K * ‖w‖ := by
      rw [h2, norm_smul, Real.norm_eq_abs]
      have hmw : ‖Submission.ShapeDeriv.mvec M w‖ ≤ K * ‖w‖ := by
        rw [hK]; exact Submission.ShapeDeriv.mvec_norm_le_sum_abs M w
      nlinarith [hmw, abs_nonneg t, norm_nonneg w]
    have hsum : Submission.ShapeDeriv.mvec (normCurve M t) w - w
        = (Submission.ShapeDeriv.mvec (normCurve M t) w
            - Submission.ShapeDeriv.mvec ((1 : Mx) + t • M) w)
          + (Submission.ShapeDeriv.mvec ((1 : Mx) + t • M) w - w) := by abel
    rw [hsum]
    calc ‖_ + _‖ ≤ C₁ * t ^ 2 * ‖w‖ + |t| * K * ‖w‖ := norm_add_le_of_le hdev h3
      _ ≤ (C₁ * t ^ 2 * (1 + δ₁ * K) + |t| * K) * ‖w‖ := by
          have h1 : C₁ * t ^ 2 * ‖w‖ ≤ C₁ * t ^ 2 * (1 + δ₁ * K) * ‖w‖ := by
            have h1a : 0 ≤ C₁ * t ^ 2 := mul_nonneg hC₁0 (sq_nonneg t)
            have h1b : (1:ℝ) ≤ 1 + δ₁ * K := by nlinarith [hK0, hδ₁pos]
            calc C₁ * t ^ 2 * ‖w‖ = (C₁ * t ^ 2) * 1 * ‖w‖ := by ring
              _ ≤ (C₁ * t ^ 2) * (1 + δ₁ * K) * ‖w‖ := by
                  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg w)
                  exact mul_le_mul_of_nonneg_left h1b h1a
              _ = C₁ * t ^ 2 * (1 + δ₁ * K) * ‖w‖ := by ring
          have hexp : (C₁ * t ^ 2 * (1 + δ₁ * K) + |t| * K) * ‖w‖
              = C₁ * t ^ 2 * (1 + δ₁ * K) * ‖w‖ + |t| * K * ‖w‖ := by ring
          rw [hexp]; linarith
      _ = ε * ‖w‖ := by rw [hε]
  have hfmeas : Measurable Submission.SameGrad.fGauss := by
    rw [show Submission.SameGrad.fGauss = fun u : ℝ => rexp (-Real.pi * u) from rfl]
    exact Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id)
  have hdiff : ∀ u ∈ Set.Icc 0 ((2 * R) ^ 2), DifferentiableAt ℝ Submission.SameGrad.fGauss u := by
    intro u _
    rw [show Submission.SameGrad.fGauss = fun u : ℝ => rexp (-Real.pi * u) from rfl]
    exact ((Real.hasDerivAt_exp (-Real.pi * u)).comp u (hasDerivAt_const_mul (-Real.pi))).differentiableAt
  have hderiv_val : ∀ u : ℝ, deriv Submission.SameGrad.fGauss u = -Real.pi * rexp (-Real.pi * u) := by
    intro u
    have h2 := (Real.hasDerivAt_exp (-Real.pi * u)).comp u (hasDerivAt_const_mul (-Real.pi))
    have h3 := h2.deriv
    rw [show Submission.SameGrad.fGauss = fun u : ℝ => rexp (-Real.pi * u) from rfl]
    simpa [mul_comm] using h3
  have hbound : ∀ u ∈ Set.Icc 0 ((2 * R) ^ 2), ‖deriv Submission.SameGrad.fGauss u‖ ≤ Real.pi := by
    intro u hu
    rw [hderiv_val u, Real.norm_eq_abs, abs_mul, abs_neg,
      abs_of_nonneg (le_of_lt Real.pi_pos)]
    have hexp0 : 0 ≤ rexp (-Real.pi * u) := le_of_lt (Real.exp_pos _)
    rw [abs_of_nonneg hexp0]
    have hexp : rexp (-Real.pi * u) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, hu.1]
    nlinarith [Real.pi_pos]
  have hmain := Submission.SameGrad.det_mul_shapeH_sub_shapeG_le' (ℒ := ℒ) r R ε hr hR0 hε0
    hε1 hνe hℒ hdetne hball hcell hlam hA hfmeas Real.pi_pos.le hdiff hbound hVfin
  -- |det A| = 1
  have habs1 : |LinearMap.det (Submission.ShapeDeriv.mvec (normCurve M t))| = 1 := by
    rw [hdetmv, hdet1, abs_one]
  rw [habs1, one_mul] at hmain
  -- bound S·B ≤ C ε²
  have ha0 : 0 ≤ ν * ε := by positivity
  have ha1 : ν * ε ≤ 1 := le_of_lt hνe
  have hS : ((1 + ν * ε) ^ (Module.finrank ℝ E) - (1 - ν * ε) ^ (Module.finrank ℝ E))
      ≤ (Module.finrank ℝ E : ℝ) * (2:ℝ) ^ (Module.finrank ℝ E) * (ν * ε) :=
    Submission.EpsVoronoi.shell_pow_lin (Module.finrank ℝ E) (ν * ε) ha0 ha1
  have hfinE : Module.finrank ℝ E = m := by simp
  rw [hfinE] at hS
  have hone : 1 + ν * ε ≤ 2 := by linarith
  have hvol0 : 0 ≤ (volume : Measure E).real (VC ℒ) := measureReal_nonneg
  have hbound2 : ((((1 + ν * ε) ^ m - (1 - ν * ε) ^ m) * (volume : Measure E).real (VC ℒ)) *
      (Real.pi * (2 * (2 * R)) * (4 * (ν * ε) * (1 + ν * ε) * R)))
      ≤ 32 * Real.pi * (m : ℝ) * (2:ℝ) ^ m * R ^ 2 * ν ^ 2 * (volume : Measure E).real (VC ℒ)
        * Ef ^ 2 * t ^ 2 := by
    have hS' : ((1 + ν * ε) ^ m - (1 - ν * ε) ^ m) * (volume : Measure E).real (VC ℒ)
        ≤ ((m:ℝ) * (2:ℝ)^m * (ν*ε)) * (volume : Measure E).real (VC ℒ) :=
      mul_le_mul_of_nonneg_right hS hvol0
    have hB0 : 0 ≤ Real.pi * (2 * (2*R)) * (4 * (ν*ε) * (1 + ν*ε) * R) := by positivity
    refine le_trans (mul_le_mul_of_nonneg_right hS' hB0) ?_
    have hEq : ((m:ℝ) * (2:ℝ)^m * (ν*ε)) * (volume : Measure E).real (VC ℒ) *
          (Real.pi * (2 * (2*R)) * (4 * (ν*ε) * (1 + ν*ε) * R))
        = 16 * Real.pi * (m:ℝ) * (2:ℝ)^m * R^2 * ν^2 * (volume : Measure E).real (VC ℒ)
          * ε^2 * (1 + ν*ε) := by ring
    rw [hEq]
    have h6 : 0 ≤ 16 * Real.pi * (m:ℝ) * (2:ℝ)^m * R^2 * ν^2 * (volume : Measure E).real (VC ℒ)
        * ε^2 := by positivity
    refine le_trans (mul_le_mul_of_nonneg_left hone h6) ?_
    have h7 : ε ^ 2 ≤ Ef ^ 2 * t ^ 2 := by
      have h8 : ε ≤ Ef * |t| := hEbound
      have h9 : 0 ≤ ε := hε0
      nlinarith [h8, h9, hEf0, abs_nonneg t, sq_abs t]
    have h8 : 0 ≤ 32 * Real.pi * (m:ℝ) * (2:ℝ)^m * R^2 * ν^2 * (volume : Measure E).real (VC ℒ) := by
      positivity
    calc 16 * Real.pi * (m:ℝ) * (2:ℝ)^m * R^2 * ν^2 * (volume : Measure E).real (VC ℒ) * ε^2 * 2
        = (32 * Real.pi * (m:ℝ) * (2:ℝ)^m * R^2 * ν^2 * (volume : Measure E).real (VC ℒ)) * ε^2 := by
          ring
      _ ≤ (32 * Real.pi * (m:ℝ) * (2:ℝ)^m * R^2 * ν^2 * (volume : Measure E).real (VC ℒ))
            * (Ef ^ 2 * t ^ 2) := mul_le_mul_of_nonneg_left h7 h8
      _ = 32 * Real.pi * (m:ℝ) * (2:ℝ)^m * R^2 * ν^2 * (volume : Measure E).real (VC ℒ)
            * Ef ^ 2 * t ^ 2 := by ring
  rw [← hν, hfinE] at hmain
  exact hmain.trans hbound2


/-- **Change of variables `h`-side, general matrix.**  For `B.det ≠ 0`,
`h(B) = ∫_{V(ℒ)} e^{−π‖B y‖²}`. -/
lemma shapeH_eq_integral_mvec (ℒ : Submodule ℤ E) (B : Mx) (hdet : B.det ≠ 0) :
    Submission.SameGrad.shapeH ℒ (Submission.ShapeDeriv.mvec B) Submission.SameGrad.fGauss
      = ∫ y in VC ℒ, rexp (-Real.pi * ‖Submission.ShapeDeriv.mvec B y‖ ^ 2) := by
  have h := Submission.ShapeDeriv.integral_image_fA (A := B) hdet
    (fun x : E => rexp (-Real.pi * ‖x‖ ^ 2)) (VC ℒ)
  simp only [Submission.ShapeDeriv.fA] at h
  have hdetL : LinearMap.det (Submission.ShapeDeriv.mvec B) = B.det := by
    simpa [Submission.ShapeDeriv.fA] using Submission.ShapeDeriv.det_fA B
  unfold Submission.SameGrad.shapeH Submission.SameGrad.fGauss
  rw [hdetL, h, ← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.mpr hdet), one_mul]

/-- `γ₁` of a determinant-one image is the `shapeG` functional. -/
lemma gammaMass_one_image_eq_shapeG (ℒ : Submodule ℤ E) (A : Mx) (hA : |A.det| = 1) :
    Submission.GaussianMeasure.gammaMass 1
        (VC (ℒ.map ((Submission.ShapeDeriv.mvec A).restrictScalars ℤ)))
      = Submission.SameGrad.shapeG ℒ (Submission.ShapeDeriv.mvec A) Submission.SameGrad.fGauss := by
  have hdetL : LinearMap.det (Submission.ShapeDeriv.mvec A) = A.det := by
    simpa [Submission.ShapeDeriv.fA] using Submission.ShapeDeriv.det_fA A
  have h1 : |LinearMap.det (Submission.ShapeDeriv.mvec A)| = 1 := by rw [hdetL, hA]
  unfold Submission.SameGrad.shapeG Submission.SameGrad.fGauss
  rw [h1, inv_one, one_mul, Submission.GaussianMeasure.gammaMass_one]

/-- **The derivative of the cell-side functional along the normalized curve** is the S3 pairing
value (paper `same_grad_VL`, `∇g(I) = ∇h(I)` combined with the admissible det-one curve). -/
theorem normCurve_shapeG_hasDerivAt (r R : ℝ) (hr : 0 < r) (hR0 : 0 ≤ R)
    {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    (hball : Metric.closedBall (0 : E) r ⊆ VC ℒ)
    (hcell : VC ℒ ⊆ Metric.closedBall (0 : E) R)
    (hlam : ∀ z : ℒ, z ≠ 0 → r ≤ ‖(z : E)‖)
    (hVfin : (volume : Measure E) (VC ℒ) ≠ ⊤)
    (M : Mx) (hm : m ≠ 0) (hM : M.trace = 0) :
    HasDerivAt (fun t : ℝ => Submission.SameGrad.shapeG ℒ (Submission.ShapeDeriv.mvec (normCurve M t))
        Submission.SameGrad.fGauss)
      (-2 * Real.pi * ∑ i : Fin m, ∑ j : Fin m, M i j *
        Submission.ShapeDeriv.secondMoment (VC ℒ) i j) 0 := by
  set L : ℝ := -2 * Real.pi * ∑ i : Fin m, ∑ j : Fin m, M i j *
      Submission.ShapeDeriv.secondMoment (VC ℒ) i j with hL
  -- (i) the linear curve, `h`-side
  have hχ : HasDerivAt (fun t : ℝ => Submission.SameGrad.shapeH ℒ
      (Submission.ShapeDeriv.mvec ((1 : Mx) + t • M)) Submission.SameGrad.fGauss) L 0 := by
    have h0 := Submission.SameGrad.shapeH_curve_hasDerivAt (ℒ := ℒ) M
    have htp := Submission.ShapeDeriv.trace_pairing M (VC ℒ) (Submission.Voronoi.voronoi_measurable ℒ)
    rw [htp] at h0
    rw [hL]
    exact h0
  -- (ii) ψ − χ = O(t²)
  have hψ : HasDerivAt (fun t : ℝ => ∫ y in VC ℒ,
      rexp (-Real.pi * ‖Submission.ShapeDeriv.mvec (normCurve M t) y‖ ^ 2)) L 0 := by
    rcases shapeH_deviation (ℒ := ℒ) hVfin hR0 hcell M hm hM with ⟨δ, hδpos, C, hC0, hdev⟩
    have h0 : (fun t : ℝ => (∫ y in VC ℒ,
        rexp (-Real.pi * ‖Submission.ShapeDeriv.mvec (normCurve M t) y‖ ^ 2))
        - (∫ y in VC ℒ,
          rexp (-Real.pi * ‖Submission.ShapeDeriv.mvec ((1 : Mx) + t • M) y‖ ^ 2))) 0 = 0 := by
      simp only [Pi.sub_apply, normCurve_zero', zero_smul, add_zero,
        Submission.SameGrad.mvec_one_eq_id, LinearMap.id_apply, sub_self]
    have hE : HasDerivAt (fun t : ℝ => (∫ y in VC ℒ,
        rexp (-Real.pi * ‖Submission.ShapeDeriv.mvec (normCurve M t) y‖ ^ 2))
        - (∫ y in VC ℒ,
          rexp (-Real.pi * ‖Submission.ShapeDeriv.mvec ((1 : Mx) + t • M) y‖ ^ 2))) 0 0 :=
      hasDerivAt_zero_of_abs_le_sq h0 hδpos hdev
    have hχ' : HasDerivAt (fun t : ℝ => ∫ y in VC ℒ,
        rexp (-Real.pi * ‖Submission.ShapeDeriv.mvec ((1 : Mx) + t • M) y‖ ^ 2)) L 0 := by
      refine hχ.congr_of_eventuallyEq ?_
      have hK0 : 0 ≤ ∑ i : Fin m, ∑ j : Fin m, |M i j| :=
        Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _))
      have hrad : (0:ℝ) < 1 / (2 * (1 + (∑ i : Fin m, ∑ j : Fin m, |M i j|))) := by positivity
      filter_upwards [Metric.ball_mem_nhds (0:ℝ) hrad] with t ht
      have htabs : |t| < 1 / (2 * (1 + (∑ i : Fin m, ∑ j : Fin m, |M i j|))) := by
        have := Metric.mem_ball.mp ht; rwa [Real.dist_eq, sub_zero] at this
      have hK0 : 0 ≤ ∑ i : Fin m, ∑ j : Fin m, |M i j| :=
        Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _))
      have hlt : |t| * (∑ i : Fin m, ∑ j : Fin m, |M i j|) < 1 := by
        have h1 : |t| * (∑ i : Fin m, ∑ j : Fin m, |M i j|)
            ≤ (1 / (2 * (1 + (∑ i : Fin m, ∑ j : Fin m, |M i j|)))) *
              (∑ i : Fin m, ∑ j : Fin m, |M i j|) :=
          mul_le_mul_of_nonneg_right (le_of_lt htabs) hK0
        have h2 : (1 / (2 * (1 + (∑ i : Fin m, ∑ j : Fin m, |M i j|)))) *
              (∑ i : Fin m, ∑ j : Fin m, |M i j|) ≤ 1 / 2 := by
          rw [div_mul_eq_mul_div,
            div_le_iff₀ (by linarith [hK0] : (0:ℝ) < 2 * (1 + (∑ i : Fin m, ∑ j : Fin m, |M i j|)))]
          linarith
        linarith
      have hdetne : ((1 : Mx) + t • M).det ≠ 0 := by
        have h1 := Submission.SameGrad.det_ne_zero_of_close
          (Submission.ShapeDeriv.mvec ((1 : Mx) + t • M))
          (|t| * (∑ i : Fin m, ∑ j : Fin m, |M i j|)) hlt
          (Submission.SameGrad.curve_lipschitz M (∑ i : Fin m, ∑ j : Fin m, |M i j|) t rfl)
        have h2 : LinearMap.det (Submission.ShapeDeriv.mvec ((1 : Mx) + t • M))
            = ((1 : Mx) + t • M).det := by
          simpa [Submission.ShapeDeriv.fA] using Submission.ShapeDeriv.det_fA ((1 : Mx) + t • M)
        intro hz
        exact h1 (by rw [h2]; exact hz)
      exact (Submission.SameGrad.shapeH_curve_eq (ℒ := ℒ) M t hdetne).symm
    have hsum := hE.add hχ'
    have hfun : ((fun t : ℝ => (∫ y in VC ℒ,
        rexp (-Real.pi * ‖Submission.ShapeDeriv.mvec (normCurve M t) y‖ ^ 2))
        - (∫ y in VC ℒ,
          rexp (-Real.pi * ‖Submission.ShapeDeriv.mvec ((1 : Mx) + t • M) y‖ ^ 2)))
      + (fun t : ℝ => ∫ y in VC ℒ,
          rexp (-Real.pi * ‖Submission.ShapeDeriv.mvec ((1 : Mx) + t • M) y‖ ^ 2)))
      = (fun t : ℝ => ∫ y in VC ℒ,
          rexp (-Real.pi * ‖Submission.ShapeDeriv.mvec (normCurve M t) y‖ ^ 2)) := by
      exact sub_add_cancel _ _
    rw [hfun] at hsum
    simpa using hsum
  -- (iii) transfer to the `shapeH`-curve
  have hH : HasDerivAt (fun t : ℝ => Submission.SameGrad.shapeH ℒ
      (Submission.ShapeDeriv.mvec (normCurve M t)) Submission.SameGrad.fGauss) L 0 := by
    refine hψ.congr_of_eventuallyEq ?_
    rcases det_one_add_trace_zero_bound M hM with ⟨δd, hδdpos, Cd, hCd0, hbd⟩
    have hCd1 : (0:ℝ) < 2 * (Cd + 1) := by linarith
    have hCd1sq : (0:ℝ) < (2 * (Cd + 1)) ^ 2 := by positivity
    have h3 : Cd * (1 / (2 * (Cd + 1))) ^ 2 ≤ 1 / 2 := by
      rw [div_pow, one_pow, mul_one_div, div_le_iff₀ hCd1sq]
      nlinarith [hCd0, sq_nonneg Cd, sq_nonneg (Cd + 1)]
    have hrad2 : (0:ℝ) < 1 / (2 * (Cd + 1)) := by positivity
    filter_upwards [Metric.ball_mem_nhds (0:ℝ) (lt_min hδdpos hrad2)] with t ht
    have hbase : dist t 0 < min δd (1 / (2 * (Cd + 1))) := Metric.mem_ball.mp ht
    rw [Real.dist_eq, sub_zero] at hbase
    have htd : |t| < δd := lt_of_lt_of_le hbase (min_le_left _ _)
    have ht2 : |t| < 1 / (2 * (Cd + 1)) := lt_of_lt_of_le hbase (min_le_right _ _)
    have ht2' : |t| ≤ 1 / (2 * (Cd + 1)) := le_of_lt ht2
    have h1 : |(1 + t • M).det - 1| ≤ Cd * t ^ 2 := hbd t (le_of_lt htd)
    have h2 : Cd * t ^ 2 ≤ Cd * (1 / (2 * (Cd + 1))) ^ 2 := by
      have htδ : t ^ 2 ≤ (1 / (2 * (Cd + 1))) ^ 2 := by
        have h := mul_self_le_mul_self (abs_nonneg t) ht2'
        rwa [← sq, ← sq, sq_abs] at h
      exact mul_le_mul_of_nonneg_left htδ hCd0
    have hle : |(1 + t • M).det - 1| ≤ 1 / 2 := h1.trans (h2.trans h3)
    have hpos : 0 < (1 + t • M).det := by
      have := neg_le_of_abs_le hle; linarith
    rw [shapeH_eq_integral_mvec (ℒ := ℒ) (normCurve M t) (by rw [normCurve_det M hm t hpos]; exact one_ne_zero)]
  -- (iv) g − h = O(t²) and assembly
  rcases shapeG_deviation (ℒ := ℒ) r R hr hR0 hℒ hball hcell hlam hVfin M hm hM with ⟨δ, hδpos, C, hC0, hdev⟩
  have h0 : (fun t : ℝ => Submission.SameGrad.shapeH ℒ (Submission.ShapeDeriv.mvec (normCurve M t))
      Submission.SameGrad.fGauss
      - Submission.SameGrad.shapeG ℒ (Submission.ShapeDeriv.mvec (normCurve M t))
        Submission.SameGrad.fGauss) 0 = 0 := by
    simp only [normCurve_zero', Submission.SameGrad.mvec_one_eq_id, Pi.sub_apply]
    unfold Submission.SameGrad.shapeH Submission.SameGrad.shapeG
    rw [LinearMap.restrictScalars_id ℤ, Submodule.map_id, LinearMap.id_coe,
      Set.image_id, LinearMap.det_id]
    norm_num
  have hE : HasDerivAt (fun t : ℝ => Submission.SameGrad.shapeH ℒ
      (Submission.ShapeDeriv.mvec (normCurve M t)) Submission.SameGrad.fGauss
      - Submission.SameGrad.shapeG ℒ (Submission.ShapeDeriv.mvec (normCurve M t))
        Submission.SameGrad.fGauss) 0 0 :=
    hasDerivAt_zero_of_abs_le_sq h0 hδpos hdev
  have := hH.sub hE
  have hfun : ((fun t : ℝ => Submission.SameGrad.shapeH ℒ (Submission.ShapeDeriv.mvec (normCurve M t))
        Submission.SameGrad.fGauss)
      - (fun t : ℝ => Submission.SameGrad.shapeH ℒ (Submission.ShapeDeriv.mvec (normCurve M t))
          Submission.SameGrad.fGauss
        - Submission.SameGrad.shapeG ℒ (Submission.ShapeDeriv.mvec (normCurve M t))
          Submission.SameGrad.fGauss))
      = (fun t : ℝ => Submission.SameGrad.shapeG ℒ (Submission.ShapeDeriv.mvec (normCurve M t))
          Submission.SameGrad.fGauss) := by
    exact sub_sub_cancel _ _
  rw [hfun] at this
  simpa using this


/-- Entrywise linear bound for the normalized curve (trace-free `M`). -/
lemma normCurve_entry_bound (M : Mx) (hm : m ≠ 0) (hM : M.trace = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |t| ≤ δ → ∀ j i : Fin m,
      |normCurve M t j i - (1 : Mx) j i| ≤ C * |t| := by
  rcases normCurve_coeff_bound M hm hM with ⟨δ₁, hδ₁pos, C₁, hC₁0, hb⟩
  set K : ℝ := ∑ i : Fin m, ∑ j : Fin m, |M i j| with hK
  have hK0 : 0 ≤ K := by
    rw [hK]; exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _))
  refine ⟨min δ₁ 1, lt_min hδ₁pos one_pos, C₁ + (1 + C₁) * K, by positivity, ?_⟩
  intro t ht j i
  have ht₁ : |t| ≤ δ₁ := le_trans ht (min_le_left _ _)
  have ht1' : |t| ≤ 1 := le_trans ht (min_le_right _ _)
  have hcoef : |((1 + t • M).det) ^ (-(1 / (m : ℝ))) - 1| ≤ C₁ * t ^ 2 := hb t ht₁
  have ht2 : t ^ 2 ≤ |t| := by
    have h := mul_self_le_mul_self (abs_nonneg t) ht1'
    have h2 : |t| * |t| = t ^ 2 := by rw [← sq_abs, sq]
    have h3 : (1:ℝ) * 1 = 1 := by norm_num
    rw [h3, h2] at h
    nlinarith [h, h2, abs_nonneg t]
  have hc_ub : |((1 + t • M).det) ^ (-(1 / (m : ℝ)))| ≤ 1 + C₁ := by
    have h1 : |((1 + t • M).det) ^ (-(1 / (m : ℝ))) - 1| ≤ C₁ * t ^ 2 := hcoef
    have h2 : C₁ * t ^ 2 ≤ C₁ * 1 := mul_le_mul_of_nonneg_left (le_trans ht2 ht1') hC₁0
    have h3 := abs_sub_abs_le_abs_sub ((1 + t • M).det ^ (-(1 / (m : ℝ)))) 1
    rw [abs_one] at h3
    linarith
  have hMji : |M j i| ≤ K := by
    rw [hK]
    calc |M j i| ≤ ∑ k : Fin m, |M j k| :=
          Finset.single_le_sum (s := Finset.univ) (f := fun k => |M j k|)
            (fun k _ => abs_nonneg _) (Finset.mem_univ i)
      _ ≤ ∑ l : Fin m, ∑ k : Fin m, |M l k| :=
          Finset.single_le_sum (s := Finset.univ) (f := fun l => ∑ k : Fin m, |M l k|)
            (fun l _ => Finset.sum_nonneg (fun k _ => abs_nonneg _)) (Finset.mem_univ j)
  have hone : |(1 : Mx) j i| ≤ 1 := by
    rw [Matrix.one_apply]
    by_cases h : j = i <;> simp [h]
  have hval : normCurve M t j i - (1 : Mx) j i
      = (((1 + t • M).det) ^ (-(1 / (m : ℝ))) - 1) * (1 : Mx) j i
        + ((1 + t • M).det) ^ (-(1 / (m : ℝ))) * (t * M j i) := by
    rw [normCurve_apply]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [hval]
  calc |(((1 + t • M).det) ^ (-(1 / (m : ℝ))) - 1) * (1 : Mx) j i
        + ((1 + t • M).det) ^ (-(1 / (m : ℝ))) * (t * M j i)|
      ≤ |(((1 + t • M).det) ^ (-(1 / (m : ℝ))) - 1) * (1 : Mx) j i|
        + |((1 + t • M).det) ^ (-(1 / (m : ℝ))) * (t * M j i)| := abs_add_le _ _
    _ = |((1 + t • M).det) ^ (-(1 / (m : ℝ))) - 1| * |(1 : Mx) j i|
        + |((1 + t • M).det) ^ (-(1 / (m : ℝ)))| * |t * M j i| := by
        rw [abs_mul, abs_mul]
    _ ≤ (C₁ * t ^ 2) * 1 + (1 + C₁) * (|t| * K) := by
        refine add_le_add (mul_le_mul hcoef hone (abs_nonneg _) (by positivity)) ?_
        refine mul_le_mul hc_ub ?_ (abs_nonneg _) (by positivity)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hMji (abs_nonneg t)
    _ ≤ (C₁ + (1 + C₁) * K) * |t| := by
        have h2 : C₁ * t ^ 2 ≤ C₁ * |t| := mul_le_mul_of_nonneg_left ht2 hC₁0
        nlinarith [h2, abs_nonneg t, hC₁0, hK0]

/-- `γ₁(V ℒ)` is `shapeG` at the identity. -/
lemma gammaMass_one_voronoi_eq (ℒ : Submodule ℤ E) :
    Submission.GaussianMeasure.gammaMass 1 (VC ℒ)
      = Submission.SameGrad.shapeG ℒ
          (Submission.ShapeDeriv.mvec (1 : Mx)) Submission.SameGrad.fGauss := by
  have h := gammaMass_one_image_eq_shapeG ℒ (1 : Mx) (by simp)
  have hmap : ℒ.map ((Submission.ShapeDeriv.mvec (1 : Mx)).restrictScalars ℤ) = ℒ := by
    rw [Submission.SameGrad.mvec_one_eq_id, LinearMap.restrictScalars_id ℤ, Submodule.map_id]
  rw [hmap] at h
  exact h

/-- `shapeG` at the normalized curve's value at `0` is `γ₁(V ℒ)`. -/
lemma shapeG_normCurve_zero (ℒ : Submodule ℤ E) (M : Mx) :
    Submission.SameGrad.shapeG ℒ (Submission.ShapeDeriv.mvec (normCurve M 0))
        Submission.SameGrad.fGauss
      = Submission.GaussianMeasure.gammaMass 1 (VC ℒ) := by
  rw [normCurve_zero', ← gammaMass_one_voronoi_eq ℒ]

/-- **Isotropy of the Voronoi cell from a local minimum over the determinant-one locus.**

If the determinant-one locus of positions has a local minimum of `γ₁(V(·))` at the identity,
then the Gaussian second-moment matrix of `V(ℒ)` is a scalar multiple of the identity. -/
theorem secondMoment_scalar_of_local_min
    {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    (r R : ℝ) (hr : 0 < r) (hR0 : 0 ≤ R)
    (hball : Metric.closedBall (0 : E) r ⊆ VC ℒ)
    (hcell : VC ℒ ⊆ Metric.closedBall (0 : E) R)
    (hlam : ∀ z : ℒ, z ≠ 0 → r ≤ ‖(z : E)‖)
    (hVfin : (volume : Measure E) (VC ℒ) ≠ ⊤)
    (hloc : ∃ δ : ℝ, 0 < δ ∧ ∀ A : Mx, A.det ≠ 0 → |A.det| = 1 →
      (∀ j i : Fin m, |A j i - (1 : Mx) j i| < δ) →
      Submission.GaussianMeasure.gammaMass 1 (VC ℒ) ≤
        Submission.GaussianMeasure.gammaMass 1
          (VC (ℒ.map ((Submission.ShapeDeriv.mvec A).restrictScalars ℤ))))
    (hm : 2 ≤ m) :
    ∃ α : ℝ, ∀ i j : Fin m,
      Submission.ShapeDeriv.secondMoment (VC ℒ) i j = α * (if i = j then 1 else 0) := by
  classical
  have hmnz : m ≠ 0 := by omega
  -- the key orthogonality for every trace-free M
  have horth : ∀ M : Mx, M.trace = 0 →
      ∑ i : Fin m, ∑ j : Fin m, M i j * Submission.ShapeDeriv.secondMoment (VC ℒ) i j = 0 := by
    intro M hM
    rcases hloc with ⟨δl, hδlpos, hl⟩
    rcases normCurve_entry_bound M hmnz hM with ⟨δe, hδepos, Ce, hCe0, hentry⟩
    -- the local-min inequality along the curve
    rcases det_one_add_trace_zero_bound M hM with ⟨δd, hδdpos, Cd, hCd0, hbd⟩
    have hCd1 : (0:ℝ) < 2 * (Cd + 1) := by linarith
    have hCd1sq : (0:ℝ) < (2 * (Cd + 1)) ^ 2 := by positivity
    have h3 : Cd * (1 / (2 * (Cd + 1))) ^ 2 ≤ 1 / 2 := by
      rw [div_pow, one_pow, mul_one_div, div_le_iff₀ hCd1sq]
      nlinarith [hCd0, sq_nonneg Cd, sq_nonneg (Cd + 1)]
    have hrad4 : (0:ℝ) < 1 / (2 * (Cd + 1)) := by positivity
    have hrad3 : (0:ℝ) < δl / (Ce + 1) := div_pos hδlpos (by positivity)
    have hmin : ∀ᶠ t in 𝓝 (0:ℝ), Submission.SameGrad.shapeG ℒ
          (Submission.ShapeDeriv.mvec (normCurve M 0)) Submission.SameGrad.fGauss
        ≤ Submission.SameGrad.shapeG ℒ (Submission.ShapeDeriv.mvec (normCurve M t))
            Submission.SameGrad.fGauss := by
      filter_upwards [Metric.ball_mem_nhds (0:ℝ)
        (lt_min (lt_min hδepos hδdpos) (lt_min hrad3 hrad4))] with t ht
      have htabs : |t| < min (min δe δd) (min (δl / (Ce + 1)) (1 / (2 * (Cd + 1)))) := by
        have := Metric.mem_ball.mp ht; rwa [Real.dist_eq, sub_zero] at this
      have hte : |t| < δe := lt_of_lt_of_le htabs (le_trans (min_le_left _ _) (min_le_left _ _))
      have htd : |t| < δd := lt_of_lt_of_le htabs (le_trans (min_le_left _ _) (min_le_right _ _))
      have htl : |t| < δl / (Ce + 1) :=
        lt_of_lt_of_le htabs (le_trans (min_le_right _ _) (min_le_left _ _))
      have ht4 : |t| < 1 / (2 * (Cd + 1)) :=
        lt_of_lt_of_le htabs (le_trans (min_le_right _ _) (min_le_right _ _))
      have hent : ∀ j i : Fin m, |normCurve M t j i - (1 : Mx) j i| < δl := by
        intro j i
        have h1 := hentry t (le_of_lt hte) j i
        have h2 : Ce * |t| < δl := by
          have h5 : Ce * |t| ≤ (Ce + 1) * |t| :=
            mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg t)
          have h6 : (Ce + 1) * |t| < δl := by
            have := mul_lt_mul_of_pos_left htl (by linarith : (0:ℝ) < Ce + 1)
            rwa [mul_div_cancel₀ _ (by positivity : (Ce + 1) ≠ 0)] at this
          linarith
        linarith
      have hdetpos : 0 < (1 + t • M).det := by
        have h1 : |(1 + t • M).det - 1| ≤ Cd * t ^ 2 := hbd t (le_of_lt htd)
        have h2 : Cd * t ^ 2 ≤ Cd * (1 / (2 * (Cd + 1))) ^ 2 := by
          have htδ : t ^ 2 ≤ (1 / (2 * (Cd + 1))) ^ 2 := by
            have h := mul_self_le_mul_self (abs_nonneg t) (le_of_lt ht4)
            rwa [← sq, ← sq, sq_abs] at h
          exact mul_le_mul_of_nonneg_left htδ hCd0
        have := neg_le_of_abs_le (h1.trans (h2.trans h3))
        linarith
      have hdet1 : (normCurve M t).det = 1 := normCurve_det M hmnz t hdetpos
      have hshape : Submission.GaussianMeasure.gammaMass 1
            (VC (ℒ.map ((Submission.ShapeDeriv.mvec (normCurve M t)).restrictScalars ℤ)))
          = Submission.SameGrad.shapeG ℒ
              (Submission.ShapeDeriv.mvec (normCurve M t)) Submission.SameGrad.fGauss :=
        gammaMass_one_image_eq_shapeG ℒ (normCurve M t) (by rw [hdet1, abs_one])
      rw [shapeG_normCurve_zero ℒ M, ← hshape]
      exact hl (normCurve M t) (by rw [hdet1]; exact one_ne_zero) (by rw [hdet1, abs_one]) hent
    have hlocmin : IsLocalMin (fun t : ℝ => Submission.SameGrad.shapeG ℒ
        (Submission.ShapeDeriv.mvec (normCurve M t)) Submission.SameGrad.fGauss) 0 := hmin
    have hderiv := normCurve_shapeG_hasDerivAt r R hr hR0 hℒ hball hcell hlam hVfin M hmnz hM
    have hzero := hlocmin.hasDerivAt_eq_zero hderiv
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd h (by have := Real.pi_pos; nlinarith)
    · exact h
  -- symmetric matrix with this orthogonality
  set G : Mx := fun i j => Submission.ShapeDeriv.secondMoment (VC ℒ) i j with hG
  have hGsym : G.IsSymm := by
    rw [Matrix.IsSymm]
    ext i j
    rw [Matrix.transpose_apply]
    simp only [hG]
    unfold Submission.ShapeDeriv.secondMoment
    refine MeasureTheory.setIntegral_congr_fun (Submission.Voronoi.voronoi_measurable ℒ) ?_
    intro y _
    ring
  rcases Submission.ShapeDeriv.symm_of_orthogonal_to_trace_zero m hm G hGsym
      (fun M hMsym hMtr => horth M hMtr) with ⟨α, hα⟩
  refine ⟨α, ?_⟩
  intro i j
  have := congr_fun (congr_fun hα i) j
  simpa [hG, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero] using this


open Submission.QuotientLattice in
/-- Voronoi cell of a positive scalar multiple of a lattice. -/
lemma voronoi_smulLattice (c : ℝ) (hc : 0 < c) (Λ : Submodule ℤ E) :
    VC (smulLattice c Λ) = c • VC Λ := by
  ext x
  constructor
  · intro hx
    rw [Submission.Voronoi.mem_voronoi] at hx
    refine Set.mem_smul_set.mpr ⟨c⁻¹ • x, ?_, ?_⟩
    · rw [Submission.Voronoi.mem_voronoi]
      intro y
      have h1 := hx (⟨c • (y : E), (mem_smulLattice).mpr ⟨y, y.2, rfl⟩⟩ : smulLattice c Λ)
      simp only [Subtype.coe_mk] at h1
      rw [real_inner_smul_right] at h1
      have h3 : ‖c • (y : E)‖ ^ 2 = c ^ 2 * ‖(y : E)‖ ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      rw [h3] at h1
      have h5 : inner ℝ x (y : E) ≤ c * ‖(y : E)‖ ^ 2 / 2 := by
        have h4 : c * inner ℝ x (y : E) ≤ c * (c * ‖(y : E)‖ ^ 2 / 2) := by nlinarith [h1]
        nlinarith [h4, hc]
      rw [real_inner_smul_left]
      have h6 : c⁻¹ * inner ℝ x (y : E) ≤ c⁻¹ * (c * ‖(y : E)‖ ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left h5 (by positivity)
      have h7 : c⁻¹ * (c * ‖(y : E)‖ ^ 2 / 2) = ‖(y : E)‖ ^ 2 / 2 := by
        field_simp
      linarith [h6, h7]
    · exact smul_inv_smul₀ (ne_of_gt hc) x
  · intro hx
    rcases Set.mem_smul_set.mp hx with ⟨v, hv, hxv⟩
    rw [Submission.Voronoi.mem_voronoi] at hv ⊢
    intro y
    rcases (mem_smulLattice.mp y.2) with ⟨z, hz, hyz⟩
    rw [← hyz, ← hxv]
    have h1 := hv ⟨z, hz⟩
    rw [real_inner_smul_left, real_inner_smul_right]
    have h3 : ‖c • z‖ ^ 2 = c ^ 2 * ‖z‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [h3]
    nlinarith [h1]

open Submission.QuotientLattice in
/-- Scaling the parameter equals scaling the lattice. -/
lemma gammaMass_smulLattice (s : ℝ) (hs : 0 < s) (Λ : Submodule ℤ E) :
    Submission.GaussianMeasure.gammaMass s (VC Λ)
      = Submission.GaussianMeasure.gammaMass 1 (VC (smulLattice (1 / s) Λ)) := by
  have hc : (0:ℝ) < 1 / s := by positivity
  have hset : {y : E | s • y ∈ VC Λ} = (1 / s) • VC Λ := by
    ext x
    constructor
    · intro hx
      exact Set.mem_smul_set.mpr ⟨s • x, hx, by
        rw [smul_smul, one_div, inv_mul_cancel₀ (ne_of_gt hs), one_smul]⟩
    · intro hx
      rcases Set.mem_smul_set.mp hx with ⟨v, hv, hxv⟩
      have hthis : s • x = v := by
        rw [← hxv, smul_smul, one_div, mul_inv_cancel₀ (ne_of_gt hs), one_smul]
      show s • x ∈ VC Λ
      rw [hthis]
      exact hv
  rw [voronoi_smulLattice (1 / s) hc Λ, Submission.GaussianMeasure.gammaMass_one]
  unfold Submission.GaussianMeasure.gammaMass
  rw [hset]

open Submission.QuotientLattice in
/-- Scalar multiples commute with images of `ℝ`-linear maps. -/
lemma smulLattice_map (c : ℝ) (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] E) :
    smulLattice c (Λ.map (f.restrictScalars ℤ)) = (smulLattice c Λ).map (f.restrictScalars ℤ) := by
  ext x
  rw [mem_smulLattice, Submodule.mem_map]
  constructor
  · rintro ⟨y, ⟨z, hz, hyz⟩, hxy⟩
    refine ⟨c • z, (mem_smulLattice).mpr ⟨z, hz, rfl⟩, ?_⟩
    rw [← hxy, ← hyz]
    exact f.map_smul c z
  · rintro ⟨y, ⟨z, hz, hyz⟩, hxy⟩
    refine ⟨f z, ⟨z, hz, rfl⟩, ?_⟩
    rw [← hxy, ← hyz]
    exact (f.map_smul c z).symm

open Submission.QuotientLattice in
/-- `ℤ`-lattice property is preserved by nonzero scaling. -/
lemma isZLattice_smulLattice (c : ℝ) (hc : c ≠ 0) {Λ : Submodule ℤ E} [DiscreteTopology Λ]
    (hΛ : IsZLattice ℝ Λ) : IsZLattice ℝ (smulLattice c Λ) := by
  haveI : DiscreteTopology (smulLattice c Λ) := Submission.Filtration.discrete_smulLattice_inst c Λ
  refine ⟨?_⟩
  have hcoe : ((smulLattice c Λ : Submodule ℤ E) : Set E) = c • (Λ : Set E) := by
    ext x
    change x ∈ smulLattice c Λ ↔ x ∈ c • (Λ : Set E)
    rw [mem_smulLattice, Set.mem_smul_set]
    exact ⟨fun ⟨y, hy, hxy⟩ => ⟨y, hy, hxy⟩, fun ⟨y, hy, hxy⟩ => ⟨y, hy, hxy⟩⟩
  have himg : c • (Λ : Set E) = (smulMap c : E →ₗ[ℝ] E) '' (Λ : Set E) := by
    ext x
    exact ⟨fun ⟨y, hy, hxy⟩ => ⟨y, hy, hxy⟩, fun ⟨y, hy, hxy⟩ => ⟨y, hy, hxy⟩⟩
  have h2 : Submodule.span ℝ ((smulMap c : E →ₗ[ℝ] E) '' (Λ : Set E))
      = Submodule.map (smulMap c : E →ₗ[ℝ] E) (Submodule.span ℝ (Λ : Set E)) := by
    rw [Submodule.map_span]
  rw [hcoe, himg, h2, hΛ.span_top, Submodule.map_top, LinearMap.range_eq_top]
  intro y
  refine ⟨c⁻¹ • y, ?_⟩
  show c • (c⁻¹ • y) = y
  rw [smul_smul, mul_inv_cancel₀ hc, one_smul]

open Submission.QuotientLattice in
/-- **Isotropy from a local minimum at parameter `s`.** -/
theorem secondMoment_scalar_of_local_min_scaled
    {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    (s : ℝ) (hs : 0 < s)
    (r R : ℝ) (hr : 0 < r) (hR0 : 0 ≤ R)
    (hball : Metric.closedBall (0 : E) r ⊆ VC ℒ)
    (hcell : VC ℒ ⊆ Metric.closedBall (0 : E) R)
    (hlam : ∀ z : ℒ, z ≠ 0 → r ≤ ‖(z : E)‖)
    (hVfin : (volume : Measure E) (VC ℒ) ≠ ⊤)
    (hloc : ∃ δ : ℝ, 0 < δ ∧ ∀ A : Mx, A.det ≠ 0 → |A.det| = 1 →
      (∀ j i : Fin m, |A j i - (1 : Mx) j i| < δ) →
      Submission.GaussianMeasure.gammaMass s (VC ℒ) ≤
        Submission.GaussianMeasure.gammaMass s
          (VC (ℒ.map ((Submission.ShapeDeriv.mvec A).restrictScalars ℤ))))
    (hm : 2 ≤ m) :
    ∃ α : ℝ, ∀ i j : Fin m,
      Submission.ShapeDeriv.secondMoment (VC (smulLattice (1/s) ℒ)) i j
        = α * (if i = j then 1 else 0) := by
  classical
  set c : ℝ := 1 / s with hcdef
  have hcpos : 0 < c := by rw [hcdef]; positivity
  have hcne : c ≠ 0 := ne_of_gt hcpos
  letI : DiscreteTopology (smulLattice c ℒ) :=
    Submission.Filtration.discrete_smulLattice_inst c ℒ
  have h𝔏 : IsZLattice ℝ (smulLattice c ℒ) := isZLattice_smulLattice c hcne hℒ
  have hball' : Metric.closedBall (0 : E) (c * r) ⊆ VC (smulLattice c ℒ) := by
    rw [voronoi_smulLattice c hcpos ℒ]
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    refine Set.mem_smul_set.mpr ⟨c⁻¹ • x, hball ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      calc c⁻¹ * ‖x‖ ≤ c⁻¹ * (c * r) := mul_le_mul_of_nonneg_left hx (by positivity)
        _ = r := by rw [← mul_assoc, inv_mul_cancel₀ hcne, one_mul]
    · show c • (c⁻¹ • x) = x
      rw [smul_smul, mul_inv_cancel₀ hcne, one_smul]
  have hcell' : VC (smulLattice c ℒ) ⊆ Metric.closedBall (0 : E) (c * R) := by
    rw [voronoi_smulLattice c hcpos ℒ]
    rintro x ⟨y, hy, hxy⟩
    rw [← hxy]
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]
    have h := Metric.mem_closedBall.mp (hcell hy)
    rw [dist_zero_right] at h
    exact mul_le_mul_of_nonneg_left h (le_of_lt hcpos)
  have hlam' : ∀ z : smulLattice c ℒ, z ≠ 0 → c * r ≤ ‖(z : E)‖ := by
    intro z hz
    rcases (mem_smulLattice.mp z.2) with ⟨y, hy, hyz⟩
    have hy0 : (⟨y, hy⟩ : ℒ) ≠ 0 := by
      rintro h0
      apply hz
      apply Subtype.ext
      rw [← hyz]
      have h1 : y = 0 := by
        have := congrArg (fun w : ℒ => (w : E)) h0
        simpa using this
      rw [h1]
      simp
    rw [← hyz, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]
    exact mul_le_mul_of_nonneg_left (hlam ⟨y, hy⟩ hy0) (le_of_lt hcpos)
  have hVfin' : (volume : Measure E) (VC (smulLattice c ℒ)) ≠ ⊤ := by
    rw [voronoi_smulLattice c hcpos ℒ, Submission.EpsVoronoi.measure_smul]
    exact ne_of_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ((lt_top_iff_ne_top).mpr hVfin))
  have hloc' : ∃ δ : ℝ, 0 < δ ∧ ∀ A : Mx, A.det ≠ 0 → |A.det| = 1 →
      (∀ j i : Fin m, |A j i - (1 : Mx) j i| < δ) →
      Submission.GaussianMeasure.gammaMass 1 (VC (smulLattice c ℒ)) ≤
        Submission.GaussianMeasure.gammaMass 1
          (VC ((smulLattice c ℒ).map ((Submission.ShapeDeriv.mvec A).restrictScalars ℤ))) := by
    obtain ⟨δ, hδpos, hl⟩ := hloc
    refine ⟨δ, hδpos, ?_⟩
    intro A hA0 hA1 hAc
    have h1 := hl A hA0 hA1 hAc
    rw [gammaMass_smulLattice s hs ℒ,
        gammaMass_smulLattice s hs (ℒ.map ((Submission.ShapeDeriv.mvec A).restrictScalars ℤ)),
        smulLattice_map c ℒ (Submission.ShapeDeriv.mvec A)] at h1
    exact h1
  exact secondMoment_scalar_of_local_min h𝔏 (c * r) (c * R) (by positivity) (by positivity)
    hball' hcell' hlam' hVfin' hloc' hm

end PartC

end Submission.Isotropic
