import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

open MeasureTheory Metric Filter Function Set
open scoped Topology ContDiff

namespace Commons.Analysis.GaussianMeasure

/-!
# Mollified distance function

Auxiliary lemmas (Gaussian smoothing of the distance-to-a-set function, its Taylor
expansion, and bounds on the first Gaussian moment) used to construct a smooth
approximation of `Metric.infDist · E` whose derivative is bounded by `1`, which is
nonpositive on `E` and never smaller than `infDist · E - 2η`.
-/
namespace MollifierAux

noncomputable section

variable {n : ℕ}

lemma pow_mul_exp_neg_half_sq_le (t : ℝ) (ht : 0 ≤ t) (k : ℕ) :
    t ^ k * Real.exp (-(t^2)/2) ≤ 4 ^ k * (k.factorial : ℝ) := by
  have hexp_le : Real.exp (-(t^2)/2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg t]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using hexp_le
  set m : ℕ := (k + 1) / 2 with hm
  have hkm : k ≤ 2 * m := by omega
  have hmk : m ≤ k := by omega
  have ht_le : t ^ k ≤ 1 + t ^ (2 * m) := by
    rcases le_or_gt t 1 with h | h
    · have h1 : t ^ k ≤ 1 := pow_le_one₀ ht h
      have h2 : (0:ℝ) ≤ t ^ (2*m) := pow_nonneg ht _
      linarith
    · have h2 : t ^ k ≤ t ^ (2*m) := pow_le_pow_right₀ h.le hkm
      have h3 : (1:ℝ) ≤ t^(2*m) := one_le_pow₀ h.le
      linarith
  have h2m_pos : (0:ℝ) < (m.factorial : ℝ) := by positivity
  have hmom : t ^ (2*m) * Real.exp (-(t^2)/2) ≤ 2 ^ m * (m.factorial : ℝ) := by
    have hx : 0 ≤ t^2/2 := by positivity
    have h2 := Real.pow_div_factorial_le_exp (t^2/2) hx m
    rw [div_le_iff₀ h2m_pos] at h2
    have h4 : t ^ (2*m) = 2^m * (t^2/2)^m := by
      calc t ^ (2*m) = (t^2)^m := by rw [pow_mul]
        _ = (2 * (t^2/2))^m := by congr 1; ring
        _ = 2^m * (t^2/2)^m := by rw [mul_pow]
    have hinv : Real.exp (-(t^2)/2) = (Real.exp (t^2/2))⁻¹ := by
      rw [← Real.exp_neg]; congr 1; ring
    rw [h4, hinv]
    calc 2^m * (t^2/2)^m * (Real.exp (t^2/2))⁻¹
        = 2^m * ((t^2/2)^m * (Real.exp (t^2/2))⁻¹) := by ring
      _ ≤ 2^m * ((Real.exp (t^2/2) * (m.factorial:ℝ)) * (Real.exp (t^2/2))⁻¹) := by
          gcongr
      _ = 2^m * (m.factorial:ℝ) := by
          rw [mul_comm (Real.exp (t^2/2)) (m.factorial:ℝ), mul_assoc,
            mul_inv_cancel₀ (Real.exp_ne_zero _), mul_one]
  have hsum : t ^ k * Real.exp (-(t^2)/2) ≤ Real.exp (-(t^2)/2) + 2^m * (m.factorial : ℝ) := by
    have h := mul_le_mul_of_nonneg_right ht_le (Real.exp_pos (-(t^2)/2)).le
    rw [add_mul, one_mul] at h
    linarith [h, hmom]
  have hfac : (m.factorial : ℝ) ≤ (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_le hmk
  have h2m : (2:ℝ)^m ≤ 2^k := pow_le_pow_right₀ (by norm_num) hmk
  have hkfac : (1:ℝ) ≤ (k.factorial : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)
  have h4k : (4:ℝ)^k = 2^k * 2^k := by
    rw [show (4:ℝ) = 2*2 by norm_num, mul_pow]
  have hmain : (1:ℝ) + 2^k ≤ 4^k := by
    rw [h4k]
    have h2k2 : (2:ℝ) ≤ 2^k := by
      calc (2:ℝ) = 2^1 := by norm_num
        _ ≤ 2^k := pow_le_pow_right₀ (by norm_num) hk
    nlinarith [h2k2]
  have hfin : Real.exp (-(t^2)/2) + 2^m * (m.factorial : ℝ) ≤ 4 ^ k * (k.factorial : ℝ) := by
    have h1 : Real.exp (-(t^2)/2) + 2^m * (m.factorial : ℝ)
        ≤ (k.factorial:ℝ) * (1 + 2^k) := by
      have h1' : Real.exp (-(t^2)/2) ≤ (k.factorial:ℝ) := le_trans hexp_le hkfac
      have h2' : 2^m * (m.factorial : ℝ) ≤ 2^k * (k.factorial : ℝ) :=
        mul_le_mul h2m hfac (Nat.cast_nonneg m.factorial) (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) k)
      calc Real.exp (-(t^2)/2) + 2^m * (m.factorial : ℝ)
          ≤ (k.factorial:ℝ) + 2^k * (k.factorial:ℝ) := add_le_add h1' h2'
        _ = (k.factorial:ℝ) * (1 + 2^k) := by ring
    have h2'' : (k.factorial:ℝ) * (1 + 2^k) ≤ (k.factorial:ℝ) * 4^k :=
      mul_le_mul_of_nonneg_left hmain (Nat.cast_nonneg _)
    have h3'' : (k.factorial:ℝ) * 4^k = 4^k * (k.factorial:ℝ) := by ring
    linarith
  exact hsum.trans hfin

/-- One-dimensional Gaussian weight bound with variance `σ ^ 2`. -/
lemma one_dim_gauss_bound (σ : ℝ) (hσ : 0 < σ) (k : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    t ^ k * Real.exp (-(t^2)/(2*σ^2)) ≤
      (4 * Real.sqrt 2 * σ)^k * (k.factorial:ℝ) * Real.exp (-(t^2)/(4*σ^2)) := by
  have hσne : σ ≠ 0 := ne_of_gt hσ
  set s : ℝ := t/σ with hs
  have hs0 : 0 ≤ s := by positivity
  have ht_eq : t = s * σ := by rw [hs]; field_simp
  have hkey : s ^ k * Real.exp (-(s^2)/4) ≤ (4*Real.sqrt 2)^k * (k.factorial:ℝ) := by
    have h := pow_mul_exp_neg_half_sq_le (s/Real.sqrt 2) (by positivity) k
    have h1 : Real.exp (-((s/Real.sqrt 2)^2)/2) = Real.exp (-(s^2)/4) := by
      congr 1
      rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      ring
    have h2 : (s/Real.sqrt 2)^k = s^k / (Real.sqrt 2)^k := by rw [div_pow]
    rw [h2, h1] at h
    have hsp : (0:ℝ) < (Real.sqrt 2)^k := by positivity
    have h3 : s ^ k * Real.exp (-(s^2)/4) * ((Real.sqrt 2)^k)⁻¹ ≤ 4^k * (k.factorial:ℝ) := by
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h
    have h4 : s ^ k * Real.exp (-(s^2)/4) ≤ 4^k * (k.factorial:ℝ) * (Real.sqrt 2)^k := by
      have h5 := mul_le_mul_of_nonneg_right h3 hsp.le
      simpa [mul_assoc, inv_mul_cancel₀ hsp.ne', mul_one] using h5
    calc s ^ k * Real.exp (-(s^2)/4) ≤ 4^k * (k.factorial:ℝ) * (Real.sqrt 2)^k := h4
      _ = (4*Real.sqrt 2)^k * (k.factorial:ℝ) := by rw [mul_pow]; ring
  rw [ht_eq]
  have e1 : (s*σ)^k = (s^k) * (σ^k) := by rw [mul_pow]
  have e2 : -((s*σ)^2)/(2*σ^2) = -(s^2)/2 := by field_simp
  have e3 : -((s*σ)^2)/(4*σ^2) = -(s^2)/4 := by field_simp
  rw [e1, e2, e3]
  have e4 : Real.exp (-(s^2)/2) = Real.exp (-(s^2)/4) * Real.exp (-(s^2)/4) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e4]
  calc s^k * σ^k * (Real.exp (-(s^2)/4) * Real.exp (-(s^2)/4))
      = (s^k * Real.exp (-(s^2)/4)) * (σ^k * Real.exp (-(s^2)/4)) := by ring
    _ ≤ ((4*Real.sqrt 2)^k * (k.factorial:ℝ)) * (σ^k * Real.exp (-(s^2)/4)) :=
        mul_le_mul_of_nonneg_right hkey (by positivity)
    _ = (4*Real.sqrt 2*σ)^k * (k.factorial:ℝ) * Real.exp (-(s^2)/4) := by
        rw [mul_pow]; ring


/-- The Gaussian integral on `EuclideanSpace ℝ (Fin n)`. -/
lemma integral_gauss (σ : ℝ) (hσ : 0 < σ) :
    ∫ w : EuclideanSpace ℝ (Fin n), Real.exp (-‖w‖^2/(4*σ^2)) = (4*Real.pi*σ^2)^((n:ℝ)/2) := by
  have hb : 0 < 1/(4*σ^2) := by positivity
  have hval := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := EuclideanSpace ℝ (Fin n)) hb
  rw [finrank_euclideanSpace_fin] at hval
  have harg : ∀ w : EuclideanSpace ℝ (Fin n), Real.exp (-(1/(4*σ^2))*‖w‖^2) =
      Real.exp (-‖w‖^2/(4*σ^2)) := by
    intro w; congr 1; field_simp
  rw [show (∫ w : EuclideanSpace ℝ (Fin n), Real.exp (-(1/(4*σ^2))*‖w‖^2))
      = ∫ w, Real.exp (-‖w‖^2/(4*σ^2)) from by
        apply integral_congr_ae; filter_upwards with w; exact harg w] at hval
  rw [hval]
  congr 2
  field_simp

lemma integrable_gauss (σ : ℝ) (hσ : 0 < σ) :
    Integrable (fun w : EuclideanSpace ℝ (Fin n) => Real.exp (-‖w‖^2/(4*σ^2))) volume := by
  by_contra h
  have hval := integral_gauss (n := n) σ hσ
  rw [integral_undef h] at hval
  have hpos : (0:ℝ) < (4*Real.pi*σ^2)^((n:ℝ)/2) :=
    Real.rpow_pos_of_pos (by positivity) _
  linarith

/-- The moment bound for the Gaussian weight. -/
lemma gauss_moment_le (σ : ℝ) (hσ : 0 < σ) (k : ℕ) :
    ∫ w : EuclideanSpace ℝ (Fin n), ‖w‖^k * Real.exp (-‖w‖^2/(2*σ^2)) ≤
      (4*Real.sqrt 2*σ)^k * (k.factorial:ℝ) * (4*Real.pi*σ^2)^((n:ℝ)/2) := by
  have hpt : ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖^k * Real.exp (-‖w‖^2/(2*σ^2)) ≤
      (4*Real.sqrt 2*σ)^k * (k.factorial:ℝ) * Real.exp (-‖w‖^2/(4*σ^2)) := by
    intro w
    have h := one_dim_gauss_bound σ hσ k ‖w‖ (norm_nonneg w)
    simpa using h
  have hint : Integrable (fun w : EuclideanSpace ℝ (Fin n) =>
      ‖w‖^k * Real.exp (-‖w‖^2/(2*σ^2))) volume := by
    refine Integrable.mono' ((integrable_gauss (n := n) σ hσ).const_mul ((4*Real.sqrt 2*σ)^k * (k.factorial:ℝ))) ?_ ?_
    · apply Continuous.aestronglyMeasurable
      fun_prop
    · filter_upwards with w
      rw [Real.norm_of_nonneg (by positivity)]
      exact hpt w
  have hgint : Integrable (fun w : EuclideanSpace ℝ (Fin n) =>
      (4*Real.sqrt 2*σ)^k * (k.factorial:ℝ) * Real.exp (-‖w‖^2/(4*σ^2))) volume :=
    (integrable_gauss (n := n) σ hσ).const_mul ((4*Real.sqrt 2*σ)^k * (k.factorial:ℝ))
  calc ∫ w, ‖w‖^k * Real.exp (-‖w‖^2/(2*σ^2))
      ≤ ∫ w, (4*Real.sqrt 2*σ)^k * (k.factorial:ℝ) * Real.exp (-‖w‖^2/(4*σ^2)) :=
        integral_mono hint hgint hpt
    _ = (4*Real.sqrt 2*σ)^k * (k.factorial:ℝ) * (4*Real.pi*σ^2)^((n:ℝ)/2) := by
        rw [integral_const_mul, integral_gauss σ hσ]


/-- The `k`-linear form `v ↦ ∏ᵢ ⟪z, vᵢ⟫ / σ²` on `EuclideanSpace ℝ (Fin d)`. -/
def gaussML (σ : ℝ) (d k : ℕ) (z : EuclideanSpace ℝ (Fin d)) :
    ContinuousMultilinearMap ℝ (fun _ : Fin k => EuclideanSpace ℝ (Fin d)) ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebraFin ℝ k ℝ).compContinuousLinearMap
    (fun _ : Fin k => (σ ^ 2)⁻¹ • innerSL ℝ z)

lemma gaussML_apply (σ : ℝ) (d k : ℕ) (z : EuclideanSpace ℝ (Fin d))
    (v : Fin k → EuclideanSpace ℝ (Fin d)) :
    gaussML σ d k z v = ∏ i : Fin k, ((σ^2)⁻¹ * inner ℝ z (v i)) := by
  simp only [gaussML, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.prod_ofFn]
  apply Finset.prod_congr rfl
  intro i _
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul, innerSL_apply_apply]

lemma gaussML_diag (σ : ℝ) (d k : ℕ) (z h : EuclideanSpace ℝ (Fin d)) :
    gaussML σ d k z (fun _ : Fin k => h) = ((σ^2)⁻¹ * inner ℝ z h)^k := by
  rw [gaussML_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma norm_innerSL (d : ℕ) (z : EuclideanSpace ℝ (Fin d)) : ‖innerSL ℝ z‖ = ‖z‖ := by
  simpa using LinearIsometry.norm_map (InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ (Fin d))) z

lemma norm_gaussML_le (σ : ℝ) (d k : ℕ) (z : EuclideanSpace ℝ (Fin d)) :
    ‖gaussML σ d k z‖ ≤ (‖z‖ / σ^2)^k := by
  have h1 : ‖gaussML σ d k z‖ ≤ ‖ContinuousMultilinearMap.mkPiAlgebraFin ℝ k ℝ‖ *
      ∏ _i : Fin k, ‖(σ^2)⁻¹ • innerSL ℝ z‖ :=
    ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
  rw [ContinuousMultilinearMap.norm_mkPiAlgebraFin] at h1
  have h2 : ∏ _i : Fin k, ‖(σ^2)⁻¹ • innerSL ℝ z‖ = ‖(σ^2)⁻¹ • innerSL ℝ z‖^k := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [h2, one_mul] at h1
  refine h1.trans (pow_le_pow_left₀ (norm_nonneg _) ?_ k)
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (sq_nonneg σ), norm_innerSL]
  rw [div_eq_inv_mul]

lemma continuous_gaussML (σ : ℝ) (d k : ℕ) :
    Continuous (fun z : EuclideanSpace ℝ (Fin d) => gaussML σ d k z) := by
  have h0 : Continuous (fun z : EuclideanSpace ℝ (Fin d) => innerSL ℝ z) :=
    (InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ (Fin d))).continuous
  have h1 : Continuous (fun z : EuclideanSpace ℝ (Fin d) => fun _ : Fin k => (σ^2)⁻¹ • innerSL ℝ z) := by
    apply continuous_pi
    intro i
    exact h0.const_smul ((σ^2)⁻¹)
  have h2 : Continuous (fun f : Fin k → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) =>
      (ContinuousMultilinearMap.compContinuousLinearMapLRight
        (𝕜 := ℝ) (E := fun _ : Fin k => EuclideanSpace ℝ (Fin d)) (E₁ := fun _ : Fin k => ℝ)
        (G := ℝ) (ContinuousMultilinearMap.mkPiAlgebraFin ℝ k ℝ)) f) :=
    (ContinuousMultilinearMap.compContinuousLinearMapLRight
      (𝕜 := ℝ) (E := fun _ : Fin k => EuclideanSpace ℝ (Fin d)) (E₁ := fun _ : Fin k => ℝ)
      (G := ℝ) (ContinuousMultilinearMap.mkPiAlgebraFin ℝ k ℝ)).cont
  exact h2.comp h1

/-- The power series coefficients of the Gaussian transform. -/
def gaussCoeff (σ : ℝ) (g : EuclideanSpace ℝ (Fin n) → ℝ) (k : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin k => EuclideanSpace ℝ (Fin n)) ℝ :=
  ∫ z, (g z * Real.exp (-‖z‖^2/(2*σ^2)) * ((k.factorial:ℝ))⁻¹) • gaussML σ n k z

/-- The Laplace-type transform `h ↦ ∫ z, g z * exp (-‖z‖²/2σ²) * exp (⟪z,h⟫/σ²)`. -/
def gaussTransform (σ : ℝ) (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (h : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ z, g z * Real.exp (-‖z‖^2/(2*σ^2)) * Real.exp (inner ℝ z h / σ^2)


lemma one_add_pow_gauss_le (σ : ℝ) (hσ : 0 < σ) (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (1 + t)^m * Real.exp (-t^2/(2*σ^2)) ≤
      2^m * (1 + (8*σ)^m * (m.factorial:ℝ)) * Real.exp (-t^2/(4*σ^2)) := by
  have hA : t^m * Real.exp (-t^2/(4*σ^2)) ≤ (8*σ)^m * (m.factorial:ℝ) := by
    have hs : 0 < σ * Real.sqrt 2 := by positivity
    have h := one_dim_gauss_bound (σ * Real.sqrt 2) hs m t ht
    have h1 : -(t^2)/(2*(σ*Real.sqrt 2)^2) = -t^2/(4*σ^2) := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; ring
    have h2 : 4*Real.sqrt 2*(σ*Real.sqrt 2) = 8*σ := by
      have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
      calc 4*Real.sqrt 2*(σ*Real.sqrt 2) = 4*σ*(Real.sqrt 2*Real.sqrt 2) := by ring
        _ = 8*σ := by rw [hs2]; ring
    have h3 : -(t^2)/(4*(σ*Real.sqrt 2)^2) = -t^2/(8*σ^2) := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; ring
    rw [h1, h2, h3] at h
    have hexp1 : Real.exp (-t^2/(8*σ^2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg t)) (by positivity)
    calc t^m * Real.exp (-t^2/(4*σ^2)) ≤ (8*σ)^m * (m.factorial:ℝ) * 1 := by
          exact h.trans (mul_le_mul_of_nonneg_left hexp1 (by positivity))
      _ = (8*σ)^m * (m.factorial:ℝ) := by ring
  have h2 : (1+t)^m ≤ 2^m * (1 + t^m) := by
    have hle : (1+t) ≤ 2 * max 1 t := by
      rcases le_or_gt t 1 with h' | h'
      · rw [max_eq_left h']; linarith
      · rw [max_eq_right h'.le]; linarith
    calc (1+t)^m ≤ (2*max 1 t)^m := pow_le_pow_left₀ (by linarith) hle m
      _ = 2^m * (max 1 t)^m := by rw [mul_pow]
      _ ≤ 2^m * (1 + t^m) := by
          gcongr
          rcases le_or_gt t 1 with h' | h'
          · rw [max_eq_left h', one_pow]; exact le_add_of_nonneg_right (pow_nonneg ht m)
          · rw [max_eq_right h'.le]
            exact le_add_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1)
  have hexp4 : 0 < Real.exp (-t^2/(4*σ^2)) := Real.exp_pos _
  have hmain : (1 + t^m) * Real.exp (-t^2/(4*σ^2)) ≤ 1 + (8*σ)^m * (m.factorial:ℝ) := by
    have h1 : Real.exp (-t^2/(4*σ^2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg t)) (by positivity)
    have hgoal : (1 + t^m) * Real.exp (-t^2/(4*σ^2))
        = Real.exp (-t^2/(4*σ^2)) + t^m * Real.exp (-t^2/(4*σ^2)) := by ring
    rw [hgoal]
    linarith
  have h3 : 0 < (2:ℝ)^m := by positivity
  calc (1+t)^m * Real.exp (-t^2/(2*σ^2))
      ≤ 2^m * (1 + t^m) * Real.exp (-t^2/(2*σ^2)) := by
        apply mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = 2^m * ((1 + t^m) * Real.exp (-t^2/(4*σ^2))) * Real.exp (-t^2/(4*σ^2)) := by
        rw [show Real.exp (-t^2/(2*σ^2)) =
          Real.exp (-t^2/(4*σ^2)) * Real.exp (-t^2/(4*σ^2)) by
            rw [← Real.exp_add]; congr 1; ring]
        ring
    _ ≤ 2^m * (1 + (8*σ)^m * (m.factorial:ℝ)) * Real.exp (-t^2/(4*σ^2)) := by
        apply mul_le_mul_of_nonneg_right _ hexp4.le
        apply mul_le_mul_of_nonneg_left hmain h3.le

lemma integrable_one_add_pow_gauss (σ : ℝ) (hσ : 0 < σ) (m : ℕ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
      (1 + ‖z‖)^m * Real.exp (-‖z‖^2/(2*σ^2))) volume := by
  refine Integrable.mono' ((integrable_gauss (n := n) σ hσ).const_mul
    (2^m * (1 + (8*σ)^m * (m.factorial:ℝ)))) ?_ ?_
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · filter_upwards with z
    rw [Real.norm_of_nonneg (by positivity)]
    exact one_add_pow_gauss_le σ hσ m ‖z‖ (norm_nonneg z)


/-- Pointwise bound for the integrand defining `gaussCoeff`. -/
lemma norm_gaussCoeff_integrand_le (σ : ℝ) (hσ : 0 < σ) (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (C : ℝ) (hg : ∀ z, |g z| ≤ C * (1 + ‖z‖)) (k : ℕ) (z : EuclideanSpace ℝ (Fin n)) :
    ‖(g z * Real.exp (-‖z‖^2/(2*σ^2)) * ((k.factorial:ℝ))⁻¹) • gaussML σ n k z‖ ≤
      (|C| * (2:ℝ)^(k+1) * (1 + (8*σ)^(k+1) * ((k+1).factorial:ℝ)) /
        ((k.factorial:ℝ) * σ^(2*k))) * Real.exp (-‖z‖^2/(4*σ^2)) := by
  have hk : (0:ℝ) < (k.factorial:ℝ) := by positivity
  have hσ2 : (0:ℝ) < σ^(2*k) := by positivity
  have h1 : ‖(g z * Real.exp (-‖z‖^2/(2*σ^2)) * ((k.factorial:ℝ))⁻¹) • gaussML σ n k z‖
      = |g z| * Real.exp (-‖z‖^2/(2*σ^2)) * ((k.factorial:ℝ))⁻¹ * ‖gaussML σ n k z‖ := by
    simp only [norm_smul, Real.norm_eq_abs, abs_mul, abs_inv, abs_of_nonneg (Real.exp_nonneg _),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (k.factorial:ℝ))]
  rw [h1]
  have h2 := norm_gaussML_le σ n k z
  have h3 := hg z
  have hexp_pos : 0 < Real.exp (-‖z‖^2/(2*σ^2)) := Real.exp_pos _
  have h4 : ‖gaussML σ n k z‖ ≤ (1 + ‖z‖)^k / σ^(2*k) := by
    refine h2.trans ?_
    rw [div_pow, show (σ^2)^k = σ^(2*k) by rw [← pow_mul]]
    apply div_le_div_of_nonneg_right _ (by positivity : (0:ℝ) ≤ σ^(2*k))
    exact pow_le_pow_left₀ (norm_nonneg z) (le_add_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1)) k
  have h5 : |g z| * Real.exp (-‖z‖^2/(2*σ^2)) * ((k.factorial:ℝ))⁻¹ * ‖gaussML σ n k z‖
      ≤ |C| * (1 + ‖z‖)^(k+1) * Real.exp (-‖z‖^2/(2*σ^2)) * ((k.factorial:ℝ))⁻¹ * σ⁻¹^(2*k) := by
    have hC1 : |g z| ≤ |C| * (1 + ‖z‖) := by
      calc |g z| ≤ C * (1 + ‖z‖) := h3
        _ ≤ |C| * (1 + ‖z‖) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact le_abs_self C
    have h6 : ‖gaussML σ n k z‖ ≤ σ⁻¹^(2*k) * (1 + ‖z‖)^k := by
      rw [inv_pow, ← div_eq_inv_mul]
      exact h4
    have h7 : |g z| * ((k.factorial:ℝ))⁻¹ * ‖gaussML σ n k z‖
        ≤ |C| * (1 + ‖z‖) * ((k.factorial:ℝ))⁻¹ * (σ⁻¹^(2*k) * (1 + ‖z‖)^k) := by
      gcongr
    calc |g z| * Real.exp (-‖z‖^2/(2*σ^2)) * ((k.factorial:ℝ))⁻¹ * ‖gaussML σ n k z‖
        = (|g z| * ((k.factorial:ℝ))⁻¹ * ‖gaussML σ n k z‖) * Real.exp (-‖z‖^2/(2*σ^2)) := by ring
      _ ≤ (|C| * (1 + ‖z‖) * ((k.factorial:ℝ))⁻¹ * (σ⁻¹^(2*k) * (1 + ‖z‖)^k)) *
            Real.exp (-‖z‖^2/(2*σ^2)) := by
          apply mul_le_mul_of_nonneg_right h7 (Real.exp_nonneg _)
      _ = |C| * (1 + ‖z‖)^(k+1) * Real.exp (-‖z‖^2/(2*σ^2)) * ((k.factorial:ℝ))⁻¹ * σ⁻¹^(2*k) := by
          ring
  have hfin : |C| * (1 + ‖z‖)^(k+1) * Real.exp (-‖z‖^2/(2*σ^2)) * ((k.factorial:ℝ))⁻¹ * σ⁻¹^(2*k)
      ≤ (|C| * (2:ℝ)^(k+1) * (1 + (8*σ)^(k+1) * ((k+1).factorial:ℝ)) /
        ((k.factorial:ℝ) * σ^(2*k))) * Real.exp (-‖z‖^2/(4*σ^2)) := by
    have hA := one_add_pow_gauss_le σ hσ (k+1) ‖z‖ (norm_nonneg z)
    have h8 : (|C| * (1 + ‖z‖)^(k+1) * Real.exp (-‖z‖^2/(2*σ^2)) * ((k.factorial:ℝ))⁻¹ * σ⁻¹^(2*k))
        = (|C| * ((k.factorial:ℝ))⁻¹ * σ⁻¹^(2*k)) * ((1 + ‖z‖)^(k+1) * Real.exp (-‖z‖^2/(2*σ^2))) := by
      ring
    rw [h8]
    have h9 : (0:ℝ) ≤ |C| * ((k.factorial:ℝ))⁻¹ * σ⁻¹^(2*k) := by positivity
    calc (|C| * ((k.factorial:ℝ))⁻¹ * σ⁻¹^(2*k)) * ((1 + ‖z‖)^(k+1) * Real.exp (-‖z‖^2/(2*σ^2)))
        ≤ (|C| * ((k.factorial:ℝ))⁻¹ * σ⁻¹^(2*k)) *
            ((2:ℝ)^(k+1) * (1 + (8*σ)^(k+1) * ((k+1).factorial:ℝ)) * Real.exp (-‖z‖^2/(4*σ^2))) := by
          apply mul_le_mul_of_nonneg_left hA h9
      _ = (|C| * (2:ℝ)^(k+1) * (1 + (8*σ)^(k+1) * ((k+1).factorial:ℝ)) /
        ((k.factorial:ℝ) * σ^(2*k))) * Real.exp (-‖z‖^2/(4*σ^2)) := by
          rw [show (σ⁻¹:ℝ)^(2*k) = (σ^(2*k))⁻¹ by rw [inv_pow]]
          field_simp
  exact h5.trans hfin

/-- Integrability of the integrand defining `gaussCoeff`. -/
lemma integrable_gaussCoeff_integrand (σ : ℝ) (hσ : 0 < σ)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg_cont : Continuous g) (C : ℝ)
    (hg : ∀ z, |g z| ≤ C * (1 + ‖z‖)) (k : ℕ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
      (g z * Real.exp (-‖z‖^2/(2*σ^2)) * ((k.factorial:ℝ))⁻¹) • gaussML σ n k z) volume := by
  refine Integrable.mono' ((integrable_gauss (n := n) σ hσ).const_mul
    (|C| * (2:ℝ)^(k+1) * (1 + (8*σ)^(k+1) * ((k+1).factorial:ℝ)) /
      ((k.factorial:ℝ) * σ^(2*k)))) ?_ ?_
  · apply Continuous.aestronglyMeasurable
    exact (by fun_prop : Continuous (fun z : EuclideanSpace ℝ (Fin n) =>
      g z * Real.exp (-‖z‖^2/(2*σ^2)) * ((k.factorial:ℝ))⁻¹)).smul (continuous_gaussML σ n k)
  · filter_upwards with z
    exact norm_gaussCoeff_integrand_le σ hσ g C hg k z


/-- Integral bound for the coefficient integrand. -/
lemma integral_norm_gaussCoeff_integrand_le (σ : ℝ) (hσ : 0 < σ) (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg_cont : Continuous g) (C : ℝ) (hg : ∀ z, |g z| ≤ C * (1 + ‖z‖)) (k : ℕ) :
    ∫ z : EuclideanSpace ℝ (Fin n), ‖(g z * Real.exp (-‖z‖^2/(2*σ^2)) * ((k.factorial:ℝ))⁻¹) •
        gaussML σ n k z‖ ≤
      (|C| * (2:ℝ)^(k+1) * (1 + (8*σ)^(k+1) * ((k+1).factorial:ℝ)) /
        ((k.factorial:ℝ) * σ^(2*k))) * (4*Real.pi*σ^2)^((n:ℝ)/2) := by
  have hpt := norm_gaussCoeff_integrand_le σ hσ g C hg k
  have h1 := integrable_gaussCoeff_integrand σ hσ g hg_cont C hg k
  calc ∫ z, ‖(g z * Real.exp (-‖z‖^2/(2*σ^2)) * ((k.factorial:ℝ))⁻¹) • gaussML σ n k z‖
      ≤ ∫ z, (|C| * (2:ℝ)^(k+1) * (1 + (8*σ)^(k+1) * ((k+1).factorial:ℝ)) /
        ((k.factorial:ℝ) * σ^(2*k))) * Real.exp (-‖z‖^2/(4*σ^2)) :=
        integral_mono h1.norm ((integrable_gauss (n := n) σ hσ).const_mul
          (|C| * (2:ℝ)^(k+1) * (1 + (8*σ)^(k+1) * ((k+1).factorial:ℝ)) /
            ((k.factorial:ℝ) * σ^(2*k)))) hpt
    _ = (|C| * (2:ℝ)^(k+1) * (1 + (8*σ)^(k+1) * ((k+1).factorial:ℝ)) /
        ((k.factorial:ℝ) * σ^(2*k))) * (4*Real.pi*σ^2)^((n:ℝ)/2) := by
        rw [integral_const_mul, integral_gauss σ hσ]


lemma gaussCoeff_term_le (σ : ℝ) (hσ : 0 < σ) (C H : ℝ) (k : ℕ) :
    (|C| * (2:ℝ)^(k+1) * (1 + (8*σ)^(k+1) * ((k+1).factorial:ℝ)) /
        ((k.factorial:ℝ) * σ^(2*k))) * H^k ≤
      |C| * (2 * (2*H/σ^2)^k / (k.factorial:ℝ) + 16*σ*(k+1)*(16*H/σ)^k) := by
  have hk : (0:ℝ) < (k.factorial:ℝ) := by positivity
  have hfac : ((k+1).factorial : ℝ) = (k+1) * (k.factorial:ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hA' : (2:ℝ)^(k+1) / ((k.factorial:ℝ) * σ^(2*k)) * H^k
      = 2 * (2*H/σ^2)^k / (k.factorial:ℝ) := by
    rw [show (2:ℝ)^(k+1) = 2 * 2^k by rw [pow_succ]; ring, div_pow, mul_pow]
    rw [show (σ:ℝ)^(2*k) = (σ^2)^k by rw [pow_mul]]
    field_simp
  have hB' : (2:ℝ)^(k+1) * (8*σ)^(k+1) * (k+1) / σ^(2*k) * H^k
      = 16*σ*(k+1)*(16*H/σ)^k := by
    have h1 : (2:ℝ)^(k+1) * (8*σ)^(k+1) = (16*σ)^(k+1) := by rw [← mul_pow]; ring_nf
    rw [h1, show (σ:ℝ)^(2*k) = (σ^2)^k by rw [pow_mul]]
    rw [div_pow, mul_pow]
    field_simp
    ring
  have hsplit : (|C| * (2:ℝ)^(k+1) * (1 + (8*σ)^(k+1) * ((k+1).factorial:ℝ)) /
        ((k.factorial:ℝ) * σ^(2*k))) * H^k
      = |C| * ((2:ℝ)^(k+1) / ((k.factorial:ℝ) * σ^(2*k)) * H^k) +
        |C| * ((2:ℝ)^(k+1) * (8*σ)^(k+1) * (k+1) / σ^(2*k) * H^k) := by
    rw [hfac]
    field_simp
  rw [hsplit, hA', hB']
  exact le_of_eq (by ring)

/-- Norm bound for the coefficients of the Gaussian transform. -/
lemma norm_gaussCoeff_le (σ : ℝ) (hσ : 0 < σ) (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg_cont : Continuous g) (C : ℝ) (hg : ∀ z, |g z| ≤ C * (1 + ‖z‖)) (k : ℕ) :
    ‖gaussCoeff σ g k‖ ≤ (|C| * (2:ℝ)^(k+1) * (1 + (8*σ)^(k+1) * ((k+1).factorial:ℝ)) /
        ((k.factorial:ℝ) * σ^(2*k))) * (4*Real.pi*σ^2)^((n:ℝ)/2) :=
  (norm_integral_le_integral_norm _).trans
    (integral_norm_gaussCoeff_integrand_le σ hσ g hg_cont C hg k)

/-- Evaluation of the coefficients on the diagonal. -/
lemma gaussCoeff_apply_diag (σ : ℝ) (hσ : 0 < σ) (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg_cont : Continuous g) (C : ℝ) (hg : ∀ z, |g z| ≤ C * (1 + ‖z‖)) (k : ℕ)
    (h : EuclideanSpace ℝ (Fin n)) :
    gaussCoeff σ g k (fun _ : Fin k => h) =
      ∫ z, g z * Real.exp (-‖z‖^2/(2*σ^2)) * ((k.factorial:ℝ))⁻¹ *
        ((σ^2)⁻¹ * inner ℝ z h)^k := by
  have hint := integrable_gaussCoeff_integrand σ hσ g hg_cont C hg k
  rw [gaussCoeff, ContinuousMultilinearMap.integral_apply hint]
  apply integral_congr_ae
  filter_upwards with z
  rw [ContinuousMultilinearMap.smul_apply, smul_eq_mul, gaussML_diag]

/-- The `HasSum` statement for the power series of the Gaussian transform. -/
lemma hasSum_gaussCoeff (σ : ℝ) (hσ : 0 < σ) (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg_cont : Continuous g) (C : ℝ) (hg : ∀ z, |g z| ≤ C * (1 + ‖z‖)) {h : EuclideanSpace ℝ (Fin n)}
    (hh : ‖h‖ < σ/16) :
    HasSum (fun k => gaussCoeff σ g k (fun _ : Fin k => h)) (gaussTransform σ g h) := by
  set F : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun k z =>
    g z * Real.exp (-‖z‖^2/(2*σ^2)) * ((k.factorial:ℝ))⁻¹ * ((σ^2)⁻¹ * inner ℝ z h)^k with hF
  have hFint : ∀ k, Integrable (F k) volume := by
    intro k
    have h1 : ∀ z, ‖F k z‖ ≤ ‖(g z * Real.exp (-‖z‖^2/(2*σ^2)) * ((k.factorial:ℝ))⁻¹) •
        gaussML σ n k z‖ * ‖h‖^k := by
      intro z
      have h2 : F k z = ((g z * Real.exp (-‖z‖^2/(2*σ^2)) * ((k.factorial:ℝ))⁻¹) •
          gaussML σ n k z) (fun _ : Fin k => h) := by
        rw [hF, ContinuousMultilinearMap.smul_apply, smul_eq_mul, gaussML_diag]
      rw [h2]
      calc ‖((g z * Real.exp (-‖z‖^2/(2*σ^2)) * ((k.factorial:ℝ))⁻¹) • gaussML σ n k z)
            (fun _ : Fin k => h)‖
          ≤ ‖(g z * Real.exp (-‖z‖^2/(2*σ^2)) * ((k.factorial:ℝ))⁻¹) • gaussML σ n k z‖ *
            ∏ _i : Fin k, ‖h‖ := ContinuousMultilinearMap.le_opNorm _ _
        _ = ‖(g z * Real.exp (-‖z‖^2/(2*σ^2)) * ((k.factorial:ℝ))⁻¹) • gaussML σ n k z‖ * ‖h‖^k := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    refine Integrable.mono'
      ((integrable_gaussCoeff_integrand σ hσ g hg_cont C hg k).norm.mul_const (‖h‖^k)) ?_ ?_
    · exact (by fun_prop : Continuous (F k)).aestronglyMeasurable
    · filter_upwards with z
      exact h1 z
  have hbound : ∀ k, ∫ z, ‖F k z‖ ≤ |C| * (4*Real.pi*σ^2)^((n:ℝ)/2) *
      (2 * (2*‖h‖/σ^2)^k / (k.factorial:ℝ) + 16*σ*(k+1)*(16*‖h‖/σ)^k) := by
    intro k
    have h2 : ∀ z, ‖F k z‖ ≤ ‖(g z * Real.exp (-‖z‖^2/(2*σ^2)) * ((k.factorial:ℝ))⁻¹) •
        gaussML σ n k z‖ * ‖h‖^k := by
      intro z
      have h3 : F k z = ((g z * Real.exp (-‖z‖^2/(2*σ^2)) * ((k.factorial:ℝ))⁻¹) •
          gaussML σ n k z) (fun _ : Fin k => h) := by
        rw [hF, ContinuousMultilinearMap.smul_apply, smul_eq_mul, gaussML_diag]
      rw [h3]
      calc ‖((g z * Real.exp (-‖z‖^2/(2*σ^2)) * ((k.factorial:ℝ))⁻¹) • gaussML σ n k z)
            (fun _ : Fin k => h)‖
          ≤ ‖(g z * Real.exp (-‖z‖^2/(2*σ^2)) * ((k.factorial:ℝ))⁻¹) • gaussML σ n k z‖ *
            ∏ _i : Fin k, ‖h‖ := ContinuousMultilinearMap.le_opNorm _ _
        _ = ‖(g z * Real.exp (-‖z‖^2/(2*σ^2)) * ((k.factorial:ℝ))⁻¹) • gaussML σ n k z‖ * ‖h‖^k := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have h3 : 0 ≤ ‖h‖^k := by positivity
    calc ∫ z, ‖F k z‖ ≤ ∫ z, ‖(g z * Real.exp (-‖z‖^2/(2*σ^2)) * ((k.factorial:ℝ))⁻¹) •
          gaussML σ n k z‖ * ‖h‖^k :=
          integral_mono (hFint k).norm
            ((integrable_gaussCoeff_integrand σ hσ g hg_cont C hg k).norm.mul_const _) h2
      _ = (∫ z, ‖(g z * Real.exp (-‖z‖^2/(2*σ^2)) * ((k.factorial:ℝ))⁻¹) • gaussML σ n k z‖) * ‖h‖^k := by
          rw [integral_mul_const]
      _ ≤ ((|C| * (2:ℝ)^(k+1) * (1 + (8*σ)^(k+1) * ((k+1).factorial:ℝ)) /
            ((k.factorial:ℝ) * σ^(2*k))) * (4*Real.pi*σ^2)^((n:ℝ)/2)) * ‖h‖^k := by
          apply mul_le_mul_of_nonneg_right
            (integral_norm_gaussCoeff_integrand_le σ hσ g hg_cont C hg k) h3
      _ = |C| * (4*Real.pi*σ^2)^((n:ℝ)/2) *
            ((2:ℝ)^(k+1) * (1 + (8*σ)^(k+1) * ((k+1).factorial:ℝ)) /
              ((k.factorial:ℝ) * σ^(2*k)) * ‖h‖^k) := by ring
      _ ≤ |C| * (4*Real.pi*σ^2)^((n:ℝ)/2) *
            (2 * (2*‖h‖/σ^2)^k / (k.factorial:ℝ) + 16*σ*(k+1)*(16*‖h‖/σ)^k) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          simpa using gaussCoeff_term_le σ hσ 1 ‖h‖ k
  have hmaj : Summable (fun k : ℕ => |C| * (4*Real.pi*σ^2)^((n:ℝ)/2) *
      (2 * (2*‖h‖/σ^2)^k / (k.factorial:ℝ) + 16*σ*(k+1)*(16*‖h‖/σ)^k)) := by
    have hq : (16*‖h‖/σ) < 1 := by
      rw [div_lt_one (by positivity)]; nlinarith [hh, hσ]
    have hq0 : 0 ≤ 16*‖h‖/σ := by positivity
    have hqn : ‖16*‖h‖/σ‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq
    have h1 : Summable (fun k : ℕ => (2*‖h‖/σ^2)^k / (k.factorial:ℝ)) :=
      Real.summable_pow_div_factorial _
    have h2 : Summable (fun k : ℕ => (16*‖h‖/σ)^k) := summable_geometric_of_norm_lt_one hqn
    have h3 : Summable (fun k : ℕ => ((k:ℝ)+1) * (16*‖h‖/σ)^k) := by
      have h4 : Summable (fun k : ℕ => (k:ℝ) * (16*‖h‖/σ)^k) :=
        (hasSum_coe_mul_geometric_of_norm_lt_one hqn).summable
      refine (h4.add h2).congr (fun k => ?_)
      push_cast; ring
    have h5 : Summable (fun k : ℕ => 2 * ((2*‖h‖/σ^2)^k / (k.factorial:ℝ))) := h1.mul_left 2
    have h6 : Summable (fun k : ℕ => 16*σ * (((k:ℝ)+1) * (16*‖h‖/σ)^k)) := h3.mul_left (16*σ)
    have h7 := h5.add h6
    refine (h7.mul_left (|C| * (4*Real.pi*σ^2)^((n:ℝ)/2))).congr (fun k => ?_)
    ring
  have hsumm : Summable (fun k => ∫ z, ‖F k z‖) :=
    Summable.of_nonneg_of_le (fun k => integral_nonneg (fun z => norm_nonneg _)) hbound hmaj
  have hmain := hasSum_integral_of_summable_integral_norm hFint hsumm
  rw [show (fun k => ∫ z, F k z) = (fun k => gaussCoeff σ g k (fun _ : Fin k => h)) from
    funext (fun k => (gaussCoeff_apply_diag σ hσ g hg_cont C hg k h).symm)] at hmain
  rw [show (∫ z, ∑' k, F k z) = gaussTransform σ g h from ?_] at hmain
  · exact hmain
  · rw [gaussTransform]
    apply integral_congr_ae
    filter_upwards with z
    have hsum_eq : (∑' k, F k z) =
        g z * Real.exp (-‖z‖^2/(2*σ^2)) * Real.exp (inner ℝ z h / σ^2) := by
      have h1 : ∀ k : ℕ, F k z = (g z * Real.exp (-‖z‖^2/(2*σ^2))) *
          (((σ^2)⁻¹ * inner ℝ z h)^k * ((k.factorial:ℝ))⁻¹) := by
        intro k; rw [hF]; ring
      rw [tsum_congr h1, tsum_mul_left]
      have h2 : HasSum (fun k : ℕ => ((σ^2)⁻¹ * inner ℝ z h)^k * ((k.factorial:ℝ))⁻¹)
          (Real.exp ((σ^2)⁻¹ * inner ℝ z h)) := by
        have hs : Summable (fun k : ℕ => ((σ^2)⁻¹ * inner ℝ z h)^k * ((k.factorial:ℝ))⁻¹) := by
          simpa [div_eq_mul_inv, mul_comm] using
            (Real.summable_pow_div_factorial ((σ^2)⁻¹ * inner ℝ z h))
        have htsum : (∑' k, ((σ^2)⁻¹ * inner ℝ z h)^k * ((k.factorial:ℝ))⁻¹)
            = Real.exp ((σ^2)⁻¹ * inner ℝ z h) := by
          rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
          apply tsum_congr
          intro k
          rw [smul_eq_mul]
          ring
        rw [← htsum]
        exact hs.hasSum
      rw [h2.tsum_eq]
      congr 1
      ring
    rw [hsum_eq]


/-- The Gaussian transform has a power series with positive radius of convergence. -/
lemma hasFPowerSeriesOnBall_gaussTransform (σ : ℝ) (hσ : 0 < σ)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg_cont : Continuous g) (C : ℝ)
    (hg : ∀ z, |g z| ≤ C * (1 + ‖z‖)) :
    HasFPowerSeriesOnBall (gaussTransform σ g) (gaussCoeff σ g) 0
      (((σ/128).toNNReal : NNReal) : ENNReal) := by
  have hσ128 : (0:ℝ) < σ/128 := by positivity
  have hA : (2*(σ/128)/σ^2) = 1/(64*σ) := by field_simp; ring
  have hB : 16*(σ/128)/σ = 1/8 := by field_simp; ring
  refine ⟨?_, ?_, ?_⟩
  · refine FormalMultilinearSeries.le_radius_of_bound _ (|C| * (4*Real.pi*σ^2)^((n:ℝ)/2) *
      (2*Real.exp (1/(64*σ)) + 32*σ)) ?_
    intro k
    have h1 := norm_gaussCoeff_le σ hσ g hg_cont C hg k
    have h2 : (|C| * (2:ℝ)^(k+1) * (1 + (8*σ)^(k+1) * ((k+1).factorial:ℝ)) /
        ((k.factorial:ℝ) * σ^(2*k))) * (σ/128)^k ≤
        |C| * (2 * (2*(σ/128)/σ^2)^k / (k.factorial:ℝ) + 16*σ*(k+1)*(16*(σ/128)/σ)^k) :=
      gaussCoeff_term_le σ hσ C (σ/128) k
    have h3 : (2*(σ/128)/σ^2)^k / (k.factorial:ℝ) ≤ Real.exp (1/(64*σ)) := by
      have hh := Real.pow_div_factorial_le_exp (2*(σ/128)/σ^2) (by positivity) k
      simpa [hA] using hh
    have h4 : ((k:ℝ)+1)*(16*(σ/128)/σ)^k ≤ 2 := by
      rw [hB]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · norm_num
      · have hk1 : (k:ℝ) + 1 ≤ 2^k := by
          have hk2 := Nat.lt_two_pow_self (n := k)
          have hk3 : k + 1 ≤ 2^k := hk2
          exact_mod_cast hk3
        calc ((k:ℝ)+1)*(1/8)^k ≤ (2:ℝ)^k * (1/8)^k := by
              apply mul_le_mul_of_nonneg_right hk1 (by positivity)
          _ = (1/4:ℝ)^k := by rw [← mul_pow]; norm_num
          _ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
          _ ≤ 2 := by norm_num
    calc ‖gaussCoeff σ g k‖ * ((((σ/128).toNNReal : NNReal) : ℝ))^k
        = ‖gaussCoeff σ g k‖ * (σ/128)^k := by rw [Real.coe_toNNReal _ hσ128.le]
      _ ≤ ((|C| * (2:ℝ)^(k+1) * (1 + (8*σ)^(k+1) * ((k+1).factorial:ℝ)) /
            ((k.factorial:ℝ) * σ^(2*k))) * (4*Real.pi*σ^2)^((n:ℝ)/2)) * (σ/128)^k := by
          apply mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (4*Real.pi*σ^2)^((n:ℝ)/2) * ((|C| * (2:ℝ)^(k+1) *
            (1 + (8*σ)^(k+1) * ((k+1).factorial:ℝ)) / ((k.factorial:ℝ) * σ^(2*k))) * (σ/128)^k) := by
          ring
      _ ≤ (4*Real.pi*σ^2)^((n:ℝ)/2) * (|C| * (2 * (2*(σ/128)/σ^2)^k / (k.factorial:ℝ) +
            16*σ*(k+1)*(16*(σ/128)/σ)^k)) := by
          apply mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ |C| * (4*Real.pi*σ^2)^((n:ℝ)/2) * (2*Real.exp (1/(64*σ)) + 32*σ) := by
          have hmid : 2*(2*(σ/128)/σ^2)^k / (k.factorial:ℝ) +
                16*σ*((k:ℝ)+1)*(16*(σ/128)/σ)^k ≤ 2*Real.exp (1/(64*σ)) + 32*σ := by
            have h5 := mul_le_mul_of_nonneg_left h4 (by positivity : (0:ℝ) ≤ 16*σ)
            have h6 := mul_le_mul_of_nonneg_left h3 (by norm_num : (0:ℝ) ≤ 2)
            have e1 : 2*(2*(σ/128)/σ^2)^k / (k.factorial:ℝ)
                = 2*((2*(σ/128)/σ^2)^k/(k.factorial:ℝ)) := by ring
            have e2 : 16*σ*((k:ℝ)+1)*(16*(σ/128)/σ)^k
                = 16*σ*(((k:ℝ)+1)*(16*(σ/128)/σ)^k) := by ring
            rw [e1, e2]
            linarith [h5, h6]
          calc (4*Real.pi*σ^2)^((n:ℝ)/2) * (|C| * (2*(2*(σ/128)/σ^2)^k / (k.factorial:ℝ) +
                16*σ*((k:ℝ)+1)*(16*(σ/128)/σ)^k))
              = |C| * (4*Real.pi*σ^2)^((n:ℝ)/2) * (2*(2*(σ/128)/σ^2)^k / (k.factorial:ℝ) +
                16*σ*((k:ℝ)+1)*(16*(σ/128)/σ)^k) := by ring
            _ ≤ |C| * (4*Real.pi*σ^2)^((n:ℝ)/2) * (2*Real.exp (1/(64*σ)) + 32*σ) := by
                apply mul_le_mul_of_nonneg_left hmid (by positivity)
  · rw [ENNReal.coe_pos]; exact Real.toNNReal_pos.mpr hσ128
  · intro y hy
    rw [Metric.mem_eball] at hy
    have hy' : ‖y‖ < σ/16 := by
      have h1 : edist y 0 < (((σ/128).toNNReal : NNReal) : ENNReal) := hy
      rw [edist_eq_enorm_sub, sub_zero, enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal] at h1
      rw [show (((σ/128).toNNReal : NNReal) : ENNReal) = ENNReal.ofReal (σ/128) from rfl] at h1
      have h2 : (↑(‖y‖₊) : ℝ) < σ/128 := (ENNReal.ofReal_lt_ofReal_iff hσ128).mp h1
      have h3 : (‖y‖ : ℝ) < σ/128 := by simpa using h2
      linarith
    simpa using hasSum_gaussCoeff σ hσ g hg_cont C hg hy'

/-- The Gaussian transform is analytic at the origin. -/
lemma analyticAt_gaussTransform (σ : ℝ) (hσ : 0 < σ)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg_cont : Continuous g) (C : ℝ)
    (hg : ∀ z, |g z| ≤ C * (1 + ‖z‖)) :
    AnalyticAt ℝ (gaussTransform σ g) 0 :=
  (hasFPowerSeriesOnBall_gaussTransform σ hσ g hg_cont C hg).analyticAt


/-- The Gaussian smoothing of a continuous function of at most linear growth is `C^ω`. -/
theorem contDiff_top_gauss_smoothing (σ : ℝ) (hσ : 0 < σ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Continuous f) (C : ℝ)
    (hC : ∀ y, |f y| ≤ C * (1 + ‖y‖)) :
    ContDiff ℝ ⊤ (fun x : EuclideanSpace ℝ (Fin n) =>
      ∫ y, f y * Real.exp (-‖x - y‖^2/(2*σ^2))) := by
  rw [contDiff_omega_iff_analyticOnNhd]
  intro x₀ _
  set g : EuclideanSpace ℝ (Fin n) → ℝ := fun z => f (x₀ + z) with hg
  have hg_cont : Continuous g := hf.comp (continuous_const.add continuous_id)
  have hg_grow : ∀ z, |g z| ≤ (|C| * (1 + ‖x₀‖)) * (1 + ‖z‖) := by
    intro z
    have h1 : |f (x₀ + z)| ≤ C * (1 + ‖x₀ + z‖) := hC (x₀ + z)
    have h1' : |f (x₀ + z)| ≤ |C| * (1 + ‖x₀ + z‖) := by
      calc |f (x₀ + z)| ≤ C * (1 + ‖x₀ + z‖) := h1
        _ ≤ |C| * (1 + ‖x₀ + z‖) := by
            apply mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    have h2 : ‖x₀ + z‖ ≤ ‖x₀‖ + ‖z‖ := norm_add_le _ _
    have h3 : (0:ℝ) ≤ |C| := abs_nonneg _
    have h4 : (0:ℝ) ≤ 1 + ‖z‖ := by positivity
    rw [hg]
    calc |f (x₀ + z)| ≤ |C| * (1 + ‖x₀ + z‖) := h1'
      _ ≤ |C| * (1 + (‖x₀‖ + ‖z‖)) := by
          apply mul_le_mul_of_nonneg_left _ h3
          linarith
      _ ≤ |C| * (1 + ‖x₀‖) * (1 + ‖z‖) := by
          have h5 : (0:ℝ) ≤ ‖x₀‖ := norm_nonneg _
          have h6 : (0:ℝ) ≤ ‖z‖ := norm_nonneg _
          have h7 : (1 + (‖x₀‖ + ‖z‖)) ≤ (1 + ‖x₀‖) * (1 + ‖z‖) := by nlinarith
          calc |C| * (1 + (‖x₀‖ + ‖z‖)) ≤ |C| * ((1 + ‖x₀‖) * (1 + ‖z‖)) :=
                mul_le_mul_of_nonneg_left h7 h3
            _ = |C| * (1 + ‖x₀‖) * (1 + ‖z‖) := by ring
  have hW : AnalyticAt ℝ (gaussTransform σ g) 0 :=
    analyticAt_gaussTransform σ hσ g hg_cont _ hg_grow
  have hpre : AnalyticAt ℝ (fun h : EuclideanSpace ℝ (Fin n) => Real.exp (-‖h‖^2/(2*σ^2))) 0 := by
    have h1 : ContDiff ℝ ⊤ (fun h : EuclideanSpace ℝ (Fin n) => -‖h‖^2/(2*σ^2)) := by
      have h2 : ContDiff ℝ ⊤ (fun h : EuclideanSpace ℝ (Fin n) => inner ℝ h h) := by
        have hh := (contDiff_inner (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n)) (n := ⊤)).comp
          (contDiff_id.prodMk contDiff_id)
        have h2' : ((fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => inner ℝ p.1 p.2) ∘
            fun x => (id x, id x)) = fun h => inner ℝ h h := by
          funext h; rfl
        rwa [h2'] at hh
      have h3 : (fun h : EuclideanSpace ℝ (Fin n) => -‖h‖^2/(2*σ^2))
          = fun h => -(inner ℝ h h)/(2*σ^2) := by
        funext h; rw [real_inner_self_eq_norm_sq]
      rw [h3]
      fun_prop
    have h4 : ContDiff ℝ ⊤ (fun h : EuclideanSpace ℝ (Fin n) => Real.exp (-‖h‖^2/(2*σ^2))) :=
      Real.contDiff_exp.comp h1
    exact (contDiff_omega_iff_analyticOnNhd.mp h4) 0 (mem_univ 0)
  have hkey : AnalyticAt ℝ (fun h : EuclideanSpace ℝ (Fin n) =>
      ∫ y, f y * Real.exp (-‖(x₀ + h) - y‖^2/(2*σ^2))) 0 := by
    have hfun : (fun h : EuclideanSpace ℝ (Fin n) =>
        ∫ y, f y * Real.exp (-‖(x₀ + h) - y‖^2/(2*σ^2)))
        = fun h => Real.exp (-‖h‖^2/(2*σ^2)) * gaussTransform σ g h := by
      funext h
      show (∫ y, f y * Real.exp (-‖(x₀ + h) - y‖^2/(2*σ^2)))
        = Real.exp (-‖h‖^2/(2*σ^2)) * (∫ z, g z * Real.exp (-‖z‖^2/(2*σ^2)) *
            Real.exp (inner ℝ z h / σ^2))
      have htrans : (∫ z, g z * Real.exp (-‖z‖^2/(2*σ^2)) * Real.exp (inner ℝ z h / σ^2))
          = ∫ y, f y * Real.exp (-‖y - x₀‖^2/(2*σ^2)) * Real.exp (inner ℝ (y - x₀) h / σ^2) := by
        have h1 := integral_add_left_eq_self (μ := volume)
          (fun y => f y * Real.exp (-‖y - x₀‖^2/(2*σ^2)) * Real.exp (inner ℝ (y - x₀) h / σ^2)) x₀
        simpa only [hg, add_sub_cancel_left] using h1
      rw [htrans, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      rw [show -(‖(x₀ + h) - y‖^2)/(2*σ^2) = -(‖h‖^2)/(2*σ^2) + (inner ℝ (y - x₀) h)/σ^2 +
        (-(‖y - x₀‖^2)/(2*σ^2)) by
          have hns : ‖(x₀ + h) - y‖^2 = ‖h‖^2 - 2*inner ℝ h (y - x₀) + ‖y - x₀‖^2 := by
            rw [show (x₀ + h) - y = h - (y - x₀) by abel, norm_sub_sq_real]
          rw [hns, real_inner_comm h (y - x₀)]
          field_simp
          ring]
      rw [Real.exp_add, Real.exp_add]
      ring
    rw [hfun]
    exact hpre.mul hW
  have hfin := hkey.comp_sub x₀
  simpa only [add_sub_cancel, zero_add, add_sub_cancel_left] using hfin


/-- Integrability of `z ↦ ‖z‖ * exp(-‖z‖²/(2σ²))`, the first-moment integrand. -/
lemma integrable_norm_mul_gauss (σ : ℝ) (hσ : 0 < σ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
      ‖z‖ * Real.exp (-‖z‖^2/(2*σ^2))) volume := by
  refine (integrable_one_add_pow_gauss (n := n) σ hσ 1).mono' ?_ ?_
  · fun_prop
  · filter_upwards with z
    have h6 : ‖z‖ ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
    have h5 : (0:ℝ) ≤ Real.exp (-‖z‖^2/(2*σ^2)) := Real.exp_nonneg _
    have h7 : ‖z‖ * Real.exp (-‖z‖^2/(2*σ^2)) ≤ (1 + ‖z‖) * Real.exp (-‖z‖^2/(2*σ^2)) :=
      mul_le_mul_of_nonneg_right h6 h5
    have h8 : (1 + ‖z‖) * Real.exp (-‖z‖^2/(2*σ^2)) =
        (1 + ‖z‖)^1 * Real.exp (-‖z‖^2/(2*σ^2)) := by ring
    calc ‖‖z‖ * Real.exp (-‖z‖^2/(2*σ^2))‖
        = ‖z‖ * Real.exp (-‖z‖^2/(2*σ^2)) := Real.norm_of_nonneg (by positivity)
      _ ≤ (1 + ‖z‖) * Real.exp (-‖z‖^2/(2*σ^2)) := h7
      _ = (1 + ‖z‖)^1 * Real.exp (-‖z‖^2/(2*σ^2)) := h8


end

end MollifierAux

open MollifierAux

theorem mollified_infDist {n : ℕ} (E : Set (EuclideanSpace ℝ (Fin n)))
    (η : ℝ) (hη : 0 < η) :
    ∃ ρ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ⊤ ρ ∧ (∀ x, ‖fderiv ℝ ρ x‖ ≤ 1) ∧
      (∀ x, Metric.infDist x E - 2 * η ≤ ρ x) ∧
      (∀ x ∈ E, ρ x ≤ 0) := by
  set f : EuclideanSpace ℝ (Fin n) → ℝ := fun x => Metric.infDist x E with hf
  have hf_cont : Continuous f := Metric.continuous_infDist_pt E
  have hf_lip : LipschitzWith 1 f := Metric.lipschitz_infDist_pt E
  obtain ⟨C₀, hC₀⟩ : ∃ C : ℝ, ∀ y, |f y| ≤ C * (1 + ‖y‖) := by
    by_cases hE : E.Nonempty
    · obtain ⟨e₀, he₀⟩ := hE
      refine ⟨1 + ‖e₀‖, fun y => ?_⟩
      have h1 : f y ≤ dist y e₀ := by
        rw [hf]; exact Metric.infDist_le_dist_of_mem he₀
      have h2 : dist y e₀ ≤ ‖y‖ + ‖e₀‖ := dist_le_norm_add_norm y e₀
      have h3 : 0 ≤ f y := by rw [hf]; exact Metric.infDist_nonneg
      rw [abs_of_nonneg h3]
      nlinarith [h1, h2, norm_nonneg y, norm_nonneg e₀]
    · refine ⟨0, fun y => ?_⟩
      have h1 : f y = 0 := by
        rw [hf, Set.not_nonempty_iff_eq_empty.mp hE]
        exact Metric.infDist_empty
      rw [h1]; simp
  set B : ℝ := 4 * Real.sqrt 2 * (2:ℝ)^((n:ℝ)/2) with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  set σ : ℝ := η / (B + 1) with hσdef
  have hσ : 0 < σ := by rw [hσdef]; positivity
  have hσB : σ * B ≤ η := by
    rw [hσdef, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith [hB0, hη]
  have h2πσ : (0:ℝ) < 2*Real.pi*σ^2 := by positivity
  -- integral of the kernel
  have hKint : ∫ z : EuclideanSpace ℝ (Fin n), Real.exp (-‖z‖^2/(2*σ^2)) =
      (2*Real.pi*σ^2)^((n:ℝ)/2) := by
    have h1 := integral_gauss (n := n) (σ/Real.sqrt 2) (by positivity)
    have e1 : 4*(σ/Real.sqrt 2)^2 = 2*σ^2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; ring
    have e2 : 4*Real.pi*(σ/Real.sqrt 2)^2 = 2*Real.pi*σ^2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; ring
    simpa only [e1, e2] using h1
  -- the normalized first moment bound
  have hmoment : (2*Real.pi*σ^2)^(-(n:ℝ)/2) *
      (∫ z : EuclideanSpace ℝ (Fin n), ‖z‖ * Real.exp (-‖z‖^2/(2*σ^2))) ≤ σ * B := by
    have h1 := gauss_moment_le (n := n) σ hσ 1
    simp only [pow_one, Nat.factorial_one, Nat.cast_one, mul_one] at h1
    have h4π : (0:ℝ) < 4*Real.pi*σ^2 := by positivity
    have h2 : ∫ z : EuclideanSpace ℝ (Fin n), ‖z‖ * Real.exp (-‖z‖^2/(2*σ^2)) ≤
        4*Real.sqrt 2*σ * (4*Real.pi*σ^2)^((n:ℝ)/2) := by simpa using h1
    refine le_trans (mul_le_mul_of_nonneg_left h2 (by positivity)) ?_
    rw [hBdef]
    have key : (2*Real.pi*σ^2)^(-(n:ℝ)/2) * (4*Real.pi*σ^2)^((n:ℝ)/2) = (2:ℝ)^((n:ℝ)/2) := by
      have h4 : (4:ℝ)*Real.pi*σ^2 = 2*(2*Real.pi*σ^2) := by ring
      rw [h4, Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) h2πσ.le]
      have h5 : (2*Real.pi*σ^2)^(-(n:ℝ)/2) * (2*Real.pi*σ^2)^((n:ℝ)/2) = 1 := by
        rw [← Real.rpow_add h2πσ, show (-(n:ℝ)/2 + (n:ℝ)/2) = 0 by ring, Real.rpow_zero]
      calc (2*Real.pi*σ^2)^(-(n:ℝ)/2) * ((2:ℝ)^((n:ℝ)/2) * (2*Real.pi*σ^2)^((n:ℝ)/2))
          = (2:ℝ)^((n:ℝ)/2) *
            ((2*Real.pi*σ^2)^(-(n:ℝ)/2) * (2*Real.pi*σ^2)^((n:ℝ)/2)) := by ring
        _ = (2:ℝ)^((n:ℝ)/2) := by rw [h5, mul_one]
    have key2 : (2*Real.pi*σ^2)^(-(n:ℝ)/2) * (4*Real.sqrt 2*σ * (4*Real.pi*σ^2)^((n:ℝ)/2))
        = σ * (4 * Real.sqrt 2 * (2:ℝ)^((n:ℝ)/2)) := by
      rw [show (2*Real.pi*σ^2)^(-(n:ℝ)/2) * (4*Real.sqrt 2*σ * (4*Real.pi*σ^2)^((n:ℝ)/2))
          = 4*Real.sqrt 2*σ * ((2*Real.pi*σ^2)^(-(n:ℝ)/2) * (4*Real.pi*σ^2)^((n:ℝ)/2)) by ring,
        key]
      ring
    exact le_of_eq key2
  -- substitution: the smoothing is the convolution with the kernel
  have hsub : ∀ x : EuclideanSpace ℝ (Fin n), (∫ y, f y * Real.exp (-‖x - y‖^2/(2*σ^2)))
      = ∫ z, f (x - z) * Real.exp (-‖z‖^2/(2*σ^2)) := by
    intro x
    have h1 := integral_sub_left_eq_self
      (fun z : EuclideanSpace ℝ (Fin n) => f (x - z) * Real.exp (-‖z‖^2/(2*σ^2))) volume x
    simpa only [sub_sub_cancel] using h1
  -- integrability of the convolution integrand
  have hint : ∀ w : EuclideanSpace ℝ (Fin n),
      Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
        f (w - z) * Real.exp (-‖z‖^2/(2*σ^2))) volume := by
    intro w
    have h1 : Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
        (C₀ * (1 + ‖w‖)) * ((1 + ‖z‖) * Real.exp (-‖z‖^2/(2*σ^2)))) volume := by
      have h2 : Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
          (1 + ‖z‖) * Real.exp (-‖z‖^2/(2*σ^2))) volume := by
        simpa using integrable_one_add_pow_gauss (n := n) σ hσ 1
      simpa only [mul_assoc, mul_comm, mul_left_comm] using h2.const_mul (C₀ * (1 + ‖w‖))
    refine Integrable.mono' h1 ?_ ?_
    · apply Continuous.aestronglyMeasurable
      fun_prop
    · filter_upwards with z
      have h4 : (0:ℝ) ≤ Real.exp (-‖z‖^2/(2*σ^2)) := Real.exp_nonneg _
      have hfw : (0:ℝ) ≤ f (w - z) := by rw [hf]; exact Metric.infDist_nonneg
      have h2 : ‖w - z‖ ≤ ‖w‖ + ‖z‖ := norm_sub_le _ _
      have h3 : |f (w - z)| ≤ C₀ * (1 + ‖w - z‖) := hC₀ (w - z)
      have hC₀0 : 0 ≤ C₀ := by
        have hh := hC₀ 0
        simp only [norm_zero, add_zero, mul_one] at hh
        linarith [abs_nonneg (f 0)]
      have h5 : f (w - z) * Real.exp (-‖z‖^2/(2*σ^2)) ≤
          (C₀ * (1 + ‖w‖)) * ((1 + ‖z‖) * Real.exp (-‖z‖^2/(2*σ^2))) := by
        have h6 : C₀ * (1 + ‖w - z‖) ≤ C₀ * (1 + ‖w‖) * (1 + ‖z‖) := by
          have h7 : (1 + (‖w‖ + ‖z‖)) ≤ (1 + ‖w‖) * (1 + ‖z‖) := by
            nlinarith [norm_nonneg w, norm_nonneg z]
          calc C₀ * (1 + ‖w - z‖) ≤ C₀ * (1 + (‖w‖ + ‖z‖)) :=
                mul_le_mul_of_nonneg_left (by linarith) hC₀0
            _ ≤ C₀ * ((1 + ‖w‖) * (1 + ‖z‖)) := mul_le_mul_of_nonneg_left h7 hC₀0
            _ = C₀ * (1 + ‖w‖) * (1 + ‖z‖) := by ring
        calc f (w - z) * Real.exp (-‖z‖^2/(2*σ^2))
            ≤ (C₀ * (1 + ‖w - z‖)) * Real.exp (-‖z‖^2/(2*σ^2)) := by
              apply mul_le_mul_of_nonneg_right _ h4
              exact le_trans (le_abs_self _) h3
          _ ≤ (C₀ * (1 + ‖w‖) * (1 + ‖z‖)) * Real.exp (-‖z‖^2/(2*σ^2)) :=
              mul_le_mul_of_nonneg_right h6 h4
          _ = (C₀ * (1 + ‖w‖)) * ((1 + ‖z‖) * Real.exp (-‖z‖^2/(2*σ^2))) := by ring
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hfw h4)]
      exact h5
  -- the smoothed function is 1-Lipschitz
  have hv_lip : LipschitzWith 1 (fun x : EuclideanSpace ℝ (Fin n) =>
      (2*Real.pi*σ^2)^(-(n:ℝ)/2) * ∫ y, f y * Real.exp (-‖x - y‖^2/(2*σ^2))) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simp only [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
    rw [hsub x, hsub y]
    have hCpos : (0:ℝ) < (2*Real.pi*σ^2)^(-(n:ℝ)/2) := by positivity
    have hbound : ∀ z : EuclideanSpace ℝ (Fin n),
        ‖f (x - z) * Real.exp (-‖z‖^2/(2*σ^2)) - f (y - z) * Real.exp (-‖z‖^2/(2*σ^2))‖ ≤
          ‖x - y‖ * Real.exp (-‖z‖^2/(2*σ^2)) := by
      intro z
      have hA : |f (x - z) - f (y - z)| ≤ ‖x - y‖ := by
        have h1 := hf_lip.norm_sub_le (x - z) (y - z)
        have h2 : (x - z) - (y - z) = x - y := by abel
        simpa [h2] using h1
      have h4 : (0:ℝ) ≤ Real.exp (-‖z‖^2/(2*σ^2)) := Real.exp_nonneg _
      have h5 : f (x - z) * Real.exp (-‖z‖^2/(2*σ^2)) - f (y - z) * Real.exp (-‖z‖^2/(2*σ^2))
          = (f (x - z) - f (y - z)) * Real.exp (-‖z‖^2/(2*σ^2)) := by ring
      rw [h5, Real.norm_eq_abs, abs_mul, abs_of_nonneg h4]
      exact mul_le_mul_of_nonneg_right hA h4
    have hdiff : (∫ z : EuclideanSpace ℝ (Fin n), f (x - z) * Real.exp (-‖z‖^2/(2*σ^2))) -
        (∫ z, f (y - z) * Real.exp (-‖z‖^2/(2*σ^2)))
        = ∫ z, (f (x - z) * Real.exp (-‖z‖^2/(2*σ^2)) - f (y - z) * Real.exp (-‖z‖^2/(2*σ^2))) := by
      rw [integral_sub (hint x) (hint y)]
    have hKint'' : Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
        Real.exp (-‖z‖^2/(2*σ^2))) volume := by
      simpa using integrable_one_add_pow_gauss (n := n) σ hσ 0
    have hKint' : Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
        ‖x - y‖ * Real.exp (-‖z‖^2/(2*σ^2))) volume :=
      hKint''.const_mul (‖x - y‖)
    rw [← mul_sub, hdiff, Real.norm_eq_abs, abs_mul, abs_of_pos hCpos]
    have h3 : ‖∫ z : EuclideanSpace ℝ (Fin n), (f (x - z) * Real.exp (-‖z‖^2/(2*σ^2)) -
        f (y - z) * Real.exp (-‖z‖^2/(2*σ^2)))‖ ≤
        ∫ z, ‖x - y‖ * Real.exp (-‖z‖^2/(2*σ^2)) :=
      norm_integral_le_of_norm_le hKint' (Eventually.of_forall hbound)
    have h4 : (∫ z : EuclideanSpace ℝ (Fin n), ‖x - y‖ * Real.exp (-‖z‖^2/(2*σ^2))) = ‖x - y‖ * (2*Real.pi*σ^2)^((n:ℝ)/2) := by
      rw [integral_const_mul, hKint]
    calc (2*Real.pi*σ^2)^(-(n:ℝ)/2) * ‖∫ z, (f (x - z) * Real.exp (-‖z‖^2/(2*σ^2)) -
          f (y - z) * Real.exp (-‖z‖^2/(2*σ^2)))‖
        ≤ (2*Real.pi*σ^2)^(-(n:ℝ)/2) * (‖x - y‖ * (2*Real.pi*σ^2)^((n:ℝ)/2)) := by
          rw [h4] at h3
          exact mul_le_mul_of_nonneg_left h3 hCpos.le
      _ = ‖x - y‖ := by
          rw [show (2*Real.pi*σ^2)^(-(n:ℝ)/2) * (‖x - y‖ * (2*Real.pi*σ^2)^((n:ℝ)/2))
              = ‖x - y‖ * ((2*Real.pi*σ^2)^(-(n:ℝ)/2) * (2*Real.pi*σ^2)^((n:ℝ)/2)) by ring]
          rw [← Real.rpow_add h2πσ, show (-(n:ℝ)/2 + (n:ℝ)/2) = 0 by ring, Real.rpow_zero,
            mul_one]
  -- the approximation bound
  have hKi'' : Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
      ‖z‖ * Real.exp (-‖z‖^2/(2*σ^2))) volume := integrable_norm_mul_gauss (n := n) σ hσ
  have happrox : ∀ w : EuclideanSpace ℝ (Fin n),
      |(2*Real.pi*σ^2)^(-(n:ℝ)/2) * (∫ y, f y * Real.exp (-‖w - y‖^2/(2*σ^2))) - f w| ≤ σ * B := by
    intro w
    rw [hsub w]
    have hCpos : (0:ℝ) < (2*Real.pi*σ^2)^(-(n:ℝ)/2) := by positivity
    have hKi : Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
        Real.exp (-‖z‖^2/(2*σ^2))) volume := by
      simpa using integrable_one_add_pow_gauss (n := n) σ hσ 0
    have h1 : (∫ z : EuclideanSpace ℝ (Fin n), f (w - z) * Real.exp (-‖z‖^2/(2*σ^2)))
        - f w * (2*Real.pi*σ^2)^((n:ℝ)/2)
        = ∫ z : EuclideanSpace ℝ (Fin n), (f (w - z) - f w) * Real.exp (-‖z‖^2/(2*σ^2)) := by
      have hfw_int : Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
          f w * Real.exp (-‖z‖^2/(2*σ^2))) volume := hKi.const_mul (f w)
      have hfw_eq : (∫ z : EuclideanSpace ℝ (Fin n), f w * Real.exp (-‖z‖^2/(2*σ^2))) =
          f w * (2*Real.pi*σ^2)^((n:ℝ)/2) := by
        rw [integral_const_mul, hKint]
      rw [← hfw_eq, ← integral_sub (hint w) hfw_int]
      apply integral_congr_ae
      filter_upwards with z
      ring
    have h3 : (2*Real.pi*σ^2)^(-(n:ℝ)/2) *
          (∫ z : EuclideanSpace ℝ (Fin n), f (w - z) * Real.exp (-‖z‖^2/(2*σ^2))) - f w
        = (2*Real.pi*σ^2)^(-(n:ℝ)/2) *
          (∫ z : EuclideanSpace ℝ (Fin n), (f (w - z) - f w) * Real.exp (-‖z‖^2/(2*σ^2))) := by
      rw [← h1, mul_sub]
      have h4 : (2*Real.pi*σ^2)^(-(n:ℝ)/2) * (f w * (2*Real.pi*σ^2)^((n:ℝ)/2)) = f w := by
        rw [mul_comm (f w) ((2*Real.pi*σ^2)^((n:ℝ)/2)), ← mul_assoc, ← Real.rpow_add h2πσ,
          show (-(n:ℝ)/2 + (n:ℝ)/2) = 0 by ring, Real.rpow_zero, one_mul]
      rw [h4]
    rw [h3, abs_mul, abs_of_pos hCpos]
    have h2 : |∫ z : EuclideanSpace ℝ (Fin n), (f (w - z) - f w) * Real.exp (-‖z‖^2/(2*σ^2))| ≤
        ∫ z : EuclideanSpace ℝ (Fin n), ‖z‖ * Real.exp (-‖z‖^2/(2*σ^2)) := by
      have hb : ∀ z : EuclideanSpace ℝ (Fin n),
          ‖(f (w - z) - f w) * Real.exp (-‖z‖^2/(2*σ^2))‖ ≤
            ‖z‖ * Real.exp (-‖z‖^2/(2*σ^2)) := by
        intro z
        have hA : |f (w - z) - f w| ≤ ‖z‖ := by
          have h5 := hf_lip.norm_sub_le (w - z) w
          have h6 : (w - z) - w = -z := by abel
          simpa [h6] using h5
        have h5 : (0:ℝ) ≤ Real.exp (-‖z‖^2/(2*σ^2)) := Real.exp_nonneg _
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h5]
        exact mul_le_mul_of_nonneg_right hA h5
      rw [← Real.norm_eq_abs]
      exact norm_integral_le_of_norm_le hKi'' (Eventually.of_forall hb)
    calc (2*Real.pi*σ^2)^(-(n:ℝ)/2) *
          |∫ z : EuclideanSpace ℝ (Fin n), (f (w - z) - f w) * Real.exp (-‖z‖^2/(2*σ^2))|
        ≤ (2*Real.pi*σ^2)^(-(n:ℝ)/2) *
          (∫ z : EuclideanSpace ℝ (Fin n), ‖z‖ * Real.exp (-‖z‖^2/(2*σ^2))) :=
          mul_le_mul_of_nonneg_left h2 hCpos.le
      _ ≤ σ * B := hmoment
  refine ⟨fun x => (2*Real.pi*σ^2)^(-(n:ℝ)/2) *
      (∫ y, f y * Real.exp (-‖x - y‖^2/(2*σ^2))) - σ * B, ?_, ?_, ?_, ?_⟩
  · -- analyticity / smoothness
    have h1 : ContDiff ℝ ⊤ (fun x : EuclideanSpace ℝ (Fin n) =>
        (2*Real.pi*σ^2)^(-(n:ℝ)/2) * ∫ y, f y * Real.exp (-‖x - y‖^2/(2*σ^2))) := by
      have h2 := ContDiff.const_smul ((2*Real.pi*σ^2)^(-(n:ℝ)/2))
        (contDiff_top_gauss_smoothing σ hσ f hf_cont C₀ hC₀)
      simpa using h2
    exact h1.sub contDiff_const
  · -- uniform bound on the derivative
    intro x
    have h1 : LipschitzWith 1 (fun x : EuclideanSpace ℝ (Fin n) =>
        (2*Real.pi*σ^2)^(-(n:ℝ)/2) *
        (∫ y, f y * Real.exp (-‖x - y‖^2/(2*σ^2))) - σ * B) := by
      have h2 := hv_lip.sub (LipschitzWith.const (σ * B))
      simpa using h2
    have h3 := norm_fderiv_le_of_lipschitz ℝ h1 (x₀ := x)
    simpa using h3
  · -- lower bound
    intro x
    have h1 := happrox x
    rw [abs_le] at h1
    have h2 : f x - 2 * η ≤ (2*Real.pi*σ^2)^(-(n:ℝ)/2) *
        (∫ y, f y * Real.exp (-‖x - y‖^2/(2*σ^2))) - σ * B := by
      linarith [h1.1, hσB]
    rw [show Metric.infDist x E = f x by rw [hf]]
    exact h2
  · -- nonpositive on E
    intro x hx
    have h4 : ∀ z : EuclideanSpace ℝ (Fin n),
        f (x - z) * Real.exp (-‖z‖^2/(2*σ^2)) ≤ ‖z‖ * Real.exp (-‖z‖^2/(2*σ^2)) := by
      intro z
      have h5' : (0:ℝ) ≤ Real.exp (-‖z‖^2/(2*σ^2)) := Real.exp_nonneg _
      have hle : f (x - z) ≤ ‖z‖ := by
        have h6 : f (x - z) ≤ dist (x - z) x := by
          rw [hf]
          exact Metric.infDist_le_dist_of_mem hx
        rw [dist_eq_norm] at h6
        have h7 : (x - z) - x = -z := by abel
        rw [h7, norm_neg] at h6
        exact h6
      exact mul_le_mul_of_nonneg_right hle h5'
    have h2 : (∫ y, f y * Real.exp (-‖x - y‖^2/(2*σ^2))) ≤
        ∫ z : EuclideanSpace ℝ (Fin n), ‖z‖ * Real.exp (-‖z‖^2/(2*σ^2)) := by
      rw [hsub x]
      exact integral_mono_ae (hint x) hKi'' (Eventually.of_forall h4)
    have h3 : (2*Real.pi*σ^2)^(-(n:ℝ)/2) *
        (∫ y, f y * Real.exp (-‖x - y‖^2/(2*σ^2))) ≤ σ * B :=
      le_trans (mul_le_mul_of_nonneg_left h2 (by positivity)) hmoment
    linarith [h3]

end Commons.Analysis.GaussianMeasure