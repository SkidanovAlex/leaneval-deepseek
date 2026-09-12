import Mathlib
import Submission.Model
import Submission.ModelCore
import Submission.ModelAlg

/-!
# The derivative of the geodesic field at a rest point

Task: prove the final theorem `fderiv_odeField_rest`.

For the geodesic first-order field `V z := (z.2, accel (g z.1) (fderiv g z.1) z.2)`, at the rest
point `(x₀, 0)` (where `V = 0`), the derivative is the linear map `δ ↦ (δ.2, 0)`:

    fderiv ℝ (odeField g) (x₀, 0) δ = (δ.2, 0)

## Proof structure (helpers below, all proved in this file)

1. `expRest_bilin_apply_norm_le` … `expRest_accel_bound`: the acceleration is bounded by
   `‖inverse (g x)‖ * (‖fderiv ℝ g x‖ * ‖v‖²) * 2` (rhsCovector is quadratic in the velocity).
2. `expRest_local_sq_bound`: near `x₀` the coefficients `‖fderiv ℝ g x‖` and `‖inverse (g x)‖`
   are bounded (continuity of `fderiv g` from `ContDiff 3 g`, continuity of the inverse at the
   invertible value `g x₀`), so along `h = (h₁, h₂)` with `‖h‖` small
   `‖accel (g (x₀+h₁)) (fderiv ℝ g (x₀+h₁)) h₂‖ ≤ C * ‖h‖²`.
3. `expRest_isLittleO`, `expRest_hasFDerivAt_zero`: that quadratic bound is `o(‖h‖)`, i.e.
   the second component of the field has derivative `0` at `(x₀, 0)`.
4. The first component is the linear second projection; assembling both components gives
   `HasFDerivAt (odeField g) (δ ↦ (δ.2, 0)) (x₀, 0)` and hence the stated `fderiv` formula.
-/

open ContinuousLinearMap
open scoped ContDiff Topology
open Set Metric Filter
open Asymptotics

set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 4000000

namespace Submission.Model

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable section
set_option linter.unusedSectionVars false

/-- Pointwise bound for a bilinear form: `‖(B a) b‖ ≤ ‖B‖ * ‖a‖ * ‖b‖`. -/
lemma expRest_bilin_apply_norm_le (B : Bilin E) (a b : E) : ‖(B a) b‖ ≤ ‖B‖ * ‖a‖ * ‖b‖ := by
  calc
    ‖(B a) b‖ ≤ ‖B a‖ * ‖b‖ := ContinuousLinearMap.le_opNorm (𝕜 := ℝ) (B a) b
    _ ≤ (‖B‖ * ‖a‖) * ‖b‖ := by
      exact mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm (𝕜 := ℝ) B a) (norm_nonneg b)
    _ = ‖B‖ * ‖a‖ * ‖b‖ := by ring

/-- First `v v` term of the Euler-Lagrange covector for `T = fderiv g x`, applied at `w`. -/
lemma expRest_derivBilin_quad_bound (g : E → Bilin E) (x v w : E) :
    ‖(((fderiv ℝ g x) w) v) v‖ ≤ ‖fderiv ℝ g x‖ * ‖v‖ ^ 2 * ‖w‖ := by
  have h1 := expRest_bilin_apply_norm_le ((fderiv ℝ g x) w) v v
  have htw := ContinuousLinearMap.le_opNorm (𝕜 := ℝ) (fderiv ℝ g x) w
  calc
    ‖(((fderiv ℝ g x) w) v) v‖ ≤ ‖(fderiv ℝ g x) w‖ * ‖v‖ * ‖v‖ := h1
    _ ≤ (‖fderiv ℝ g x‖ * ‖w‖) * ‖v‖ * ‖v‖ := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right htw (norm_nonneg v)) (norm_nonneg v)
    _ = ‖fderiv ℝ g x‖ * ‖v‖ ^ 2 * ‖w‖ := by ring

/-- Second `v w` term of the Euler-Lagrange covector for `T = fderiv g x`, applied at `w`. -/
lemma expRest_derivBilin_apply_bound (g : E → Bilin E) (x v w : E) :
    ‖(((fderiv ℝ g x) v) v) w‖ ≤ ‖fderiv ℝ g x‖ * ‖v‖ ^ 2 * ‖w‖ := by
  have h1 := expRest_bilin_apply_norm_le ((fderiv ℝ g x) v) v w
  have htv := ContinuousLinearMap.le_opNorm (𝕜 := ℝ) (fderiv ℝ g x) v
  calc
    ‖(((fderiv ℝ g x) v) v) w‖ ≤ ‖(fderiv ℝ g x) v‖ * ‖v‖ * ‖w‖ := h1
    _ ≤ (‖fderiv ℝ g x‖ * ‖v‖) * ‖v‖ * ‖w‖ := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right htv (norm_nonneg v)) (norm_nonneg w)
    _ = ‖fderiv ℝ g x‖ * ‖v‖ ^ 2 * ‖w‖ := by ring

/-- The right-hand covector vanishes at zero velocity. -/
lemma expRest_rhsCovector_zero (T : E →L[ℝ] Bilin E) : rhsCovector T 0 = 0 := by
  unfold rhsCovector evalAtV
  ext w
  simp

/-- The acceleration vanishes at zero velocity. -/
lemma expRest_accel_zero (gx : Bilin E) (T : E →L[ℝ] Bilin E) : accel gx T 0 = 0 := by
  unfold accel
  rw [expRest_rhsCovector_zero]
  simp

/-- `rhsCovector (fderiv g x)` is bounded by twice `‖fderiv g x‖ ‖v‖²` in operator norm. -/
lemma expRest_rhsCovector_norm_le (g : E → Bilin E) (x v : E) :
    ‖rhsCovector (fderiv ℝ g x) v‖ ≤ (‖fderiv ℝ g x‖ * ‖v‖ ^ 2) * 2 := by
  refine ContinuousLinearMap.opNorm_le_bound (rhsCovector (fderiv ℝ g x) v) (by positivity) ?_
  intro w
  calc
    ‖(rhsCovector (fderiv ℝ g x) v) w‖ = ‖(1 / 2 : ℝ) * ((((fderiv ℝ g x) w) v) v) - ((((fderiv ℝ g x) v) v) w)‖ := by
        rw [rhsCovector_apply]
    _ ≤ ‖(1 / 2 : ℝ) * ((((fderiv ℝ g x) w) v) v)‖ + ‖((((fderiv ℝ g x) v) v) w)‖ := norm_sub_le _ _
    _ ≤ (1 / 2 : ℝ) * (‖fderiv ℝ g x‖ * ‖v‖ ^ 2 * ‖w‖) + ‖fderiv ℝ g x‖ * ‖v‖ ^ 2 * ‖w‖ := by
      have hA : ‖(1 / 2 : ℝ) * ((((fderiv ℝ g x) w) v) v)‖ ≤ (1 / 2 : ℝ) * (‖fderiv ℝ g x‖ * ‖v‖ ^ 2 * ‖w‖) := by
        rw [norm_mul, Real.norm_eq_abs]
        have h12 : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
        rw [h12]
        gcongr
        exact expRest_derivBilin_quad_bound g x v w
      have hB : ‖((((fderiv ℝ g x) v) v) w)‖ ≤ ‖fderiv ℝ g x‖ * ‖v‖ ^ 2 * ‖w‖ := expRest_derivBilin_apply_bound g x v w
      exact add_le_add hA hB
    _ ≤ 2 * (‖fderiv ℝ g x‖ * ‖v‖ ^ 2 * ‖w‖) := by
      have ht : 0 ≤ ‖fderiv ℝ g x‖ * ‖v‖ ^ 2 * ‖w‖ := by positivity
      nlinarith
    _ = ((‖fderiv ℝ g x‖ * ‖v‖ ^ 2) * 2) * ‖w‖ := by ring

/-- The acceleration is bounded by a constant times the square of the velocity norm. -/
lemma expRest_accel_bound (g : E → Bilin E) (x v : E) :
    ‖accel (g x) (fderiv ℝ g x) v‖ ≤ ‖(ContinuousLinearMap.inverse (g x))‖ * (‖fderiv ℝ g x‖ * ‖v‖ ^ 2) * 2 := by
  unfold accel
  calc
    ‖(ContinuousLinearMap.inverse (g x)) (rhsCovector (fderiv ℝ g x) v)‖
        ≤ ‖(ContinuousLinearMap.inverse (g x))‖ * ‖rhsCovector (fderiv ℝ g x) v‖ := ContinuousLinearMap.le_opNorm (𝕜 := ℝ) (ContinuousLinearMap.inverse (g x)) (rhsCovector (fderiv ℝ g x) v)
    _ ≤ ‖(ContinuousLinearMap.inverse (g x))‖ * ((‖fderiv ℝ g x‖ * ‖v‖ ^ 2) * 2) := by
      exact mul_le_mul_of_nonneg_left (expRest_rhsCovector_norm_le g x v) (norm_nonneg (ContinuousLinearMap.inverse (g x)))
    _ = ‖(ContinuousLinearMap.inverse (g x))‖ * (‖fderiv ℝ g x‖ * ‖v‖ ^ 2) * 2 := by ring

/-- A function continuous at a point is bounded on a small ball around it. -/
lemma expRest_norm_bound_near {F : Type*} [NormedAddCommGroup F] (φ : E → F) (x₀ : E)
    (hφ : ContinuousAt φ x₀) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : E, ‖x - x₀‖ < δ → ‖φ x‖ ≤ ‖φ x₀‖ + 1 := by
  have h := Metric.continuousAt_iff.mp hφ 1 zero_lt_one
  rcases h with ⟨δ, hδ, hbd⟩
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  have hx' : dist x x₀ < δ := by simpa [dist_eq_norm] using hx
  have hnorm : dist (φ x) (φ x₀) < 1 := hbd hx'
  have hsub : ‖φ x - φ x₀‖ < 1 := by simpa [dist_eq_norm] using hnorm
  have htri : ‖φ x‖ ≤ ‖φ x₀‖ + ‖φ x - φ x₀‖ := by
    have hle := norm_sub_norm_le (φ x) (φ x₀)
    linarith
  linarith

/-- `accel` along `(x, v) ↦ accel (g x) (Dg x) v` is locally quadratic in `v`: the main
estimate behind `HasFDerivAt`-with-zero-derivative at a rest point. -/
lemma expRest_local_sq_bound (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (x₀ : E) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ h : E × E, ‖h‖ < ρ →
        ‖accel (g (x₀ + h.1)) (fderiv ℝ g (x₀ + h.1)) h.2‖ ≤ C * ‖h‖ ^ 2 := by
  have hcdf1 : ContDiff ℝ 1 (fderiv ℝ g) :=
    hg.fderiv_right (m := 1) (by norm_num : (1 : ℕ∞ω) + 1 ≤ 3)
  have hcdfcont : Continuous (fderiv ℝ g) := hcdf1.continuous
  have hinvCa : ContinuousAt (fun gx : Bilin E =>
      (ContinuousLinearMap.inverse gx : (E →L[ℝ] ℝ) →L[ℝ] E)) (g x₀) := by
    have hinvAt : ContDiffAt ℝ 1 (fun gx : Bilin E =>
        (ContinuousLinearMap.inverse gx : (E →L[ℝ] ℝ) →L[ℝ] E)) (g x₀) :=
      ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse
        (𝕜 := ℝ) (E := E) (F := E →L[ℝ] ℝ) (n := 1) (hinv x₀)
    exact hinvAt.continuousAt
  have hgca : ContinuousAt g x₀ := hg.continuous.continuousAt
  let φ₂ : E → (E →L[ℝ] ℝ) →L[ℝ] E := fun x =>
    (ContinuousLinearMap.inverse (g x) : (E →L[ℝ] ℝ) →L[ℝ] E)
  have hφ₂ : ContinuousAt φ₂ x₀ := by
    exact ContinuousAt.comp (f := fun x : E => g x) (g := fun gx : Bilin E =>
      (ContinuousLinearMap.inverse gx : (E →L[ℝ] ℝ) →L[ℝ] E)) hinvCa hgca
  rcases expRest_norm_bound_near (fderiv ℝ g) x₀ hcdfcont.continuousAt with ⟨δA, hδA, hA⟩
  rcases expRest_norm_bound_near φ₂ x₀ hφ₂ with ⟨δB, hδB, hB⟩
  let C1 : ℝ := ‖fderiv ℝ g x₀‖ + 1
  let C2 : ℝ := ‖φ₂ x₀‖ + 1
  let C : ℝ := (C1 * C2) * 2
  refine ⟨min δA δB, lt_min hδA hδB, C, by positivity, ?_⟩
  intro h hh
  have hnorm : ‖h‖ < min δA δB := by simpa [dist_eq_norm] using hh
  have h1le : ‖h.1‖ < δA := lt_of_le_of_lt (norm_fst_le h) (lt_of_lt_of_le hnorm (min_le_left δA δB))
  have h2le : ‖h.1‖ < δB := lt_of_le_of_lt (norm_fst_le h) (lt_of_lt_of_le hnorm (min_le_right δA δB))
  have hA' : ‖fderiv ℝ g (x₀ + h.1)‖ ≤ C1 := by
    have hx : ‖(x₀ + h.1) - x₀‖ < δA := by simpa using h1le
    simpa [C1] using hA (x₀ + h.1) hx
  have hB' : ‖φ₂ (x₀ + h.1)‖ ≤ C2 := by
    have hx : ‖(x₀ + h.1) - x₀‖ < δB := by simpa using h2le
    simpa [C2] using hB (x₀ + h.1) hx
  have hab := expRest_accel_bound g (x₀ + h.1) h.2
  have hB2 : ‖h.2‖ ^ 2 ≤ ‖h‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg h.2) (norm_snd_le h) 2
  calc
    ‖accel (g (x₀ + h.1)) (fderiv ℝ g (x₀ + h.1)) h.2‖
        ≤ ‖(ContinuousLinearMap.inverse (g (x₀ + h.1)))‖ * (‖fderiv ℝ g (x₀ + h.1)‖ * ‖h.2‖ ^ 2) * 2 := hab
    _ ≤ (C2) * (C1 * ‖h.2‖ ^ 2) * 2 := by
      have hφ : ‖φ₂ (x₀ + h.1)‖ = ‖(ContinuousLinearMap.inverse (g (x₀ + h.1)))‖ := by rfl
      rw [hφ]
      gcongr
    _ ≤ (C2) * (C1 * ‖h‖ ^ 2) * 2 := by
      gcongr
    _ = ((C1 * C2) * 2) * ‖h‖ ^ 2 := by ring
    _ = C * ‖h‖ ^ 2 := by rfl

/-- A quadratic local bound implies little-o of the norm. -/
lemma expRest_isLittleO_of_norm_sq_bound {ρ C : ℝ} (hρ : 0 < ρ) (hC : 0 < C)
    {f : E × E → E}
    (hbound : ∀ h : E × E, ‖h‖ < ρ → ‖f h‖ ≤ C * ‖h‖ ^ 2) :
    f =o[𝓝 (0 : E × E)] (fun h : E × E => h) := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hδ : 0 < min ρ (c / C) := lt_min hρ (div_pos hc hC)
  refine Metric.eventually_nhds_iff.mpr ⟨min ρ (c / C), hδ, ?_⟩
  intro h hh
  have hnorm : ‖h‖ < min ρ (c / C) := by simpa [dist_eq_norm] using hh
  have hltρ : ‖h‖ < ρ := lt_of_lt_of_le hnorm (min_le_left ρ (c / C))
  have hltc : ‖h‖ < c / C := lt_of_lt_of_le hnorm (min_le_right ρ (c / C))
  have hb := hbound h hltρ
  have hCf : C * ‖h‖ ≤ c := by
    have hmul : C * ‖h‖ < c := by
      have hm := mul_lt_mul_of_pos_left hltc hC
      have hcc : C * (c / C) = c := by field_simp [ne_of_gt hC]
      nlinarith
    exact le_of_lt hmul
  calc
    ‖f h‖ ≤ C * ‖h‖ ^ 2 := hb
    _ ≤ c * ‖h‖ := by
      have h1 : C * ‖h‖ ^ 2 ≤ c * ‖h‖ := by
        calc
          C * ‖h‖ ^ 2 = (C * ‖h‖) * ‖h‖ := by ring
          _ ≤ c * ‖h‖ := mul_le_mul_of_nonneg_right hCf (norm_nonneg h)
      exact h1

/-- Along a path through the rest point the acceleration map is `o(‖h‖)`. -/
lemma expRest_isLittleO (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (x₀ : E) :
    (fun h : E × E => accel (g (x₀ + h.1)) (fderiv ℝ g (x₀ + h.1)) h.2)
      =o[𝓝 (0 : E × E)] (fun h : E × E => h) := by
  rcases expRest_local_sq_bound g hg hinv x₀ with ⟨ρ, hρ, C, hC, hb⟩
  exact expRest_isLittleO_of_norm_sq_bound hρ hC hb

/-- The second component of the field has zero derivative at a rest point. -/
lemma expRest_hasFDerivAt_zero (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (x₀ : E) :
    HasFDerivAt (fun z : E × E => accel (g z.1) (fderiv ℝ g z.1) z.2)
      (0 : (E × E) →L[ℝ] E) (x₀, 0) := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  let F1 : E × E → E := fun h =>
    accel (g ((x₀, 0) + h).1) (fderiv ℝ g ((x₀, 0) + h).1) ((x₀, 0) + h).2
      - accel (g (x₀, 0).1) (fderiv ℝ g (x₀, 0).1) (x₀, 0).2
      - (0 : (E × E) →L[ℝ] E) h
  let F2 : E × E → E := fun h =>
    accel (g (x₀ + h.1)) (fderiv ℝ g (x₀ + h.1)) h.2
  have hpt : ∀ h : E × E, F2 h = F1 h := by
    intro h
    simp [F1, F2, expRest_accel_zero]
  exact Asymptotics.IsLittleO.congr (expRest_isLittleO g hg hinv x₀) hpt (fun h => rfl)

/-- The Fréchet derivative of the geodesic field at a rest point is `δ ↦ (δ.2, 0)`. -/
lemma fderiv_odeField_rest (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (x₀ : E) (δ : E × E) :
    fderiv ℝ (odeField g) (x₀, 0) δ = (δ.2, 0) := by
  let snd : (E × E) →L[ℝ] E := ContinuousLinearMap.snd ℝ E E
  let W : (E × E) →L[ℝ] (E × E) := snd.prod (0 : (E × E) →L[ℝ] E)
  have h1 : HasFDerivAt (fun z : E × E => z.2) snd (x₀, 0) := by
    simpa [snd] using ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.snd ℝ E E)
  have h2 : HasFDerivAt (fun z : E × E => accel (g z.1) (fderiv ℝ g z.1) z.2)
      (0 : (E × E) →L[ℝ] E) (x₀, 0) :=
    expRest_hasFDerivAt_zero g hg hinv x₀
  have hboth : HasFDerivAt (fun z : E × E => (z.2, accel (g z.1) (fderiv ℝ g z.1) z.2)) W (x₀, 0) := by
    simpa [W] using HasFDerivAt.prodMk h1 h2
  have hode : HasFDerivAt (odeField g) W (x₀, 0) := by
    refine HasFDerivAt.congr_of_eventuallyEq hboth ?_
    refine Filter.Eventually.of_forall (fun z : E × E => ?_)
    unfold odeField
    rfl
  have hfd : fderiv ℝ (odeField g) (x₀, 0) = W := hode.fderiv
  have hWδ : W δ = (δ.2, 0) := by
    simp [W, snd]
  simpa [hfd] using hWδ

end

end Submission.Model
