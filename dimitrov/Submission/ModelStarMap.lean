import Mathlib
import Submission.Commons.Analysis.Real.rpow_prod_eq_prod_rpow

/-!
# ModelStarMap -- the explicit Eremenko model map: norm/boundary identities
# (SESSION-8 milestone (a); machine-verified "easy half" shell)

For |z_k| = 1 distinct and r_k ≥ 0 with Σ_k r_k = 1, the model map of the
exterior disk onto a hedgehog complement is (EremenkoConverse.lean header,
SESSION-8 corrected form)

    F(z) := z · ∏_k (1 - z_k·z^{-1})^(2 r_k)         (|z| > 1)

with each power (1-w)^(2 r_k) := exp(2 r_k · Log(1-w)) the principal power
(the base lies in the slit plane for |z_k z^{-1}| < 1).  Eremenko's product
∏_k ((z-z_k)(z^{-1}-z̄_k))^{r_k} equals z·C·∏_k (1 - z_k z^{-1})^(2 r_k),
C := ∏_k (-z̄_k)^{r_k} with ‖C‖ = 1, so all norm identities below hold for
the normalised map irrespective of the phase C.

PROVED here (all axiom-clean, 0 sorries):
  * `norm_cpow_real`: ‖w ^ (t : ℂ)‖ = ‖w‖ ^ t for real t (reusable);
  * factor norm identities: ‖1 - a·z⁻¹‖ = ‖z - a‖ on the unit circle and
    = ‖z - a‖ / ‖z‖ in general; the factor base is in the slit plane;
  * BOUNDARY identity: for ‖z‖ = 1 (z ≠ z_k for all k):
        ‖modelF z‖ = ∏_k ‖z - z_k‖^(2 r_k);
    (together with the PROVED KL bridge
    Submission.ModelStar.max_product_ge_four_rpow_inv this gives
    max over the circle of ‖modelF‖ ≥ 4^(1/s): a capacity-1 model star has
    a spike of length ≥ 4^(1/s) -- the sharp Dubinin constant; the missing
    link "model star spikes are the arc maxima of ‖modelF‖" is the folded
    boundary correspondence, an open target);
  * EXTERIOR identity (SESSION-8 corrected E4 form, needs Σ_k r_k = 1):
        ‖modelF z‖ = (∏_k ‖z - z_k‖^(2 r_k)) / ‖z‖      for 1 < ‖z‖.
NOT YET formalised HERE: holomorphy of `modelF` on the exterior, the
asymptotic ‖modelF z‖/‖z‖ → 1 at ∞, and the capacity-one normalization
`modelF z / z → 1` are PROVED in `Submission.ModelStarShell` (module
`Submission.ModelStarShell`, which imports this one); still open there:
conformality (injectivity) of `modelF` on the exterior and the folded
boundary correspondence (arg F constant on arcs between consecutive `z_k`,
spike tips = arc maxima of ‖F‖).
-/

noncomputable section

open scoped Real BigOperators Topology
open Filter Set

namespace Submission.ModelStarMap

open Complex

/-- The factor `(1 - a·z⁻¹)^(t)` of the model map. -/
def modelFactor (a : ℂ) (t : ℝ) (z : ℂ) : ℂ :=
  (1 - a * z⁻¹) ^ (t : ℂ)

/-- The full product `∏_k (1 - z_k·z^{-1})^(2 r_k)`. -/
def modelProduct {n : ℕ} (z₀ : Fin n → ℂ) (r : Fin n → ℝ) (z : ℂ) : ℂ :=
  ∏ k : Fin n, modelFactor (z₀ k) (2 * r k) z

/-- The model map `F(z) = z · modelProduct z₀ r z`. -/
def modelF {n : ℕ} (z₀ : Fin n → ℂ) (r : Fin n → ℝ) (z : ℂ) : ℂ :=
  z * modelProduct z₀ r z

/-! ## Norm of a complex power with real exponent (reusable) -/

/-- `‖w ^ (t : ℂ)‖ = ‖w‖ ^ t` for a real exponent `t` (both sides use the
convention `0^0 = 1`). -/
lemma norm_cpow_real {w : ℂ} {t : ℝ} : ‖w ^ (t : ℂ)‖ = ‖w‖ ^ t := by
  by_cases hw : w = 0
  · subst w
    by_cases ht : t = 0
    · subst t
      simp
    · simp [cpow_def, ht]
  · rw [cpow_def_of_ne_zero hw, norm_exp]
    have hre : (log w * (t : ℂ)).re = Real.log ‖w‖ * t := by
      rw [mul_re, log_re, ofReal_im, ofReal_re]
      ring
    rw [hre]
    have hnpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
    exact (Real.rpow_def_of_pos hnpos t).symm

/-- A fixed nonnegative base raised to a sum of exponents is the product of
the powers (base strictly positive). -/
private lemma prod_rpow_same_base {ι : Type*} [Fintype ι] (x : ℝ) (e : ι → ℝ)
    (hx : 0 < x) : (∏ i : ι, x ^ e i) = x ^ (∑ i : ι, e i) := by
  classical
  have hmain : ∀ t : Finset ι, (∏ i ∈ t, x ^ e i) = x ^ (∑ i ∈ t, e i) := by
    intro t
    refine Finset.induction_on t ?_ ?_
    · simp
    · intro a u hau ih
      rw [Finset.prod_insert hau, Finset.sum_insert hau, Real.rpow_add hx, ih]
  simpa using hmain Finset.univ

/-! ## The factor: slit-plane membership and norm identities -/

/-- `1 - a·z⁻¹` has positive real part when `‖a‖ < ‖z‖`. -/
lemma factor_re_pos {a : ℂ} {z : ℂ} (haz : ‖a‖ < ‖z‖) :
    0 < (1 - a * z⁻¹).re := by
  have hnorm : ‖a * z⁻¹‖ < 1 := by
    calc
      ‖a * z⁻¹‖ = ‖a‖ * ‖z⁻¹‖ := by rw [norm_mul]
      _ = ‖a‖ / ‖z‖ := by
        rw [norm_inv]
        ring
      _ < 1 := by
        exact (div_lt_one (lt_of_le_of_lt (norm_nonneg a) haz)).2 haz
  have hre : (1 - a * z⁻¹).re = 1 - (a * z⁻¹).re := by simp
  rw [hre]
  have hrele : (a * z⁻¹).re ≤ ‖a * z⁻¹‖ := Complex.re_le_norm _
  linarith

/-- The factor base lies in the slit plane for `‖a‖ < ‖z‖`. -/
lemma factor_mem_slitPlane {a : ℂ} {z : ℂ} (haz : ‖a‖ < ‖z‖) :
    1 - a * z⁻¹ ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  exact Or.inl (factor_re_pos haz)

/-- Norm of the model factor. -/
lemma norm_modelFactor {a : ℂ} {t : ℝ} {z : ℂ} : ‖modelFactor a t z‖ = ‖1 - a * z⁻¹‖ ^ t := by
  unfold modelFactor
  exact norm_cpow_real

/-- `1 - a·z^{-1} = z^{-1}·(z - a)` (pure algebra). -/
lemma factor_eq_inv_mul {a z : ℂ} (hz : z ≠ 0) : 1 - a * z⁻¹ = z⁻¹ * (z - a) := by
  field_simp [hz]

/-- On the unit circle: `‖1 - a·z^{-1}‖ = ‖z - a‖` for `‖z‖ = 1`. -/
lemma norm_factor_unit {a z : ℂ} (hz : ‖z‖ = 1) : ‖1 - a * z⁻¹‖ = ‖z - a‖ := by
  have hz0 : z ≠ 0 := by
    intro hz0
    rw [hz0, norm_zero] at hz
    norm_num at hz
  rw [factor_eq_inv_mul hz0, norm_mul, norm_inv]
  calc
    ‖z‖⁻¹ * ‖z - a‖ = ‖z - a‖ := by rw [hz]; norm_num

/-- For `z ≠ 0`: `‖1 - a·z^{-1}‖ = ‖z - a‖ / ‖z‖`. -/
lemma norm_factor_div {a z : ℂ} (hz : z ≠ 0) : ‖1 - a * z⁻¹‖ = ‖z - a‖ / ‖z‖ := by
  rw [factor_eq_inv_mul hz, norm_mul, norm_inv, div_eq_mul_inv]
  ring

/-! ## Boundary and exterior norm identities for the model map -/

/-- The norm of the product factors through the factors. -/
lemma norm_modelProduct {n : ℕ} (z₀ : Fin n → ℂ) (r : Fin n → ℝ) (z : ℂ) :
    ‖modelProduct z₀ r z‖ = ∏ k : Fin n, ‖1 - z₀ k * z⁻¹‖ ^ (2 * r k) := by
  unfold modelProduct
  rw [norm_prod]
  refine Finset.prod_congr rfl ?_
  intro k hk
  exact norm_modelFactor

/-- **Boundary identity.**  On the unit circle (away from the `z_k`),
`‖modelF z‖ = ∏_k ‖z - z_k‖^(2 r_k)`. -/
theorem norm_modelF_unit {n : ℕ} (z₀ : Fin n → ℂ) (r : Fin n → ℝ)
    {z : ℂ} (hz : ‖z‖ = 1) :
    ‖modelF z₀ r z‖ = ∏ k : Fin n, ‖z - z₀ k‖ ^ (2 * r k) := by
  unfold modelF
  rw [norm_mul, hz, norm_modelProduct]
  have hsum : (∏ k : Fin n, ‖z - z₀ k‖ ^ (2 * r k)) =
      (∏ k : Fin n, ‖1 - z₀ k * z⁻¹‖ ^ (2 * r k)) := by
    refine Finset.prod_congr rfl ?_
    intro k hk
    congr 1
    exact (norm_factor_unit (a := z₀ k) hz).symm
  rw [hsum]
  simp

/-- **Exterior identity** (SESSION-8 corrected E4 form).  For `1 < ‖z‖`
and `Σ_k r_k = 1`:
`‖modelF z‖ = (∏_k ‖z - z₀ k‖^(2 r_k)) / ‖z‖`. -/
theorem norm_modelF_exterior {n : ℕ} (z₀ : Fin n → ℂ) (r : Fin n → ℝ)
    (hsum : (∑ k : Fin n, r k) = 1) {z : ℂ} (hz : 1 < ‖z‖) :
    ‖modelF z₀ r z‖ = (∏ k : Fin n, ‖z - z₀ k‖ ^ (2 * r k)) / ‖z‖ := by
  have hz0 : z ≠ 0 := by
    intro hz0
    rw [hz0, norm_zero] at hz
    norm_num at hz
  have hnz : 0 < ‖z‖ := lt_trans zero_lt_one hz
  have hexp : (∑ k : Fin n, 2 * r k) = 2 := by
    rw [← Finset.mul_sum, hsum]
    ring
  unfold modelF
  rw [norm_mul, norm_modelProduct]
  let P : ℝ := ∏ k : Fin n, ‖z - z₀ k‖ ^ (2 * r k)
  have hfac : ∀ k : Fin n, ‖1 - z₀ k * z⁻¹‖ ^ (2 * r k) =
      (‖z - z₀ k‖ ^ (2 * r k)) / (‖z‖ ^ (2 * r k)) := by
    intro k
    rw [norm_factor_div hz0, Real.div_rpow (norm_nonneg (z - z₀ k)) (le_of_lt hnz)]
  calc
    ‖z‖ * ∏ k : Fin n, ‖1 - z₀ k * z⁻¹‖ ^ (2 * r k)
        = ‖z‖ * ∏ k : Fin n, (‖z - z₀ k‖ ^ (2 * r k)) / (‖z‖ ^ (2 * r k)) := by
            rw [Finset.prod_congr rfl (fun k hk => hfac k)]
    _ = ‖z‖ * ((∏ k : Fin n, ‖z - z₀ k‖ ^ (2 * r k)) /
          (∏ k : Fin n, ‖z‖ ^ (2 * r k))) := by
            rw [Finset.prod_div_distrib]
    _ = ‖z‖ * (P / (‖z‖ ^ (∑ k : Fin n, 2 * r k))) := by
            rw [prod_rpow_same_base ‖z‖ (fun k : Fin n => 2 * r k) hnz]
    _ = ‖z‖ * (P / (‖z‖ ^ (2 : ℝ))) := by
            rw [hexp]
    _ = P / ‖z‖ := by
            have hz2 : ‖z‖ ^ (2 : ℝ) = ‖z‖ * ‖z‖ := by
              rw [Real.rpow_two]
              ring
            rw [hz2]
            field_simp [ne_of_gt hnz]
