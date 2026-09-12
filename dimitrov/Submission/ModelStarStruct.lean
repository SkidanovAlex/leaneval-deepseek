import Mathlib
import Submission.ModelStarMap

/-!
# ModelStarStruct -- the exterior-map structure of the Eremenko model star

For distinct unit points `z₀ k` and positive weights `r k` with `Σ r k = 1`
the model map is `modelF z₀ r z = z · ∏_k (1 - z₀ k·z⁻¹)^(2 r k)`.
This module develops the analytic structure of `modelF` needed to identify
it with the exterior (Riemann) map of the model star `M := modelF '' {‖z‖=1}`:

* logarithmic representation `modelF = z · exp (Σ_k 2r_k log (1 - z₀k z⁻¹))`;
* logarithmic-derivative identity `deriv modelF z = modelF z · H z / z`
  with `H z = Σ_k r_k (z + z₀k)/(z - z₀k)`;
* the KEY fact `H z = 0` has NO solution with `‖z‖ ≠ 1` (the real part is
  `(‖z‖²-1)·Σ_k r_k/‖z-z₀k‖²`);
* finiteness of the critical set `{ζ : ‖ζ‖ = 1, deriv modelF ζ = 0}` via the
  explicit polynomial `Q z = ∏_j (z-z₀j)·H z` of degree `n`.

These are the inputs of the "no exterior preimage of a boundary point"
theorem (the exterior map does not meet its own boundary), the analytic
content of `ModelStarMap`'s open "folded boundary correspondence".
-/

noncomputable section
open scoped Real BigOperators Topology
open Filter Set

namespace Submission.ModelStarStruct

open Submission.ModelStarMap

/-- `L(z) = Σ_k (2 r_k) · log (1 - z₀ k · z⁻¹)`. -/
def logSum {n : ℕ} (z₀ : Fin n → ℂ) (r : Fin n → ℝ) (z : ℂ) : ℂ :=
  ∑ k : Fin n, ((2 * r k : ℝ) : ℂ) * Complex.log (1 - z₀ k * z⁻¹)

/-- `H(z) = Σ_k r_k (z + z₀ k)/(z − z₀ k)`: the numerator of the
logarithmic derivative of `modelF`. -/
def H {n : ℕ} (z₀ : Fin n → ℂ) (r : Fin n → ℝ) (z : ℂ) : ℂ :=
  ∑ k : Fin n, (r k : ℂ) * ((z + z₀ k) / (z - z₀ k))

/-! ## §1  Logarithmic representation -/

lemma one_sub_mul_inv_ne_zero {a z : ℂ} (hz : z ≠ 0) (hz' : z ≠ a) :
    1 - a * z⁻¹ ≠ 0 := by
  intro h
  apply hz'
  have h' : a * z⁻¹ = 1 := (sub_eq_zero.mp h).symm
  calc z = z * 1 := by ring
    _ = z * (a * z⁻¹) := by rw [h']
    _ = a := by field_simp

lemma modelFactor_eq_exp {a : ℂ} {t : ℝ} {z : ℂ} (hz : z ≠ 0) (ha : z ≠ a) :
    modelFactor a t z = Complex.exp ((t : ℂ) * Complex.log (1 - a * z⁻¹)) := by
  unfold modelFactor
  rw [Complex.cpow_def_of_ne_zero (one_sub_mul_inv_ne_zero hz ha),
    mul_comm (Complex.log _) ((t : ℝ) : ℂ)]

lemma modelF_eq_exp {n : ℕ} (z₀ : Fin n → ℂ) (r : Fin n → ℝ) {z : ℂ}
    (hz0 : z ≠ 0) (hz : ∀ k, z ≠ z₀ k) :
    modelF z₀ r z = z * Complex.exp (logSum z₀ r z) := by
  unfold modelF modelProduct logSum
  rw [Finset.prod_congr rfl
    (fun k _ => modelFactor_eq_exp (a := z₀ k) (t := 2 * r k) hz0 (hz k))]
  rw [← Complex.exp_sum]

/-- The junctions are avoided eventually. -/
lemma eventually_off_junctions {n : ℕ} (z₀ : Fin n → ℂ) {z : ℂ} (hz : ∀ k, z ≠ z₀ k) :
    ∀ᶠ w in 𝓝 z, ∀ k : Fin n, w ≠ z₀ k := by
  rw [Filter.eventually_all]
  exact fun k => isOpen_ne.mem_nhds (hz k)

/-- `modelF =ᶠ z · exp (logSum)` near a point off the junctions and the origin. -/
lemma modelF_eventuallyEq {n : ℕ} (z₀ : Fin n → ℂ) (r : Fin n → ℝ) {z : ℂ}
    (hz0 : z ≠ 0) (hz : ∀ k, z ≠ z₀ k) :
    (fun w : ℂ => modelF z₀ r w) =ᶠ[𝓝 z] (fun w => w * Complex.exp (logSum z₀ r w)) := by
  filter_upwards [isOpen_ne.mem_nhds hz0, eventually_off_junctions z₀ hz] with w hw0 hwk
  exact modelF_eq_exp z₀ r hw0 hwk

/-! ## §2  Derivative of the log-sum and of `modelF` -/

/-- Derivative of `z ↦ log (1 - a·z⁻¹)`. -/
lemma hasDerivAt_log_one_sub {a z : ℂ} (hz : z ≠ 0)
    (hp : 1 - a * z⁻¹ ∈ Complex.slitPlane) :
    HasDerivAt (fun w : ℂ => Complex.log (1 - a * w⁻¹)) (a / (z * (z - a))) z := by
  have hc : HasDerivAt (fun w : ℂ => w⁻¹) (-(z ^ 2)⁻¹) z := hasDerivAt_inv hz
  have h1 : HasDerivAt (fun w : ℂ => a * w⁻¹) (a * (-(z ^ 2)⁻¹)) z := hc.const_mul a
  have h3 : HasDerivAt (fun w : ℂ => 1 - a * w⁻¹) (0 - a * (-(z ^ 2)⁻¹)) z :=
    (hasDerivAt_const (x := z) (c := (1 : ℂ))).sub h1
  have h4 : HasDerivAt (fun w : ℂ => 1 - a * w⁻¹) (a * (z ^ 2)⁻¹) z := by
    convert h3 using 1
    ring
  have h5 := (Complex.hasDerivAt_log hp).comp z h4
  have hval : (1 - a * z⁻¹)⁻¹ * (a * (z ^ 2)⁻¹) = a / (z * (z - a)) := by
    field_simp
  rw [← hval]
  exact h5

/-- Derivative of the log-sum. -/
lemma hasDerivAt_logSum {n : ℕ} (z₀ : Fin n → ℂ) (r : Fin n → ℝ) {z : ℂ}
    (hz : z ≠ 0) (hsp : ∀ k, 1 - z₀ k * z⁻¹ ∈ Complex.slitPlane) :
    HasDerivAt (logSum z₀ r)
      (∑ k : Fin n, ((2 * r k : ℝ) : ℂ) * (z₀ k / (z * (z - z₀ k)))) z := by
  unfold logSum
  refine HasDerivAt.fun_sum ?_
  intro k _
  have hk := (hasDerivAt_log_one_sub (a := z₀ k) hz (hsp k)).const_mul ((2 * r k : ℝ) : ℂ)
  simpa [mul_assoc] using hk

lemma summand_identity {z a c : ℂ} (h : z ≠ a) :
    c + (2 * c) * (a / (z - a)) = c * ((z + a) / (z - a)) := by
  field_simp
  ring

/-- **Algebraic identity** `1 + z·L'(z) = H(z)` for `z ≠ 0` and `Σ r_k = 1`. -/
lemma one_add_mul_sum_eq_H {n : ℕ} (z₀ : Fin n → ℂ) (r : Fin n → ℝ) {z : ℂ}
    (hz : z ≠ 0) (hz' : ∀ k, z ≠ z₀ k) (hsum : (∑ k : Fin n, r k) = 1) :
    1 + z * (∑ k : Fin n, ((2 * r k : ℝ) : ℂ) * (z₀ k / (z * (z - z₀ k)))) =
      H z₀ r z := by
  have hprod : ∀ k : Fin n,
      z * (((2 * r k : ℝ) : ℂ) * (z₀ k / (z * (z - z₀ k)))) =
        ((2 * r k : ℝ) : ℂ) * (z₀ k / (z - z₀ k)) := by
    intro k
    field_simp
  have hone : (1 : ℂ) = ∑ k : Fin n, (r k : ℂ) := by
    have h : (∑ k : Fin n, (r k : ℂ)) = ((∑ k : Fin n, r k : ℝ) : ℂ) := by push_cast; rfl
    rw [h, hsum]; norm_num
  rw [Finset.mul_sum, Finset.sum_congr rfl (fun k _ => hprod k), hone, H,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [show ((2 * r k : ℝ) : ℂ) = 2 * (r k : ℂ) from by push_cast; ring]
  exact summand_identity (hz' k)

/-- **Log-derivative of `modelF`.** -/
lemma hasDerivAt_modelF {n : ℕ} (z₀ : Fin n → ℂ) (r : Fin n → ℝ) {z : ℂ}
    (hz : z ≠ 0) (hz' : ∀ k, z ≠ z₀ k)
    (hsp : ∀ k, 1 - z₀ k * z⁻¹ ∈ Complex.slitPlane)
    (hsum : (∑ k : Fin n, r k) = 1) :
    HasDerivAt (fun w : ℂ => modelF z₀ r w) (modelF z₀ r z * H z₀ r z / z) z := by
  set S : ℂ := ∑ k : Fin n, ((2 * r k : ℝ) : ℂ) * (z₀ k / (z * (z - z₀ k))) with hS
  have hL := hasDerivAt_logSum z₀ r hz hsp
  have hExp : HasDerivAt (fun w : ℂ => Complex.exp (logSum z₀ r w))
      (Complex.exp (logSum z₀ r z) * S) z := hL.cexp
  have hMul := (hasDerivAt_id z).mul hExp
  have hval : 1 * Complex.exp (logSum z₀ r z) + z * (Complex.exp (logSum z₀ r z) * S)
      = modelF z₀ r z * H z₀ r z / z := by
    have h1 : 1 * Complex.exp (logSum z₀ r z) + z * (Complex.exp (logSum z₀ r z) * S)
        = Complex.exp (logSum z₀ r z) * (1 + z * S) := by ring
    rw [h1, hS, one_add_mul_sum_eq_H z₀ r hz hz' hsum, modelF_eq_exp z₀ r hz hz']
    field_simp
  have hMul' := hMul.congr_deriv hval
  refine hMul'.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_ne.mem_nhds hz, eventually_off_junctions z₀ hz'] with w hw0 hwk
  simpa only [Pi.mul_apply, id_eq] using (modelF_eq_exp z₀ r hw0 hwk)

/-- `deriv` form of the log-derivative identity. -/
lemma deriv_modelF {n : ℕ} (z₀ : Fin n → ℂ) (r : Fin n → ℝ) {z : ℂ}
    (hz : z ≠ 0) (hz' : ∀ k, z ≠ z₀ k)
    (hsp : ∀ k, 1 - z₀ k * z⁻¹ ∈ Complex.slitPlane)
    (hsum : (∑ k : Fin n, r k) = 1) :
    deriv (fun w : ℂ => modelF z₀ r w) z = modelF z₀ r z * H z₀ r z / z :=
  (hasDerivAt_modelF z₀ r hz hz' hsp hsum).deriv

/-! ## §3  The critical points lie on the unit circle -/

/-- For unit `w`: `Re ((z+w)/(z-w)) = (‖z‖²-1)/‖z-w‖²`. -/
lemma re_add_div_sub (z w : ℂ) (hw : ‖w‖ = 1) :
    ((z + w) / (z - w)).re = (‖z‖ ^ 2 - 1) / ‖z - w‖ ^ 2 := by
  have hwre : w.re * w.re + w.im * w.im = 1 := by
    have h := Complex.sq_norm w
    rw [hw, Complex.normSq_apply] at h
    norm_num at h
    linarith
  have hnum : (z + w).re * (z - w).re + (z + w).im * (z - w).im = ‖z‖ ^ 2 - 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.sub_re, Complex.add_im, Complex.sub_im]
    nlinarith [hwre]
  have hden : Complex.normSq (z - w) = ‖z - w‖ ^ 2 := Complex.normSq_eq_norm_sq (z - w)
  rw [Complex.div_re, ← add_div, hnum, hden]

/-- Real part of `H`. -/
lemma H_re {n : ℕ} (z₀ : Fin n → ℂ) (r : Fin n → ℝ)
    (hunit : ∀ k, ‖z₀ k‖ = 1) {z : ℂ} (hz : ∀ k, z ≠ z₀ k) :
    (H z₀ r z).re = (‖z‖ ^ 2 - 1) * ∑ k : Fin n, r k / ‖z - z₀ k‖ ^ 2 := by
  unfold H
  rw [Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    re_add_div_sub z (z₀ k) (hunit k)]
  ring

/-- **No critical point off the unit circle.**  For distinct unit points and
positive weights, `H z ≠ 0` whenever `‖z‖ ≠ 1`. -/
theorem H_ne_zero {n : ℕ} [NeZero n] (z₀ : Fin n → ℂ) (r : Fin n → ℝ)
    (hunit : ∀ k, ‖z₀ k‖ = 1) (hrpos : ∀ k, 0 < r k) {z : ℂ} (hz : ‖z‖ ≠ 1) :
    H z₀ r z ≠ 0 := by
  intro h
  have hz' : ∀ k, z ≠ z₀ k := by
    intro k hk
    exact hz (by rw [hk, hunit k])
  have hre := H_re z₀ r hunit hz'
  rw [h, Complex.zero_re] at hre
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty
  have hpos : 0 < ∑ k : Fin n, r k / ‖z - z₀ k‖ ^ 2 := by
    apply Finset.sum_pos
    · intro k _
      have hzk : 0 < ‖z - z₀ k‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hz' k))
      exact div_pos (hrpos k) (pow_pos hzk 2)
    · exact hne
  have hz2 : ‖z‖ ^ 2 - 1 ≠ 0 := by
    intro hh
    apply hz
    have : ‖z‖ ^ 2 = 1 := by linarith
    nlinarith [norm_nonneg z]
  exact (mul_ne_zero hz2 (ne_of_gt hpos)) hre.symm

end Submission.ModelStarStruct

namespace Submission.ModelStarStruct

open Submission.ModelStarMap

/-! ## §4  The slit-plane criterion on the closed exterior -/

/-- `1 - w` lies in the slit plane for `‖w‖ ≤ 1`, `w ≠ 1`. -/
lemma one_sub_mem_slitPlane {w : ℂ} (hw : ‖w‖ ≤ 1) (hw1 : w ≠ 1) :
    1 - w ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_contra h
  rw [not_or] at h
  obtain ⟨hre, him⟩ := h
  push_neg at hre
  have himw : w.im = 0 := by
    have : (1 - w).im = -w.im := by simp
    rw [this] at him
    simpa using him
  have hrew : 1 ≤ w.re := by
    have : (1 - w).re = 1 - w.re := by simp
    rw [this] at hre
    linarith
  have hnormw : ‖w‖ = w.re := by
    have h2 : ‖w‖ ^ 2 = w.re ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, himw]; ring
    nlinarith [norm_nonneg w, hrew]
  rw [hnormw] at hw
  have hwe : w.re = 1 := le_antisymm hw hrew
  apply hw1
  have : w = (w.re : ℂ) := Complex.ext (by simp) (by simp [himw])
  rw [this, hwe]; norm_num

/-- The model-map factor base lies in the slit plane at every point of the
closed exterior off the junctions. -/
lemma one_sub_mul_inv_mem_slitPlane {a z : ℂ} (ha : ‖a‖ = 1) (hz : 1 ≤ ‖z‖)
    (haz : z ≠ a) : 1 - a * z⁻¹ ∈ Complex.slitPlane := by
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; linarith
  have hnorm : ‖a * z⁻¹‖ = 1 / ‖z‖ := by
    rw [norm_mul, norm_inv, ha, one_mul, one_div]
  refine one_sub_mem_slitPlane ?_ ?_
  · rw [hnorm]
    exact (div_le_one (lt_of_lt_of_le zero_lt_one hz)).mpr hz
  · intro h
    apply haz
    have h1 : a * z⁻¹ = 1 := h
    have h2 : a = z := by
      calc a = a * z⁻¹ * z := by field_simp
        _ = 1 * z := by rw [h1]
        _ = z := one_mul z
    exact h2.symm

/-! ## §5  `modelF` does not vanish off the unit circle -/

lemma modelF_ne_zero {n : ℕ} (z₀ : Fin n → ℂ) (r : Fin n → ℝ) {z : ℂ}
    (hz0 : z ≠ 0) (hz : ∀ k, z ≠ z₀ k) : modelF z₀ r z ≠ 0 := by
  rw [modelF_eq_exp z₀ r hz0 hz]
  exact mul_ne_zero hz0 (Complex.exp_ne_zero _)

/-- `deriv modelF z = 0` iff `H z = 0` (off the junctions and the origin). -/
theorem deriv_modelF_eq_zero_iff {n : ℕ} (z₀ : Fin n → ℂ) (r : Fin n → ℝ) {z : ℂ}
    (hz : z ≠ 0) (hz' : ∀ k, z ≠ z₀ k)
    (hsp : ∀ k, 1 - z₀ k * z⁻¹ ∈ Complex.slitPlane)
    (hsum : (∑ k : Fin n, r k) = 1) :
    deriv (fun w : ℂ => modelF z₀ r w) z = 0 ↔ H z₀ r z = 0 := by
  rw [deriv_modelF z₀ r hz hz' hsp hsum, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · rcases mul_eq_zero.mp h with h1 | h2
      · exact absurd h1 (modelF_ne_zero z₀ r hz hz')
      · exact h2
    · exact absurd h hz
  · intro h; exact Or.inl (mul_eq_zero.mpr (Or.inr h))

/-! ## §6  Finiteness of the critical set on the unit circle -/

/-- The polynomial `Q(z) = ∏_j (z - z₀ j)·H(z) = Σ_k r_k (z+z₀k)∏_{j≠k}(z-z₀j)`. -/
def Qpoly {n : ℕ} (z₀ : Fin n → ℂ) (r : Fin n → ℝ) : Polynomial ℂ :=
  ∑ k : Fin n, Polynomial.C (r k : ℂ) * (Polynomial.X + Polynomial.C (z₀ k)) *
    ∏ j ∈ Finset.univ.erase k, (Polynomial.X - Polynomial.C (z₀ j))

lemma Qpoly_eval {n : ℕ} (z₀ : Fin n → ℂ) (r : Fin n → ℝ) (z : ℂ) :
    (Qpoly z₀ r).eval z =
      ∑ k : Fin n, (r k : ℂ) * (z + z₀ k) * ∏ j ∈ Finset.univ.erase k, (z - z₀ j) := by
  rw [Qpoly, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_prod]
  simp

lemma Qpoly_eval_eq_prod_mul_H {n : ℕ} (z₀ : Fin n → ℂ) (r : Fin n → ℝ) {z : ℂ}
    (hz : ∀ j, z ≠ z₀ j) :
    (Qpoly z₀ r).eval z = (∏ j, (z - z₀ j)) * H z₀ r z := by
  rw [Qpoly_eval, H, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hsplit : (∏ j, (z - z₀ j)) = (z - z₀ k) * ∏ j ∈ Finset.univ.erase k, (z - z₀ j) := by
    rw [← Finset.prod_erase_mul Finset.univ (fun j => z - z₀ j) (Finset.mem_univ k)]
    ring
  rw [hsplit]
  have hk : z - z₀ k ≠ 0 := sub_ne_zero.mpr (hz k)
  field_simp

/-- `Q` is not the zero polynomial (its value at `0` is `-∏ z₀ j ≠ 0`). -/
lemma Qpoly_ne_zero {n : ℕ} [NeZero n] (z₀ : Fin n → ℂ) (r : Fin n → ℝ)
    (hunit : ∀ k, ‖z₀ k‖ = 1) (hsum : (∑ k : Fin n, r k) = 1) : Qpoly z₀ r ≠ 0 := by
  intro hQ
  have h0 : ∀ j, (0 : ℂ) ≠ z₀ j := by
    intro j hj
    have := hunit j
    rw [← hj, norm_zero] at this
    norm_num at this
  have hval := Qpoly_eval_eq_prod_mul_H z₀ r h0
  rw [hQ] at hval
  simp only [Polynomial.eval_zero] at hval
  have hprod : (∏ j, ((0 : ℂ) - z₀ j)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact sub_ne_zero.mpr (h0 j)
  have hH0 : H z₀ r 0 = 0 := by
    rcases mul_eq_zero.mp hval.symm with h | h
    · exact absurd h hprod
    · exact h
  have hsumC : (∑ k : Fin n, (r k : ℂ)) = 1 := by
    have h : (∑ k : Fin n, (r k : ℂ)) = ((∑ k : Fin n, r k : ℝ) : ℂ) := by push_cast; rfl
    rw [h, hsum]; norm_num
  have hH0' : H z₀ r 0 = -1 := by
    have hinner : ∀ k : Fin n, (0 + z₀ k) / (0 - z₀ k) = (-1 : ℂ) := by
      intro k
      have hzk : z₀ k ≠ 0 := (h0 k).symm
      field_simp
      ring
    unfold H
    calc ∑ k : Fin n, (r k : ℂ) * ((0 + z₀ k) / (0 - z₀ k))
        = ∑ k : Fin n, (r k : ℂ) * (-1 : ℂ) :=
            Finset.sum_congr rfl (fun k _ => by rw [hinner k])
      _ = -(∑ k : Fin n, (r k : ℂ)) := by
            rw [← Finset.sum_neg_distrib]
            exact Finset.sum_congr rfl (fun k _ => by ring)
      _ = -1 := by rw [hsumC]
  rw [hH0'] at hH0
  norm_num at hH0

/-- The set of solutions of `H z = 0` on the unit circle is finite. -/
theorem finite_critical_set {n : ℕ} [NeZero n] (z₀ : Fin n → ℂ) (r : Fin n → ℝ)
    (hunit : ∀ k, ‖z₀ k‖ = 1) (hsum : (∑ k : Fin n, r k) = 1) :
    {ζ : ℂ | ‖ζ‖ = 1 ∧ H z₀ r ζ = 0}.Finite := by
  have hQ := Qpoly_ne_zero z₀ r hunit hsum
  refine Set.Finite.subset (Set.Finite.union (Polynomial.finite_setOf_isRoot hQ)
    (Set.finite_range z₀)) ?_
  intro ζ hζ
  obtain ⟨h1, h2⟩ := hζ
  by_cases hz : ∃ k, z₀ k = ζ
  · exact Or.inr (Set.mem_range.mpr hz)
  · left
    push_neg at hz
    show (Qpoly z₀ r).eval ζ = 0
    rw [Qpoly_eval_eq_prod_mul_H z₀ r (fun j h => hz j h.symm), h2, mul_zero]

end Submission.ModelStarStruct
