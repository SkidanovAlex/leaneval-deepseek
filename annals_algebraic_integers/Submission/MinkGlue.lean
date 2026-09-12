import Submission.MinkBox
import Submission.MinkEngine
import Submission.MinkVol
import Submission.MinkFinite
import Submission.MinkFlagBasis
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.Analysis.Convex.Body
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension

noncomputable section

open Polynomial
open scoped Real BigOperators ENNReal Pointwise
open MeasureTheory MeasureTheory.Measure Set

/-!
# Assembly: `MinkBox.minkUpper` from `mink_engine` and `vol_weighted_vandermonde`

Prove `Submission.MinkUpperGlue.minkUpper_proved : MinkBox.minkUpper` (take `C := 1`).

## Route

* (geometry) With `T := wvMap d α v` (toLin of the weighted Vandermonde matrix) and
  `B := wvBody = {x | ∀ k, |(T x) k| < 1} = {x | ‖T x‖ < 1}` (open, convex, symmetric,
  `0 ∈ B`, bounded), we have `volume.real B = 2^d / Dval d α v`
  (`vol_weighted_vandermonde`) and the gauge `g x := ‖T x‖` satisfies
  `z ∈ r • B ↔ g z < r` for `0 < r`.

* (greedy recursion) Build integer vectors `u i : ℤ^d` and positive scales
  `m i = g (u i)` such that with `W_k := span{u_j | j.val < k}`: for each `i`,
  `u i ∉ W_{i.val}` and every integer vector `z ∉ W_{i.val}` has `m i ≤ g z`
  (minimality ⇒ the flag property used by the engine).

* (adapted basis) There is a ℤ-basis `e_0..e_{d-1}` of the integer lattice with
  `span(e_0..e_{k-1}) = W_k` for every `k` (child lemma
  `Submission.MinkFlagBasis.exists_flag_basis`); the associated linear map
  `Φ (coord j) = e_j` is unimodular (`|det Φ| = 1`) and maps integer vectors
  to integer vectors.

* (engine) Apply `MinkEngine.mink_engine` to `B_eng := Φ ⁻¹' B` with scales `m`:
  the flag property `hP` follows from greedy minimality; `volume.real B_eng =
  volume.real B` by `|det Φ| = 1`.  Hence `∏ i, m i ≤ Dval d α v`.

* (polynomials) For each `i`, `Q i` is the integer polynomial whose coefficients
  are the integer vector `u i`.  Then `v k * |evalInt (Q i) (α k)| =
  |(T (u i)) k| ≤ g (u i) = m i`; with `mu := m`, `∏ mu ≤ Dval ≤ (d:ℝ)^d * Dval`.
-/

namespace Submission.MinkUpperGlue

open Submission.MinkBox
open Submission.MinkEngine

abbrev E (d : ℕ) := Fin d → ℝ

-- =====================================================================
--  Geometry of the weighted Vandermonde body
-- =====================================================================

/-- weighted Vandermonde linear map: `(T x) k = v k * ∑_j x j * (α k)^j`. -/
def wvMap (d : ℕ) (α : Fin d → ℝ) (v : Fin d → ℝ) : E d →ₗ[ℝ] E d :=
  Matrix.toLin' (MinkVol.wvMatrix d α v)

lemma wvMap_apply (d : ℕ) (α : Fin d → ℝ) (v : Fin d → ℝ) (x : E d) (k : Fin d) :
    wvMap d α v x k = v k * (∑ j : Fin d, x j * (α k) ^ j.val) := by
  unfold wvMap
  rw [Matrix.toLin'_apply]
  exact MinkVol.wvMatrix_mulVec_apply d α v x k

lemma wvMap_det (d : ℕ) (α : Fin d → ℝ) (v : Fin d → ℝ) :
    LinearMap.det (wvMap d α v) = (MinkVol.wvMatrix d α v).det := by
  unfold wvMap
  exact LinearMap.det_toLin' (MinkVol.wvMatrix d α v)

lemma wvMap_det_ne_zero (d : ℕ) {α : Fin d → ℝ} (hinj : Function.Injective α)
    {v : Fin d → ℝ} (hv : ∀ k : Fin d, 0 < v k) :
    LinearMap.det (wvMap d α v) ≠ 0 := by
  rw [wvMap_det, MinkVol.wvMatrix_det]
  refine mul_ne_zero ?_ ?_
  · exact ne_of_gt (Finset.prod_pos (fun k hk => hv k))
  · exact Matrix.det_vandermonde_ne_zero_iff.mpr hinj

/-- gauge (sup-norm of the image under `wvMap`) -/
def gauge (d : ℕ) (α : Fin d → ℝ) (v : Fin d → ℝ) (x : E d) : ℝ := ‖wvMap d α v x‖

lemma gauge_coord_le (d : ℕ) (α : Fin d → ℝ) (v : Fin d → ℝ) (x : E d) (k : Fin d) :
    |wvMap d α v x k| ≤ gauge d α v x := by
  unfold gauge
  exact norm_le_pi_norm (wvMap d α v x) k

lemma gauge_nonneg (d : ℕ) (α : Fin d → ℝ) (v : Fin d → ℝ) (x : E d) : 0 ≤ gauge d α v x := by
  unfold gauge
  exact norm_nonneg _

/-- The weighted Vandermonde body: strict preimage of the unit cube. -/
def wvBody (d : ℕ) (α : Fin d → ℝ) (v : Fin d → ℝ) : Set (E d) :=
  {x | ∀ k : Fin d, |wvMap d α v x k| < 1}

lemma wvBody_eq (d : ℕ) (α : Fin d → ℝ) (v : Fin d → ℝ) :
    wvBody d α v = {x : E d | ‖wvMap d α v x‖ < 1} := by
  ext x
  change (∀ k : Fin d, |wvMap d α v x k| < 1) ↔ ‖wvMap d α v x‖ < 1
  rw [pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)]
  simp

lemma smul_wvBody_eq (d : ℕ) (α : Fin d → ℝ) (v : Fin d → ℝ) (r : ℝ) (hr : 0 < r) :
    r • wvBody d α v = {x : E d | gauge d α v x < r} := by
  ext x
  rw [mem_smul_set]
  constructor
  · rintro ⟨b, hb, hbeq⟩
    change gauge d α v x < r
    rw [wvBody_eq] at hb
    change ‖wvMap d α v b‖ < 1 at hb
    have hx : x = r • b := hbeq.symm
    rw [hx]
    unfold gauge
    have hlin : wvMap d α v (r • b) = r • wvMap d α v b := by simp
    rw [hlin, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    simpa using (mul_lt_mul_of_pos_left hb hr)
  · intro hg
    change gauge d α v x < r at hg
    refine ⟨r⁻¹ • x, ?_, ?_⟩
    · rw [wvBody_eq]
      change ‖wvMap d α v (r⁻¹ • x)‖ < 1
      have hlin : wvMap d α v (r⁻¹ • x) = r⁻¹ • wvMap d α v x := by simp
      rw [hlin, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
      rw [← div_eq_inv_mul]
      exact (div_lt_one hr).mpr hg
    · rw [smul_smul]
      rw [mul_comm]
      rw [inv_mul_cancel₀ (ne_of_gt hr)]
      simp

lemma mem_smul_wvBody (d : ℕ) (α : Fin d → ℝ) (v : Fin d → ℝ) (x : E d) (r : ℝ) (hr : 0 < r) :
    x ∈ r • wvBody d α v ↔ gauge d α v x < r := by
  rw [smul_wvBody_eq d α v r hr]
  simp

lemma wvBody_isOpen (d : ℕ) (α : Fin d → ℝ) (v : Fin d → ℝ) :
    IsOpen (wvBody d α v) := by
  rw [wvBody_eq]
  have hcont : Continuous (fun x : E d => wvMap d α v x) :=
    (wvMap d α v).continuous_of_finiteDimensional
  have hEq : {x : E d | ‖wvMap d α v x‖ < 1} =
      (fun x : E d => wvMap d α v x) ⁻¹' (Metric.ball (0 : E d) 1) := by
    ext x
    change ‖wvMap d α v x‖ < 1 ↔ (fun y : E d => wvMap d α v y) x ∈ Metric.ball (0 : E d) 1
    simp [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg]
  rw [hEq]
  exact Metric.isOpen_ball.preimage hcont

lemma wvBody_convex (d : ℕ) (α : Fin d → ℝ) (v : Fin d → ℝ) :
    Convex ℝ (wvBody d α v) := by
  rw [wvBody_eq]
  have hEq : {x : E d | ‖wvMap d α v x‖ < 1} =
      (fun x : E d => wvMap d α v x) ⁻¹' (Metric.ball (0 : E d) 1) := by
    ext x
    change ‖wvMap d α v x‖ < 1 ↔ (fun y : E d => wvMap d α v y) x ∈ Metric.ball (0 : E d) 1
    simp [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg]
  rw [hEq]
  exact (convex_ball (0 : E d) 1).linear_preimage (wvMap d α v)

lemma wvBody_symm (d : ℕ) (α : Fin d → ℝ) (v : Fin d → ℝ) :
    ∀ x : E d, x ∈ wvBody d α v → -x ∈ wvBody d α v := by
  intro x hx
  rw [wvBody_eq] at hx ⊢
  change ‖wvMap d α v x‖ < 1 at hx
  change ‖wvMap d α v (-x)‖ < 1
  have hneg : wvMap d α v (-x) = -wvMap d α v x := by simp
  rw [hneg, norm_neg]
  exact hx

lemma wvBody_zero (d : ℕ) (α : Fin d → ℝ) (v : Fin d → ℝ) :
    (0 : E d) ∈ wvBody d α v := by
  rw [wvBody_eq]
  change ‖wvMap d α v (0 : E d)‖ < 1
  simp

/-- the inverse of `wvMap` as a continuous linear equivalence -/
def wvContEquiv (d : ℕ) {α : Fin d → ℝ} (hinj : Function.Injective α)
    {v : Fin d → ℝ} (hv : ∀ k : Fin d, 0 < v k) : E d ≃L[ℝ] E d :=
  (LinearMap.equivOfDetNeZero (wvMap d α v) (wvMap_det_ne_zero d hinj hv)).toContinuousLinearEquiv

/-- the continuous linear inverse of `wvMap` -/
def wvInv (d : ℕ) {α : Fin d → ℝ} (hinj : Function.Injective α)
    {v : Fin d → ℝ} (hv : ∀ k : Fin d, 0 < v k) : E d →L[ℝ] E d :=
  ((wvContEquiv d hinj hv).symm).toContinuousLinearMap

lemma wvContEquiv_apply (d : ℕ) {α : Fin d → ℝ} (hinj : Function.Injective α)
    {v : Fin d → ℝ} (hv : ∀ k : Fin d, 0 < v k) (x : E d) :
    wvContEquiv d hinj hv x = wvMap d α v x := by
  rfl

lemma wvBody_isBounded (d : ℕ) {α : Fin d → ℝ} (hinj : Function.Injective α)
    {v : Fin d → ℝ} (hv : ∀ k : Fin d, 0 < v k) :
    Bornology.IsBounded (wvBody d α v) := by
  rw [wvBody_eq]
  let Ts : E d →L[ℝ] E d := wvInv d hinj hv
  rw [isBounded_iff_forall_norm_le]
  refine ⟨‖Ts‖, ?_⟩
  intro x hx
  change ‖wvMap d α v x‖ < 1 at hx
  have hle : ‖Ts ((wvContEquiv d hinj hv) x)‖ ≤ ‖Ts‖ * ‖(wvContEquiv d hinj hv) x‖ :=
    ContinuousLinearMap.le_opNorm Ts ((wvContEquiv d hinj hv) x)
  calc
    ‖x‖ = ‖Ts ((wvContEquiv d hinj hv) x)‖ := by
      congr 1
      have hwv : wvMap d α v x = (wvContEquiv d hinj hv) x :=
        (wvContEquiv_apply d hinj hv x).symm
      simpa [Ts, wvInv, hwv] using (wvContEquiv d hinj hv).symm_apply_apply x
    _ ≤ ‖Ts‖ * ‖(wvContEquiv d hinj hv) x‖ := hle
    _ ≤ ‖Ts‖ * 1 := by
        apply mul_le_mul_of_nonneg_left (le_of_lt hx) (norm_nonneg _)
    _ = ‖Ts‖ := by rw [mul_one]

/-- the norm of a vector is controlled by its gauge (norm-equivalence, explicit constant) -/
lemma norm_le_gauge (d : ℕ) {α : Fin d → ℝ} (hinj : Function.Injective α)
    {v : Fin d → ℝ} (hv : ∀ k : Fin d, 0 < v k) (x : E d) :
    ‖x‖ ≤ ‖wvInv d hinj hv‖ * gauge d α v x := by
  let Ts : E d →L[ℝ] E d := wvInv d hinj hv
  have hle : ‖Ts ((wvContEquiv d hinj hv) x)‖ ≤ ‖Ts‖ * ‖(wvContEquiv d hinj hv) x‖ :=
    ContinuousLinearMap.le_opNorm Ts ((wvContEquiv d hinj hv) x)
  calc
    ‖x‖ = ‖Ts ((wvContEquiv d hinj hv) x)‖ := by
      congr 1
      have hwv : wvMap d α v x = (wvContEquiv d hinj hv) x :=
        (wvContEquiv_apply d hinj hv x).symm
      simpa [Ts, wvInv, hwv] using (wvContEquiv d hinj hv).symm_apply_apply x
    _ ≤ ‖Ts‖ * ‖(wvContEquiv d hinj hv) x‖ := hle
    _ = ‖wvInv d hinj hv‖ * gauge d α v x := by
      rfl

/-- the volume of the body is `2^d / Dval` -/
lemma vol_wvBody (d : ℕ) {α : Fin d → ℝ} (hinj : Function.Injective α)
    {v : Fin d → ℝ} (hv : ∀ k : Fin d, 0 < v k) :
    (MeasureTheory.volume : Measure (E d)).real (wvBody d α v) = (2 : ℝ) ^ d / Dval d α v := by
  have hEq : wvBody d α v =
      {x : E d | ∀ k : Fin d, |v k * (∑ j : Fin d, x j * (α k) ^ j.val)| < 1} := by
    ext x
    change (∀ k : Fin d, |wvMap d α v x k| < 1) ↔
        (∀ k : Fin d, |v k * (∑ j : Fin d, x j * (α k) ^ j.val)| < 1)
    simp [wvMap_apply]
  rw [hEq]
  exact MinkVol.vol_weighted_vandermonde d α v hinj hv

/-- `Dval` is positive -/
lemma Dval_pos (d : ℕ) {α : Fin d → ℝ} (hinj : Function.Injective α)
    {v : Fin d → ℝ} (hv : ∀ k : Fin d, 0 < v k) :
    0 < Dval d α v := by
  unfold Dval
  refine mul_pos (Finset.prod_pos (fun k hk => hv k)) ?_
  unfold pairProd
  refine Finset.prod_pos (fun i hi => ?_)
  refine Finset.prod_pos (fun j hj => ?_)
  have hne : α i ≠ α j := by
    have hj' := (Finset.mem_filter.mp hj).2
    exact hinj.ne (ne_of_lt hj')
  exact abs_pos.mpr (sub_ne_zero.mpr hne)

lemma Dval_ne_zero (d : ℕ) {α : Fin d → ℝ} (hinj : Function.Injective α)
    {v : Fin d → ℝ} (hv : ∀ k : Fin d, 0 < v k) :
    Dval d α v ≠ 0 := ne_of_gt (Dval_pos d hinj hv)

/-- preimage volume under an invertible linear map with |det| = 1 is unchanged -/
lemma vol_preimage_eq (d : ℕ) (Φ : E d →ₗ[ℝ] E d)
    (hdet : |LinearMap.det Φ| = 1) (hne : LinearMap.det Φ ≠ 0) (s : Set (E d)) :
    (volume : Measure (E d)).real (Φ ⁻¹' s) = (volume : Measure (E d)).real s := by
  have hvol := Measure.addHaar_preimage_linearMap (μ := (volume : Measure (E d))) (f := Φ) hne s
  rw [Measure.real_def, Measure.real_def]
  rw [hvol]
  rw [ENNReal.toReal_mul]
  rw [ENNReal.toReal_ofReal (abs_nonneg _)]
  rw [abs_inv, hdet]
  norm_num

/-- preimage volume scales by |det|⁻¹ -/
lemma vol_preimage_det (d : ℕ) (Φ : E d →ₗ[ℝ] E d) (hne : LinearMap.det Φ ≠ 0) (s : Set (E d)) :
    (volume : Measure (E d)).real (Φ ⁻¹' s) =
      |(LinearMap.det Φ)⁻¹| * (volume : Measure (E d)).real s := by
  have hvol := Measure.addHaar_preimage_linearMap (μ := (volume : Measure (E d))) (f := Φ) hne s
  rw [Measure.real_def, Measure.real_def]
  rw [hvol]
  rw [ENNReal.toReal_mul]
  rw [ENNReal.toReal_ofReal (abs_nonneg _)]

/-- finiteness of bounded integer points (discreteness of the standard lattice) -/
lemma finite_int_norm_le {d : ℕ} (R : ℝ) (hR : 0 ≤ R) :
    Set.Finite {z : E d | IntFun d z ∧ ‖z‖ ≤ R} := by
  simpa [IntFun, IntV] using MinkFinite.finite_int_norm_le d R hR

/-- finiteness: integer vectors with `wvMap`-gauge bounded by `R` -/
lemma finite_int_gauge_le {d : ℕ} {α : Fin d → ℝ} {v : Fin d → ℝ}
    (hinj : Function.Injective α) (hv : ∀ k : Fin d, 0 < v k)
    (R : ℝ) (hR : 0 ≤ R) :
    Set.Finite {z : E d | IntFun d z ∧ gauge d α v z ≤ R} := by
  have hsub : {z : E d | IntFun d z ∧ gauge d α v z ≤ R} ⊆
      {z : E d | IntFun d z ∧ ‖z‖ ≤ ‖wvInv d hinj hv‖ * R} := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    calc
      ‖z‖ ≤ ‖wvInv d hinj hv‖ * gauge d α v z := norm_le_gauge d hinj hv z
      _ ≤ ‖wvInv d hinj hv‖ * R := mul_le_mul_of_nonneg_left hz.2 (norm_nonneg _)
  exact (finite_int_norm_le (‖wvInv d hinj hv‖ * R)
    (mul_nonneg (norm_nonneg _) hR)).subset hsub

variable {d : ℕ} {α : Fin d → ℝ} {v : Fin d → ℝ}

/-- standard basis vector -/
def basisVec (j : Fin d) : E d := Pi.single j (1 : ℝ)

lemma basisVec_apply (j k : Fin d) : basisVec (d := d) j k = if k = j then 1 else 0 := by
  by_cases h : k = j
  · simp [basisVec, h]
  · simp [basisVec, h]

lemma basisVec_int (j : Fin d) : IntFun d (basisVec (d := d) j) := by
  intro k
  by_cases h : k = j
  · subst h
    exact ⟨1, by simp [basisVec]⟩
  · exact ⟨0, by simp [basisVec, h]⟩

lemma basisVec_eq_basisFun (j : Fin d) :
    basisVec (d := d) j = Pi.basisFun ℝ (Fin d) j := by
  simp [basisVec]

lemma span_basisVec_top : Submodule.span ℝ (Set.range (basisVec (d := d))) = ⊤ := by
  have h : Set.range (fun j : Fin d => basisVec (d := d) j) =
      Set.range (fun j : Fin d => Pi.basisFun ℝ (Fin d) j) := by
    exact congrArg Set.range (funext (fun j => basisVec_eq_basisFun (d := d) j))
  rw [h]
  exact (Pi.basisFun ℝ (Fin d)).span_eq

/-- standard basis vector outside a proper subspace -/
lemma exists_basisVec_not_mem (W : Submodule ℝ (E d)) (hW : W ≠ ⊤) :
    ∃ j : Fin d, basisVec (d := d) j ∉ W := by
  by_contra h
  push_neg at h
  have hsub : Submodule.span ℝ (Set.range (basisVec (d := d))) ≤ W := by
    rw [Submodule.span_le]
    intro x hx
    rcases hx with ⟨j, rfl⟩
    exact h j
  have htop : Submodule.span ℝ (Set.range (basisVec (d := d))) = ⊤ := span_basisVec_top
  exact hW (le_antisymm le_top (by simpa [htop] using hsub))
/-- set of the first `k` values of a family -/
def prefixSet {n : ℕ} (u : Fin n → E d) (k : ℕ) : Set (E d) :=
  {x : E d | ∃ j : Fin n, j.val < k ∧ u j = x}

/-- span of the first `k` vectors of a family -/
def flagSpan {n : ℕ} (u : Fin n → E d) (k : ℕ) : Submodule ℝ (E d) :=
  Submodule.span ℝ (prefixSet u k)

/-- append a vector to a family -/
abbrev snocE {n : ℕ} (u : Fin n → E d) (w : E d) : Fin (n + 1) → E d :=
  Fin.snoc (α := fun _ : Fin (n + 1) => E d) u w

lemma prefixSet_mono {n : ℕ} (u : Fin n → E d) {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) :
    prefixSet u k₁ ⊆ prefixSet u k₂ := by
  intro x hx
  rcases hx with ⟨j, hj, hjx⟩
  exact ⟨j, lt_of_lt_of_le hj h, hjx⟩

lemma flagSpan_mono {n : ℕ} (u : Fin n → E d) {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) :
    flagSpan u k₁ ≤ flagSpan u k₂ :=
  Submodule.span_mono (prefixSet_mono u h)

@[simp] lemma snocE_castSucc {n : ℕ} (u : Fin n → E d) (w : E d) (j : Fin n) :
    snocE u w (Fin.castSucc j) = u j := by
  simp [snocE]

@[simp] lemma snocE_last {n : ℕ} (u : Fin n → E d) (w : E d) :
    snocE u w (Fin.last n) = w := by
  simp [snocE]

lemma prefixSet_last {n : ℕ} (u : Fin n → E d) : prefixSet u n = Set.range u := by
  ext x
  constructor
  · rintro ⟨j, hj, hx⟩
    exact ⟨j, hx⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j, j.isLt, rfl⟩

lemma prefixSet_snoc_of_le {n : ℕ} (u : Fin n → E d) (w : E d) (k : ℕ) (hk : k ≤ n) :
    prefixSet (snocE u w) k = prefixSet u k := by
  ext x
  constructor
  · rintro ⟨j, hj, hx⟩
    have hjn : j.val < n := lt_of_lt_of_le hj hk
    have hjcast : j = Fin.castSucc ⟨j.val, hjn⟩ := by ext; simp
    rw [hjcast] at hx
    change snocE u w (Fin.castSucc ⟨j.val, hjn⟩) = x at hx
    rw [snocE_castSucc] at hx
    exact ⟨⟨j.val, hjn⟩, hj, hx⟩
  · rintro ⟨j, hj, hx⟩
    refine ⟨Fin.castSucc j, hj, ?_⟩
    rw [snocE_castSucc]
    exact hx

lemma flagSpan_snoc_of_le {n : ℕ} (u : Fin n → E d) (w : E d) (k : ℕ) (hk : k ≤ n) :
    flagSpan (snocE u w) k = flagSpan u k := by
  unfold flagSpan
  rw [prefixSet_snoc_of_le u w k hk]

lemma flagSpan_snoc_castSucc {n : ℕ} (u : Fin n → E d) (w : E d) (i : Fin n) :
    flagSpan (snocE u w) (Fin.castSucc i).val = flagSpan u i.val := by
  simpa using flagSpan_snoc_of_le u w i.val (le_of_lt i.isLt)

lemma flagSpan_snoc_last {n : ℕ} (u : Fin n → E d) (w : E d) :
    flagSpan (snocE u w) (Fin.last n).val = flagSpan u n := by
  simpa using flagSpan_snoc_of_le u w n (by omega)

lemma prefixSet_init_of_le {n : ℕ} (u : Fin (n + 1) → E d) (k : ℕ) (hk : k ≤ n) :
    prefixSet (Fin.init u) k = prefixSet u k := by
  ext x
  constructor
  · rintro ⟨i, hi, hx⟩
    refine ⟨Fin.castSucc i, hi, ?_⟩
    change Fin.init u i = x at hx
    rw [Fin.init_def] at hx
    exact hx
  · rintro ⟨j, hj, hx⟩
    have hjn : j.val < n := lt_of_lt_of_le hj hk
    refine ⟨⟨j.val, hjn⟩, hj, ?_⟩
    change Fin.init u ⟨j.val, hjn⟩ = x
    rw [Fin.init_def]
    change u (Fin.castSucc ⟨j.val, hjn⟩) = x
    have hval : (Fin.castSucc ⟨j.val, hjn⟩ : Fin (n + 1)) = j := by ext; simp
    rw [hval]
    exact hx

lemma flagSpan_init_of_le {n : ℕ} (u : Fin (n + 1) → E d) (k : ℕ) (hk : k ≤ n) :
    flagSpan (Fin.init u) k = flagSpan u k := by
  unfold flagSpan
  rw [prefixSet_init_of_le u k hk]

lemma range_init_eq_prefix {n : ℕ} (u : Fin (n + 1) → E d) :
    Set.range (Fin.init u) = prefixSet u n := by
  ext x
  constructor
  · rintro ⟨i, hx⟩
    have hcast : u (Fin.castSucc i) = x := by simpa [Fin.init_def] using hx
    exact ⟨Fin.castSucc i, i.isLt, hcast⟩
  · rintro ⟨j, hj, hx⟩
    have hjn : j.val < n := hj
    have hval : (Fin.castSucc ⟨j.val, hjn⟩ : Fin (n + 1)) = j := by ext; simp
    refine ⟨⟨j.val, hjn⟩, ?_⟩
    rw [Fin.init_def]
    change u (Fin.castSucc ⟨j.val, hjn⟩) = x
    rw [hval]
    exact hx

/-- nested non-membership implies linear independence -/
lemma linearIndependent_of_nested {n : ℕ} (u : Fin n → E d)
    (h : ∀ i : Fin n, u i ∉ flagSpan u i.val) : LinearIndependent ℝ u := by
  induction n with
  | zero =>
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      exact Fin.elim0 i
  | succ n ih =>
      rw [linearIndependent_finSucc']
      constructor
      · apply ih (Fin.init u)
        intro i
        have hspan : flagSpan (Fin.init u) i.val = flagSpan u i.val :=
          flagSpan_init_of_le u i.val (le_of_lt i.isLt)
        have hmem := h (Fin.castSucc i)
        change u (Fin.castSucc i) ∉ flagSpan (Fin.init u) i.val
        rw [hspan]
        simpa using hmem
      · intro hm
        have hspan : flagSpan u n = Submodule.span ℝ (Set.range (Fin.init u)) := by
          unfold flagSpan
          rw [range_init_eq_prefix (u := u)]
        exact h (Fin.last n) (by simpa [hspan] using hm)

/-- the span of `n` nested vectors is not the whole space when `n < d` -/
lemma flagSpan_nested_ne_top {n : ℕ} (u : Fin n → E d)
    (h : ∀ i : Fin n, u i ∉ flagSpan u i.val) (hlt : n < d) :
    flagSpan u n ≠ ⊤ := by
  have hind : LinearIndependent ℝ u := linearIndependent_of_nested u h
  intro htop
  have hfin : Module.finrank ℝ (flagSpan u n) = n := by
    have hfin' := finrank_span_eq_card hind
    unfold flagSpan
    rw [prefixSet_last]
    simpa using hfin'
  have htopfin : Module.finrank ℝ (flagSpan u n) = d := by
    rw [htop]
    simp
  omega

/-- the greedy prefix properties -/
def GreedyProps (α : Fin d → ℝ) (v : Fin d → ℝ) {n : ℕ} (u : Fin n → E d) : Prop :=
  (∀ i : Fin n, IntFun d (u i)) ∧
  (∀ i : Fin n, u i ∉ flagSpan u i.val) ∧
  (∀ i : Fin n, ∀ z : E d, IntFun d z → z ∉ flagSpan u i.val →
    gauge d α v (u i) ≤ gauge d α v z)

/-- `wvMap` is injective -/
lemma wvMap_injective (hinj : Function.Injective α) (hv : ∀ k : Fin d, 0 < v k) :
    Function.Injective (wvMap d α v) := by
  exact (LinearMap.equivOfDetNeZero (wvMap d α v) (wvMap_det_ne_zero d hinj hv)).injective

/-- gauge is positive on nonzero vectors -/
lemma gauge_pos_of_ne_zero (hinj : Function.Injective α) (hv : ∀ k : Fin d, 0 < v k)
    {x : E d} (hx : x ≠ 0) : 0 < gauge d α v x := by
  have hne : ‖wvMap d α v x‖ ≠ 0 := by
    intro hz
    apply hx
    apply wvMap_injective hinj hv
    simpa using (norm_eq_zero.mp hz)
  exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)

/-- gauge of the zero vector -/
lemma gauge_zero : gauge d α v 0 = 0 := by
  simp [gauge]

/-- standard basis vector outside a proper subspace (imported here for clarity) -/
lemma exists_min_gauge_outside (hinj : Function.Injective α) (hv : ∀ k : Fin d, 0 < v k)
    (W : Submodule ℝ (E d)) (hW : W ≠ ⊤) :
    ∃ w : E d, IntFun d w ∧ w ∉ W ∧
      ∀ z : E d, IntFun d z → z ∉ W → gauge d α v w ≤ gauge d α v z := by
  classical
  obtain ⟨j, hj⟩ := exists_basisVec_not_mem W hW
  let e := basisVec (d := d) j
  have he : IntFun d e := basisVec_int j
  let S : Set (E d) := {z | IntFun d z ∧ z ∉ W ∧ gauge d α v z ≤ gauge d α v e}
  have hSne : S.Nonempty := ⟨e, he, hj, le_rfl⟩
  have hSfin : S.Finite :=
    (finite_int_gauge_le hinj hv (gauge d α v e) (gauge_nonneg d α v e)).subset (by
      intro z hz
      exact ⟨hz.1, hz.2.2⟩)
  obtain ⟨w, hwS, hwmin⟩ := Set.exists_min_image S (gauge d α v) hSfin hSne
  refine ⟨w, hwS.1, hwS.2.1, ?_⟩
  intro z hzint hzW
  by_cases hz : gauge d α v z ≤ gauge d α v e
  · exact hwmin z ⟨hzint, hzW, hz⟩
  · have hlt' : gauge d α v e < gauge d α v z := lt_of_not_ge hz
    exact le_trans hwS.2.2 (le_of_lt hlt')

/-- greedy recursion: existence of the whole greedy flag -/
theorem greedy_rec (n : ℕ) (hn : n ≤ d) (hinj : Function.Injective α)
    (hv : ∀ k : Fin d, 0 < v k) :
    ∃ u : Fin n → E d, GreedyProps α v u := by
  classical
  induction n with
  | zero =>
      refine ⟨fun i => Fin.elim0 i, ?_, ?_, ?_⟩
      · intro i; exact Fin.elim0 i
      · intro i; exact Fin.elim0 i
      · intro i; exact Fin.elim0 i
  | succ n ih =>
      obtain ⟨u, hu⟩ := ih (by omega : n ≤ d)
      let W : Submodule ℝ (E d) := flagSpan u n
      have hW : W ≠ ⊤ := by
        intro htop
        apply flagSpan_nested_ne_top (n := n) u hu.2.1 (by omega : n < d)
        exact htop
      obtain ⟨w, hwI, hwW, hwmin⟩ := exists_min_gauge_outside hinj hv W hW
      refine ⟨snocE u w, ?_, ?_, ?_⟩
      · intro i
        cases i using Fin.lastCases with
        | last => simpa using hwI
        | cast i => simpa using hu.1 i
      · intro i
        cases i using Fin.lastCases with
        | last =>
            rw [snocE_last]
            rw [flagSpan_snoc_last]
            exact hwW
        | cast i =>
            rw [snocE_castSucc]
            rw [flagSpan_snoc_castSucc]
            exact hu.2.1 i
      · intro i z hzI hzW
        cases i using Fin.lastCases with
        | last =>
            rw [snocE_last]
            have hpre : flagSpan (snocE u w) (Fin.last n).val = flagSpan u n :=
              flagSpan_snoc_last (u := u) (w := w)
            have hznot : z ∉ flagSpan u n := by
              intro hz2
              apply hzW
              rwa [← hpre] at hz2
            exact hwmin z hzI hznot
        | cast i =>
            rw [snocE_castSucc]
            have hpre : flagSpan (snocE u w) (Fin.castSucc i).val = flagSpan u i.val :=
              flagSpan_snoc_castSucc (u := u) (w := w) i
            have hznot : z ∉ flagSpan u i.val := by
              intro hz2
              apply hzW
              rwa [← hpre] at hz2
            exact hu.2.2 i z hzI hznot

/-- the full greedy data for dimension `d` -/
theorem greedy_full (hd : 0 < d) (hinj : Function.Injective α)
    (hv : ∀ k : Fin d, 0 < v k) :
    ∃ u : Fin d → E d,
      (∀ i : Fin d, IntFun d (u i)) ∧
      (∀ i : Fin d, u i ∉ flagSpan u i.val) ∧
      (∀ i : Fin d, 0 < gauge d α v (u i)) ∧
      (∀ i : Fin d, ∀ z : E d, IntFun d z → z ∉ flagSpan u i.val →
        gauge d α v (u i) ≤ gauge d α v z) := by
  classical
  obtain ⟨u, hu⟩ := greedy_rec d (by omega : d ≤ d) hinj hv
  refine ⟨u, hu.1, hu.2.1, ?_, hu.2.2⟩
  intro i
  apply gauge_pos_of_ne_zero hinj hv
  intro hzero
  have hmem : (0 : E d) ∈ flagSpan u i.val := by
    exact Submodule.zero_mem _
  simpa [hzero] using hu.2.1 i


/-- the linear map whose columns are a given family -/
def fromCols (e : Fin d → E d) : E d →ₗ[ℝ] E d :=
  Matrix.toLin' (Matrix.of (fun k j => e j k))

lemma fromCols_apply (e : Fin d → E d) (x : E d) (k : Fin d) :
    fromCols e x k = ∑ j : Fin d, x j * e j k := by
  unfold fromCols
  rw [Matrix.toLin'_apply]
  simpa [mul_comm] using (Matrix.mulVec_apply_eq_sum (Matrix.of (fun k j => e j k)) x k)

lemma fromCols_basisVec (e : Fin d → E d) (j : Fin d) :
    fromCols e (basisVec (d := d) j) = e j := by
  ext k
  rw [fromCols_apply]
  simp [basisVec_apply]

/-- integer-valued maps to integer matrices -/
def intOfFun {u : Fin d → E d} (huint : ∀ i : Fin d, IntFun d (u i)) :
    Fin d → Fin d → ℤ :=
  fun i j => Classical.choose (huint i j)

lemma intOfFun_cast (u : Fin d → E d) (huint : ∀ i : Fin d, IntFun d (u i)) (i j : Fin d) :
    (((intOfFun (u := u) huint i j : ℤ) : ℝ)) = u i j :=
  Classical.choose_spec (huint i j)

/-- ℤ-linear independence of the integer versions -/
lemma linearIndependent_int_of_real {u : Fin d → E d}
    (huint : ∀ i : Fin d, IntFun d (u i)) (hindep : LinearIndependent ℝ u) :
    LinearIndependent ℤ (fun i : Fin d => intOfFun (u := u) huint i) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  let uZ : Fin d → Fin d → ℤ := intOfFun (u := u) huint
  have hcR : (∑ j : Fin d, (c j : ℝ) • u j) = 0 := by
    funext i0
    have h1 := congrFun hc i0
    rw [Finset.sum_apply] at h1
    simp only [Pi.smul_apply, smul_eq_mul] at h1
    have hc0 : (∑ j : Fin d, (((c j * uZ j i0 : ℤ) : ℝ))) = 0 := by
      exact_mod_cast h1
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply]
    calc
      (∑ j : Fin d, (c j : ℝ) * u j i0)
          = (∑ j : Fin d, (((c j * uZ j i0 : ℤ) : ℝ))) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            have huj : u j i0 = (((uZ j i0 : ℤ) : ℝ)) :=
              (intOfFun_cast (u := u) huint j i0).symm
            rw [huj]
            norm_num [uZ]
      _ = 0 := hc0
  have hind' := (Fintype.linearIndependent_iff.mp hindep) (fun j : Fin d => (c j : ℝ)) hcR
  exact_mod_cast hind' i

/-- span over a prefix equals span over the first `k` columns (ℤ-family to ℝ coercion) -/
lemma span_prefix_firstCols {d : ℕ} {k : ℕ} (hk : k ≤ d) (x : Fin d → Fin d → ℤ) :
    Submodule.span ℝ (prefixSet (fun j : Fin d => fun i : Fin d => (((x j i : ℤ) : ℝ))) k) =
      Submodule.span ℝ (MinkFlagBasis.firstCols d k hk x) := by
  congr 1
  ext y
  constructor
  · rintro ⟨j, hj, hy⟩
    refine ⟨⟨j.val, hj⟩, ?_⟩
    change (fun i : Fin d => (((x (Fin.castLE hk ⟨j.val, hj⟩) i : ℤ) : ℝ))) = y
    have hjcast : (Fin.castLE hk ⟨j.val, hj⟩ : Fin d) = j := by
      ext
      simp
    rw [hjcast]
    exact hy
  · rintro ⟨j, hy⟩
    refine ⟨Fin.castLE hk j, by simpa using j.isLt, ?_⟩
    change (fun i : Fin d => (((x (Fin.castLE hk j) i : ℤ) : ℝ))) = y
    exact hy

/-- the real coercion of `uZ` is pointwise `u` -/
lemma uZ_coe_eq_u (u : Fin d → E d) (huint : ∀ i : Fin d, IntFun d (u i)) :
    (fun j : Fin d => fun i : Fin d => (((intOfFun (u := u) huint j i : ℤ) : ℝ))) = u := by
  funext j
  funext i
  exact intOfFun_cast (u := u) huint j i

/-- adapted unimodular family (bridge) -/
theorem adapted_exists (u : Fin d → E d)
    (huint : ∀ i : Fin d, IntFun d (u i))
    (hindep : LinearIndependent ℝ u) :
    ∃ eR : Fin d → E d,
      (∀ j : Fin d, IntFun d (eR j)) ∧
      (∀ k : Fin (d + 1), flagSpan eR k.val = flagSpan u k.val) ∧
      (|LinearMap.det (fromCols eR)| = 1) := by
  classical
  let uZ : Fin d → Fin d → ℤ := intOfFun (u := u) huint
  have huZindep : LinearIndependent ℤ uZ := linearIndependent_int_of_real huint hindep
  obtain ⟨e, hdet, hspans⟩ := MinkFlagBasis.exists_flag_basis uZ huZindep
  let eR : Fin d → E d := fun j i => (((e j i : ℤ) : ℝ))
  refine ⟨eR, ?_, ?_, ?_⟩
  · intro j i
    exact ⟨e j i, rfl⟩
  · intro k
    have hk' : k.val ≤ d := Nat.le_of_lt_succ k.2
    have hEq := hspans k
    unfold flagSpan
    rw [← uZ_coe_eq_u u huint]
    rw [span_prefix_firstCols hk' e]
    rw [span_prefix_firstCols hk' (intOfFun (u := u) huint)]
    simpa [uZ] using hEq
  · let MZ : Matrix (Fin d) (Fin d) ℤ := Matrix.of (fun i j : Fin d => (e j i : ℤ))
    have hMdet : MZ.det = 1 ∨ MZ.det = -1 := by
      simpa [MZ] using hdet
    have hEqMat : (Matrix.of (fun k j : Fin d => eR j k)) = MZ.map (fun z : ℤ => (z : ℝ)) := by
      ext k j
      rfl
    calc
      |LinearMap.det (fromCols eR)| = |(Matrix.of (fun k j : Fin d => eR j k)).det| := by
            unfold fromCols
            rw [LinearMap.det_toLin']
      _ = |((MZ.det : ℤ) : ℝ)| := by
            rw [hEqMat, ← Int.cast_det MZ]
      _ = 1 := by
            rcases hMdet with h | h <;> rw [h] <;> norm_num


/-- subspace of functions vanishing at coordinates `≥ k` -/
def VzeroSub (d : ℕ) (k : ℕ) : Submodule ℝ (E d) where
  carrier := {x | ∀ j : Fin d, k ≤ j.val → x j = 0}
  zero_mem' := by intro j hj; simp
  add_mem' := by intro x y hx hy j hj; simp [hx j hj, hy j hj]
  smul_mem' := by intro a x hx j hj; simp [hx j hj]

lemma mem_VzeroSub (x : E d) (k : ℕ) :
    x ∈ VzeroSub d k ↔ ∀ j : Fin d, k ≤ j.val → x j = 0 := by
  rfl

/-- every vector is the combination of the standard basis -/
lemma sum_basisVec (x : E d) :
    x = ∑ j : Fin d, x j • basisVec (d := d) j := by
  ext i
  simp only [Finset.sum_apply, Pi.smul_apply]
  rw [Finset.sum_eq_single i]
  · simp [basisVec]
  · intro j hj hji
    simp [basisVec, hji]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/-- the coordinate subspace equals the span of the first `k` basis vectors -/
lemma VzeroSub_eq_span (d : ℕ) (k : ℕ) :
    VzeroSub d k = Submodule.span ℝ {v : E d | ∃ j : Fin d, j.val < k ∧ basisVec (d := d) j = v} := by
  classical
  apply le_antisymm
  · intro x hx
    rw [sum_basisVec x]
    apply Submodule.sum_mem
    intro j hj
    by_cases hjk : j.val < k
    · exact Submodule.smul_mem _ (x j) (Submodule.subset_span ⟨j, hjk, rfl⟩)
    · have hz : x j = 0 := hx j (by omega)
      simp [hz]
  · rw [Submodule.span_le]
    intro v hv
    rcases hv with ⟨j, hj, rfl⟩
    intro i hi
    by_cases hji : i = j
    · subst i
      omega
    · rw [basisVec_apply]
      simp [hji]

/-- the linear map from columns sends the coordinate subspace to the span of its columns -/
lemma fromCols_map_Vzero {e : Fin d → E d} (k : ℕ) (hk : k ≤ d) :
    Submodule.map (fromCols e) (VzeroSub d k) = flagSpan e k := by
  rw [VzeroSub_eq_span]
  rw [Submodule.map_span]
  unfold flagSpan
  congr 1
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    rcases hu with ⟨j, hj, rfl⟩
    refine ⟨j, hj, ?_⟩
    exact (fromCols_basisVec e j).symm
  · rintro ⟨j, hj, hje⟩
    refine ⟨basisVec (d := d) j, ?_, ?_⟩
    · exact ⟨j, hj, rfl⟩
    · exact (fromCols_basisVec e j).trans hje

/-- coordinate extraction -/
lemma in_preimage_span_of_cols {e : Fin d → E d} (k : ℕ) (hk : k ≤ d)
    (hne : LinearMap.det (fromCols e) ≠ 0)
    {z : E d} (hz : fromCols e z ∈ flagSpan e k) : z ∈ VzeroSub d k := by
  have hinj : Function.Injective (fromCols e) := by
    exact (LinearMap.equivOfDetNeZero (fromCols e) hne).injective
  have hmap : Submodule.map (fromCols e) (VzeroSub d k) = flagSpan e k :=
    fromCols_map_Vzero (e := e) k hk
  rw [← hmap] at hz
  rcases hz with ⟨w, hw, hweq⟩
  have hwz : w = z := hinj hweq
  rwa [← hwz]

/-- the columns preserve integrality -/
lemma fromCols_int {e : Fin d → E d} (heint : ∀ j : Fin d, IntFun d (e j)) (x : E d) :
    IntFun d x → IntFun d (fromCols e x) := by
  intro hx k
  refine ⟨∑ j : Fin d, Classical.choose (hx j) * Classical.choose (heint j k), ?_⟩
  rw [fromCols_apply]
  change (Int.castRingHom ℝ) (∑ j : Fin d, Classical.choose (hx j) * Classical.choose (heint j k)) =
      ∑ j : Fin d, x j * e j k
  rw [_root_.map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hxj := Classical.choose_spec (hx j)
  have hejk := Classical.choose_spec (heint j k)
  conv_rhs => rw [← hxj, ← hejk]
  norm_num

/-- preimage and scalar commute for a linear map -/
lemma mem_smul_preimage_linearMap (Φ : E d →ₗ[ℝ] E d) (s : Set (E d)) (r : ℝ) (hr : r ≠ 0)
    (z : E d) :
    z ∈ r • (Φ ⁻¹' s) ↔ Φ z ∈ r • s := by
  constructor
  · intro hz
    rw [mem_smul_set] at hz
    rcases hz with ⟨y, hy, hzy⟩
    rw [mem_smul_set]
    refine ⟨Φ y, hy, ?_⟩
    calc r • Φ y = Φ (r • y) := by simp
      _ = Φ z := by rw [hzy]
  · intro hz
    rw [mem_smul_set] at hz
    rcases hz with ⟨w, hw, hzw⟩
    rw [mem_smul_set]
    refine ⟨r⁻¹ • z, ?_, ?_⟩
    · change Φ (r⁻¹ • z) ∈ s
      have hΦw : Φ (r⁻¹ • z) = w := by
        calc Φ (r⁻¹ • z) = r⁻¹ • Φ z := by simp
          _ = w := by
            rw [← hzw]
            rw [smul_smul]
            simp [hr]
      simpa [hΦw] using hw
    · rw [smul_smul]
      simp [hr]

/-- the transported body is bounded -/
lemma wvBody_preimage_isBounded (Φ : E d →ₗ[ℝ] E d) (hne : LinearMap.det Φ ≠ 0)
    (hinj : Function.Injective α) (hv : ∀ k : Fin d, 0 < v k) :
    Bornology.IsBounded (Φ ⁻¹' (wvBody d α v)) := by
  rw [wvBody_eq]
  rw [isBounded_iff_forall_norm_le]
  let Tc : E d ≃L[ℝ] E d := (LinearMap.equivOfDetNeZero Φ hne).toContinuousLinearEquiv
  let Ts : E d →L[ℝ] E d := Tc.symm.toContinuousLinearMap
  refine ⟨‖Ts‖ * ‖wvInv d hinj hv‖, ?_⟩
  intro x hx
  have hx' : ‖wvMap d α v (Φ x)‖ < 1 := by
    simpa [wvBody_eq] using hx
  have hx1 : ‖Φ x‖ ≤ ‖wvInv d hinj hv‖ * 1 := by
    calc ‖Φ x‖ ≤ ‖wvInv d hinj hv‖ * ‖wvMap d α v (Φ x)‖ := norm_le_gauge d hinj hv (Φ x)
      _ ≤ ‖wvInv d hinj hv‖ * 1 := by
        exact mul_le_mul_of_nonneg_left (le_of_lt hx') (norm_nonneg _)
  calc
    ‖x‖ = ‖Ts (Φ x)‖ := by
      have hTs : Ts (Φ x) = x := by
        change Ts (Tc x) = x
        simpa [Ts] using (Tc.symm_apply_apply x)
      rw [hTs]
    _ ≤ ‖Ts‖ * ‖Φ x‖ := by
      exact ContinuousLinearMap.le_opNorm Ts (Φ x)
    _ ≤ ‖Ts‖ * (‖wvInv d hinj hv‖ * 1) := by
      exact mul_le_mul_of_nonneg_left hx1 (norm_nonneg _)
    _ = ‖Ts‖ * ‖wvInv d hinj hv‖ := by rw [mul_one]

/-- the main engine bound for the greedy data -/
theorem engine_bound_greedy (hd : 0 < d) (hinj : Function.Injective α)
    (hv : ∀ k : Fin d, 0 < v k)
    (u : Fin d → E d)
    (huint : ∀ i : Fin d, IntFun d (u i))
    (huflag : ∀ i : Fin d, u i ∉ flagSpan u i.val)
    (hmin : ∀ i : Fin d, ∀ z : E d, IntFun d z → z ∉ flagSpan u i.val →
      gauge d α v (u i) ≤ gauge d α v z)
    (e : Fin d → E d)
    (heint : ∀ j : Fin d, IntFun d (e j))
    (heflag : ∀ k : Fin (d + 1), flagSpan e k.val = flagSpan u k.val)
    (hedet : |LinearMap.det (fromCols e)| = 1) :
    (∏ i : Fin d, gauge d α v (u i)) ≤ Dval d α v := by
  classical
  let Φ : E d →ₗ[ℝ] E d := fromCols e
  let B : Set (E d) := Φ ⁻¹' (wvBody d α v)
  let a : Fin d → ℝ := fun i => gauge d α v (u i)
  have hneΦ : LinearMap.det Φ ≠ 0 := by
    dsimp [Φ]
    intro hz
    have : |(0 : ℝ)| = 1 := by simpa [hz] using hedet
    norm_num at this
  have hB_open : IsOpen B := by
    dsimp [B, Φ]
    exact (wvBody_isOpen d α v).preimage (fromCols e).continuous_of_finiteDimensional
  have hB_convex : Convex ℝ B := by
    dsimp [B, Φ]
    exact (wvBody_convex d α v).linear_preimage (fromCols e)
  have hB_symm : ∀ x : E d, x ∈ B → -x ∈ B := by
    intro x hx
    have hx' : Φ x ∈ wvBody d α v := by simpa [B] using hx
    have hneg : Φ (-x) = -Φ x := by simp
    dsimp [B]
    change Φ (-x) ∈ wvBody d α v
    rw [hneg]
    exact wvBody_symm d α v (Φ x) hx'
  have hB_zero : (0 : E d) ∈ B := by
    dsimp [B]
    simp
    exact wvBody_zero d α v
  have hB_bdd : Bornology.IsBounded B := by
    dsimp [B, Φ]
    exact wvBody_preimage_isBounded (fromCols e) hneΦ hinj hv
  have ha_pos : ∀ i : Fin d, 0 < a i := by
    intro i
    dsimp [a]
    apply gauge_pos_of_ne_zero hinj hv
    intro hzero
    have hmem : (0 : E d) ∈ flagSpan u i.val := Submodule.zero_mem _
    simpa [hzero] using huflag i
  have ha_mono : ∀ i : Fin d, ∀ j : Fin d, i.val ≤ j.val → a i ≤ a j := by
    intro i j hij
    dsimp [a]
    have hsub : flagSpan u i.val ≤ flagSpan u j.val := flagSpan_mono u hij
    have hnot : u j ∉ flagSpan u i.val := by
      intro h
      exact huflag j (hsub h)
    exact hmin i (u j) (huint j) hnot
  have hP : ∀ i : Fin d, ∀ z : E d, IntFun d z → z ∈ (a i) • B →
      ∀ j : Fin d, i.val ≤ j.val → z j = 0 := by
    intro i z hzI hzmem j hij
    have hai : a i ≠ 0 := ne_of_gt (ha_pos i)
    have hz2 : Φ z ∈ (a i) • wvBody d α v := by
      have hz' := (mem_smul_preimage_linearMap Φ (wvBody d α v) (a i) hai z).mp (by simpa [B] using hzmem)
      simpa [Φ] using hz'
    have hg : gauge d α v (Φ z) < a i := by
      exact (mem_smul_wvBody d α v (Φ z) (a i) (ha_pos i)).mp hz2
    have hΦzI : IntFun d (Φ z) := by
      simpa [Φ] using fromCols_int (e := e) heint z hzI
    have hΦzspan : Φ z ∈ flagSpan u i.val := by
      by_contra hnot
      have hle := hmin i (Φ z) hΦzI hnot
      exact (not_lt_of_ge hle) hg
    have hfe : flagSpan e i.val = flagSpan u i.val := by
      simpa using heflag (⟨i.val, by omega⟩ : Fin (d + 1))
    have hΦzspan' : Φ z ∈ flagSpan e i.val := by
      simpa [Φ, hfe] using hΦzspan
    have hzV : z ∈ VzeroSub d i.val := by
      apply in_preimage_span_of_cols (e := e) i.val (le_of_lt i.isLt) (by simpa [Φ] using hneΦ)
      simpa [Φ] using hΦzspan'
    exact (mem_VzeroSub z i.val).mp hzV j hij
  have heng := MinkEngine.mink_engine d B a hB_open hB_convex hB_symm hB_zero hB_bdd
    ha_pos ha_mono hP
  have hvolB : (MeasureTheory.volume : Measure (E d)).real B = (2 : ℝ) ^ d / Dval d α v := by
    have hvol := vol_preimage_eq d Φ hedet hneΦ (wvBody d α v)
    dsimp [B, Φ]
    rw [hvol]
    rw [vol_wvBody d hinj hv]
  have hD : 0 < Dval d α v := Dval_pos d hinj hv
  have h2 : 0 < (2 : ℝ) ^ d := pow_pos (by norm_num) d
  have hle' : (∏ i : Fin d, a i) * ((2 : ℝ) ^ d / Dval d α v) ≤ (2 : ℝ) ^ d := by
    simpa [B, a, hvolB] using heng
  have hmul := mul_le_mul_of_nonneg_right hle' (le_of_lt hD)
  have hL : ((∏ i : Fin d, a i) * ((2 : ℝ) ^ d / Dval d α v)) * Dval d α v =
      (∏ i : Fin d, a i) * (2 : ℝ) ^ d := by
    field_simp [Dval_ne_zero d hinj hv]
  have hmul' : (∏ i : Fin d, a i) * (2 : ℝ) ^ d ≤ (2 : ℝ) ^ d * Dval d α v := by
    simpa [hL] using hmul
  have hPle : (∏ i : Fin d, a i) ≤ Dval d α v := by
    have hmul2 : (∏ i : Fin d, a i) * (2 : ℝ) ^ d ≤ Dval d α v * (2 : ℝ) ^ d := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul'
    exact (le_of_mul_le_mul_right hmul2 h2)
  simpa [a] using hPle

/-- polynomial from a vector of `d` integer coefficients -/
def polyOfVec (u : Fin d → ℤ) : Polynomial ℤ :=
  ∑ j : Fin d, Polynomial.C (u j) * Polynomial.X ^ j.val

lemma evalInt_eq_sum {d : ℕ} (Q : Polynomial ℤ) {x : ℝ} (hdeg : Q.natDegree < d) :
    evalInt Q x = ∑ j : Fin d, ((Q.coeff j.val : ℤ) : ℝ) * x ^ (j.val : ℕ) := by
  let p : Polynomial ℝ := Q.map (algebraMap ℤ ℝ)
  have hpdeg : p.natDegree < d := by
    rw [Polynomial.natDegree_map_eq_of_injective]
    · exact hdeg
    · intro a b h
      exact Int.cast_injective h
  calc
    evalInt Q x = p.eval x := by rfl
    _ = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * x ^ i := by
      rw [Polynomial.eval_eq_sum_range]
    _ = ∑ i ∈ Finset.range d, p.coeff i * x ^ i := by
      apply Finset.sum_subset
      · rw [Finset.range_subset]
        intro i hi
        exact Finset.mem_range.mpr (lt_of_lt_of_le hi (Nat.succ_le_of_lt hpdeg))
      · intro i hi hnot
        have hi' : p.natDegree < i := by
          have : ¬ i < p.natDegree + 1 := by
            intro h
            apply hnot
            exact Finset.mem_range.mpr h
          omega
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi']
        simp
    _ = ∑ j : Fin d, p.coeff j.val * x ^ (j.val : ℕ) := by
      rw [← Fin.sum_univ_eq_sum_range (fun n : ℕ => p.coeff n * x ^ n) d]
    _ = ∑ j : Fin d, ((Q.coeff j.val : ℤ) : ℝ) * x ^ (j.val : ℕ) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hc : p.coeff j.val = ((Q.coeff j.val : ℤ) : ℝ) := by
        simp [p, Polynomial.coeff_map]
      rw [hc]

lemma coeff_sum_univ {α : Type*} [Fintype α] (f : α → Polynomial ℤ) (n : ℕ) :
    (∑ a : α, f a).coeff n = ∑ a : α, (f a).coeff n := by
  classical
  let φ : Polynomial ℤ →+ ℤ :=
    { toFun := fun p => p.coeff n
      map_zero' := by simp
      map_add' := by intro p q; rfl }
  change φ (∑ a : α, f a) = ∑ a : α, φ (f a)
  exact map_sum φ f Finset.univ

/-- coefficient of a monomial -/
lemma coeff_C_mul_X_pow (a : ℤ) (m n : ℕ) :
    (Polynomial.C a * Polynomial.X ^ m).coeff n = if n = m then a else 0 := by
  by_cases h : n = m
  · subst n
    simp
  · simp [h]

/-- coefficients of the constructed polynomial -/
lemma polyOfVec_coeff (u : Fin d → ℤ) (j : Fin d) : (polyOfVec u).coeff j.val = u j := by
  rw [polyOfVec]
  rw [coeff_sum_univ]
  rw [Finset.sum_eq_single j]
  · simp [coeff_C_mul_X_pow]
  · intro k hk hkj
    have hval : j.val ≠ k.val := by
      intro h
      apply hkj
      apply Fin.ext
      exact h.symm
    simp [coeff_C_mul_X_pow, hval]
  · intro hmem
    exact False.elim (hmem (Finset.mem_univ j))

/-- natDegree of the constructed polynomial is at most `d - 1` -/
lemma polyOfVec_natDegree_le (hd : 0 < d) (u : Fin d → ℤ) :
    (polyOfVec u).natDegree ≤ d - 1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [polyOfVec]
  rw [coeff_sum_univ]
  apply Finset.sum_eq_zero
  intro j hj
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  have hle : (Polynomial.C (u j) * Polynomial.X ^ j.val).natDegree ≤ j.val := by
    calc (Polynomial.C (u j) * Polynomial.X ^ j.val).natDegree
          ≤ (Polynomial.C (u j)).natDegree + (Polynomial.X ^ j.val).natDegree := Polynomial.natDegree_mul_le
      _ ≤ j.val := by
            simp [Polynomial.natDegree_X_pow]
  have hlt : j.val < n := by
    have : j.val ≤ d - 1 := by omega
    omega
  exact lt_of_le_of_lt hle hlt

/-- evaluation of `polyOfVec` at a real point -/
lemma eval_polyOfVec (hd : 0 < d) (u : Fin d → ℤ) (x : ℝ) :
    evalInt (polyOfVec u) x = ∑ j : Fin d, ((u j : ℤ) : ℝ) * x ^ (j.val : ℕ) := by
  have hdeg : (polyOfVec u).natDegree < d := lt_of_le_of_lt (polyOfVec_natDegree_le hd u) (by omega)
  rw [evalInt_eq_sum (Q := polyOfVec u) (x := x) (d := d) hdeg]
  apply Finset.sum_congr rfl
  intro j hj
  rw [polyOfVec_coeff]


/-- polynomial whose coefficients are the integer vector of `u i` -/
def QOfGreedy (u : Fin d → E d) (huint : ∀ i : Fin d, IntFun d (u i)) (i : Fin d) :
    Polynomial ℤ :=
  polyOfVec (intOfFun (u := u) huint i)

/-- multiplying the evaluation by the weight gives the Vandermonde coordinate -/
lemma mul_evalInt_wvMap (hd : 0 < d) (u : Fin d → E d)
    (huint : ∀ i : Fin d, IntFun d (u i)) (i : Fin d) (k : Fin d) :
    v k * evalInt (QOfGreedy u huint i) (α k) = (wvMap d α v (u i)) k := by
  have hsum : (∑ j : Fin d, (((intOfFun (u := u) huint i j : ℤ) : ℝ)) * (α k) ^ j.val) =
      (∑ j : Fin d, (u i j) * (α k) ^ j.val) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [intOfFun_cast]
  calc
    v k * evalInt (QOfGreedy u huint i) (α k)
        = v k * evalInt (polyOfVec (intOfFun (u := u) huint i)) (α k) := by rfl
    _ = v k * (∑ j : Fin d, (((intOfFun (u := u) huint i j : ℤ) : ℝ)) * (α k) ^ j.val) := by
          rw [eval_polyOfVec hd (intOfFun (u := u) huint i) (α k)]
    _ = v k * (∑ j : Fin d, (u i j) * (α k) ^ j.val) := by rw [hsum]
    _ = (wvMap d α v (u i)) k := by rw [wvMap_apply]

/-- the bound on weighted evaluations -/
lemma evalInt_bound (hd : 0 < d) (hv : ∀ k : Fin d, 0 < v k) (u : Fin d → E d)
    (huint : ∀ i : Fin d, IntFun d (u i)) (i : Fin d) (k : Fin d) :
    v k * |evalInt (QOfGreedy u huint i) (α k)| ≤ gauge d α v (u i) := by
  have habs : |v k * evalInt (QOfGreedy u huint i) (α k)| =
      v k * |evalInt (QOfGreedy u huint i) (α k)| := by
    rw [abs_mul, abs_of_pos (hv k)]
  calc
    v k * |evalInt (QOfGreedy u huint i) (α k)| = |v k * evalInt (QOfGreedy u huint i) (α k)| := habs.symm
    _ = |(wvMap d α v (u i)) k| := by rw [mul_evalInt_wvMap hd u huint i k]
    _ ≤ gauge d α v (u i) := gauge_coord_le d α v (u i) k

/-- the Q-family is ℚ-linearly independent -/
lemma linearIndependent_q_of_real {d : ℕ} {c : Fin d → Fin d → ℚ} {u : Fin d → E d}
    (hcoef : ∀ i j, u i j = (((c i j : ℚ) : ℝ)))
    (hindep : LinearIndependent ℝ u) : LinearIndependent ℚ c := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hgR : (∑ j : Fin d, (g j : ℝ) • u j) = 0 := by
    funext i0
    have h1 := congrFun hg i0
    rw [Finset.sum_apply] at h1
    simp only [Pi.smul_apply, smul_eq_mul] at h1
    have hc0 : (∑ j : Fin d, (((g j * c j i0 : ℚ) : ℝ))) = 0 := by
      exact_mod_cast h1
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply]
    calc
      (∑ j : Fin d, (g j : ℝ) * u j i0) = (∑ j : Fin d, (((g j * c j i0 : ℚ) : ℝ))) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [hcoef j i0]
            norm_num
      _ = 0 := hc0
  have hind' := (Fintype.linearIndependent_iff.mp hindep) (fun j : Fin d => (g j : ℝ)) hgR
  exact_mod_cast hind' i

/-- the coefficient vectors of the greedy polynomials are ℚ-independent -/
lemma linIndepInt_QOfGreedy (hd : 0 < d) (u : Fin d → E d)
    (huint : ∀ i : Fin d, IntFun d (u i)) (hindep : LinearIndependent ℝ u) :
    LinIndepInt d (QOfGreedy u huint) := by
  classical
  let cVec : Fin d → Fin d → ℤ := intOfFun (u := u) huint
  let cQ : Fin d → Fin d → ℚ := fun i j => ((cVec i j : ℤ) : ℚ)
  have hcoef : ∀ i j, u i j = (((cQ i j : ℚ) : ℝ)) := by
    intro i j
    simp [cQ, cVec, intOfFun_cast]
  have hq : LinearIndependent ℚ cQ := linearIndependent_q_of_real hcoef hindep
  change LinearIndependent ℚ (fun i : Fin d => coeffVec d (QOfGreedy u huint i))
  have hsame : (fun i : Fin d => coeffVec d (QOfGreedy u huint i)) = cQ := by
    funext i
    funext j
    change (((QOfGreedy u huint i).coeff j.val : ℤ) : ℚ) = ((cVec i j : ℤ) : ℚ)
    unfold QOfGreedy
    rw [polyOfVec_coeff]
  simpa [hsame] using hq

/-- the greedy polynomials have degree at most d - 1 -/
lemma natDegree_QOfGreedy_le (hd : 0 < d) (u : Fin d → E d)
    (huint : ∀ i : Fin d, IntFun d (u i)) (i : Fin d) :
    (QOfGreedy u huint i).natDegree ≤ d - 1 := by
  exact polyOfVec_natDegree_le hd (intOfFun (u := u) huint i)

theorem minkUpper_proved : MinkBox.minkUpper := by
  classical
  refine ⟨1, by norm_num, ?_⟩
  intro d hd2 α hinj v hv
  have hd : 0 < d := lt_of_lt_of_le (by norm_num : 0 < 2) hd2
  obtain ⟨u, huint, huflag, hpos, hmin⟩ := greedy_full hd hinj hv
  have hindep : LinearIndependent ℝ u := linearIndependent_of_nested u huflag
  obtain ⟨e, heint, heflag, hedet⟩ := adapted_exists u huint hindep
  have hprod : (∏ i : Fin d, gauge d α v (u i)) ≤ Dval d α v :=
    engine_bound_greedy hd hinj hv u huint huflag hmin e heint heflag hedet
  let Q : Fin d → Polynomial ℤ := QOfGreedy u huint
  let mu : Fin d → ℝ := fun i => gauge d α v (u i)
  refine ⟨Q, ?_, ?_, mu, ?_, ?_⟩
  · exact linIndepInt_QOfGreedy hd u huint hindep
  · intro i
    exact natDegree_QOfGreedy_le hd u huint i
  · intro i k
    simpa [Q, mu] using evalInt_bound hd hv u huint i k
  · have hpow : (d : ℝ) ^ (1 * (d : ℝ)) = (d : ℝ) ^ d := by
      rw [show 1 * (d : ℝ) = (d : ℝ) by ring]
      rw [Real.rpow_natCast]
    calc
      (∏ i : Fin d, mu i) = (∏ i : Fin d, gauge d α v (u i)) := rfl
      _ ≤ Dval d α v := hprod
      _ ≤ (d : ℝ) ^ (1 * (d : ℝ)) * Dval d α v := by
        rw [hpow]
        have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
          exact_mod_cast (le_trans (by norm_num : 1 ≤ (2 : ℕ)) hd2)
        have hone : 1 ≤ (d : ℝ) ^ d := by
          exact (one_le_pow₀ (a := (d : ℝ)) (n := d) hd1)
        simpa [mul_comm] using (le_mul_of_one_le_right (le_of_lt (Dval_pos d hinj hv)) hone)

end Submission.MinkUpperGlue
