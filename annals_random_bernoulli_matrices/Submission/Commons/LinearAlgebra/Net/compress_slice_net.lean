import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Submission.Commons.Topology.MetricSpace.sphere_net_cardinality

set_option autoImplicit false
open scoped BigOperators

namespace Commons.LinearAlgebra.Net

open Finset

noncomputable def sqNorm {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ i, (x i)^2
noncomputable def vecSum {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ i, x i

/-- `x` is (δ,ν)-compressible: unit, within Euclidean distance ν of a vector
of support at most δ·n (real comparison). -/
noncomputable def compressible {n : ℕ} (δ ν : ℝ) (x : Fin n → ℝ) : Prop :=
  sqNorm x = 1 ∧
  ∃ z : Fin n → ℝ, sqNorm (x - z) ≤ ν^2 ∧
    (((Finset.univ.filter (fun i => z i ≠ 0)).card : ℝ) ≤ δ * (n : ℝ))

/-- A slice: unit vectors with Σx ∈ [w·ℓ, w·(ℓ+1)). -/
noncomputable def slice {n : ℕ} (δ ν w : ℝ) (ℓ : ℤ) (x : Fin n → ℝ) : Prop :=
  compressible δ ν x ∧ w * (ℓ : ℝ) ≤ vecSum x ∧ vecSum x < w * ((ℓ : ℝ) + 1)



/-! ## ℓ² structure on coordinate vectors `Fin n → ℝ` -/

/-- Euclidean ℓ₂ norm (as a real) of a coordinate vector. -/
noncomputable def nrm {n : ℕ} (x : Fin n → ℝ) : ℝ := Real.sqrt (sqNorm x)

/-- Standard dot product on coordinate vectors. -/
noncomputable def dot {n : ℕ} (x y : Fin n → ℝ) : ℝ := ∑ i, x i * y i


lemma sqNorm_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ sqNorm x := by
  unfold sqNorm
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (x i))

lemma sqNorm_zero {n : ℕ} : sqNorm (0 : Fin n → ℝ) = 0 := by
  unfold sqNorm
  simp

lemma sqNorm_eq_zero_iff {n : ℕ} (x : Fin n → ℝ) : sqNorm x = 0 ↔ x = 0 := by
  unfold sqNorm
  constructor
  · intro h
    funext i
    have hi : (x i)^2 = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg (s := (Finset.univ : Finset (Fin n)))
        (f := fun j : Fin n => (x j)^2) (fun j _ => sq_nonneg (x j))).mp h i (Finset.mem_univ i)
    exact sq_eq_zero_iff.mp hi
  · intro h
    simp [h]

lemma nrm_sq {n : ℕ} (x : Fin n → ℝ) : (nrm x)^2 = sqNorm x := by
  dsimp [nrm]
  exact Real.sq_sqrt (sqNorm_nonneg x)

lemma sqNorm_eq_nrm_sq {n : ℕ} (x : Fin n → ℝ) : sqNorm x = (nrm x)^2 := (nrm_sq x).symm

lemma nrm_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ nrm x := Real.sqrt_nonneg _

lemma nrm_eq_zero_iff {n : ℕ} (x : Fin n → ℝ) : nrm x = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply (sqNorm_eq_zero_iff x).mp
    have : (nrm x)^2 = 0 := by rw [h, zero_pow]; norm_num
    exact (nrm_sq x).symm.trans this
  · intro hx
    simp [nrm, sqNorm, hx]

lemma nrm_pos_iff {n : ℕ} (x : Fin n → ℝ) : 0 < nrm x ↔ x ≠ 0 := by
  constructor
  · intro h h0
    simpa [nrm, sqNorm, h0] using h
  · intro hx
    by_contra h
    have : nrm x = 0 := le_antisymm (le_of_not_gt h) (nrm_nonneg x)
    exact hx ((nrm_eq_zero_iff x).mp this)



lemma dot_comm {n : ℕ} (x y : Fin n → ℝ) : dot x y = dot y x := by
  unfold dot
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma dot_add_left {n : ℕ} (x y z : Fin n → ℝ) : dot (x + y) z = dot x z + dot y z := by
  unfold dot
  simp [Finset.sum_add_distrib, add_mul]

lemma dot_neg_right {n : ℕ} (x y : Fin n → ℝ) : dot x (-y) = - dot x y := by
  unfold dot
  simp [Finset.sum_neg_distrib]

lemma dot_neg_left {n : ℕ} (x y : Fin n → ℝ) : dot (-x) y = - dot x y := by
  unfold dot
  simp [Finset.sum_neg_distrib]

lemma sqNorm_neg {n : ℕ} (x : Fin n → ℝ) : sqNorm (-x) = sqNorm x := by
  unfold sqNorm
  apply Finset.sum_congr rfl
  intro i hi
  simp

lemma sqNorm_add {n : ℕ} (x y : Fin n → ℝ) :
    sqNorm (x + y) = sqNorm x + 2 * dot x y + sqNorm y := by
  unfold sqNorm dot
  calc
    (∑ i, (x i + y i)^2) = ∑ i, ((x i)^2 + (2 * (x i * y i)) + (y i)^2) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (∑ i, (x i)^2) + (∑ i, 2 * (x i * y i)) + (∑ i, (y i)^2) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = (∑ i, (x i)^2) + 2 * (∑ i, x i * y i) + (∑ i, (y i)^2) := by
      rw [Finset.mul_sum]

lemma sqNorm_sub {n : ℕ} (x y : Fin n → ℝ) :
    sqNorm (x - y) = sqNorm x - 2 * dot x y + sqNorm y := by
  have h := sqNorm_add x (-y)
  have h1 : sqNorm (-y) = sqNorm y := sqNorm_neg y
  have h2 : dot x (-y) = -dot x y := dot_neg_right x y
  rw [sub_eq_add_neg, h, h1, h2]
  ring

lemma dot_sq_le_sqNorm_mul {n : ℕ} (x y : Fin n → ℝ) :
    (dot x y)^2 ≤ sqNorm x * sqNorm y := by
  unfold dot sqNorm
  simpa using (Finset.sum_mul_sq_le_sq_mul_sq (s := (Finset.univ : Finset (Fin n))) x y)

lemma abs_dot_le_nrm_mul {n : ℕ} (x y : Fin n → ℝ) : |dot x y| ≤ nrm x * nrm y := by
  have hsq : (dot x y)^2 ≤ (nrm x * nrm y)^2 := by
    calc
      (dot x y)^2 ≤ sqNorm x * sqNorm y := dot_sq_le_sqNorm_mul x y
      _ = (nrm x)^2 * (nrm y)^2 := by rw [← nrm_sq, ← nrm_sq]
      _ = (nrm x * nrm y)^2 := by ring
  have hmul : 0 ≤ nrm x * nrm y := mul_nonneg (nrm_nonneg x) (nrm_nonneg y)
  rw [← abs_of_nonneg hmul]
  exact (sq_le_sq.mp hsq)

lemma sq_le_of_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a^2 ≤ b^2) : a ≤ b := by
  have h' : |a| ≤ |b| := sq_le_sq.mp h
  simpa [abs_of_nonneg ha, abs_of_nonneg hb] using h'

lemma nrm_add_le {n : ℕ} (x y : Fin n → ℝ) : nrm (x + y) ≤ nrm x + nrm y := by
  apply sq_le_of_sq (nrm_nonneg (x + y))
  · exact add_nonneg (nrm_nonneg x) (nrm_nonneg y)
  · calc
      (nrm (x + y))^2 = sqNorm (x + y) := nrm_sq (x + y)
      _ = sqNorm x + 2 * dot x y + sqNorm y := sqNorm_add x y
      _ ≤ (nrm x)^2 + 2 * (nrm x * nrm y) + (nrm y)^2 := by
        have hd : dot x y ≤ nrm x * nrm y := le_trans (le_abs_self _) (abs_dot_le_nrm_mul x y)
        nlinarith [nrm_sq x, nrm_sq y]
      _ = (nrm x + nrm y)^2 := by ring

lemma nrm_neg {n : ℕ} (x : Fin n → ℝ) : nrm (-x) = nrm x := by
  unfold nrm
  rw [sqNorm_neg]

lemma nrm_sub_le {n : ℕ} (x y : Fin n → ℝ) : nrm (x - y) ≤ nrm x + nrm y := by
  have h := nrm_add_le x (-y)
  simpa [sub_eq_add_neg, nrm_neg] using h

lemma nrm_sub_le_add_sub {n : ℕ} (x y z : Fin n → ℝ) :
    nrm (x - z) ≤ nrm (x - y) + nrm (y - z) := by
  have h : x - z = (x - y) + (y - z) := by
    ext i
    simp
  rw [h]
  exact nrm_add_le (x - y) (y - z)

lemma sqNorm_smul {n : ℕ} (a : ℝ) (x : Fin n → ℝ) : sqNorm (a • x) = a^2 * sqNorm x := by
  unfold sqNorm
  calc
    (∑ i, (a * x i)^2) = ∑ i, a^2 * (x i)^2 := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = a^2 * (∑ i, (x i)^2) := by rw [Finset.mul_sum]

lemma nrm_smul {n : ℕ} (a : ℝ) (x : Fin n → ℝ) : nrm (a • x) = |a| * nrm x := by
  unfold nrm
  rw [sqNorm_smul]
  calc
    Real.sqrt (a^2 * sqNorm x) = Real.sqrt (a^2) * Real.sqrt (sqNorm x) :=
      Real.sqrt_mul (sq_nonneg a) (sqNorm x)
    _ = |a| * Real.sqrt (sqNorm x) := by rw [Real.sqrt_sq_eq_abs]

lemma nrm_smul_of_nonneg {n : ℕ} {a : ℝ} (x : Fin n → ℝ) (ha : 0 ≤ a) : nrm (a • x) = a * nrm x := by
  rw [nrm_smul, abs_of_nonneg ha]
def res {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if i ∈ S then x i else 0

/-- Support of a coordinate vector. -/
noncomputable def supp {n : ℕ} (x : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i ≠ 0)

@[simp] lemma res_apply {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ℝ) (i : Fin n) :
    res S x i = if i ∈ S then x i else 0 := rfl

lemma res_self_of_supp {n : ℕ} (S : Finset (Fin n)) {x : Fin n → ℝ}
    (h : ∀ i : Fin n, i ∉ S → x i = 0) : res S x = x := by
  funext i
  by_cases hi : i ∈ S
  · simp [res, hi]
  · simp [res, hi, h i hi]

lemma res_eq_zero_of_not_mem {n : ℕ} (S : Finset (Fin n)) {x : Fin n → ℝ} {i : Fin n}
    (hi : i ∉ S) : res S x i = 0 := by
  simp [res, hi]

lemma supp_res {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ℝ) : supp (res S x) ⊆ S := by
  intro i hi
  by_contra hnot
  have hi' : res S x i ≠ 0 := (Finset.mem_filter.mp hi).2
  simp [res, hnot] at hi'

lemma mem_supp {n : ℕ} (x : Fin n → ℝ) {i : Fin n} : i ∈ supp x ↔ x i ≠ 0 := by
  unfold supp
  simp

lemma not_mem_supp {n : ℕ} (x : Fin n → ℝ) {i : Fin n} : i ∉ supp x ↔ x i = 0 := by
  unfold supp
  simp

lemma sqNorm_res {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ℝ) :
    sqNorm (res S x) = ∑ i ∈ S, (x i)^2 := by
  unfold sqNorm res
  calc
    (∑ i : Fin n, (if i ∈ S then x i else 0)^2)
        = ∑ i : Fin n, if i ∈ S then (x i)^2 else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          by_cases hiS : i ∈ S <;> simp [hiS]
    _ = ∑ i ∈ (Finset.univ.filter (fun i : Fin n => i ∈ S)), (x i)^2 := by
          rw [Finset.sum_filter]
    _ = ∑ i ∈ S, (x i)^2 := by
          apply Finset.sum_congr
          · ext i; simp
          · intro i hi; rfl

lemma res_add {n : ℕ} (S : Finset (Fin n)) (x y : Fin n → ℝ) :
    res S (x + y) = res S x + res S y := by
  funext i
  by_cases hi : i ∈ S <;> simp [res, hi]

lemma res_add_eq {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ℝ) :
    res S x + (x - res S x) = x := by
  funext i
  by_cases hi : i ∈ S <;> simp [res, hi]

lemma dot_supp_left_res_sub_zero {n : ℕ} (S : Finset (Fin n)) {w : Fin n → ℝ}
    (hw : ∀ i : Fin n, i ∉ S → w i = 0) (x : Fin n → ℝ) :
    dot w (x - res S x) = 0 := by
  unfold dot
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hiS : i ∈ S
  · have : (x - res S x) i = 0 := by
      simp [res, hiS]
    simp [this]
  · simp [res, hiS, hw i hiS]

lemma sqNorm_decomp {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ℝ) :
    sqNorm x = sqNorm (res S x) + sqNorm (x - res S x) := by
  have hx : x = res S x + (x - res S x) := (res_add_eq S x).symm
  rw [hx, sqNorm_add]
  have hd : dot (res S x) (x - res S x) = 0 := by
    apply dot_supp_left_res_sub_zero S (w := res S x)
    intro i hi
    simp [res, hi]
  simp [hd]

lemma sqNorm_sub_ge_sqNorm_sub_res {n : ℕ} (S : Finset (Fin n)) (x z : Fin n → ℝ)
    (hz : ∀ i : Fin n, i ∉ S → z i = 0) :
    sqNorm (x - res S x) ≤ sqNorm (x - z) := by
  -- x - z = (res S x - z) + (x - res S x) with orthogonal pieces
  have hzres : res S z = z := res_self_of_supp S hz
  have h1 : res S x - z = res S x - res S z := by rw [hzres]
  have hx : x - z = (res S x - z) + (x - res S x) := by
    ext i
    by_cases hiS : i ∈ S
    · simp [res, hiS]
    · simp [res, hiS, hz i hiS]
  rw [hx, sqNorm_add]
  have hd : dot (res S x - z) (x - res S x) = 0 := by
    rw [sub_eq_add_neg, dot_add_left, dot_neg_left]
    have h1' : dot (res S x) (x - res S x) = 0 := by
      apply dot_supp_left_res_sub_zero S (w := res S x)
      intro i hi; simp [res, hi]
    have h2' : dot z (x - res S x) = 0 := by
      apply dot_supp_left_res_sub_zero S (w := z) hz
    simp [h1', h2']
  rw [hd]
  nlinarith [sqNorm_nonneg (res S x - z)]

lemma nrm_le_of_sqNorm_le_sq {n : ℕ} {x : Fin n → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (h : sqNorm x ≤ a^2) : nrm x ≤ a := by
  apply sq_le_of_sq (nrm_nonneg x) ha
  rwa [nrm_sq]

lemma sqNorm_le_sq_of_nrm_le {n : ℕ} {x : Fin n → ℝ} {a : ℝ} (_ha : 0 ≤ a)
    (h : nrm x ≤ a) : sqNorm x ≤ a^2 := by
  have : (nrm x)^2 ≤ a^2 := by
    exact pow_le_pow_left₀ (nrm_nonneg x) h 2
  simpa [nrm_sq] using this

lemma nrm_smul_sub_smul_le {n : ℕ} (a b : ℝ) (x y : Fin n → ℝ) :
    nrm (a • x - b • y) ≤ |a| * nrm (x - y) + |a - b| * nrm y := by
  have h : a • x - b • y = a • (x - y) + (a - b) • y := by
    ext i
    simp [Pi.smul_apply, sub_eq_add_neg, add_mul]
  rw [h]
  calc
    nrm (a • (x - y) + (a - b) • y) ≤ nrm (a • (x - y)) + nrm ((a - b) • y) := nrm_add_le _ _
    _ = |a| * nrm (x - y) + |a - b| * nrm y := by rw [nrm_smul, nrm_smul]

lemma sqNorm_eq_one_of_nrm {n : ℕ} (x : Fin n → ℝ) : sqNorm x = 1 ↔ nrm x = 1 := by
  constructor
  · intro h
    have hs : (nrm x)^2 = 1 := by rw [nrm_sq, h]
    have hnn : 0 ≤ nrm x := nrm_nonneg x
    nlinarith
  · intro h
    rw [← nrm_sq, h, one_pow]


/-! ## Direction (normalised S-projection) and bucket diameter -/

/-- Normalised projection of `x` onto the coordinate subspace `S` (unit vector supported on `S`). -/
noncomputable def dir {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ℝ) : Fin n → ℝ :=
  (nrm (res S x))⁻¹ • res S x

lemma sqNorm_dir_eq_one {n : ℕ} (S : Finset (Fin n)) {x : Fin n → ℝ}
    (hres : res S x ≠ 0) : sqNorm (dir S x) = 1 := by
  have ha : nrm (res S x) ≠ 0 := by
    intro h
    exact hres ((nrm_eq_zero_iff (res S x)).mp h)
  unfold dir
  rw [sqNorm_smul]
  rw [(nrm_sq (res S x)).symm]
  field_simp [ha]

lemma res_eq_nrm_smul_dir {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ℝ)
    (hres : res S x ≠ 0) : res S x = nrm (res S x) • dir S x := by
  unfold dir
  ext i
  simp [Pi.smul_apply]
  field_simp [show nrm (res S x) ≠ 0 by
    intro h; exact hres ((nrm_eq_zero_iff (res S x)).mp h)]

lemma sqrt_one_sub_sq_sub_le {ν : ℝ} (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) :
    1 - Real.sqrt (1 - ν^2) ≤ ν^2 := by
  have h01 : 0 ≤ 1 - ν^2 := by nlinarith
  have hsq : (1 - ν^2)^2 ≤ 1 - ν^2 := by nlinarith
  have hle : 1 - ν^2 ≤ Real.sqrt (1 - ν^2) := by
    exact sq_le_of_sq h01 (Real.sqrt_nonneg _) (by simpa [Real.sq_sqrt h01] using hsq)
  nlinarith

lemma nrm_dir_sub_le_of_nrm_p {n : ℕ} (S : Finset (Fin n)) {x₁ x₂ p : Fin n → ℝ}
    (η : ℝ) (hd1 : nrm (dir S x₁ - p) ≤ η) (hd2 : nrm (dir S x₂ - p) ≤ η) :
    nrm (dir S x₁ - dir S x₂) ≤ 2 * η := by
  have h := nrm_sub_le_add_sub (dir S x₁) p (dir S x₂)
  have hfun : dir S x₂ - p = -(p - dir S x₂) := by
    ext i
    simp
  have hsym : nrm (p - dir S x₂) = nrm (dir S x₂ - p) := by
    calc
      nrm (p - dir S x₂) = nrm (-(p - dir S x₂)) := (nrm_neg (p - dir S x₂)).symm
      _ = nrm (dir S x₂ - p) := by rw [← hfun]
  calc
    nrm (dir S x₁ - dir S x₂) ≤ nrm (dir S x₁ - p) + nrm (p - dir S x₂) := h
    _ ≤ η + η := by rw [hsym]; nlinarith
    _ = 2 * η := by ring

lemma nrm_smul_sub_smul_le_one {n : ℕ} {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (b : ℝ) (d₁ d₂ : Fin n → ℝ) :
    nrm (a • d₁ - b • d₂) ≤ nrm (d₁ - d₂) + |a - b| * nrm d₂ := by
  have h := nrm_smul_sub_smul_le a b d₁ d₂
  calc
    nrm (a • d₁ - b • d₂) ≤ |a| * nrm (d₁ - d₂) + |a - b| * nrm d₂ := h
    _ ≤ nrm (d₁ - d₂) + |a - b| * nrm d₂ := by
      have hmain : |a| * nrm (d₁ - d₂) ≤ 1 * nrm (d₁ - d₂) := by
        exact mul_le_mul_of_nonneg_right (by simpa [abs_of_nonneg ha0] using ha1) (nrm_nonneg (d₁ - d₂))
      nlinarith
    _ = nrm (d₁ - d₂) + |a - b| * nrm d₂ := by ring

lemma alpha_bounds {n : ℕ} (S : Finset (Fin n)) {x : Fin n → ℝ} {ν : ℝ}
    (hu : sqNorm x = 1) (hv : nrm (x - res S x) ≤ ν) (hν0 : 0 ≤ ν) (hν1 : ν < 1) :
    Real.sqrt (1 - ν^2) ≤ nrm (res S x) ∧ nrm (res S x) ≤ 1 ∧ nrm (res S x) ≠ 0 := by
  have hdecomp := sqNorm_decomp S x
  have hnorm : sqNorm (x - res S x) ≤ ν^2 := sqNorm_le_sq_of_nrm_le hν0 hv
  have h01 : 0 ≤ 1 - ν^2 := by nlinarith
  have hsq : (nrm (res S x))^2 ≥ 1 - ν^2 := by
    rw [nrm_sq]
    nlinarith [hdecomp, hnorm]
  have hnn : 0 ≤ nrm (res S x) := nrm_nonneg _
  have hL : Real.sqrt (1 - ν^2) ≤ nrm (res S x) := by
    apply sq_le_of_sq
    · exact Real.sqrt_nonneg _
    · exact hnn
    · rw [Real.sq_sqrt h01]
      exact hsq
  have hle1 : nrm (res S x) ≤ 1 := by
    have hs : (nrm (res S x))^2 ≤ 1 := by
      rw [nrm_sq]
      nlinarith [hu, hdecomp, sqNorm_nonneg (x - res S x)]
    exact sq_le_of_sq hnn (by norm_num : 0 ≤ (1 : ℝ)) (by simpa using hs)
  have hne : nrm (res S x) ≠ 0 := by
    intro hz
    have hz' : Real.sqrt (1 - ν^2) ≤ 0 := by simpa [hz] using hL
    nlinarith [Real.sq_sqrt h01, Real.sqrt_nonneg (1 - ν^2), hz', hν1]
  exact ⟨hL, hle1, hne⟩

/-- Diameter bound for the bucket over a grid point `p` (Euclidean metric on the slice). -/
lemma bucket_diam {n : ℕ} (S : Finset (Fin n)) {x₁ x₂ p : Fin n → ℝ} (η ν : ℝ)
    (hν0 : 0 ≤ ν) (hν1 : ν < 1)
    (hu₁ : sqNorm x₁ = 1) (hu₂ : sqNorm x₂ = 1)
    (hv₁ : nrm (x₁ - res S x₁) ≤ ν) (hv₂ : nrm (x₂ - res S x₂) ≤ ν)
    (hd₁ : nrm (dir S x₁ - p) ≤ η) (hd₂ : nrm (dir S x₂ - p) ≤ η) :
    nrm (x₁ - x₂) ≤ 2 * η + 2 * ν + ν^2 := by
  let v₁ : Fin n → ℝ := x₁ - res S x₁
  let v₂ : Fin n → ℝ := x₂ - res S x₂
  let a₁ : ℝ := nrm (res S x₁)
  let a₂ : ℝ := nrm (res S x₂)
  let d₁ : Fin n → ℝ := dir S x₁
  let d₂ : Fin n → ℝ := dir S x₂
  have hab₁ := alpha_bounds S (x := x₁) (ν := ν) hu₁ hv₁ hν0 hν1
  have hab₂ := alpha_bounds S (x := x₂) (ν := ν) hu₂ hv₂ hν0 hν1
  have ha₁ : a₁ ≠ 0 := hab₁.2.2
  have ha₂ : a₂ ≠ 0 := hab₂.2.2
  have hres₁ne : res S x₁ ≠ 0 := by
    intro h
    apply ha₁
    simpa [a₁] using (nrm_eq_zero_iff (res S x₁)).mpr h
  have hres₂ne : res S x₂ ≠ 0 := by
    intro h
    apply ha₂
    simpa [a₂] using (nrm_eq_zero_iff (res S x₂)).mpr h
  have hx₁ : a₁ • d₁ + v₁ = x₁ := by
    dsimp [v₁, d₁]
    rw [← res_eq_nrm_smul_dir S x₁ hres₁ne]
    exact res_add_eq S x₁
  have hx₂ : a₂ • d₂ + v₂ = x₂ := by
    dsimp [v₂, d₂]
    rw [← res_eq_nrm_smul_dir S x₂ hres₂ne]
    exact res_add_eq S x₂
  have hd₂nrm : nrm d₂ = 1 := by
    dsimp [d₂]
    exact (sqNorm_eq_one_of_nrm (dir S x₂)).mp (sqNorm_dir_eq_one S hres₂ne)
  have hd₁₂ : nrm (d₁ - d₂) ≤ 2 * η := by
    dsimp [d₁, d₂]
    exact nrm_dir_sub_le_of_nrm_p S (η := η) hd₁ hd₂
  have habs : |a₁ - a₂| ≤ 1 - Real.sqrt (1 - ν^2) := by
    have hL₁ : Real.sqrt (1 - ν^2) ≤ a₁ := by simpa [a₁] using hab₁.1
    have hL₂ : Real.sqrt (1 - ν^2) ≤ a₂ := by simpa [a₂] using hab₂.1
    have hle1₁ : a₁ ≤ 1 := by simpa [a₁] using hab₁.2.1
    have hle1₂ : a₂ ≤ 1 := by simpa [a₂] using hab₂.2.1
    have h1 : a₁ - a₂ ≤ 1 - Real.sqrt (1 - ν^2) := by nlinarith
    have h2 : a₂ - a₁ ≤ 1 - Real.sqrt (1 - ν^2) := by nlinarith
    rw [abs_le]
    constructor
    · linarith
    · linarith
  have hsq_sub : 1 - Real.sqrt (1 - ν^2) ≤ ν^2 := sqrt_one_sub_sq_sub_le hν0 (le_of_lt hν1)
  have hmain : nrm (a₁ • d₁ - a₂ • d₂) ≤ 2 * η + |a₁ - a₂| := by
    have h : nrm (a₁ • d₁ - a₂ • d₂) ≤ nrm (d₁ - d₂) + |a₁ - a₂| * nrm d₂ := by
      exact nrm_smul_sub_smul_le_one (a := a₁) (b := a₂) (d₁ := d₁) (d₂ := d₂)
        (by simpa [a₁] using (nrm_nonneg (res S x₁))) (by simpa [a₁] using hab₁.2.1)
    nlinarith [hd₁₂, hd₂nrm, h]
  have hvv : nrm (v₁ - v₂) ≤ nrm v₁ + nrm v₂ := by
    dsimp [v₁, v₂]
    exact nrm_sub_le (x₁ - res S x₁) (x₂ - res S x₂)
  calc
    nrm (x₁ - x₂) = nrm ((a₁ • d₁ + v₁) - (a₂ • d₂ + v₂)) := by
      rw [← hx₁, ← hx₂]
    _ ≤ nrm (a₁ • d₁ - a₂ • d₂) + nrm (v₁ - v₂) := by
      have hsub : (a₁ • d₁ + v₁) - (a₂ • d₂ + v₂) = (a₁ • d₁ - a₂ • d₂) + (v₁ - v₂) := by
        ext i
        simp
        ring
      rw [hsub]
      exact nrm_add_le _ _
    _ ≤ (2 * η + |a₁ - a₂|) + (nrm v₁ + nrm v₂) := by
      exact add_le_add hmain hvv
    _ ≤ 2 * η + 2 * ν + ν^2 := by
      dsimp [v₁, v₂] at hv₁ hv₂ ⊢
      nlinarith [habs, hsq_sub, hv₁, hv₂]


noncomputable def coext {n : ℕ} (S : Finset (Fin n)) (g : {i : Fin n // i ∈ S} → ℝ) : Fin n → ℝ :=
  fun i => if h : i ∈ S then g ⟨i, h⟩ else 0

/-- Workhorse identity: extension by zero from the coordinate subset reindexed by `τ`
has the same square-sum as the underlying function on `Fin d`. -/
lemma sqNorm_coext_eq {n d : ℕ} (S : Finset (Fin n)) (τ : {i : Fin n // i ∈ S} ≃ Fin d)
    (h : Fin d → ℝ) :
    (∑ i : Fin n, (if hi : i ∈ S then h (τ ⟨i,hi⟩) else 0)^2) = ∑ k : Fin d, (h k)^2 := by
  classical
  calc
    (∑ i : Fin n, (if hi : i ∈ S then h (τ ⟨i,hi⟩) else 0)^2)
        = ∑ i : Fin n, (if hi : i ∈ S then (h (τ ⟨i,hi⟩))^2 else 0) := by
          apply Finset.sum_congr rfl
          intro i hi
          by_cases hs : i ∈ S <;> simp [hs]
    _ = ∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i : Fin n => i ∈ S),
            (if hi : i ∈ S then (h (τ ⟨i,hi⟩))^2 else 0) := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro i hi
          by_cases hs : i ∈ S <;> simp [hs]
    _ = ∑ k : Fin d, (h k)^2 := by
          symm
          rw [show (∑ k : Fin d, (h k)^2) = ∑ k ∈ (Finset.univ : Finset (Fin d)), (h k)^2 by rfl]
          refine Finset.sum_bij (s := (Finset.univ : Finset (Fin d)))
            (t := (Finset.univ : Finset (Fin n)).filter (fun i : Fin n => i ∈ S))
            (f := fun k => (h k)^2)
            (g := fun i => if hi : i ∈ S then (h (τ ⟨i,hi⟩))^2 else 0)
            (i := fun k hk => (τ.symm k).1) ?hi ?inj ?surj ?values
          · intro k hk
            simp [(τ.symm k).2]
          · intro k₁ hk₁ k₂ hk₂ hmain
            apply Equiv.injective τ.symm
            exact Subtype.ext hmain
          · intro i hi
            refine ⟨τ ⟨i, (Finset.mem_filter.mp hi).2⟩, by simp, ?_⟩
            rw [Equiv.symm_apply_apply]
          · intro k hk
            dsimp
            have hs : (τ.symm k).1 ∈ S := (τ.symm k).2
            simp [hs]

/-! ## Transport from `EuclideanSpace ℝ (Fin d)` sphere-nets to functions supported on `S` -/

lemma sqNorm_coext {n d : ℕ} (S : Finset (Fin n)) (τ : {i : Fin n // i ∈ S} ≃ Fin d)
    (h : Fin d → ℝ) :
    sqNorm (coext S (fun j : {i : Fin n // i ∈ S} => h (τ j))) = ∑ k : Fin d, (h k)^2 := by
  unfold sqNorm coext
  exact sqNorm_coext_eq S τ h

lemma sum_equiv_left {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) (f : β → ℝ) :
    (∑ a : α, f (e a)) = ∑ b : β, f b := by
  simpa using
    (Finset.sum_equiv (s := (Finset.univ : Finset α)) (t := (Finset.univ : Finset β)) e
      (by intro a; simp) (by intro a ha; rfl))

lemma EuclideanSpace_norm_sq_eq_sqNorm {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) :
    ‖a‖^2 = sqNorm (fun k : Fin d => a k) := by
  rw [PiLp.norm_sq_eq_of_L2 (β := fun _ : Fin d => ℝ) a]
  simp [sqNorm, sq_abs]

lemma EuclideanSpace_norm_sub_sq_eq_sqNorm {d : ℕ} (a b : EuclideanSpace ℝ (Fin d)) :
    ‖a - b‖^2 = sqNorm (fun k : Fin d => a k - b k) := by
  rw [PiLp.norm_sq_eq_of_L2 (β := fun _ : Fin d => ℝ) (a - b)]
  simp [sqNorm, sq_abs]

lemma norm_eq_nrm {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) :
    ‖a‖ = nrm (fun k : Fin d => a k) := by
  have heq₁ : ‖a‖^2 = (nrm (fun k : Fin d => a k))^2 := by
    rw [EuclideanSpace_norm_sq_eq_sqNorm, sqNorm_eq_nrm_sq]
  have heq₂ : (nrm (fun k : Fin d => a k))^2 = ‖a‖^2 := heq₁.symm
  apply le_antisymm
  · exact sq_le_of_sq (norm_nonneg _) (nrm_nonneg _) (le_of_eq heq₁)
  · exact sq_le_of_sq (nrm_nonneg _) (norm_nonneg _) (le_of_eq heq₂)

lemma norm_sub_eq_nrm {d : ℕ} (a b : EuclideanSpace ℝ (Fin d)) :
    ‖a - b‖ = nrm (fun k : Fin d => a k - b k) := by
  have heq₁ : ‖a - b‖^2 = (nrm (fun k : Fin d => a k - b k))^2 := by
    rw [EuclideanSpace_norm_sub_sq_eq_sqNorm, sqNorm_eq_nrm_sq]
  have heq₂ : (nrm (fun k : Fin d => a k - b k))^2 = ‖a - b‖^2 := heq₁.symm
  apply le_antisymm
  · exact sq_le_of_sq (norm_nonneg _) (nrm_nonneg _) (le_of_eq heq₁)
  · exact sq_le_of_sq (nrm_nonneg _) (norm_nonneg _) (le_of_eq heq₂)

/-- A coordinate-`S`-supported unit sphere net (obtained by transporting the Euclidean sphere net
of dimension `S.card`), with explicit cardinality bound. -/
lemma exists_support_unit_net :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (n : ℕ) (S : Finset (Fin n)) (ε : ℝ), 0 < ε → ε ≤ 1 →
      ∃ G : Finset (Fin n → ℝ),
        (∀ g ∈ G, sqNorm g = 1 ∧ ∀ i, i ∉ S → g i = 0) ∧
        (∀ u : Fin n → ℝ, sqNorm u = 1 → (∀ i, i ∉ S → u i = 0) →
           ∃ g ∈ G, nrm (u - g) ≤ ε) ∧
        ((G.card : ℝ) ≤ (C / ε) ^ S.card) := by
  classical
  rcases Commons.Topology.MetricSpace.sphere_net_cardinality with ⟨C, hC1, hnet⟩
  refine ⟨C, hC1, ?_⟩
  intro n S ε hε0 hε1
  let ι : Type := {i : Fin n // i ∈ S}
  let d : ℕ := Fintype.card ι
  have hd : d = S.card := by
    dsimp [d, ι]
    simp
  let τ : ι ≃ Fin d := by
    dsimp [d, ι]
    exact Fintype.equivFin ι
  rcases hnet d ε hε0 hε1 with ⟨A, hAfin, hAunit, hAcover, hAcard⟩
  let toG : EuclideanSpace ℝ (Fin d) → (Fin n → ℝ) :=
    fun a => coext S (fun j : ι => a (τ j))
  let G : Finset (Fin n → ℝ) := (hAfin.toFinset).image toG
  refine ⟨G, ?_, ?_, ?_⟩
  · intro g hg
    rcases (Finset.mem_image.mp hg) with ⟨a, haA, rfl⟩
    have hA : a ∈ A := (Set.Finite.mem_toFinset hAfin).mp haA
    have ha1 : ‖a‖ = 1 := hAunit a hA
    have hgsq : sqNorm (toG a) = 1 := by
      dsimp [toG]
      have h1 : sqNorm (coext S (fun j : ι => a (τ j))) = ‖a‖^2 := by
        rw [show sqNorm (coext S (fun j : ι => a (τ j)))
              = sqNorm (coext S (fun j : ι => (fun k : Fin d => a k) (τ j))) by rfl]
        rw [sqNorm_coext]
        rw [EuclideanSpace_norm_sq_eq_sqNorm a]
        rfl
      rw [h1]
      rw [ha1]
      norm_num
    have hgsup : ∀ i : Fin n, i ∉ S → toG a i = 0 := by
      intro i hi
      dsimp [toG]
      simp [coext, hi]
    exact ⟨hgsq, hgsup⟩
  · intro u hu hsup
    let ure : Fin d → ℝ := fun k => u (τ.symm k).1
    have hsq_ure : sqNorm ure = 1 := by
      have hcoext : coext S (fun j : ι => ure (τ j)) = u := by
        funext i
        by_cases hs : i ∈ S
        · simp [coext, ure, hs]
        · have hui : u i = 0 := hsup i hs
          simp [coext, hs, hui]
      have h1 : sqNorm (coext S (fun j : ι => ure (τ j))) = ∑ k : Fin d, (ure k)^2 := by
        simpa [ure] using (sqNorm_coext S τ ure)
      calc
        sqNorm ure = ∑ k : Fin d, (ure k)^2 := by rw [sqNorm]
        _ = sqNorm (coext S (fun j : ι => ure (τ j))) := h1.symm
        _ = sqNorm u := by rw [hcoext]
        _ = 1 := hu
    let y : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 ure
    have hy : ‖y‖ = 1 := by
      have hsq : ‖y‖^2 = 1 := by
        calc
          ‖y‖^2 = sqNorm ure := by
            rw [EuclideanSpace_norm_sq_eq_sqNorm y]
          _ = 1 := hsq_ure
      have hnn : 0 ≤ ‖y‖ := norm_nonneg _
      nlinarith
    rcases hAcover y hy with ⟨a, haA, hya⟩
    refine ⟨toG a, ?_, ?_⟩
    · exact (Finset.mem_image.mpr ⟨a, (Set.Finite.mem_toFinset hAfin).mpr haA, rfl⟩)
    · -- nrm (u - toG a) ≤ ε
      have hdiff : u - toG a = coext S (fun j : ι => (ure (τ j) - a (τ j))) := by
        funext i
        by_cases hs : i ∈ S
        · simp [toG, coext, ure, hs]
        · simp [toG, coext, hs, hsup i hs]
      have h1 : sqNorm (u - toG a) = ∑ k : Fin d, (ure k - a k)^2 := by
        rw [hdiff]
        exact sqNorm_coext S τ (fun k : Fin d => ure k - a k)
      have h2 : ∑ k : Fin d, (ure k - a k)^2 = ‖y - a‖^2 := by
        rw [EuclideanSpace_norm_sub_sq_eq_sqNorm y a]
        congr 1
      have hsq : sqNorm (u - toG a) ≤ ε^2 := by
        calc
          sqNorm (u - toG a) = ‖y - a‖^2 := by rw [h1, h2]
          _ ≤ ε^2 := by
            exact pow_le_pow_left₀ (norm_nonneg (y - a)) hya 2
      exact nrm_le_of_sqNorm_le_sq (le_of_lt hε0) hsq
  · -- cardinality bound
    have h1 : (G.card : ℝ) ≤ ((hAfin.toFinset).card : ℝ) := by
      dsimp [G]
      exact_mod_cast (Finset.card_image_le)
    have h2 : ((hAfin.toFinset).card : ℝ) = (A.ncard : ℝ) := by
      rw [Set.ncard_eq_toFinset_card A hAfin]
    calc
      (G.card : ℝ) ≤ ((hAfin.toFinset).card : ℝ) := h1
      _ = (A.ncard : ℝ) := h2
      _ ≤ (C / ε) ^ d := hAcard
      _ = (C / ε) ^ S.card := by rw [hd]


/-! ## Per-subset slice covering -/

lemma dir_supported {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ℝ) {i : Fin n} (hi : i ∉ S) :
    dir S x i = 0 := by
  unfold dir
  simp [res, hi]

lemma nrm_sub_res_le_of_sqNorm_sub {n : ℕ} (S : Finset (Fin n)) (x z : Fin n → ℝ) (ν : ℝ)
    (hν0 : 0 ≤ ν) (hz : ∀ i : Fin n, i ∉ S → z i = 0) (hsq : sqNorm (x - z) ≤ ν^2) :
    nrm (x - res S x) ≤ ν := by
  apply nrm_le_of_sqNorm_le_sq hν0
  exact le_trans (sqNorm_sub_ge_sqNorm_sub_res S x z hz) hsq

/-- For a fixed support `S`, the part of the slice within Euclidean distance `ν` of `V_S`
admits an `R`-net (net points inside the slice) of cardinality at most `G.card`,
where `G` is an `η`-net of the unit sphere of `V_S` with `2η + 2ν + ν² ≤ R`. -/
lemma perS_slice_cover {n : ℕ} {δ ν w : ℝ} {ℓ : ℤ} {S : Finset (Fin n)} {η R : ℝ}
    (hν0 : 0 ≤ ν) (hν1 : ν < 1) (hR0 : 0 ≤ R)
    (hη_ν : 2 * η + 2 * ν + ν^2 ≤ R)
    (G : Finset (Fin n → ℝ))
    (hG1 : ∀ g ∈ G, sqNorm g = 1)
    (hG2 : ∀ g ∈ G, ∀ i : Fin n, i ∉ S → g i = 0)
    (hG3 : ∀ u : Fin n → ℝ, sqNorm u = 1 → (∀ i : Fin n, i ∉ S → u i = 0) →
           ∃ g ∈ G, nrm (u - g) ≤ η) :
    ∃ NetS : Finset (Fin n → ℝ),
      (∀ y ∈ NetS, slice δ ν w ℓ y) ∧
      (∀ x : Fin n → ℝ, slice δ ν w ℓ x →
         (∃ z : Fin n → ℝ, sqNorm (x - z) ≤ ν^2 ∧ (∀ i : Fin n, i ∉ S → z i = 0)) →
         ∃ y ∈ NetS, sqNorm (y - x) ≤ R^2) ∧
      (NetS.card ≤ G.card) := by
  classical
  let pred : (Fin n → ℝ) → (Fin n → ℝ) → Prop := fun g x =>
    slice δ ν w ℓ x ∧ nrm (dir S x - g) ≤ η ∧ nrm (x - res S x) ≤ ν
  let NetS : Finset (Fin n → ℝ) :=
    ((G.filter (fun g => ∃ x : Fin n → ℝ, pred g x)).attach).image
      (fun t : {g : Fin n → ℝ // g ∈ G.filter (fun g => ∃ x : Fin n → ℝ, pred g x)} =>
         Classical.choose (Finset.mem_filter.mp t.2).2)
  refine ⟨NetS, ?_, ?_, ?_⟩
  · -- net points are in the slice
    intro y hy
    rcases (Finset.mem_image.mp hy) with ⟨t, ht, rfl⟩
    have ht' : t.1 ∈ G.filter (fun g => ∃ x : Fin n → ℝ, pred g x) := t.2
    have hw : ∃ x : Fin n → ℝ, pred t.1 x := (Finset.mem_filter.mp ht').2
    have hpred : pred t.1 (Classical.choose hw) := Classical.choose_spec hw
    exact hpred.1
  · -- covering
    intro x hx hxz
    rcases hxz with ⟨z, hzsq, hzsup⟩
    have hx1 : sqNorm x = 1 := hx.1.1
    have hvx : nrm (x - res S x) ≤ ν := nrm_sub_res_le_of_sqNorm_sub S x z ν hν0 hzsup hzsq
    have hab := alpha_bounds S (x := x) (ν := ν) hx1 hvx hν0 hν1
    have hresne : res S x ≠ 0 := by
      intro h
      apply hab.2.2
      exact (nrm_eq_zero_iff (res S x)).mpr h
    let u : Fin n → ℝ := dir S x
    have hu1 : sqNorm u = 1 := by
      dsimp [u]
      exact sqNorm_dir_eq_one S hresne
    have hsup : ∀ i : Fin n, i ∉ S → u i = 0 := by
      intro i hi
      dsimp [u]
      exact dir_supported S x hi
    rcases hG3 u hu1 hsup with ⟨g, hgG, hd1⟩
    -- witness: pred g x
    have hw : ∃ x : Fin n → ℝ, pred g x := ⟨x, ⟨hx, hd1, hvx⟩⟩
    have hgfil : g ∈ G.filter (fun g => ∃ x : Fin n → ℝ, pred g x) :=
      Finset.mem_filter.mpr ⟨hgG, hw⟩
    let y : Fin n → ℝ := Classical.choose hw
    have hyMem : y ∈ NetS := by
      dsimp [NetS]
      exact Finset.mem_image.mpr ⟨⟨g, hgfil⟩, by simp, rfl⟩
    have hypred : pred g y := Classical.choose_spec hw
    have hy1 : sqNorm y = 1 := hypred.1.1.1
    have hdy : nrm (dir S y - g) ≤ η := hypred.2.1
    have hvy : nrm (y - res S y) ≤ ν := hypred.2.2
    have hdiam := bucket_diam S (x₁ := x) (x₂ := y) (p := g) η ν hν0 hν1 hx1 hy1 hvx hvy hd1 hdy
    have hnrm : nrm (y - x) ≤ R := by
      have hxy : nrm (x - y) ≤ R := le_trans hdiam hη_ν
      have hyx : nrm (y - x) = nrm (x - y) := by
        rw [← nrm_neg (y - x)]
        congr 1
        ext i
        simp
      rwa [hyx]
    refine ⟨y, hyMem, ?_⟩
    exact sqNorm_le_sq_of_nrm_le hR0 hnrm
  · -- cardinality
    calc
      NetS.card ≤ ((G.filter (fun g => ∃ x : Fin n → ℝ, pred g x)).attach).card := by
        dsimp [NetS]
        exact Finset.card_image_le
      _ = (G.filter (fun g => ∃ x : Fin n → ℝ, pred g x)).card := Finset.card_attach
      _ ≤ G.card := by
        exact Finset.card_le_card (Finset.filter_subset _ G)


/-! ## Global assembly: slice nets for the compressible set -/

/-- Superset of a coordinate finset of prescribed cardinality. -/
lemma exists_superset_card_eq {α : Type*} [DecidableEq α] [Fintype α] {T : Finset α} {k : ℕ}
    (hTk : T.card ≤ k) (hk : k ≤ Fintype.card α) : ∃ S : Finset α, T ⊆ S ∧ S.card = k := by
  classical
  by_cases hkT : k ≤ T.card
  · -- k ≤ T.card ≤ k: take S := T
    refine ⟨T, Finset.Subset.rfl, ?_⟩
    exact le_antisymm hTk hkT
  · let m : ℕ := k - T.card
    have hsub : T ⊆ (Finset.univ : Finset α) := Finset.subset_univ T
    have hTcomp : T.card + m = k := Nat.add_sub_of_le hTk
    have hm : m ≤ (Finset.univ : Finset α).card - T.card := by
      dsimp [m]
      omega
    -- complement has card univ.card - T.card; use subset card lemma on complement
    rcases Finset.exists_subset_card_eq (s := (Finset.univ : Finset α) \ T)
        (n := m) (by simpa [Finset.card_sdiff, hsub] using hm) with ⟨R, hRsub, hRcard⟩
    let S : Finset α := T ∪ R
    refine ⟨S, ?_, ?_⟩
    · exact Finset.subset_union_left
    · have hdisj : Disjoint T R := by
        rw [Finset.disjoint_left]
        intro x hxT hxR
        exact (Finset.mem_sdiff.mp (hRsub hxR)).2 hxT
      calc
        S.card = T.card + R.card := by
          dsimp [S]
          exact Finset.card_union_of_disjoint hdisj
        _ = k := by rw [hRcard, hTcomp]

/-! ## Volumetric slice-net theorem -/
/-! ## Volumetric slice-net theorem -/

/-- When `⌊δn⌋₊ = 0` the `(δ,ν)`-compressible set is empty (for `ν < 1`). -/
lemma no_slice_of_floor_zero {n : ℕ} {δ ν w : ℝ} {ℓ : ℤ} {x : Fin n → ℝ}
    (hν0 : 0 ≤ ν) (hν1 : ν < 1) (hδn : δ * (n : ℝ) < 1) : ¬ slice δ ν w ℓ x := by
  intro hx
  rcases hx with ⟨hxc, hwlo, hwhi⟩
  rcases hxc with ⟨hx1, hz⟩
  rcases hz with ⟨z, hzsq, hzsupp⟩
  have hcard0 : (Finset.univ.filter (fun i => z i ≠ 0)).card = 0 := by
    have hlt : ((Finset.univ.filter (fun i => z i ≠ 0)).card : ℝ) < 1 :=
      lt_of_le_of_lt hzsupp hδn
    by_contra hne
    have hpos : 0 < (Finset.univ.filter (fun i => z i ≠ 0)).card := Nat.pos_of_ne_zero hne
    have h1r : (1 : ℝ) ≤ ((Finset.univ.filter (fun i => z i ≠ 0)).card : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hpos)
    linarith
  have hz0 : z = 0 := by
    ext i
    have hc0 : supp z = ∅ := by
      exact Finset.card_eq_zero.mp (by simpa [supp] using hcard0)
    have hi : i ∉ supp z := by rw [hc0]; simp
    exact (not_mem_supp z).mp hi
  have hxle : sqNorm x ≤ ν^2 := by simpa [hz0] using hzsq
  have hxeq : sqNorm x = 1 := hx1
  nlinarith [sqNorm_nonneg x]

/-- Per-support cover with an explicit cardinality bound. -/
lemma perS_slice_cover_bound {n : ℕ} {δ ν w : ℝ} {ℓ : ℤ} {S : Finset (Fin n)}
    (η R : ℝ) (hν0 : 0 ≤ ν) (hν1 : ν < 1) (hR0 : 0 ≤ R)
    (hη_ν : 2 * η + 2 * ν + ν^2 ≤ R)
    (G : Finset (Fin n → ℝ))
    (hG1 : ∀ g ∈ G, sqNorm g = 1)
    (hG2 : ∀ g ∈ G, ∀ i : Fin n, i ∉ S → g i = 0)
    (hG3 : ∀ u : Fin n → ℝ, sqNorm u = 1 → (∀ i : Fin n, i ∉ S → u i = 0) →
           ∃ g ∈ G, nrm (u - g) ≤ η)
    (B : ℝ) (hGcard : (G.card : ℝ) ≤ B) :
    ∃ NetS : Finset (Fin n → ℝ),
      (∀ y ∈ NetS, slice δ ν w ℓ y) ∧
      (∀ x : Fin n → ℝ, slice δ ν w ℓ x →
         (∃ z : Fin n → ℝ, sqNorm (x - z) ≤ ν^2 ∧ (∀ i : Fin n, i ∉ S → z i = 0)) →
         ∃ y ∈ NetS, sqNorm (y - x) ≤ R^2) ∧
      ((NetS.card : ℝ) ≤ B) := by
  rcases perS_slice_cover hν0 hν1 hR0 hη_ν G hG1 hG2 hG3 with ⟨NetS, h1, h2, h3⟩
  refine ⟨NetS, h1, h2, ?_⟩
  have h3r : (NetS.card : ℝ) ≤ (G.card : ℝ) := by exact_mod_cast h3
  exact le_trans h3r hGcard

theorem compress_slice_net :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ {δ ν R : ℝ}, 0 < δ → δ ≤ 1 → 0 < ν → ν ≤ R / 4 → 0 < R → R ≤ 1 →
      ∀ (w : ℝ), 0 < w → ∀ (ℓ : ℤ),
        ∃ Net : Finset (Fin n → ℝ),
          (∀ x : Fin n → ℝ, slice δ ν w ℓ x →
              ∃ y ∈ Net, slice δ ν w ℓ y ∧ sqNorm (y - x) ≤ R^2) ∧
          (Net.card : ℝ) ≤ (n.choose ⌊δ * (n : ℝ)⌋₊ : ℝ) * (C₀ / R) ^ ⌊δ * (n : ℝ)⌋₊ := by
  classical
  rcases exists_support_unit_net with ⟨C, hC1, hnets⟩
  let C₀ : ℝ := max 1 (8 * C)
  have hC₀ge1 : 1 ≤ C₀ := by dsimp [C₀]; simp
  have h8C : 8 * C ≤ C₀ := by
    dsimp [C₀]
    exact le_max_right _ _
  refine ⟨C₀, hC₀ge1, ?_⟩
  intro n hn δ ν R hδ0 hδ1 hν0 hνR hR0 hR1 w hw0 ℓ
  let k : ℕ := ⌊δ * (n : ℝ)⌋₊
  let η : ℝ := R / 8
  have hη0 : 0 < η := by dsimp [η]; linarith
  have hη1 : η ≤ 1 := by dsimp [η]; nlinarith
  have hδn0 : 0 ≤ δ * (n : ℝ) := by positivity
  have hkδ : (k : ℝ) ≤ δ * (n : ℝ) := by
    dsimp [k]
    exact Nat.floor_le hδn0
  have hδn_le : δ * (n : ℝ) ≤ (n : ℝ) := by nlinarith
  have hkn : k ≤ n := by
    have hkr : (k : ℝ) ≤ (n : ℝ) := le_trans hkδ hδn_le
    exact_mod_cast hkr
  have hνlt1 : ν < 1 := by nlinarith
  by_cases hk0 : k = 0
  · -- empty slice
    have hδn1 : δ * (n : ℝ) < 1 := by
      have h1 : δ * (n : ℝ) < (⌊δ * (n : ℝ)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (δ * (n : ℝ))
      have hk0r : (⌊δ * (n : ℝ)⌋₊ : ℝ) = 0 := by
        dsimp [k] at hk0
        exact_mod_cast hk0
      nlinarith
    refine ⟨∅, ?_, ?_⟩
    · intro x hx
      exfalso
      exact no_slice_of_floor_zero (le_of_lt hν0) hνlt1 hδn1 hx
    · -- cardinality of the empty net
      have hfloor : ⌊δ * (n : ℝ)⌋₊ = 0 := by
        dsimp [k] at hk0
        exact hk0
      rw [hfloor]
      simp
  · -- k ≥ 1 : build the union of per-support nets
    have hkpos : 0 < k := by
      by_contra h
      exact hk0 (Nat.eq_zero_of_not_pos h)
    let All : Finset (Finset (Fin n)) := (Finset.univ : Finset (Fin n)).powersetCard k
    have hAllcard : All.card = n.choose k := by
      dsimp [All]
      simp
    have hη_ν : 2 * η + 2 * ν + ν^2 ≤ R := by
      dsimp [η]
      nlinarith
    have hcoverS : ∀ S : Finset (Fin n), S.card = k →
        ∃ NetS : Finset (Fin n → ℝ),
          (∀ y ∈ NetS, slice δ ν w ℓ y) ∧
          (∀ x : Fin n → ℝ, slice δ ν w ℓ x →
             (∃ z : Fin n → ℝ, sqNorm (x - z) ≤ ν^2 ∧ (∀ i : Fin n, i ∉ S → z i = 0)) →
             ∃ y ∈ NetS, sqNorm (y - x) ≤ R^2) ∧
          ((NetS.card : ℝ) ≤ (8 * C / R)^k) := by
        intro S hSk
        rcases hnets n S η hη0 hη1 with ⟨G, hG1hG2, hG3, hGcard0⟩
        have hG1 : ∀ g ∈ G, sqNorm g = 1 := fun g hg => (hG1hG2 g hg).1
        have hG2 : ∀ g ∈ G, ∀ i : Fin n, i ∉ S → g i = 0 := fun g hg i hi => (hG1hG2 g hg).2 i hi
        have hGcardk : (G.card : ℝ) ≤ (C / η)^k := by
          simpa [hSk, η] using hGcard0
        have hbase : C / η = 8 * C / R := by
          dsimp [η]
          field_simp [show R ≠ 0 by linarith]
        have hGcard8 : (G.card : ℝ) ≤ (8 * C / R)^k := by
          simpa [hbase] using hGcardk
        exact perS_slice_cover_bound η R (le_of_lt hν0) hνlt1 (le_of_lt hR0) hη_ν
          G hG1 hG2 hG3 ((8 * C / R)^k) hGcard8
    let NS : (Finset (Fin n)) → Finset (Fin n → ℝ) := fun S =>
      if hS : S.card = k then Classical.choose (hcoverS S hS) else ∅
    let Net : Finset (Fin n → ℝ) := All.biUnion NS
    refine ⟨Net, ?_, ?_⟩
    · -- covering
      intro x hx
      have hx1 : sqNorm x = 1 := hx.1.1
      rcases hx.1.2 with ⟨z, hzsq, hzsupp⟩
      have hsuppk : (supp z).card ≤ k := by
        apply Nat.le_floor
        simpa [supp] using hzsupp
      have hkn' : k ≤ Fintype.card (Fin n) := by simpa using hkn
      rcases exists_superset_card_eq (T := supp z) (k := k) hsuppk hkn' with ⟨S, hTS, hSk⟩
      have hS_mem : S ∈ All := by
        dsimp [All]
        exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, hSk⟩
      have hzS : ∀ i : Fin n, i ∉ S → z i = 0 := by
        intro i hi
        have : i ∉ supp z := fun hiT => hi (hTS hiT)
        exact (not_mem_supp z).mp this
      have hpropS := Classical.choose_spec (hcoverS S hSk)
      rcases hpropS with ⟨hSslice, hScover, hScard⟩
      rcases hScover x hx ⟨z, hzsq, hzS⟩ with ⟨y, hyNS, hybound⟩
      refine ⟨y, ?_, ?_⟩
      · dsimp [Net]
        have hNS : NS S = Classical.choose (hcoverS S hSk) := by
          dsimp [NS]
          rw [dif_pos hSk]
        exact Finset.mem_biUnion.mpr ⟨S, hS_mem, by simpa [hNS] using hyNS⟩
      · have hNS : NS S = Classical.choose (hcoverS S hSk) := by
          dsimp [NS]
          rw [dif_pos hSk]
        exact ⟨hSslice y (by simpa [hNS] using hyNS), hybound⟩
    · -- cardinality
      dsimp [Net]
      calc
        ((All.biUnion NS).card : ℝ)
            ≤ ∑ S ∈ All, ((NS S).card : ℝ) := by
              have h0 := Finset.card_biUnion_le (s := All) (t := NS)
              -- cast the natural inequality
              have h1 : ((All.biUnion NS).card : ℝ) ≤ ((∑ S ∈ All, (NS S).card) : ℝ) := by exact_mod_cast h0
              simpa [Finset.sum_apply, Finset.sum_attach] using h1
        _ ≤ ∑ S ∈ All, (8 * C / R)^k := by
              apply Finset.sum_le_sum
              intro S hS
              have hSk : S.card = k := (Finset.mem_powersetCard.mp hS).2
              have hNS : NS S = Classical.choose (hcoverS S hSk) := by
                dsimp [NS]
                rw [dif_pos hSk]
              have hc : (NS S).card ≤ (8 * C / R)^k := by
                rw [hNS]
                exact (Classical.choose_spec (hcoverS S hSk)).2.2
              exact_mod_cast hc
        _ = (All.card : ℝ) * (8 * C / R)^k := by
              rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((n.choose k : ℝ)) * (8 * C / R)^k := by
              rw [hAllcard]
        _ ≤ (n.choose k : ℝ) * (C₀ / R)^k := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              apply pow_le_pow_left₀
              · positivity
              · exact div_le_div_of_nonneg_right h8C (le_of_lt hR0)
        _ = (n.choose ⌊δ * (n : ℝ)⌋₊ : ℝ) * (C₀ / R) ^ ⌊δ * (n : ℝ)⌋₊ := by
              dsimp [k]
end Commons.LinearAlgebra.Net