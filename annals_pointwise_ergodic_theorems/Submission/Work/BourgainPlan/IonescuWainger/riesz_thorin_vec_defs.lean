import Mathlib
import Submission.Commons.Analysis.Complex.hadamard_three_lines
import Submission.Commons.Analysis.Integral.holder_complex_finset

/-!
# Vector-valued Riesz--Thorin: definitions

Foundational definitions for the vector-valued (finite-dimensional Hilbert-space valued)
Riesz--Thorin theorem `Work.BourgainPlan.IonescuWainger.riesz_thorin_vector_valued`.

The target space is written as functions `β → ι → ℂ` with the *mixed* norm
`‖u‖_{ℓ^p(β;ℓ²(ι))} = (∑ b, (∑ i, ‖u b i‖ ^ 2) ^ (p/2)) ^ (1/p)`.

We collect here
* `n2sq`, `n2` : the squared/normal `ℓ²`-norm of a finite vector `ι → ℂ`;
* `mLp`, `mLinf` : the mixed `ℓ^p` / `ℓ^∞` norms of `u : β → ι → ℂ`;
* `interpE` : the interpolation vector for a function with values in a complex normed space
  (used for the *source* function `α → ℂ`);
* `vinterp` : the interpolation vector for `u : β → ι → ℂ`, scaling each fibre by its `ℓ²`-norm.
-/

open scoped BigOperators

namespace Work.BourgainPlan.IonescuWainger

noncomputable section

/-- Squared `ℓ²`-norm of a finite vector. -/
def n2sq {ι : Type*} [Fintype ι] (v : ι → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

/-- `ℓ²`-norm of a finite vector. -/
def n2 {ι : Type*} [Fintype ι] (v : ι → ℂ) : ℝ := Real.sqrt (n2sq v)

/-- Mixed `ℓ^p(β; ℓ²(ι))` norm. -/
def mLp {β ι : Type*} [Fintype β] [Fintype ι] (u : β → ι → ℂ) (p : ℝ) : ℝ :=
  (∑ b, (n2 (u b)) ^ p) ^ (1 / p)

/-- Mixed `ℓ^∞(β; ℓ²(ι))` norm. -/
def mLinf {β ι : Type*} [Fintype β] [Fintype ι] (u : β → ι → ℂ) : ℝ := ⨆ b, n2 (u b)

lemma n2sq_nonneg {ι : Type*} [Fintype ι] (v : ι → ℂ) : 0 ≤ n2sq v :=
  Finset.sum_nonneg fun i _ => sq_nonneg _

lemma n2_nonneg {ι : Type*} [Fintype ι] (v : ι → ℂ) : 0 ≤ n2 v := Real.sqrt_nonneg _

@[simp] lemma n2sq_zero {ι : Type*} [Fintype ι] : n2sq (0 : ι → ℂ) = 0 := by
  simp [n2sq]

@[simp] lemma n2_zero {ι : Type*} [Fintype ι] : n2 (0 : ι → ℂ) = 0 := by
  simp [n2]

lemma sq_n2 {ι : Type*} [Fintype ι] (v : ι → ℂ) : n2 v ^ 2 = n2sq v := Real.sq_sqrt (n2sq_nonneg v)

lemma n2_eq_rpow {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    n2 v = (∑ i, ‖v i‖ ^ 2) ^ ((1 : ℝ) / 2) := by
  rw [n2, n2sq, Real.sqrt_eq_rpow]

lemma n2sq_eq_zero_iff {ι : Type*} [Fintype ι] (v : ι → ℂ) : n2sq v = 0 ↔ v = 0 := by
  rw [n2sq, Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)]
  constructor
  · intro h
    funext i
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp (h i (Finset.mem_univ i)))
  · rintro rfl i _
    simp

lemma n2_eq_zero_iff {ι : Type*} [Fintype ι] (v : ι → ℂ) : n2 v = 0 ↔ v = 0 := by
  rw [← sq_eq_zero_iff (a := n2 v), sq_n2, n2sq_eq_zero_iff]

lemma n2sq_smul {ι : Type*} [Fintype ι] (c : ℂ) (v : ι → ℂ) :
    n2sq (c • v) = ‖c‖ ^ 2 * n2sq v := by
  rw [n2sq, n2sq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, norm_smul, mul_pow]

lemma n2_smul {ι : Type*} [Fintype ι] (c : ℂ) (v : ι → ℂ) : n2 (c • v) = ‖c‖ * n2 v := by
  rw [n2, n2sq_smul, n2, Real.sqrt_mul (sq_nonneg ‖c‖), Real.sqrt_sq (norm_nonneg c)]

lemma n2_smul_real {ι : Type*} [Fintype ι] (c : ℝ) (hc : 0 ≤ c) (v : ι → ℂ) :
    n2 ((c : ℂ) • v) = c * n2 v := by
  rw [n2_smul, Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self hc]

lemma mLp_nonneg {β ι : Type*} [Fintype β] [Fintype ι] (u : β → ι → ℂ) (p : ℝ) :
    0 ≤ mLp u p :=
  Real.rpow_nonneg (Finset.sum_nonneg fun b _ => Real.rpow_nonneg (n2_nonneg (u b)) p) _

lemma mLp_eq_goal {β ι : Type*} [Fintype β] [Fintype ι] (u : β → ι → ℂ) (p : ℝ) :
    mLp u p = (∑ b, (∑ i, ‖u b i‖ ^ 2) ^ (p / 2)) ^ (1 / p) := by
  rw [mLp]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [n2_eq_rpow, ← Real.rpow_mul (Finset.sum_nonneg fun i _ => sq_nonneg (‖u b i‖)),
    show ((1:ℝ)/2) * p = p / 2 by ring]


/-- The affine map `z ↦ A + B z`. -/
def affine (A B : ℝ) (z : ℂ) : ℂ := (A : ℂ) + (B : ℂ) * z

lemma affine_re (A B : ℝ) (z : ℂ) : (affine A B z).re = A + B * z.re := by
  simp [affine, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

lemma differentiable_affine (A B : ℝ) : Differentiable ℂ (affine A B) := by
  unfold affine; fun_prop

/-- The interpolation vector of a scalar function: `φ ↦ ‖φ a‖ ^ (t z) · ‖φ a‖⁻¹ · φ a`. -/
def interpC {σ : Type*} (f : σ → ℂ) (t : ℂ → ℂ) (z : ℂ) : σ → ℂ :=
  fun a => (((‖f a‖ : ℝ) : ℂ) ^ (t z)) * ((((‖f a‖ : ℝ) : ℂ)⁻¹) * f a)

lemma interpC_apply {σ : Type*} (f : σ → ℂ) (t : ℂ → ℂ) (z : ℂ) (a : σ) :
    interpC f t z a = (((‖f a‖ : ℝ) : ℂ) ^ (t z)) * ((((‖f a‖ : ℝ) : ℂ)⁻¹) * f a) := rfl

/-- The interpolation vector of a vector-valued function `g : β → ι → ℂ`: each fibre is scaled
by the power of its `ℓ²`-norm. -/
def vinterp {β ι : Type*} [Fintype ι] (g : β → ι → ℂ) (s : ℂ → ℂ) (z : ℂ) : β → ι → ℂ :=
  fun b i => (((n2 (g b) : ℝ) : ℂ) ^ (s z)) * ((((n2 (g b) : ℝ) : ℂ)⁻¹) * g b i)

lemma vinterp_apply {β ι : Type*} [Fintype ι] (g : β → ι → ℂ) (s : ℂ → ℂ) (z : ℂ) (b : β)
    (i : ι) :
    vinterp g s z b i = (((n2 (g b) : ℝ) : ℂ) ^ (s z)) * ((((n2 (g b) : ℝ) : ℂ)⁻¹) * g b i) :=
  rfl

lemma mLp_smul {β ι : Type*} [Fintype β] [Fintype ι] (c : ℂ) (u : β → ι → ℂ) {p : ℝ}
    (hp : 0 < p) : mLp (c • u) p = ‖c‖ * mLp u p := by
  have hterm : ∀ b, (n2 ((c • u) b)) ^ p = ‖c‖ ^ p * (n2 (u b)) ^ p := by
    intro b
    have h : (c • u) b = c • (u b) := rfl
    rw [h, n2_smul, Real.mul_rpow (norm_nonneg c) (n2_nonneg (u b))]
  rw [mLp, mLp, Finset.sum_congr rfl (fun b _ => hterm b), ← Finset.mul_sum]
  rw [Real.mul_rpow (Real.rpow_nonneg (norm_nonneg c) p)
    (Finset.sum_nonneg fun b _ => Real.rpow_nonneg (n2_nonneg (u b)) p)]
  rw [← Real.rpow_mul (norm_nonneg c) p (1/p)]
  rw [mul_one_div, div_self (ne_of_gt hp), Real.rpow_one]

end

end Work.BourgainPlan.IonescuWainger
