import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Analysis.Fourier.zpow_summable_gauss_matrix
import Submission.Commons.Analysis.Fourier.mFourierLift_eq_exp
import Submission.Commons.Analysis.Fourier.sum_sq_le_const_sum_sq_mulVec
import Submission.Commons.Analysis.Fourier.torus_descent_continuous
import Submission.Commons.Analysis.Fourier.gaussian_integrable_fn

noncomputable section
open scoped BigOperators Topology ENNReal
open MeasureTheory Filter Complex
open Matrix

set_option autoImplicit false

namespace Commons.Analysis.Fourier

/-! ## Coordinate-norm vocabulary

We work over the function space `ι → ℝ` for a finite type `ι`.  For a real square matrix
`C : Matrix ι ι ℝ` we write

* `sqNorm C x = ∑ i, ((C *ᵥ x) i) ^ 2` — squared Euclidean norm of `C·x`;
* `dot x y  = ∑ i, x i * y i` — coordinate dot product. -/

variable {ι : Type*}

/-- Squared Euclidean coordinate norm of `C·x`. -/
def sqNormMat [Fintype ι] (C : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ := ∑ i : ι, ((C *ᵥ x) i) ^ 2

/-- Squared Euclidean coordinate norm of `x`. -/
def sqNormId [Fintype ι] (x : ι → ℝ) : ℝ := ∑ i : ι, (x i) ^ 2

/-- Coordinate dot product. -/
def coordDot [Fintype ι] (x y : ι → ℝ) : ℝ := ∑ i : ι, x i * y i

/-- The `ℤ`-lattice vector `k : ι → ℤ` as a real vector. -/
def intToReal (k : ι → ℤ) : ι → ℝ := fun i => (k i : ℝ)

/-- The Gaussian `x ↦ exp (-π·‖C·x‖²)` as a complex-valued function. -/
def cgauss [Fintype ι] (C : Matrix ι ι ℝ) (x : ι → ℝ) : ℂ :=
  cexp (-(Real.pi : ℂ) * (sqNormMat C x : ℂ))

/-- The Gaussian `x ↦ exp (-π·‖C·x‖²)` as a real-valued function. -/
def rgauss [Fintype ι] (C : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  Real.exp (-Real.pi * sqNormMat C x)

/-- `mFourier (-m)` applied to the lift of `x : ι → ℝ` to the torus, as a
complex-valued function of `x`. -/
def mFourierLift {d : Type*} [Fintype d] (m : d → ℤ) (x : d → ℝ) : ℂ :=
  UnitAddTorus.mFourier (-m) (fun i : d => (x i : UnitAddCircle))

/-- The fundamental domain `(0, 1]ᵈ` in `d → ℝ`. -/
def box01 (d : Type*) : Set (d → ℝ) :=
  {x : d → ℝ | ∀ i : d, x i ∈ Set.Ioc (0 : ℝ) 1}

/-- The map from `d → ℝ` to the torus. -/
def torusMk (d : Type*) (x : d → ℝ) : UnitAddTorus d := fun i => (x i : UnitAddCircle)

/-- The periodicized Gaussian `x ↦ Σ'_{k : ι → ℤ} exp(-π·‖C·(x + k)‖²)`. -/
def pgauss [Fintype ι] (C : Matrix ι ι ℝ) (x : ι → ℝ) : ℂ :=
  ∑' k : ι → ℤ, cgauss C (x + intToReal k)

section MatrixNormLemmas

/-! ### Matrix identities relating `sqNormMat`, `sqNormId`, `coordDot` -/

variable {ι : Type*} [Fintype ι]

/-- `coordDot` is the dot product. -/
lemma coordDot_eq_dotProduct (x y : ι → ℝ) : coordDot x y = x ⬝ᵥ y := rfl

/-- Dot product with a matrix-transformed vector moves to the transpose. -/
lemma coordDot_mulVec (C : Matrix ι ι ℝ) (x y : ι → ℝ) :
    coordDot (C *ᵥ x) y = coordDot x (Cᵀ *ᵥ y) := by
  rw [coordDot_eq_dotProduct, coordDot_eq_dotProduct]
  calc
    (C *ᵥ x) ⬝ᵥ y = y ⬝ᵥ (C *ᵥ x) := dotProduct_comm _ _
    _ = (y ᵥ* C) ⬝ᵥ x := Matrix.dotProduct_mulVec (R := ℝ) y C x
    _ = x ⬝ᵥ (y ᵥ* C) := dotProduct_comm _ _
    _ = x ⬝ᵥ (Cᵀ *ᵥ y) := by rw [Matrix.mulVec_transpose]

/-- `sqNormId x = coordDot x x`. -/
lemma sqNormId_eq_coordDot (x : ι → ℝ) : sqNormId x = coordDot x x := by
  unfold sqNormId coordDot
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- `sqNormMat C x = coordDot (C *ᵥ x) (C *ᵥ x)`. -/
lemma sqNormMat_eq_coordDot (C : Matrix ι ι ℝ) (x : ι → ℝ) :
    sqNormMat C x = coordDot (C *ᵥ x) (C *ᵥ x) := by
  unfold sqNormMat coordDot
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- `sqNormMat` of a product: `sqNormMat (A * B) x = sqNormMat A (B *ᵥ x)`. -/
lemma sqNormMat_mul (A B : Matrix ι ι ℝ) (x : ι → ℝ) :
    sqNormMat (A * B) x = sqNormMat A (B *ᵥ x) := by
  unfold sqNormMat
  apply Finset.sum_congr rfl
  intro i hi
  rw [Matrix.mulVec_mulVec]

/-- For invertible `C`, `C⁻¹ *ᵥ (C *ᵥ x) = x`. -/
lemma inv_mulVec_mulVec [DecidableEq ι] (C : Matrix ι ι ℝ) (hC : C.det ≠ 0) (x : ι → ℝ) :
    C⁻¹ *ᵥ (C *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec]
  rw [Matrix.nonsing_inv_mul C (isUnit_iff_ne_zero.mpr hC)]
  simp

/-- For invertible `C`, `C *ᵥ (C⁻¹ *ᵥ x) = x`. -/
lemma mulVec_inv_mulVec [DecidableEq ι] (C : Matrix ι ι ℝ) (hC : C.det ≠ 0) (x : ι → ℝ) :
    C *ᵥ (C⁻¹ *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec]
  rw [Matrix.mul_nonsing_inv C (isUnit_iff_ne_zero.mpr hC)]
  simp

/-- `Cᵀ * (C⁻¹)ᵀ = 1` for invertible `C`. -/
lemma transpose_mul_transpose_inv [DecidableEq ι] (C : Matrix ι ι ℝ) (hC : C.det ≠ 0) :
    Cᵀ * (C⁻¹)ᵀ = 1 := by
  simpa [Matrix.transpose_nonsing_inv] using
    (Matrix.mul_nonsing_inv (Cᵀ) (isUnit_iff_ne_zero.mpr (by rwa [Matrix.det_transpose])))

/-- `coordDot (C *ᵥ x) ((C⁻¹)ᵀ *ᵥ y) = coordDot x y` for invertible `C`. -/
lemma coordDot_mulVec_invTranspose [DecidableEq ι] (C : Matrix ι ι ℝ) (hC : C.det ≠ 0)
    (x y : ι → ℝ) : coordDot (C *ᵥ x) ((C⁻¹)ᵀ *ᵥ y) = coordDot x y := by
  rw [coordDot_mulVec]
  congr 1
  rw [Matrix.mulVec_mulVec]
  rw [transpose_mul_transpose_inv C hC]
  simp

/-- Pointwise `(B *ᵥ w) i` as an explicit sum. -/
lemma mulVec_apply_sum (B : Matrix ι ι ℝ) (w : ι → ℝ) (i : ι) :
    (B *ᵥ w) i = ∑ j : ι, B i j * w j := by
  rw [Matrix.mulVec_apply]
  change (B.row i ⬝ᵥ w) = ∑ j : ι, B i j * w j
  simp [Matrix.row_apply, dotProduct]

/-- A sum of squares is nonnegative. -/
lemma sum_sq_nonneg (f : ι → ℝ) : 0 ≤ ∑ i : ι, (f i) ^ 2 := by
  exact Finset.sum_nonneg (fun i hi => sq_nonneg (f i))

/-- `sqNormMat C x ≥ 0`. -/
lemma sqNormMat_nonneg (C : Matrix ι ι ℝ) (x : ι → ℝ) : 0 ≤ sqNormMat C x := by
  dsimp [sqNormMat]
  exact sum_sq_nonneg (fun i => ((C *ᵥ x) i))

/-- For invertible `C`, `sqNormId` is bounded by a constant times `sqNormMat C`. -/
lemma sqNormId_le_const_sqNormMat [DecidableEq ι] (C : Matrix ι ι ℝ) (hC : C.det ≠ 0) :
    ∃ a : ℝ, 0 < a ∧ ∀ x : ι → ℝ, sqNormId x ≤ a * sqNormMat C x := by
  let B : Matrix ι ι ℝ := C⁻¹
  let S : ℝ := ∑ i : ι, ∑ j : ι, (B i j) ^ 2
  refine ⟨1 + S, ?pos, ?ineq⟩
  · have hS : 0 ≤ S := by
      dsimp [S]
      exact Finset.sum_nonneg (fun i hi => sum_sq_nonneg (fun j => (B i j)))
    linarith
  · intro x
    let w : ι → ℝ := C *ᵥ x
    have hcoord : ∀ i : ι, (x i) ^ 2 ≤ (∑ j : ι, (B i j) ^ 2) * sqNormMat C x := by
      intro i
      have hxw : x = B *ᵥ w := by
        dsimp [B, w]
        exact (inv_mulVec_mulVec C hC x).symm
      calc
        (x i) ^ 2 = ((B *ᵥ w) i) ^ 2 := by rw [hxw]
        _ = (∑ j : ι, B i j * w j) ^ 2 := by rw [mulVec_apply_sum]
        _ ≤ (∑ j : ι, (B i j) ^ 2) * (∑ j : ι, (w j) ^ 2) := by
          exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j : ι => B i j) w
        _ = (∑ j : ι, (B i j) ^ 2) * sqNormMat C x := by
          dsimp [w, sqNormMat]
    calc
      sqNormId x = ∑ i : ι, (x i) ^ 2 := rfl
      _ ≤ ∑ i : ι, ((∑ j : ι, (B i j) ^ 2) * sqNormMat C x) := by
        exact Finset.sum_le_sum (fun i hi => hcoord i)
      _ = (∑ i : ι, ∑ j : ι, (B i j) ^ 2) * sqNormMat C x := by
        rw [Finset.sum_mul]
      _ = S * sqNormMat C x := by rfl
      _ ≤ (1 + S) * sqNormMat C x := by
        nlinarith [sqNormMat_nonneg C x]

/-- `sqNormId` of an integer vector is `∑ (kᵢ:ℝ)²`. -/
lemma sqNormId_intToReal (k : ι → ℤ) : sqNormId (intToReal k) = ∑ i : ι, ((k i : ℤ) : ℝ) ^ 2 := by
  rfl

end MatrixNormLemmas

section GaussianBasics

variable {ι : Type*} [Fintype ι]

/-- The complex Gaussian is the coercion of the real one. -/
lemma cgauss_eq_ofReal_rgauss (C : Matrix ι ι ℝ) (x : ι → ℝ) :
    cgauss C x = (rgauss C x : ℂ) := by
  unfold cgauss rgauss
  rw [show (-(Real.pi : ℂ) * (sqNormMat C x : ℂ)) = (( -Real.pi * sqNormMat C x : ℝ) : ℂ) by
    push_cast; ring]
  rw [← Complex.ofReal_exp]

/-- Complex norm of the Gaussian. -/
lemma norm_cgauss (C : Matrix ι ι ℝ) (x : ι → ℝ) :
    ‖cgauss C x‖ = Real.exp (-Real.pi * sqNormMat C x) := by
  unfold cgauss
  rw [Complex.norm_exp]
  congr 1
  rw [show (-(Real.pi : ℂ) * (sqNormMat C x : ℂ)) = (( -Real.pi * sqNormMat C x : ℝ) : ℂ) by
    push_cast; ring]
  simp

/-- `‖cgauss C x‖` is a real-valued bound via monotonicity of `exp`. -/
lemma norm_cgauss_le (C : Matrix ι ι ℝ) (x : ι → ℝ) {a : ℝ} (ha : a ≤ sqNormMat C x) :
    ‖cgauss C x‖ ≤ Real.exp (-Real.pi * a) := by
  rw [norm_cgauss]
  rw [Real.exp_le_exp]
  have hπ : 0 < Real.pi := Real.pi_pos
  nlinarith

/-- Real exponential is nonnegative. -/
lemma rgauss_nonneg (C : Matrix ι ι ℝ) (x : ι → ℝ) : 0 ≤ rgauss C x := by
  unfold rgauss
  exact (Real.exp_pos _).le

/-- `exp (-π * a) ≤ 1` for `a ≥ 0`. -/
lemma exp_neg_pi_mul_nonpos_le_one (a : ℝ) : 0 ≤ a → Real.exp (-Real.pi * a) ≤ 1 := by
  intro ha
  rw [Real.exp_le_one_iff]
  nlinarith [Real.pi_pos]

end GaussianBasics

section PeriodicGaussian

variable {ι : Type*} [Fintype ι]

/-- Pointwise: `(x + intToReal z) + intToReal k = x + intToReal (z + k)`. -/
lemma add_intToReal_assoc (x : ι → ℝ) (z k : ι → ℤ) :
    (x + intToReal z) + intToReal k = x + intToReal (z + k) := by
  funext i
  simp [intToReal, Pi.add_apply]
  ring

/-- The periodicized Gaussian is `ℤ`-periodic in every coordinate (i.e. constant on the
fibers of the torus quotient map). -/
lemma pgauss_periodic (C : Matrix ι ι ℝ) (x : ι → ℝ) (z : ι → ℤ) :
    pgauss C (x + intToReal z) = pgauss C x := by
  let f : (ι → ℤ) → ℂ := fun j => cgauss C (x + intToReal j)
  have hrew : (∑' k : ι → ℤ, cgauss C (x + intToReal z + intToReal k)) =
      (∑' k : ι → ℤ, cgauss C (x + intToReal (z + k))) := by
    apply tsum_congr
    intro k
    congr 1
    exact add_intToReal_assoc x z k
  calc
    pgauss C (x + intToReal z) = ∑' k : ι → ℤ, cgauss C (x + intToReal z + intToReal k) := by
      rfl
    _ = ∑' k : ι → ℤ, cgauss C (x + intToReal (z + k)) := hrew
    _ = ∑' j : ι → ℤ, f j := by
      let e : (ι → ℤ) ≃ (ι → ℤ) :=
        { toFun := fun k => z + k, invFun := fun k => -z + k
          left_inv := by intro k; funext i; simp, right_inv := by intro k; funext i; simp }
      exact Equiv.tsum_eq e f
    _ = pgauss C x := by rfl

/-- Value of the periodicized Gaussian at the origin. -/
lemma pgauss_zero (C : Matrix ι ι ℝ) :
    pgauss C 0 = ∑' k : ι → ℤ, cgauss C (intToReal k) := by
  unfold pgauss
  apply tsum_congr
  intro k
  simp

/-- `mFourier` monomials are `1` at the origin of the torus. -/
lemma mFourier_zero_torus (d : Type*) [Fintype d] (m : d → ℤ) :
    UnitAddTorus.mFourier m (0 : UnitAddTorus d) = 1 := by
  simp [UnitAddTorus.mFourier]

end PeriodicGaussian

section Continuity

/-! ### Continuity of the periodicized Gaussian -/

/-- per-coordinate `(k + y)² ≥ k²/2 - y²`. -/
lemma sq_add_ge_half (y k : ℝ) : (y + k) ^ 2 ≥ k ^ 2 / 2 - y ^ 2 := by
  nlinarith [sq_nonneg (k + 2 * y)]

/-- Summable Gaussian over `ℤⁿ` with decay in the plain coordinate norm. -/
lemma summable_exp_neg_sqNormId_int (n : ℕ) {c : ℝ} (hc : 0 < c) :
    Summable (fun k : Fin n → ℤ => Real.exp (-c * (∑ i : Fin n, ((k i : ℝ) ^ 2)))) := by
  have h := Commons.Analysis.Fourier.zpow_summable_gauss_matrix n
    (1 : Matrix (Fin n) (Fin n) ℝ) (by simp) c hc
  simpa using h

/-- For `|x - x₀| < 1/2`, we have `|x| ≤ |x₀| + 1/2`. -/
lemma abs_coord_le (x₀ x : ℝ) (hx : |x - x₀| < 1 / 2) : |x| ≤ |x₀| + 1 / 2 := by
  have htri : |x| ≤ |x - x₀| + |x₀| := by
    calc
      |x| = |(x - x₀) + x₀| := by congr 1; ring
      _ ≤ |x - x₀| + |x₀| := abs_add_le _ _
  have hle : |x - x₀| ≤ 1 / 2 := le_of_lt hx
  linarith

/-- coordinate-wise lower bound for `(y + k)²`. -/
lemma coord_sq_lower (y k b : ℝ) (hb : 0 ≤ b) (hy : |y| ≤ b) :
    (y + k) ^ 2 ≥ k ^ 2 / 2 - b ^ 2 := by
  have h1 := sq_add_ge_half y k
  have hsq : y ^ 2 ≤ b ^ 2 := by
    have hyb : |y| ≤ |b| := by rwa [← abs_of_nonneg hb] at hy
    exact sq_le_sq.mpr hyb
  nlinarith

/-- `‖cgauss C v‖ ≤ exp (-(π/a)·‖v‖²)` under the invertibility bound. -/
lemma exp_neg_sqMat_le (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.det ≠ 0) (a : ℝ)
    (ha0 : 0 < a) (hab : ∀ v : Fin n → ℝ, sqNormId v ≤ a * sqNormMat C v)
    (v : Fin n → ℝ) :
    ‖cgauss C v‖ ≤ Real.exp (-(Real.pi / a) * sqNormId v) := by
  rw [norm_cgauss]
  rw [Real.exp_le_exp]
  have hb := hab v
  have hπa : 0 < Real.pi / a := by positivity
  have hmul : (Real.pi / a) * sqNormId v ≤ (Real.pi / a) * (a * sqNormMat C v) :=
    mul_le_mul_of_nonneg_left hb (le_of_lt hπa)
  have hmul' : (Real.pi / a) * (a * sqNormMat C v) = Real.pi * sqNormMat C v := by
    field_simp [ne_of_gt ha0]
  rw [hmul'] at hmul
  linarith

/-- Pointwise domination bound for `cgauss C (x + k)` on the open box of radius 1/2
around `x₀`. -/
lemma cgauss_bound (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.det ≠ 0) (x₀ : Fin n → ℝ)
    {a : ℝ} (ha0 : 0 < a) (hab : ∀ v : Fin n → ℝ, sqNormId v ≤ a * sqNormMat C v) :
    ∃ u : (Fin n → ℤ) → ℝ,
      (Summable u) ∧
      ∀ x : Fin n → ℝ, (∀ i : Fin n, |x i - x₀ i| < 1 / 2) → ∀ k : Fin n → ℤ,
        ‖cgauss C (x + intToReal k)‖ ≤ u k := by
  let B : ℝ := ∑ i : Fin n, (|x₀ i| + 1 / 2) ^ 2
  let u : (Fin n → ℤ) → ℝ := fun k => Real.exp ((Real.pi / a) * B) *
    Real.exp (-(Real.pi / (2 * a)) * (∑ i : Fin n, ((k i : ℝ) ^ 2)))
  refine ⟨u, ?summable, ?bnd⟩
  · have hc : 0 < Real.pi / (2 * a) := by positivity
    have hs : Summable (fun k : Fin n → ℤ =>
        Real.exp (-(Real.pi / (2 * a)) * (∑ i : Fin n, ((k i : ℝ) ^ 2)))) :=
      summable_exp_neg_sqNormId_int n hc
    dsimp [u]
    exact hs.mul_left (Real.exp ((Real.pi / a) * B))
  · intro x hxO k
    have hxi : ∀ i : Fin n, |x i| ≤ |x₀ i| + 1 / 2 := by
      intro i
      exact abs_coord_le (x₀ i) (x i) (hxO i)
    have hbi : ∀ i : Fin n, 0 ≤ |x₀ i| + 1 / 2 := by
      intro i
      positivity
    have hcoord : ∀ i : Fin n, (x i + (k i : ℝ)) ^ 2 ≥ ((k i : ℝ) ^ 2) / 2 - (|x₀ i| + 1 / 2) ^ 2 := by
      intro i
      exact coord_sq_lower (x i) (k i : ℝ) (|x₀ i| + 1 / 2) (hbi i) (hxi i)
    have hsqId : (∑ i : Fin n, ((x i + (k i : ℝ)) ^ 2)) ≥
        (∑ i : Fin n, ((k i : ℝ) ^ 2)) / 2 - B := by
      dsimp [B]
      calc
        (∑ i : Fin n, (x i + (k i : ℝ)) ^ 2) ≥
            ∑ i : Fin n, (((k i : ℝ) ^ 2) / 2 - (|x₀ i| + 1 / 2) ^ 2) := by
          exact Finset.sum_le_sum (fun i hi => hcoord i)
        _ = (∑ i : Fin n, ((k i : ℝ) ^ 2)) / 2 - ∑ i : Fin n, (|x₀ i| + 1 / 2) ^ 2 := by
          rw [Finset.sum_sub_distrib]
          rw [Finset.sum_div]
        _ = (∑ i : Fin n, ((k i : ℝ) ^ 2)) / 2 - B := by rfl
    let S : ℝ := ∑ i : Fin n, ((k i : ℝ) ^ 2)
    have hT : sqNormId (x + intToReal k) = ∑ i : Fin n, ((x i + (k i : ℝ)) ^ 2) := by
      dsimp [sqNormId, intToReal]
    calc
      ‖cgauss C (x + intToReal k)‖ ≤ Real.exp (-(Real.pi / a) * sqNormId (x + intToReal k)) := by
        exact exp_neg_sqMat_le n C hC a ha0 hab (x + intToReal k)
      _ ≤ Real.exp (-(Real.pi / a) * (S / 2 - B)) := by
        rw [Real.exp_le_exp]
        have hmain : S / 2 - B ≤ sqNormId (x + intToReal k) := by
          rw [hT]
          nlinarith
        have hpos : 0 ≤ Real.pi / a := by positivity
        have hm : (Real.pi / a) * (S / 2 - B) ≤ (Real.pi / a) * sqNormId (x + intToReal k) :=
          mul_le_mul_of_nonneg_left hmain hpos
        linarith
      _ = Real.exp ((Real.pi / a) * B) * Real.exp (-(Real.pi / (2 * a)) * S) := by
        rw [show -(Real.pi / a) * (S / 2 - B) =
            (Real.pi / a) * B + (-(Real.pi / (2 * a)) * S) by
          field_simp [ne_of_gt ha0]
          ring]
        rw [Real.exp_add]
      _ = u k := by
        dsimp [u, S]

/-- The coordinate `(C *ᵥ x) i` is continuous in `x`. -/
lemma continuous_coord_mulVec (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    Continuous (fun x : Fin n → ℝ => (C *ᵥ x) i) := by
  have h : (fun x : Fin n → ℝ => (C *ᵥ x) i) =
      fun x : Fin n → ℝ => ∑ j : Fin n, C i j * x j := by
    funext x
    exact mulVec_apply_sum C x i
  rw [h]
  exact continuous_finsetSum Finset.univ (fun j hj => continuous_const.mul (continuous_apply j))

/-- `sqNormMat C` is continuous. -/
lemma continuous_sqNormMat (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (fun x : Fin n → ℝ => sqNormMat C x) := by
  unfold sqNormMat
  exact continuous_finsetSum Finset.univ (fun i hi => (continuous_coord_mulVec n C i).pow 2)

/-- `cgauss C` is continuous. -/
lemma continuous_cgauss (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) : Continuous (cgauss C) := by
  unfold cgauss
  refine Complex.continuous_exp.comp ?_
  exact continuous_const.mul (continuous_ofReal.comp (continuous_sqNormMat n C))

/-- The periodicized Gaussian is continuous. -/
lemma pgauss_continuous (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.det ≠ 0) :
    Continuous (pgauss C) := by
  classical
  rw [continuous_iff_continuousAt]
  intro x₀
  obtain ⟨a, ha0, hab⟩ := sqNormId_le_const_sqNormMat C hC
  obtain ⟨u, hu, hbnd⟩ := cgauss_bound n C hC x₀ ha0 hab
  let O : Set (Fin n → ℝ) := {x : Fin n → ℝ | ∀ i : Fin n, |x i - x₀ i| < 1 / 2}
  have hcontOn : ContinuousOn (pgauss C) O := by
    refine continuousOn_tsum (f := fun k : Fin n → ℤ => (fun x : Fin n → ℝ => cgauss C (x + intToReal k)))
      (s := O) ?_ hu ?_
    · intro k
      exact ((continuous_cgauss n C).comp (continuous_id.add continuous_const)).continuousOn
    · intro k x hx
      exact hbnd x hx k
  let box : Set (Fin n → ℝ) := Set.pi Set.univ
    (fun i : Fin n => Set.Ioo (x₀ i - 1 / 2) (x₀ i + 1 / 2))
  have hbox_open : IsOpen box := by
    exact isOpen_set_pi Set.finite_univ (fun i _ => isOpen_Ioo)
  have hbox_x₀ : x₀ ∈ box := by
    intro i hi
    exact ⟨by linarith, by linarith⟩
  have hbox_sub : box ⊆ O := by
    intro x hx i
    have hxi : x i ∈ Set.Ioo (x₀ i - 1 / 2) (x₀ i + 1 / 2) := hx i trivial
    exact abs_lt.mpr ⟨by linarith [hxi.1], by linarith [hxi.2]⟩
  have hO_nhds : O ∈ 𝓝 x₀ := by
    exact Filter.mem_of_superset (IsOpen.mem_nhds hbox_open hbox_x₀) hbox_sub
  exact hcontOn.continuousAt hO_nhds

end Continuity

section TorusDescent

/-! ### The periodicized Gaussian as a continuous function on the torus -/

/-- The periodicized Gaussian, as a continuous function on the torus `UnitAddTorus (Fin n)`. -/
noncomputable def pgaussTorus (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.det ≠ 0) :
    C(UnitAddTorus (Fin n), ℂ) :=
  Classical.choose (Commons.Analysis.Fourier.torus_descent_continuous
    (ι := Fin n) (h := ⟨pgauss C, pgauss_continuous n C hC⟩)
    (hper := by
      intro x z
      exact pgauss_periodic C x z))

/-- The descent property: `pgaussTorus` pulled back along the torus map is `pgauss`. -/
lemma pgaussTorus_descent (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.det ≠ 0)
    (x : Fin n → ℝ) :
    pgaussTorus n C hC (torusMk (Fin n) x) = pgauss C x := by
  exact Classical.choose_spec (Commons.Analysis.Fourier.torus_descent_continuous
    (ι := Fin n) (h := ⟨pgauss C, pgauss_continuous n C hC⟩)
    (hper := by
      intro x z
      exact pgauss_periodic C x z)) x

/-- Value at the origin of the torus. -/
lemma pgaussTorus_zero (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.det ≠ 0) :
    pgaussTorus n C hC (0 : UnitAddTorus (Fin n)) = ∑' k : Fin n → ℤ, cgauss C (intToReal k) := by
  have h0 : (0 : UnitAddTorus (Fin n)) = torusMk (Fin n) 0 := by
    ext i
    simp [torusMk]
  rw [h0]
  rw [pgaussTorus_descent n C hC 0]
  exact pgauss_zero C

end TorusDescent

section FourierTransform

/-! ### The Fourier transform of the Gaussian, via `EuclideanSpace` -/

abbrev EuE (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Transport: integral over the coordinate space equals the integral over `EuclideanSpace`. -/
lemma ft_integral_transport_E (n : ℕ) (G : EuE n → ℂ) :
    (∫ x : Fin n → ℝ, G (WithLp.toLp 2 x)) = (∫ v : EuE n, G v) := by
  exact (PiLp.volume_preserving_toLp (Fin n)).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding G

/-- Squared norm on `EuclideanSpace` is the coordinate sum of squares. -/
lemma ft_norm_sq_E (n : ℕ) (x : Fin n → ℝ) :
    ‖(WithLp.toLp 2 x : EuE n)‖ ^ 2 = ∑ i : Fin n, (x i) ^ 2 := by
  rw [EuclideanSpace.norm_eq]
  rw [Real.sq_sqrt]
  · apply Finset.sum_congr rfl
    intro i hi
    simp
  · positivity

/-- Inner product on `EuclideanSpace` is the coordinate dot product. -/
lemma ft_inner_E (n : ℕ) (x y : Fin n → ℝ) :
    inner ℝ (WithLp.toLp 2 x : EuE n) (WithLp.toLp 2 y) = ∑ i : Fin n, x i * y i := by
  simp [inner]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Isotropic Gaussian Fourier transform on `EuclideanSpace` (integral form). -/
lemma iso_ft_E (n : ℕ) (w0 : EuE n) :
    (∫ v : EuE n, cexp (-(Real.pi : ℂ) * ↑‖v‖ ^ 2
        - (2 * (Real.pi : ℂ) * I) * ↑(inner ℝ w0 v)))
      = cexp (-(Real.pi : ℂ) * ↑‖w0‖ ^ 2) := by
  have hb : 0 < (Real.pi : ℂ).re := by
    rw [Complex.ofReal_re]
    exact Real.pi_pos
  have h := GaussianFourier.integral_cexp_neg_mul_sq_norm_add_of_euclideanSpace
    (b := (Real.pi : ℂ)) hb (c := -(2 * (Real.pi : ℂ) * I)) (w := w0) (ι := Fin n)
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hp : (2 * (Real.pi : ℂ) * I) ^ 2 = (-4 : ℂ) * (Real.pi : ℂ) ^ 2 := by
    have hmul : (2 * (Real.pi : ℂ) * I) ^ 2 = (2 * (Real.pi : ℂ)) ^ 2 * I ^ 2 := by ring
    rw [hmul, Complex.I_sq]
    ring
  have hcoef : (2 * (Real.pi : ℂ) * I) ^ 2 / (4 * (Real.pi : ℂ)) = -(Real.pi : ℂ) := by
    rw [hp]
    field_simp [hπ]
  calc
    (∫ v : EuE n, cexp (-(Real.pi : ℂ) * ↑‖v‖ ^ 2
        - (2 * (Real.pi : ℂ) * I) * ↑(inner ℝ w0 v)))
        = (∫ v : EuE n, cexp (-(Real.pi : ℂ) * ↑‖v‖ ^ 2
            + (-(2 * (Real.pi : ℂ) * I)) * ↑(inner ℝ w0 v))) := by
          apply integral_congr_ae
          filter_upwards with v
          congr 1
          ring
    _ = cexp (-(Real.pi : ℂ) * ↑‖w0‖ ^ 2) := by
      rw [h]
      have hdiv : (Real.pi : ℂ) / (Real.pi : ℂ) = (1 : ℂ) := div_self hπ
      rw [hdiv]
      simp
      congr 1
      rw [show (2 * (Real.pi : ℂ) * I) ^ 2 * ↑‖w0‖ ^ 2 / (4 * (Real.pi : ℂ)) =
                (2 * (Real.pi : ℂ) * I) ^ 2 / (4 * (Real.pi : ℂ)) * ↑‖w0‖ ^ 2 by ring]
      rw [hcoef]
      ring

/-- `(↑‖v‖)^2 = ↑(‖v‖^2)`. -/
lemma ft_pow_cast_norm (n : ℕ) (v : EuE n) :
    (↑‖v‖ : ℂ) ^ 2 = ↑(‖v‖ ^ 2) := by
  rw [← Complex.ofReal_pow]

/-- Isotropic Gaussian Fourier transform on the coordinate function space. -/
lemma iso_ft_sqNormId (n : ℕ) (w : Fin n → ℝ) :
    (∫ x : Fin n → ℝ, cexp (-(Real.pi : ℂ) * ↑(sqNormId x)) *
        cexp (-(2 * (Real.pi : ℂ) * I) * ↑(coordDot x w)))
      = cexp (-(Real.pi : ℂ) * ↑(sqNormId w)) := by
  let w0 : EuE n := WithLp.toLp 2 w
  have hpoint : ∀ x : Fin n → ℝ,
      cexp (-(Real.pi : ℂ) * ↑(sqNormId x)) *
        cexp (-(2 * (Real.pi : ℂ) * I) * ↑(coordDot x w)) =
      cexp (-(Real.pi : ℂ) * ↑(‖(WithLp.toLp 2 x : EuE n)‖ ^ 2)) *
        cexp (-(2 * (Real.pi : ℂ) * I) *
          ↑(inner ℝ (WithLp.toLp 2 x : EuE n) w0)) := by
    intro x
    dsimp [w0, sqNormId, coordDot]
    congr 1
    · rw [ft_norm_sq_E n x]
    · rw [ft_inner_E n x w]
  have hIsq := iso_ft_E n w0
  calc
    (∫ x : Fin n → ℝ, cexp (-(Real.pi : ℂ) * ↑(sqNormId x)) *
        cexp (-(2 * (Real.pi : ℂ) * I) * ↑(coordDot x w)))
        = (∫ x : Fin n → ℝ, cexp (-(Real.pi : ℂ) * ↑(‖(WithLp.toLp 2 x : EuE n)‖ ^ 2)) *
            cexp (-(2 * (Real.pi : ℂ) * I) * ↑(inner ℝ (WithLp.toLp 2 x : EuE n) w0))) := by
          apply integral_congr_ae
          filter_upwards with x
          exact hpoint x
    _ = (∫ v : EuE n, cexp (-(Real.pi : ℂ) * ↑(‖v‖ ^ 2)) *
            cexp (-(2 * (Real.pi : ℂ) * I) * ↑(inner ℝ v w0))) := by
          exact ft_integral_transport_E n
            (fun v : EuE n => cexp (-(Real.pi : ℂ) * ↑(‖v‖ ^ 2)) *
              cexp (-(2 * (Real.pi : ℂ) * I) * ↑(inner ℝ v w0)))
    _ = (∫ v : EuE n, cexp (-(Real.pi : ℂ) * ↑‖v‖ ^ 2
          - (2 * (Real.pi : ℂ) * I) * ↑(inner ℝ w0 v))) := by
          apply integral_congr_ae
          filter_upwards with v
          rw [← Complex.exp_add]
          congr 1
          rw [ft_pow_cast_norm n v]
          rw [real_inner_comm]
          ring
    _ = cexp (-(Real.pi : ℂ) * ↑(sqNormId w)) := by
          rw [hIsq]
          congr 1
          dsimp [w0]
          rw [ft_pow_cast_norm n (WithLp.toLp 2 w)]
          rw [ft_norm_sq_E n w]
          rfl

/-- `sqNormMat C x = sqNormId (C *ᵥ x)` (definitional). -/
lemma sqNormMat_eq_sqNormId (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    sqNormMat C x = sqNormId (C *ᵥ x) := rfl

end FourierTransform

section FourierEngine

/-! ### The Fourier transform of the anisotropic Gaussian at lattice points -/

/-- Integral of `f` after a matrix change of variables. -/
lemma integral_comp_toLin'_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M.det ≠ 0) (f : (ι → ℝ) → ℂ)
    (hf : AEStronglyMeasurable f (Measure.map (Matrix.toLin' M) MeasureTheory.volume)) :
    (∫ x : ι → ℝ, f (Matrix.toLin' M x)) = ((|M.det| : ℝ)⁻¹ : ℂ) • (∫ y : ι → ℝ, f y) := by
  rw [← MeasureTheory.integral_map]
  · rw [Real.map_matrix_volume_pi_eq_smul_volume_pi (M := M) hM]
    rw [integral_smul_measure]
    rw [ENNReal.toReal_ofReal]
    · simp
    · positivity
  · exact (Matrix.toLin' M).continuous_of_finiteDimensional.aemeasurable
  · exact hf

/-- The lifted Fourier monomial is an exponential. -/
lemma mFourierLift_eq_cexp (n : ℕ) (m : Fin n → ℤ) (x : Fin n → ℝ) :
    mFourierLift m x = cexp (-(2 * (Real.pi : ℂ) * I) * ↑(coordDot x (intToReal m))) := by
  unfold mFourierLift
  rw [Commons.Analysis.Fourier.mFourierLift_eq_exp n m x]
  congr 1
  simp [coordDot, intToReal]

/-- `coordDot y w` is continuous in `y`. -/
lemma continuous_coordDot_right (n : ℕ) (w : Fin n → ℝ) :
    Continuous (fun y : Fin n → ℝ => coordDot y w) := by
  unfold coordDot
  exact continuous_finsetSum Finset.univ
    (fun i hi => continuous_apply i |>.mul continuous_const)

/-- `sqNormId` is continuous. -/
lemma continuous_sqNormId (n : ℕ) : Continuous (fun y : Fin n → ℝ => sqNormId y) := by
  unfold sqNormId
  exact continuous_finsetSum Finset.univ (fun i hi => (continuous_apply i).pow 2)

/-- The function `F` used in the change of variables is continuous. -/
lemma continuous_coeff_F (n : ℕ) (w : Fin n → ℝ) :
    Continuous (fun y : Fin n → ℝ =>
      cexp (-(2 * (Real.pi : ℂ) * I) * ↑(coordDot y w)) *
        cexp (-(Real.pi : ℂ) * ↑(sqNormId y))) := by
  refine (Complex.continuous_exp.comp ?_).mul (Complex.continuous_exp.comp ?_)
  · exact continuous_const.mul (continuous_ofReal.comp (continuous_coordDot_right n w))
  · exact continuous_const.mul (continuous_ofReal.comp (continuous_sqNormId n))

/-- The Fourier coefficient integral of the anisotropic Gaussian at lattice point `m`. -/
noncomputable def coeffIntegral (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (m : Fin n → ℤ) : ℂ :=
  ∫ x : Fin n → ℝ, mFourierLift m x * cgauss C x

/-- Value of the anisotropic Gaussian Fourier transform at a lattice point. -/
lemma coeffIntegral_eq (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.det ≠ 0)
    (m : Fin n → ℤ) :
    coeffIntegral n C m =
      ((|C.det| : ℝ)⁻¹ : ℂ) * cexp (-(Real.pi : ℂ) * ↑(sqNormMat (C⁻¹)ᵀ (intToReal m))) := by
  classical
  let w : Fin n → ℝ := (C⁻¹)ᵀ *ᵥ intToReal m
  have hw1 : ∀ x : Fin n → ℝ,
      mFourierLift m x = cexp (-(2 * (Real.pi : ℂ) * I) * ↑(coordDot (C *ᵥ x) w)) := by
    intro x
    rw [mFourierLift_eq_cexp]
    have hd : coordDot x (intToReal m) = coordDot (C *ᵥ x) w := by
      dsimp [w]
      exact (coordDot_mulVec_invTranspose (ι := Fin n) C hC x (intToReal m)).symm
    rw [← hd]
  have hpoint : ∀ x : Fin n → ℝ,
      mFourierLift m x * cgauss C x =
        cexp (-(2 * (Real.pi : ℂ) * I) * ↑(coordDot (C *ᵥ x) w)) *
          cexp (-(Real.pi : ℂ) * ↑(sqNormId (C *ᵥ x))) := by
    intro x
    have h1 : mFourierLift m x =
        cexp (-(2 * (Real.pi : ℂ) * I) * ↑(coordDot (C *ᵥ x) w)) := hw1 x
    have h2 : cgauss C x = cexp (-(Real.pi : ℂ) * ↑(sqNormId (C *ᵥ x))) := by
      unfold cgauss
      rw [sqNormMat_eq_sqNormId n C x]
    rw [h1, h2]
  have hmf : coeffIntegral n C m =
      (∫ x : Fin n → ℝ, cexp (-(2 * (Real.pi : ℂ) * I) * ↑(coordDot x (intToReal m))) *
        cgauss C x) := by
    unfold coeffIntegral
    apply integral_congr_ae
    filter_upwards with x
    rw [mFourierLift_eq_cexp]
  let F : (Fin n → ℝ) → ℂ := fun y =>
    cexp (-(2 * (Real.pi : ℂ) * I) * ↑(coordDot y w)) *
      cexp (-(Real.pi : ℂ) * ↑(sqNormId y))
  have hpoint' : ∀ x : Fin n → ℝ,
      cexp (-(2 * (Real.pi : ℂ) * I) * ↑(coordDot x (intToReal m))) * cgauss C x =
        F (C *ᵥ x) := by
    intro x
    have hp := hpoint x
    rwa [mFourierLift_eq_cexp] at hp
  have hsub : coeffIntegral n C m =
      ((|C.det| : ℝ)⁻¹ : ℂ) • (∫ y : Fin n → ℝ, F y) := by
    rw [hmf]
    have hint : (∫ x : Fin n → ℝ,
        cexp (-(2 * (Real.pi : ℂ) * I) * ↑(coordDot x (intToReal m))) * cgauss C x) =
        (∫ x : Fin n → ℝ, F (C *ᵥ x)) := by
      apply integral_congr_ae
      filter_upwards with x
      exact hpoint' x
    rw [hint]
    change (∫ x : Fin n → ℝ, F (Matrix.toLin' C x)) = ((|C.det| : ℝ)⁻¹ : ℂ) • (∫ y : Fin n → ℝ, F y)
    have hmf' : AEStronglyMeasurable F (Measure.map (Matrix.toLin' C) MeasureTheory.volume) := by
      dsimp [F]
      exact (continuous_coeff_F n w).aestronglyMeasurable
    rw [integral_comp_toLin'_det (M := C) hC F hmf']
  have hiso : (∫ y : Fin n → ℝ, F y) = cexp (-(Real.pi : ℂ) * ↑(sqNormId w)) := by
    dsimp [F]
    simpa [mul_comm] using (iso_ft_sqNormId n w)
  calc
    coeffIntegral n C m = ((|C.det| : ℝ)⁻¹ : ℂ) • (∫ y : Fin n → ℝ, F y) := hsub
    _ = ((|C.det| : ℝ)⁻¹ : ℂ) • cexp (-(Real.pi : ℂ) * ↑(sqNormId w)) := by rw [hiso]
    _ = ((|C.det| : ℝ)⁻¹ : ℂ) * cexp (-(Real.pi : ℂ) * ↑(sqNormMat (C⁻¹)ᵀ (intToReal m))) := by
      congr 1


end FourierEngine


section CoefficientEngine

/-! ### The Fourier coefficient of the periodicized Gaussian equals the transform value -/

variable {d : Type*} [Fintype d]

/-- The fundamental box `(0,1]ᵈ`. -/
def boxF (d : Type*) : Set (d → ℝ) := {x : d → ℝ | ∀ i : d, x i ∈ Set.Ioc (0 : ℝ) 1}

/-- The box translated by `k`; these tile `ℝᵈ`. -/
def boxK (k : d → ℤ) : Set (d → ℝ) :=
  {x : d → ℝ | ∀ i : d, x i ∈ Set.Ioc (k i : ℝ) ((k i : ℝ) + 1)}

lemma boxK_measurable (k : d → ℤ) : MeasurableSet (boxK k) := by
  rw [show boxK k = Set.univ.pi (fun i : d => Set.Ioc (k i : ℝ) ((k i : ℝ) + 1)) by
    ext x; simp [boxK]]
  exact MeasurableSet.univ_pi (fun i => measurableSet_Ioc)

lemma boxF_measurable : MeasurableSet (boxF d) := by
  rw [show boxF d = Set.univ.pi (fun _ : d => Set.Ioc (0 : ℝ) 1) by
    ext x; simp [boxF]]
  exact MeasurableSet.univ_pi (fun i => measurableSet_Ioc)

/-- Each real lies in exactly one translated half-open box. -/
lemma mem_boxK_self (x : d → ℝ) : x ∈ boxK (fun i => Int.ceil (x i) - 1) := by
  intro i
  let kk : ℤ := Int.ceil (x i) - 1
  have hle : x i ≤ (Int.ceil (x i) : ℝ) := Int.le_ceil (x i)
  have hlt : ((Int.ceil (x i) : ℝ) - 1) < x i := by
    have hc := Int.ceil_lt_add_one (x i)
    linarith
  have hlow : (kk : ℝ) < x i := by
    dsimp [kk]
    push_cast
    exact hlt
  have hup : x i ≤ (kk : ℝ) + 1 := by
    dsimp [kk]
    push_cast
    linarith
  exact ⟨hlow, hup⟩

/-- Boxes with different indices are disjoint. -/
lemma boxK_disjoint {k l : d → ℤ} (hne : k ≠ l) : Disjoint (boxK k) (boxK l) := by
  rw [Set.disjoint_left]
  intro x hxk hxl
  apply hne
  funext i
  by_contra hne_i
  have hk : x i ∈ Set.Ioc (k i : ℝ) ((k i : ℝ) + 1) := hxk i
  have hl : x i ∈ Set.Ioc (l i : ℝ) ((l i : ℝ) + 1) := hxl i
  by_cases h : k i ≤ l i
  · have hkl' : k i < l i := lt_of_le_of_ne h hne_i
    have hle : (k i : ℝ) + 1 ≤ (l i : ℝ) := by
      have hz : (k i : ℤ) + 1 ≤ l i := by omega
      exact_mod_cast hz
    have h1 : x i ≤ (k i : ℝ) + 1 := hk.2
    have h2 : (l i : ℝ) < x i := hl.1
    linarith
  · have hl' : l i < k i := lt_of_not_ge h
    have hle : (l i : ℝ) + 1 ≤ (k i : ℝ) := by
      have hz : (l i : ℤ) + 1 ≤ k i := by omega
      exact_mod_cast hz
    have h1 : x i ≤ (l i : ℝ) + 1 := hl.2
    have h2 : (k i : ℝ) < x i := hk.1
    linarith

/-- The shifted boxes are pairwise disjoint. -/
lemma boxK_pairwise_disjoint :
    Pairwise (fun k l : d → ℤ => Disjoint (boxK k) (boxK l)) := by
  intro k l hne
  exact boxK_disjoint hne

/-- The translated boxes cover `ℝᵈ`. -/
lemma union_boxK (d : Type*) [Fintype d] :
    (⋃ k : d → ℤ, boxK k) = Set.univ := by
  ext x
  constructor
  · intro h; trivial
  · intro hx
    exact Set.mem_iUnion.mpr ⟨fun i => Int.ceil (x i) - 1, mem_boxK_self x⟩

/-- Tiling: the integral over `ℝᵈ` is the sum over boxes. -/
lemma tsum_box_integrals (f : (d → ℝ) → ℂ) (hf : Integrable f) :
    ∑' k : d → ℤ, (∫ x in boxK k, f x) = ∫ x : d → ℝ, f x := by
  have hfi : IntegrableOn f (⋃ k : d → ℤ, boxK k) := by
    rw [union_boxK d]
    exact hf.integrableOn
  have htsum := MeasureTheory.integral_iUnion (fun k => boxK_measurable k)
    (boxK_pairwise_disjoint) hfi
  rw [union_boxK d] at htsum
  simpa using htsum.symm

/-- The translated box is the image of the fundamental box. -/
lemma boxK_eq_image (k : d → ℤ) :
    boxK k = (fun x : d → ℝ => x + intToReal k) '' boxF d := by
  ext y
  constructor
  · intro hy
    refine ⟨fun i => y i - (k i : ℝ), ?_, ?_⟩
    · intro i
      have hyi : y i ∈ Set.Ioc (k i : ℝ) ((k i : ℝ) + 1) := hy i
      have hl : (0 : ℝ) < y i - (k i : ℝ) := by linarith [hyi.1]
      have hu : y i - (k i : ℝ) ≤ 1 := by linarith [hyi.2]
      exact ⟨hl, hu⟩
    · funext i
      simp [intToReal]
  · rintro ⟨x, hx, rfl⟩
    intro i
    have hxi : x i ∈ Set.Ioc (0 : ℝ) 1 := hx i
    have hl : (k i : ℝ) < x i + (k i : ℝ) := by linarith [hxi.1]
    have hu : x i + (k i : ℝ) ≤ (k i : ℝ) + 1 := by linarith [hxi.2]
    exact ⟨hl, hu⟩

/-- Translation of a set integral over the fundamental box. -/
lemma setIntegral_box_translate (f : (d → ℝ) → ℂ) (k : d → ℤ) :
    (∫ x in boxF d, f (x + intToReal k)) = ∫ x in boxK k, f x := by
  have hp : MeasurePreserving (fun x : d → ℝ => x + intToReal k) volume volume :=
    measurePreserving_add_right volume (intToReal k)
  have hme : MeasurableEmbedding (fun x : d → ℝ => x + intToReal k) := by
    exact (Homeomorph.addRight (intToReal k)).measurableEmbedding
  rw [boxK_eq_image k]
  exact (hp.setIntegral_image_emb hme f (boxF d)).symm

/-- Periodicity of the lifted Fourier monomial under `ℤ`-shifts. -/
lemma mFourierLift_periodic (m : d → ℤ) (x : d → ℝ) (k : d → ℤ) :
    mFourierLift m (x - intToReal k) = mFourierLift m x := by
  unfold mFourierLift
  congr 2
  funext i
  have hsub : ((x i - (k i : ℝ) : ℝ) : UnitAddCircle) = (x i : UnitAddCircle) := by
    rw [QuotientAddGroup.eq]
    rw [AddSubgroup.mem_zmultiples_iff]
    refine ⟨k i, ?_⟩
    simp
  simpa [intToReal, sub_eq_add_neg] using hsub

end CoefficientEngine




section CoeffValue

/-! ### The coefficient of the periodicized Gaussian: computation -/

variable {d : Type*} [Fintype d]

/-- Bound for `cgauss` over the fundamental box: `|g(x+k)| ≤ u k` with `u` summable. -/
lemma cgauss_bound_box (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.det ≠ 0) :
    ∃ u : (Fin n → ℤ) → ℝ,
      (Summable u) ∧
      (∀ k : Fin n → ℤ,
        0 ≤ u k ∧
        (∀ x : Fin n → ℝ, x ∈ boxF (Fin n) → ‖cgauss C (x + intToReal k)‖ ≤ u k)) := by
  classical
  obtain ⟨a, ha0, hab⟩ := sqNormId_le_const_sqNormMat C hC
  let B : ℝ := (Fintype.card (Fin n) : ℝ)
  let u : (Fin n → ℤ) → ℝ := fun k => Real.exp ((Real.pi / a) * B) *
    Real.exp (-(Real.pi / (2 * a)) * (∑ i : Fin n, ((k i : ℝ) ^ 2)))
  refine ⟨u, ?sum, ?rest⟩
  · have hc : 0 < Real.pi / (2 * a) := by positivity
    have hs : Summable (fun k : Fin n → ℤ =>
        Real.exp (-(Real.pi / (2 * a)) * (∑ i : Fin n, ((k i : ℝ) ^ 2)))) :=
      summable_exp_neg_sqNormId_int n hc
    dsimp [u]
    exact hs.mul_left (Real.exp ((Real.pi / a) * B))
  · intro k
    constructor
    · dsimp [u]
      positivity
    · intro x hx
      have hxi : ∀ i : Fin n, |x i| ≤ 1 := by
        intro i
        have hxi : x i ∈ Set.Ioc (0 : ℝ) 1 := hx i
        have h1 : -1 ≤ x i := by linarith [hxi.1]
        have h2 : x i ≤ 1 := by linarith [hxi.2]
        exact abs_le.mpr ⟨h1, h2⟩
      have hcoord : ∀ i : Fin n, (x i + (k i : ℝ)) ^ 2 ≥ ((k i : ℝ) ^ 2) / 2 - 1 := by
        intro i
        simpa using (coord_sq_lower (x i) (k i : ℝ) 1 (by norm_num) (hxi i))
      have hsqId : (∑ i : Fin n, ((x i + (k i : ℝ)) ^ 2)) ≥
          (∑ i : Fin n, ((k i : ℝ) ^ 2)) / 2 - B := by
        dsimp [B]
        calc
          (∑ i : Fin n, (x i + (k i : ℝ)) ^ 2) ≥
              ∑ i : Fin n, (((k i : ℝ) ^ 2) / 2 - 1) := by
            exact Finset.sum_le_sum (fun i hi => hcoord i)
          _ = (∑ i : Fin n, ((k i : ℝ) ^ 2)) / 2 - Fintype.card (Fin n) := by
            rw [Finset.sum_sub_distrib]
            rw [Finset.sum_div]
            rw [Finset.sum_const]
            simp
      let S : ℝ := ∑ i : Fin n, ((k i : ℝ) ^ 2)
      have hT : sqNormId (x + intToReal k) = ∑ i : Fin n, ((x i + (k i : ℝ)) ^ 2) := by
        dsimp [sqNormId, intToReal]
      calc
        ‖cgauss C (x + intToReal k)‖ ≤ Real.exp (-(Real.pi / a) * sqNormId (x + intToReal k)) := by
          exact exp_neg_sqMat_le n C hC a ha0 hab (x + intToReal k)
        _ ≤ Real.exp (-(Real.pi / a) * (S / 2 - B)) := by
          rw [Real.exp_le_exp]
          have hmain : S / 2 - B ≤ sqNormId (x + intToReal k) := by
            rw [hT]
            nlinarith
          have hpos : 0 ≤ Real.pi / a := by positivity
          have hm : (Real.pi / a) * (S / 2 - B) ≤ (Real.pi / a) * sqNormId (x + intToReal k) :=
            mul_le_mul_of_nonneg_left hmain hpos
          linarith
        _ = Real.exp ((Real.pi / a) * B) * Real.exp (-(Real.pi / (2 * a)) * S) := by
          rw [show -(Real.pi / a) * (S / 2 - B) =
              (Real.pi / a) * B + (-(Real.pi / (2 * a)) * S) by
            field_simp [ne_of_gt ha0]
            ring]
          rw [Real.exp_add]
        _ = u k := by
          dsimp [u, S]


/-- Sum and integral over the fundamental box commute (absolute summability of norms). -/
lemma box_integral_tsum (F : (d → ℤ) → (d → ℝ) → ℂ)
    (hF_int : ∀ k, IntegrableOn (F k) (boxF d))
    (hF_sum : Summable (fun k : d → ℤ => ∫ x in boxF d, ‖F k x‖)) :
    (∫ x in boxF d, (∑' k : d → ℤ, F k x)) = ∑' k : d → ℤ, (∫ x in boxF d, F k x) := by
  let μ : Measure (d → ℝ) := volume.restrict (boxF d)
  have hint : ∀ k, Integrable (F k) μ := by
    intro k
    exact hF_int k
  have hsum : Summable (fun k : d → ℤ => ∫ x, ‖F k x‖ ∂μ) := by
    simpa [μ] using hF_sum
  have h := MeasureTheory.integral_tsum_of_summable_integral_norm hint hsum
  simpa [μ] using h.symm

end CoeffValue




section CoefficientId

variable {d : Type*} [Fintype d]

/-- The volume of the fundamental box is finite. -/
lemma volume_boxF_lt_top (d : Type*) [Fintype d] :
    volume (boxF d) < ∞ := by
  have hs : boxF d ⊆ Set.Icc (0 : d → ℝ) 1 := by
    intro x hx
    constructor
    · intro i
      exact le_of_lt (hx i).1
    · intro i
      exact (hx i).2
  have hcube : volume (Set.Icc (0 : d → ℝ) 1) < ∞ := by
    rw [Real.volume_Icc_pi]
    exact ENNReal.prod_lt_top (fun i hi => by simp)
  exact lt_of_le_of_lt (measure_mono hs) hcube

/-- The measure of the fundamental box is at most `1`. -/
lemma volume_boxF_le_one (d : Type*) [Fintype d] : volume (boxF d) ≤ 1 := by
  have hs : boxF d ⊆ Set.Icc (0 : d → ℝ) 1 := by
    intro x hx
    constructor
    · intro i
      exact le_of_lt (hx i).1
    · intro i
      exact (hx i).2
  have hcube : volume (Set.Icc (0 : d → ℝ) 1) = (1 : ℝ≥0∞) := by
    rw [Real.volume_Icc_pi]
    simp
  rw [← hcube]
  exact measure_mono hs

/-- `mFourierLift m` is continuous. -/
lemma continuous_mFourierLift (m : d → ℤ) : Continuous (fun x : d → ℝ => mFourierLift m x) := by
  unfold mFourierLift
  exact (UnitAddTorus.mFourier (-m)).continuous.comp
    (continuous_pi (fun i : d => (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_apply i)))

/-- `‖mFourierLift m x‖ ≤ 1`. -/
lemma norm_mFourierLift_le_one (m : d → ℤ) (x : d → ℝ) : ‖mFourierLift m x‖ ≤ 1 := by
  unfold mFourierLift
  calc
    ‖(UnitAddTorus.mFourier (-m)) (fun i : d => (x i : UnitAddCircle))‖ ≤
        ‖UnitAddTorus.mFourier (-m)‖ := ContinuousMap.norm_coe_le_norm _ _
    _ = 1 := UnitAddTorus.mFourier_norm

/-- The box term of the Gaussian is integrable on the box. -/
lemma integrable_box_term (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.det ≠ 0)
    (m : Fin n → ℤ) (k : Fin n → ℤ) :
    IntegrableOn (fun x : Fin n → ℝ => mFourierLift m x * cgauss C (x + intToReal k))
      (boxF (Fin n)) := by
  rcases cgauss_bound_box n C hC with ⟨u, hu, hrest⟩
  rcases hrest k with ⟨hun, hb⟩
  let g := fun x : Fin n → ℝ => mFourierLift m x * cgauss C (x + intToReal k)
  refine IntegrableOn.of_bound (volume_boxF_lt_top (Fin n)) ?_ (u k) ?_
  · have hc1 : Continuous (fun x : Fin n → ℝ => mFourierLift m x) := continuous_mFourierLift m
    have hc2 : Continuous (fun x : Fin n → ℝ => cgauss C (x + intToReal k)) :=
      (continuous_cgauss n C).comp (continuous_id.add continuous_const)
    exact (hc1.mul hc2).aestronglyMeasurable
  · have hle : ∀ x : Fin n → ℝ, x ∈ boxF (Fin n) → ‖g x‖ ≤ u k := by
      intro x hx
      dsimp [g]
      calc
        ‖mFourierLift m x * cgauss C (x + intToReal k)‖ ≤
            ‖mFourierLift m x‖ * ‖cgauss C (x + intToReal k)‖ := norm_mul_le _ _
        _ ≤ ‖cgauss C (x + intToReal k)‖ := by
          exact mul_le_of_le_one_left (norm_nonneg _) (norm_mFourierLift_le_one m x)
        _ ≤ u k := hb x hx
    have hset : MeasurableSet {x : Fin n → ℝ | x ∈ boxF (Fin n)} := boxF_measurable
    filter_upwards [self_mem_ae_restrict hset] with x hx
    exact hle x hx

/-- periodicity (additive version) of the lifted monomial. -/
lemma mFourierLift_periodic_add (m : d → ℤ) (x : d → ℝ) (k : d → ℤ) :
    mFourierLift m (x + intToReal k) = mFourierLift m x := by
  have h := mFourierLift_periodic m (x + intToReal k) k
  simpa [sub_eq_add_neg, add_assoc] using h.symm

/-- pointwise expansion of the product with the periodicized Gaussian. -/
lemma pointwise_expand (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (m : Fin n → ℤ) (x : Fin n → ℝ) :
    mFourierLift m x * pgauss C x =
      ∑' k : Fin n → ℤ, mFourierLift m x * cgauss C (x + intToReal k) := by
  rw [pgauss]
  rw [← tsum_mul_left]

/-- The coefficient, written over the fundamental box. -/
lemma coeff_box_form (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.det ≠ 0)
    (m : Fin n → ℤ) :
    UnitAddTorus.mFourierCoeff (⇑(pgaussTorus n C hC)) m =
      (∫ x in boxF (Fin n), mFourierLift m x * pgauss C x) := by
  let S0 : Set (Fin n → ℝ) := {x : Fin n → ℝ | ∀ i : Fin n, x i ∈ Set.Ioc (0 : ℝ) ((0 : ℝ) + 1)}
  have hcoef :
      UnitAddTorus.mFourierCoeff (⇑(pgaussTorus n C hC)) m =
        ∫ x in S0,
          ((UnitAddTorus.mFourier (-m)) (fun i => (x i : UnitAddCircle))) •
            (pgaussTorus n C hC) (fun i => (x i : UnitAddCircle)) := by
    simpa [S0] using (UnitAddTorus.mFourierCoeff_eq_integral (f := ⇑(pgaussTorus n C hC))
      (n := m) (a := fun _ : Fin n => (0 : ℝ)))
  have hset : S0 = boxF (Fin n) := by
    ext x
    simp [S0, boxF]
  calc
    UnitAddTorus.mFourierCoeff (⇑(pgaussTorus n C hC)) m
        = ∫ x in S0,
            ((UnitAddTorus.mFourier (-m)) (fun i => (x i : UnitAddCircle))) •
              (pgaussTorus n C hC) (fun i => (x i : UnitAddCircle)) := hcoef
    _ = (∫ x in boxF (Fin n), mFourierLift m x * pgauss C x) := by
      rw [hset]
      apply integral_congr_ae
      filter_upwards with x
      unfold mFourierLift
      rw [smul_eq_mul]
      congr 1
      congr 1
      change pgaussTorus n C hC (torusMk (Fin n) x) = pgauss C x
      exact pgaussTorus_descent n C hC x

/-- Expand the periodicized Gaussian in the box integral and swap sum/integral. -/
lemma box_expand_tsum (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.det ≠ 0)
    (m : Fin n → ℤ) :
    (∫ x in boxF (Fin n), mFourierLift m x * pgauss C x) =
      ∑' k : Fin n → ℤ, (∫ x in boxF (Fin n), mFourierLift m x * cgauss C (x + intToReal k)) := by
  let F : (Fin n → ℤ) → (Fin n → ℝ) → ℂ := fun k x =>
    mFourierLift m x * cgauss C (x + intToReal k)
  have hint : ∀ k, IntegrableOn (F k) (boxF (Fin n)) := by
    intro k
    exact integrable_box_term n C hC m k
  have hsum : Summable (fun k : Fin n → ℤ => ∫ x in boxF (Fin n), ‖F k x‖) := by
    rcases cgauss_bound_box n C hC with ⟨u, hu, hrest⟩
    have hle : ∀ k : Fin n → ℤ, ∫ x in boxF (Fin n), ‖F k x‖ ≤ u k := by
      intro k
      rcases hrest k with ⟨hun, hb⟩
      have hfi := integrable_box_term n C hC m k
      have hfn : IntegrableOn (fun x : Fin n → ℝ => ‖F k x‖) (boxF (Fin n)) := by
        dsimp [IntegrableOn]
        exact MeasureTheory.Integrable.norm (by simpa [IntegrableOn] using hfi)
      have hcst : IntegrableOn (fun _ : Fin n → ℝ => u k) (boxF (Fin n)) := by
        exact integrableOn_const (C := u k) (by
          exact (ne_of_lt (volume_boxF_lt_top (Fin n))))
      have hlept : ∀ x : Fin n → ℝ, x ∈ boxF (Fin n) → ‖F k x‖ ≤ u k := by
        intro x hx
        dsimp [F]
        calc
          ‖mFourierLift m x * cgauss C (x + intToReal k)‖ ≤
              ‖mFourierLift m x‖ * ‖cgauss C (x + intToReal k)‖ := norm_mul_le _ _
          _ ≤ ‖cgauss C (x + intToReal k)‖ := by
            exact mul_le_of_le_one_left (norm_nonneg _) (norm_mFourierLift_le_one m x)
          _ ≤ u k := hb x hx
      have hmono := MeasureTheory.setIntegral_mono_on hfn hcst (boxF_measurable) hlept
      -- ∫ s ‖F k‖ ≤ ∫ s u k
      calc
        (∫ x in boxF (Fin n), ‖F k x‖) ≤ (∫ x in boxF (Fin n), u k) := hmono
        _ = u k * volume.real (boxF (Fin n)) := by
          rw [setIntegral_const]
          simp [smul_eq_mul, mul_comm]
        _ ≤ u k := by
          have hvol : volume.real (boxF (Fin n)) ≤ 1 := by
            have hle1 : volume (boxF (Fin n)) ≤ 1 := volume_boxF_le_one (Fin n)
            have hne : volume (boxF (Fin n)) ≠ ∞ := (ne_of_lt (volume_boxF_lt_top (Fin n)))
            have hiff : (volume (boxF (Fin n))).toReal ≤ 1 ↔ volume (boxF (Fin n)) ≤ 1 := by
              have h := ENNReal.toReal_le_toReal (a := volume (boxF (Fin n))) (b := (1 : ℝ≥0∞)) hne (by simp)
              simpa using h
            change (volume (boxF (Fin n))).toReal ≤ 1
            exact hiff.mpr hle1
          nlinarith
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => hle k) ?_
    · -- nonneg of ∫box ‖F k‖
      exact setIntegral_nonneg boxF_measurable (fun x hx => norm_nonneg (F k x))
    · -- summable u
      exact hu
  calc
    (∫ x in boxF (Fin n), mFourierLift m x * pgauss C x)
        = (∫ x in boxF (Fin n), (∑' k : Fin n → ℤ, F k x)) := by
          apply integral_congr_ae
          filter_upwards with x
          dsimp [F]
          exact pointwise_expand n C m x
    _ = ∑' k : Fin n → ℤ, (∫ x in boxF (Fin n), F k x) := by
          exact box_integral_tsum F hint hsum
    _ = ∑' k : Fin n → ℤ, (∫ x in boxF (Fin n), mFourierLift m x * cgauss C (x + intToReal k)) := by rfl

/-- Shift each box integral to its translated box. -/
lemma box_sum_shift (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (m : Fin n → ℤ) :
    (∑' k : Fin n → ℤ, (∫ x in boxF (Fin n), mFourierLift m x * cgauss C (x + intToReal k))) =
      ∑' k : Fin n → ℤ, (∫ x in boxK k, mFourierLift m x * cgauss C x) := by
  apply tsum_congr
  intro k
  calc
    (∫ x in boxF (Fin n), mFourierLift m x * cgauss C (x + intToReal k))
        = (∫ x in boxF (Fin n),
            (fun y : Fin n → ℝ => mFourierLift m y * cgauss C y) (x + intToReal k)) := by
          apply integral_congr_ae
          filter_upwards with x
          conv_lhs => rw [show mFourierLift m x = mFourierLift m (x + intToReal k) by
            exact (mFourierLift_periodic_add m x k).symm]
    _ = ∫ x in boxK k, (fun y : Fin n → ℝ => mFourierLift m y * cgauss C y) x := by
          exact setIntegral_box_translate (fun y : Fin n → ℝ => mFourierLift m y * cgauss C y) k
    _ = ∫ x in boxK k, mFourierLift m x * cgauss C x := by rfl

/-- The whole-space lifted Gaussian is integrable. -/
lemma gaussian_lifted_integrable (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.det ≠ 0)
    (m : Fin n → ℤ) :
    Integrable (fun x : Fin n → ℝ => mFourierLift m x * cgauss C x) := by
  obtain ⟨a, ha0, hab⟩ := sqNormId_le_const_sqNormMat C hC
  have hc : 0 < Real.pi / a := by positivity
  have hbnd : ∀ᵐ x ∂volume, ‖mFourierLift m x * cgauss C x‖ ≤ Real.exp (-(Real.pi / a) * sqNormId x) := by
    refine ae_of_all volume (fun x => ?_)
    calc
      ‖mFourierLift m x * cgauss C x‖ ≤ ‖mFourierLift m x‖ * ‖cgauss C x‖ := norm_mul_le _ _
      _ ≤ ‖cgauss C x‖ := mul_le_of_le_one_left (norm_nonneg _) (norm_mFourierLift_le_one m x)
      _ ≤ Real.exp (-(Real.pi / a) * sqNormId x) := exp_neg_sqMat_le n C hC a ha0 hab x
  have hmeas : AEStronglyMeasurable (fun x : Fin n → ℝ => mFourierLift m x * cgauss C x) volume :=
    ((continuous_mFourierLift m).mul (continuous_cgauss n C)).aestronglyMeasurable
  exact MeasureTheory.Integrable.mono'
    (Commons.Analysis.Fourier.gaussian_integrable_fn n (Real.pi / a) hc) hmeas hbnd

lemma mFourierCoeff_pgaussTorus (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.det ≠ 0)
    (m : Fin n → ℤ) :
    UnitAddTorus.mFourierCoeff (⇑(pgaussTorus n C hC)) m = coeffIntegral n C m := by
  calc
    UnitAddTorus.mFourierCoeff (⇑(pgaussTorus n C hC)) m
        = (∫ x in boxF (Fin n), mFourierLift m x * pgauss C x) := coeff_box_form n C hC m
    _ = ∑' k : Fin n → ℤ, (∫ x in boxF (Fin n), mFourierLift m x * cgauss C (x + intToReal k)) :=
          box_expand_tsum n C hC m
    _ = ∑' k : Fin n → ℤ, (∫ x in boxK k, mFourierLift m x * cgauss C x) := box_sum_shift n C m
    _ = (∫ x : Fin n → ℝ, mFourierLift m x * cgauss C x) := by
          exact tsum_box_integrals (fun x : Fin n → ℝ => mFourierLift m x * cgauss C x)
            (gaussian_lifted_integrable n C hC m)
    _ = coeffIntegral n C m := by rfl


end CoefficientId
/-- n-dimensional Poisson summation / Jacobi theta transformation for a Gaussian over the
integer lattice ℤⁿ, in the s = 1 normalization: for any invertible real `n × n` matrix `C`,

  Σ_{k ∈ ℤⁿ} exp (-π·‖C·k‖²) = |det C|⁻¹ · Σ_{m ∈ ℤⁿ} exp (-π·‖C⁻ᵀ·m‖²),

where vectors live in `Fin n → ℝ`, `‖x‖² = Σᵢ (x i)²`, and `C⁻ᵀ = (C⁻¹)ᵀ`.  Derive it from the
one-dimensional identity `Real.tsum_exp_neg_mul_int_sq` (or `Complex.tsum_exp_neg_quadratic`)
together with an n-dimensional Poisson-summation argument, e.g. Fourier series on the
n-torus `UnitAddTorus (Fin n)` (`Mathlib.Analysis.Fourier.AddCircleMulti`), whose Fourier
coefficients `UnitAddTorus.mFourierCoeff` of the periodicized Gaussian are the values of its
n-dimensional Fourier transform at lattice points, computed with
`fourier_gaussian_innerProductSpace` / `Real.map_matrix_volume_pi_eq_smul_volume_pi`
(after identifying `Fin n → ℝ` with `EuclideanSpace ℝ (Fin n)`), plus
`UnitAddTorus.hasSum_mFourier_series_apply_of_summable` for pointwise convergence of the
Fourier series of a continuous function with summable coefficients. -/
theorem gaussian_psf_core (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.det ≠ 0) :
    (∑' k : Fin n → ℤ, Real.exp (-Real.pi * (∑ i, (((C.mulVec fun j : Fin n => (k j : ℝ)) i) ^ 2)))) =
      |C.det|⁻¹ *
        (∑' m : Fin n → ℤ,
          Real.exp (-Real.pi * (∑ i, ((((C⁻¹).transpose.mulVec fun j : Fin n => (m j : ℝ)) i) ^ 2)))) := by
  -- Express the left hand side and the right hand side through `rgauss`.
  have hL : (∑' k : Fin n → ℤ, Real.exp (-Real.pi * (∑ i, (((C.mulVec fun j : Fin n => (k j : ℝ)) i) ^ 2)))) =
      ∑' k : Fin n → ℤ, rgauss C (intToReal k) := by
    apply tsum_congr
    intro k
    rfl
  have hR : (∑' m : Fin n → ℤ, Real.exp (-Real.pi * (∑ i,
      ((((C⁻¹).transpose.mulVec fun j : Fin n => (m j : ℝ)) i) ^ 2)))) =
      ∑' m : Fin n → ℤ, rgauss (C⁻¹).transpose (intToReal m) := by
    apply tsum_congr
    intro m
    rfl
  rw [hL, hR]
  -- Coefficient identity and value
  have hcoef : ∀ m : Fin n → ℤ,
      UnitAddTorus.mFourierCoeff (⇑(pgaussTorus n C hC)) m =
        ((|C.det| : ℝ)⁻¹ : ℂ) * cexp (-(Real.pi : ℂ) * ↑(sqNormMat (C⁻¹)ᵀ (intToReal m))) := by
    intro m
    rw [mFourierCoeff_pgaussTorus n C hC m]
    exact coeffIntegral_eq n C hC m
  -- summability of the coefficient norms
  have hMnz : ((C⁻¹).transpose).det ≠ 0 := by
    rw [Matrix.det_transpose]
    intro hz
    have hd : (C⁻¹).det * C.det = 1 := by
      rw [← Matrix.det_mul]
      rw [Matrix.nonsing_inv_mul C (isUnit_iff_ne_zero.mpr hC)]
      simp
    rw [hz, zero_mul] at hd
    norm_num at hd
  have hz := Commons.Analysis.Fourier.zpow_summable_gauss_matrix n ((C⁻¹).transpose) hMnz Real.pi Real.pi_pos
  let decayReal : (Fin n → ℤ) → ℝ := fun m =>
    Real.exp (-Real.pi * (∑ i : Fin n, ((((C⁻¹).transpose) *ᵥ fun j : Fin n => (m j : ℝ)) i) ^ 2))
  have hg : Summable decayReal := by
    simpa [decayReal] using hz
  have hsumN : Summable (fun m : Fin n → ℤ =>
      ‖UnitAddTorus.mFourierCoeff (⇑(pgaussTorus n C hC)) m‖) := by
    refine Summable.of_norm_bounded (g := fun m : Fin n → ℤ => ((|C.det| : ℝ)⁻¹) * decayReal m) ?_ ?_
    · exact hg.mul_left ((|C.det| : ℝ)⁻¹)
    · intro m
      have hnorm : ‖UnitAddTorus.mFourierCoeff (⇑(pgaussTorus n C hC)) m‖ ≤
          ((|C.det| : ℝ)⁻¹) * decayReal m := by
        rw [hcoef m]
        calc
          ‖((|C.det| : ℝ)⁻¹ : ℂ) * cexp (-(Real.pi : ℂ) * ↑(sqNormMat (C⁻¹)ᵀ (intToReal m)))‖ ≤
              ‖((|C.det| : ℝ)⁻¹ : ℂ)‖ * ‖cexp (-(Real.pi : ℂ) * ↑(sqNormMat (C⁻¹)ᵀ (intToReal m)))‖ :=
                norm_mul_le _ _
          _ = ((|C.det| : ℝ)⁻¹) * Real.exp (-Real.pi * sqNormMat (C⁻¹)ᵀ (intToReal m)) := by
            rw [Complex.norm_exp]
            congr 2
            · simp
            · rw [show (-(Real.pi : ℂ) * (sqNormMat (C⁻¹)ᵀ (intToReal m) : ℂ)) =
                    ((-Real.pi * sqNormMat (C⁻¹)ᵀ (intToReal m) : ℝ) : ℂ) by push_cast; ring]
              simp
          _ = ((|C.det| : ℝ)⁻¹) * decayReal m := by
            dsimp [decayReal]
            rfl
      exact (by simpa using hnorm)
  have hsumm : Summable (fun m : Fin n → ℤ =>
      UnitAddTorus.mFourierCoeff (⇑(pgaussTorus n C hC)) m) := by
    exact Summable.of_norm hsumN
  -- Fourier series at the origin of the torus
  have hfs := UnitAddTorus.hasSum_mFourier_series_apply_of_summable (f := pgaussTorus n C hC) hsumm
    (0 : UnitAddTorus (Fin n))
  have hsum0 : HasSum (fun m : Fin n → ℤ => UnitAddTorus.mFourierCoeff (⇑(pgaussTorus n C hC)) m)
      (∑' k : Fin n → ℤ, cgauss C (intToReal k)) := by
    -- hfs: HasSum (fun m => coeff m • mFourier m 0) (pgaussTorus n C hC 0)
    have hfs' : HasSum (fun m : Fin n → ℤ => UnitAddTorus.mFourierCoeff (⇑(pgaussTorus n C hC)) m)
        ((pgaussTorus n C hC) 0) := by
      simpa [mFourier_zero_torus, smul_eq_mul] using hfs
    simpa [pgaussTorus_zero] using hfs'
  -- coefficient value under the sum
  have hvalsum : (∑' m : Fin n → ℤ, UnitAddTorus.mFourierCoeff (⇑(pgaussTorus n C hC)) m) =
      ((|C.det| : ℝ)⁻¹ : ℂ) * (∑' m : Fin n → ℤ,
        cexp (-(Real.pi : ℂ) * ↑(sqNormMat (C⁻¹)ᵀ (intToReal m)))) := by
    calc
      (∑' m : Fin n → ℤ, UnitAddTorus.mFourierCoeff (⇑(pgaussTorus n C hC)) m)
          = ∑' m : Fin n → ℤ, (((|C.det| : ℝ)⁻¹ : ℂ) *
              cexp (-(Real.pi : ℂ) * ↑(sqNormMat (C⁻¹)ᵀ (intToReal m)))) := by
            exact tsum_congr (fun m => hcoef m)
      _ = ((|C.det| : ℝ)⁻¹ : ℂ) * (∑' m : Fin n → ℤ,
              cexp (-(Real.pi : ℂ) * ↑(sqNormMat (C⁻¹)ᵀ (intToReal m)))) := by
            rw [tsum_mul_left]
  -- equality of complex values
  have hCeq : (∑' k : Fin n → ℤ, cgauss C (intToReal k)) =
      ((|C.det| : ℝ)⁻¹ : ℂ) * (∑' m : Fin n → ℤ,
        cexp (-(Real.pi : ℂ) * ↑(sqNormMat (C⁻¹)ᵀ (intToReal m)))) := by
    rw [← hvalsum]
    exact (hsum0.tsum_eq).symm
  -- convert to the real statement
  apply Complex.ofReal_inj.mp
  rw [Complex.ofReal_tsum]
  -- LHS: ∑ ↑(rgauss C (intToReal k)) = ∑ cgauss C (intToReal k)
  rw [show (∑' k : Fin n → ℤ, ((rgauss C (intToReal k) : ℂ))) =
      (∑' k : Fin n → ℤ, cgauss C (intToReal k)) by
    apply tsum_congr
    intro k
    exact (cgauss_eq_ofReal_rgauss C (intToReal k)).symm]
  rw [Complex.ofReal_mul]
  rw [Complex.ofReal_tsum]
  -- RHS second factor: ∑ ↑(rgauss M (intToReal m)) = ∑ cexp(-π·↑(sqNormMat M (intToReal m)))
  rw [show ((∑' m : Fin n → ℤ, (rgauss (C⁻¹).transpose (intToReal m) : ℂ))) =
      (∑' m : Fin n → ℤ, cexp (-(Real.pi : ℂ) * ↑(sqNormMat (C⁻¹)ᵀ (intToReal m)))) by
    apply tsum_congr
    intro m
    unfold rgauss
    rw [show (-(Real.pi : ℂ) * (sqNormMat (C⁻¹)ᵀ (intToReal m) : ℂ)) =
        ((-Real.pi * sqNormMat (C⁻¹)ᵀ (intToReal m) : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.ofReal_exp]]
  convert hCeq using 1
  rw [Complex.ofReal_inv]


end Commons.Analysis.Fourier