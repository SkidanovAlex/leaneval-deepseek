import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.Analysis.GaussianMeasure.integral_diag_image

namespace Commons.Analysis.GaussianMeasure

open MeasureTheory Filter
open scoped Real BigOperators Pointwise

noncomputable section

variable {n : ℕ}

/-- The diagonal scaling map `D_u y = WithLp.toLp 2 (fun i => exp (u i) * y i)`. -/
def diagMap (u : Fin n → ℝ) : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
  fun x => WithLp.toLp 2 (fun i => Real.exp (u i) * x i)

/-- The inverse of `diagMap u`. -/
def diagMapInv (u : Fin n → ℝ) : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
  fun x => WithLp.toLp 2 (fun i => (Real.exp (u i))⁻¹ * x i)

lemma continuous_diagMap (u : Fin n → ℝ) : Continuous (diagMap u) := by
  unfold diagMap; fun_prop

lemma continuous_diagMapInv (u : Fin n → ℝ) : Continuous (diagMapInv u) := by
  unfold diagMapInv; fun_prop

lemma diagMapInv_diagMap (u : Fin n → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    diagMapInv u (diagMap u x) = x := by
  apply WithLp.ofLp_injective 2
  ext i
  simp only [diagMapInv, diagMap, WithLp.ofLp_toLp]
  rw [← mul_assoc, inv_mul_cancel₀ (Real.exp_ne_zero (u i)), one_mul]

lemma diagMap_diagMapInv (u : Fin n → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    diagMap u (diagMapInv u x) = x := by
  apply WithLp.ofLp_injective 2
  ext i
  simp only [diagMapInv, diagMap, WithLp.ofLp_toLp]
  rw [← mul_assoc, mul_inv_cancel₀ (Real.exp_ne_zero (u i)), one_mul]

lemma diagMap_injective (u : Fin n → ℝ) : Function.Injective (diagMap u) :=
  Function.LeftInverse.injective (diagMapInv_diagMap u)

lemma diagMap_neg (u : Fin n → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    diagMap u (-x) = -diagMap u x := by
  apply WithLp.ofLp_injective 2
  ext i
  simp [diagMap]

lemma norm_diagMap_sq (u : Fin n → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖diagMap u x‖ ^ 2 = ∑ i, (Real.exp (u i) * x i) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

lemma isClosed_image_diagMap {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsClosed K)
    (u : Fin n → ℝ) : IsClosed (diagMap u '' K) := by
  have h : diagMap u '' K = diagMapInv u ⁻¹' K := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      show diagMapInv u (diagMap u y) ∈ K
      rw [diagMapInv_diagMap]
      exact hy
    · intro hx
      exact ⟨diagMapInv u x, hx, diagMap_diagMapInv u x⟩
  rw [h]
  exact hK.preimage (continuous_diagMapInv u)

/-- `diagMap u` as a linear map. -/
def diagLinearMap (u : Fin n → ℝ) : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun := diagMap u
  map_add' a b := by
    apply WithLp.ofLp_injective 2; ext i
    simp [diagMap, mul_add]
  map_smul' c a := by
    apply WithLp.ofLp_injective 2; ext i
    simp [diagMap, mul_assoc, mul_comm, mul_left_comm]

lemma diagLinearMap_apply (u : Fin n → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    diagLinearMap u x = diagMap u x := rfl

lemma convex_image_diagMap {K : Set (EuclideanSpace ℝ (Fin n))} (hK : Convex ℝ K)
    (u : Fin n → ℝ) : Convex ℝ (diagMap u '' K) :=
  hK.linear_image (diagLinearMap u)

lemma neg_image_diagMap {K : Set (EuclideanSpace ℝ (Fin n))} (h : -K = K) (u : Fin n → ℝ) :
    -(diagMap u '' K) = diagMap u '' K := by
  have hneg : ∀ y, y ∈ K → -y ∈ K := by
    intro y hy
    have h1 : -y ∈ (-K : Set (EuclideanSpace ℝ (Fin n))) := by
      refine Set.mem_neg.mpr ?_
      simpa using hy
    rwa [h] at h1
  ext x
  constructor
  · intro hx
    rw [Set.mem_neg] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    refine ⟨-y, hneg y hy, ?_⟩
    rw [diagMap_neg, hyx, neg_neg]
  · intro hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [Set.mem_neg]
    exact ⟨-y, hneg y hy, diagMap_neg u y⟩

/-! ### Change of variables: integrals over `diagMap w '' K` -/

private def diagExp (w : Fin n → ℝ) (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.exp (∑ i, w i) * Real.exp (-Real.pi * ∑ i, (Real.exp (w i) * y i) ^ 2)

private def diagD1 (w v : Fin n → ℝ) (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.exp (∑ i, w i) * Real.exp (-Real.pi * ∑ i, (Real.exp (w i) * y i) ^ 2) *
    ((∑ i, v i) - 2 * Real.pi * ∑ i, v i * Real.exp (2 * w i) * y i ^ 2)

private def diagD2 (w v : Fin n → ℝ) (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.exp (∑ i, w i) * Real.exp (-Real.pi * ∑ i, (Real.exp (w i) * y i) ^ 2) *
    (((∑ i, v i) - 2 * Real.pi * ∑ i, v i * Real.exp (2 * w i) * y i ^ 2) ^ 2
      - 4 * Real.pi * ∑ i, v i ^ 2 * Real.exp (2 * w i) * y i ^ 2)

private lemma exp_two_mul (x : ℝ) : Real.exp (2 * x) = Real.exp x ^ 2 := by
  rw [show (2 : ℝ) * x = (2 : ℕ) * x by norm_num, Real.exp_nat_mul]


private theorem integrable_one_add_sq_pow_mul_exp (c : ℝ) (hc : 0 < c) (M : ℕ) :
    Integrable (fun x : ℝ => (1 + x ^ 2) ^ M * Real.exp (-c * x ^ 2)) volume := by
  have hfun : (fun x : ℝ => (1 + x ^ 2) ^ M * Real.exp (-c * x ^ 2))
      = fun x : ℝ => ∑ m ∈ Finset.range (M + 1),
          (M.choose m : ℝ) * ((x ^ 2) ^ (M - m) * Real.exp (-c * x ^ 2)) := by
    funext x
    rw [add_pow]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    simp only [one_pow]
    ring
  rw [hfun]
  refine integrable_finsetSum _ (fun m hm => ?_)
  have h3 : Integrable (fun x : ℝ => x ^ ((2 * (M - m) : ℕ) : ℝ) * Real.exp (-c * x ^ 2))
      volume := integrable_rpow_mul_exp_neg_mul_sq hc (s := ((2 * (M - m) : ℕ) : ℝ))
        (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg _))
  have h2 : (fun x : ℝ => x ^ ((2 * (M - m) : ℕ) : ℝ) * Real.exp (-c * x ^ 2))
      = fun x : ℝ => (x ^ 2) ^ (M - m) * Real.exp (-c * x ^ 2) := by
    funext x
    rw [Real.rpow_natCast, ← pow_mul]
  rw [h2] at h3
  exact h3.const_mul _

private theorem integrable_prod_one_add_sq_pow_mul_exp {n : ℕ} {c : ℝ} (hc : 0 < c) (M : ℕ) :
    Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
      (∏ i, (1 + y i ^ 2) ^ M) * Real.exp (-c * ‖y‖ ^ 2)) volume := by
  rw [← (PiLp.volume_preserving_toLp (Fin n)).integrable_comp
    (g := fun y : EuclideanSpace ℝ (Fin n) =>
      (∏ i, (1 + y i ^ 2) ^ M) * Real.exp (-c * ‖y‖ ^ 2)) (by fun_prop)]
  change Integrable (fun y : Fin n → ℝ => (∏ i, (1 + y i ^ 2) ^ M) *
      Real.exp (-c * ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))‖ ^ 2)) volume
  have h2 : (fun y : Fin n → ℝ => (∏ i, (1 + y i ^ 2) ^ M) *
        Real.exp (-c * ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))‖ ^ 2))
      = fun y : Fin n → ℝ =>
          ∏ i, ((1 + y i ^ 2) ^ M * Real.exp (-c * y i ^ 2)) := by
    funext y
    rw [EuclideanSpace.real_norm_sq_eq]
    rw [Finset.mul_sum, Real.exp_sum Finset.univ (fun i => -c * y i ^ 2)]
    simp only [Finset.prod_mul_distrib]
  rw [h2]
  rw [show (volume : Measure (Fin n → ℝ)) = Measure.pi (fun _ => volume) from volume_pi]
  exact Integrable.fintype_prod (fun i => integrable_one_add_sq_pow_mul_exp c hc M)

private lemma hasDerivAt_diagExp_pointwise (w v : Fin n → ℝ) (y : EuclideanSpace ℝ (Fin n))
    (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (∑ i, (w i + s * v i)) *
        Real.exp (-Real.pi * ∑ i, (Real.exp (w i + s * v i) * y i) ^ 2))
      (Real.exp (∑ i, (w i + t * v i)) *
        Real.exp (-Real.pi * ∑ i, (Real.exp (w i + t * v i) * y i) ^ 2) *
        ((∑ i, v i) - 2 * Real.pi * ∑ i, v i * Real.exp (2 * (w i + t * v i)) * y i ^ 2))
      t := by
  have hA : HasDerivAt (fun s : ℝ => ∑ i, (w i + s * v i)) (∑ i, v i) t := by
    have h : ∀ s : ℝ, ∑ i, (w i + s * v i) = (∑ i, w i) + s * (∑ i, v i) := by
      intro s; rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [funext h]
    simpa using ((hasDerivAt_id t).mul_const (∑ i, v i)).const_add (∑ i, w i)
  have hB : HasDerivAt (fun s : ℝ => ∑ i, (Real.exp (w i + s * v i) * y i) ^ 2)
      (∑ i, 2 * (Real.exp (w i + t * v i) * y i) * (Real.exp (w i + t * v i) * v i * y i))
      t := by
    refine HasDerivAt.fun_sum (fun i hi => ?_)
    have h1 : HasDerivAt (fun s : ℝ => w i + s * v i) (v i) t := by
      simpa using ((hasDerivAt_id t).mul_const (v i)).const_add (w i)
    have h2 : HasDerivAt (fun s : ℝ => Real.exp (w i + s * v i) * y i)
        (Real.exp (w i + t * v i) * v i * y i) t := by
      simpa using (h1.exp.mul_const (y i))
    have hmul : HasDerivAt ((fun s : ℝ => Real.exp (w i + s * v i) * y i) *
        (fun s : ℝ => Real.exp (w i + s * v i) * y i))
        ((Real.exp (w i + t * v i) * v i * y i) * (Real.exp (w i + t * v i) * y i) +
          (Real.exp (w i + t * v i) * y i) * (Real.exp (w i + t * v i) * v i * y i)) t :=
      h2.mul h2
    have hfun : ((fun s : ℝ => Real.exp (w i + s * v i) * y i) *
        (fun s : ℝ => Real.exp (w i + s * v i) * y i))
        = fun s : ℝ => (Real.exp (w i + s * v i) * y i) ^ 2 := by
      funext s; simp [pow_two]
    rw [hfun] at hmul
    refine hmul.congr_deriv ?_
    ring
  have hkey : (∑ i, 2 * (Real.exp (w i + t * v i) * y i) *
        (Real.exp (w i + t * v i) * v i * y i))
      = 2 * ∑ i, v i * Real.exp (2 * (w i + t * v i)) * y i ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [exp_two_mul (w i + t * v i)]
    ring
  have hmain := (hA.exp).mul ((hB.const_mul (-Real.pi)).exp)
  rw [hkey] at hmain
  refine hmain.congr_deriv ?_
  ring

private lemma hasDerivAt_diagH_pointwise (w v : Fin n → ℝ) (y : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (∑ i, v i) - 2 * Real.pi * ∑ i, v i * Real.exp (2 * (w i + s * v i)) * y i ^ 2)
      (-(4 * Real.pi * ∑ i, v i ^ 2 * Real.exp (2 * (w i + t * v i)) * y i ^ 2)) t := by
  have hsum : HasDerivAt (fun s : ℝ => ∑ i, v i * Real.exp (2 * (w i + s * v i)) * y i ^ 2)
      (∑ i, (v i * (Real.exp (2 * (w i + t * v i)) * (2 * v i))) * y i ^ 2) t := by
    refine HasDerivAt.fun_sum (fun i hi => ?_)
    have h1 : HasDerivAt (fun s : ℝ => 2 * (w i + s * v i)) (2 * v i) t := by
      have heq : ∀ s : ℝ, 2 * (w i + s * v i) = 2 * w i + s * (2 * v i) := fun s => by ring
      rw [funext heq]
      simpa using ((hasDerivAt_id t).mul_const (2 * v i)).const_add (2 * w i)
    have h2 : HasDerivAt (fun s : ℝ => Real.exp (2 * (w i + s * v i)))
        (Real.exp (2 * (w i + t * v i)) * (2 * v i)) t := h1.exp
    exact (h2.const_mul (v i)).mul_const (y i ^ 2)
  have hkey : (∑ i, (v i * (Real.exp (2 * (w i + t * v i)) * (2 * v i))) * y i ^ 2)
      = 2 * ∑ i, v i ^ 2 * Real.exp (2 * (w i + t * v i)) * y i ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    ring
  have hmain := (hsum.const_mul (-2 * Real.pi)).const_add (∑ i, v i)
  rw [hkey] at hmain
  have hfun : (fun s : ℝ => ∑ i, v i + -2 * Real.pi * ∑ i, v i *
        Real.exp (2 * (w i + s * v i)) * y i ^ 2)
      = fun s : ℝ => (∑ i, v i) - 2 * Real.pi * ∑ i, v i *
        Real.exp (2 * (w i + s * v i)) * y i ^ 2 := by
    funext s; ring
  rw [hfun] at hmain
  refine hmain.congr_deriv ?_
  ring

private lemma continuous_diagExp (w : Fin n → ℝ) : Continuous (diagExp w) := by
  unfold diagExp; fun_prop

private lemma continuous_diagD1 (w v : Fin n → ℝ) : Continuous (diagD1 w v) := by
  unfold diagD1; fun_prop

private lemma continuous_diagD2 (w v : Fin n → ℝ) : Continuous (diagD2 w v) := by
  unfold diagD2; fun_prop

private lemma one_add_sum_le_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) : 1 + ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 + f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have hf' : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have h1 : 1 + ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 + f i) := ih hf'
      have h2 : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
      have h3 : 0 ≤ ∏ i ∈ s, (1 + f i) :=
        Finset.prod_nonneg (fun i hi => by linarith [hf' i hi])
      have h4 : 0 ≤ ∑ i ∈ s, f i := Finset.sum_nonneg (fun i hi => hf' i hi)
      have hP : 1 ≤ ∏ i ∈ s, (1 + f i) := by linarith
      have h5 : f a ≤ f a * ∏ i ∈ s, (1 + f i) := le_mul_of_one_le_right h2 hP
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      linarith

private lemma one_add_norm_sq_le_prod (y : EuclideanSpace ℝ (Fin n)) :
    1 + ‖y‖ ^ 2 ≤ ∏ i, (1 + y i ^ 2) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  exact one_add_sum_le_prod _ _ (fun i _ => sq_nonneg _)

private lemma prod_one_add_sq_one_le (y : EuclideanSpace ℝ (Fin n)) :
    1 ≤ ∏ i, (1 + y i ^ 2) := by
  have h := Finset.prod_le_prod (s := Finset.univ) (f := fun _ : Fin n => (1:ℝ))
    (g := fun i => 1 + y i ^ 2) (fun i _ => by norm_num) (fun i _ => by linarith [sq_nonneg (y i)])
  simpa using h

private def qS (w v : Fin n → ℝ) : ℝ := ∑ i, (|w i| + |v i|)
private def qV (v : Fin n → ℝ) : ℝ := ∑ i, |v i|
private def qE (w v : Fin n → ℝ) : ℝ := Real.exp (2 * qS w v)
private def qA (w v : Fin n → ℝ) : ℝ := Real.pi * Real.exp (-(2 * qS w v))
private def qK (w v : Fin n → ℝ) : ℝ := max 1 (max (qV v) (2 * Real.pi * qV v * qE w v))
private def qC (w v : Fin n → ℝ) : ℝ :=
  Real.exp (qS w v) * max 1 ((qK w v) ^ 2 + 4 * Real.pi * (qV v) ^ 2 * qE w v)
private def qMaj (a : ℝ) (M : ℕ) (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (∏ i, (1 + y i ^ 2) ^ M) * Real.exp (-a * ‖y‖ ^ 2)

private lemma exp_sum_le_exp_abs_sum (w v : Fin n → ℝ) (t : ℝ) (ht : |t| ≤ 1) :
    Real.exp (∑ i, (w i + t * v i)) ≤ Real.exp (qS w v) := by
  apply Real.exp_le_exp.mpr
  apply Finset.sum_le_sum
  intro i _
  have h1 : t * v i ≤ |v i| := by
    calc t * v i ≤ |t * v i| := le_abs_self _
      _ = |t| * |v i| := abs_mul t (v i)
      _ ≤ 1 * |v i| := by gcongr
      _ = |v i| := one_mul _
  linarith [le_abs_self (w i)]

private lemma exp_two_mul_le_qE (w v : Fin n → ℝ) (t : ℝ) (ht : |t| ≤ 1) (i : Fin n) :
    Real.exp (2 * (w i + t * v i)) ≤ qE w v := by
  apply Real.exp_le_exp.mpr
  have h1 : |w i| + |v i| ≤ qS w v := by
    rw [qS]
    exact Finset.single_le_sum (fun j _ => add_nonneg (abs_nonneg (w j)) (abs_nonneg (v j)))
      (Finset.mem_univ i)
  have h2 : |v i| ≤ qS w v := le_trans (le_add_of_nonneg_left (abs_nonneg _)) h1
  have h3 : w i ≤ |w i| := le_abs_self _
  have h4 : t * v i ≤ |t| * |v i| := by rw [← abs_mul]; exact le_abs_self _
  have h5 : |t| * |v i| ≤ |v i| := by
    calc |t| * |v i| ≤ 1 * |v i| := by gcongr
      _ = |v i| := one_mul _
  have h6 : w i + t * v i ≤ qS w v := by linarith
  linarith

private lemma qE_pos (w v : Fin n → ℝ) : 0 < qE w v := Real.exp_pos _

private lemma exp_weight_le (w v : Fin n → ℝ) (t : ℝ) (ht : |t| ≤ 1)
    (y : EuclideanSpace ℝ (Fin n)) :
    Real.exp (-Real.pi * ∑ i, (Real.exp (w i + t * v i) * y i) ^ 2)
      ≤ Real.exp (-(qA w v) * ‖y‖ ^ 2) := by
  rw [Real.exp_le_exp, EuclideanSpace.real_norm_sq_eq]
  have key : ∀ i, Real.exp (-(2 * qS w v)) * y i ^ 2
      ≤ (Real.exp (w i + t * v i) * y i) ^ 2 := by
    intro i
    have hle : Real.exp (-(2 * qS w v)) ≤ Real.exp (w i + t * v i) ^ 2 := by
      rw [← exp_two_mul]
      apply Real.exp_le_exp.mpr
      have h1 : |w i| + |v i| ≤ qS w v := by
        rw [qS]
        exact Finset.single_le_sum (fun j _ => add_nonneg (abs_nonneg (w j)) (abs_nonneg (v j)))
          (Finset.mem_univ i)
      have h2 : -(2 * qS w v) ≤ -(2 * (|w i| + |v i|)) := by linarith
      have h3 : -(2 * (|w i| + |v i|)) ≤ 2 * (w i + t * v i) := by
        have h4 : -(|w i|) ≤ w i := neg_abs_le _
        have h5 : -(|v i|) ≤ t * v i := by
          calc -(|v i|) = -(|v i|) := rfl
            _ ≤ t * v i := by
              have : t * v i ≥ -|t * v i| := neg_abs_le _
              rw [abs_mul] at this
              have : |t| * |v i| ≤ |v i| := by
                calc |t| * |v i| ≤ 1 * |v i| := by gcongr
                  _ = |v i| := one_mul _
              linarith
        linarith
      linarith
    calc Real.exp (-(2 * qS w v)) * y i ^ 2
        ≤ Real.exp (w i + t * v i) ^ 2 * y i ^ 2 :=
          mul_le_mul_of_nonneg_right hle (sq_nonneg _)
      _ = (Real.exp (w i + t * v i) * y i) ^ 2 := by rw [mul_pow]
  have hmain : qA w v * ∑ i, y i ^ 2
      ≤ Real.pi * ∑ i, (Real.exp (w i + t * v i) * y i) ^ 2 := by
    calc qA w v * ∑ i, y i ^ 2
        = Real.pi * ∑ i, Real.exp (-(2 * qS w v)) * y i ^ 2 := by
          rw [qA, Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ => by ring)
      _ ≤ Real.pi * ∑ i, (Real.exp (w i + t * v i) * y i) ^ 2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => key i)) Real.pi_pos.le
  linarith



private lemma sum_mul_sum_le {n : ℕ} (a b : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    ∑ i, a i * b i ≤ (∑ i, a i) * (∑ i, b i) := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  exact Finset.single_le_sum (fun j _ => mul_nonneg (ha i) (hb j)) (Finset.mem_univ i)

private lemma abs_h_le {n : ℕ} (w v : Fin n → ℝ) (t : ℝ) (ht : |t| ≤ 1)
    (y : EuclideanSpace ℝ (Fin n)) :
    |(∑ i, v i) - 2 * Real.pi * ∑ i, v i * Real.exp (2 * (w i + t * v i)) * y i ^ 2|
      ≤ qK w v * (1 + ‖y‖ ^ 2) := by
  have hV : |∑ i, v i| ≤ qV v := by
    rw [qV]; exact Finset.abs_sum_le_sum_abs _ _
  have hE : |∑ i, v i * Real.exp (2 * (w i + t * v i)) * y i ^ 2|
      ≤ qV v * qE w v * ‖y‖ ^ 2 := by
    calc |∑ i, v i * Real.exp (2 * (w i + t * v i)) * y i ^ 2|
        ≤ ∑ i, |v i * Real.exp (2 * (w i + t * v i)) * y i ^ 2| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |v i| * qE w v * y i ^ 2 := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg (sq_nonneg (y i))]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (exp_two_mul_le_qE w v t ht i) (abs_nonneg _))
            (sq_nonneg _)
      _ = qE w v * ∑ i, |v i| * y i ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ => by ring)
      _ ≤ qE w v * (qV v * ‖y‖ ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          rw [EuclideanSpace.real_norm_sq_eq, qV]
          exact sum_mul_sum_le _ _ (fun i => abs_nonneg _) (fun i => sq_nonneg _)
      _ = qV v * qE w v * ‖y‖ ^ 2 := by ring
  have hY : |2 * Real.pi * (∑ i, v i * Real.exp (2 * (w i + t * v i)) * y i ^ 2)|
      ≤ 2 * Real.pi * (qV v * qE w v * ‖y‖ ^ 2) := by
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
    exact mul_le_mul_of_nonneg_left hE (by positivity)
  have hmain : |(∑ i, v i) - 2 * Real.pi * ∑ i, v i * Real.exp (2 * (w i + t * v i)) * y i ^ 2|
      ≤ qV v + 2 * Real.pi * qV v * qE w v * ‖y‖ ^ 2 := by
    calc |(∑ i, v i) - 2 * Real.pi * ∑ i, v i * Real.exp (2 * (w i + t * v i)) * y i ^ 2|
        ≤ |∑ i, v i| +
            |2 * Real.pi * (∑ i, v i * Real.exp (2 * (w i + t * v i)) * y i ^ 2)| := by
          have := abs_sub_le (∑ i, v i) 0
            (2 * Real.pi * (∑ i, v i * Real.exp (2 * (w i + t * v i)) * y i ^ 2))
          simpa using this
      _ ≤ qV v + 2 * Real.pi * (qV v * qE w v * ‖y‖ ^ 2) := add_le_add hV hY
      _ = qV v + 2 * Real.pi * qV v * qE w v * ‖y‖ ^ 2 := by ring
  have hK1 : qV v ≤ qK w v := le_trans (le_max_left _ _) (le_max_right _ _)
  have hK2 : 2 * Real.pi * qV v * qE w v ≤ qK w v :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hsq : 0 ≤ ‖y‖ ^ 2 := sq_nonneg _
  have h1 : 1 ≤ 1 + ‖y‖ ^ 2 := by linarith
  nlinarith [hmain, hK1, hK2, hsq, mul_le_mul_of_nonneg_right hK2 hsq,
    mul_le_mul_of_nonneg_right hK1 (by positivity : (0:ℝ) ≤ 1 + ‖y‖ ^ 2)]

private lemma prod_one_add_sq_pow_eq (y : EuclideanSpace ℝ (Fin n)) (M : ℕ) :
    (∏ i, (1 + y i ^ 2) ^ M) = (∏ i, (1 + y i ^ 2)) ^ M :=
  Finset.prod_pow _ _ _

private lemma prod_one_add_sq_pow_one_le (y : EuclideanSpace ℝ (Fin n)) (M : ℕ) :
    1 ≤ ∏ i, (1 + y i ^ 2) ^ M := by
  rw [prod_one_add_sq_pow_eq]
  exact one_le_pow₀ (prod_one_add_sq_one_le y)

private lemma qC_one_le (w v : Fin n → ℝ) : 1 ≤ qC w v := by
  rw [qC]
  have h1 : (1:ℝ) ≤ Real.exp (qS w v) := Real.one_le_exp (Finset.sum_nonneg (by intro i _; positivity))
  nlinarith [h1, le_max_left (1:ℝ) (qK w v ^ 2 + 4 * Real.pi * qV v ^ 2 * qE w v)]

private lemma norm_diagExp_le (w v : Fin n → ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    ‖diagExp w y‖ ≤ qC w v * qMaj (qA w v) 2 y := by
  have h1 : Real.exp (∑ i, w i) ≤ Real.exp (qS w v) := by
    apply Real.exp_le_exp.mpr
    rw [qS]
    exact Finset.sum_le_sum (fun i _ => by
      linarith [le_abs_self (w i), abs_nonneg (v i)])
  have h2 : Real.exp (-Real.pi * ∑ i, (Real.exp (w i) * y i) ^ 2)
      ≤ Real.exp (-(qA w v) * ‖y‖ ^ 2) := by
    have h := exp_weight_le w v 0 (by norm_num) y
    simpa using h
  have hnorm : ‖diagExp w y‖ = Real.exp (∑ i, w i) *
      Real.exp (-Real.pi * ∑ i, (Real.exp (w i) * y i) ^ 2) := by
    rw [diagExp, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_pos (Real.exp_pos _)]
  rw [hnorm]
  have hC : Real.exp (qS w v) ≤ qC w v * ∏ i, (1 + y i ^ 2) ^ 2 := by
    have hP : 1 ≤ ∏ i, (1 + y i ^ 2) ^ 2 := prod_one_add_sq_pow_one_le y 2
    have h21 : 1 ≤ max (1:ℝ) (qK w v ^ 2 + 4 * Real.pi * qV v ^ 2 * qE w v) :=
      le_max_left _ _
    rw [qC]
    have ha : Real.exp (qS w v) ≤ Real.exp (qS w v) *
        max 1 (qK w v ^ 2 + 4 * Real.pi * qV v ^ 2 * qE w v) :=
      le_mul_of_one_le_right (Real.exp_pos _).le h21
    have hb : Real.exp (qS w v) * max 1 (qK w v ^ 2 + 4 * Real.pi * qV v ^ 2 * qE w v)
        ≤ Real.exp (qS w v) * max 1 (qK w v ^ 2 + 4 * Real.pi * qV v ^ 2 * qE w v)
          * ∏ i, (1 + y i ^ 2) ^ 2 :=
      le_mul_of_one_le_right (by positivity) hP
    linarith
  calc Real.exp (∑ i, w i) * Real.exp (-Real.pi * ∑ i, (Real.exp (w i) * y i) ^ 2)
      ≤ Real.exp (qS w v) * Real.exp (-(qA w v) * ‖y‖ ^ 2) :=
        mul_le_mul h1 h2 (Real.exp_pos _).le (Real.exp_pos _).le
    _ ≤ qC w v * ((∏ i, (1 + y i ^ 2) ^ 2) * Real.exp (-(qA w v) * ‖y‖ ^ 2)) := by
        have := mul_le_mul_of_nonneg_right hC (Real.exp_pos (-(qA w v) * ‖y‖ ^ 2)).le
        calc Real.exp (qS w v) * Real.exp (-(qA w v) * ‖y‖ ^ 2)
            ≤ (qC w v * ∏ i, (1 + y i ^ 2) ^ 2) * Real.exp (-(qA w v) * ‖y‖ ^ 2) := this
          _ = qC w v * ((∏ i, (1 + y i ^ 2) ^ 2) * Real.exp (-(qA w v) * ‖y‖ ^ 2)) := by ring
    _ = qC w v * qMaj (qA w v) 2 y := by rw [qMaj]

private lemma sum_sq_le_sq (v : Fin n → ℝ) : ∑ i, v i ^ 2 ≤ (∑ i, |v i|) ^ 2 := by
  have h : ∑ i, |v i| * |v i| ≤ (∑ i, |v i|) * (∑ i, |v i|) :=
    sum_mul_sum_le _ _ (fun i => abs_nonneg _) (fun i => abs_nonneg _)
  calc ∑ i, v i ^ 2 = ∑ i, |v i| * |v i| := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [← abs_mul, abs_of_nonneg (mul_self_nonneg (v i)), pow_two]
    _ ≤ (∑ i, |v i|) * (∑ i, |v i|) := h
    _ = (∑ i, |v i|) ^ 2 := by ring

private lemma qV_nonneg (v : Fin n → ℝ) : 0 ≤ qV v := by rw [qV]; positivity

private lemma qS_nonneg (w v : Fin n → ℝ) : 0 ≤ qS w v := by rw [qS]; positivity

private lemma qK_one_le (w v : Fin n → ℝ) : 1 ≤ qK w v := le_max_left _ _

private lemma qK_le_qC_factor (w v : Fin n → ℝ) :
    qK w v ≤ max 1 (qK w v ^ 2 + 4 * Real.pi * qV v ^ 2 * qE w v) := by
  have h1 : 1 ≤ qK w v := qK_one_le w v
  have h2 : qK w v ≤ qK w v ^ 2 := by nlinarith
  have h3 : qK w v ^ 2 ≤ qK w v ^ 2 + 4 * Real.pi * qV v ^ 2 * qE w v :=
    le_add_of_nonneg_right (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4)
      Real.pi_pos.le) (sq_nonneg (qV v))) (Real.exp_pos _).le)
  exact le_trans h2 (le_trans h3 (le_max_right _ _))

private lemma one_add_norm_sq_le_prod_sq (y : EuclideanSpace ℝ (Fin n)) :
    1 + ‖y‖ ^ 2 ≤ ∏ i, (1 + y i ^ 2) ^ 2 := by
  refine le_trans (one_add_norm_sq_le_prod y) ?_
  rw [prod_one_add_sq_pow_eq]
  have h := prod_one_add_sq_one_le y
  nlinarith

private lemma one_add_norm_sq_sq_le_prod_sq (y : EuclideanSpace ℝ (Fin n)) :
    (1 + ‖y‖ ^ 2) ^ 2 ≤ ∏ i, (1 + y i ^ 2) ^ 2 := by
  rw [prod_one_add_sq_pow_eq]
  exact pow_le_pow_left₀ (by positivity) (one_add_norm_sq_le_prod y) 2

private lemma norm_diagD1_le (w v : Fin n → ℝ) (t : ℝ) (ht : |t| ≤ 1)
    (y : EuclideanSpace ℝ (Fin n)) :
    ‖diagD1 (w + t • v) v y‖ ≤ qC w v * qMaj (qA w v) 2 y := by
  have h1 : Real.exp (∑ i, (w + t • v) i) ≤ Real.exp (qS w v) := exp_sum_le_exp_abs_sum w v t ht
  have h2 : Real.exp (-Real.pi * ∑ i, (Real.exp ((w + t • v) i) * y i) ^ 2)
      ≤ Real.exp (-(qA w v) * ‖y‖ ^ 2) := exp_weight_le w v t ht y
  have h3 : |(∑ i, v i) - 2 * Real.pi * ∑ i, v i * Real.exp (2 * ((w + t • v) i)) * y i ^ 2|
      ≤ qK w v * (1 + ‖y‖ ^ 2) := abs_h_le w v t ht y
  have hnorm : ‖diagD1 (w + t • v) v y‖ = Real.exp (∑ i, (w + t • v) i) *
      Real.exp (-Real.pi * ∑ i, (Real.exp ((w + t • v) i) * y i) ^ 2) *
      |(∑ i, v i) - 2 * Real.pi * ∑ i, v i * Real.exp (2 * ((w + t • v) i)) * y i ^ 2| := by
    rw [diagD1, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_pos (Real.exp_pos _)]
  rw [hnorm]
  have hkey : Real.exp (qS w v) * qK w v * (1 + ‖y‖ ^ 2)
      ≤ qC w v * ∏ i, (1 + y i ^ 2) ^ 2 := by
    rw [qC]
    have hP : 1 + ‖y‖ ^ 2 ≤ ∏ i, (1 + y i ^ 2) ^ 2 := one_add_norm_sq_le_prod_sq y
    have hM : qK w v ≤ max 1 (qK w v ^ 2 + 4 * Real.pi * qV v ^ 2 * qE w v) :=
      qK_le_qC_factor w v
    have ha : (0:ℝ) ≤ 1 + ‖y‖ ^ 2 := by positivity
    calc Real.exp (qS w v) * qK w v * (1 + ‖y‖ ^ 2)
        ≤ Real.exp (qS w v) * max 1 (qK w v ^ 2 + 4 * Real.pi * qV v ^ 2 * qE w v)
            * (1 + ‖y‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM (Real.exp_pos _).le) ha
      _ ≤ Real.exp (qS w v) * max 1 (qK w v ^ 2 + 4 * Real.pi * qV v ^ 2 * qE w v)
            * ∏ i, (1 + y i ^ 2) ^ 2 :=
          mul_le_mul_of_nonneg_left hP (by positivity)
  calc Real.exp (∑ i, (w + t • v) i) *
        Real.exp (-Real.pi * ∑ i, (Real.exp ((w + t • v) i) * y i) ^ 2) *
        |(∑ i, v i) - 2 * Real.pi * ∑ i, v i * Real.exp (2 * ((w + t • v) i)) * y i ^ 2|
      ≤ Real.exp (qS w v) * Real.exp (-(qA w v) * ‖y‖ ^ 2) * (qK w v * (1 + ‖y‖ ^ 2)) :=
        mul_le_mul (mul_le_mul h1 h2 (Real.exp_pos _).le (Real.exp_pos _).le) h3
          (abs_nonneg _) (by positivity)
    _ = Real.exp (qS w v) * qK w v * (1 + ‖y‖ ^ 2) * Real.exp (-(qA w v) * ‖y‖ ^ 2) := by ring
    _ ≤ qC w v * (∏ i, (1 + y i ^ 2) ^ 2) * Real.exp (-(qA w v) * ‖y‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hkey (Real.exp_pos _).le
    _ = qC w v * qMaj (qA w v) 2 y := by rw [qMaj]; ring

private lemma abs_sum_sq_exp_le (w v : Fin n → ℝ) (t : ℝ) (ht : |t| ≤ 1)
    (y : EuclideanSpace ℝ (Fin n)) :
    |∑ i, v i ^ 2 * Real.exp (2 * (w i + t * v i)) * y i ^ 2|
      ≤ qV v ^ 2 * qE w v * ‖y‖ ^ 2 := by
  have h2 : ∑ i, |v i ^ 2 * Real.exp (2 * (w i + t * v i)) * y i ^ 2|
      ≤ ∑ i, v i ^ 2 * qE w v * y i ^ 2 := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg (sq_nonneg (y i)),
      abs_of_nonneg (sq_nonneg (v i))]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (exp_two_mul_le_qE w v t ht i) (sq_nonneg _)) (sq_nonneg _)
  have h3 : ∑ i, v i ^ 2 * qE w v * y i ^ 2 = qE w v * ∑ i, v i ^ 2 * y i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have h4 : ∑ i, v i ^ 2 * y i ^ 2 ≤ (∑ i, v i ^ 2) * (∑ i, y i ^ 2) :=
    sum_mul_sum_le _ _ (fun i => sq_nonneg _) (fun i => sq_nonneg _)
  have h5 : ∑ i, v i ^ 2 ≤ qV v ^ 2 := sum_sq_le_sq v
  have h6 : (0:ℝ) ≤ ∑ i, y i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have h7 : ∑ i, v i ^ 2 * y i ^ 2 ≤ qV v ^ 2 * ‖y‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact le_trans h4 (mul_le_mul_of_nonneg_right h5 h6)
  calc |∑ i, v i ^ 2 * Real.exp (2 * (w i + t * v i)) * y i ^ 2|
      ≤ ∑ i, |v i ^ 2 * Real.exp (2 * (w i + t * v i)) * y i ^ 2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, v i ^ 2 * qE w v * y i ^ 2 := h2
    _ = qE w v * ∑ i, v i ^ 2 * y i ^ 2 := h3
    _ ≤ qE w v * (qV v ^ 2 * ‖y‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h7 (Real.exp_pos _).le
    _ = qV v ^ 2 * qE w v * ‖y‖ ^ 2 := by ring

private lemma norm_diagD2_le (w v : Fin n → ℝ) (t : ℝ) (ht : |t| ≤ 1)
    (y : EuclideanSpace ℝ (Fin n)) :
    ‖diagD2 (w + t • v) v y‖ ≤ qC w v * qMaj (qA w v) 2 y := by
  have h1 : Real.exp (∑ i, (w + t • v) i) ≤ Real.exp (qS w v) := exp_sum_le_exp_abs_sum w v t ht
  have h2 : Real.exp (-Real.pi * ∑ i, (Real.exp ((w + t • v) i) * y i) ^ 2)
      ≤ Real.exp (-(qA w v) * ‖y‖ ^ 2) := exp_weight_le w v t ht y
  have h3 : |(∑ i, v i) - 2 * Real.pi * ∑ i, v i * Real.exp (2 * ((w + t • v) i)) * y i ^ 2|
      ≤ qK w v * (1 + ‖y‖ ^ 2) := abs_h_le w v t ht y
  have h4 : |∑ i, v i ^ 2 * Real.exp (2 * ((w + t • v) i)) * y i ^ 2|
      ≤ qV v ^ 2 * qE w v * ‖y‖ ^ 2 := abs_sum_sq_exp_le w v t ht y
  have hnorm : ‖diagD2 (w + t • v) v y‖ = Real.exp (∑ i, (w + t • v) i) *
      Real.exp (-Real.pi * ∑ i, (Real.exp ((w + t • v) i) * y i) ^ 2) *
      |((∑ i, v i) - 2 * Real.pi * ∑ i, v i * Real.exp (2 * ((w + t • v) i)) * y i ^ 2) ^ 2
        - 4 * Real.pi * ∑ i, v i ^ 2 * Real.exp (2 * ((w + t • v) i)) * y i ^ 2| := by
    rw [diagD2, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_pos (Real.exp_pos _)]
  rw [hnorm]
  have h5 : |((∑ i, v i) - 2 * Real.pi * ∑ i, v i * Real.exp (2 * ((w + t • v) i)) * y i ^ 2) ^ 2
        - 4 * Real.pi * ∑ i, v i ^ 2 * Real.exp (2 * ((w + t • v) i)) * y i ^ 2|
      ≤ (qK w v * (1 + ‖y‖ ^ 2)) ^ 2 + 4 * Real.pi * (qV v ^ 2 * qE w v * ‖y‖ ^ 2) := by
    have hsq : ((∑ i, v i) - 2 * Real.pi * ∑ i, v i * Real.exp (2 * ((w + t • v) i)) * y i ^ 2) ^ 2
        = |(∑ i, v i) - 2 * Real.pi * ∑ i, v i * Real.exp (2 * ((w + t • v) i)) * y i ^ 2| ^ 2 :=
      (sq_abs _).symm
    have hT : |4 * Real.pi * (∑ i, v i ^ 2 * Real.exp (2 * ((w + t • v) i)) * y i ^ 2)|
        = 4 * Real.pi * |∑ i, v i ^ 2 * Real.exp (2 * ((w + t • v) i)) * y i ^ 2| := by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 4 * Real.pi)]
    calc |((∑ i, v i) - 2 * Real.pi * ∑ i, v i * Real.exp (2 * ((w + t • v) i)) * y i ^ 2) ^ 2
          - 4 * Real.pi * ∑ i, v i ^ 2 * Real.exp (2 * ((w + t • v) i)) * y i ^ 2|
        ≤ |((∑ i, v i) - 2 * Real.pi * ∑ i, v i * Real.exp (2 * ((w + t • v) i)) * y i ^ 2) ^ 2|
          + |4 * Real.pi * (∑ i, v i ^ 2 * Real.exp (2 * ((w + t • v) i)) * y i ^ 2)| := by
          have := abs_sub_le
            (((∑ i, v i) - 2 * Real.pi * ∑ i, v i * Real.exp (2 * ((w + t • v) i)) * y i ^ 2) ^ 2)
            0 (4 * Real.pi * (∑ i, v i ^ 2 * Real.exp (2 * ((w + t • v) i)) * y i ^ 2))
          simpa using this
      _ ≤ (qK w v * (1 + ‖y‖ ^ 2)) ^ 2 + 4 * Real.pi * (qV v ^ 2 * qE w v * ‖y‖ ^ 2) := by
          rw [hsq, hT, abs_of_nonneg (sq_nonneg _)]
          exact add_le_add (pow_le_pow_left₀ (abs_nonneg _) h3 2)
            (mul_le_mul_of_nonneg_left h4 (by positivity))
  have hkey : Real.exp (qS w v) * ((qK w v * (1 + ‖y‖ ^ 2)) ^ 2
      + 4 * Real.pi * (qV v ^ 2 * qE w v * ‖y‖ ^ 2))
      ≤ qC w v * ∏ i, (1 + y i ^ 2) ^ 2 := by
    rw [qC]
    have hP : (1 + ‖y‖ ^ 2) ^ 2 ≤ ∏ i, (1 + y i ^ 2) ^ 2 := one_add_norm_sq_sq_le_prod_sq y
    have hP0 : (0:ℝ) ≤ ∏ i, (1 + y i ^ 2) ^ 2 := le_trans zero_le_one (prod_one_add_sq_pow_one_le y 2)
    have hM : qK w v ^ 2 + 4 * Real.pi * qV v ^ 2 * qE w v
        ≤ max 1 (qK w v ^ 2 + 4 * Real.pi * qV v ^ 2 * qE w v) := le_max_right _ _
    have hsq : 0 ≤ ‖y‖ ^ 2 := sq_nonneg _
    have hsq2 : ‖y‖ ^ 2 ≤ (1 + ‖y‖ ^ 2) ^ 2 := by nlinarith
    have hstep1 : (qK w v * (1 + ‖y‖ ^ 2)) ^ 2 + 4 * Real.pi * (qV v ^ 2 * qE w v * ‖y‖ ^ 2)
        ≤ (qK w v ^ 2 + 4 * Real.pi * qV v ^ 2 * qE w v) * (1 + ‖y‖ ^ 2) ^ 2 := by
      have h4a : 4 * Real.pi * (qV v ^ 2 * qE w v * ‖y‖ ^ 2)
          ≤ 4 * Real.pi * qV v ^ 2 * qE w v * (1 + ‖y‖ ^ 2) ^ 2 := by
        have hc : 0 ≤ 4 * Real.pi * qV v ^ 2 * qE w v :=
          mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) Real.pi_pos.le)
            (sq_nonneg (qV v))) (Real.exp_pos _).le
        have := mul_le_mul_of_nonneg_left hsq2 hc
        calc 4 * Real.pi * (qV v ^ 2 * qE w v * ‖y‖ ^ 2)
            = 4 * Real.pi * qV v ^ 2 * qE w v * ‖y‖ ^ 2 := by ring
          _ ≤ 4 * Real.pi * qV v ^ 2 * qE w v * (1 + ‖y‖ ^ 2) ^ 2 := this
      nlinarith [h4a, sq_nonneg (qK w v), sq_nonneg (1 + ‖y‖ ^ 2), hsq2,
        sq_nonneg (qK w v * (1 + ‖y‖ ^ 2))]
    have hstep2 : (qK w v ^ 2 + 4 * Real.pi * qV v ^ 2 * qE w v) * (1 + ‖y‖ ^ 2) ^ 2
        ≤ max 1 (qK w v ^ 2 + 4 * Real.pi * qV v ^ 2 * qE w v) * ∏ i, (1 + y i ^ 2) ^ 2 := by
      refine mul_le_mul hM ?_ (sq_nonneg _) (le_trans zero_le_one (le_max_left _ _))
      exact hP
    have hpos : 0 ≤ Real.exp (qS w v) := (Real.exp_pos _).le
    calc Real.exp (qS w v) * ((qK w v * (1 + ‖y‖ ^ 2)) ^ 2
          + 4 * Real.pi * (qV v ^ 2 * qE w v * ‖y‖ ^ 2))
        ≤ Real.exp (qS w v) * ((qK w v ^ 2 + 4 * Real.pi * qV v ^ 2 * qE w v)
            * (1 + ‖y‖ ^ 2) ^ 2) := mul_le_mul_of_nonneg_left hstep1 hpos
      _ ≤ Real.exp (qS w v) * (max 1 (qK w v ^ 2 + 4 * Real.pi * qV v ^ 2 * qE w v)
            * ∏ i, (1 + y i ^ 2) ^ 2) := mul_le_mul_of_nonneg_left hstep2 hpos
      _ = Real.exp (qS w v) * max 1 (qK w v ^ 2 + 4 * Real.pi * qV v ^ 2 * qE w v)
            * ∏ i, (1 + y i ^ 2) ^ 2 := by ring
  calc Real.exp (∑ i, (w + t • v) i) *
        Real.exp (-Real.pi * ∑ i, (Real.exp ((w + t • v) i) * y i) ^ 2) *
        |((∑ i, v i) - 2 * Real.pi * ∑ i, v i * Real.exp (2 * ((w + t • v) i)) * y i ^ 2) ^ 2
          - 4 * Real.pi * ∑ i, v i ^ 2 * Real.exp (2 * ((w + t • v) i)) * y i ^ 2|
      ≤ Real.exp (qS w v) * Real.exp (-(qA w v) * ‖y‖ ^ 2) *
        ((qK w v * (1 + ‖y‖ ^ 2)) ^ 2 + 4 * Real.pi * (qV v ^ 2 * qE w v * ‖y‖ ^ 2)) :=
        mul_le_mul (mul_le_mul h1 h2 (Real.exp_pos _).le (Real.exp_pos _).le) h5 (abs_nonneg _)
          (by positivity)
    _ = Real.exp (qS w v) * ((qK w v * (1 + ‖y‖ ^ 2)) ^ 2
          + 4 * Real.pi * (qV v ^ 2 * qE w v * ‖y‖ ^ 2)) * Real.exp (-(qA w v) * ‖y‖ ^ 2) := by
        ring
    _ ≤ qC w v * (∏ i, (1 + y i ^ 2) ^ 2) * Real.exp (-(qA w v) * ‖y‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hkey (Real.exp_pos _).le
    _ = qC w v * qMaj (qA w v) 2 y := by rw [qMaj]; ring

private lemma qA_pos (w v : Fin n → ℝ) : 0 < qA w v := by
  rw [qA]; positivity

private lemma qMaj_integrable (w v : Fin n → ℝ) (M : ℕ) :
    Integrable (fun y : EuclideanSpace ℝ (Fin n) => qMaj (qA w v) M y) volume :=
  integrable_prod_one_add_sq_pow_mul_exp (qA_pos w v) M

private lemma hasDerivAt_diagExp_diagD1_pointwise (w v : Fin n → ℝ)
    (y : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => diagExp (w + s • v) y) (diagD1 (w + t • v) v y) t := by
  simpa only [diagExp, diagD1, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    using hasDerivAt_diagExp_pointwise w v y t

private lemma hasDerivAt_diagD1_diagD2_pointwise (w v : Fin n → ℝ)
    (y : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => diagD1 (w + s • v) v y) (diagD2 (w + t • v) v y) t := by
  have hΦ := hasDerivAt_diagExp_pointwise w v y t
  have hh := hasDerivAt_diagH_pointwise w v y t
  have hmain : HasDerivAt (fun s : ℝ => Real.exp (∑ i, (w i + s * v i)) *
      Real.exp (-Real.pi * ∑ i, (Real.exp (w i + s * v i) * y i) ^ 2) *
      ((∑ i, v i) - 2 * Real.pi * ∑ i, v i * Real.exp (2 * (w i + s * v i)) * y i ^ 2))
      (Real.exp (∑ i, (w i + t * v i)) *
        Real.exp (-Real.pi * ∑ i, (Real.exp (w i + t * v i) * y i) ^ 2) *
        (((∑ i, v i) - 2 * Real.pi * ∑ i, v i * Real.exp (2 * (w i + t * v i)) * y i ^ 2) ^ 2
          - 4 * Real.pi * ∑ i, v i ^ 2 * Real.exp (2 * (w i + t * v i)) * y i ^ 2)) t := by
    have h := hΦ.mul hh
    refine h.congr_deriv ?_
    ring
  simpa only [diagD1, diagD2, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hmain

private theorem hasDerivAt_integral_diagExp {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (w v : Fin n → ℝ) :
    HasDerivAt (fun t : ℝ => ∫ y in K, diagExp (w + t • v) y) (∫ y in K, diagD1 w v y) 0 := by
  have hbound : Integrable (fun y : EuclideanSpace ℝ (Fin n) => qC w v * qMaj (qA w v) 2 y)
      (volume.restrict K) :=
    ((qMaj_integrable w v 2).const_mul _).integrableOn
  have hFint : Integrable (fun y : EuclideanSpace ℝ (Fin n) => diagExp (w + (0:ℝ) • v) y)
      (volume.restrict K) := by
    refine Integrable.mono' hbound ?_ (Eventually.of_forall (fun y => ?_))
    · exact (continuous_diagExp (w + (0:ℝ) • v)).aestronglyMeasurable
    · simpa only [zero_smul, add_zero] using norm_diagExp_le w v y
  have hF'meas : AEStronglyMeasurable (fun y : EuclideanSpace ℝ (Fin n) => diagD1 w v y)
      (volume.restrict K) := (continuous_diagD1 w v).aestronglyMeasurable
  obtain ⟨-, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict K) (s := Metric.ball (0:ℝ) 1) (x₀ := 0)
    (bound := fun y : EuclideanSpace ℝ (Fin n) => qC w v * qMaj (qA w v) 2 y)
    (F := fun (t : ℝ) (y : EuclideanSpace ℝ (Fin n)) => diagExp (w + t • v) y)
    (F' := fun (t : ℝ) (y : EuclideanSpace ℝ (Fin n)) => diagD1 (w + t • v) v y)
    (Metric.ball_mem_nhds 0 one_pos)
    (by filter_upwards with t
        exact (continuous_diagExp (w + t • v)).aestronglyMeasurable)
    hFint
    (by simpa only [zero_smul, add_zero] using hF'meas)
    (by
      refine Eventually.of_forall (fun y t ht => ?_)
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
      exact norm_diagD1_le w v t (le_of_lt ht) y)
    hbound
    (Eventually.of_forall (fun y t _ => hasDerivAt_diagExp_diagD1_pointwise w v y t))
  simpa using hderiv

private theorem hasDerivAt_integral_diagD1 {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (w v : Fin n → ℝ) :
    HasDerivAt (fun t : ℝ => ∫ y in K, diagD1 (w + t • v) v y) (∫ y in K, diagD2 w v y) 0 := by
  have hbound : Integrable (fun y : EuclideanSpace ℝ (Fin n) => qC w v * qMaj (qA w v) 2 y)
      (volume.restrict K) :=
    ((qMaj_integrable w v 2).const_mul _).integrableOn
  have hFint : Integrable (fun y : EuclideanSpace ℝ (Fin n) => diagD1 (w + (0:ℝ) • v) v y)
      (volume.restrict K) := by
    refine Integrable.mono' hbound ?_ (Eventually.of_forall (fun y => ?_))
    · exact (continuous_diagD1 (w + (0:ℝ) • v) v).aestronglyMeasurable
    · simpa only [zero_smul, add_zero] using norm_diagD1_le w v (0:ℝ) (by norm_num) y
  have hF'meas : AEStronglyMeasurable (fun y : EuclideanSpace ℝ (Fin n) => diagD2 w v y)
      (volume.restrict K) := (continuous_diagD2 w v).aestronglyMeasurable
  obtain ⟨-, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict K) (s := Metric.ball (0:ℝ) 1) (x₀ := 0)
    (bound := fun y : EuclideanSpace ℝ (Fin n) => qC w v * qMaj (qA w v) 2 y)
    (F := fun (t : ℝ) (y : EuclideanSpace ℝ (Fin n)) => diagD1 (w + t • v) v y)
    (F' := fun (t : ℝ) (y : EuclideanSpace ℝ (Fin n)) => diagD2 (w + t • v) v y)
    (Metric.ball_mem_nhds 0 one_pos)
    (by filter_upwards with t
        exact (continuous_diagD1 (w + t • v) v).aestronglyMeasurable)
    hFint
    (by simpa only [zero_smul, add_zero] using hF'meas)
    (by
      refine Eventually.of_forall (fun y t ht => ?_)
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
      exact norm_diagD2_le w v t (le_of_lt ht) y)
    hbound
    (Eventually.of_forall (fun y t _ => hasDerivAt_diagD1_diagD2_pointwise w v y t))
  simpa using hderiv

private theorem integral_diag_image_gen {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : MeasurableSet K) (u : Fin n → ℝ) (g : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫ x in diagMap u '' K, g x) = ∫ y in K, Real.exp (∑ i, u i) * g (diagMap u y) := by
  classical
  let e : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] (Fin n → ℝ) := WithLp.linearEquiv 2 ℝ (Fin n → ℝ)
  let L' : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    LinearMap.pi (fun i => (LinearMap.mulLeft ℝ (Real.exp (u i))).comp (LinearMap.proj i))
  let L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (e.symm : (Fin n → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).comp
      (L'.comp (e : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] (Fin n → ℝ)))
  have hL : ∀ x : EuclideanSpace ℝ (Fin n), L x = diagMap u x := by
    intro x
    have h1 : e x = (fun i => x i) := by
      ext i
      show (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)) x i = x i
      simp [WithLp.linearEquiv_apply]
    have h2 : ∀ v : Fin n → ℝ, e.symm v = WithLp.toLp 2 v := by
      intro v
      apply WithLp.ofLp_injective 2
      show ((WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm v).ofLp = v
      simp [WithLp.linearEquiv_symm_apply]
    show e.symm (L' (e x)) = diagMap u x
    rw [h2, h1]
    rfl
  have hdet : LinearMap.det L = Real.exp (∑ i, u i) := by
    have hdet' : LinearMap.det L' = Real.exp (∑ i, u i) := by
      rw [LinearMap.det_pi, Real.exp_sum]
      simp
    rw [← hdet']
    exact LinearMap.det_conj L' e.symm
  let A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) := L.toContinuousLinearMap
  have hA : (⇑A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) = ⇑L :=
    LinearMap.coe_toContinuousLinearMap' (f := L)
  have hAD : ⇑A = diagMap u := by
    funext x
    rw [congrFun hA x]
    exact hL x
  have hAdet : A.det = Real.exp (∑ i, u i) := by
    rw [show A.det = LinearMap.det L from LinearMap.det_toContinuousLinearMap (f := L), hdet]
  have hInj : Set.InjOn (diagMap u) K := (diagMap_injective u).injOn
  have hf' : ∀ x ∈ K, HasFDerivWithinAt (diagMap u) A K x := by
    intro x _
    have h := A.hasFDerivAt (x := x)
    rw [hAD] at h
    exact h.hasFDerivWithinAt
  rw [integral_image_eq_integral_abs_det_fderiv_smul (μ := volume) hK hf' hInj g]
  apply setIntegral_congr_fun hK
  intro y _
  beta_reduce
  rw [hAdet, abs_of_pos (Real.exp_pos _), smul_eq_mul]

private lemma integral_diagExp_mul {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : MeasurableSet K) (w : Fin n → ℝ) (Ψ : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫ y in K, diagExp w y * Ψ (diagMap w y))
      = ∫ x in diagMap w '' K, Ψ x * Real.exp (-Real.pi * ‖x‖ ^ 2) := by
  rw [integral_diag_image_gen K hK w (fun x => Ψ x * Real.exp (-Real.pi * ‖x‖ ^ 2))]
  apply setIntegral_congr_fun hK
  intro y _
  simp only [diagExp, norm_diagMap_sq]
  ring

private lemma hasFDerivAt_quadform (v : Fin n → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => ∑ i, v i * z i ^ 2)
      (∑ i, (2 * v i * x i) • (PiLp.proj 2 (fun _ : Fin n => ℝ) i) :
        EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) x := by
  have hsum : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => ∑ i, v i * z i ^ 2)
      ((∑ i, v i • (((2 : ℕ) • x.ofLp i ^ (2 - 1)) •
        (PiLp.proj 2 (fun _ : Fin n => ℝ) i))) :
        EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) x := by
    refine HasFDerivAt.fun_sum (u := Finset.univ)
      (A := fun i (z : EuclideanSpace ℝ (Fin n)) => v i * z i ^ 2)
      (A' := fun i => (v i • (((2 : ℕ) • x.ofLp i ^ (2 - 1)) •
        (PiLp.proj 2 (fun _ : Fin n => ℝ) i)) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
      (fun i _ => ?_)
    have h1 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => z.ofLp i)
        (PiLp.proj 2 (fun _ : Fin n => ℝ) i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) x :=
      PiLp.hasFDerivAt_apply (E := fun _ : Fin n => ℝ) 2 x i
    exact (h1.pow 2).const_mul (v i)
  have heq : (∑ i, v i • (((2 : ℕ) • x.ofLp i ^ (2 - 1)) •
        (PiLp.proj 2 (fun _ : Fin n => ℝ) i)) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      = (∑ i, (2 * v i * x i) • (PiLp.proj 2 (fun _ : Fin n => ℝ) i) :
        EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    ext y
    simp only [smul_apply, PiLp.proj_apply, smul_eq_mul]
    ring
  rw [heq] at hsum
  exact hsum

private lemma fderiv_quadform (v : Fin n → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun z : EuclideanSpace ℝ (Fin n) => ∑ i, v i * z i ^ 2) x
      = ∑ i, (2 * v i * x i) • (PiLp.proj 2 (fun _ : Fin n => ℝ) i) :=
  (hasFDerivAt_quadform v x).fderiv

private lemma fderiv_quadform_eq_toDual (v : Fin n → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun z : EuclideanSpace ℝ (Fin n) => ∑ i, v i * z i ^ 2) x
      = InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))
          (WithLp.toLp 2 (fun i => 2 * v i * x i)) := by
  rw [fderiv_quadform]
  ext y
  rw [InnerProductSpace.toDual_apply_apply]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, PiLp.proj_apply,
    smul_eq_mul]
  rw [PiLp.inner_apply]
  simp only [WithLp.ofLp_toLp, RCLike.inner_apply, conj_trivial, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

private lemma norm_fderiv_quadform_sq (v : Fin n → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖fderiv ℝ (fun z : EuclideanSpace ℝ (Fin n) => ∑ i, v i * z i ^ 2) x‖ ^ 2
      = 4 * ∑ i, v i ^ 2 * x i ^ 2 := by
  rw [fderiv_quadform_eq_toDual, LinearIsometryEquiv.norm_map, EuclideanSpace.real_norm_sq_eq]
  simp only [WithLp.ofLp_toLp]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring


private lemma core_algebra {Z0 Z1 Z2 Z3 F1 F2 G Sv : ℝ} (hZ0 : 0 < Z0)
    (hZ1 : Z1 = Sv * Z0 - 2 * Real.pi * F1)
    (hZ2 : Z2 = Sv ^ 2 * Z0 - 4 * Real.pi * Sv * F1 + 4 * Real.pi ^ 2 * F2)
    (hG : G = 4 * Z3)
    (hpoin : F2 / Z0 - (F1 / Z0) ^ 2 ≤ (1 / (4 * Real.pi)) * (G / Z0)) :
    Z0 * (Z2 - 4 * Real.pi * Z3) - Z1 ^ 2 ≤ 0 := by
  have h2 : F2 / Z0 - (F1 / Z0) ^ 2 = (Z0 * F2 - F1 ^ 2) / Z0 ^ 2 := by
    field_simp
  rw [h2, div_le_iff₀ (by positivity : (0:ℝ) < Z0^2)] at hpoin
  have h3 : (1 / (4 * Real.pi)) * (G / Z0) * Z0 ^ 2 = (1 / (4 * Real.pi)) * (Z0 * G) := by
    field_simp
  rw [h3] at hpoin
  rw [hG] at hpoin
  have hmul := mul_le_mul_of_nonneg_left hpoin (by positivity : (0:ℝ) ≤ 4 * Real.pi ^ 2)
  have hsimp : 4 * Real.pi ^ 2 * ((1 / (4 * Real.pi)) * (Z0 * (4 * Z3))) = 4 * Real.pi * Z0 * Z3 := by
    field_simp
  rw [hsimp] at hmul
  rw [hZ1, hZ2]
  nlinarith [hmul, Real.pi_pos, hZ0]



private lemma integrable_of_bound_gauss {P : EuclideanSpace ℝ (Fin n) → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hPc : Continuous P) (hP : ∀ y, |P y| ≤ C * (1 + ‖y‖ ^ 2) ^ 2) :
    Integrable (fun y : EuclideanSpace ℝ (Fin n) => P y * Real.exp (-Real.pi * ‖y‖ ^ 2)) := by
  refine Integrable.mono'
    ((integrable_prod_one_add_sq_pow_mul_exp (c := Real.pi) Real.pi_pos 2).const_mul C) ?_ ?_
  · exact (hPc.mul (by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin n) =>
      Real.exp (-Real.pi * ‖y‖ ^ 2))).aestronglyMeasurable
  · filter_upwards with y
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hE : 0 ≤ Real.exp (-Real.pi * ‖y‖ ^ 2) := (Real.exp_pos _).le
    have h1 := mul_le_mul_of_nonneg_left (one_add_norm_sq_sq_le_prod_sq y) hC
    have h2 := mul_le_mul_of_nonneg_right h1 hE
    calc |P y| * Real.exp (-Real.pi * ‖y‖ ^ 2)
        ≤ C * (1 + ‖y‖ ^ 2) ^ 2 * Real.exp (-Real.pi * ‖y‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (hP y) hE
      _ ≤ C * (∏ i, (1 + y i ^ 2) ^ 2) * Real.exp (-Real.pi * ‖y‖ ^ 2) := h2
      _ = C * ((∏ i, (1 + y i ^ 2) ^ 2) * Real.exp (-Real.pi * ‖y‖ ^ 2)) := by ring

private lemma abs_sum_sq_mul_le (v x : Fin n → ℝ) :
    |∑ i, v i * x i ^ 2| ≤ (∑ i, |v i|) * (∑ i, x i ^ 2) := by
  calc |∑ i, v i * x i ^ 2| ≤ ∑ i, |v i * x i ^ 2| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |v i| * x i ^ 2 := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [abs_mul, abs_of_nonneg (sq_nonneg (x i))]
    _ ≤ (∑ i, |v i|) * (∑ i, x i ^ 2) :=
        sum_mul_sum_le _ _ (fun i => abs_nonneg _) (fun i => sq_nonneg _)

private lemma abs_sum_sq_sq_mul_le (v x : Fin n → ℝ) :
    |∑ i, v i ^ 2 * x i ^ 2| ≤ (∑ i, v i ^ 2) * (∑ i, x i ^ 2) := by
  calc |∑ i, v i ^ 2 * x i ^ 2| ≤ ∑ i, |v i ^ 2 * x i ^ 2| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, v i ^ 2 * x i ^ 2 := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [abs_mul, abs_of_nonneg (sq_nonneg (v i)), abs_of_nonneg (sq_nonneg (x i))]
    _ ≤ (∑ i, v i ^ 2) * (∑ i, x i ^ 2) :=
        sum_mul_sum_le _ _ (fun i => sq_nonneg _) (fun i => sq_nonneg _)


private lemma norm_sq_le_sq_one_add (y : EuclideanSpace ℝ (Fin n)) :
    ‖y‖ ^ 2 ≤ (1 + ‖y‖ ^ 2) ^ 2 := by
  nlinarith [sq_nonneg (‖y‖ ^ 2)]

private lemma integrable_quad_gauss (v : Fin n → ℝ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      (∑ i, v i * x i ^ 2) * Real.exp (-Real.pi * ‖x‖ ^ 2)) := by
  refine integrable_of_bound_gauss (C := ∑ i, |v i|)
    (Finset.sum_nonneg (fun i _ => abs_nonneg _)) (by fun_prop) (fun y => ?_)
  have h1 := abs_sum_sq_mul_le v y
  rw [← EuclideanSpace.real_norm_sq_eq y] at h1
  calc |∑ i, v i * y i ^ 2| ≤ (∑ i, |v i|) * ‖y‖ ^ 2 := h1
    _ ≤ (∑ i, |v i|) * (1 + ‖y‖ ^ 2) ^ 2 :=
        mul_le_mul_of_nonneg_left (norm_sq_le_sq_one_add y)
          (Finset.sum_nonneg (fun i _ => abs_nonneg _))

private lemma integrable_quad_sq_gauss (v : Fin n → ℝ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      (∑ i, v i * x i ^ 2) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)) := by
  refine integrable_of_bound_gauss (C := (∑ i, |v i|) ^ 2) (by positivity) (by fun_prop) (fun y => ?_)
  have h1 := abs_sum_sq_mul_le v y
  rw [← EuclideanSpace.real_norm_sq_eq y] at h1
  have h2 : |(∑ i, v i * y i ^ 2) ^ 2| ≤ ((∑ i, |v i|) * ‖y‖ ^ 2) ^ 2 := by
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have h3 : ((∑ i, |v i|) * ‖y‖ ^ 2) ^ 2 ≤ (∑ i, |v i|) ^ 2 * (1 + ‖y‖ ^ 2) ^ 2 := by
    rw [mul_pow]
    have h4 : ‖y‖ ^ 2 ≤ 1 + ‖y‖ ^ 2 := by nlinarith [sq_nonneg ‖y‖]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h4 2) (by positivity)
  exact le_trans h2 h3

private lemma integrable_fderiv_quad_gauss (v : Fin n → ℝ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      ‖fderiv ℝ (fun x : EuclideanSpace ℝ (Fin n) => ∑ i, v i * x i ^ 2) x‖ ^ 2
        * Real.exp (-Real.pi * ‖x‖ ^ 2)) := by
  have hg3 : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      (∑ i, v i ^ 2 * x i ^ 2) * Real.exp (-Real.pi * ‖x‖ ^ 2)) := by
    refine integrable_of_bound_gauss (C := ∑ i, v i ^ 2) (by positivity) (by fun_prop) (fun y => ?_)
    have h1 := abs_sum_sq_sq_mul_le v y
    rw [← EuclideanSpace.real_norm_sq_eq y] at h1
    calc |∑ i, v i ^ 2 * y i ^ 2| ≤ (∑ i, v i ^ 2) * ‖y‖ ^ 2 := h1
      _ ≤ (∑ i, v i ^ 2) * (1 + ‖y‖ ^ 2) ^ 2 :=
          mul_le_mul_of_nonneg_left (norm_sq_le_sq_one_add y) (by positivity)
  refine (hg3.const_mul 4).congr (Eventually.of_forall (fun x => ?_))
  show 4 * ((∑ i, v i ^ 2 * x.ofLp i ^ 2) * Real.exp (-Real.pi * ‖x‖ ^ 2))
    = ‖fderiv ℝ (fun z : EuclideanSpace ℝ (Fin n) => ∑ i, v i * z.ofLp i ^ 2) x‖ ^ 2
      * Real.exp (-Real.pi * ‖x‖ ^ 2)
  rw [norm_fderiv_quadform_sq]
  ring

private theorem core_ineq {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K)
    (w v : Fin n → ℝ)
    (hpoin : (∫ x in diagMap w '' K, (∑ i, v i * x i ^ 2) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2))
          / (∫ x in diagMap w '' K, Real.exp (-Real.pi * ‖x‖ ^ 2))
        - ((∫ x in diagMap w '' K, (∑ i, v i * x i ^ 2) * Real.exp (-Real.pi * ‖x‖ ^ 2))
            / (∫ x in diagMap w '' K, Real.exp (-Real.pi * ‖x‖ ^ 2))) ^ 2
      ≤ (1 / (4 * Real.pi)) *
          ((∫ x in diagMap w '' K, ‖fderiv ℝ (fun x : EuclideanSpace ℝ (Fin n) => ∑ i, v i * x i ^ 2) x‖ ^ 2
              * Real.exp (-Real.pi * ‖x‖ ^ 2))
            / (∫ x in diagMap w '' K, Real.exp (-Real.pi * ‖x‖ ^ 2))))
    (hpos : 0 < ∫ x in diagMap w '' K, Real.exp (-Real.pi * ‖x‖ ^ 2)) :
    (∫ y in K, diagExp w y) * (∫ y in K, diagD2 w v y) - (∫ y in K, diagD1 w v y) ^ 2 ≤ 0 := by
  have hEw_cont : Continuous fun x : EuclideanSpace ℝ (Fin n) => Real.exp (-Real.pi * ‖x‖ ^ 2) := by
    fun_prop
  -- basic integrability of the Gaussian weight
  have hEw_int : Integrable (fun x : EuclideanSpace ℝ (Fin n) => Real.exp (-Real.pi * ‖x‖ ^ 2)) := by
    have h := integrable_of_bound_gauss (P := fun _ : EuclideanSpace ℝ (Fin n) => (1:ℝ))
      (C := 1) zero_le_one continuous_const (fun y => by
        rw [abs_one, one_mul]
        have : (1:ℝ) ≤ (1 + ‖y‖ ^ 2) ^ 2 := by nlinarith [sq_nonneg (‖y‖ ^ 2)]
        exact this)
    simpa using h
  -- substitution identities
  have hZ : (∫ y in K, diagExp w y) = ∫ x in diagMap w '' K, Real.exp (-Real.pi * ‖x‖ ^ 2) := by
    simpa using (integral_diagExp_mul K hK w (fun _ => (1 : ℝ)))
  have hsum1 : ∀ y : EuclideanSpace ℝ (Fin n),
      (∑ i, v i * Real.exp (2 * w i) * y i ^ 2)
        = ∑ i, v i * (Real.exp (w i) * y i) ^ 2 := by
    intro y
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [exp_two_mul (w i)]
    ring
  have hZ1 : (∫ y in K, diagD1 w v y)
      = ∫ x in diagMap w '' K, ((∑ i, v i) - 2 * Real.pi * ∑ i, v i * x i ^ 2)
          * Real.exp (-Real.pi * ‖x‖ ^ 2) := by
    have hpt : (∫ y in K, diagD1 w v y) = ∫ y in K, diagExp w y *
        ((∑ i, v i) - 2 * Real.pi * ∑ i, v i * (diagMap w y) i ^ 2) := by
      apply setIntegral_congr_fun hK
      intro y _
      simp only [diagD1, diagExp, diagMap, WithLp.ofLp_toLp]
      rw [hsum1 y]
    rw [hpt, integral_diagExp_mul K hK w
      (fun x => (∑ i, v i) - 2 * Real.pi * ∑ i, v i * x i ^ 2)]
  have hsum2 : ∀ y : EuclideanSpace ℝ (Fin n),
      (∑ i, v i ^ 2 * Real.exp (2 * w i) * y i ^ 2)
        = ∑ i, v i ^ 2 * (Real.exp (w i) * y i) ^ 2 := by
    intro y
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [exp_two_mul (w i)]
    ring
  have hZ3 : (∫ y in K, diagExp w y * (∑ i, v i ^ 2 * Real.exp (2 * w i) * y i ^ 2))
      = ∫ x in diagMap w '' K, (∑ i, v i ^ 2 * x i ^ 2) * Real.exp (-Real.pi * ‖x‖ ^ 2) := by
    have hpt : (∫ y in K, diagExp w y * (∑ i, v i ^ 2 * Real.exp (2 * w i) * y i ^ 2))
        = ∫ y in K, diagExp w y * (∑ i, v i ^ 2 * (diagMap w y) i ^ 2) := by
      apply setIntegral_congr_fun hK
      intro y _
      simp only [diagExp, diagMap, WithLp.ofLp_toLp]
      rw [hsum2 y]
    rw [hpt, integral_diagExp_mul K hK w (fun x => ∑ i, v i ^ 2 * x i ^ 2)]
  have hZ2 : (∫ y in K, diagExp w y * ((∑ i, v i) - 2 * Real.pi * ∑ i, v i * Real.exp (2 * w i) * y i ^ 2) ^ 2)
      = ∫ x in diagMap w '' K, ((∑ i, v i) - 2 * Real.pi * ∑ i, v i * x i ^ 2) ^ 2
          * Real.exp (-Real.pi * ‖x‖ ^ 2) := by
    have hpt : (∫ y in K, diagExp w y *
          ((∑ i, v i) - 2 * Real.pi * ∑ i, v i * Real.exp (2 * w i) * y i ^ 2) ^ 2)
        = ∫ y in K, diagExp w y *
            ((∑ i, v i) - 2 * Real.pi * ∑ i, v i * (diagMap w y) i ^ 2) ^ 2 := by
      apply setIntegral_congr_fun hK
      intro y _
      simp only [diagExp, diagMap, WithLp.ofLp_toLp]
      rw [hsum1 y]
    rw [hpt, integral_diagExp_mul K hK w
      (fun x => ((∑ i, v i) - 2 * Real.pi * ∑ i, v i * x i ^ 2) ^ 2)]
  have hAmeas : MeasurableSet (diagMap w '' K) := by
    have h : diagMap w '' K = diagMapInv w ⁻¹' K := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        show diagMapInv w (diagMap w y) ∈ K
        rw [diagMapInv_diagMap]
        exact hy
      · intro hx
        exact ⟨diagMapInv w x, hx, diagMap_diagMapInv w x⟩
    rw [h]
    exact hK.preimage (continuous_diagMapInv w).measurable
  have hsv_nonneg : (0:ℝ) ≤ ∑ i, |v i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hnorm_le : ∀ y : EuclideanSpace ℝ (Fin n), ‖y‖ ^ 2 ≤ (1 + ‖y‖ ^ 2) ^ 2 := by
    intro y; nlinarith [sq_nonneg (‖y‖ ^ 2)]
  have hf_int := integrable_quad_gauss v
  have hf2_int := integrable_quad_sq_gauss v
  have hg3_int : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      (∑ i, v i ^ 2 * x i ^ 2) * Real.exp (-Real.pi * ‖x‖ ^ 2)) := by
    refine integrable_of_bound_gauss (C := ∑ i, v i ^ 2) (by positivity) (by fun_prop) (fun y => ?_)
    have h1 := abs_sum_sq_sq_mul_le v y
    rw [← EuclideanSpace.real_norm_sq_eq y] at h1
    calc |∑ i, v i ^ 2 * y i ^ 2| ≤ (∑ i, v i ^ 2) * ‖y‖ ^ 2 := h1
      _ ≤ (∑ i, v i ^ 2) * (1 + ‖y‖ ^ 2) ^ 2 := mul_le_mul_of_nonneg_left (hnorm_le y) (by positivity)
  have hg1_int : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      ((∑ i, v i) - 2 * Real.pi * ∑ i, v i * x i ^ 2) * Real.exp (-Real.pi * ‖x‖ ^ 2)) := by
    refine integrable_of_bound_gauss (C := |∑ i, v i| + 2 * Real.pi * ∑ i, |v i|)
      (by positivity) (by fun_prop) (fun y => ?_)
    have h1 := abs_sum_sq_mul_le v y
    rw [← EuclideanSpace.real_norm_sq_eq y] at h1
    have h2 : |(∑ i, v i) - 2 * Real.pi * ∑ i, v i * y i ^ 2|
        ≤ |∑ i, v i| + 2 * Real.pi * ((∑ i, |v i|) * ‖y‖ ^ 2) := by
      calc |(∑ i, v i) - 2 * Real.pi * ∑ i, v i * y i ^ 2|
          ≤ |∑ i, v i| + |2 * Real.pi * (∑ i, v i * y i ^ 2)| := by
            have := abs_sub_le (∑ i, v i) 0 (2 * Real.pi * (∑ i, v i * y i ^ 2))
            simpa using this
        _ = |∑ i, v i| + 2 * Real.pi * |∑ i, v i * y i ^ 2| := by
            rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
        _ ≤ |∑ i, v i| + 2 * Real.pi * ((∑ i, |v i|) * ‖y‖ ^ 2) := by
            have := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 2 * Real.pi)
            linarith
    have h4 : |∑ i, v i| + 2 * Real.pi * ((∑ i, |v i|) * ‖y‖ ^ 2)
        ≤ (|∑ i, v i| + 2 * Real.pi * ∑ i, |v i|) * (1 + ‖y‖ ^ 2) ^ 2 := by
      have h5 := hnorm_le y
      have h6 : (1:ℝ) ≤ (1 + ‖y‖ ^ 2) ^ 2 := by nlinarith [sq_nonneg (‖y‖ ^ 2)]
      have h7 : |∑ i, v i| ≤ |∑ i, v i| * (1 + ‖y‖ ^ 2) ^ 2 :=
        le_mul_of_one_le_right (abs_nonneg _) h6
      have h8 : 2 * Real.pi * ((∑ i, |v i|) * ‖y‖ ^ 2)
          ≤ 2 * Real.pi * (∑ i, |v i|) * (1 + ‖y‖ ^ 2) ^ 2 := by
        have hb : 0 ≤ 2 * Real.pi * ∑ i, |v i| := by positivity
        have hb2 := mul_le_mul_of_nonneg_left h5 hb
        calc 2 * Real.pi * ((∑ i, |v i|) * ‖y‖ ^ 2)
            = (2 * Real.pi * ∑ i, |v i|) * ‖y‖ ^ 2 := by ring
          _ ≤ (2 * Real.pi * ∑ i, |v i|) * (1 + ‖y‖ ^ 2) ^ 2 := hb2
      calc |∑ i, v i| + 2 * Real.pi * ((∑ i, |v i|) * ‖y‖ ^ 2)
          ≤ |∑ i, v i| * (1 + ‖y‖ ^ 2) ^ 2
            + 2 * Real.pi * (∑ i, |v i|) * (1 + ‖y‖ ^ 2) ^ 2 := add_le_add h7 h8
        _ = (|∑ i, v i| + 2 * Real.pi * ∑ i, |v i|) * (1 + ‖y‖ ^ 2) ^ 2 := by ring
    exact le_trans h2 h4
  have hg1sq_int : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      ((∑ i, v i) - 2 * Real.pi * ∑ i, v i * x i ^ 2) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)) := by
    refine integrable_of_bound_gauss (C := (|∑ i, v i| + 2 * Real.pi * ∑ i, |v i|) ^ 2)
      (by positivity) (by fun_prop) (fun y => ?_)
    have h1 := abs_sum_sq_mul_le v y
    rw [← EuclideanSpace.real_norm_sq_eq y] at h1
    have h2 : |((∑ i, v i) - 2 * Real.pi * ∑ i, v i * y i ^ 2) ^ 2|
        ≤ (|∑ i, v i| + 2 * Real.pi * ((∑ i, |v i|) * ‖y‖ ^ 2)) ^ 2 := by
      rw [abs_of_nonneg (sq_nonneg _)]
      rw [show ((∑ i, v i) - 2 * Real.pi * ∑ i, v i * y i ^ 2) ^ 2
          = |(∑ i, v i) - 2 * Real.pi * ∑ i, v i * y i ^ 2| ^ 2 from (sq_abs _).symm]
      apply pow_le_pow_left₀ (abs_nonneg _)
      calc |(∑ i, v i) - 2 * Real.pi * ∑ i, v i * y i ^ 2|
          ≤ |∑ i, v i| + |2 * Real.pi * (∑ i, v i * y i ^ 2)| := by
            have := abs_sub_le (∑ i, v i) 0 (2 * Real.pi * (∑ i, v i * y i ^ 2))
            simpa using this
        _ = |∑ i, v i| + 2 * Real.pi * |∑ i, v i * y i ^ 2| := by
            rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
        _ ≤ |∑ i, v i| + 2 * Real.pi * ((∑ i, |v i|) * ‖y‖ ^ 2) := by
            have := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 2 * Real.pi)
            linarith
    have h4 : (|∑ i, v i| + 2 * Real.pi * ((∑ i, |v i|) * ‖y‖ ^ 2)) ^ 2
        ≤ (|∑ i, v i| + 2 * Real.pi * ∑ i, |v i|) ^ 2 * (1 + ‖y‖ ^ 2) ^ 2 := by
      have h5 := hnorm_le y
      have h6 : 0 ≤ |∑ i, v i| + 2 * Real.pi * ∑ i, |v i| := by positivity
      have h7 : |∑ i, v i| + 2 * Real.pi * ((∑ i, |v i|) * ‖y‖ ^ 2)
          ≤ (|∑ i, v i| + 2 * Real.pi * ∑ i, |v i|) * (1 + ‖y‖ ^ 2) := by
        have h6 : (1:ℝ) ≤ 1 + ‖y‖ ^ 2 := by nlinarith [sq_nonneg ‖y‖]
        have h8 : |∑ i, v i| ≤ |∑ i, v i| * (1 + ‖y‖ ^ 2) :=
          le_mul_of_one_le_right (abs_nonneg _) h6
        have h9 : 2 * Real.pi * ((∑ i, |v i|) * ‖y‖ ^ 2)
            ≤ 2 * Real.pi * (∑ i, |v i|) * (1 + ‖y‖ ^ 2) := by
          have hb : 0 ≤ 2 * Real.pi * ∑ i, |v i| := by positivity
          have h5b : ‖y‖ ^ 2 ≤ 1 + ‖y‖ ^ 2 := by nlinarith [sq_nonneg ‖y‖]
          have hb2 := mul_le_mul_of_nonneg_left h5b hb
          calc 2 * Real.pi * ((∑ i, |v i|) * ‖y‖ ^ 2)
              = (2 * Real.pi * ∑ i, |v i|) * ‖y‖ ^ 2 := by ring
            _ ≤ (2 * Real.pi * ∑ i, |v i|) * (1 + ‖y‖ ^ 2) := hb2
        calc |∑ i, v i| + 2 * Real.pi * ((∑ i, |v i|) * ‖y‖ ^ 2)
            ≤ |∑ i, v i| * (1 + ‖y‖ ^ 2)
              + 2 * Real.pi * (∑ i, |v i|) * (1 + ‖y‖ ^ 2) := add_le_add h8 h9
          _ = (|∑ i, v i| + 2 * Real.pi * ∑ i, |v i|) * (1 + ‖y‖ ^ 2) := by ring
      calc (|∑ i, v i| + 2 * Real.pi * ((∑ i, |v i|) * ‖y‖ ^ 2)) ^ 2
          ≤ ((|∑ i, v i| + 2 * Real.pi * ∑ i, |v i|) * (1 + ‖y‖ ^ 2)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) h7 2
        _ ≤ (|∑ i, v i| + 2 * Real.pi * ∑ i, |v i|) ^ 2 * (1 + ‖y‖ ^ 2) ^ 2 := by
            rw [mul_pow]
    exact le_trans h2 h4
  have hG_int := integrable_fderiv_quad_gauss v
  have hlin1 : (∫ x in diagMap w '' K, ((∑ i, v i) - 2 * Real.pi * ∑ i, v i * x i ^ 2)
        * Real.exp (-Real.pi * ‖x‖ ^ 2))
      = (∑ i, v i) * (∫ x in diagMap w '' K, Real.exp (-Real.pi * ‖x‖ ^ 2))
        - 2 * Real.pi * (∫ x in diagMap w '' K, (∑ i, v i * x i ^ 2)
            * Real.exp (-Real.pi * ‖x‖ ^ 2)) := by
    have hpt : ∀ x : EuclideanSpace ℝ (Fin n),
        ((∑ i, v i) - 2 * Real.pi * ∑ i, v i * x i ^ 2) * Real.exp (-Real.pi * ‖x‖ ^ 2)
          = (∑ i, v i) * Real.exp (-Real.pi * ‖x‖ ^ 2)
            - 2 * Real.pi * ((∑ i, v i * x i ^ 2) * Real.exp (-Real.pi * ‖x‖ ^ 2)) := by
      intro x; ring
    have e1 : IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) =>
        (∑ i, v i) * Real.exp (-Real.pi * ‖x‖ ^ 2)) (diagMap w '' K) :=
      hEw_int.integrableOn.const_mul _
    have e2 : IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) =>
        2 * Real.pi * ((∑ i, v i * x i ^ 2) * Real.exp (-Real.pi * ‖x‖ ^ 2)))
        (diagMap w '' K) := hf_int.integrableOn.const_mul _
    rw [setIntegral_congr_fun hAmeas (fun x _ => hpt x)]
    rw [integral_sub e1 e2, integral_const_mul, integral_const_mul]
  have hlin2 : (∫ x in diagMap w '' K, ((∑ i, v i) - 2 * Real.pi * ∑ i, v i * x i ^ 2) ^ 2
        * Real.exp (-Real.pi * ‖x‖ ^ 2))
      = (∑ i, v i) ^ 2 * (∫ x in diagMap w '' K, Real.exp (-Real.pi * ‖x‖ ^ 2))
        - 4 * Real.pi * (∑ i, v i) * (∫ x in diagMap w '' K, (∑ i, v i * x i ^ 2)
            * Real.exp (-Real.pi * ‖x‖ ^ 2))
        + 4 * Real.pi ^ 2 * (∫ x in diagMap w '' K, (∑ i, v i * x i ^ 2) ^ 2
            * Real.exp (-Real.pi * ‖x‖ ^ 2)) := by
    have hpt : ∀ x : EuclideanSpace ℝ (Fin n),
        ((∑ i, v i) - 2 * Real.pi * ∑ i, v i * x i ^ 2) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)
          = (∑ i, v i) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)
            - 4 * Real.pi * (∑ i, v i) * ((∑ i, v i * x i ^ 2) * Real.exp (-Real.pi * ‖x‖ ^ 2))
            + 4 * Real.pi ^ 2 * ((∑ i, v i * x i ^ 2) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)) := by
      intro x; ring
    have e1 : IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) =>
        (∑ i, v i) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)) (diagMap w '' K) :=
      hEw_int.integrableOn.const_mul _
    have e2 : IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) =>
        4 * Real.pi * (∑ i, v i) * ((∑ i, v i * x i ^ 2) * Real.exp (-Real.pi * ‖x‖ ^ 2)))
        (diagMap w '' K) := hf_int.integrableOn.const_mul _
    have e3 : IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) =>
        4 * Real.pi ^ 2 * ((∑ i, v i * x i ^ 2) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)))
        (diagMap w '' K) := hf2_int.integrableOn.const_mul _
    rw [setIntegral_congr_fun hAmeas (fun x _ => hpt x)]
    have e12 : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
        (∑ i, v i) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)
          - 4 * Real.pi * (∑ i, v i) * ((∑ i, v i * x i ^ 2) * Real.exp (-Real.pi * ‖x‖ ^ 2)))
        (volume.restrict (diagMap w '' K)) := e1.sub e2
    have hsum := integral_add (f := fun x : EuclideanSpace ℝ (Fin n) =>
          (∑ i, v i) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)
            - 4 * Real.pi * (∑ i, v i) * ((∑ i, v i * x i ^ 2) * Real.exp (-Real.pi * ‖x‖ ^ 2)))
      (g := fun x : EuclideanSpace ℝ (Fin n) =>
          4 * Real.pi ^ 2 * ((∑ i, v i * x i ^ 2) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)))
      e12 e3
    rw [hsum]
    have hsub := integral_sub (f := fun x : EuclideanSpace ℝ (Fin n) =>
          (∑ i, v i) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2))
      (g := fun x : EuclideanSpace ℝ (Fin n) =>
          4 * Real.pi * (∑ i, v i) * ((∑ i, v i * x i ^ 2) * Real.exp (-Real.pi * ‖x‖ ^ 2)))
      e1 e2
    rw [hsub, integral_const_mul, integral_const_mul, integral_const_mul]
  have hG_lin : (∫ x in diagMap w '' K, ‖fderiv ℝ
        (fun x : EuclideanSpace ℝ (Fin n) => ∑ i, v i * x i ^ 2) x‖ ^ 2
        * Real.exp (-Real.pi * ‖x‖ ^ 2))
      = 4 * (∫ x in diagMap w '' K, (∑ i, v i ^ 2 * x i ^ 2)
          * Real.exp (-Real.pi * ‖x‖ ^ 2)) := by
    have hpt : ∀ x : EuclideanSpace ℝ (Fin n),
        ‖fderiv ℝ (fun x : EuclideanSpace ℝ (Fin n) => ∑ i, v i * x i ^ 2) x‖ ^ 2
          * Real.exp (-Real.pi * ‖x‖ ^ 2)
        = 4 * ((∑ i, v i ^ 2 * x i ^ 2) * Real.exp (-Real.pi * ‖x‖ ^ 2)) := by
      intro x
      rw [norm_fderiv_quadform_sq]
      ring
    rw [setIntegral_congr_fun hAmeas (fun x _ => hpt x), integral_const_mul]
  have hZ2' : (∫ y in K, diagD2 w v y)
      = ∫ x in diagMap w '' K, (((∑ i, v i) - 2 * Real.pi * ∑ i, v i * x i ^ 2) ^ 2
          - 4 * Real.pi * (∑ i, v i ^ 2 * x i ^ 2)) * Real.exp (-Real.pi * ‖x‖ ^ 2) := by
    have hpt : (∫ y in K, diagD2 w v y) = ∫ y in K, diagExp w y *
        (((∑ i, v i) - 2 * Real.pi * ∑ i, v i * (diagMap w y) i ^ 2) ^ 2
          - 4 * Real.pi * (∑ i, v i ^ 2 * (diagMap w y) i ^ 2)) := by
      apply setIntegral_congr_fun hK
      intro y _
      simp only [diagD2, diagExp, diagMap, WithLp.ofLp_toLp]
      rw [hsum1 y, hsum2 y]
    rw [hpt, integral_diagExp_mul K hK w
      (fun x => ((∑ i, v i) - 2 * Real.pi * ∑ i, v i * x i ^ 2) ^ 2
        - 4 * Real.pi * (∑ i, v i ^ 2 * x i ^ 2))]
  have hsplit : (∫ x in diagMap w '' K, (((∑ i, v i) - 2 * Real.pi * ∑ i, v i * x i ^ 2) ^ 2
          - 4 * Real.pi * (∑ i, v i ^ 2 * x i ^ 2)) * Real.exp (-Real.pi * ‖x‖ ^ 2))
      = (∫ x in diagMap w '' K, ((∑ i, v i) - 2 * Real.pi * ∑ i, v i * x i ^ 2) ^ 2
          * Real.exp (-Real.pi * ‖x‖ ^ 2))
        - 4 * Real.pi * (∫ x in diagMap w '' K, (∑ i, v i ^ 2 * x i ^ 2)
            * Real.exp (-Real.pi * ‖x‖ ^ 2)) := by
    have hpt : ∀ x : EuclideanSpace ℝ (Fin n),
        (((∑ i, v i) - 2 * Real.pi * ∑ i, v i * x i ^ 2) ^ 2
          - 4 * Real.pi * (∑ i, v i ^ 2 * x i ^ 2)) * Real.exp (-Real.pi * ‖x‖ ^ 2)
          = ((∑ i, v i) - 2 * Real.pi * ∑ i, v i * x i ^ 2) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)
            - 4 * Real.pi * ((∑ i, v i ^ 2 * x i ^ 2) * Real.exp (-Real.pi * ‖x‖ ^ 2)) := by
      intro x; ring
    rw [setIntegral_congr_fun hAmeas (fun x _ => hpt x)]
    rw [integral_sub hg1sq_int.integrableOn (hg3_int.integrableOn.const_mul _),
      integral_const_mul]
  rw [hZ, hZ1, hZ2', hsplit]
  exact core_algebra hpos hlin1 hlin2 hG_lin hpoin


private lemma integral_diagMap_closure {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hKc : Convex ℝ K) (u : Fin n → ℝ) :
    (∫ x in diagMap u '' K, Real.exp (-Real.pi * ‖x‖ ^ 2))
      = ∫ x in diagMap u '' closure K, Real.exp (-Real.pi * ‖x‖ ^ 2) := by
  have hnull : volume (diagMap u '' frontier K) = 0 := by
    have h := MeasureTheory.Measure.addHaar_image_linearMap (μ := volume) (diagLinearMap u) (frontier K)
    rw [hKc.addHaar_frontier volume, mul_zero] at h
    have hfun : (⇑(diagLinearMap u) : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        = diagMap u := funext fun x => diagLinearMap_apply u x
    rwa [hfun] at h
  have hset : diagMap u '' closure K = (diagMap u '' K) ∪ (diagMap u '' frontier K) := by
    rw [closure_eq_self_union_frontier, Set.image_union]
  have hae : (diagMap u '' K) =ᵐ[volume] (diagMap u '' closure K) := by
    rw [MeasureTheory.ae_eq_set]
    constructor
    · have h0 : (diagMap u '' K) \ (diagMap u '' closure K) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro x ⟨hx, hx'⟩
        exact hx' (Set.image_mono subset_closure hx)
      rw [h0, measure_empty]
    · have hsub : (diagMap u '' closure K) \ (diagMap u '' K) ⊆ diagMap u '' frontier K := by
        rw [hset]
        rintro x ⟨hx, hx'⟩
        rcases hx with hx | hx
        · exact absurd hx hx'
        · exact hx
      exact measure_mono_null hsub hnull
  rw [Measure.restrict_congr_set hae]

private lemma closure_neg_eq {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (h : -K = K) :
    -(closure K) = closure K := by
  have himg : ∀ S : Set (EuclideanSpace ℝ (Fin n)),
      (Homeomorph.neg (EuclideanSpace ℝ (Fin n))) '' S = -S := by
    intro S
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Set.mem_neg]
      simpa using hy
    · intro hz
      rw [Set.mem_neg] at hz
      exact ⟨-z, hz, by simp⟩
  have h2 := (Homeomorph.neg (EuclideanSpace ℝ (Fin n))).image_closure K
  rw [himg, himg] at h2
  rw [h2, h]

private lemma det_diagLinearMap_ne_zero {n : ℕ} (u : Fin n → ℝ) :
    LinearMap.det (diagLinearMap u) ≠ 0 := by
  intro hdet
  rw [LinearMap.det_eq_zero_iff_ker_ne_bot] at hdet
  apply hdet
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hx0 : diagLinearMap u x = 0 := hx
  have hx1 : diagMap u x = diagMap u 0 := by
    have h1 : diagMap u x = 0 := by simpa only [diagLinearMap_apply] using hx0
    have h2 : diagMap u 0 = 0 := by
      simpa only [diagLinearMap_apply] using (map_zero (diagLinearMap u))
    rw [h1, h2]
  exact diagMap_injective u hx1

private lemma measurableSet_image_diagMap {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (u : Fin n → ℝ) : MeasurableSet (diagMap u '' K) := by
  have h : diagMap u '' K = diagMapInv u ⁻¹' K := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      show diagMapInv u (diagMap u y) ∈ K
      rw [diagMapInv_diagMap]
      exact hy
    · intro hx
      exact ⟨diagMapInv u x, hx, diagMap_diagMapInv u x⟩
  rw [h]
  exact hK.preimage (continuous_diagMapInv u).measurable


private lemma integral_diag_image_diagMap {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : MeasurableSet K) (u : Fin n → ℝ) :
    (∫ x in diagMap u '' K, Real.exp (-Real.pi * ‖x‖ ^ 2)) = ∫ y in K, diagExp u y :=
  integral_diag_image K hK u

private lemma hasDerivAt_of_comp_add {f : ℝ → ℝ} {f' t : ℝ}
    (h : HasDerivAt (fun s : ℝ => f (t + s)) f' 0) : HasDerivAt f f' t := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero] at h ⊢
  simpa using h

theorem B_conj_of_even_poincare
    (H : ∀ {m : ℕ} (A : Set (EuclideanSpace ℝ (Fin m))),
        Convex ℝ A → (∀ x, x ∈ A ↔ -x ∈ A) → MeasurableSet A →
        0 < ∫ x in A, Real.exp (-Real.pi * ‖x‖ ^ 2) →
        ∀ f : EuclideanSpace ℝ (Fin m) → ℝ, ContDiff ℝ 1 f → (∀ x, f (-x) = f x) →
        IntegrableOn (fun x => f x ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)) A →
        IntegrableOn (fun x => ‖fderiv ℝ f x‖ ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)) A →
        (∫ x in A, f x ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2))
            / (∫ x in A, Real.exp (-Real.pi * ‖x‖ ^ 2))
          - ((∫ x in A, f x * Real.exp (-Real.pi * ‖x‖ ^ 2))
              / (∫ x in A, Real.exp (-Real.pi * ‖x‖ ^ 2))) ^ 2
        ≤ (1 / (4 * Real.pi)) *
            ((∫ x in A, ‖fderiv ℝ f x‖ ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2))
              / (∫ x in A, Real.exp (-Real.pi * ‖x‖ ^ 2))))
    {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hKcvx : Convex ℝ K)
    (hKsymm : (-K : Set (EuclideanSpace ℝ (Fin n))) = K)
    (a b : Fin n → ℝ) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    (∫ x in (fun x : EuclideanSpace ℝ (Fin n) =>
        WithLp.toLp 2 (fun i => Real.exp (a i) * x i)) '' K,
        Real.exp (-Real.pi * ‖x‖ ^ 2)) ^ lam
      * (∫ x in (fun x : EuclideanSpace ℝ (Fin n) =>
        WithLp.toLp 2 (fun i => Real.exp (b i) * x i)) '' K,
        Real.exp (-Real.pi * ‖x‖ ^ 2)) ^ (1 - lam)
      ≤ ∫ x in (fun x : EuclideanSpace ℝ (Fin n) =>
        WithLp.toLp 2 (fun i => Real.exp (lam * a i + (1 - lam) * b i) * x i)) '' K,
        Real.exp (-Real.pi * ‖x‖ ^ 2) := by
  classical
  show (∫ x in diagMap a '' K, Real.exp (-Real.pi * ‖x‖ ^ 2)) ^ lam
      * (∫ x in diagMap b '' K, Real.exp (-Real.pi * ‖x‖ ^ 2)) ^ (1 - lam)
      ≤ ∫ x in diagMap (fun i => lam * a i + (1 - lam) * b i) '' K,
        Real.exp (-Real.pi * ‖x‖ ^ 2)
  -- replace `K` by its closure
  rw [integral_diagMap_closure K hKcvx a, integral_diagMap_closure K hKcvx b,
    integral_diagMap_closure K hKcvx (fun i => lam * a i + (1 - lam) * b i)]
  have hKomeas : MeasurableSet (closure K) := isClosed_closure.measurableSet
  have hKocvx : Convex ℝ (closure K) := hKcvx.closure
  have hKosymm : -(closure K) = closure K := closure_neg_eq K hKsymm
  have hEw_int : Integrable (fun x : EuclideanSpace ℝ (Fin n) => Real.exp (-Real.pi * ‖x‖ ^ 2)) := by
    have h := integrable_prod_one_add_sq_pow_mul_exp (n := n) (c := Real.pi) Real.pi_pos 0
    simpa using h
  have hsupp : Function.support (fun x : EuclideanSpace ℝ (Fin n) =>
      Real.exp (-Real.pi * ‖x‖ ^ 2)) = Set.univ := by
    ext x
    simp [Function.mem_support]
  have hvol_eq : ∀ u : Fin n → ℝ, volume (diagMap u '' closure K)
      = ENNReal.ofReal |LinearMap.det (diagLinearMap u)| * volume (closure K) := by
    intro u
    have h := MeasureTheory.Measure.addHaar_image_linearMap (μ := volume) (diagLinearMap u) (closure K)
    have hfun : (⇑(diagLinearMap u) : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        = diagMap u := funext fun x => diagLinearMap_apply u x
    rwa [hfun] at h
  by_cases hvol : volume (closure K) = 0
  · -- degenerate case: all integrals vanish
    have hzero : ∀ u : Fin n → ℝ, (∫ x in diagMap u '' closure K,
        Real.exp (-Real.pi * ‖x‖ ^ 2)) = 0 := by
      intro u
      apply setIntegral_measure_zero
      rw [hvol_eq u, hvol, mul_zero]
    rw [hzero a, hzero b, hzero (fun i => lam * a i + (1 - lam) * b i)]
    rcases eq_or_lt_of_le h0 with hl | hl
    · subst hl; simp
    · rcases eq_or_lt_of_le h1 with hl1 | hl1
      · subst hl1; simp
      · rw [Real.zero_rpow (ne_of_gt hl), Real.zero_rpow (by linarith : (1:ℝ) - lam ≠ 0)]
        norm_num
  · -- main case: `closure K` has positive measure
    have hvolpos : 0 < volume (closure K) := pos_iff_ne_zero.mpr hvol
    have hvolA : ∀ u : Fin n → ℝ, 0 < volume (diagMap u '' closure K) := by
      intro u
      rw [hvol_eq u]
      exact pos_iff_ne_zero.mpr (mul_ne_zero (by
        rw [ENNReal.ofReal_ne_zero_iff]
        exact abs_pos.mpr (det_diagLinearMap_ne_zero u)) hvol)
    have hpos_int : ∀ u : Fin n → ℝ,
        0 < ∫ x in diagMap u '' closure K, Real.exp (-Real.pi * ‖x‖ ^ 2) := by
      intro u
      have hAmeas : MeasurableSet (diagMap u '' closure K) := measurableSet_image_diagMap hKomeas u
      refine (integral_pos_iff_support_of_nonneg_ae
        (μ := volume.restrict (diagMap u '' closure K))
        (Eventually.of_forall (fun x : EuclideanSpace ℝ (Fin n) => (Real.exp_pos _).le))
        hEw_int.integrableOn).mpr ?_
      rw [hsupp]
      rw [Measure.restrict_apply' hAmeas, Set.univ_inter]
      exact hvolA u
    have hφpos : ∀ t : ℝ, 0 < ∫ y in closure K, diagExp (b + t • (a - b)) y := by
      intro t
      rw [show (∫ y in closure K, diagExp (b + t • (a - b)) y)
          = ∫ x in diagMap (b + t • (a - b)) '' closure K, Real.exp (-Real.pi * ‖x‖ ^ 2) from
        (integral_diag_image (closure K) hKomeas (b + t • (a - b))).symm]
      exact hpos_int _
    have hderiv : ∀ t : ℝ, HasDerivAt (fun u : ℝ => ∫ y in closure K, diagExp (b + u • (a - b)) y)
        (∫ y in closure K, diagD1 (b + t • (a - b)) (a - b) y) t := by
      intro t
      have h := hasDerivAt_integral_diagExp (closure K) (b + t • (a - b)) (a - b)
      have harg : ∀ s : ℝ, ((b + t • (a - b)) + s • (a - b) : Fin n → ℝ)
          = b + (t + s) • (a - b) := by
        intro s
        ext i
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      have hfun : (fun s : ℝ => ∫ y in closure K, diagExp ((b + t • (a - b)) + s • (a - b)) y)
          = fun s : ℝ => (fun u : ℝ => ∫ y in closure K, diagExp (b + u • (a - b)) y) (t + s) := by
        funext s
        rw [harg s]
      rw [hfun] at h
      exact hasDerivAt_of_comp_add (f := fun u : ℝ =>
        ∫ y in closure K, diagExp (b + u • (a - b)) y)
        (f' := ∫ y in closure K, diagD1 (b + t • (a - b)) (a - b) y) (t := t) h
    have hderiv2 : ∀ t : ℝ,
        HasDerivAt (fun u : ℝ => ∫ y in closure K, diagD1 (b + u • (a - b)) (a - b) y)
          (∫ y in closure K, diagD2 (b + t • (a - b)) (a - b) y) t := by
      intro t
      have h := hasDerivAt_integral_diagD1 (closure K) (b + t • (a - b)) (a - b)
      have harg : ∀ s : ℝ, ((b + t • (a - b)) + s • (a - b) : Fin n → ℝ)
          = b + (t + s) • (a - b) := by
        intro s
        ext i
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      have hfun : (fun s : ℝ => ∫ y in closure K,
            diagD1 ((b + t • (a - b)) + s • (a - b)) (a - b) y)
          = fun s : ℝ => (fun u : ℝ => ∫ y in closure K,
              diagD1 (b + u • (a - b)) (a - b) y) (t + s) := by
        funext s
        rw [harg s]
      rw [hfun] at h
      exact hasDerivAt_of_comp_add (f := fun u : ℝ =>
        ∫ y in closure K, diagD1 (b + u • (a - b)) (a - b) y)
        (f' := ∫ y in closure K, diagD2 (b + t • (a - b)) (a - b) y) (t := t) h
    have hcore : ∀ t : ℝ, (∫ y in closure K, diagExp (b + t • (a - b)) y) *
        (∫ y in closure K, diagD2 (b + t • (a - b)) (a - b) y)
        - (∫ y in closure K, diagD1 (b + t • (a - b)) (a - b) y) ^ 2 ≤ 0 := by
      intro t
      refine core_ineq (closure K) hKomeas (b + t • (a - b)) (a - b) ?_ (hpos_int _)
      have hAmeas : MeasurableSet (diagMap (b + t • (a - b)) '' closure K) :=
        measurableSet_image_diagMap hKomeas _
      have hAcvx : Convex ℝ (diagMap (b + t • (a - b)) '' closure K) :=
        convex_image_diagMap hKocvx _
      have hAsymm : ∀ x, x ∈ diagMap (b + t • (a - b)) '' closure K ↔
          -x ∈ diagMap (b + t • (a - b)) '' closure K := by
        intro x
        rw [← Set.mem_neg (s := diagMap (b + t • (a - b)) '' closure K) (a := x),
          neg_image_diagMap hKosymm]
      have hf_cd : ContDiff ℝ 1 (fun x : EuclideanSpace ℝ (Fin n) =>
          ∑ i, (a - b) i * x i ^ 2) := by fun_prop
      have hf_even : ∀ x : EuclideanSpace ℝ (Fin n),
          (fun x : EuclideanSpace ℝ (Fin n) => ∑ i, (a - b) i * x i ^ 2) (-x)
            = (fun x : EuclideanSpace ℝ (Fin n) => ∑ i, (a - b) i * x i ^ 2) x := by
        intro x
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp only [PiLp.neg_apply]
        ring
      exact H _ hAcvx hAsymm hAmeas (hpos_int _) _ hf_cd hf_even
        ((integrable_quad_sq_gauss (a - b)).integrableOn)
        ((integrable_fderiv_quad_gauss (a - b)).integrableOn)
    have hconc : ConcaveOn ℝ (Set.Icc 0 1)
        (fun t : ℝ => Real.log (∫ y in closure K, diagExp (b + t • (a - b)) y)) := by
      refine concaveOn_of_hasDerivWithinAt2_nonpos (D := Set.Icc 0 1) (convex_Icc 0 1)
        (f' := fun t : ℝ => (∫ y in closure K, diagD1 (b + t • (a - b)) (a - b) y)
          / (∫ y in closure K, diagExp (b + t • (a - b)) y))
        (f'' := fun t : ℝ => ((∫ y in closure K, diagExp (b + t • (a - b)) y)
            * (∫ y in closure K, diagD2 (b + t • (a - b)) (a - b) y)
            - (∫ y in closure K, diagD1 (b + t • (a - b)) (a - b) y) ^ 2)
          / ((∫ y in closure K, diagExp (b + t • (a - b)) y) ^ 2)) ?_ ?_ ?_ ?_
      · exact (Continuous.log (continuous_iff_continuousAt.mpr
          fun t => (hderiv t).continuousAt) (fun t => (hφpos t).ne')).continuousOn
      · intro x _
        exact ((hderiv x).log (hφpos x).ne').hasDerivWithinAt
      · intro x _
        refine (((hderiv2 x).div (hderiv x) (hφpos x).ne').hasDerivWithinAt).congr_deriv ?_
        ring
      · intro x _
        have h2 : (0:ℝ) < (∫ y in closure K, diagExp (b + x • (a - b)) y) ^ 2 :=
          pow_pos (hφpos x) 2
        exact div_nonpos_of_nonpos_of_nonneg (hcore x) h2.le
    have e0 : (fun t : ℝ => ∫ y in closure K, diagExp (b + t • (a - b)) y) 0
        = ∫ y in closure K, diagExp b y := by
      show (∫ y in closure K, diagExp (b + (0:ℝ) • (a - b)) y)
        = ∫ y in closure K, diagExp b y
      simp only [zero_smul, add_zero]
    have e1 : (fun t : ℝ => ∫ y in closure K, diagExp (b + t • (a - b)) y) 1
        = ∫ y in closure K, diagExp a y := by
      show (∫ y in closure K, diagExp (b + (1:ℝ) • (a - b)) y)
        = ∫ y in closure K, diagExp a y
      have harg : (b + (1:ℝ) • (a - b) : Fin n → ℝ) = a := by
        ext i
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, one_mul]
        ring
      rw [harg]
    have elam : (fun t : ℝ => ∫ y in closure K, diagExp (b + t • (a - b)) y)
          ((1 - lam) • 0 + lam • 1) = ∫ y in closure K, diagExp (b + lam • (a - b)) y := by
      show (∫ y in closure K, diagExp (b + ((1 - lam) • (0:ℝ) + lam • 1) • (a - b)) y)
        = ∫ y in closure K, diagExp (b + lam • (a - b)) y
      have hs : ((1 - lam) • (0:ℝ) + lam • 1) = lam := by ring
      rw [hs]

    have hlog : (1 - lam) * Real.log (∫ y in closure K, diagExp b y)
        + lam * Real.log (∫ y in closure K, diagExp a y)
        ≤ Real.log (∫ y in closure K, diagExp (b + lam • (a - b)) y) := by
      have h := hconc.2 (show (0:ℝ) ∈ Set.Icc 0 1 from ⟨le_rfl, zero_le_one⟩)
        (show (1:ℝ) ∈ Set.Icc 0 1 from ⟨zero_le_one, le_rfl⟩)
        (show (0:ℝ) ≤ 1 - lam by linarith) h0 (show (1 - lam) + lam = 1 by ring)
      simp only [smul_eq_mul, e0, e1, elam,
        show ((1 - lam) * (0:ℝ) + lam * 1) = lam by ring] at h
      exact h
    have key : (∫ y in closure K, diagExp b y) ^ (1 - lam)
        * (∫ y in closure K, diagExp a y) ^ lam
        ≤ ∫ y in closure K, diagExp (b + lam • (a - b)) y := by
      have hp0 : (0:ℝ) < ∫ y in closure K, diagExp b y := e0 ▸ hφpos 0
      have hp1 : (0:ℝ) < ∫ y in closure K, diagExp a y := e1 ▸ hφpos 1
      have hplam : (0:ℝ) < ∫ y in closure K, diagExp (b + lam • (a - b)) y := hφpos lam
      calc (∫ y in closure K, diagExp b y) ^ (1 - lam)
            * (∫ y in closure K, diagExp a y) ^ lam
          = Real.exp ((1 - lam) * Real.log (∫ y in closure K, diagExp b y))
              * Real.exp (lam * Real.log (∫ y in closure K, diagExp a y)) := by
            rw [Real.rpow_def_of_pos hp0, Real.rpow_def_of_pos hp1]
            ring_nf
        _ = Real.exp ((1 - lam) * Real.log (∫ y in closure K, diagExp b y)
              + lam * Real.log (∫ y in closure K, diagExp a y)) := by rw [Real.exp_add]
        _ ≤ Real.exp (Real.log (∫ y in closure K, diagExp (b + lam • (a - b)) y)) :=
            Real.exp_le_exp.mpr hlog
        _ = ∫ y in closure K, diagExp (b + lam • (a - b)) y := Real.exp_log hplam
    rw [integral_diag_image_diagMap (closure K) hKomeas a,
      integral_diag_image_diagMap (closure K) hKomeas b,
      integral_diag_image_diagMap (closure K) hKomeas (fun i => lam * a i + (1 - lam) * b i)]
    have hfun : (b + lam • (a - b) : Fin n → ℝ) = fun i => lam * a i + (1 - lam) * b i := by
      funext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [← hfun]
    calc (∫ y in closure K, diagExp a y) ^ lam * (∫ y in closure K, diagExp b y) ^ (1 - lam)
        = (∫ y in closure K, diagExp b y) ^ (1 - lam)
            * (∫ y in closure K, diagExp a y) ^ lam := mul_comm _ _
      _ ≤ ∫ y in closure K, diagExp (b + lam • (a - b)) y := key

end

end Commons.Analysis.GaussianMeasure