import Mathlib
import Submission.Work.HP.ArchDefs

/-!
# Basic Euclidean facts for `rNorm`, `dotR` and `formEvalR`

Elementary lemmas about the *Euclidean* norm `rNorm` and inner product `dotR` of `Work.HP`,
used by the archimedean scaling lemma `Work.HP.tau_prop_scale`.

* `rNorm_sq` : `rNorm v ^ 2 = ∑ i, v i ^ 2`
* `abs_dotR_le` : Cauchy--Schwarz, `|dotR v w| ≤ rNorm v * rNorm w`
* `rNorm_smul'` : `rNorm (t • v) = |t| * rNorm v`
* `rNorm_add_le`, `rNorm_sub_le`, ... : triangle inequality
* `formEvalR_smul` : `f_{t·a}(x) = t * f_a(x)`
-/

set_option autoImplicit false

noncomputable section

open Classical Finset MvPolynomial MeasureTheory
open scoped BigOperators

namespace Work.HP

variable {ι : Type*} [Fintype ι]

/-! ## The norm `rNorm` -/

lemma rNorm_nonneg (v : ι → ℝ) : 0 ≤ rNorm v := Real.sqrt_nonneg _

lemma rNorm_sq (v : ι → ℝ) : rNorm v ^ 2 = ∑ i, v i ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)

lemma rNorm_eq_zero {v : ι → ℝ} : rNorm v = 0 ↔ v = 0 := by
  constructor
  · intro h
    funext i
    have h2 : rNorm v ^ 2 = 0 := by rw [h]; ring
    rw [rNorm_sq] at h2
    have hnon : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ v i ^ 2 := fun i _ => sq_nonneg _
    have hle : v i ^ 2 ≤ ∑ j, v j ^ 2 := Finset.single_le_sum hnon (Finset.mem_univ i)
    have : v i ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  · intro h; rw [h]; simp [rNorm]

lemma abs_apply_le_rNorm (v : ι → ℝ) (i : ι) : |v i| ≤ rNorm v := by
  have h : v i ^ 2 ≤ ∑ j, v j ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  calc |v i| = Real.sqrt (v i ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∑ j, v j ^ 2) := Real.sqrt_le_sqrt h
    _ = rNorm v := rfl

lemma rNorm_smul' (t : ℝ) (v : ι → ℝ) : rNorm (t • v) = |t| * rNorm v := by
  simp only [rNorm, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs]

lemma rNorm_smul_of_pos (t : ℝ) (v : ι → ℝ) (ht : 0 < t) : rNorm (t • v) = t * rNorm v := by
  rw [rNorm_smul', abs_of_pos ht]

lemma rNorm_neg (v : ι → ℝ) : rNorm (-v) = rNorm v := by
  have h := rNorm_smul' (-1) v
  simpa using h

lemma rNorm_eq_normE (v : ι → ℝ) : rNorm v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ ι)‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [rNorm]

lemma rNorm_add_le (v w : ι → ℝ) : rNorm (v + w) ≤ rNorm v + rNorm w := by
  rw [rNorm_eq_normE (v + w), rNorm_eq_normE v, rNorm_eq_normE w,
    show (WithLp.toLp 2 (v + w) : EuclideanSpace ℝ ι) = WithLp.toLp 2 v + WithLp.toLp 2 w from by
      simp]
  exact norm_add_le _ _

lemma rNorm_sub_le (v w : ι → ℝ) : rNorm (v - w) ≤ rNorm v + rNorm w := by
  rw [sub_eq_add_neg]
  exact (rNorm_add_le v (-w)).trans (by rw [rNorm_neg])

lemma rNorm_sub_comm (v w : ι → ℝ) : rNorm (v - w) = rNorm (w - v) := by
  rw [← neg_sub w v, rNorm_neg]

lemma rNorm_le_add_sub (y a : ι → ℝ) : rNorm y ≤ rNorm a + rNorm (y - a) := by
  have h : y = a + (y - a) := by ext i; simp
  nth_rewrite 1 [h]
  exact rNorm_add_le a (y - a)

/-! ## The inner product `dotR` -/

lemma dotR_add_right (v w₁ w₂ : ι → ℝ) : dotR v (w₁ + w₂) = dotR v w₁ + dotR v w₂ := by
  simp only [dotR, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma dotR_sub_right (v w₁ w₂ : ι → ℝ) : dotR v (w₁ - w₂) = dotR v w₁ - dotR v w₂ := by
  simp only [dotR, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

lemma dotR_smul_right (v w : ι → ℝ) (t : ℝ) : dotR v (t • w) = t * dotR v w := by
  simp only [dotR, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Cauchy--Schwarz for `dotR` and `rNorm`. -/
lemma abs_dotR_le (v w : ι → ℝ) : |dotR v w| ≤ rNorm v * rNorm w := by
  have h1 : (∑ i, v i * w i) ^ 2 ≤ (∑ i, v i ^ 2) * (∑ i, w i ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h2 : rNorm v ^ 2 = ∑ i, v i ^ 2 := rNorm_sq v
  have h3 : rNorm w ^ 2 = ∑ i, w i ^ 2 := rNorm_sq w
  have h5 : dotR v w ^ 2 ≤ (rNorm v * rNorm w) ^ 2 := by
    rw [dotR, mul_pow, h2, h3]
    exact h1
  calc |dotR v w| = Real.sqrt (dotR v w ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((rNorm v * rNorm w) ^ 2) := Real.sqrt_le_sqrt h5
    _ = rNorm v * rNorm w := Real.sqrt_sq (mul_nonneg (rNorm_nonneg v) (rNorm_nonneg w))

/-! ## `formEvalR` as a pairing with the Veronese point -/

lemma formEvalR_eq_dotR (d n : ℕ) (a : Mon d n → ℝ) (x : Fin (n + 1) → ℝ) :
    formEvalR d n a x = dotR a (veronese d n x) := rfl

lemma formEvalR_smul (d n : ℕ) (a : Mon d n → ℝ) (x : Fin (n + 1) → ℝ) (t : ℝ) :
    formEvalR d n (t • a) x = t * formEvalR d n a x := by
  simp only [formEvalR, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by ring

lemma formEvalR_congr (d n : ℕ) {a a' : Mon d n → ℝ} (h : a = a') (x : Fin (n + 1) → ℝ) :
    formEvalR d n a x = formEvalR d n a' x := by rw [h]

end Work.HP
