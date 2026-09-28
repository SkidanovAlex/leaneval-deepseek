import Mathlib
import Submission.Work.HP.ArchDefs
import Submission.Work.HP.tau_basic
import Submission.Work.HP.ArchGlueV2
import Submission.Work.HP.tau_meas_posV2
import Submission.Work.HP.volume_rNorm_ball
import Submission.Work.HP.rNorm_smul
import Submission.Work.HP.HPtau.slab_lower
import Submission.Work.HP.HPtau.scale_consts

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Classical Finset MvPolynomial MeasureTheory
open scoped BigOperators ENNReal Pointwise

namespace Work.HP

variable {d n : ℕ}

/-! ## 1. The one-coordinate monomial and the Veronese lower bound -/

/-- The one-coordinate monomial `x_j^d`. -/
def dMon (d n : ℕ) (j : Fin (n + 1)) : Mon d n :=
  ⟨Function.update (fun _ : Fin (n + 1) => (0 : Fin (d + 1))) j ⟨d, Nat.lt_succ_self d⟩, by
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hi
      simp [Function.update_of_ne hi]
    · intro h; exact absurd (Finset.mem_univ j) h⟩

lemma veronese_dMon (d n : ℕ) (j : Fin (n + 1)) (u : Fin (n + 1) → ℝ) :
    veronese d n u (dMon d n j) = u j ^ d := by
  rw [veronese, Finset.prod_eq_single j]
  · simp [dMon]
  · intro i _ hi
    simp [dMon, Function.update_of_ne hi]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- One coordinate times `√(n+1)` dominates the Euclidean norm. -/
lemma exists_max_abs (u : Fin (n + 1) → ℝ) :
    ∃ j : Fin (n + 1), rNorm u ≤ Real.sqrt ((n : ℝ) + 1) * |u j| := by
  obtain ⟨j, _, hj⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin (n + 1))) (fun i => |u i|)
      Finset.univ_nonempty
  refine ⟨j, ?_⟩
  rw [rNorm]
  have hle : ∀ i : Fin (n + 1), u i ^ 2 ≤ u j ^ 2 := by
    intro i
    have h1 : |u i| ≤ |u j| := hj i (Finset.mem_univ i)
    have h2 := pow_le_pow_left₀ (abs_nonneg (u i)) h1 2
    simpa only [sq_abs] using h2
  calc Real.sqrt (∑ i, u i ^ 2) ≤ Real.sqrt (∑ _i : Fin (n + 1), u j ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => hle i)
    _ = Real.sqrt (((n : ℝ) + 1) * u j ^ 2) := by
        rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
        push_cast
        ring_nf
    _ = Real.sqrt ((n : ℝ) + 1) * |u j| := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs]

/-- `‖ν_{d,n}(u)‖ ≥ (√(n+1))^{-d} ‖u‖^d`. -/
lemma veronese_rNorm_ge (d n : ℕ) (u : Fin (n + 1) → ℝ) :
    (Real.sqrt ((n : ℝ) + 1))⁻¹ ^ d * rNorm u ^ d ≤ rNorm (veronese d n u) := by
  obtain ⟨j, hj⟩ := exists_max_abs u
  have h1 : (Real.sqrt ((n : ℝ) + 1))⁻¹ ^ d * rNorm u ^ d
      ≤ (Real.sqrt ((n : ℝ) + 1))⁻¹ ^ d * ((Real.sqrt ((n : ℝ) + 1)) * |u j|) ^ d := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact pow_le_pow_left₀ (rNorm_nonneg _) hj d
  refine h1.trans ?_
  have h2 : (Real.sqrt ((n : ℝ) + 1))⁻¹ ^ d
      * ((Real.sqrt ((n : ℝ) + 1)) * |u j|) ^ d = |u j| ^ d := by
    rw [mul_pow, ← mul_assoc, ← mul_pow,
      inv_mul_cancel₀ (by positivity : Real.sqrt ((n : ℝ) + 1) ≠ 0), one_pow, one_mul]
  rw [h2]
  have h3 : |u j| ^ d ≤ rNorm (veronese d n u) := by
    have h4 := abs_apply_le_rNorm (veronese d n u) (dMon d n j)
    rwa [veronese_dMon, abs_pow] at h4
  exact h3

/-- Half of the guaranteed lower bound for `‖ν_{d,n}(u)‖` when `‖u‖ ≥ 1/4`. -/
def K0 (d n : ℕ) : ℝ := (1 / 2) * (Real.sqrt ((n : ℝ) + 1))⁻¹ ^ d * (1 / 4) ^ d

lemma K0_pos (d n : ℕ) : 0 < K0 d n := by
  rw [K0]; positivity

lemma K0_le_veronese {d n : ℕ} {u : Fin (n + 1) → ℝ} (hu : 1 / 4 ≤ rNorm u) :
    K0 d n ≤ (1 / 2) * rNorm (veronese d n u) := by
  have h := veronese_rNorm_ge d n u
  have h4 : (1 / 4 : ℝ) ^ d ≤ rNorm u ^ d := pow_le_pow_left₀ (by norm_num) hu d
  calc K0 d n = (1 / 2) * ((Real.sqrt ((n : ℝ) + 1))⁻¹ ^ d * (1 / 4) ^ d) := by rw [K0]; ring
    _ ≤ (1 / 2) * ((Real.sqrt ((n : ℝ) + 1))⁻¹ ^ d * rNorm u ^ d) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact mul_le_mul_of_nonneg_left h4 (by positivity)
    _ ≤ (1 / 2) * rNorm (veronese d n u) :=
        mul_le_mul_of_nonneg_left h (by norm_num)

/-- `f_a` is homogeneous of degree `d`. -/
lemma formEvalR_smul_vec (d n : ℕ) (a : Mon d n → ℝ) (t : ℝ) (x : Fin (n + 1) → ℝ) :
    formEvalR d n a (t • x) = t ^ d * formEvalR d n a x := by
  simp only [formEvalR, veronese, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have h1 : (∏ i : Fin (n + 1), (t * x i) ^ ((m.1 i : ℕ)))
      = t ^ d * ∏ i : Fin (n + 1), x i ^ ((m.1 i : ℕ)) := by
    rw [Finset.prod_congr rfl (fun i _ => by rw [mul_pow]), Finset.prod_mul_distrib]
    have h2 : (∏ i : Fin (n + 1), t ^ ((m.1 i : ℕ))) = t ^ d := by
      rw [Finset.prod_pow_eq_pow_sum, m.2]
    rw [h2]
  rw [h1]; ring

lemma K0_pos' (d n : ℕ) : 0 < K0 d n := K0_pos d n

/-! ## 2. Inserting a coordinate and the inner product -/

/-- The vector `x` with the `i`-th coordinate replaced by `t` and the other coordinates given by
`z`.  This is a non-dependent wrapper around `Fin.insertNth`, whose elaboration is much more
robust (the family argument of `Fin.insertNth` is a metavariable otherwise). -/
def insN (n : ℕ) (i : Fin (n + 1)) (t : ℝ) (z : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.insertNth i t z

lemma insN_eq_insertNth (i : Fin (n + 1)) (t : ℝ) (z : Fin n → ℝ) :
    insN n i t z = Fin.insertNth i t z := rfl

@[simp] lemma insN_apply_same (i : Fin (n + 1)) (t : ℝ) (z : Fin n → ℝ) : insN n i t z i = t := by
  rw [insN_eq_insertNth, Fin.insertNth_apply_same]

@[simp] lemma insN_apply_succAbove (i : Fin (n + 1)) (t : ℝ) (z : Fin n → ℝ) (j : Fin n) :
    insN n i t z (i.succAbove j) = z j := by
  rw [insN_eq_insertNth, Fin.insertNth_apply_succAbove]

/-- The `i`-th unit vector. -/
def evec (n : ℕ) (i : Fin (n + 1)) : Fin (n + 1) → ℝ := insN n i (1 : ℝ) (fun _ => 0)

lemma evec_eq_insertNth (i : Fin (n + 1)) :
    evec n i = Fin.insertNth i (1 : ℝ) (fun _ : Fin n => (0 : ℝ)) := rfl

@[simp] lemma evec_apply_same (i : Fin (n + 1)) : evec n i i = 1 := insN_apply_same i 1 (fun _ => 0)

@[simp] lemma evec_apply_succAbove (i : Fin (n + 1)) (j : Fin n) : evec n i (i.succAbove j) = 0 :=
  insN_apply_succAbove i 1 (fun _ => 0) j

lemma dotR_insN (i : Fin (n + 1)) (g : Fin (n + 1) → ℝ) (t : ℝ) (z : Fin n → ℝ) :
    dotR g (insN n i t z) = t * g i + ∑ j : Fin n, z j * g (i.succAbove j) := by
  rw [insN_eq_insertNth, dotR, Fin.sum_univ_succAbove _ i]
  congr 1
  · rw [Fin.insertNth_apply_same]; ring
  · exact Finset.sum_congr rfl fun j _ => by rw [Fin.insertNth_apply_succAbove]; ring

lemma dotR_evec (i : Fin (n + 1)) (g : Fin (n + 1) → ℝ) : dotR g (evec n i) = g i := by
  rw [evec, dotR_insN]
  simp

lemma rNorm_insN_sq (i : Fin (n + 1)) (t : ℝ) (z : Fin n → ℝ) :
    rNorm (insN n i t z) ^ 2 = t ^ 2 + ∑ j : Fin n, z j ^ 2 := by
  rw [insN_eq_insertNth, rNorm_sq, Fin.sum_univ_succAbove _ i]
  simp

lemma rNorm_evec (i : Fin (n + 1)) : rNorm (evec n i) = 1 := by
  have h : rNorm (evec n i) ^ 2 = 1 := by
    rw [evec, rNorm_insN_sq]
    simp
  nlinarith [rNorm_nonneg (evec n i)]

lemma rNorm_succAbove_le (i : Fin (n + 1)) (g : Fin (n + 1) → ℝ) :
    rNorm (fun j : Fin n => g (i.succAbove j)) ≤ rNorm g := by
  rw [rNorm, rNorm]
  refine Real.sqrt_le_sqrt ?_
  have h := Fin.sum_univ_succAbove (fun j => g j ^ 2) i
  rw [h]
  exact le_add_of_nonneg_left (sq_nonneg _)

lemma insN_slice_eq (i : Fin (n + 1)) (t : ℝ) (z : Fin n → ℝ) :
    insN n i t z = insN n i 0 z + t • (evec n i) := by
  rw [insN_eq_insertNth, insN_eq_insertNth, evec_eq_insertNth]
  refine Fin.insertNth_eq_iff.mpr ⟨by simp, ?_⟩
  funext k
  simp only [Fin.removeNth_apply, Fin.insertNth_apply_succAbove, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, mul_zero, add_zero]

lemma insN_slice_sub (i : Fin (n + 1)) (t t₀ : ℝ) (z : Fin n → ℝ) :
    insN n i t z - insN n i t₀ z = (t - t₀) • (evec n i) := by
  funext j
  have h1 := congrFun (insN_slice_eq i t z) j
  have h2 := congrFun (insN_slice_eq i t₀ z) j
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply] at h1 h2 ⊢
  rw [h1, h2]
  ring

/-- The slice `t ↦ x + insN n i t z` is continuous. -/
lemma continuous_insN_slice (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) (z : Fin n → ℝ) :
    Continuous fun t : ℝ => x + insN n i t z := by
  have hw : (fun t : ℝ => x + insN n i t z)
      = fun t : ℝ => (x + insN n i 0 z) + t • (evec n i) := by
    funext t
    rw [insN_slice_eq i t z, add_assoc]
  rw [hw]
  exact continuous_const.add (continuous_id.smul continuous_const)

/-! ## 3. The band contains a translate of a ball around `x/2` -/

lemma sub_band (d n : ℕ) (a : Mon d n → ℝ) (x : Fin (n + 1) → ℝ) (γ : ℝ)
    (hx : rNorm x = 1) (hγ : 0 < γ) :
    {u : Fin (n + 1) → ℝ | rNorm (u - (1 / 2 : ℝ) • x) ≤ 1 / 4 ∧
        |formEvalR d n a u| ≤ K0 d n * rNorm a / γ} ⊆ band d n a γ := by
  intro u ⟨hu, hf⟩
  have hx2 : rNorm ((1 / 2 : ℝ) • x) = 1 / 2 := by
    rw [rNorm_smul, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2), hx]
    norm_num
  have hru : rNorm u ≤ 1 := by
    have h := rNorm_le_add_sub u ((1 / 2 : ℝ) • x)
    rw [hx2] at h
    linarith
  have hru' : (1 / 4 : ℝ) ≤ rNorm u := by
    have h := rNorm_le_add_sub ((1 / 2 : ℝ) • x) u
    rw [hx2, rNorm_sub_comm] at h
    linarith
  refine ⟨hru, ?_⟩
  simp only [Cgam, Set.mem_ofPred_eq]
  have hcomm : dotR (veronese d n u) a = dotR a (veronese d n u) := by
    simp only [dotR]
    exact Finset.sum_congr rfl (fun m _ => mul_comm _ _)
  rw [hcomm, ← formEvalR_eq_dotR]
  have h2 := K0_le_veronese (d := d) (n := n) hru'
  calc |formEvalR d n a u| ≤ K0 d n * rNorm a / γ := hf
    _ ≤ ((1 / 2) * rNorm (veronese d n u)) * rNorm a / γ := by
        refine div_le_div_of_nonneg_right ?_ hγ.le
        exact mul_le_mul_of_nonneg_right h2 (rNorm_nonneg _)
    _ = rNorm (veronese d n u) * rNorm a / (2 * γ) := by ring

lemma volume_sub_band (d n : ℕ) (a : Mon d n → ℝ) (x : Fin (n + 1) → ℝ) (γ : ℝ)
    (hx : rNorm x = 1) (hγ : 0 < γ) :
    (volume {w : Fin (n + 1) → ℝ | rNorm w ≤ 1 / 4 ∧
        |formEvalR d n a (w + (1 / 2 : ℝ) • x)| ≤ K0 d n * rNorm a / γ})
      ≤ volume (band d n a γ) := by
  have htrans := measure_preimage_add_right (volume : Measure (Fin (n + 1) → ℝ))
      ((1 / 2 : ℝ) • x)
      {u : Fin (n + 1) → ℝ | rNorm (u - (1 / 2 : ℝ) • x) ≤ 1 / 4 ∧
        |formEvalR d n a u| ≤ K0 d n * rNorm a / γ}
  have hset : (fun h : Fin (n + 1) → ℝ => h + (1 / 2 : ℝ) • x) ⁻¹'
      {u : Fin (n + 1) → ℝ | rNorm (u - (1 / 2 : ℝ) • x) ≤ 1 / 4 ∧
        |formEvalR d n a u| ≤ K0 d n * rNorm a / γ}
      = {w : Fin (n + 1) → ℝ | rNorm w ≤ 1 / 4 ∧
        |formEvalR d n a (w + (1 / 2 : ℝ) • x)| ≤ K0 d n * rNorm a / γ} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, add_sub_cancel_right]
  rw [hset] at htrans
  rw [htrans]
  exact measure_mono (sub_band d n a x γ hx hγ)

/-! ## 4. Auxiliary norm estimates -/

/-- `∑ z_j² ≤ m A²` when `|z_j| ≤ A`. -/
lemma sum_sq_le (m : ℕ) (z : Fin m → ℝ) {A : ℝ} (hz : ∀ j, |z j| ≤ A) :
    ∑ j : Fin m, z j ^ 2 ≤ m * A ^ 2 := by
  have h1 : ∀ j : Fin m, z j ^ 2 ≤ A ^ 2 := by
    intro j
    have h := pow_le_pow_left₀ (abs_nonneg (z j)) (hz j) 2
    simpa only [sq_abs] using h
  calc ∑ j : Fin m, z j ^ 2 ≤ ∑ _j : Fin m, A ^ 2 := Finset.sum_le_sum fun j _ => h1 j
    _ = m * A ^ 2 := by rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]

lemma rNorm_insN_le_half {z : Fin n → ℝ} {A B t : ℝ} (i : Fin (n + 1))
    (hz : ∀ j, |z j| ≤ A) (ht : |t| ≤ B) (hbox : B ^ 2 + n * A ^ 2 ≤ 1 / 4) :
    rNorm (insN n i t z) ≤ 1 / 2 := by
  have h2 : rNorm (insN n i t z) ^ 2 ≤ (1 / 2) ^ 2 := by
    rw [rNorm_insN_sq]
    have ht2 : t ^ 2 ≤ B ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg t) ht 2
      rw [sq_abs] at h
      exact h
    have hz2 := sum_sq_le n z hz
    nlinarith
  nlinarith [rNorm_nonneg (insN n i t z)]

/-- `rNorm z ≤ √n · A` when `|z_j| ≤ A` and `0 ≤ A`. -/
lemma rNorm_le_sqrt_card (m : ℕ) (z : Fin m → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hz : ∀ j, |z j| ≤ A) : rNorm z ≤ Real.sqrt m * A := by
  rw [rNorm]
  have h := sum_sq_le m z hz
  calc Real.sqrt (∑ j, z j ^ 2) ≤ Real.sqrt ((m : ℝ) * A ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt m * A := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hA]

/-- The vector `e` with a single `1` in the coordinate `i`; see `evec`. -/
lemma abs_gradF_le (d n : ℕ) (a : Mon d n → ℝ) (x : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    |gradF d n a x j| ≤ rNorm (gradVec d n a x) :=
  abs_apply_le_rNorm _ _

lemma continuous_formEvalR_self (d n : ℕ) (a : Mon d n → ℝ) :
    Continuous fun v : Fin (n + 1) → ℝ => formEvalR d n a v := by
  simp only [formEvalR, veronese]
  fun_prop

/-! ## 5. A gradient bound from the two-sided Taylor estimate -/

private lemma dotR_sub_left {ι : Type*} [Fintype ι] (v₁ v₂ w : ι → ℝ) :
    dotR (v₁ - v₂) w = dotR v₁ w - dotR v₂ w := by
  simp only [dotR, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- A two-sided second order Taylor estimate at every pair of points of `B₂` bounds the difference
of the gradient at two nearby points. -/
lemma gradF_lip_const (d n : ℕ) (a : Mon d n → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (htay : ∀ (x y : Fin (n + 1) → ℝ), rNorm x ≤ 2 → rNorm y ≤ 2 →
        |formEvalR d n a y - formEvalR d n a x - dotR (gradVec d n a x) (y - x)|
          ≤ T * rNorm a * rNorm (y - x) ^ 2) :
    ∀ (x u : Fin (n + 1) → ℝ) (j : Fin (n + 1)), rNorm x ≤ 1 → rNorm u ≤ 1 / 2 →
      |gradF d n a (x + u) j - gradF d n a x j| ≤ 3 * T * rNorm a := by
  intro x u j hx hu
  set w : Fin (n + 1) → ℝ := (1 / 2 : ℝ) • evec n j with hwdef
  have hwn : rNorm w = 1 / 2 := by
    rw [hwdef, rNorm_smul, rNorm_evec, mul_one]
    norm_num
  have hx2 : rNorm x ≤ 2 := by linarith
  have hxu1 : rNorm (x + u) ≤ 3 / 2 := by
    have h := rNorm_add_le x u
    linarith
  have hxu : rNorm (x + u) ≤ 2 := by linarith
  have hxuw : rNorm (x + u + w) ≤ 2 := by
    have h := rNorm_add_le (x + u) w
    rw [hwn] at h
    linarith
  have hA : |formEvalR d n a (x + u + w) - formEvalR d n a (x + u)
      - dotR (gradVec d n a (x + u)) w| ≤ T * rNorm a * rNorm w ^ 2 := by
    have h := htay (x + u) (x + u + w) hxu hxuw
    rwa [show x + u + w - (x + u) = w from by abel] at h
  have hB : |formEvalR d n a (x + u + w) - formEvalR d n a x
      - dotR (gradVec d n a x) (u + w)| ≤ T * rNorm a * rNorm (u + w) ^ 2 := by
    have h := htay x (x + u + w) hx2 hxuw
    rwa [show x + u + w - x = u + w from by abel] at h
  have hC : |formEvalR d n a (x + u) - formEvalR d n a x
      - dotR (gradVec d n a x) u| ≤ T * rNorm a * rNorm u ^ 2 := by
    have h := htay x (x + u) hx2 hxu
    rwa [show x + u - x = u from by abel] at h
  have hid : dotR (gradVec d n a (x + u) - gradVec d n a x) w
      = -(  (formEvalR d n a (x + u + w) - formEvalR d n a (x + u)
              - dotR (gradVec d n a (x + u)) w)
          - (formEvalR d n a (x + u + w) - formEvalR d n a x
              - dotR (gradVec d n a x) (u + w))
          + (formEvalR d n a (x + u) - formEvalR d n a x - dotR (gradVec d n a x) u)) := by
    have e2 : dotR (gradVec d n a x) (u + w) - dotR (gradVec d n a x) u
        = dotR (gradVec d n a x) w := by
      rw [← dotR_sub_right]
      congr 1
      abel
    have e3 : dotR (gradVec d n a (x + u)) w - dotR (gradVec d n a x) w
        = dotR (gradVec d n a (x + u) - gradVec d n a x) w := by
      rw [dotR_sub_left]
    linarith [e2, e3]
  have hbound : |dotR (gradVec d n a (x + u) - gradVec d n a x) w|
      ≤ T * rNorm a * rNorm w ^ 2 + T * rNorm a * rNorm (u + w) ^ 2
        + T * rNorm a * rNorm u ^ 2 := by
    rw [hid, abs_neg]
    have h2 := abs_add_le
      ((formEvalR d n a (x + u + w) - formEvalR d n a (x + u) - dotR (gradVec d n a (x + u)) w)
        - (formEvalR d n a (x + u + w) - formEvalR d n a x - dotR (gradVec d n a x) (u + w)))
      (formEvalR d n a (x + u) - formEvalR d n a x - dotR (gradVec d n a x) u)
    have h3 : |(formEvalR d n a (x + u + w) - formEvalR d n a (x + u)
          - dotR (gradVec d n a (x + u)) w)
        - (formEvalR d n a (x + u + w) - formEvalR d n a x - dotR (gradVec d n a x) (u + w))|
        ≤ |formEvalR d n a (x + u + w) - formEvalR d n a (x + u) - dotR (gradVec d n a (x + u)) w|
          + |formEvalR d n a (x + u + w) - formEvalR d n a x - dotR (gradVec d n a x) (u + w)| := by
      have h := abs_add_le
        (formEvalR d n a (x + u + w) - formEvalR d n a (x + u) - dotR (gradVec d n a (x + u)) w)
        (-(formEvalR d n a (x + u + w) - formEvalR d n a x - dotR (gradVec d n a x) (u + w)))
      rwa [sub_eq_add_neg, abs_neg] at h
    linarith [h2, h3, hA, hB, hC]
  have hdot : dotR (gradVec d n a (x + u) - gradVec d n a x) w
      = (1 / 2 : ℝ) * (gradF d n a (x + u) j - gradF d n a x j) := by
    rw [hwdef]
    simp only [dotR_sub_left, dotR_smul_right, dotR_evec, gradVec]
  rw [hdot, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hbound
  have h1 : rNorm w ^ 2 = 1 / 4 := by rw [hwn]; norm_num
  have h2 : rNorm (u + w) ^ 2 ≤ 1 := by
    have h := rNorm_add_le u w
    rw [hwn] at h
    nlinarith [h, rNorm_nonneg (u + w)]
  have h3 : rNorm u ^ 2 ≤ 1 / 4 := by nlinarith [hu, rNorm_nonneg u]
  have hν : 0 ≤ rNorm a := rNorm_nonneg a
  rw [h1] at hbound
  nlinarith [hbound, h2, h3, hT, hν, abs_nonneg (gradF d n a (x + u) j - gradF d n a x j)]

/-! ## 5. Elementary slice lemmas -/

/-- Sign change of a function known up to a linear term: if `|hfun t - (D t + L)| ≤ Qb` for
`|t| ≤ B` and `|L| + Qb < |D| (B/2)`, then `hfun` takes both signs at `±B/2`. -/
lemma sign_slice {D L Qb B : ℝ} {hfun : ℝ → ℝ}
    (hQb : ∀ t : ℝ, |t| ≤ B → |hfun t - (D * t + L)| ≤ Qb)
    (hkey : |L| + Qb < |D| * (B / 2)) (hB : 0 < B) :
    (0 < hfun (B / 2) ∧ hfun (-(B / 2)) < 0) ∨
      (hfun (B / 2) < 0 ∧ 0 < hfun (-(B / 2))) := by
  have hB2 : 0 ≤ B / 2 := by linarith
  have hBhalf : |B / 2| ≤ B := by rw [abs_of_nonneg hB2]; linarith
  have hBhalf' : |-(B / 2)| ≤ B := by rw [abs_neg, abs_of_nonneg hB2]; linarith
  have hq1 := hQb (B / 2) hBhalf
  have hq2 := hQb (-(B / 2)) hBhalf'
  have h3 : -Qb ≤ hfun (B / 2) - (D * (B / 2) + L) := neg_le_of_abs_le hq1
  have h4 : hfun (B / 2) - (D * (B / 2) + L) ≤ Qb := le_of_abs_le hq1
  have h5 : -Qb ≤ hfun (-(B / 2)) - (D * (-(B / 2)) + L) := neg_le_of_abs_le hq2
  have h6 : hfun (-(B / 2)) - (D * (-(B / 2)) + L) ≤ Qb := le_of_abs_le hq2
  have hL1 : -|L| ≤ L := neg_abs_le L
  have hL2 : L ≤ |L| := le_abs_self L
  have h1 : hfun (B / 2) = D * (B / 2) + L + (hfun (B / 2) - (D * (B / 2) + L)) := by ring
  have h2 : hfun (-(B / 2))
      = D * (-(B / 2)) + L + (hfun (-(B / 2)) - (D * (-(B / 2)) + L)) := by ring
  by_cases hD0 : 0 ≤ D
  · left
    have hDabs : |D| = D := abs_of_nonneg hD0
    constructor <;> nlinarith [hkey, h1, h2, h3, h4, h5, h6, hL1, hL2, hDabs]
  · right
    have hD0' : D < 0 := lt_of_not_ge hD0
    have hDabs : |D| = -D := abs_of_neg hD0'
    constructor <;> nlinarith [hkey, h1, h2, h3, h4, h5, h6, hL1, hL2, hDabs]

/-- A second order Taylor expansion at a root bounds the value: the error and the linear part are
estimated separately. -/
lemma taylor_assembly {d n : ℕ} (a : Mon d n → ℝ) (T M s : ℝ)
    (Z U : Fin (n + 1) → ℝ)
    (hzero : formEvalR d n a Z = 0)
    (hTay : |formEvalR d n a (Z + U) - formEvalR d n a Z - dotR (gradVec d n a Z) U|
      ≤ T * rNorm a * s ^ 2)
    (hlin : |dotR (gradVec d n a Z) U| ≤ M * s) :
    |formEvalR d n a (Z + U)| ≤ T * rNorm a * s ^ 2 + M * s := by
  have hsum : formEvalR d n a (Z + U)
      = (formEvalR d n a (Z + U) - formEvalR d n a Z - dotR (gradVec d n a Z) U)
        + dotR (gradVec d n a Z) U + formEvalR d n a Z := by ring
  rw [hsum, hzero, add_zero]
  rw [hzero] at hTay
  have h1 := abs_add_le
    (formEvalR d n a (Z + U) - 0 - dotR (gradVec d n a Z) U)
    (dotR (gradVec d n a Z) U)
  linarith [h1, hTay, hlin]

/-- If a quantity is bounded by `K s² + M s` with `s ≤ δ` and both `K δ² ≤ ε/2` and
`M δ ≤ ε/2`, then it is bounded by `ε`. -/
lemma sq_lin_le {K M δ ε s : ℝ} (hK0 : 0 ≤ K) (hM0 : 0 ≤ M) (hs0 : 0 ≤ s) (hsδ : s ≤ δ)
    (hK : K * δ ^ 2 ≤ ε / 2) (hM : M * δ ≤ ε / 2) {x : ℝ} (hx : x ≤ K * s ^ 2 + M * s) :
    x ≤ ε := by
  have h1 : s ^ 2 ≤ δ ^ 2 := by nlinarith
  have h2 : K * s ^ 2 ≤ K * δ ^ 2 := mul_le_mul_of_nonneg_left h1 hK0
  have h3 : M * s ≤ M * δ := mul_le_mul_of_nonneg_left hsδ hM0
  linarith

/-- **Slice analysis.**  Around a point `x` (of norm `1`) where `f_a` vanishes with a non-zero
`i₀`-th partial derivative, every line `t ↦ x + insN n i₀ t z` over the transverse box
`|z_j| ≤ A` crosses the zero set, and the crossing has a neighbourhood of length `2δ` on which
`|f_a| ≤ ε`. -/
theorem slice_exists (d n : ℕ) (a : Mon d n → ℝ) (x : Fin (n + 1) → ℝ) (i₀ : Fin (n + 1))
    (T lam γ ε A B δ : ℝ)
    (hx1 : rNorm x = 1) (hf0 : formEvalR d n a x = 0)
    (hγ : 0 < γ) (hT : 0 < T) (hlam : 0 < lam) (hA : 0 < A) (hB : 0 < B) (hδ : 0 < δ)
    (hδB : δ ≤ B / 2)
    (hbox : B ^ 2 + n * A ^ 2 ≤ 1 / 4)
    (hgrad : rNorm (gradVec d n a x) ≤ 2 * lam * rNorm a)
    (hD : lam * rNorm a / Real.sqrt ((n : ℝ) + 1) ≤ |gradF d n a x i₀|)
    (htay : ∀ p q : Fin (n + 1) → ℝ, rNorm p ≤ 2 → rNorm q ≤ 2 →
        |formEvalR d n a q - formEvalR d n a p - dotR (gradVec d n a p) (q - p)|
          ≤ T * rNorm a * rNorm (q - p) ^ 2)
    (hlip : ∀ u : Fin (n + 1) → ℝ, rNorm u ≤ 1 / 2 →
        |gradF d n a (x + u) i₀ - gradF d n a x i₀| ≤ 3 * T * rNorm a)
    (hsgn : 2 * lam * rNorm a * (Real.sqrt n * A) + T * rNorm a * (B ^ 2 + n * A ^ 2)
        < lam * rNorm a / Real.sqrt ((n : ℝ) + 1) * (B / 2))
    (hδM : ((2 * lam + 3 * T) * rNorm a) * δ ≤ ε / 2)
    (hδq : (T * rNorm a) * δ ^ 2 ≤ ε / 2) :
    ∀ z : Fin n → ℝ, (∀ j, |z j| ≤ A) → ∃ t₀ : ℝ, |t₀| ≤ B / 2 ∧
      ∀ t : ℝ, |t - t₀| ≤ δ → |formEvalR d n a (x + insN n i₀ t z)| ≤ ε := by
  intro z hz
  have hA0 : 0 ≤ A := hA.le
  have hν0 : 0 ≤ rNorm a := rNorm_nonneg a
  have hB2 : 0 ≤ B / 2 := by linarith
  have hlamnu0 : 0 ≤ 2 * lam * rNorm a := mul_nonneg (by linarith) hν0
  have hTν0 : 0 ≤ T * rNorm a := mul_nonneg hT.le hν0
  have hM0 : 0 ≤ (2 * lam + 3 * T) * rNorm a :=
    mul_nonneg (by linarith [hT.le, hlam.le]) hν0
  have hzn : rNorm z ≤ Real.sqrt n * A := rNorm_le_sqrt_card n z hA0 hz
  -- (1) the transverse linear part
  have hLb : |∑ j : Fin n, z j * gradF d n a x (i₀.succAbove j)|
      ≤ 2 * lam * rNorm a * (Real.sqrt n * A) := by
    have h1 : (∑ j : Fin n, z j * gradF d n a x (i₀.succAbove j))
        = dotR (fun j : Fin n => gradF d n a x (i₀.succAbove j)) z := by
      rw [dotR]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h1]
    have h2 : |dotR (fun j : Fin n => gradF d n a x (i₀.succAbove j)) z|
        ≤ rNorm (fun j : Fin n => gradF d n a x (i₀.succAbove j)) * rNorm z :=
      abs_dotR_le _ _
    have h3 : rNorm (fun j : Fin n => gradF d n a x (i₀.succAbove j))
        ≤ rNorm (gradVec d n a x) := rNorm_succAbove_le i₀ (gradVec d n a x)
    have h4 : rNorm (gradVec d n a x) * rNorm z ≤ 2 * lam * rNorm a * (Real.sqrt n * A) :=
      mul_le_mul hgrad hzn (rNorm_nonneg _) hlamnu0
    have h5 : rNorm (fun j : Fin n => gradF d n a x (i₀.succAbove j)) * rNorm z
        ≤ rNorm (gradVec d n a x) * rNorm z :=
      mul_le_mul_of_nonneg_right h3 (rNorm_nonneg _)
    linarith [h2, h5, h4]
  -- (2) the norm of the slice point
  have hnorm_ins : ∀ t : ℝ, |t| ≤ B → rNorm (insN n i₀ t z) ≤ 1 / 2 := by
    intro t ht
    have h2 : rNorm (insN n i₀ t z) ^ 2 ≤ (1 / 2) ^ 2 := by
      rw [rNorm_insN_sq]
      have ht2 : t ^ 2 ≤ B ^ 2 := by
        have h := pow_le_pow_left₀ (abs_nonneg t) ht 2
        rw [sq_abs] at h
        exact h
      have hz2 := sum_sq_le n z hz
      nlinarith
    nlinarith [rNorm_nonneg (insN n i₀ t z)]
  -- (3) the quadratic remainder along the slice
  have hQb : ∀ t : ℝ, |t| ≤ B →
      |(fun s : ℝ => formEvalR d n a (x + insN n i₀ s z)) t
          - (gradF d n a x i₀ * t + ∑ j : Fin n, z j * gradF d n a x (i₀.succAbove j))|
        ≤ T * rNorm a * (B ^ 2 + n * A ^ 2) := by
    intro t ht
    have hd := dotR_insN i₀ (gradVec d n a x) t z
    have hfun_eq : (fun s : ℝ => formEvalR d n a (x + insN n i₀ s z)) t
        = formEvalR d n a (x + insN n i₀ t z) := rfl
    have hd' : gradF d n a x i₀ * t + ∑ j : Fin n, z j * gradF d n a x (i₀.succAbove j)
        = dotR (gradVec d n a x) (insN n i₀ t z) := by
      rw [hd]
      simp only [gradVec]
      ring
    rw [hfun_eq, hd']
    have hv1 : rNorm (insN n i₀ t z) ≤ 1 / 2 := hnorm_ins t ht
    have hp : rNorm (x + insN n i₀ t z) ≤ 2 := by
      have h1 := rNorm_add_le x (insN n i₀ t z)
      rw [hx1] at h1
      linarith
    have htay' := htay x (x + insN n i₀ t z) (by rw [hx1]; norm_num) hp
    have h2 : |formEvalR d n a (x + insN n i₀ t z)
        - dotR (gradVec d n a x) (insN n i₀ t z)|
        ≤ T * rNorm a * rNorm (insN n i₀ t z) ^ 2 := by
      rw [add_sub_cancel_left] at htay'
      rwa [hf0, sub_zero] at htay'
    have h3 : rNorm (insN n i₀ t z) ^ 2 ≤ B ^ 2 + n * A ^ 2 := by
      rw [rNorm_insN_sq]
      have ht2 : t ^ 2 ≤ B ^ 2 := by
        have h := pow_le_pow_left₀ (abs_nonneg t) ht 2
        rw [sq_abs] at h
        exact h
      have hz2 := sum_sq_le n z hz
      linarith
    exact h2.trans (mul_le_mul_of_nonneg_left h3 hTν0)
  -- (4) the key inequality and the sign change
  have hkey : |∑ j : Fin n, z j * gradF d n a x (i₀.succAbove j)|
      + T * rNorm a * (B ^ 2 + n * A ^ 2)
      < |gradF d n a x i₀| * (B / 2) := by
    have h1 : 2 * lam * rNorm a * (Real.sqrt n * A) + T * rNorm a * (B ^ 2 + n * A ^ 2)
        < |gradF d n a x i₀| * (B / 2) :=
      hsgn.trans_le (mul_le_mul_of_nonneg_right hD hB2)
    linarith [hLb]
  have hsigns : (0 < (fun s : ℝ => formEvalR d n a (x + insN n i₀ s z)) (B / 2) ∧
        (fun s : ℝ => formEvalR d n a (x + insN n i₀ s z)) (-(B / 2)) < 0) ∨
      ((fun s : ℝ => formEvalR d n a (x + insN n i₀ s z)) (B / 2) < 0 ∧
        0 < (fun s : ℝ => formEvalR d n a (x + insN n i₀ s z)) (-(B / 2))) :=
    sign_slice (D := gradF d n a x i₀)
      (L := ∑ j : Fin n, z j * gradF d n a x (i₀.succAbove j))
      (Qb := T * rNorm a * (B ^ 2 + n * A ^ 2)) (B := B) hQb hkey hB
  -- (5) the root, by the intermediate value theorem
  have hcont : Continuous fun t : ℝ => formEvalR d n a (x + insN n i₀ t z) :=
    (continuous_formEvalR_self d n a).comp (continuous_insN_slice i₀ x z)
  obtain ⟨t₀, ht₀mem, ht₀val⟩ : ∃ t₀ ∈ Set.Icc (-(B / 2)) (B / 2),
      formEvalR d n a (x + insN n i₀ t₀ z) = 0 := by
    have hBle : -(B / 2) ≤ B / 2 := by linarith
    rcases hsigns with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact intermediate_value_Icc hBle hcont.continuousOn ⟨h2.le, h1.le⟩
    · exact intermediate_value_Icc' hBle hcont.continuousOn ⟨h1.le, h2.le⟩
  have ht₀abs : |t₀| ≤ B / 2 := by rw [abs_le]; exact ⟨ht₀mem.1, ht₀mem.2⟩
  refine ⟨t₀, ht₀abs, ?_⟩
  intro t ht
  have hw : |t - t₀| ≤ δ := ht
  have ht₀B : |t₀| ≤ B := by linarith [ht₀abs]
  have hv₀ : rNorm (insN n i₀ t₀ z) ≤ 1 / 2 := hnorm_ins t₀ ht₀B
  -- (6) the derivative bound at the root
  have hderiv : |gradF d n a (x + insN n i₀ t₀ z) i₀| ≤ (2 * lam + 3 * T) * rNorm a := by
    have h1 : |gradF d n a (x + insN n i₀ t₀ z) i₀ - gradF d n a x i₀|
        ≤ 3 * T * rNorm a := hlip (insN n i₀ t₀ z) hv₀
    have h2 : |gradF d n a x i₀| ≤ 2 * lam * rNorm a :=
      (abs_gradF_le d n a x i₀).trans hgrad
    have h3 : |gradF d n a (x + insN n i₀ t₀ z) i₀|
        ≤ |gradF d n a x i₀| + |gradF d n a (x + insN n i₀ t₀ z) i₀ - gradF d n a x i₀| := by
      have h := abs_add_le (gradF d n a x i₀)
        (gradF d n a (x + insN n i₀ t₀ z) i₀ - gradF d n a x i₀)
      have heq : gradF d n a x i₀
          + (gradF d n a (x + insN n i₀ t₀ z) i₀ - gradF d n a x i₀)
          = gradF d n a (x + insN n i₀ t₀ z) i₀ := by ring
      rw [heq] at h
      exact h
    linarith [h1, h2, h3]
  -- (7) the second order Taylor bound at the root
  have hZ1 : rNorm (x + insN n i₀ t₀ z) ≤ 3 / 2 := by
    have h1 := rNorm_add_le x (insN n i₀ t₀ z)
    rw [hx1] at h1
    linarith
  have hZ2 : rNorm (x + insN n i₀ t₀ z) ≤ 2 := by linarith
  have hUnorm : rNorm ((t - t₀) • evec n i₀) = |t - t₀| := by
    rw [rNorm_smul, rNorm_evec, mul_one]
  have hBsmall : B ≤ 1 / 2 := by nlinarith [hbox, hB.le, sq_nonneg B]
  have hqd : rNorm ((x + insN n i₀ t₀ z) + (t - t₀) • evec n i₀) ≤ 2 := by
    have h2 := rNorm_add_le (x + insN n i₀ t₀ z) ((t - t₀) • evec n i₀)
    rw [hUnorm] at h2
    linarith
  have htay' := htay (x + insN n i₀ t₀ z)
    ((x + insN n i₀ t₀ z) + (t - t₀) • evec n i₀) hZ2 hqd
  have hdisp : rNorm ((x + insN n i₀ t₀ z) + (t - t₀) • evec n i₀
      - (x + insN n i₀ t₀ z)) ^ 2 = |t - t₀| ^ 2 := by
    rw [add_sub_cancel_left, hUnorm]
  have hTay : |formEvalR d n a ((x + insN n i₀ t₀ z) + (t - t₀) • evec n i₀)
      - formEvalR d n a (x + insN n i₀ t₀ z)
      - dotR (gradVec d n a (x + insN n i₀ t₀ z)) ((t - t₀) • evec n i₀)|
      ≤ T * rNorm a * |t - t₀| ^ 2 := by
    rw [hdisp] at htay'
    rwa [add_sub_cancel_left] at htay'
  have hlin : |dotR (gradVec d n a (x + insN n i₀ t₀ z)) ((t - t₀) • evec n i₀)|
      ≤ ((2 * lam + 3 * T) * rNorm a) * |t - t₀| := by
    have h1 : dotR (gradVec d n a (x + insN n i₀ t₀ z)) ((t - t₀) • evec n i₀)
        = (t - t₀) * gradF d n a (x + insN n i₀ t₀ z) i₀ := by
      rw [dotR_smul_right, dotR_evec]
      simp only [gradVec]
    rw [h1, abs_mul]
    calc |t - t₀| * |gradF d n a (x + insN n i₀ t₀ z) i₀|
        ≤ |t - t₀| * ((2 * lam + 3 * T) * rNorm a) :=
          mul_le_mul_of_nonneg_left hderiv (abs_nonneg _)
      _ = ((2 * lam + 3 * T) * rNorm a) * |t - t₀| := by ring
  -- (8) conclusion
  have hass := taylor_assembly a T ((2 * lam + 3 * T) * rNorm a) |t - t₀|
    (x + insN n i₀ t₀ z) ((t - t₀) • evec n i₀) ht₀val hTay hlin
  have hgoal : formEvalR d n a (x + insN n i₀ t z)
      = formEvalR d n a ((x + insN n i₀ t₀ z) + (t - t₀) • evec n i₀) := by
    congr 1
    rw [insN_slice_eq i₀ t z, insN_slice_eq i₀ t₀ z]
    have h2 : t • evec n i₀ = t₀ • evec n i₀ + (t - t₀) • evec n i₀ := by
      rw [← add_smul]
      ring_nf
    rw [h2]
    abel
  rw [hgoal]
  exact sq_lin_le (K := T * rNorm a) (M := (2 * lam + 3 * T) * rNorm a) (δ := δ)
    (ε := ε) (s := |t - t₀|) hTν0 hM0 (abs_nonneg _) hw hδq hδM hass

/-! ## 6. From the slice analysis to the measure of the band -/

lemma volume_band_ne_top (d n : ℕ) (a : Mon d n → ℝ) (γ : ℝ) :
    volume (band d n a γ) ≠ ⊤ := by
  have hsub : band d n a γ ⊆ Metric.closedBall (0 : Fin (n + 1) → ℝ) 1 := by
    intro u hu
    have hru : rNorm u ≤ 1 := hu.1
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact le_trans (norm_le_rNorm u) hru
  refine ne_of_lt (lt_of_le_of_lt (measure_mono hsub) ?_)
  rw [Real.volume_pi_closedBall (0 : Fin (n + 1) → ℝ) (by norm_num : (0 : ℝ) ≤ 1)]
  exact ENNReal.ofReal_lt_top

/-- **Measure bound for the band.**  Under the hypotheses of `slice_exists` (with the box
threshold `ε = 2^d K₀ ‖a‖/γ`), the band of `a` has measure at least `2^{-(n+1)}·2δ·(2A)^n`, so that
`τ(a;γ) ≥ γ δ A^n`. -/
theorem core_bound (d n : ℕ) (a : Mon d n → ℝ) (x : Fin (n + 1) → ℝ) (i₀ : Fin (n + 1))
    (T lam γ ε A B δ : ℝ)
    (hx1 : rNorm x = 1) (hf0 : formEvalR d n a x = 0)
    (hγ : 0 < γ) (hT : 0 < T) (hlam : 0 < lam) (hA : 0 < A) (hB : 0 < B) (hδ : 0 < δ)
    (hδB : δ ≤ B / 2)
    (hbox : B ^ 2 + n * A ^ 2 ≤ 1 / 4)
    (hgrad : rNorm (gradVec d n a x) ≤ 2 * lam * rNorm a)
    (hD : lam * rNorm a / Real.sqrt ((n : ℝ) + 1) ≤ |gradF d n a x i₀|)
    (htay : ∀ p q : Fin (n + 1) → ℝ, rNorm p ≤ 2 → rNorm q ≤ 2 →
        |formEvalR d n a q - formEvalR d n a p - dotR (gradVec d n a p) (q - p)|
          ≤ T * rNorm a * rNorm (q - p) ^ 2)
    (hlip : ∀ u : Fin (n + 1) → ℝ, rNorm u ≤ 1 / 2 →
        |gradF d n a (x + u) i₀ - gradF d n a x i₀| ≤ 3 * T * rNorm a)
    (hsgn : 2 * lam * rNorm a * (Real.sqrt n * A) + T * rNorm a * (B ^ 2 + n * A ^ 2)
        < lam * rNorm a / Real.sqrt ((n : ℝ) + 1) * (B / 2))
    (hε : ε = 2 ^ d * (K0 d n * rNorm a / γ))
    (hδM : ((2 * lam + 3 * T) * rNorm a) * δ ≤ ε / 2)
    (hδq : (T * rNorm a) * δ ^ 2 ≤ ε / 2) :
    γ * δ * A ^ n ≤ tauArch d n a γ := by
  have hslice := slice_exists d n a x i₀ T lam γ ε A B δ hx1 hf0 hγ hT hlam hA hB hδ hδB hbox
    hgrad hD htay hlip hsgn hδM hδq
  -- the slab set and the two other sets
  set S : Set (ℝ × (Fin n → ℝ)) := {p | rNorm (insN n i₀ p.1 p.2) ≤ 1 / 2 ∧
      |formEvalR d n a (x + insN n i₀ p.1 p.2)| ≤ ε} with hSdef
  set V : Set (Fin (n + 1) → ℝ) :=
    {v | rNorm v ≤ 1 / 2 ∧ |formEvalR d n a (x + v)| ≤ ε} with hVdef
  set W : Set (Fin (n + 1) → ℝ) :=
    {w | rNorm w ≤ 1 / 4 ∧ |formEvalR d n a (w + (1 / 2 : ℝ) • x)| ≤ K0 d n * rNorm a / γ}
    with hWdef
  have hSmeas : MeasurableSet S := by
    rw [hSdef]
    have hins : Measurable fun p : ℝ × (Fin n → ℝ) => insN n i₀ p.1 p.2 := by
      have h2 : (fun p : ℝ × (Fin n → ℝ) => insN n i₀ p.1 p.2)
          = ⇑(Fin.insertNthEquiv (fun _ : Fin (n + 1) => ℝ) i₀) := rfl
      rw [h2]
      exact (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i₀).measurable_invFun
    have h1 : Measurable fun p : ℝ × (Fin n → ℝ) => rNorm (insN n i₀ p.1 p.2) :=
      continuous_rNorm.measurable.comp hins
    have h2 : Measurable fun p : ℝ × (Fin n → ℝ) =>
        formEvalR d n a (x + insN n i₀ p.1 p.2) :=
      ((continuous_formEvalR_self d n a).comp (continuous_const.add continuous_id)).measurable.comp hins
    exact (measurableSet_le h1 measurable_const).inter
      (measurableSet_le (continuous_abs.measurable.comp h2) measurable_const)
  have hsec : ∀ z : Fin n → ℝ, (∀ j, |z j| ≤ A) → ∃ t₀ : ℝ, ∀ t : ℝ,
      |t - t₀| ≤ δ → (t, z) ∈ S := by
    intro z hz
    obtain ⟨t₀, ht₀abs, ht₀bound⟩ := hslice z hz
    refine ⟨t₀, fun t ht => ?_⟩
    rw [hSdef]
    refine ⟨?_, ht₀bound t ht⟩
    have htB : |t| ≤ B := by
      have h := abs_add_le t₀ (t - t₀)
      have h2 : t₀ + (t - t₀) = t := by ring
      rw [h2] at h
      linarith
    exact rNorm_insN_le_half i₀ hz htB hbox
  have hslab : ENNReal.ofReal (2 * δ) * (ENNReal.ofReal (2 * A)) ^ n ≤ volume S :=
    HPtau.slab_lower n S hSmeas A δ hA hδ hsec
  -- transfer along the product decomposition
  have htransfer : volume S = volume V := by
    have hEsymm : ∀ p : ℝ × (Fin n → ℝ),
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i₀).symm p
          = insN n i₀ p.1 p.2 := fun p => rfl
    have hpre : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i₀) ⁻¹' S = V := by
      rw [hSdef, hVdef]
      ext v
      have h2 : insN n i₀ ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i₀) v).1
            ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i₀) v).2 = v := by
        rw [← hEsymm _]
        exact (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i₀).symm_apply_apply v
      simp only [Set.mem_preimage, Set.mem_ofPred_eq]
      rw [h2]
    rw [← hpre, ← Measure.map_apply
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i₀).measurable hSmeas,
      (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i₀).map_eq]
  -- scaling `w ↦ 2 w`
  have hx2 : (2 : ℝ) • ((1 / 2 : ℝ) • x) = x := by
    rw [smul_smul]; norm_num
  have hW2 : W = (fun w : Fin (n + 1) → ℝ => (2 : ℝ) • w) ⁻¹' V := by
    rw [hWdef, hVdef, hε]
    ext w
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    have hsplit : x + (2 : ℝ) • w = (2 : ℝ) • (w + (1 / 2 : ℝ) • x) := by
      rw [smul_add, smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul]
      abel
    constructor
    · rintro ⟨hw, hf⟩
      refine ⟨?_, ?_⟩
      · rw [rNorm_smul_of_pos 2 w (by norm_num)]
        linarith
      · rw [hsplit, formEvalR_smul_vec, abs_mul,
          abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ d)]
        exact mul_le_mul_of_nonneg_left hf (by positivity)
    · rintro ⟨hv, hf⟩
      refine ⟨?_, ?_⟩
      · have h := rNorm_smul_of_pos 2 w (by norm_num)
        rw [h] at hv
        linarith
      · have h2 : x + (2 : ℝ) • w = (2 : ℝ) • (w + (1 / 2 : ℝ) • x) := by
          rw [smul_add, smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul]
          abel
        rw [h2, formEvalR_smul_vec, abs_mul,
          abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ d)] at hf
        exact le_of_mul_le_mul_left hf (by positivity)
  have hscale : volume W = ENNReal.ofReal (((2 : ℝ) ^ (n + 1))⁻¹) * volume V := by
    rw [hW2, Measure.addHaar_preimage_smul volume (by norm_num : (2 : ℝ) ≠ 0)]
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
      abs_of_pos (by positivity : (0 : ℝ) < ((2 : ℝ) ^ (n + 1))⁻¹)]
  -- assemble
  have hmain : ENNReal.ofReal (((2 : ℝ) ^ (n + 1))⁻¹) * ENNReal.ofReal (2 * δ)
        * (ENNReal.ofReal (2 * A)) ^ n ≤ volume (band d n a γ) := by
    calc ENNReal.ofReal (((2 : ℝ) ^ (n + 1))⁻¹) * ENNReal.ofReal (2 * δ)
          * (ENNReal.ofReal (2 * A)) ^ n
        ≤ ENNReal.ofReal (((2 : ℝ) ^ (n + 1))⁻¹) * volume S := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left hslab (by simp : (0 : ℝ≥0∞) ≤ _)
      _ = ENNReal.ofReal (((2 : ℝ) ^ (n + 1))⁻¹) * volume V := by rw [htransfer]
      _ = volume W := hscale.symm
      _ ≤ volume (band d n a γ) := by
          rw [hWdef]
          exact volume_sub_band d n a x γ hx1 hγ
  have hfin := volume_band_ne_top d n a γ
  have hreal : ((2 : ℝ) ^ (n + 1))⁻¹ * (2 * δ) * (2 * A) ^ n
      ≤ (volume (band d n a γ)).toReal := by
    have h1 : ENNReal.ofReal (((2 : ℝ) ^ (n + 1))⁻¹ * (2 * δ) * (2 * A) ^ n)
        ≤ volume (band d n a γ) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_pow (by positivity)]
      exact hmain
    have h2 := ENNReal.toReal_mono hfin h1
    rwa [ENNReal.toReal_ofReal (by positivity)] at h2
  have harith : ((2 : ℝ) ^ (n + 1))⁻¹ * (2 * δ) * (2 * A) ^ n = δ * A ^ n := by
    have h2 : ((2 : ℝ) ^ (n + 1))⁻¹ = (1 / 2) * ((2 : ℝ) ^ n)⁻¹ := by
      rw [pow_succ', mul_inv]
      norm_num
    rw [h2, mul_pow]
    field_simp
  rw [harith] at hreal
  rw [tauArch_eq]
  nlinarith [hreal, hγ]

/-! ## 7. Assembly -/


/-! ## 7. The constant bookkeeping -/

/-- `δ₁ ≥ Kc Λ/γ`. -/
lemma d1_estimate {K0d T mu Kc lam γ : ℝ} (hK0 : 0 < K0d) (hT : 0 < T) (hmu : 0 < mu)
    (hγ : 0 < γ) (hKc : 0 ≤ Kc) (hlam : 0 < lam) (hlamμ : lam ≤ mu)
    (h1 : Kc ≤ 2 ^ d * K0d / (2 * (2 + 3 * T)))
    (h2 : Kc ≤ 2 ^ d * K0d / (2 * (2 * mu + 3 * T))) :
    Kc * min lam 1 / γ ≤ 2 ^ d * K0d / (2 * γ * (2 * lam + 3 * T)) := by
  have hkey : Kc * min lam 1 ≤ 2 ^ d * K0d / (2 * (2 * lam + 3 * T)) := by
    rcases le_or_gt lam 1 with hle | hgt
    · rw [min_eq_left hle]
      have h3 : 2 ^ d * K0d / (2 * (2 + 3 * T)) * lam
          ≤ 2 ^ d * K0d / (2 * (2 * lam + 3 * T)) := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by linarith) (by linarith)]
        have hquad : lam * (2 * lam + 3 * T) ≤ 2 + 3 * T := by
          have h1 : lam * lam ≤ 1 := by nlinarith [hle, hlam]
          nlinarith [h1, hle, hT, hlam]
        have h4 : 0 < 2 ^ d * K0d := mul_pos (pow_pos (by norm_num) d) hK0
        nlinarith [mul_le_mul_of_nonneg_left hquad h4.le]
      exact (mul_le_mul_of_nonneg_right h1 hlam.le).trans h3
    · rw [min_eq_right hgt.le, mul_one]
      have h3 : 2 ^ d * K0d / (2 * (2 * mu + 3 * T)) ≤ 2 ^ d * K0d / (2 * (2 * lam + 3 * T)) := by
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        have h4 : 0 < 2 ^ d * K0d := mul_pos (pow_pos (by norm_num) d) hK0
        nlinarith [h4, hT, hlamμ]
      exact h2.trans h3
  calc Kc * min lam 1 / γ ≤ (2 ^ d * K0d / (2 * (2 * lam + 3 * T))) / γ :=
        div_le_div_of_nonneg_right hkey hγ.le
    _ = 2 ^ d * K0d / (2 * γ * (2 * lam + 3 * T)) := by field_simp; try ring

/-- `δ₂ ≥ Kc Λ/γ`. -/
lemma d2_estimate {K0d T Kc lam γ : ℝ} (hK0 : 0 < K0d) (hT : 0 < T) (hγ : 0 < γ)
    (hγ1 : 1 ≤ γ) (hKc : 0 ≤ Kc) (hlam : 0 < lam)
    (h1 : Kc ≤ Real.sqrt (2 ^ d * K0d / (2 * T))) :
    Kc * min lam 1 / γ ≤ Real.sqrt (2 ^ d * K0d / (2 * T * γ)) := by
  have h4 : Kc ≤ Real.sqrt (2 ^ d * K0d / (2 * T * γ)) * γ := by
    have h3 : Real.sqrt (2 ^ d * K0d * γ / (2 * T))
        = Real.sqrt (2 ^ d * K0d / (2 * T * γ)) * γ := by
      rw [show 2 ^ d * K0d * γ / (2 * T) = (2 ^ d * K0d / (2 * T * γ)) * γ ^ 2 by
        field_simp
        try ring]
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hγ.le]
    rw [← h3]
    refine h1.trans (Real.sqrt_le_sqrt ?_)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hc : 0 ≤ 2 ^ d * K0d * (2 * T) := by
      have h2 : (0 : ℝ) < 2 ^ d := pow_pos (by norm_num) d
      positivity
    nlinarith [mul_le_mul_of_nonneg_left hγ1 hc]
  have h5 : Kc / γ ≤ Real.sqrt (2 ^ d * K0d / (2 * T * γ)) := by
    rw [div_le_iff₀ hγ]
    linarith [h4]
  calc Kc * min lam 1 / γ = (Kc / γ) * min lam 1 := by ring
    _ ≤ (Kc / γ) * 1 := mul_le_mul_of_nonneg_left (min_le_right _ _) (div_nonneg hKc hγ.le)
    _ = Kc / γ := by ring
    _ ≤ _ := h5

/-- `B/2 ≥ Kc Λ/γ`. -/
lemma B_estimate {Kc c₂ lam γ : ℝ} (hc₂ : 0 < c₂) (hγ : 0 < γ) (hγ1 : 1 ≤ γ)
    (hKc : 0 ≤ Kc) (hlam : 0 < lam) (h1 : Kc ≤ c₂ / 2) :
    Kc * min lam 1 / γ ≤ c₂ * min lam 1 / 2 := by
  have h2 : Kc / γ ≤ c₂ / 2 := by
    rw [div_le_iff₀ hγ]
    nlinarith [h1, hγ1]
  calc Kc * min lam 1 / γ = (Kc / γ) * min lam 1 := by ring
    _ ≤ (c₂ / 2) * min lam 1 :=
        mul_le_mul_of_nonneg_right h2 (le_min hlam.le zero_le_one)
    _ = c₂ * min lam 1 / 2 := by ring

/-- The final case distinction on `λ ≤ 1` versus `λ ≥ 1`. -/
lemma final_estimate {Kc c₁ lam mu : ℝ} {n : ℕ} (hn : 1 ≤ n) (hKc : 0 ≤ Kc) (hc₁ : 0 ≤ c₁)
    (hlam : 0 < lam) (hmu : 0 < mu) (hlamμ : lam ≤ mu) :
    Kc * c₁ ^ n / (max 1 mu) ^ (n - 1) * min (lam ^ (n + 1)) (lam ^ (n - 1))
      ≤ Kc * c₁ ^ n * (min lam 1) ^ (n + 1) := by
  have hKcn : 0 ≤ Kc * c₁ ^ n := mul_nonneg hKc (pow_nonneg hc₁ n)
  rcases le_or_gt lam 1 with hle | hgt
  · rw [min_eq_left hle, min_eq_left (pow_le_pow_of_le_one hlam.le hle (by omega))]
    have h1 : Kc * c₁ ^ n / (max 1 mu) ^ (n - 1) ≤ Kc * c₁ ^ n := by
      rw [div_le_iff₀ (pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _)]
      have h2 : (1 : ℝ) ≤ (max 1 mu) ^ (n - 1) := one_le_pow₀ (le_max_left _ _)
      nlinarith [hKcn]
    exact mul_le_mul_of_nonneg_right h1 (pow_nonneg hlam.le _)
  · rw [min_eq_right hgt.le, one_pow, mul_one,
      min_eq_right (pow_le_pow_right₀ hgt.le (by omega))]
    have hmax : max 1 mu = mu := max_eq_right (le_trans hgt.le hlamμ)
    rw [hmax]
    have h3 : lam ^ (n - 1) ≤ mu ^ (n - 1) := pow_le_pow_left₀ hlam.le hlamμ _
    have h4 : Kc * c₁ ^ n / mu ^ (n - 1) * lam ^ (n - 1)
        ≤ Kc * c₁ ^ n / mu ^ (n - 1) * mu ^ (n - 1) :=
      mul_le_mul_of_nonneg_left h3 (div_nonneg hKcn (pow_nonneg hmu.le _))
    have h5 : Kc * c₁ ^ n / mu ^ (n - 1) * mu ^ (n - 1) = Kc * c₁ ^ n := by
      rw [div_mul_cancel₀]
      exact pow_ne_zero _ hmu.ne'
    linarith [h4, h5]

/-- **Constant bookkeeping.**  Choosing the box parameters `A = c₁ min(λ,1)`, `B = c₂ min(λ,1)`,
the thickness `δ` and the threshold `ε = 2^d K₀‖a‖/γ` as in `core_bound`, `τ(a;γ)` is bounded
below by `K min(λ^{n+1}, λ^{n-1})` uniformly in `λ ∈ (0,μ]` and `γ ≥ 1`. -/
theorem core_all (d n : ℕ) (hd : 2 ≤ d) (hn : 3 ≤ n) (T mu : ℝ) (hT : 0 < T) (hmu : 0 < mu) :
    ∃ Kf : ℝ, 0 < Kf ∧ ∀ (a : Mon d n → ℝ) (x : Fin (n + 1) → ℝ) (i₀ : Fin (n + 1))
      (lam γ : ℝ),
      0 < lam → lam ≤ mu → 1 ≤ γ → rNorm x = 1 → formEvalR d n a x = 0 → 0 < rNorm a →
      rNorm (gradVec d n a x) ≤ 2 * lam * rNorm a →
      lam * rNorm a / Real.sqrt ((n : ℝ) + 1) ≤ |gradF d n a x i₀| →
      (∀ p q : Fin (n + 1) → ℝ, rNorm p ≤ 2 → rNorm q ≤ 2 →
        |formEvalR d n a q - formEvalR d n a p - dotR (gradVec d n a p) (q - p)|
          ≤ T * rNorm a * rNorm (q - p) ^ 2) →
      (∀ u : Fin (n + 1) → ℝ, rNorm u ≤ 1 / 2 →
        |gradF d n a (x + u) i₀ - gradF d n a x i₀| ≤ 3 * T * rNorm a) →
      Kf * min (lam ^ (n + 1)) (lam ^ (n - 1)) ≤ tauArch d n a γ := by
  obtain ⟨c₁, c₂, hc₁, hc₂, hc₂eq, hboxc, hsignc⟩ := HPtau.scale_consts n hn T hT
  have hK0 := K0_pos d n
  have h2d : (0 : ℝ) < 2 ^ d := pow_pos (by norm_num) d
  set Kc : ℝ := min (2 ^ d * K0 d n / (2 * (2 + 3 * T)))
    (min (2 ^ d * K0 d n / (2 * (2 * mu + 3 * T)))
      (min (Real.sqrt (2 ^ d * K0 d n / (2 * T))) (c₂ / 2))) with hKcdef
  have hKc1 : Kc ≤ 2 ^ d * K0 d n / (2 * (2 + 3 * T)) := by
    rw [hKcdef]; exact min_le_left _ _
  have hKc2 : Kc ≤ 2 ^ d * K0 d n / (2 * (2 * mu + 3 * T)) := by
    rw [hKcdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hKc3 : Kc ≤ Real.sqrt (2 ^ d * K0 d n / (2 * T)) := by
    rw [hKcdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hKc4 : Kc ≤ c₂ / 2 := by
    rw [hKcdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hKc0 : 0 < Kc := by
    rw [hKcdef]
    refine lt_min (div_pos (mul_pos h2d hK0) (by linarith))
      (lt_min (div_pos (mul_pos h2d hK0) (by linarith))
        (lt_min (Real.sqrt_pos.mpr (div_pos (mul_pos h2d hK0)
          (mul_pos (by norm_num) hT))) (by linarith)))
  refine ⟨Kc * c₁ ^ n / (max 1 mu) ^ (n - 1), ?_, ?_⟩
  · refine div_pos (mul_pos hKc0 (pow_pos hc₁ n)) (pow_pos ?_ _)
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  intro a x i₀ lam γ hlam hlamμ hγ hx1 hf0 hν hgrad hD htay hlip
  have hγ0 : 0 < γ := lt_of_lt_of_le zero_lt_one hγ
  set Lam : ℝ := min lam 1 with hLamdef
  have hLam0 : 0 < Lam := lt_min hlam one_pos
  have hLamle1 : Lam ≤ 1 := min_le_right _ _
  have hLamle : Lam ≤ lam := min_le_left _ _
  set A : ℝ := c₁ * Lam with hAdef
  set B : ℝ := c₂ * Lam with hBdef
  have hA0 : 0 < A := mul_pos hc₁ hLam0
  have hB0 : 0 < B := mul_pos hc₂ hLam0
  set eps : ℝ := 2 ^ d * (K0 d n * rNorm a / γ) with hepsdef
  have heps0 : 0 < eps := by
    rw [hepsdef]
    exact mul_pos h2d (div_pos (mul_pos hK0 hν) hγ0)
  have hM0 : 0 < (2 * lam + 3 * T) * rNorm a := mul_pos (by linarith) hν
  have hTν : 0 < T * rNorm a := mul_pos hT hν
  set d1 : ℝ := eps / (2 * ((2 * lam + 3 * T) * rNorm a)) with hd1def
  set d2 : ℝ := Real.sqrt (eps / (2 * (T * rNorm a))) with hd2def
  set dlt : ℝ := min d1 (min d2 (B / 2)) with hdltdef
  have hd10 : 0 < d1 := div_pos heps0 (mul_pos (by norm_num) hM0)
  have hd20 : 0 < d2 := Real.sqrt_pos.mpr (div_pos heps0 (mul_pos (by norm_num) hTν))
  have hdlt0 : 0 < dlt := by
    rw [hdltdef]; exact lt_min hd10 (lt_min hd20 (by linarith))
  have hdltB : dlt ≤ B / 2 := by
    rw [hdltdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  -- the box condition
  have hLam2 : Lam ^ 2 ≤ 1 := by nlinarith [hLam0.le, hLamle1]
  have hbox : B ^ 2 + n * A ^ 2 ≤ 1 / 4 := by
    have h1 : B ^ 2 + n * A ^ 2 = Lam ^ 2 * (c₂ ^ 2 + n * c₁ ^ 2) := by
      rw [hAdef, hBdef]; ring
    rw [h1]
    have hnn : 0 ≤ c₂ ^ 2 + n * c₁ ^ 2 := by nlinarith [sq_nonneg c₁, sq_nonneg c₂, (Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    nlinarith [hboxc, hLam2, hnn, mul_le_mul_of_nonneg_left hLam2 hnn]
  -- the sign condition
  have hfac : (lam * rNorm a * Lam) * (2 * Real.sqrt n * c₁ + T * (c₂ ^ 2 + n * c₁ ^ 2))
      - (2 * lam * rNorm a * (Real.sqrt n * A) + T * rNorm a * (B ^ 2 + n * A ^ 2))
      = T * rNorm a * (c₂ ^ 2 + n * c₁ ^ 2) * Lam * (lam - Lam) := by
    rw [hAdef, hBdef]; ring
  have hnn : 0 ≤ T * rNorm a * (c₂ ^ 2 + n * c₁ ^ 2) * Lam * (lam - Lam) := by
    have h1 : (0 : ℝ) ≤ T * rNorm a := mul_nonneg hT.le hν.le
    have h2 : (0 : ℝ) ≤ c₂ ^ 2 + n * c₁ ^ 2 := by
      nlinarith [sq_nonneg c₁, sq_nonneg c₂, (Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    have h3 : (0 : ℝ) ≤ lam - Lam := sub_nonneg.mpr hLamle
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) hLam0.le) h3
  have hsgn : 2 * lam * rNorm a * (Real.sqrt n * A) + T * rNorm a * (B ^ 2 + n * A ^ 2)
      < lam * rNorm a / Real.sqrt ((n : ℝ) + 1) * (B / 2) := by
    have h2 : (lam * rNorm a * Lam) * ((1 / Real.sqrt ((n : ℝ) + 1)) * c₂ / 2)
        > (lam * rNorm a * Lam) * (2 * Real.sqrt n * c₁ + T * (c₂ ^ 2 + n * c₁ ^ 2)) :=
      mul_lt_mul_of_pos_left hsignc (mul_pos (mul_pos hlam hν) hLam0)
    have h3 : lam * rNorm a / Real.sqrt ((n : ℝ) + 1) * (B / 2)
        = (lam * rNorm a * Lam) * ((1 / Real.sqrt ((n : ℝ) + 1)) * c₂ / 2) := by
      rw [hBdef]; field_simp; try ring
    linarith [h2, h3, hfac, hnn]
  -- the thickness conditions
  have hd1half : eps / 2 = ((2 * lam + 3 * T) * rNorm a) * d1 := by
    rw [hd1def]; field_simp; try ring
  have hdltM : ((2 * lam + 3 * T) * rNorm a) * dlt ≤ eps / 2 := by
    have h1 : dlt ≤ d1 := by rw [hdltdef]; exact min_le_left _ _
    have h2 : ((2 * lam + 3 * T) * rNorm a) * dlt ≤ ((2 * lam + 3 * T) * rNorm a) * d1 :=
      mul_le_mul_of_nonneg_left h1 hM0.le
    rw [← hd1half] at h2
    linarith [h2]
  have hdltq : (T * rNorm a) * dlt ^ 2 ≤ eps / 2 := by
    have h1 : dlt ≤ d2 := by rw [hdltdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
    have h2 : dlt ^ 2 ≤ d2 ^ 2 := pow_le_pow_left₀ hdlt0.le h1 2
    have h3 : d2 ^ 2 = eps / (2 * (T * rNorm a)) := by
      rw [hd2def, Real.sq_sqrt (div_nonneg heps0.le (by positivity))]
    have h4 : (T * rNorm a) * d2 ^ 2 = eps / 2 := by
      rw [h3]; field_simp; try ring
    have h5 : (T * rNorm a) * dlt ^ 2 ≤ (T * rNorm a) * d2 ^ 2 :=
      mul_le_mul_of_nonneg_left h2 hTν.le
    linarith [h4, h5]
  -- the main estimate
  have hcore := core_bound d n a x i₀ T lam γ eps A B dlt hx1 hf0 hγ0 hT hlam hA0 hB0 hdlt0
    hdltB hbox hgrad hD htay hlip hsgn hepsdef hdltM hdltq
  -- the three elementary bounds on `dlt`
  have hd1eq : d1 = 2 ^ d * K0 d n / (2 * γ * (2 * lam + 3 * T)) := by
    rw [hd1def, hepsdef]; field_simp; try ring
  have hd2eq : d2 = Real.sqrt (2 ^ d * K0 d n / (2 * T * γ)) := by
    rw [hd2def, hepsdef]
    congr 1
    field_simp
    try ring
  have hKdlt : Kc * Lam / γ ≤ dlt := by
    refine le_min ?_ (le_min ?_ ?_)
    · rw [hd1eq]
      exact d1_estimate hK0 hT hmu hγ0 hKc0.le hlam hlamμ hKc1 hKc2
    · rw [hd2eq]
      exact d2_estimate hK0 hT hγ0 hγ hKc0.le hlam hKc3
    · rw [hBdef, hLamdef]
      exact B_estimate hc₂ hγ0 hγ hKc0.le hlam hKc4
  -- the final arithmetic
  have hgoal : Kc * c₁ ^ n * Lam ^ (n + 1) ≤ tauArch d n a γ := by
    have h1 : γ * (Kc * Lam / γ) * (c₁ * Lam) ^ n ≤ γ * (dlt * A ^ n) := by
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hγ0.le
      exact mul_le_mul hKdlt (le_refl _) (pow_nonneg (mul_nonneg hc₁.le hLam0.le) n) hdlt0.le
    have h2 : Kc * c₁ ^ n * Lam ^ (n + 1) = γ * (Kc * Lam / γ) * (c₁ * Lam) ^ n := by
      field_simp
      try ring
    rw [h2]
    calc γ * (Kc * Lam / γ) * (c₁ * Lam) ^ n ≤ γ * (dlt * A ^ n) := h1
      _ = γ * dlt * A ^ n := by ring
      _ ≤ tauArch d n a γ := hcore
  have hAfinal : Kc * c₁ ^ n * (min lam 1) ^ (n + 1) ≤ tauArch d n a γ := by
    rw [hLamdef] at hgoal
    exact hgoal
  have hfinal := final_estimate (Kc := Kc) (c₁ := c₁) (n := n) (by omega) hKc0.le hc₁.le
    hlam hmu hlamμ
  exact le_trans hfinal hAfinal

/-- **Main lower bound for the Archimedean factor.** -/
theorem tau_lower_all (d n : ℕ) (hd : 2 ≤ d) (hn : 3 ≤ n)
    (hgrad : ∃ C, 0 < C ∧ ∀ (a : Mon d n → ℝ) (x : Fin (n + 1) → ℝ), rNorm x ≤ 1 →
        rNorm (gradVec d n a x) ≤ C * rNorm a)
    (htay : ∃ C, 0 < C ∧ ∀ (a : Mon d n → ℝ) (x y : Fin (n + 1) → ℝ), rNorm x ≤ 2 → rNorm y ≤ 2 →
        |formEvalR d n a y - formEvalR d n a x - dotR (gradVec d n a x) (y - x)|
          ≤ C * rNorm a * (rNorm (y - x)) ^ 2)
    (hball : (∀ (r : ℝ) (x : Mon d n → ℝ), 0 ≤ r →
          volume {w : Mon d n → ℝ | rNorm (w - x) ≤ r}
            = ENNReal.ofReal (r ^ NN d n) * volume {w : Mon d n → ℝ | rNorm w ≤ 1}) ∧
        (0 < volume {w : Mon d n → ℝ | rNorm w ≤ 1})) :
    ∃ K : ℝ, 0 < K ∧ ∀ (a : Mon d n → ℝ) (lam γ : ℝ), 0 < lam → 1 ≤ γ → a ∈ Bset d n lam →
      K * min (lam ^ (n + 1)) (lam ^ (n - 1)) ≤ tauArch d n a γ := by
  obtain ⟨mu, hmu, hgrad'⟩ := hgrad
  obtain ⟨T, hT, htay'⟩ := htay
  obtain ⟨Kf, hKf, hcore⟩ := core_all d n hd hn T mu hT hmu
  refine ⟨Kf, hKf, ?_⟩
  intro a lam γ hlam hγ ha
  obtain ⟨ha1, -, x, hx1, hfx, hgl, hgu⟩ := ha
  have hν : 0 < rNorm a := by nlinarith [hgl, hgu, hlam]
  have hlamμ : lam ≤ mu := by
    have h2 : rNorm (gradVec d n a x) ≤ mu * rNorm a := hgrad' a x (le_of_eq hx1)
    nlinarith [hgl, h2, hν]
  obtain ⟨j, hj⟩ := exists_max_abs (fun i : Fin (n + 1) => gradF d n a x i)
  have hD : lam * rNorm a / Real.sqrt ((n : ℝ) + 1) ≤ |gradF d n a x j| := by
    have h2 : rNorm (gradVec d n a x) ≤ Real.sqrt ((n : ℝ) + 1) * |gradF d n a x j| := hj
    have h3 : lam * rNorm a / Real.sqrt ((n : ℝ) + 1)
        < rNorm (gradVec d n a x) / Real.sqrt ((n : ℝ) + 1) := by
      rw [div_lt_div_iff_of_pos_right (by positivity : (0:ℝ) < Real.sqrt ((n:ℝ) + 1))]
      exact hgl
    have h4 : rNorm (gradVec d n a x) / Real.sqrt ((n : ℝ) + 1) ≤ |gradF d n a x j| := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < Real.sqrt ((n:ℝ) + 1))]
      linarith
    linarith
  have hlip : ∀ u : Fin (n + 1) → ℝ, rNorm u ≤ 1 / 2 →
      |gradF d n a (x + u) j - gradF d n a x j| ≤ 3 * T * rNorm a :=
    fun u hu => gradF_lip_const d n a T hT.le (htay' a) x u j (le_of_eq hx1) hu
  exact hcore a x j lam γ hlam hlamμ hγ hx1 hfx hν hgu hD (htay' a) hlip

end Work.HP
