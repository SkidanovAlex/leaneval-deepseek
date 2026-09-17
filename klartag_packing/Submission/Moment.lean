import Mathlib
import Submission.Contact
import Submission.Rescale
import Submission.Rank
import Submission.Commons.MeasureTheory.Integral.integral_pi_fin_succAbove

/-!
# Moments of the state of the exploration process

`Submission/PLAN_V7.md` §2b needs two moment identities for the state

    H_K := A_K - a₀ · Id = ∑_{j < K} ε · π_j ξ_j

of the exploration process (the sum is exact, see `GenProc.proc_eq_sum`):

* the mean of `H_K` in the inner product with the identity matrix vanishes,
  `E ⟪Id, H_K⟫ = 0` (this is what makes the first-order term of the Taylor expansion of
  `log det` disappear), and
* `E ‖H_K‖² = ε² ∑_{j < K} E N_j`, where `N_j = dim F_j` is the dimension of the constraint
  space at time `j`.

Both are proved by an induction that peels off the **last** Gaussian coordinate, using the
product structure of `sampleLaw`.  For the last coordinate the constraint projection `π_K`
and the past state are functions of the other coordinates only, and the mean of a linear
functional of a centred Gaussian vanishes.
-/

namespace Submission.Moment

open Matrix MeasureTheory ProbabilityTheory
open Submission.MatSpace
open Submission.MatBridge
open Submission.GenProc
open Submission.Contact
open Submission.Rank

noncomputable section

variable {d : ℕ}

/-- Forget the last coordinate of a sample. -/
def dropLast {α : Type*} {K : ℕ} (ω : Fin (K + 1) → α) : Fin K → α := fun j => ω j.castSucc

@[simp] lemma dropLast_apply {α : Type*} {K : ℕ} (ω : Fin (K + 1) → α) (j : Fin K) :
    dropLast ω j = ω j.castSucc := rfl

lemma dropLast_measurable {α : Type*} [MeasurableSpace α] {K : ℕ} :
    Measurable (dropLast (α := α) (K := K)) :=
  Measurable.of_eval (fun j => measurable_pi_apply _)

/-- The second component of `MeasurableEquiv.piFinSuccAbove` at the last index is `dropLast`. -/
lemma piFinSuccAbove_last_snd {α : Type*} [MeasurableSpace α] {K : ℕ}
    (ω : Fin (K + 1) → α) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (K + 1) => α) (Fin.last K) ω).2
      = dropLast ω := by
  rw [show MeasurableEquiv.piFinSuccAbove (fun _ : Fin (K + 1) => α) (Fin.last K) ω
      = (Fin.insertNthEquiv (fun _ : Fin (K + 1) => α) (Fin.last K)).symm ω from rfl,
    Fin.insertNthEquiv_symm_apply]
  funext j
  show (Fin.removeNth (Fin.last K) ω) j = dropLast ω j
  rw [Fin.removeNth_apply, Fin.succAbove_last_apply]
  rfl

/-- The first component of `MeasurableEquiv.piFinSuccAbove` at the last index is evaluation. -/
lemma piFinSuccAbove_last_fst {α : Type*} [MeasurableSpace α] {K : ℕ}
    (ω : Fin (K + 1) → α) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (K + 1) => α) (Fin.last K) ω).1
      = ω (Fin.last K) := by
  rw [show MeasurableEquiv.piFinSuccAbove (fun _ : Fin (K + 1) => α) (Fin.last K) ω
      = (Fin.insertNthEquiv (fun _ : Fin (K + 1) => α) (Fin.last K)).symm ω from rfl,
    Fin.insertNthEquiv_symm_apply]

/-- The process at time `k ≤ K` only depends on the first `k` coordinates; hence forgetting the
last coordinate does not change it. -/
lemma proc_dropLast (pl : MatV d → MatV d →L[ℝ] MatV d) (a₀ ε : ℝ) (K k : ℕ) (hk : k ≤ K)
    (ω : Fin (K + 1) → MatV d × MatV d) :
    proc pl a₀ ε (K + 1) ω k = proc pl a₀ ε K (dropLast ω) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hkK : k < K := by omega
    have hkK' : k < K + 1 := by omega
    have hω : ω ⟨k, hkK'⟩ = (dropLast ω) ⟨k, hkK⟩ := by
      rw [show (⟨k, hkK'⟩ : Fin (K + 1)) = (⟨k, hkK⟩ : Fin K).castSucc from Fin.ext rfl,
        dropLast_apply]
    rw [proc_succ, proc_succ]
    simp only [hkK, hkK', dif_pos]
    rw [ih (by omega), hω]

/-- The state `A_k - a₀·Id` of the process. -/
def stateK (pl : MatV d → MatV d →L[ℝ] MatV d) (a₀ ε : ℝ) (K : ℕ)
    (ω : Fin K → MatV d × MatV d) : MatV d :=
  proc pl a₀ ε K ω K - a₀ • oneV d

/-- The recursion of the state, peeling the last coordinate. -/
lemma stateK_succ (pl : MatV d → MatV d →L[ℝ] MatV d) (a₀ ε : ℝ) (K : ℕ)
    (ω : Fin (K + 1) → MatV d × MatV d) :
    stateK pl a₀ ε (K + 1) ω
      = stateK pl a₀ ε K (dropLast ω)
        + ε • (pl (proc pl a₀ ε K (dropLast ω) K)) (ω (Fin.last K)).1 := by
  unfold stateK
  rw [show proc pl a₀ ε (K + 1) ω (K + 1)
      = step pl ε (proc pl a₀ ε (K + 1) ω K) (ω (Fin.last K)).1 from by
    rw [proc_succ]
    simp only [Nat.lt_succ_self, dif_pos]
    congr 1]
  rw [proc_dropLast pl a₀ ε K K le_rfl ω]
  simp only [step]
  abel

/-! ## Integrability and the Fubini step -/

section Moment

variable {m : ℕ} (R : ℝ) (BoxL : Fin m → Vec d) (a₀ ε : ℝ)

/-- The law of the Gaussian sample is a probability measure; each coordinate of the first
component is a standard Gaussian. -/
lemma integrable_eval_norm (K : ℕ) (j : Fin K) :
    Integrable (fun u : Fin K → MatV d × MatV d => ‖(u j).1‖) (sampleLaw d K) := by
  have hg : AEMeasurable (fun u : Fin K → MatV d × MatV d => (u j).1) (sampleLaw d K) :=
    ((measurable_pi_apply j).fst).aemeasurable
  have hnorm : Integrable (fun x : MatV d => ‖x‖) (ProbabilityTheory.stdGaussian (MatV d)) :=
    ((ProbabilityTheory.IsGaussian.memLp_id (ProbabilityTheory.stdGaussian (MatV d)) 1
      (by norm_num)).integrable (by norm_num)).norm
  have h1 : Integrable (fun x : MatV d => ‖x‖)
      ((sampleLaw d K).map (fun u : Fin K → MatV d × MatV d => (u j).1)) := by
    rw [Submission.Rescale.sampleLaw_map_fst]; exact hnorm
  exact (MeasureTheory.integrable_map_measure (continuous_norm.measurable.aestronglyMeasurable)
    hg).mp h1

lemma integrable_eval_norm_sq (K : ℕ) (j : Fin K) :
    Integrable (fun u : Fin K → MatV d × MatV d => ‖(u j).1‖ ^ 2) (sampleLaw d K) := by
  have hg : AEMeasurable (fun u : Fin K → MatV d × MatV d => (u j).1) (sampleLaw d K) :=
    ((measurable_pi_apply j).fst).aemeasurable
  have hnorm : Integrable (fun x : MatV d => ‖x‖ ^ 2) (ProbabilityTheory.stdGaussian (MatV d)) :=
    (ProbabilityTheory.IsGaussian.memLp_id (ProbabilityTheory.stdGaussian (MatV d)) 2
      (by norm_num)).integrable_norm_pow (p := 2) (by norm_num)
  have h1 : Integrable (fun x : MatV d => ‖x‖ ^ 2)
      ((sampleLaw d K).map (fun u : Fin K → MatV d × MatV d => (u j).1)) := by
    rw [Submission.Rescale.sampleLaw_map_fst]; exact hnorm
  exact (MeasureTheory.integrable_map_measure ((continuous_norm.pow 2).measurable.aestronglyMeasurable)
    hg).mp h1

/-- The state is a sum of the increments. -/
lemma stateK_eq_sum (K : ℕ) (ω : Fin K → MatV d × MatV d) :
    stateK (projL R BoxL) a₀ ε K ω
      = ∑ j : Fin K, ε • incrAt (projL R BoxL) a₀ ε K ω j := by
  unfold stateK
  rw [proc_eq_sum (pl := projL R BoxL) (a₀ := a₀) (ε := ε) (K := K) le_rfl ω]
  rw [show (Finset.univ.filter (fun j : Fin K => (j : ℕ) < K)) = Finset.univ from by
    ext j; simp]
  abel

/-- Pointwise bound of the state by the sample. -/
lemma norm_stateK_le (K : ℕ) (hε : 0 ≤ ε) (ω : Fin K → MatV d × MatV d) :
    ‖stateK (projL R BoxL) a₀ ε K ω‖ ≤ ∑ j : Fin K, ε * ‖(ω j).1‖ := by
  rw [stateK_eq_sum]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_smul, Real.norm_of_nonneg hε]
  refine mul_le_mul_of_nonneg_left ?_ hε
  rw [incrAt, projAt]
  exact Submission.Rescale.norm_projL_apply_le R BoxL _ _

/-- Measurability of the state. -/
lemma measurable_stateK (K : ℕ) :
    Measurable fun ω : Fin K → MatV d × MatV d => stateK (projL R BoxL) a₀ ε K ω :=
  ((measurable_proc (pl := projL R BoxL) (a₀ := a₀) (ε := ε) (K := K)
      (measurable_projL R BoxL) K)).sub measurable_const

lemma integrable_stateK_norm (K : ℕ) (hε : 0 ≤ ε) :
    Integrable (fun ω : Fin K → MatV d × MatV d => ‖stateK (projL R BoxL) a₀ ε K ω‖)
      (sampleLaw d K) := by
  have hmaj : Integrable (fun ω : Fin K → MatV d × MatV d =>
      ∑ j : Fin K, ε * ‖(ω j).1‖) (sampleLaw d K) :=
    MeasureTheory.integrable_finsetSum (s := Finset.univ) (fun j _ =>
      (integrable_eval_norm (d := d) K j).const_mul ε)
  refine MeasureTheory.Integrable.mono' hmaj
    (measurable_stateK R BoxL a₀ ε K).norm.aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact norm_stateK_le R BoxL a₀ ε K hε ω

lemma integrable_stateK_norm_sq (K : ℕ) (hε : 0 ≤ ε) :
    Integrable (fun ω : Fin K → MatV d × MatV d => ‖stateK (projL R BoxL) a₀ ε K ω‖ ^ 2)
      (sampleLaw d K) := by
  refine MeasureTheory.Integrable.mono'
    (f := fun ω : Fin K → MatV d × MatV d => ‖stateK (projL R BoxL) a₀ ε K ω‖ ^ 2)
    (g := fun ω : Fin K → MatV d × MatV d => ∑ j : Fin K, (K : ℝ) * ε ^ 2 * ‖(ω j).1‖ ^ 2)
    ?_ ?_ ?_
  · exact MeasureTheory.integrable_finsetSum (s := Finset.univ) (fun j _ =>
      (integrable_eval_norm_sq (d := d) K j).const_mul ((K : ℝ) * ε ^ 2))
  · exact ((measurable_stateK R BoxL a₀ ε K).norm.pow_const 2).aestronglyMeasurable
  · filter_upwards with ω
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h1 : ‖stateK (projL R BoxL) a₀ ε K ω‖ ^ 2
        ≤ (∑ j : Fin K, ε * ‖(ω j).1‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_stateK_le R BoxL a₀ ε K hε ω) 2
    refine h1.trans ?_
    have h2 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin K)))
      (f := fun j => ε * ‖(ω j).1‖)
    rw [Finset.card_univ, Fintype.card_fin] at h2
    refine h2.trans (le_of_eq ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

/-! ## The Fubini step -/

/-- Peeling off the last coordinate of the sample. -/
theorem integral_pi_last {K : ℕ}
    (g : (Fin K → MatV d × MatV d) → (MatV d × MatV d) → ℝ)
    (hg : MeasureTheory.Integrable
      (fun p : (Fin K → MatV d × MatV d) × (MatV d × MatV d) => g p.1 p.2)
      ((sampleLaw d K).prod ((ProbabilityTheory.stdGaussian (MatV d)).prod
        (ProbabilityTheory.stdGaussian (MatV d))))) :
    (∫ ω : Fin (K + 1) → MatV d × MatV d, g (dropLast ω) (ω (Fin.last K))
        ∂(sampleLaw d (K + 1)))
      = ∫ u, ∫ a, g u a ∂((ProbabilityTheory.stdGaussian (MatV d)).prod
          (ProbabilityTheory.stdGaussian (MatV d))) ∂(sampleLaw d K) := by
  have h := Commons.MeasureTheory.Integral.integral_pi_fin_succAbove
    (ν := (ProbabilityTheory.stdGaussian (MatV d)).prod (ProbabilityTheory.stdGaussian (MatV d)))
    (n := K) (i := Fin.last K) g hg
  simpa only [sampleLaw, piFinSuccAbove_last_snd, piFinSuccAbove_last_fst] using h

/-- The integral of a constant against the Gaussian pair law. -/
lemma integral_const_pair (c : ℝ) :
    (∫ _a : MatV d × MatV d, c ∂((ProbabilityTheory.stdGaussian (MatV d)).prod
        (ProbabilityTheory.stdGaussian (MatV d)))) = c := by
  rw [MeasureTheory.integral_const]
  have h1 : ((ProbabilityTheory.stdGaussian (MatV d)).prod
      (ProbabilityTheory.stdGaussian (MatV d))).real Set.univ = 1 := by
    rw [MeasureTheory.Measure.real_def, MeasureTheory.measure_univ, ENNReal.toReal_one]
  rw [h1, one_smul]

/-- Integrating a function of the first coordinate against the pair law. -/
lemma integral_fst_stdGaussian_prod (h : MatV d → ℝ) (hh : Measurable h) :
    (∫ a : MatV d × MatV d, h a.1 ∂((ProbabilityTheory.stdGaussian (MatV d)).prod
        (ProbabilityTheory.stdGaussian (MatV d))))
      = ∫ x, h x ∂(ProbabilityTheory.stdGaussian (MatV d)) := by
  let M := (ProbabilityTheory.stdGaussian (MatV d)).prod (ProbabilityTheory.stdGaussian (MatV d))
  calc ∫ a, h a.1 ∂M
      = ∫ x, h x ∂(MeasureTheory.Measure.map Prod.fst M) :=
        (MeasureTheory.integral_map (measurable_fst).aemeasurable hh.aestronglyMeasurable).symm
    _ = ∫ x, h x ∂(ProbabilityTheory.stdGaussian (MatV d)) := by
        rw [show MeasureTheory.Measure.map Prod.fst M
            = ProbabilityTheory.stdGaussian (MatV d) from MeasureTheory.Measure.fst_prod]

/-- A continuous linear functional of the first coordinate of the pair has zero mean. -/
lemma integral_pair_linear (w : MatV d) (P : MatV d →L[ℝ] MatV d)
    (hadj : ∀ x y, inner ℝ (P x) y = inner ℝ x (P y)) :
    (∫ a : MatV d × MatV d, inner ℝ w (P a.1)
        ∂((ProbabilityTheory.stdGaussian (MatV d)).prod
          (ProbabilityTheory.stdGaussian (MatV d)))) = 0 := by
  have hfun : ∀ a : MatV d × MatV d, inner ℝ w (P a.1) = inner ℝ (P w) a.1 := by
    intro a
    rw [← real_inner_comm w (P a.1), hadj a.1 w, real_inner_comm (P w) a.1]
  simp only [hfun]
  rw [integral_fst_stdGaussian_prod (fun x => inner ℝ (P w) x) (innerSL ℝ (P w)).continuous.measurable]
  exact ProbabilityTheory.integral_strongDual_stdGaussian (innerSL ℝ (P w))

/-- The norm squared of the projection of the first coordinate, against the pair law. -/
lemma integral_pair_norm_sq_starProjection (F : Submodule ℝ (MatV d)) :
    (∫ a : MatV d × MatV d, ‖F.starProjection a.1‖ ^ 2
        ∂((ProbabilityTheory.stdGaussian (MatV d)).prod
          (ProbabilityTheory.stdGaussian (MatV d)))) = (Module.finrank ℝ ↥F : ℝ) := by
  rw [integral_fst_stdGaussian_prod (fun x => ‖F.starProjection x‖ ^ 2)
    (((Submodule.starProjection F).continuous.norm).pow 2).measurable]
  exact integral_norm_sq_starProjection F

/-- Integrability of the norm of the first coordinate against the pair law. -/
lemma integrable_pair_fst_norm :
    Integrable (fun a : MatV d × MatV d => ‖a.1‖)
      ((ProbabilityTheory.stdGaussian (MatV d)).prod (ProbabilityTheory.stdGaussian (MatV d))) := by
  have h : Integrable (fun x : MatV d => ‖x‖) (ProbabilityTheory.stdGaussian (MatV d)) :=
    ((ProbabilityTheory.IsGaussian.memLp_id (ProbabilityTheory.stdGaussian (MatV d)) 1
      (by norm_num)).integrable (by norm_num)).norm
  simpa using h.comp_fst (ProbabilityTheory.stdGaussian (MatV d))

/-- The pair law is a probability measure. -/
lemma pair_real_univ :
    (((ProbabilityTheory.stdGaussian (MatV d)).prod
      (ProbabilityTheory.stdGaussian (MatV d)))).real Set.univ = 1 := by
  rw [MeasureTheory.Measure.real_def, MeasureTheory.measure_univ, ENNReal.toReal_one]

/-- A constant plus a self-adjoint linear functional of the first coordinate integrates to the
constant. -/
lemma integral_pair_const_add_linear (c : ℝ) (w : MatV d) (P : MatV d →L[ℝ] MatV d)
    (hadj : ∀ x y, inner ℝ (P x) y = inner ℝ x (P y)) (hP : ∀ x, ‖P x‖ ≤ ‖x‖) :
    (∫ a : MatV d × MatV d, (c + inner ℝ w (P a.1))
        ∂((ProbabilityTheory.stdGaussian (MatV d)).prod
          (ProbabilityTheory.stdGaussian (MatV d)))) = c := by
  have hlin : Integrable (fun a : MatV d × MatV d => inner ℝ w (P a.1))
      ((ProbabilityTheory.stdGaussian (MatV d)).prod (ProbabilityTheory.stdGaussian (MatV d))) := by
    refine MeasureTheory.Integrable.mono'
      (f := fun a : MatV d × MatV d => inner ℝ w (P a.1))
      (g := fun a : MatV d × MatV d => ‖w‖ * ‖a.1‖) ?_ ?_ ?_
    · exact integrable_pair_fst_norm.const_mul ‖w‖
    · exact (((innerSL ℝ w).comp P).continuous.comp continuous_fst).measurable.aestronglyMeasurable
    · filter_upwards with a
      rw [Real.norm_eq_abs]
      calc |inner ℝ w (P a.1)| ≤ ‖w‖ * ‖P a.1‖ := abs_real_inner_le_norm w (P a.1)
        _ ≤ ‖w‖ * ‖a.1‖ := mul_le_mul_of_nonneg_left (hP a.1) (norm_nonneg w)
  calc (∫ a : MatV d × MatV d, (c + inner ℝ w (P a.1)) ∂((ProbabilityTheory.stdGaussian (MatV d)).prod
          (ProbabilityTheory.stdGaussian (MatV d))))
      = (∫ _a : MatV d × MatV d, c ∂((ProbabilityTheory.stdGaussian (MatV d)).prod
          (ProbabilityTheory.stdGaussian (MatV d))))
        + ∫ a : MatV d × MatV d, inner ℝ w (P a.1) ∂((ProbabilityTheory.stdGaussian (MatV d)).prod
          (ProbabilityTheory.stdGaussian (MatV d))) :=
        MeasureTheory.integral_add (MeasureTheory.integrable_const c) hlin
    _ = c + 0 := by rw [integral_const_pair, integral_pair_linear _ _ hadj]
    _ = c := by ring

/-- **The inner integral of the squared norm**. -/
lemma integral_pair_norm_add_sq (w : MatV d) (P : MatV d →L[ℝ] MatV d)
    (hadj : ∀ x y, inner ℝ (P x) y = inner ℝ x (P y)) (F : Submodule ℝ (MatV d))
    (hPF : P = F.starProjection) {ε : ℝ} (hε : 0 ≤ ε) :
    (∫ a : MatV d × MatV d, ‖w + ε • (P a.1)‖ ^ 2
        ∂((ProbabilityTheory.stdGaussian (MatV d)).prod
          (ProbabilityTheory.stdGaussian (MatV d))))
      = ‖w‖ ^ 2 + ε ^ 2 * (Module.finrank ℝ ↥F : ℝ) := by
  have hP : ∀ x, ‖P x‖ ≤ ‖x‖ := by
    intro x; rw [hPF]; exact Submodule.norm_starProjection_apply_le (K := F) x
  have hpt : ∀ a : MatV d × MatV d, ‖w + ε • (P a.1)‖ ^ 2
      = ‖w‖ ^ 2 + (2 * ε * inner ℝ w (P a.1) + ε ^ 2 * ‖P a.1‖ ^ 2) := by
    intro a
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_of_nonneg hε, mul_pow]
    ring
  have hlin : Integrable (fun a : MatV d × MatV d => 2 * ε * inner ℝ w (P a.1))
      ((ProbabilityTheory.stdGaussian (MatV d)).prod (ProbabilityTheory.stdGaussian (MatV d))) := by
    refine MeasureTheory.Integrable.mono'
      (f := fun a : MatV d × MatV d => 2 * ε * inner ℝ w (P a.1))
      (g := fun a : MatV d × MatV d => (2 * ε * ‖w‖) * ‖a.1‖) ?_ ?_ ?_
    · exact integrable_pair_fst_norm.const_mul _
    · exact ((((innerSL ℝ w).comp P).continuous.comp continuous_fst).const_mul (2 * ε)).measurable.aestronglyMeasurable
    · filter_upwards with a
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * ε)]
      calc 2 * ε * |inner ℝ w (P a.1)| ≤ 2 * ε * (‖w‖ * ‖P a.1‖) :=
            mul_le_mul_of_nonneg_left (abs_real_inner_le_norm w (P a.1)) (by linarith)
        _ ≤ 2 * ε * (‖w‖ * ‖a.1‖) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hP a.1) (norm_nonneg w))
              (by linarith)
        _ = (2 * ε * ‖w‖) * ‖a.1‖ := by ring
  have hquad : Integrable (fun a : MatV d × MatV d => ε ^ 2 * ‖P a.1‖ ^ 2)
      ((ProbabilityTheory.stdGaussian (MatV d)).prod (ProbabilityTheory.stdGaussian (MatV d))) := by
    refine MeasureTheory.Integrable.mono'
      (f := fun a : MatV d × MatV d => ε ^ 2 * ‖P a.1‖ ^ 2)
      (g := fun a : MatV d × MatV d => ε ^ 2 * ‖a.1‖ ^ 2) ?_ ?_ ?_
    · have h2 : Integrable (fun x : MatV d => ‖x‖ ^ 2) (ProbabilityTheory.stdGaussian (MatV d)) :=
        (ProbabilityTheory.IsGaussian.memLp_id (ProbabilityTheory.stdGaussian (MatV d)) 2
          (by norm_num)).integrable_norm_pow (p := 2) (by norm_num)
      exact (h2.comp_fst (ProbabilityTheory.stdGaussian (MatV d))).const_mul _
    · exact ((((P.continuous.comp continuous_fst).norm).pow 2).const_mul (ε ^ 2)).measurable.aestronglyMeasurable
    · filter_upwards with a
      rw [Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hP a.1) 2) (by positivity)
  have hcongr : (∫ a : MatV d × MatV d, ‖w + ε • (P a.1)‖ ^ 2 ∂((ProbabilityTheory.stdGaussian (MatV d)).prod
        (ProbabilityTheory.stdGaussian (MatV d))))
      = ∫ a : MatV d × MatV d, (‖w‖ ^ 2 + (2 * ε * inner ℝ w (P a.1) + ε ^ 2 * ‖P a.1‖ ^ 2))
          ∂((ProbabilityTheory.stdGaussian (MatV d)).prod (ProbabilityTheory.stdGaussian (MatV d))) :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
  calc (∫ a : MatV d × MatV d, ‖w + ε • (P a.1)‖ ^ 2 ∂((ProbabilityTheory.stdGaussian (MatV d)).prod
          (ProbabilityTheory.stdGaussian (MatV d))))
      = ∫ a : MatV d × MatV d, (‖w‖ ^ 2 + (2 * ε * inner ℝ w (P a.1) + ε ^ 2 * ‖P a.1‖ ^ 2))
          ∂((ProbabilityTheory.stdGaussian (MatV d)).prod (ProbabilityTheory.stdGaussian (MatV d))) := hcongr
    _ = (∫ _a : MatV d × MatV d, ‖w‖ ^ 2 ∂((ProbabilityTheory.stdGaussian (MatV d)).prod
          (ProbabilityTheory.stdGaussian (MatV d))))
        + ∫ a : MatV d × MatV d, (2 * ε * inner ℝ w (P a.1) + ε ^ 2 * ‖P a.1‖ ^ 2)
          ∂((ProbabilityTheory.stdGaussian (MatV d)).prod (ProbabilityTheory.stdGaussian (MatV d))) :=
        MeasureTheory.integral_add (MeasureTheory.integrable_const _) (hlin.add hquad)
    _ = (∫ _a : MatV d × MatV d, ‖w‖ ^ 2 ∂((ProbabilityTheory.stdGaussian (MatV d)).prod
          (ProbabilityTheory.stdGaussian (MatV d))))
        + ((∫ a : MatV d × MatV d, 2 * ε * inner ℝ w (P a.1)
            ∂((ProbabilityTheory.stdGaussian (MatV d)).prod (ProbabilityTheory.stdGaussian (MatV d))))
          + ∫ a : MatV d × MatV d, ε ^ 2 * ‖P a.1‖ ^ 2
            ∂((ProbabilityTheory.stdGaussian (MatV d)).prod (ProbabilityTheory.stdGaussian (MatV d)))) := by
        rw [MeasureTheory.integral_add hlin hquad]
    _ = ‖w‖ ^ 2 + ((∫ a : MatV d × MatV d, 2 * ε * inner ℝ w (P a.1)
            ∂((ProbabilityTheory.stdGaussian (MatV d)).prod (ProbabilityTheory.stdGaussian (MatV d))))
          + ∫ a : MatV d × MatV d, ε ^ 2 * ‖P a.1‖ ^ 2
            ∂((ProbabilityTheory.stdGaussian (MatV d)).prod (ProbabilityTheory.stdGaussian (MatV d)))) := by
        rw [integral_const_pair]
    _ = ‖w‖ ^ 2 + (2 * ε * 0 + ε ^ 2 * (Module.finrank ℝ ↥F : ℝ)) := by
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
          integral_pair_linear _ _ hadj, hPF, integral_pair_norm_sq_starProjection]
    _ = ‖w‖ ^ 2 + ε ^ 2 * (Module.finrank ℝ ↥F : ℝ) := by ring

/-! ## The dimension of the constraint space -/

/-- The dimension of the constraint space attached to a pattern of violated candidates. -/
def NfunOf (χ : Fin m → Bool) : ℝ :=
  (Module.finrank ℝ ↥(tangentSub ((Finset.univ.filter (fun i : Fin m => χ i = true)).image BoxL)) : ℝ)

/-- The dimension of the constraint space at the state `A`. -/
def Nfun (A : MatV d) : ℝ :=
  (Module.finrank ℝ ↥(tangentSub (violSet R BoxL A)) : ℝ)

lemma Nfun_eq_NfunOf (A : MatV d) : Nfun R BoxL A = NfunOf BoxL (patt R BoxL A) := by
  have h : (Finset.univ.filter (fun i : Fin m => patt R BoxL A i = true)).image BoxL
      = violSet R BoxL A := by
    ext y
    simp only [violSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, patt,
      Set.mem_setOf_eq]
    constructor
    · rintro ⟨i, hi, rfl⟩
      by_cases hh : ‖BoxL i‖ ≤ R ∧ quadFormV A (BoxL i) ≤ 1
      · exact ⟨i, hh, rfl⟩
      · simp [hh] at hi
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, by simp [hi], rfl⟩
  rw [Nfun, NfunOf, h]

lemma measurable_Nfun : Measurable (Nfun R BoxL) := by
  have h : Nfun R BoxL = NfunOf BoxL ∘ (patt R BoxL) := funext fun A => Nfun_eq_NfunOf R BoxL A
  rw [h]
  exact (measurable_of_finite (NfunOf BoxL)).comp (measurable_patt R BoxL)

lemma Nfun_nonneg (A : MatV d) : 0 ≤ Nfun R BoxL A := Nat.cast_nonneg _

lemma Nfun_le (A : MatV d) : Nfun R BoxL A ≤ ((d * d : ℕ) : ℝ) := by
  have h1 : Module.finrank ℝ ↥(tangentSub (violSet R BoxL A)) ≤ Module.finrank ℝ (MatV d) :=
    Submodule.finrank_le _
  rw [finrank_euclideanSpace, Fintype.card_prod, Fintype.card_fin] at h1
  have h2 : ((Module.finrank ℝ ↥(tangentSub (violSet R BoxL A)) : ℕ) : ℝ)
      ≤ ((d * d : ℕ) : ℝ) := by exact_mod_cast h1
  simpa [Nfun] using h2

lemma integrable_Nfun_comp (K : ℕ) (k : Fin K) :
    Integrable (fun ω : Fin K → MatV d × MatV d =>
        Nfun R BoxL (proc (projL R BoxL) a₀ ε K ω k)) (sampleLaw d K) := by
  refine MeasureTheory.Integrable.mono'
    (f := fun ω : Fin K → MatV d × MatV d =>
      Nfun R BoxL (proc (projL R BoxL) a₀ ε K ω k))
    (g := fun _ : Fin K → MatV d × MatV d => ((d * d : ℕ) : ℝ)) ?_ ?_ ?_
  · exact MeasureTheory.integrable_const _
  · exact ((measurable_Nfun R BoxL).comp
      (measurable_proc (pl := projL R BoxL) (a₀ := a₀) (ε := ε) (K := K)
        (measurable_projL R BoxL) k)).aestronglyMeasurable
  · filter_upwards with ω
    rw [Real.norm_of_nonneg (Nfun_nonneg R BoxL _)]
    exact Nfun_le R BoxL _

/-- Integrability of the constraint dimension at time `K`, for every `K`. -/
lemma integrable_Nfun_at (K : ℕ) :
    Integrable (fun ω : Fin K → MatV d × MatV d =>
        Nfun R BoxL (proc (projL R BoxL) a₀ ε K ω K)) (sampleLaw d K) := by
  refine MeasureTheory.Integrable.mono'
    (f := fun ω : Fin K → MatV d × MatV d =>
      Nfun R BoxL (proc (projL R BoxL) a₀ ε K ω K))
    (g := fun _ : Fin K → MatV d × MatV d => ((d * d : ℕ) : ℝ)) ?_ ?_ ?_
  · exact MeasureTheory.integrable_const _
  · exact ((measurable_Nfun R BoxL).comp
      (measurable_proc (pl := projL R BoxL) (a₀ := a₀) (ε := ε) (K := K)
        (measurable_projL R BoxL) K)).aestronglyMeasurable
  · filter_upwards with ω
    rw [Real.norm_of_nonneg (Nfun_nonneg R BoxL _)]
    exact Nfun_le R BoxL _

/-- Forgetting the last coordinate does not change the integral. -/
lemma integral_congr_dropLast {K : ℕ} (F : (Fin K → MatV d × MatV d) → ℝ)
    (hF : Integrable F (sampleLaw d K)) :
    (∫ ω : Fin (K + 1) → MatV d × MatV d, F (dropLast ω) ∂(sampleLaw d (K + 1)))
      = ∫ u, F u ∂(sampleLaw d K) := by
  have hg : MeasureTheory.Integrable
      (fun p : (Fin K → MatV d × MatV d) × (MatV d × MatV d) => F p.1)
      ((sampleLaw d K).prod ((ProbabilityTheory.stdGaussian (MatV d)).prod
        (ProbabilityTheory.stdGaussian (MatV d)))) :=
    hF.comp_fst _
  rw [integral_pi_last (fun u _ => F u) hg]
  have hinner : ∀ u : Fin K → MatV d × MatV d,
      (∫ _a : MatV d × MatV d, F u ∂((ProbabilityTheory.stdGaussian (MatV d)).prod
        (ProbabilityTheory.stdGaussian (MatV d)))) = F u := by
    intro u
    rw [MeasureTheory.integral_const, pair_real_univ, one_smul]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hinner)]

/-! ## The two moment identities -/

/-- The state is symmetric. -/
lemma stateK_mem_symV (K : ℕ) (ω : Fin K → MatV d × MatV d) :
    stateK (projL R BoxL) a₀ ε K ω ∈ symV d :=
  (symV d).sub_mem (proc_mem_symV (pl := projL R BoxL) (a₀ := a₀) (ε := ε) (K := K)
    (fun A => good_projL R BoxL A) K ω) ((symV d).smul_mem a₀ (oneV_mem_symV d))

/-- The trace of a state is the inner product with the identity matrix. -/
lemma trace_state_eq_inner (K : ℕ) (ω : Fin K → MatV d × MatV d) :
    (matOf d (stateK (projL R BoxL) a₀ ε K ω)).trace
      = inner ℝ (oneV d) (stateK (projL R BoxL) a₀ ε K ω) := by
  rw [inner_eq_trace_mul (oneV d) (stateK (projL R BoxL) a₀ ε K ω)
      ((mem_symV).mp (stateK_mem_symV R BoxL a₀ ε K ω)), matOf_oneV, Matrix.one_mul]

/-- **The first-order term of the drift vanishes.** -/
theorem integral_inner_oneV_state_eq_zero (K : ℕ) (hε : 0 ≤ ε) :
    (∫ ω : Fin K → MatV d × MatV d,
        inner ℝ (oneV d) (stateK (projL R BoxL) a₀ ε K ω) ∂(sampleLaw d K)) = 0 := by
  induction K with
  | zero =>
    have h0 : ∀ ω : Fin 0 → MatV d × MatV d, stateK (projL R BoxL) a₀ ε 0 ω = 0 := by
      intro ω
      simp [stateK, proc]
    simp only [h0, inner_zero_right, MeasureTheory.integral_zero]
  | succ K ih =>
    set ν : MeasureTheory.Measure (MatV d × MatV d) :=
      (ProbabilityTheory.stdGaussian (MatV d)).prod (ProbabilityTheory.stdGaussian (MatV d))
    set g : (Fin K → MatV d × MatV d) → (MatV d × MatV d) → ℝ := fun u a =>
      inner ℝ (oneV d) (stateK (projL R BoxL) a₀ ε K u)
        + inner ℝ (ε • oneV d) ((projL R BoxL (proc (projL R BoxL) a₀ ε K u K)) a.1) with hgdef
    have hfun : (fun ω : Fin (K + 1) → MatV d × MatV d =>
        inner ℝ (oneV d) (stateK (projL R BoxL) a₀ ε (K + 1) ω))
        = fun ω => g (dropLast ω) (ω (Fin.last K)) := by
      funext ω
      rw [stateK_succ, inner_add_right, real_inner_smul_right, ← real_inner_smul_left, hgdef]
    have hmaj : MeasureTheory.Integrable
        (fun p : (Fin K → MatV d × MatV d) × (MatV d × MatV d) =>
          ‖oneV d‖ * ‖stateK (projL R BoxL) a₀ ε K p.1‖ + ε * ‖oneV d‖ * ‖p.2.1‖)
        ((sampleLaw d K).prod ν) := by
      have h1 : MeasureTheory.Integrable
          (fun p : (Fin K → MatV d × MatV d) × (MatV d × MatV d) =>
            ‖stateK (projL R BoxL) a₀ ε K p.1‖) ((sampleLaw d K).prod ν) :=
        (integrable_stateK_norm R BoxL a₀ ε K hε).comp_fst ν
      have h2 : MeasureTheory.Integrable
          (fun p : (Fin K → MatV d × MatV d) × (MatV d × MatV d) => ‖p.2.1‖)
          ((sampleLaw d K).prod ν) :=
        integrable_pair_fst_norm.comp_snd (sampleLaw d K)
      exact ((h1.const_mul ‖oneV d‖).add (h2.const_mul (ε * ‖oneV d‖)))
    have hg : MeasureTheory.Integrable (fun p : (Fin K → MatV d × MatV d) × (MatV d × MatV d) =>
        g p.1 p.2) ((sampleLaw d K).prod ν) := by
      refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
      · refine Measurable.aestronglyMeasurable ?_
        simp only [hgdef]
        refine Measurable.add ?_ ?_
        · exact ((innerSL ℝ (oneV d)).continuous.measurable.comp
            ((measurable_stateK R BoxL a₀ ε K).comp measurable_fst))
        · refine (innerSL ℝ (ε • oneV d)).continuous.measurable.comp ?_
          exact measurable_clm_apply
            ((measurable_projL R BoxL).comp
              ((measurable_proc (pl := projL R BoxL) (a₀ := a₀) (ε := ε) (K := K)
                (measurable_projL R BoxL) K).comp measurable_fst))
            measurable_snd.fst
      · filter_upwards with p
        rw [Real.norm_eq_abs]
        have hb1 : |inner ℝ (oneV d) (stateK (projL R BoxL) a₀ ε K p.1)|
            ≤ ‖oneV d‖ * ‖stateK (projL R BoxL) a₀ ε K p.1‖ :=
          abs_real_inner_le_norm _ _
        have hb2 : |inner ℝ (ε • oneV d)
            ((projL R BoxL (proc (projL R BoxL) a₀ ε K p.1 K)) p.2.1)|
            ≤ ε * ‖oneV d‖ * ‖p.2.1‖ := by
          refine le_trans (abs_real_inner_le_norm _ _) ?_
          rw [norm_smul, Real.norm_of_nonneg hε]
          exact mul_le_mul_of_nonneg_left
            (Submission.Rescale.norm_projL_apply_le R BoxL _ _) (by positivity)
        rw [show g p.1 p.2 = inner ℝ (oneV d) (stateK (projL R BoxL) a₀ ε K p.1)
            + inner ℝ (ε • oneV d)
              ((projL R BoxL (proc (projL R BoxL) a₀ ε K p.1 K)) p.2.1) from rfl]
        calc |inner ℝ (oneV d) (stateK (projL R BoxL) a₀ ε K p.1)
              + inner ℝ (ε • oneV d) ((projL R BoxL (proc (projL R BoxL) a₀ ε K p.1 K)) p.2.1)|
            ≤ |inner ℝ (oneV d) (stateK (projL R BoxL) a₀ ε K p.1)|
              + |inner ℝ (ε • oneV d) ((projL R BoxL (proc (projL R BoxL) a₀ ε K p.1 K)) p.2.1)| :=
              abs_add_le _ _
          _ ≤ ‖oneV d‖ * ‖stateK (projL R BoxL) a₀ ε K p.1‖ + ε * ‖oneV d‖ * ‖p.2.1‖ :=
              add_le_add hb1 hb2
    rw [hfun, integral_pi_last g hg]
    have hinner : ∀ u : Fin K → MatV d × MatV d,
        (∫ a, g u a ∂ν) = inner ℝ (oneV d) (stateK (projL R BoxL) a₀ ε K u) := by
      intro u
      have hP : ∀ x : MatV d, ‖(projL R BoxL (proc (projL R BoxL) a₀ ε K u K)) x‖ ≤ ‖x‖ :=
        fun x => Submission.Rescale.norm_projL_apply_le R BoxL _ x
      have hadj := (good_projL R BoxL (proc (projL R BoxL) a₀ ε K u K)).adj
      have := integral_pair_const_add_linear (d := d)
        (inner ℝ (oneV d) (stateK (projL R BoxL) a₀ ε K u))
        (ε • oneV d) (projL R BoxL (proc (projL R BoxL) a₀ ε K u K)) hadj hP
      simpa [hgdef, ν] using this
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hinner), ih]

/-- Integrability of the squared norm of the first coordinate against the pair law. -/
lemma integrable_pair_fst_norm_sq :
    Integrable (fun a : MatV d × MatV d => ‖a.1‖ ^ 2)
      ((ProbabilityTheory.stdGaussian (MatV d)).prod (ProbabilityTheory.stdGaussian (MatV d))) := by
  have h : Integrable (fun x : MatV d => ‖x‖ ^ 2) (ProbabilityTheory.stdGaussian (MatV d)) :=
    (ProbabilityTheory.IsGaussian.memLp_id (ProbabilityTheory.stdGaussian (MatV d)) 2
      (by norm_num)).integrable_norm_pow (p := 2) (by norm_num)
  simpa using h.comp_fst (ProbabilityTheory.stdGaussian (MatV d))

/-- The constraint dimension at time `k < K` only depends on the first `k` coordinates. -/
lemma integral_Nfun_castSucc (K : ℕ) (k : Fin K) :
    (∫ ω : Fin (K + 1) → MatV d × MatV d,
        Nfun R BoxL (proc (projL R BoxL) a₀ ε (K + 1) ω k.castSucc) ∂(sampleLaw d (K + 1)))
      = ∫ u : Fin K → MatV d × MatV d,
          Nfun R BoxL (proc (projL R BoxL) a₀ ε K u k) ∂(sampleLaw d K) := by
  have hF : (fun ω : Fin (K + 1) → MatV d × MatV d =>
        Nfun R BoxL (proc (projL R BoxL) a₀ ε (K + 1) ω k.castSucc))
      = fun ω => Nfun R BoxL (proc (projL R BoxL) a₀ ε K (dropLast ω) k) := by
    funext ω
    rw [show ((k.castSucc : Fin (K + 1)) : ℕ) = (k : ℕ) from rfl,
      proc_dropLast (pl := projL R BoxL) (a₀ := a₀) (ε := ε) K (k : ℕ)
        (Nat.le_of_lt k.isLt) ω]
  rw [hF]
  exact integral_congr_dropLast (fun u => Nfun R BoxL (proc (projL R BoxL) a₀ ε K u k))
    (integrable_Nfun_comp R BoxL a₀ ε K k)

/-- The constraint dimension at the last step. -/
lemma integral_Nfun_last (K : ℕ) :
    (∫ ω : Fin (K + 1) → MatV d × MatV d,
        Nfun R BoxL (proc (projL R BoxL) a₀ ε (K + 1) ω (Fin.last K)) ∂(sampleLaw d (K + 1)))
      = ∫ u : Fin K → MatV d × MatV d,
          Nfun R BoxL (proc (projL R BoxL) a₀ ε K u K) ∂(sampleLaw d K) := by
  have hF : (fun ω : Fin (K + 1) → MatV d × MatV d =>
        Nfun R BoxL (proc (projL R BoxL) a₀ ε (K + 1) ω (Fin.last K)))
      = fun ω => Nfun R BoxL (proc (projL R BoxL) a₀ ε K (dropLast ω) K) := by
    funext ω
    rw [show ((Fin.last K : Fin (K + 1)) : ℕ) = K from rfl,
      proc_dropLast (pl := projL R BoxL) (a₀ := a₀) (ε := ε) K K le_rfl ω]
  rw [hF]
  exact integral_congr_dropLast (fun u => Nfun R BoxL (proc (projL R BoxL) a₀ ε K u K))
    (integrable_Nfun_at R BoxL a₀ ε K)

/-- **The second moment of the state.**  The expected square norm of the state is `ε²` times the
sum of the constraint-space dimensions along the way. -/
theorem integral_norm_sq_state (K : ℕ) (hε : 0 ≤ ε) :
    (∫ ω : Fin K → MatV d × MatV d, ‖stateK (projL R BoxL) a₀ ε K ω‖ ^ 2 ∂(sampleLaw d K))
      = ε ^ 2 * ∑ k : Fin K, ∫ ω : Fin K → MatV d × MatV d,
          Nfun R BoxL (proc (projL R BoxL) a₀ ε K ω k) ∂(sampleLaw d K) := by
  induction K with
  | zero =>
    have h0 : ∀ ω : Fin 0 → MatV d × MatV d, stateK (projL R BoxL) a₀ ε 0 ω = 0 := by
      intro ω
      simp [stateK, proc]
    simp only [h0, norm_zero, pow_two, mul_zero, MeasureTheory.integral_zero, Finset.univ_eq_empty,
      Finset.sum_empty, mul_zero]
  | succ K ih =>
    set ν : MeasureTheory.Measure (MatV d × MatV d) :=
      (ProbabilityTheory.stdGaussian (MatV d)).prod (ProbabilityTheory.stdGaussian (MatV d))
    set g : (Fin K → MatV d × MatV d) → (MatV d × MatV d) → ℝ := fun u a =>
      ‖stateK (projL R BoxL) a₀ ε K u
        + ε • (projL R BoxL (proc (projL R BoxL) a₀ ε K u K)) a.1‖ ^ 2 with hgdef
    have hfun : (fun ω : Fin (K + 1) → MatV d × MatV d =>
          ‖stateK (projL R BoxL) a₀ ε (K + 1) ω‖ ^ 2)
        = fun ω => g (dropLast ω) (ω (Fin.last K)) := by
      funext ω
      rw [stateK_succ (projL R BoxL) a₀ ε K ω, hgdef]
    have hmaj : MeasureTheory.Integrable
        (fun p : (Fin K → MatV d × MatV d) × (MatV d × MatV d) =>
          (2 : ℝ) * ‖stateK (projL R BoxL) a₀ ε K p.1‖ ^ 2 + (2 * ε ^ 2) * ‖p.2.1‖ ^ 2)
        ((sampleLaw d K).prod ν) := by
      have h1 : MeasureTheory.Integrable
          (fun p : (Fin K → MatV d × MatV d) × (MatV d × MatV d) =>
            ‖stateK (projL R BoxL) a₀ ε K p.1‖ ^ 2) ((sampleLaw d K).prod ν) :=
        (integrable_stateK_norm_sq R BoxL a₀ ε K hε).comp_fst ν
      have h2 : MeasureTheory.Integrable
          (fun p : (Fin K → MatV d × MatV d) × (MatV d × MatV d) => ‖p.2.1‖ ^ 2)
          ((sampleLaw d K).prod ν) :=
        integrable_pair_fst_norm_sq.comp_snd (sampleLaw d K)
      exact ((h1.const_mul 2).add (h2.const_mul (2 * ε ^ 2)))
    have hg : MeasureTheory.Integrable (fun p : (Fin K → MatV d × MatV d) × (MatV d × MatV d) =>
        g p.1 p.2) ((sampleLaw d K).prod ν) := by
      refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
      · refine Measurable.aestronglyMeasurable ?_
        simp only [hgdef]
        refine (((measurable_stateK R BoxL a₀ ε K).comp measurable_fst).add ?_).norm.pow_const 2
        refine (measurable_clm_apply
          ((measurable_projL R BoxL).comp
            ((measurable_proc (pl := projL R BoxL) (a₀ := a₀) (ε := ε) (K := K)
              (measurable_projL R BoxL) K).comp measurable_fst))
          measurable_snd.fst).const_smul ε
      · filter_upwards with p
        rw [Real.norm_of_nonneg (by positivity)]
        have hb : ‖stateK (projL R BoxL) a₀ ε K p.1
            + ε • (projL R BoxL (proc (projL R BoxL) a₀ ε K p.1 K)) p.2.1‖
            ≤ ‖stateK (projL R BoxL) a₀ ε K p.1‖ + ε * ‖p.2.1‖ := by
          refine le_trans (norm_add_le _ _) (add_le_add le_rfl ?_)
          rw [norm_smul, Real.norm_of_nonneg hε]
          exact mul_le_mul_of_nonneg_left
            (Submission.Rescale.norm_projL_apply_le R BoxL _ _) hε
        have hb2 : ‖stateK (projL R BoxL) a₀ ε K p.1
            + ε • (projL R BoxL (proc (projL R BoxL) a₀ ε K p.1 K)) p.2.1‖ ^ 2
            ≤ (‖stateK (projL R BoxL) a₀ ε K p.1‖ + ε * ‖p.2.1‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hb 2
        have hb3 : (‖stateK (projL R BoxL) a₀ ε K p.1‖ + ε * ‖p.2.1‖) ^ 2
            ≤ (2 : ℝ) * ‖stateK (projL R BoxL) a₀ ε K p.1‖ ^ 2 + (2 * ε ^ 2) * ‖p.2.1‖ ^ 2 := by
          nlinarith [sq_nonneg (‖stateK (projL R BoxL) a₀ ε K p.1‖ - ε * ‖p.2.1‖), sq_nonneg ε,
            norm_nonneg (stateK (projL R BoxL) a₀ ε K p.1), norm_nonneg p.2.1]
        exact hb2.trans hb3
    rw [hfun, integral_pi_last g hg]
    have hinner : ∀ u : Fin K → MatV d × MatV d,
        (∫ a, g u a ∂ν) = ‖stateK (projL R BoxL) a₀ ε K u‖ ^ 2
          + ε ^ 2 * Nfun R BoxL (proc (projL R BoxL) a₀ ε K u K) := by
      intro u
      have h := integral_pair_norm_add_sq (d := d) (ε := ε)
        (stateK (projL R BoxL) a₀ ε K u)
        (projL R BoxL (proc (projL R BoxL) a₀ ε K u K))
        (good_projL R BoxL (proc (projL R BoxL) a₀ ε K u K)).adj
        (tangentSub (violSet R BoxL (proc (projL R BoxL) a₀ ε K u K)))
        (projL_apply_eq R BoxL (proc (projL R BoxL) a₀ ε K u K)) hε
      simpa [hgdef, ν, Nfun] using h
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hinner)]
    have hint1 : MeasureTheory.Integrable
        (fun u : Fin K → MatV d × MatV d => ‖stateK (projL R BoxL) a₀ ε K u‖ ^ 2)
        (sampleLaw d K) := integrable_stateK_norm_sq R BoxL a₀ ε K hε
    have hint2 : MeasureTheory.Integrable
        (fun u : Fin K → MatV d × MatV d =>
          ε ^ 2 * Nfun R BoxL (proc (projL R BoxL) a₀ ε K u K)) (sampleLaw d K) :=
      (integrable_Nfun_at R BoxL a₀ ε K).const_mul _
    have hsplit : (∫ u : Fin K → MatV d × MatV d, (‖stateK (projL R BoxL) a₀ ε K u‖ ^ 2
          + ε ^ 2 * Nfun R BoxL (proc (projL R BoxL) a₀ ε K u K)) ∂(sampleLaw d K))
        = (∫ u : Fin K → MatV d × MatV d, ‖stateK (projL R BoxL) a₀ ε K u‖ ^ 2 ∂(sampleLaw d K))
          + ∫ u : Fin K → MatV d × MatV d,
              ε ^ 2 * Nfun R BoxL (proc (projL R BoxL) a₀ ε K u K) ∂(sampleLaw d K) :=
      MeasureTheory.integral_add hint1 hint2
    rw [hsplit, ih]
    rw [MeasureTheory.integral_const_mul]
    have hsum : (∑ k : Fin (K + 1), ∫ ω : Fin (K + 1) → MatV d × MatV d,
          Nfun R BoxL (proc (projL R BoxL) a₀ ε (K + 1) ω k) ∂(sampleLaw d (K + 1)))
        = (∑ k : Fin K, ∫ u : Fin K → MatV d × MatV d,
              Nfun R BoxL (proc (projL R BoxL) a₀ ε K u k) ∂(sampleLaw d K))
          + ∫ u : Fin K → MatV d × MatV d,
              Nfun R BoxL (proc (projL R BoxL) a₀ ε K u K) ∂(sampleLaw d K) := by
      rw [Fin.sum_univ_castSucc]
      congr 1
      · exact Finset.sum_congr rfl fun k _ => integral_Nfun_castSucc R BoxL a₀ ε K k
      · exact integral_Nfun_last R BoxL a₀ ε K
    rw [hsum]
    ring

end Moment

end

end Submission.Moment
