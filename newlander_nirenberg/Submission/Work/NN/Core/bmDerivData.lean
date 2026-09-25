/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The candidate derivative of the Bochner–Martinelli potential

For a family `g : Fin n → (Fin n → ℂ) → ℂ` (a `(0,1)`-form) the Bochner–Martinelli potential is

  `bmPot g z = Σ_j ∫ x, bmKernel j x * g j (z + x)`.

If the data `g` are `C¹`, the Wirtinger derivatives of the potential are given by the singular
integrals

  `dCoord j (bmPot g) z  = -Σ_k ∫_{‖x‖<4R} bmDzKernel j k x * (g k (z+x) - g k z)`,
  `dbarCoord j (bmPot g) z = -Σ_k ∫_{‖x‖<4R} bmDbarKernel j k x * (g k (z+x) - g k z)
                              - Σ_k cc j k * g k z`,

the second one carrying the Bochner–Martinelli kernel constants `cc` of the integration by parts
identity `Work.NN.Core.bmPot_repr`.  This file assembles those two complex numbers into the real
linear map `bmDerivData R cc g z : (Fin n → ℂ) →L[ℝ] ℂ` which is the candidate Fréchet derivative
of `bmPot g` at `z`; the point of the file is that `bmDerivData` only involves the *values* of `g`
(no derivatives of `g`), so that it makes sense for merely Hölder continuous data and can be used
to formulate the Schauder estimate for such data.
-/
import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Cauchy.bmCZDefs
import Submission.Work.CR.Flat.Cauchy.bmSetup

noncomputable section

open scoped NNReal ENNReal
open MeasureTheory Set

namespace Work.NN.Core

open Work.CR.Flat.Cauchy

/-- The `∂`-part `-Σ_k ∫_{‖x‖<4R} bmDzKernel j k x * (g k (z+x) - g k z)` of the candidate
Wirtinger derivative `dCoord j` of the Bochner–Martinelli potential of `g` at `z`. -/
noncomputable def bmDzPart {n : ℕ} (R : ℝ) (g : Fin n → (Fin n → ℂ) → ℂ) (z : Fin n → ℂ)
    (j : Fin n) : ℂ :=
  -∑ k, ∫ x in eucBall (n := n) (4 * R), bmDzKernel j k x * (g k (z + x) - g k z)

/-- The `∂̄`-part of the candidate Wirtinger derivative `dbarCoord j` of the Bochner–Martinelli
potential of `g` at `z`, including the constant term `-Σ_k cc j k * g k z`. -/
noncomputable def bmDbarPart {n : ℕ} (R : ℝ) (cc : Fin n → Fin n → ℂ)
    (g : Fin n → (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) (j : Fin n) : ℂ :=
  (-∑ k, ∫ x in eucBall (n := n) (4 * R), bmDbarKernel j k x * (g k (z + x) - g k z))
    - ∑ k, cc j k * g k z

/-- The candidate Fréchet derivative of `bmPot g` at `z`, assembled from the two Wirtinger
derivatives: on the coordinate basis `e_j = Pi.single j 1` and `i e_j = Pi.single j I` it takes the
values `A_j + B_j` and `i (A_j - B_j)`, where `A_j = bmDzPart R g z j` and
`B_j = bmDbarPart R cc g z j`. -/
noncomputable def bmDerivData {n : ℕ} (R : ℝ) (cc : Fin n → Fin n → ℂ)
    (g : Fin n → (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) : (Fin n → ℂ) →L[ℝ] ℂ :=
  ∑ j, (ContinuousLinearMap.smulRight
          (Complex.reCLM.comp (ContinuousLinearMap.proj (R := ℝ) j))
          (bmDzPart R g z j + bmDbarPart R cc g z j)
        + ContinuousLinearMap.smulRight
          (Complex.imCLM.comp (ContinuousLinearMap.proj (R := ℝ) j))
          (Complex.I * (bmDzPart R g z j - bmDbarPart R cc g z j)))

/-- The decomposition of a vector of `ℂⁿ` in the real basis `e_j`, `i e_j`. -/
lemma eq_sum_single {n : ℕ} (v : Fin n → ℂ) :
    v = ∑ j, (((v j).re : ℝ) • (Pi.single j (1 : ℂ) : Fin n → ℂ)
      + ((v j).im : ℝ) • (Pi.single j Complex.I : Fin n → ℂ)) := by
  funext m
  rw [Finset.sum_apply,
    Finset.sum_eq_single_of_mem m (Finset.mem_univ m) (fun k _ hk => by
      simp [Pi.single_eq_of_ne (Ne.symm hk)])]
  simp [Complex.re_add_im, Complex.real_smul]

/-- Evaluation of `bmDerivData` on a vector. -/
lemma bmDerivData_apply {n : ℕ} (R : ℝ) (cc : Fin n → Fin n → ℂ)
    (g : Fin n → (Fin n → ℂ) → ℂ) (z v : Fin n → ℂ) :
    bmDerivData R cc g z v
      = ∑ j, (v j).re • (bmDzPart R g z j + bmDbarPart R cc g z j)
        + ∑ j, (v j).im • (Complex.I * (bmDzPart R g z j - bmDbarPart R cc g z j)) := by
  rw [bmDerivData, sum_apply]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, Complex.reCLM_apply, Complex.imCLM_apply]
  rw [Finset.sum_add_distrib]

/-- `bmDerivData` in the coordinate direction `e_j`. -/
@[simp] lemma bmDerivData_single_one {n : ℕ} (R : ℝ) (cc : Fin n → Fin n → ℂ)
    (g : Fin n → (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) (j : Fin n) :
    bmDerivData R cc g z (Pi.single j (1 : ℂ)) = bmDzPart R g z j + bmDbarPart R cc g z j := by
  rw [bmDerivData, sum_apply]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, Complex.reCLM_apply, Complex.imCLM_apply]
  rw [Finset.sum_add_distrib,
    Finset.sum_eq_single_of_mem j (Finset.mem_univ j) (fun m _ hm => by
      simp [Pi.single_eq_of_ne hm]),
    Finset.sum_eq_single_of_mem j (Finset.mem_univ j) (fun m _ hm => by
      simp [Pi.single_eq_of_ne hm])]
  simp

/-- `bmDerivData` in the coordinate direction `i e_j`. -/
@[simp] lemma bmDerivData_single_I {n : ℕ} (R : ℝ) (cc : Fin n → Fin n → ℂ)
    (g : Fin n → (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) (j : Fin n) :
    bmDerivData R cc g z (Pi.single j Complex.I)
      = Complex.I * (bmDzPart R g z j - bmDbarPart R cc g z j) := by
  rw [bmDerivData, sum_apply]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, Complex.reCLM_apply, Complex.imCLM_apply]
  rw [Finset.sum_add_distrib,
    Finset.sum_eq_single_of_mem j (Finset.mem_univ j) (fun m _ hm => by
      simp [Pi.single_eq_of_ne hm]),
    Finset.sum_eq_single_of_mem j (Finset.mem_univ j) (fun m _ hm => by
      simp [Pi.single_eq_of_ne hm])]
  simp

/-- Two real linear maps `ℂⁿ → ℂ` which agree on the real basis `e_j`, `i e_j` are equal. -/
lemma clm_ext_single {n : ℕ} {A B : (Fin n → ℂ) →L[ℝ] ℂ}
    (h1 : ∀ j, A (Pi.single j (1 : ℂ)) = B (Pi.single j (1 : ℂ)))
    (h2 : ∀ j, A (Pi.single j Complex.I) = B (Pi.single j Complex.I)) : A = B := by
  refine ContinuousLinearMap.ext fun v => ?_
  have hA : A v = ∑ j, (((v j).re : ℝ) • A (Pi.single j (1 : ℂ))
      + ((v j).im : ℝ) • A (Pi.single j Complex.I)) := by
    conv_lhs => rw [eq_sum_single v]
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_add, map_smul, map_smul]
  have hB : B v = ∑ j, (((v j).re : ℝ) • B (Pi.single j (1 : ℂ))
      + ((v j).im : ℝ) • B (Pi.single j Complex.I)) := by
    conv_lhs => rw [eq_sum_single v]
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_add, map_smul, map_smul]
  rw [hA, hB]
  exact Finset.sum_congr rfl fun j _ => by rw [h1 j, h2 j]

/-- The operator norm of a real linear map `ℂⁿ → ℂ` is bounded by the sum of the norms of its
values on the real basis `e_j`, `i e_j`. -/
lemma norm_le_sum_coord {n : ℕ} (A : (Fin n → ℂ) →L[ℝ] ℂ) :
    ‖A‖ ≤ ∑ j, (‖A (Pi.single j (1 : ℂ))‖ + ‖A (Pi.single j Complex.I)‖) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun j _ => by positivity)
    fun v => ?_
  have key : A v = ∑ j, (((v j).re : ℝ) • A (Pi.single j (1 : ℂ))
      + ((v j).im : ℝ) • A (Pi.single j Complex.I)) := by
    conv_lhs => rw [eq_sum_single v]
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_add, map_smul, map_smul]
  rw [key]
  calc ‖∑ j, (((v j).re : ℝ) • A (Pi.single j (1 : ℂ))
        + ((v j).im : ℝ) • A (Pi.single j Complex.I))‖
      ≤ ∑ j, ‖((v j).re : ℝ) • A (Pi.single j (1 : ℂ))
        + ((v j).im : ℝ) • A (Pi.single j Complex.I)‖ := norm_sum_le _ _
    _ ≤ ∑ j, (‖A (Pi.single j (1 : ℂ))‖ + ‖A (Pi.single j Complex.I)‖) * ‖v‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        have hre : |(v j).re| ≤ ‖v‖ := le_trans (Complex.abs_re_le_norm _) (norm_le_pi_norm v j)
        have him : |(v j).im| ≤ ‖v‖ := le_trans (Complex.abs_im_le_norm _) (norm_le_pi_norm v j)
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        nlinarith [norm_nonneg (A (Pi.single j (1 : ℂ))),
          norm_nonneg (A (Pi.single j Complex.I)), hre, him, norm_nonneg v]
    _ = (∑ j, (‖A (Pi.single j (1 : ℂ))‖ + ‖A (Pi.single j Complex.I)‖)) * ‖v‖ := by
        rw [Finset.sum_mul]

end Work.NN.Core
