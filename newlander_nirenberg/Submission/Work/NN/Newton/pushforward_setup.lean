import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc

/-!
# Setup for the push-forward of a nearly standard structure (`Work.NN.Newton.pushforward_small`)

This module fixes the objects used by `Work.NN.Newton.pushforward_small`.

For `v : Fin n → ℂⁿ → ℂ` (the correction), `A : ℂⁿ → ℂⁿ →L[ℝ] ℂⁿ` (the perturbation of the
standard structure) we define

* `Phi v : ℂⁿ → ℂⁿ`, `z ↦ (z_l - v_l z)_l`, the near-identity map;
* `DvCLM v z`, the continuous linear map `h ↦ (dv_l(z) h)_l`, so that
  `fderiv ℝ (Phi v) z = 1 - DvCLM v z`;
* `Minv v z = (1 - DvCLM v z)⁻¹` (`Ring.inverse`, which is the genuine inverse whenever
  `‖DvCLM v z‖ < 1`, in particular on every set where `‖v‖_{C^{2,α}}` is small);
* `Alin A z = (i/2) • (A z ∘ A z)`, the `ℂ`-linear part `(A z - Jstd ∘ A z ∘ Jstd)/2` of `A z`
  (the equality uses `(Jstd + A z)² = -1`);
* `EVec A v k z`, the residual vector `(Lcoef A (·)_j k z − ∂̄_k v_j z)_j`;
* `Bop A v z = (1 - DvCLM v z) ∘ (Jstd + A z) − Jstd ∘ (1 - DvCLM v z)`, the defect of the
  intertwining of `Phi v` with the two structures;
* `Aop A v z = Bop A v z ∘ Minv v z`, the pushed-forward perturbation at the point `z` (i.e.
  `A'(Phi v z) = Aop A v z`).

The pointwise identity proved in `pushforward_small` is

`Bop A v z h = Alin A z h − Σ_k conj(h_k) • Alin A z e_k − 2i Σ_k conj(h_k) • EVec A v k z
  − DvCLM v z (A z h)`.
-/

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Newton

/-- The polydisc of uniform radius `R` around the origin of `ℂⁿ`. -/
def Pd (n : ℕ) (R : ℝ) : Set (Work.NN.Core.Cn n) :=
  Work.CR.Flat.polydisc 0 (fun _ => R)

@[simp] lemma mem_Pd {n : ℕ} {R : ℝ} {z : Work.NN.Core.Cn n} :
    z ∈ Pd n R ↔ ∀ j, ‖z j‖ < R := by
  simp [Pd, Work.CR.Flat.mem_polydisc]

lemma isOpen_Pd (n : ℕ) (R : ℝ) : IsOpen (Pd n R) :=
  Work.CR.Flat.isOpen_polydisc 0 _

lemma convex_Pd (n : ℕ) (R : ℝ) : Convex ℝ (Pd n R) := by
  intro x hx y hy a b ha hb hab
  rw [mem_Pd] at hx hy ⊢
  intro j
  have h1 : (a • x + b • y) j = a • x j + b • y j := rfl
  rw [h1]
  have hstep : ‖a • x j + b • y j‖ ≤ a * ‖x j‖ + b * ‖y j‖ := by
    calc ‖a • x j + b • y j‖ ≤ ‖a • x j‖ + ‖b • y j‖ := norm_add_le _ _
      _ = a * ‖x j‖ + b * ‖y j‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · subst ha0
    have hb1 : b = 1 := by linarith only [hab]
    subst hb1
    simpa using hy j
  · by_cases hb0 : b = 0
    · subst hb0
      have ha1 : a = 1 := by linarith only [hab]
      subst ha1
      simpa using hx j
    · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      calc ‖a • x j + b • y j‖ ≤ a * ‖x j‖ + b * ‖y j‖ := hstep
      _ < a * R + b * R :=
          add_lt_add (mul_lt_mul_of_pos_left (hx j) ha0) (mul_lt_mul_of_pos_left (hy j) hbpos)
      _ = (a + b) * R := by ring
      _ = R := by rw [hab, one_mul]

lemma Pd_mono {n : ℕ} {R R' : ℝ} (h : R ≤ R') : Pd n R ⊆ Pd n R' :=
  fun _ hz j => lt_of_lt_of_le (hz j) h

lemma Pd_closedBall_subset {n : ℕ} {R R' : ℝ} (h : R < R') :
    Metric.closedBall (0 : Work.NN.Core.Cn n) R ⊆ Pd n R' := by
  intro z hz
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hz
  rw [mem_Pd]
  intro j
  calc ‖z j‖ ≤ ‖z‖ := norm_le_pi_norm z j
    _ ≤ R := hz
    _ < R' := h

/-! ## The near-identity map and its derivative -/

/-- `Phi v z = (z_l - v_l z)_l`. -/
def Phi {n : ℕ} (v : Fin n → Work.NN.Core.Cn n → ℂ) (z : Work.NN.Core.Cn n) :
    Work.NN.Core.Cn n :=
  fun l => z l - v l z

@[simp] lemma Phi_apply {n : ℕ} (v : Fin n → Work.NN.Core.Cn n → ℂ) (z : Work.NN.Core.Cn n)
    (l : Fin n) : Phi v z l = z l - v l z := rfl

/-- The derivative of `Phi v` minus the identity: `h ↦ (dv_l(z) h)_l`. -/
def DvCLM {n : ℕ} (v : Fin n → Work.NN.Core.Cn n → ℂ) (z : Work.NN.Core.Cn n) :
    Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n :=
  ContinuousLinearMap.pi (fun l => fderiv ℝ (v l) z)

lemma DvCLM_apply {n : ℕ} (v : Fin n → Work.NN.Core.Cn n → ℂ) (z h : Work.NN.Core.Cn n) :
    DvCLM v z h = fun l => fderiv ℝ (v l) z h := by
  funext l
  rw [DvCLM, ContinuousLinearMap.pi_apply]

/-- The identity endomorphism of `ℂⁿ`. -/
def oneCLM (n : ℕ) : Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n := 1

/-- The standard structure as a constant continuous linear map (`Jstd z = i · id`). -/
def Jc (n : ℕ) : Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n :=
  Complex.I • (1 : Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)

lemma JstdCn_apply_eq (n : ℕ) (z : Work.NN.Core.Cn n) :
    Work.NN.Core.JstdCn n z = Jc n := rfl

/-- `Minv v z` is the inverse of `1 - DvCLM v z` (as a continuous linear map). -/
def Minv {n : ℕ} (v : Fin n → Work.NN.Core.Cn n → ℂ) (z : Work.NN.Core.Cn n) :
    Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n :=
  (Ring.inverse ((1 : Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n) - DvCLM v z) :
    Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)

/-- The derivative of the near-identity map: `d(Phi v) z = 1 - DvCLM v z`. -/
lemma fderiv_Phi {n : ℕ} (v : Fin n → Work.NN.Core.Cn n → ℂ) (z : Work.NN.Core.Cn n)
    (hv : ∀ l, DifferentiableAt ℝ (v l) z) :
    fderiv ℝ (Phi v) z = (1 : Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n) - DvCLM v z := by
  have h1 : (Phi v : Work.NN.Core.Cn n → Work.NN.Core.Cn n)
      = (id : Work.NN.Core.Cn n → Work.NN.Core.Cn n) - (fun y => fun l => v l y) := by
    funext y l
    rfl
  rw [h1, fderiv_sub differentiableAt_id (differentiableAt_pi.mpr hv), fderiv_id, DvCLM,
    fderiv_pi (fun l => hv l)]
  congr 1

/-! ## The linear part of `A` and the residual -/

/-- The `ℂ`-linear part `(i/2)·(A z ∘ A z)` of `A z` (equal to `(A z - Jstd ∘ A z ∘ Jstd)/2`
under the almost-complexity constraint `(Jstd + A z)² = -1`). -/
def Alin {n : ℕ} (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (z : Work.NN.Core.Cn n) : Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n :=
  (Complex.I / 2) • ((A z).comp (A z))

/-- The residual vector `E_k = (Lcoef A z_l k - ∂̄_k v_l)_l`. -/
def EVec {n : ℕ} (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (v : Fin n → Work.NN.Core.Cn n → ℂ) (k : Fin n) (z : Work.NN.Core.Cn n) :
    Work.NN.Core.Cn n :=
  fun j => Work.NN.Core.Lcoef A (fun y => y j) k z - Work.CR.Flat.dbarCoord k (v j) z

/-- The `k`-th conjugate-coordinate functional `u ↦ conj(u_k)`. -/
def conjC (n : ℕ) (k : Fin n) : Work.NN.Core.Cn n →L[ℝ] ℂ :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (ContinuousLinearMap.proj k)

@[simp] lemma conjC_apply (n : ℕ) (k : Fin n) (u : Work.NN.Core.Cn n) :
    conjC n k u = Complex.conjCLE (u k) := by
  simp [conjC]

/-- `Bop A v z = dΦ(z)∘(Jstd + A z) - Jstd∘dΦ(z)`. -/
def Bop {n : ℕ} (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (v : Fin n → Work.NN.Core.Cn n → ℂ) (z : Work.NN.Core.Cn n) :
    Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n :=
  ((1 : Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n) - DvCLM v z).comp
      (Work.NN.Core.JstdCn n z + A z)
    - (Work.NN.Core.JstdCn n z).comp
      ((1 : Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n) - DvCLM v z)

/-- `Aop A v z = Bop A v z ∘ Minv v z`, the pushed-forward perturbation at `z`. -/
def Aop {n : ℕ} (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (v : Fin n → Work.NN.Core.Cn n → ℂ) (z : Work.NN.Core.Cn n) :
    Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n :=
  (Bop A v z).comp (Minv v z)

end Work.NN.Newton
