import Mathlib
import Submission.Work.Mostow.fermiW_chart
import Submission.Work.Mostow.nearId_blk
import Submission.Work.Mostow.fermi_inv

/-!
# Measurability of the image of a rectangle under the `fermiW` chart

`Submission.Mostow.fermiW k m : E k × E m → E (k + m)` is the Euclidean-coordinate chart of a point
about the standard stratum: `fermiW k m v W = (√(1+‖W‖²)·v, W)`, i.e. `fermi k m v (wOf W)`.

For `k = 1` it is a bijection `E 1 × E m → E (1+m)` with the *explicit, measurable* inverse

  `fermiWInv m u = ((√(1+‖nrmC 1 m u‖²))⁻¹ • tanC 1 m u, nrmC 1 m u)`

(`tanC`/`nrmC` are the tangential/normal chart coordinates).  Hence for every `S`,
`fermiW '' S = fermiWInv ⁻¹' S`, and the image of a measurable rectangle is measurable.

This is the `fermiW`-analogue of `Work.Mostow.fermi_image_measurable`; it is used by the tube
inequality for the `k = 1` geodesic stratum.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

/-! ## The explicit inverse of `fermiW 1 m` -/

/-- The inverse of the chart `fermiW 1 m : E 1 × E m → E (1+m)`:
recover `W = nrmC 1 m u` from the normal coordinates and `v` from the tangential ones by dividing
by `√(1+‖W‖²)`. -/
private def fermiWInv (m : ℕ) (u : E (1 + m)) : E 1 × E m :=
  ((Real.sqrt (1 + ‖nrmC 1 m u‖ ^ 2))⁻¹ • tanC 1 m u, nrmC 1 m u)

private lemma continuous_tanC_image (k m : ℕ) : Continuous (tanC k m) := by
  have hmid : Continuous (fun g : Fin (k + m) → ℝ => fun i : Fin k => g (Fin.castAdd m i)) :=
    continuous_pi fun i => continuous_apply (Fin.castAdd m i)
  have hof : Continuous (WithLp.ofLp : E (k + m) → (Fin (k + m) → ℝ)) :=
    PiLp.continuous_ofLp 2 (fun _ : Fin (k + m) => ℝ)
  have hto : Continuous (WithLp.toLp 2 : (Fin k → ℝ) → E k) :=
    PiLp.continuous_toLp 2 (fun _ : Fin k => ℝ)
  rw [show tanC k m = (WithLp.toLp 2 : (Fin k → ℝ) → E k) ∘
      (fun g : Fin (k + m) → ℝ => fun i : Fin k => g (Fin.castAdd m i)) ∘
      (WithLp.ofLp : E (k + m) → (Fin (k + m) → ℝ)) from rfl]
  exact hto.comp (hmid.comp hof)

private lemma continuous_nrmC_image (k m : ℕ) : Continuous (nrmC k m) := by
  have hmid : Continuous (fun g : Fin (k + m) → ℝ => fun i : Fin m => g (Fin.natAdd k i)) :=
    continuous_pi fun i => continuous_apply (Fin.natAdd k i)
  have hof : Continuous (WithLp.ofLp : E (k + m) → (Fin (k + m) → ℝ)) :=
    PiLp.continuous_ofLp 2 (fun _ : Fin (k + m) => ℝ)
  have hto : Continuous (WithLp.toLp 2 : (Fin m → ℝ) → E m) :=
    PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ)
  rw [show nrmC k m = (WithLp.toLp 2 : (Fin m → ℝ) → E m) ∘
      (fun g : Fin (k + m) → ℝ => fun i : Fin m => g (Fin.natAdd k i)) ∘
      (WithLp.ofLp : E (k + m) → (Fin (k + m) → ℝ)) from rfl]
  exact hto.comp (hmid.comp hof)

private lemma measurable_fermiWInv (m : ℕ) : Measurable (fermiWInv m) := by
  have hnrm : Measurable (fun u : E (1 + m) => nrmC 1 m u) :=
    (continuous_nrmC_image 1 m).measurable
  have htan : Measurable (fun u : E (1 + m) => tanC 1 m u) :=
    (continuous_tanC_image 1 m).measurable
  have hcoef : Measurable (fun u : E (1 + m) => (Real.sqrt (1 + ‖nrmC 1 m u‖ ^ 2))⁻¹) :=
    ((Real.continuous_sqrt.measurable).comp (measurable_const.add (hnrm.norm.pow_const 2))).inv
  exact Measurable.prod (hcoef.smul htan) hnrm

private lemma fermiWInv_left (m : ℕ) (v : E 1) (W : E m) :
    fermiWInv m (fermiW 1 m v W) = (v, W) := by
  refine Prod.ext ?_ ?_
  · show (Real.sqrt (1 + ‖nrmC 1 m (fermiW 1 m v W)‖ ^ 2))⁻¹ • tanC 1 m (fermiW 1 m v W) = v
    rw [nib_nrmC_fermiW, nib_tanC_fermiW, smul_smul,
      inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos_of_pos (by positivity))), one_smul]
  · show nrmC 1 m (fermiW 1 m v W) = W
    rw [nib_nrmC_fermiW]

private lemma fermiWInv_right (m : ℕ) (u : E (1 + m)) :
    fermiW 1 m (fermiWInv m u).1 (fermiWInv m u).2 = u := by
  show fermiW 1 m ((Real.sqrt (1 + ‖nrmC 1 m u‖ ^ 2))⁻¹ • tanC 1 m u) (nrmC 1 m u) = u
  exact nib_fermiW_surj m u

/-! ## The image of a rectangle -/

theorem fermiW_image_measurable (m : ℕ) (A : Set (Submission.Mostow.E 1)) (B : Set (Submission.Mostow.E m))
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    MeasurableSet ((fun p : Submission.Mostow.E 1 × Submission.Mostow.E m =>
        Submission.Mostow.fermiW 1 m p.1 p.2) '' (A ×ˢ B)) := by
  have hset : (fun p : E 1 × E m => fermiW 1 m p.1 p.2) '' (A ×ˢ B)
      = (fermiWInv m) ⁻¹' (A ×ˢ B) := by
    ext u
    constructor
    · rintro ⟨p, hp, rfl⟩
      show fermiWInv m (fermiW 1 m p.1 p.2) ∈ A ×ˢ B
      rw [fermiWInv_left m p.1 p.2]
      exact hp
    · intro hu
      exact ⟨fermiWInv m u, hu, fermiWInv_right m u⟩
  rw [hset]
  exact (measurable_fermiWInv m) (hA.prod hB)

end

end Work.Mostow
