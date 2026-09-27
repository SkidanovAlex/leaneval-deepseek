import Mathlib
import Submission.Work.Mostow.tiDefs
import Submission.Work.Mostow.volH_fermi_prod

/-!
# Measurability of the image of a rectangle under the Fermi chart

`Submission.Mostow.fermi j m : E j × E m → E (j + m)` is the Fermi chart of a point about the
standard stratum: foot `v ∈ E j` and normal vector `w ∈ E m`.  It is a bijection
(`Work.Mostow.fermi_inv`) with explicit inverse `Submission.Mostow.fermiInv`.

Here we record the set-level consequence used by the tube-inequality chapter (G3'): for measurable
`A ⊆ E j` and `B ⊆ E m`, the image `fermi '' (A ×ˢ B)` is measurable.

The proof is the standard one: `fermi` is a bijection with the *measurable* explicit inverse
`fermiInv`, hence `fermi '' S = fermiInv ⁻¹' S` for every `S`; measurability of `fermiInv` is the
only analytic input.  (This is the same computation as in `Work.Mostow.volH_fermi_prod`, but with
the measurability conclusion extracted instead of the measure identity.)
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

/-! ## Measurability of the chart inverse -/

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

/-- The Euclidean inverse of the Fermi scaling map is measurable. -/
private lemma measurable_ginv_image (k m : ℕ) : Measurable (ginv k m) := by
  classical
  have hnorm : Measurable (fun y : E k × E m => ‖y.2‖) := continuous_snd.norm.measurable
  have hars : Measurable (fun y : E k × E m => Real.arsinh ‖y.2‖) :=
    Real.continuous_arsinh.measurable.comp hnorm
  have hcosh : Measurable (fun y : E k × E m => Real.cosh (Real.arsinh ‖y.2‖)) :=
    Real.measurable_cosh.comp hars
  rw [show ginv k m = fun y : E k × E m =>
      ((Real.cosh (Real.arsinh ‖y.2‖))⁻¹ • y.1,
       if y.2 = 0 then 0 else (Real.arsinh ‖y.2‖ / ‖y.2‖) • y.2) from rfl]
  refine Measurable.prod ?_ ?_
  · exact (hcosh.inv).smul measurable_fst
  · refine Measurable.ite ?_ measurable_const ?_
    · exact (measurableSet_singleton (0 : E m)).preimage measurable_snd
    · exact (hars.div hnorm).smul measurable_snd

/-- The Fermi chart inverse `fermiInv k m : E (k+m) → E k × E m` is measurable. -/
private lemma measurable_fermiInv_image (k m : ℕ) : Measurable (fermiInv k m) := by
  rw [show fermiInv k m = fun u : E (k + m) => ginv k m (tanC k m u, nrmC k m u) from rfl]
  exact (measurable_ginv_image k m).comp
    (Measurable.prod (continuous_tanC_image k m).measurable
      (continuous_nrmC_image k m).measurable)

/-! ## The image of a rectangle -/

theorem fermi_image_measurable (j m : ℕ) (A : Set (Submission.Mostow.E j)) (B : Set (Submission.Mostow.E m))
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    MeasurableSet ((fun p : Submission.Mostow.E j × Submission.Mostow.E m => Submission.Mostow.fermi j m p.1 p.2) '' (A ×ˢ B)) := by
  classical
  have hset : (fun p : E j × E m => fermi j m p.1 p.2) '' (A ×ˢ B)
      = (fermiInv j m) ⁻¹' (A ×ˢ B) := by
    ext u
    constructor
    · rintro ⟨p, hp, rfl⟩
      show fermiInv j m (fermi j m p.1 p.2) ∈ A ×ˢ B
      rw [(fermi_inv j m).1 p.1 p.2]
      exact hp
    · intro hu
      exact ⟨fermiInv j m u, hu, (fermi_inv j m).2.1 u⟩
  rw [hset]
  exact (measurable_fermiInv_image j m) (hA.prod hB)

end

end Work.Mostow
