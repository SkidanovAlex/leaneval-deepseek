import Mathlib
import Submission.Work.Mostow.fermiW_chart
import Submission.Work.Mostow.nearId_blk

/-!
# Volume of a `fermiW`-product rectangle

`Work.Mostow.fermiW_measurePreserving` (in `fermiW_chart.lean`) says that the `fermiW` chart map
`(v, W) ↦ fermiW 1 m v W = prodeMap 1 m (tpart W • v, W)` pushes the product measure
`(volH 1).prod volume` forward to `volH (1 + m)`.  Here we extract the consequence on a
*rectangle*: for measurable `A ⊆ E 1` and `B ⊆ E m`,

  `volH (1+m) (fermiW 1 m '' (A ×ˢ B)) = volH 1 A * volume B`.

The chart map is a bijection `E 1 × E m → E (1 + m)`, whose explicit inverse is
`fwInv u = (tpart (nrmC 1 m u)⁻¹ • tanC 1 m u, nrmC 1 m u)`; measurability of that inverse is
what turns the push-forward identity into the set-level statement via `MeasurableEmbedding`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped ENNReal

noncomputable section

/-! ## Continuity of the chart coordinates -/

private lemma cont_tanC (k m : ℕ) : Continuous (tanC k m) := by
  rw [show tanC k m = (WithLp.toLp 2 : (Fin k → ℝ) → E k) ∘
      (fun g : Fin (k + m) → ℝ => fun i : Fin k => g (Fin.castAdd m i)) ∘
      (WithLp.ofLp : E (k + m) → (Fin (k + m) → ℝ)) from rfl]
  exact (PiLp.continuous_toLp 2 (fun _ : Fin k => ℝ)).comp
    ((continuous_pi (fun i => continuous_apply (Fin.castAdd m i))).comp
      (PiLp.continuous_ofLp 2 (fun _ : Fin (k + m) => ℝ)))

private lemma cont_nrmC (k m : ℕ) : Continuous (nrmC k m) := by
  rw [show nrmC k m = (WithLp.toLp 2 : (Fin m → ℝ) → E m) ∘
      (fun g : Fin (k + m) → ℝ => fun i : Fin m => g (Fin.natAdd k i)) ∘
      (WithLp.ofLp : E (k + m) → (Fin (k + m) → ℝ)) from rfl]
  exact (PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ)).comp
    ((continuous_pi (fun i => continuous_apply (Fin.natAdd k i))).comp
      (PiLp.continuous_ofLp 2 (fun _ : Fin (k + m) => ℝ)))

/-! ## The explicit inverse of the `fermiW` chart -/

/-- Inverse of the `fermiW` chart: from `u = (x, W) ∈ E 1 × E m` recover `(v, W)` with `x = tpart W • v`. -/
private def fwInv (m : ℕ) (u : E (1 + m)) : E 1 × E m :=
  ((Real.sqrt (1 + ‖nrmC 1 m u‖ ^ 2))⁻¹ • tanC 1 m u, nrmC 1 m u)

private lemma cont_fwInv (m : ℕ) : Continuous (fwInv m) := by
  rw [show fwInv m = fun u : E (1 + m) =>
      ((Real.sqrt (1 + ‖nrmC 1 m u‖ ^ 2))⁻¹ • tanC 1 m u, nrmC 1 m u) from rfl]
  refine Continuous.prodMk ?_ ?_
  · have hscal : Continuous (fun u : E (1 + m) =>
        (Real.sqrt (1 + ‖nrmC 1 m u‖ ^ 2))⁻¹) :=
      Continuous.inv₀ (Real.continuous_sqrt.comp
        (continuous_const.add ((cont_nrmC 1 m).norm.pow 2))) (fun u => by positivity)
    have htan : Continuous (fun u : E (1 + m) => tanC 1 m u) := cont_tanC 1 m
    exact hscal.smul htan
  · exact cont_nrmC 1 m

private lemma fwInv_fermiW (m : ℕ) (v : E 1) (W : E m) :
    fwInv m (fermiW 1 m v W) = (v, W) := by
  refine Prod.ext ?_ ?_
  · show (Real.sqrt (1 + ‖nrmC 1 m (fermiW 1 m v W)‖ ^ 2))⁻¹ • tanC 1 m (fermiW 1 m v W) = v
    rw [nib_nrmC_fermiW, nib_tanC_fermiW, smul_smul,
      inv_mul_cancel₀ (by positivity : Real.sqrt (1 + ‖W‖ ^ 2) ≠ 0), one_smul]
  · show nrmC 1 m (fermiW 1 m v W) = W
    rw [nib_nrmC_fermiW]

private lemma fwInv_surj (m : ℕ) (u : E (1 + m)) :
    fermiW 1 m (fwInv m u).1 (fwInv m u).2 = u :=
  nib_fermiW_surj m u

/-! ## The rectangle identity -/

theorem volH_fermiW_prod (m : ℕ) (A : Set (Submission.Mostow.E 1)) (B : Set (Submission.Mostow.E m))
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Submission.Mostow.volH (1 + m)
        ((fun p : Submission.Mostow.E 1 × Submission.Mostow.E m =>
            Submission.Mostow.fermiW 1 m p.1 p.2) '' (A ×ˢ B))
      = Submission.Mostow.volH 1 A * (MeasureTheory.volume : MeasureTheory.Measure (Submission.Mostow.E m)) B := by
  classical
  set f : E 1 × E m → E (1 + m) := fun p => fermiW 1 m p.1 p.2 with hf
  have hfmeas : Measurable f := (fermiW_measurePreserving m).measurable
  have hleft : Function.LeftInverse (fwInv m) f := by
    intro p; obtain ⟨v, W⟩ := p; exact fwInv_fermiW m v W
  have hsurj : Set.range f = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro u
    exact ⟨fwInv m u, by rw [hf]; exact fwInv_surj m u⟩
  have hemb : MeasurableEmbedding f :=
    MeasurableEmbedding.of_measurable_inverse hfmeas (by rw [hsurj]; exact MeasurableSet.univ)
      (cont_fwInv m).measurable hleft
  have hmap : Measure.map f ((volH 1).prod (volume : Measure (E m))) = volH (1 + m) := by
    rw [hf]; exact (fermiW_measurePreserving m).map_eq
  have hset : MeasurableSet (f '' (A ×ˢ B)) := hemb.measurableSet_image.mpr (hA.prod hB)
  calc volH (1 + m) (f '' (A ×ˢ B))
      = (Measure.map f ((volH 1).prod (volume : Measure (E m)))) (f '' (A ×ˢ B)) := by rw [hmap]
    _ = ((volH 1).prod (volume : Measure (E m))) (f ⁻¹' (f '' (A ×ˢ B))) :=
          Measure.map_apply hfmeas hset
    _ = ((volH 1).prod (volume : Measure (E m))) (A ×ˢ B) := by
          rw [Set.preimage_image_eq (A ×ˢ B) hemb.injective]
    _ = volH 1 A * (volume : Measure (E m)) B := Measure.prod_prod A B

end

end Work.Mostow
