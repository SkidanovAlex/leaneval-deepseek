import Mathlib
import Submission.Work.Mostow.fermi_measurePreserving
import Submission.Work.Mostow.fermi_inv

/-!
# Volume of a Fermi-product rectangle

`Work.Mostow.fermi_measurePreserving` says that the Fermi chart map
`(v, w) ↦ fermi k m v w` pushes the product measure `(volH k).prod (tubeMeasure k m)`
forward to `volH (k + m)`.  Here we extract the consequence on a *rectangle*: for measurable
`A ⊆ E j` and `B ⊆ E m`,

  `volH (j+m) (fermi '' (A ×ˢ B)) = volH j A * tubeMeasure j m B`.

The Fermi map is a bijection onto `E (j+m)` with explicit inverse `fermiInv`
(`Work.Mostow.fermi_inv`); measurability of that inverse is what turns the push-forward
identity into the set-level statement, via `MeasurableEmbedding.map_apply`.
-/

namespace Work.Mostow

open Submission.Mostow MeasureTheory

noncomputable section

/-! ## Measurability of the Fermi chart inverse -/

private lemma continuous_tanC_aux (k m : ℕ) : Continuous (tanC k m) := by
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

private lemma continuous_nrmC_aux (k m : ℕ) : Continuous (nrmC k m) := by
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

/-- The explicit Euclidean inverse of the Fermi scaling map is measurable. -/
private lemma measurable_ginv_aux (k m : ℕ) : Measurable (ginv k m) := by
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
private lemma measurable_fermiInv_aux (k m : ℕ) : Measurable (fermiInv k m) := by
  rw [show fermiInv k m = fun u : E (k + m) => ginv k m (tanC k m u, nrmC k m u) from rfl]
  exact (measurable_ginv_aux k m).comp
    (Measurable.prod (continuous_tanC_aux k m).measurable (continuous_nrmC_aux k m).measurable)

/-- The normal-fibre measure `tubeMeasure k m` is `σ`-finite (it is a `withDensity` of Lebesgue
measure), which is what `Measure.prod_prod` needs. -/
private instance instSFinite_tubeMeasure (k m : ℕ) : SFinite (tubeMeasure k m) := by
  unfold tubeMeasure
  infer_instance

/-! ## The rectangle identity -/

theorem volH_fermi_prod (j m : ℕ) (A : Set (Submission.Mostow.E j)) (B : Set (Submission.Mostow.E m))
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Submission.Mostow.volH (j + m) ((fun p : Submission.Mostow.E j × Submission.Mostow.E m => Submission.Mostow.fermi j m p.1 p.2) '' (A ×ˢ B))
      = Submission.Mostow.volH j A * Submission.Mostow.tubeMeasure j m B := by
  classical
  set f : E j × E m → E (j + m) := fun p => fermi j m p.1 p.2 with hf
  have hfmeas : Measurable f := by
    have h : f = fun p => prodeMap j m (gmap j m p) := by rw [hf]; rfl
    rw [h]
    exact (measurePreserving_prodeMap j m).measurable.comp (measurable_gmap j m)
  have hleft : Function.LeftInverse (fermiInv j m) f := by
    intro p
    rw [hf]
    exact (fermi_inv j m).1 p.1 p.2
  have hsurj : Set.range f = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro u
    exact ⟨fermiInv j m u, by rw [hf]; exact (fermi_inv j m).2.1 u⟩
  have hemb : MeasurableEmbedding f :=
    MeasurableEmbedding.of_measurable_inverse hfmeas (by rw [hsurj]; exact MeasurableSet.univ)
      (measurable_fermiInv_aux j m) hleft
  have hmap : Measure.map f ((volH j).prod (tubeMeasure j m)) = volH (j + m) := by
    rw [hf]
    exact (fermi_measurePreserving j m).map_eq
  have hset : MeasurableSet (f '' (A ×ˢ B)) := hemb.measurableSet_image.mpr (hA.prod hB)
  calc volH (j + m) (f '' (A ×ˢ B))
      = (Measure.map f ((volH j).prod (tubeMeasure j m))) (f '' (A ×ˢ B)) := by rw [hmap]
    _ = ((volH j).prod (tubeMeasure j m)) (f ⁻¹' (f '' (A ×ˢ B))) :=
          Measure.map_apply hemb.measurable hset
    _ = ((volH j).prod (tubeMeasure j m)) (A ×ˢ B) := by
          rw [Set.preimage_image_eq (A ×ˢ B) hemb.injective]
    _ = volH j A * tubeMeasure j m B := Measure.prod_prod A B

end

end Work.Mostow
