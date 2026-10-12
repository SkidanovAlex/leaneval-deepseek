import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Work.BoseB1Cube.chiFibreDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Fubini factorisation of the fibre kernel over the coordinate box

The product `∏ j, chiFibreK M (A j) (B j) (u.ofLp j)` is a product of functions of a single
coordinate, so integrating it over the box `{u : EuclideanSpace ℝ (Fin 3) | ∀ j, |u j| ≤ s}`
factorises into the product of the one-dimensional integrals over `[-s,s]`.

The proof is the standard Fubini argument: the box is the image under the (volume preserving)
measurable equivalence `WithLp.toLp 2 : (Fin 3 → ℝ) ≃ᵐ EuclideanSpace ℝ (Fin 3)` of the product
`∏ j [−s,s]`; on the product space `volume = Measure.pi (fun _ => volume)`, and restricting the
product measure to a product of sets is the product of the restricted measures
(`Measure.restrict_pi_pi`), after which `integral_fintype_prod_eq_prod` is Fubini.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseB1Cube

/-- The cube `{u : EuclideanSpace ℝ (Fin 3) | ∀ j, |u.ofLp j| ≤ s}` is the image under the
coordinate equivalence `WithLp.toLp 2` of the product of the intervals `[-s,s]`. -/
lemma box_eq_image_pi_Icc (s : ℝ) :
    {u : EuclideanSpace ℝ (Fin 3) | ∀ j : Fin 3, |u.ofLp j| ≤ s}
      = WithLp.toLp 2 '' (Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (-s) s)) := by
  ext u
  constructor
  · intro hu
    refine ⟨u.ofLp, ?_, WithLp.toLp_ofLp 2 u⟩
    intro j _
    exact abs_le.mp (hu j)
  · rintro ⟨x, hx, rfl⟩ j
    have h := Set.mem_Icc.mp (hx j (Set.mem_univ j))
    rw [WithLp.ofLp_toLp]
    exact abs_le.mpr h

/-- Fubini factorisation of the coordinatewise product of one-dimensional fibre kernels over the
coordinate cube `[-s,s]³`. -/
theorem chiFibreProd (M : ℕ) (A B : Fin 3 → ℝ) (s : ℝ) :
    (∫ u in {u : EuclideanSpace ℝ (Fin 3) | ∀ j : Fin 3, |u.ofLp j| ≤ s},
        ∏ j : Fin 3, Work.BoseB1Cube.chiFibreK M (A j) (B j) (u.ofLp j))
      = ∏ j : Fin 3, ∫ t in Set.Icc (-s) s, Work.BoseB1Cube.chiFibreK M (A j) (B j) t := by
  have hmp : MeasurePreserving (WithLp.toLp 2 : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3))
      (volume : Measure (Fin 3 → ℝ)) (volume : Measure (EuclideanSpace ℝ (Fin 3))) :=
    PiLp.volume_preserving_toLp (Fin 3)
  have hemb : MeasurableEmbedding
      (WithLp.toLp 2 : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)) :=
    MeasurableEquiv.measurableEmbedding (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))
  calc (∫ u in {u : EuclideanSpace ℝ (Fin 3) | ∀ j : Fin 3, |u.ofLp j| ≤ s},
          ∏ j : Fin 3, Work.BoseB1Cube.chiFibreK M (A j) (B j) (u.ofLp j))
      = ∫ x in Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (-s) s),
          ∏ j : Fin 3, Work.BoseB1Cube.chiFibreK M (A j) (B j)
            ((WithLp.toLp 2 x).ofLp j) := by
        rw [box_eq_image_pi_Icc]
        exact hmp.setIntegral_image_emb hemb _ _
    _ = ∫ x in Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (-s) s),
          ∏ j : Fin 3, Work.BoseB1Cube.chiFibreK M (A j) (B j) (x j) := by
        rfl
    _ = ∏ j : Fin 3, ∫ t in Set.Icc (-s) s, Work.BoseB1Cube.chiFibreK M (A j) (B j) t := by
        rw [MeasureTheory.volume_pi, MeasureTheory.Measure.restrict_pi_pi]
        exact MeasureTheory.integral_fintype_prod_eq_prod
          (fun j t => Work.BoseB1Cube.chiFibreK M (A j) (B j) t)

end Work.BoseB1Cube
