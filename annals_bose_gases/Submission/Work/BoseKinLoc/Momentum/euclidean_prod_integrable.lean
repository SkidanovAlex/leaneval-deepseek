import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory

namespace Work.BoseKinLoc.Momentum

/-- If each coordinate function `g i : ℝ → ℝ` is integrable (w.r.t. Lebesgue measure on `ℝ`), then
the product function `q ↦ ∏ i, g i (q i)` is integrable on `EuclideanSpace ℝ (Fin 3)`.

The point is that `volume` on `EuclideanSpace ℝ (Fin 3) = WithLp 2 (Fin 3 → ℝ)` is the pushforward
under `WithLp.ofLp` of the product measure `Measure.pi (fun _ ↦ volume)` on `Fin 3 → ℝ`
(`EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp`), and that on a finite product
`Measure.pi` a product of functions of one coordinate is integrable
(`MeasureTheory.Integrable.fintype_prod`). -/
theorem euclidean_prod_integrable {g : Fin 3 → ℝ → ℝ} (hg : ∀ i, MeasureTheory.Integrable (g i)) :
    MeasureTheory.Integrable (fun q : EuclideanSpace ℝ (Fin 3) => ∏ i, g i (q i)) := by
  -- Integrability on the plain product space `Fin 3 → ℝ` w.r.t. the product measure.
  have h1 : MeasureTheory.Integrable (fun x : Fin 3 → ℝ => ∏ i, g i (x i))
      (MeasureTheory.Measure.pi fun _ : Fin 3 => (volume : Measure ℝ)) :=
    MeasureTheory.Integrable.fintype_prod (fun i => hg i)
  -- `volume` on `Fin 3 → ℝ` is the product of the Lebesgue measures on the coordinates.
  rw [← MeasureTheory.volume_pi] at h1
  -- Transport along the volume preserving measurable equivalence
  -- `WithLp.ofLp : EuclideanSpace ℝ (Fin 3) → (Fin 3 → ℝ)`.
  exact ((EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _)).mpr h1

end Work.BoseKinLoc.Momentum
