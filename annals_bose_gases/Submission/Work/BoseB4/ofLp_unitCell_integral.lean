import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB4

open MeasureTheory

/-- The unit cell `{x : ℝ³ | ∀ i, |x i| ≤ 1/2}` of `EuclideanSpace ℝ (Fin 3)` is the image under
`WithLp.ofLp` of the coordinate box `∏ i, [-1/2, 1/2]`, and `WithLp.ofLp` is volume preserving;
hence the integral of `F ∘ WithLp.ofLp` over the unit cell in `EuclideanSpace ℝ (Fin 3)` equals
the integral of `F` over the coordinate box in `Fin 3 → ℝ`. -/
theorem ofLp_unitCell_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : (Fin 3 → ℝ) → E) :
    ∫ x in {x : EuclideanSpace ℝ (Fin 3) | ∀ i, |x i| ≤ (1/2 : ℝ)}, F (WithLp.ofLp x)
      = ∫ y in Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (-(1/2) : ℝ) (1/2)), F y := by
  -- The unit cell is the preimage under `WithLp.ofLp` of the coordinate box.
  have hset : (WithLp.ofLp ⁻¹' (Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (-(1/2) : ℝ) (1/2))))
      = {x : EuclideanSpace ℝ (Fin 3) | ∀ i, |x i| ≤ (1/2 : ℝ)} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc, abs_le,
      Set.mem_ofPred_eq]
  -- `WithLp.ofLp` pushes the (Lebesgue) volume of `EuclideanSpace ℝ (Fin 3)` to the product
  -- Lebesgue measure on `Fin 3 → ℝ`.
  have hmap : Measure.map (WithLp.ofLp : EuclideanSpace ℝ (Fin 3) → (Fin 3 → ℝ)) volume = volume :=
    (PiLp.volume_preserving_ofLp (Fin 3)).map_eq
  -- `WithLp.ofLp` is a measurable embedding (it is the coercion of a measurable equivalence),
  -- so set integrals transform by preimage with no measurability assumption on `F`.
  have hemb : MeasurableEmbedding (WithLp.ofLp : EuclideanSpace ℝ (Fin 3) → (Fin 3 → ℝ)) :=
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.measurableEmbedding
  calc ∫ x in {x : EuclideanSpace ℝ (Fin 3) | ∀ i, |x i| ≤ (1/2 : ℝ)}, F (WithLp.ofLp x)
      = ∫ x in (WithLp.ofLp : EuclideanSpace ℝ (Fin 3) → (Fin 3 → ℝ)) ⁻¹'
              Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (-(1/2) : ℝ) (1/2)),
            F (WithLp.ofLp x) := by rw [hset]
    _ = ∫ y in Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (-(1/2) : ℝ) (1/2)), F y
          ∂Measure.map (WithLp.ofLp : EuclideanSpace ℝ (Fin 3) → (Fin 3 → ℝ)) volume :=
        (hemb.setIntegral_map F _).symm
    _ = ∫ y in Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (-(1/2) : ℝ) (1/2)), F y := by rw [hmap]

end Work.BoseB4
