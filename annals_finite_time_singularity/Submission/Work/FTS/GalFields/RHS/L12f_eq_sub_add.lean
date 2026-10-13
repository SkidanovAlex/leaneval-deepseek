import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.LocData.L12_add_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalFields.RHS

theorem L12f_eq_sub_add {a b : ℝ → ℝ → ℝ} {z : ℝ}
    (h1 : ∀ s ∈ Set.Ioi z, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * a s θ / s) Work.Spaces.Iθ)
    (h2 : ∀ s ∈ Set.Ioi z, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * b s θ / s) Work.Spaces.Iθ)
    (h3 : MeasureTheory.IntegrableOn (Work.Construction.L12dens a) (Set.Ioi z))
    (h4 : MeasureTheory.IntegrableOn (Work.Construction.L12dens b) (Set.Ioi z)) :
    Work.Coercivity.L12f a z
      = Work.Coercivity.L12f (fun z θ => a z θ - b z θ) z + Work.Coercivity.L12f b z := by
  -- `L₁₂` is an integral of the density, so it is enough to compute the density of `a - b`.
  -- At the level of the angular density the integrands subtract pointwise, and the two
  -- `θ`-slices of `a`, `b` are integrable (`h1`, `h2`), so `integral_sub` applies.
  have hdens : ∀ s ∈ Set.Ioi z,
      Work.Construction.L12dens (fun z θ => a z θ - b z θ) s
        = Work.Construction.L12dens a s - Work.Construction.L12dens b s := by
    intro s hs
    have hpt : (fun θ => Work.Spaces.K θ * (a s θ - b s θ) / s)
        = fun θ => Work.Spaces.K θ * a s θ / s - Work.Spaces.K θ * b s θ / s := by
      funext θ; ring
    simp only [Work.Construction.L12dens, Work.FM.L12dens]
    rw [hpt]
    exact MeasureTheory.integral_sub (h1 s hs) (h2 s hs)
  -- The `θ`-slice of `a - b` is integrable (difference of the two integrable slices).
  have hslice : ∀ s ∈ Set.Ioi z, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * (a s θ - b s θ) / s) Work.Spaces.Iθ := by
    intro s hs
    refine ((h1 s hs).sub (h2 s hs)).congr_fun (fun θ _ => ?_) measurableSet_Icc
    simp only [Pi.sub_apply]
    ring
  -- The density of `a - b` is integrable on `(z,∞)` (`hdens`, `h3`, `h4`).
  have hdensInt : MeasureTheory.IntegrableOn
      (Work.Construction.L12dens (fun z θ => a z θ - b z θ)) (Set.Ioi z) := by
    refine (h3.sub h4).congr_fun (fun s hs => ?_) measurableSet_Ioi
    exact (hdens s hs).symm
  -- Additivity of `L₁₂` on the pair `(a - b, b)`, with `a - b + b = a`.
  obtain ⟨hadd, -⟩ := Work.FTS.LocData.L12_add_mul (c := (0 : ℝ)) hslice h2 hdensInt h4
  have hfun : (fun z θ => (a z θ - b z θ) + b z θ) = a := by
    funext z θ; ring
  rw [hfun] at hadd
  -- `Work.Coercivity.L12f` and `Work.Construction.L12` are the same function (`rfl`).
  change Work.Construction.L12 a z
      = Work.Construction.L12 (fun z θ => a z θ - b z θ) z + Work.Construction.L12 b z
  exact hadd

end Work.FTS.GalFields.RHS
