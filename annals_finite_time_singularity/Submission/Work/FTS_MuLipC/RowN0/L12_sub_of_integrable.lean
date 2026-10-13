import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Construction.Defs
import Submission.Work.FTS.LocData.L12_add_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_MuLipC.RowN0

/-- (namespace `Work.FTS_MuLipC.RowN0`) **Additivity of `L₁₂` at `z = 0` in subtraction form.**
If the two `L₁₂`-densities are integrable on `(0,∞)` and the two angular slices
`θ ↦ K(θ)·a r θ/r`, `θ ↦ K(θ)·b r θ/r` are integrable on `Iθ` for every `r > 0`, then
`L₁₂ a 0 − L₁₂ b 0 = L₁₂ (a − b) 0`.  Proof: both sides unfold to integrals of densities; the
density of the difference is the difference of the densities on `(0,∞)`
(`Work.FTS.LocData.L12dens_add_of_integrableOn` applied to `a` and `−b`, together with
`Work.FTS.LocData.L12dens_const_mul`), and the two outer Bochner integrals split by
`MeasureTheory.integral_sub` (the density of `−b` is integrable because `L12dens_const_mul`
gives `L12dens (fun z θ => -b z θ) = - L12dens b` unconditionally, and `hBb` is integrable). -/
theorem L12_sub_of_integrable {a b : ℝ → ℝ → ℝ}
    (hBa : MeasureTheory.IntegrableOn (Work.Construction.L12dens a) (Set.Ioi (0 : ℝ)))
    (hBb : MeasureTheory.IntegrableOn (Work.Construction.L12dens b) (Set.Ioi (0 : ℝ)))
    (hSa : ∀ r ∈ Set.Ioi (0 : ℝ), MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.K θ * a r θ / r) Work.Spaces.Iθ)
    (hSb : ∀ r ∈ Set.Ioi (0 : ℝ), MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.K θ * b r θ / r) Work.Spaces.Iθ) :
    Work.Construction.L12 a 0 - Work.Construction.L12 b 0
      = Work.Construction.L12 (fun z θ => a z θ - b z θ) 0 := by
  -- `a - b` is `a + (-b)`, and `-b` is the constant `(-1)` multiple of `b`
  have hfun_sub : (fun z θ => a z θ - b z θ) = (fun z θ => a z θ + (-b z θ)) := by
    funext z θ; ring
  have hfun_neg : (fun z θ => -b z θ) = (fun z θ => (-1 : ℝ) * b z θ) := by
    funext z θ; rw [neg_one_mul]
  -- the angular slices of `-b = (-1)·b` are integrable
  have hSneg : ∀ r ∈ Set.Ioi (0 : ℝ), MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.K θ * (-b r θ) / r) Work.Spaces.Iθ := by
    intro r hr
    have hfun : (fun θ : ℝ => Work.Spaces.K θ * (-b r θ) / r)
        = fun θ : ℝ => - (Work.Spaces.K θ * b r θ / r) := by
      funext θ; ring
    rw [hfun]
    exact (hSb r hr).neg
  -- the density of `-b` is minus the density of `b`, hence integrable
  have hdens_neg : Work.Construction.L12dens (fun z θ => -b z θ)
      = fun s => - Work.Construction.L12dens b s := by
    funext s
    rw [hfun_neg]
    show Work.FM.L12dens Work.Spaces.K (fun z θ => (-1 : ℝ) * b z θ) s
      = - Work.FM.L12dens Work.Spaces.K b s
    rw [Work.FTS.LocData.L12dens_const_mul Work.Spaces.K (-1) b s, neg_one_mul]
  have hBneg : MeasureTheory.IntegrableOn
      (Work.Construction.L12dens (fun z θ => -b z θ)) (Set.Ioi (0 : ℝ)) := by
    rw [hdens_neg]; exact hBb.neg
  -- additivity of the outer integral
  have hadd : Work.Construction.L12 (fun z θ => a z θ + (-b z θ)) 0
      = Work.Construction.L12 a 0 + Work.Construction.L12 (fun z θ => -b z θ) 0 := by
    simp only [Work.Construction.L12, Work.FM.L12]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun s hs => Work.FTS.LocData.L12dens_add_of_integrableOn Work.Spaces.K
        (hSa s hs) (hSneg s hs))]
    exact MeasureTheory.integral_add hBa hBneg
  -- homogeneity in the constant `-1`
  have hneg : Work.Construction.L12 (fun z θ => -b z θ) 0
      = - Work.Construction.L12 b 0 := by
    rw [hfun_neg, (Work.FTS.LocData.L12_add_mul (-1) hSb hSa hBb hBa).2, neg_one_mul]
  rw [eq_comm, hfun_sub, hadd, hneg]
  ring

end Work.FTS_MuLipC.RowN0
