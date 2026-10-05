import Mathlib
import Submission.Work.RPB.B5.LagData

/-!
# B5: `(τ,t,σ) ↦ W τ t (ρh τ t σ)` is `C⁸` on the slab `[0,1] × ℝ × (-κ, κ)`

The chart `W` of the chord annulus is `C⁸` on the box `[0,1] × ℝ × (-ρ₀, ρ₀)` (`LagData.hWsm`)
and the level inverse `ρh` is `C⁸` on `[0,1] × ℝ × (-κ, κ)` (`LagData.hρh`), with values in
`(-ρ₀, ρ₀)` (`LagData.hρhv`).  Hence the composite `(τ,t,σ) ↦ W τ t (ρh τ t σ)` is `C⁸` on the
smaller slab: it is the composition of the `C⁸` map `z ↦ (z.1, z.2.1, ρh z.1 z.2.1 z.2.2)`, whose
range lies in the box of `W` by `LagData.hρhv`, with the `C⁸` chart function of `W`.
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

theorem chartLev_W_rho_contDiffOn (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) (D : Work.RPB.B5.LagData CI a) :
    ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => D.W z.1 z.2.1 (D.ρh z.1 z.2.1 z.2.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-D.κ) D.κ) := by
  -- `ha` is part of the interface; the smoothness does not need the phase lift
  have _ha : Work.RPB.IsChordPhase CI.c a := ha
  -- the exponentiation map `z ↦ (z.1, z.2.1, ρh z.1 z.2.1 z.2.2)` is `C⁸`
  have hf : ContDiffOn ℝ 8
      (fun z : ℝ × (ℝ × ℝ) => (z.1, (z.2.1, D.ρh z.1 z.2.1 z.2.2)))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-D.κ) D.κ) := by
    refine ContDiffOn.prodMk contDiff_fst.contDiffOn ?_
    refine ContDiffOn.prodMk (contDiff_fst.comp contDiff_snd).contDiffOn ?_
    exact D.hρh
  -- and it maps the small slab into the box of the chart, by `ρh ∈ (-ρ₀, ρ₀)`
  have hmap : Set.MapsTo (fun z : ℝ × (ℝ × ℝ) => (z.1, (z.2.1, D.ρh z.1 z.2.1 z.2.2)))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-D.κ) D.κ)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-D.ρ₀) D.ρ₀) := by
    intro z hz
    obtain ⟨hz1, -, hz2⟩ := hz
    exact ⟨hz1, Set.mem_univ _, D.hρhv z.1 hz1 z.2.1 z.2.2 hz2⟩
  exact D.hWsm.comp hf hmap

end Work.RPB.B5
