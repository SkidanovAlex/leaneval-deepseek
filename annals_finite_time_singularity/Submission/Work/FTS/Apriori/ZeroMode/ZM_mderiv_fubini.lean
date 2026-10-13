import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.Apriori.ZeroMode.L12_ZMDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Apriori.ZeroMode

open scoped Real Topology
open MeasureTheory Set Filter

/-- **Fubini for the angular `z`-integral `mdOf` and its tail form `NOf`.**

`mdOf f r = ∫_{Iθ} K(θ) ∂_z f(r,θ) dθ` and `NOf f r = ∫_{(r,∞) × Iθ} K(θ) ∂_z f(z,θ)` are the
inner and the joint form of the same function; the joint integrability hypothesis `H.hint`
therefore makes `mdOf f` integrable on `(0,∞)` and turns `NOf` into the tail integral of
`mdOf`.  Consequently the difference over `(ε,ρ)` is `NOf f ε - NOf f ρ` and the integral over
`(0,∞)` is `NOf f 0`. -/
theorem ZM_mderiv_fubini {α : ℝ} {f : ℝ → ℝ → ℝ} (H : Work.FTS.Apriori.ZeroMode.L12Hyp α f) :
    MeasureTheory.IntegrableOn (Work.FTS.Apriori.ZeroMode.mdOf f) (Set.Ioi 0)
    ∧ (∀ ε ρ : ℝ, 0 < ε → ε < ρ →
        ∫ r in Set.Ioc ε ρ, Work.FTS.Apriori.ZeroMode.mdOf f r
          = Work.FTS.Apriori.ZeroMode.NOf f ε - Work.FTS.Apriori.ZeroMode.NOf f ρ)
    ∧ (∫ r in Set.Ioi 0, Work.FTS.Apriori.ZeroMode.mdOf f r
        = Work.FTS.Apriori.ZeroMode.NOf f 0) := by
  -- The joint integrand, as a function on the product space.
  set g : ℝ × ℝ → ℝ := fun p => Work.Spaces.K p.2 * Work.Spaces.pz f p.1 p.2 with hg_def
  -- `mdOf f` is the first marginal of `g`; `NOf f r` is its integral over `(r,∞) × Iθ`.
  have hgmd : mdOf f = fun r => ∫ θ, g (r, θ) ∂(volume.restrict Work.Spaces.Iθ) := by
    funext r
    simp only [mdOf_eq, hg_def]
  have hgprod : IntegrableOn g (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) (volume.prod volume) := H.hint
  have hgi : Integrable g ((volume.restrict (Set.Ioi 0)).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [MeasureTheory.Measure.prod_restrict (s := Set.Ioi 0) (t := Work.Spaces.Iθ)]
    exact hgprod
  have hInt : IntegrableOn (fun r => ∫ θ, g (r, θ) ∂(volume.restrict Work.Spaces.Iθ))
      (Set.Ioi 0) :=
    hgi.integral_prod_left
  -- Fubini on a rectangle `s × Iθ`.
  have key : ∀ s : Set ℝ, s ⊆ Set.Ioi 0 →
      ∫ r in s, mdOf f r = ∫ p in s ×ˢ Work.Spaces.Iθ, g p := by
    intro s hs
    rw [hgmd]
    exact (MeasureTheory.setIntegral_prod g (hgprod.mono_set (Set.prod_mono hs Subset.rfl))).symm
  -- `NOf f r` is the tail integral of `mdOf f`, for `r ≥ 0`.
  have hN : ∀ r : ℝ, 0 ≤ r → NOf f r = ∫ s in Set.Ioi r, mdOf f s := by
    intro r hr
    rw [key (Set.Ioi r) (Set.Ioi_subset_Ioi hr)]
    simp only [NOf_eq, hg_def]
  refine ⟨?_, ?_, ?_⟩
  · rw [hgmd]; exact hInt
  · intro ε ρ hε hερ
    have hε0 : 0 ≤ ε := le_of_lt hε
    have hρ0 : 0 ≤ ρ := le_of_lt (lt_trans hε hερ)
    rw [hN ε hε0, hN ρ hρ0, ← Set.Ioi_sdiff_Ioi (a := ε) (b := ρ)]
    exact MeasureTheory.setIntegral_sdiff measurableSet_Ioi
      (hInt.mono_set (Set.Ioi_subset_Ioi hε0)) (Set.Ioi_subset_Ioi (le_of_lt hερ))
  · rw [key (Set.Ioi 0) Subset.rfl]
    simp only [NOf_eq, hg_def]

end Work.FTS.Apriori.ZeroMode
