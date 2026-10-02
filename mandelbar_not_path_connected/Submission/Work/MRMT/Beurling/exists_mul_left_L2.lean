import Mathlib
import Submission.Work.MRMT.Beurling.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Beurling

open MeasureTheory

/-- Multiplication on `L²(ℂ)` by the a.e. bounded measurable function `m`.

We build the operator at the level of `AEEqFun`: the class of `m` is an element `M` of the
ring of a.e. strongly measurable functions, and `M * (f : ℂ →ₘ ℂ)` is again in `L²` because
`‖m ξ * f ξ‖ ≤ ‖f ξ‖` for a.e. `ξ`.  `LinearMap.mkContinuous` then produces a continuous
linear operator of norm `≤ 1`. -/
theorem exists_mul_left_L2 (m : ℂ → ℂ) (hm : MeasureTheory.AEStronglyMeasurable m MeasureTheory.volume)
    (hm1 : ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖m ξ‖ ≤ 1) :
    ∃ T : MeasureTheory.Lp ℂ 2 MeasureTheory.volume →L[ℂ] MeasureTheory.Lp ℂ 2 MeasureTheory.volume,
      ‖T‖ ≤ 1 ∧ ∀ f : MeasureTheory.Lp ℂ 2 MeasureTheory.volume,
        ((T f : MeasureTheory.Lp ℂ 2 MeasureTheory.volume) : ℂ → ℂ) =ᵐ[MeasureTheory.volume]
          fun ξ => m ξ * ((f : MeasureTheory.Lp ℂ 2 MeasureTheory.volume) : ℂ → ℂ) ξ := by
  let M : ℂ →ₘ[(volume : Measure ℂ)] ℂ := AEEqFun.mk m hm
  have hM : ⇑M =ᵐ[(volume : Measure ℂ)] m := AEEqFun.coeFn_mk m hm
  have hMmul : ∀ (g : ℂ →ₘ[(volume : Measure ℂ)] ℂ),
      ⇑(M * g) =ᵐ[(volume : Measure ℂ)] fun ξ => m ξ * g ξ := by
    intro g
    filter_upwards [AEEqFun.coeFn_mul M g, hM] with ξ h1 h2
    rw [h1, Pi.mul_apply, h2]
  have hmem : ∀ f : Lp ℂ 2 (volume : Measure ℂ),
      M * (f : ℂ →ₘ[(volume : Measure ℂ)] ℂ) ∈ Lp ℂ 2 (volume : Measure ℂ) := by
    intro f
    refine Lp.mem_Lp_of_ae_le (g := f) ?_
    filter_upwards [hMmul (f : ℂ →ₘ[(volume : Measure ℂ)] ℂ), hm1] with ξ h1 h2
    rw [h1, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) h2
  let mulLp : Lp ℂ 2 (volume : Measure ℂ) → Lp ℂ 2 (volume : Measure ℂ) :=
    fun f => ⟨M * (f : ℂ →ₘ[(volume : Measure ℂ)] ℂ), hmem f⟩
  have hmulLp : ∀ f : Lp ℂ 2 (volume : Measure ℂ),
      ⇑(mulLp f) =ᵐ[(volume : Measure ℂ)] fun ξ => m ξ * ⇑f ξ := by
    intro f
    exact hMmul (f : ℂ →ₘ[(volume : Measure ℂ)] ℂ)
  have hadd : ∀ f g : Lp ℂ 2 (volume : Measure ℂ), mulLp (f + g) = mulLp f + mulLp g := by
    intro f g
    apply Lp.ext
    filter_upwards [hmulLp (f + g), Lp.coeFn_add f g, Lp.coeFn_add (mulLp f) (mulLp g),
      hmulLp f, hmulLp g] with ξ h1 h2 h3 h4 h5
    rw [h1, h2, h3]
    simp only [Pi.add_apply]
    rw [h4, h5]
    ring
  have hsmul : ∀ (c : ℂ) (f : Lp ℂ 2 (volume : Measure ℂ)), mulLp (c • f) = c • mulLp f := by
    intro c f
    apply Lp.ext
    filter_upwards [hmulLp (c • f), Lp.coeFn_smul c f, Lp.coeFn_smul c (mulLp f),
      hmulLp f] with ξ h1 h2 h3 h4
    rw [h1, h2, h3]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [h4]
    ring
  let φ : Lp ℂ 2 (volume : Measure ℂ) →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℂ) :=
    { toFun := mulLp, map_add' := hadd, map_smul' := hsmul }
  have hnorm : ∀ f : Lp ℂ 2 (volume : Measure ℂ), ‖φ f‖ ≤ 1 * ‖f‖ := by
    intro f
    rw [one_mul]
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [hmulLp f, hm1] with ξ h1 h2
    change ‖⇑(mulLp f) ξ‖ ≤ ‖⇑f ξ‖
    rw [h1, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) h2
  refine ⟨LinearMap.mkContinuous φ 1 hnorm, ?_, ?_⟩
  · exact LinearMap.mkContinuous_norm_le φ zero_le_one hnorm
  · intro f
    exact hmulLp f

end Work.MRMT.Beurling
