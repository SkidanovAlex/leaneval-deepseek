import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.hsolA_spec

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Filter Topology Complex Function
open scoped Distributions Topology ENNReal

namespace Work.MRMT.Found

/-- The multiplication operator `mulL2 μ hm h1` maps `L²` into `L²` with constant `k` when
`‖μ‖ ≤ k` a.e. -/
private lemma mulL2_norm_le_mul {μ : ℂ → ℂ} (hm : AEStronglyMeasurable μ (volume : Measure ℂ))
    (h1 : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ 1) {k : ℝ}
    (hb : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k) (w : Lp ℂ 2 (volume : Measure ℂ)) :
    ‖mulL2 μ hm h1 w‖ ≤ k * ‖w‖ := by
  refine Lp.norm_le_mul_norm_of_ae_le_mul (c := k) ?_
  filter_upwards [mulL2_apply_ae μ hm h1 w, hb] with z hz hkz
  rw [hz, norm_mul]
  exact mul_le_mul_of_nonneg_right hkz (norm_nonneg _)

theorem fw_ae_eq_hsolA_of_ae_eq_mul_one_add {μ ω : ℂ → ℂ} {k : ℝ} (hk1 : k < 1)
    (hAdm : Work.MRMT.Found.Admissible μ)
    (hLpμ : MeasureTheory.MemLp μ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (hω : MeasureTheory.MemLp ω 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (hμb : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖μ z‖ ≤ k)
    (heq : ω =ᵐ[MeasureTheory.volume] fun z =>
      μ z * (1 + ((Work.MRMT.beurlingL2 (hω.toLp ω) :
        MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : ℂ → ℂ) z)) :
    ω =ᵐ[MeasureTheory.volume]
      ((Work.MRMT.Found.hsolA μ hAdm hLpμ :
        MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : ℂ → ℂ) := by
  have hm : AEStronglyMeasurable μ (volume : Measure ℂ) := hAdm.meas
  have h1 : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ 1 := by
    filter_upwards [hμb] with z hz
    linarith [norm_nonneg (μ z)]
  -- the Ahlfors--Bers equation solved by `hsolA`
  obtain ⟨hspec, -, -⟩ := hsolA_spec hAdm hLpμ hk1 hμb
  -- `hsolA` is the unique `L²` solution: compare it with `ω`.
  have key : hω.toLp ω = hsolA μ hAdm hLpμ := by
    set g : Lp ℂ 2 (volume : Measure ℂ) := hω.toLp ω with hg
    set hH : Lp ℂ 2 (volume : Measure ℂ) := hsolA μ hAdm hLpμ with hh
    have hgω : (g : ℂ → ℂ) =ᵐ[volume] ω := by rw [hg]; exact MemLp.coeFn_toLp hω
    have hheq : (hH : ℂ → ℂ) =ᵐ[volume]
        fun z => μ z * (1 + ((beurlingL2 hH : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) z) := by
      rw [hh]; exact hspec
    have hgeq : ω =ᵐ[volume]
        fun z => μ z * (1 + ((beurlingL2 g : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) z) := by
      rw [hg]; exact heq
    -- `e := g - hH` satisfies `e = M_μ (S e)` a.e.
    have hee : g - hH = mulL2 μ hm h1 (beurlingL2 (g - hH)) := by
      apply Lp.ext_iff.mpr
      have hSsub : ((beurlingL2 (g - hH) : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ)
          =ᵐ[volume] fun z => ((beurlingL2 g : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) z
            - ((beurlingL2 hH : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) z := by
        have h1' : (beurlingL2 (g - hH) : Lp ℂ 2 (volume : Measure ℂ))
            = beurlingL2 g - beurlingL2 hH := map_sub beurlingL2 g hH
        rw [h1']
        exact Lp.coeFn_sub (beurlingL2 g) (beurlingL2 hH)
      filter_upwards [Lp.coeFn_sub g hH, hgω, hgeq, hheq, hSsub,
        mulL2_apply_ae μ hm h1 (beurlingL2 (g - hH))] with z hzsub hzg hzg2 hzh hzs hmul
      rw [hzsub, Pi.sub_apply, hzg, hzg2, hzh, hmul, hzs]
      ring
    -- and hence `‖e‖ ≤ k ‖e‖` with `k < 1`, so `e = 0`.
    have hbound : ‖g - hH‖ ≤ k * ‖g - hH‖ := by
      calc ‖g - hH‖ = ‖mulL2 μ hm h1 (beurlingL2 (g - hH))‖ := congrArg norm hee
        _ ≤ k * ‖beurlingL2 (g - hH)‖ := mulL2_norm_le_mul hm h1 hμb _
        _ = k * ‖g - hH‖ := by rw [norm_beurlingL2]
    have hkpos : 0 < 1 - k := by linarith
    have hz : ‖g - hH‖ = 0 := by
      have h2 : (1 - k) * ‖g - hH‖ ≤ 0 := by
        have h3 : (1 - k) * ‖g - hH‖ = ‖g - hH‖ - k * ‖g - hH‖ := by ring
        rw [h3]; linarith [hbound]
      have h4 : (1 - k) * ‖g - hH‖ = 0 :=
        le_antisymm h2 (mul_nonneg hkpos.le (norm_nonneg _))
      rcases mul_eq_zero.mp h4 with h5 | h5
      · linarith
      · exact h5
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  have hcoe : ((hω.toLp ω : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ)
      =ᵐ[volume] ((hsolA μ hAdm hLpμ : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) := by
    rw [key]
  exact (MemLp.coeFn_toLp hω).symm.trans hcoe

end Work.MRMT.Found
