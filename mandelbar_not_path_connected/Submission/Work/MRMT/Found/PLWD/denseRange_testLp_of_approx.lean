import Mathlib
import Submission.Work.MRMT.Found.PLWD.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found.PLWD

open MeasureTheory Filter Topology Complex Function
open scoped Topology ENNReal

/-- Given a nonzero extended nonnegative real `ε`, there is a positive real `δ` whose `ofReal`
is at most `ε`. -/
theorem exists_pos_ofReal_le {ε : ENNReal} (hε : ε ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ≤ ε := by
  rcases eq_or_ne ε ⊤ with h | h
  · exact ⟨1, one_pos, by rw [h]; exact le_top⟩
  · refine ⟨ε.toReal / 2, by have := ENNReal.toReal_pos hε h; linarith, ?_⟩
    calc ENNReal.ofReal (ε.toReal / 2) ≤ ENNReal.ofReal ε.toReal :=
          ENNReal.ofReal_le_ofReal (by linarith [ENNReal.toReal_nonneg (a := ε)])
      _ = ε := ENNReal.ofReal_toReal h

theorem denseRange_testLp_of_approx {R : ℝ} (hR : 0 < R)
    (happrox : ∀ {s : Set ℂ}, MeasurableSet s → s ⊆ Metric.ball 0 R →
      (MeasureTheory.volume : MeasureTheory.Measure ℂ) s < ⊤ → ∀ c : ℂ, ∀ ε : ℝ, 0 < ε →
      ∃ ψ : Work.MRMT.Found.testSpace R,
        MeasureTheory.eLpNorm (fun z => (ψ : ℂ → ℂ) z - s.indicator (fun _ => c) z) 2
          (MeasureTheory.volume : MeasureTheory.Measure ℂ) ≤ ENNReal.ofReal ε) :
    DenseRange (Work.MRMT.Found.testLp R) := by
  set μ : Measure ℂ := (volume : Measure ℂ).restrict (Metric.ball 0 R) with hμdef
  let P : (ℂ → ℂ) → Prop := fun g => ∃ ψ : Work.MRMT.Found.testSpace R, g =ᵐ[μ] (ψ : ℂ → ℂ)
  have h0P : ∀ (c : ℂ) ⦃s : Set ℂ⦄, MeasurableSet s → μ s < ⊤ →
      ∀ {ε : ENNReal}, ε ≠ 0 →
      ∃ g, eLpNorm (g - s.indicator fun _ => c) 2 μ ≤ ε ∧ P g := by
    intro c s hs hμs ε hε
    obtain ⟨ε', hε'pos, hε'le⟩ := exists_pos_ofReal_le hε
    set s' : Set ℂ := s ∩ Metric.ball 0 R with hs'def
    have hs'm : MeasurableSet s' := hs.inter measurableSet_ball
    have hs'R : s' ⊆ Metric.ball 0 R := Set.inter_subset_right
    have hvol_eq : μ s = (volume : Measure ℂ) s' := by
      rw [hs'def, hμdef, Measure.restrict_apply hs]
    have hvol' : (volume : Measure ℂ) s' < ⊤ := by rw [← hvol_eq]; exact hμs
    obtain ⟨ψ, hψ⟩ := happrox hs'm hs'R hvol' c ε' hε'pos
    have hcompl : μ (Metric.ball 0 R)ᶜ = 0 := by
      rw [hμdef, Measure.restrict_apply measurableSet_ball.compl]
      simp
    have hball_ae : ∀ᵐ z ∂μ, z ∈ Metric.ball 0 R := MeasureTheory.mem_ae_iff.mpr hcompl
    have hs_eq : s.indicator (fun _ => c) =ᵐ[μ] s'.indicator (fun _ => c) := by
      filter_upwards [hball_ae] with z hz
      by_cases hzs : z ∈ s
      · rw [Set.indicator_of_mem hzs, Set.indicator_of_mem (show z ∈ s' from ⟨hzs, hz⟩)]
      · rw [Set.indicator_of_notMem hzs,
            Set.indicator_of_notMem (show z ∉ s' from fun h => hzs h.1)]
    have hsupp : Function.support
        (fun z => (ψ : ℂ → ℂ) z - s'.indicator (fun _ => c) z) ⊆ Metric.ball 0 R := by
      intro z hz
      by_contra hzb
      apply hz
      show (ψ : ℂ → ℂ) z - s'.indicator (fun _ => c) z = 0
      have hψz : (ψ : ℂ → ℂ) z = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hmem => hzb (ψ.2.2.2 hmem))
      have hs'z : s'.indicator (fun _ => c) z = 0 :=
        Set.indicator_of_notMem (fun hmem => hzb (hs'R hmem)) _
      rw [hψz, hs'z, sub_zero]
    have hasm : AEStronglyMeasurable
        (fun z => (ψ : ℂ → ℂ) z - s'.indicator (fun _ => c) z) (volume : Measure ℂ) :=
      (ψ.2.1.continuous.aestronglyMeasurable).sub
        ((measurable_const.indicator hs'm).aestronglyMeasurable)
    refine ⟨(ψ : ℂ → ℂ), ?_, ψ, Filter.EventuallyEq.refl _ _⟩
    calc eLpNorm (fun z => (ψ : ℂ → ℂ) z - s.indicator (fun _ => c) z) 2 μ
        = eLpNorm (fun z => (ψ : ℂ → ℂ) z - s'.indicator (fun _ => c) z) 2 μ := by
          apply MeasureTheory.eLpNorm_congr_ae
          filter_upwards [hs_eq] with z hz
          rw [hz]
      _ = eLpNorm (fun z => (ψ : ℂ → ℂ) z - s'.indicator (fun _ => c) z) 2
            (volume : Measure ℂ) := by
          rw [hμdef]
          exact MeasureTheory.eLpNorm_restrict_eq_of_support_subset hasm hsupp
      _ ≤ ENNReal.ofReal ε' := hψ
      _ ≤ ε := hε'le
  have h1P : ∀ f g : ℂ → ℂ, P f → P g → P (f + g) := by
    rintro f g ⟨ψf, hf⟩ ⟨ψg, hg⟩
    refine ⟨ψf + ψg, ?_⟩
    filter_upwards [hf, hg] with z hzf hzg
    simp only [Pi.add_apply, Submodule.coe_add]
    rw [hzf, hzg]
  intro ℓ
  rw [Metric.mem_closure_iff]
  intro δ hδ
  obtain ⟨g, hg_bound, hPg⟩ := MeasureTheory.MemLp.induction_dense (μ := μ) (p := 2)
    (by norm_num) P h0P h1P (MeasureTheory.Lp.memLp ℓ) (ε := ENNReal.ofReal (δ / 2))
    (by rw [ENNReal.ofReal_ne_zero_iff]; linarith)
  obtain ⟨ψ, hgψ⟩ := hPg
  refine ⟨Work.MRMT.Found.testLp R ψ, ⟨ψ, rfl⟩, ?_⟩
  have htest : ⇑(Work.MRMT.Found.testLp R ψ) =ᵐ[μ] (ψ : ℂ → ℂ) := by
    rw [Work.MRMT.Found.testLp_apply]
    exact MeasureTheory.MemLp.coeFn_toLp _
  have hdiff : (⇑ℓ - ⇑(Work.MRMT.Found.testLp R ψ)) =ᵐ[μ] (⇑ℓ - g) := by
    filter_upwards [htest, hgψ] with z h1 h2
    rw [Pi.sub_apply, Pi.sub_apply, h1, h2]
  have hE : eLpNorm (⇑ℓ - ⇑(Work.MRMT.Found.testLp R ψ)) 2 μ = eLpNorm (⇑ℓ - g) 2 μ :=
    MeasureTheory.eLpNorm_congr_ae hdiff
  rw [MeasureTheory.Lp.dist_def, hE]
  calc (eLpNorm (⇑ℓ - g) 2 μ).toReal
      ≤ (ENNReal.ofReal (δ / 2)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hg_bound
    _ = δ / 2 := ENNReal.toReal_ofReal (by linarith)
    _ < δ := by linarith

end Work.MRMT.Found.PLWD
