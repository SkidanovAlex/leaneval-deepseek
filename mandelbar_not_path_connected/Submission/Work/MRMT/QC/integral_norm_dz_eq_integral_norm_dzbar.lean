import Mathlib
import Submission.Work.MRMT.Basic
import Submission.Work.MRMT.Weyl.Defs
import Submission.Work.MRMT.Weyl.isDzDeriv_moll_gen
import Submission.Work.MRMT.Weyl.isDbarDeriv_moll_gen
import Submission.Work.MRMT.Sobolev.dzbar_convolution_eq_of_isDbarDerivOn
import Submission.Work.MRMT.Beltrami.energy_identity
import Submission.Work.MRMT.QC.lintegral_ofReal_norm_sq_moll_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.QC

open MeasureTheory Complex Function Filter
open scoped Distributions Topology ENNReal Convolution

noncomputable section

set_option maxHeartbeats 1000000

/-- The `n`-th normalised bump kernel used for mollification. -/
def bumpKer (n : ℕ) : ℂ → ℝ :=
  (Work.MRMT.Weyl.bump n).normed (MeasureTheory.volume : MeasureTheory.Measure ℂ)

theorem bumpKer_nonneg (n : ℕ) (x : ℂ) : 0 ≤ bumpKer n x :=
  (Work.MRMT.Weyl.bump n).nonneg_normed x

theorem bumpKer_integral (n : ℕ) : ∫ x, bumpKer n x = 1 :=
  (Work.MRMT.Weyl.bump n).integral_normed

theorem bumpKer_aemeas (n : ℕ) : AEStronglyMeasurable (bumpKer n) (volume : Measure ℂ) :=
  ((Work.MRMT.Weyl.bump n).continuous_normed).aestronglyMeasurable

theorem bumpKer_contDiff (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (bumpKer n) :=
  (Work.MRMT.Weyl.bump n).contDiff_normed

theorem bumpKer_hasCompactSupport (n : ℕ) : HasCompactSupport (bumpKer n) :=
  (Work.MRMT.Weyl.bump n).hasCompactSupport_normed

theorem moll_memL2 {f : ℂ → ℂ} (hf : AEStronglyMeasurable f (volume : Measure ℂ)) (n : ℕ) :
    AEStronglyMeasurable (Work.MRMT.Weyl.moll (bumpKer n) f) (volume : Measure ℂ) := by
  have h := AEStronglyMeasurable.convolution (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (μ := (volume : Measure ℂ)) (bumpKer_aemeas n) hf
  simpa only [Work.MRMT.Weyl.moll] using h

/-- Almost everywhere convergence of the bump-mollifications to the function itself. -/
theorem ae_tendsto_moll_bumpKer {f : ℂ → ℂ} (hf : LocallyIntegrable f (volume : Measure ℂ)) :
    ∀ᵐ x ∂(volume : Measure ℂ),
      Tendsto (fun n => Work.MRMT.Weyl.moll (bumpKer n) f x) atTop (𝓝 (f x)) := by
  have hratio : ∀ᶠ n : ℕ in atTop,
      (Work.MRMT.Weyl.bump n).rOut ≤ 2 * (Work.MRMT.Weyl.bump n).rIn := by
    filter_upwards with n
    have h1 : (Work.MRMT.Weyl.bump n).rIn = 1 / ((n : ℝ) + 2) := rfl
    have h2 : (Work.MRMT.Weyl.bump n).rOut = 1 / ((n : ℝ) + 1) := rfl
    rw [h1, h2]
    rw [show (2 : ℝ) * (1 / ((n : ℝ) + 2)) = 2 / ((n : ℝ) + 2) by ring]
    rw [← sub_nonneg]
    have key : 2 / ((n : ℝ) + 2) - 1 / ((n : ℝ) + 1)
        = (n : ℝ) / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
      field_simp
      ring
    rw [key]
    positivity
  have h := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (μ := (volume : Measure ℂ)) (φ := Work.MRMT.Weyl.bump) (l := atTop) (K := 2)
    Work.MRMT.Weyl.tendsto_rOut_bump hratio hf
  filter_upwards [h] with x hx
  simpa only [bumpKer, Work.MRMT.Weyl.moll] using hx

/-- The limit of the squared `L²` norms of the bump-mollifications equals `∫ ‖f‖²`. -/
theorem tendsto_integral_norm_sq_moll_aux {f : ℂ → ℂ}
    (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) :
    Filter.Tendsto
      (fun n : ℕ => ∫ z, ‖Work.MRMT.Weyl.moll (bumpKer n) f z‖ ^ 2)
      Filter.atTop (nhds (∫ z, ‖f z‖ ^ 2)) := by
  have hfaesm : AEStronglyMeasurable f (volume : Measure ℂ) := hf.aestronglyMeasurable
  have hfint : Integrable (fun z => ‖f z‖ ^ 2) (volume : Measure ℂ) :=
    (memLp_two_iff_integrable_sq_norm hfaesm).mp hf
  have ha_nonneg : 0 ≤ ∫ z, ‖f z‖ ^ 2 := integral_nonneg (fun z => by positivity)
  let L : ℝ≥0∞ := ∫⁻ z, ENNReal.ofReal (‖f z‖ ^ 2)
  have hL : L = ENNReal.ofReal (∫ z, ‖f z‖ ^ 2) := by
    simp only [L]
    exact (ofReal_integral_eq_lintegral_ofReal hfint (Eventually.of_forall (fun z => by positivity))).symm
  have hLne : L ≠ ∞ := by rw [hL]; exact ENNReal.ofReal_ne_top
  let F : ℕ → ℝ≥0∞ := fun n =>
    ∫⁻ z, ENNReal.ofReal (‖Work.MRMT.Weyl.moll (bumpKer n) f z‖ ^ 2)
  have hbound : ∀ n, F n ≤ L := by
    intro n
    simp only [F, L]
    exact lintegral_ofReal_norm_sq_moll_le hfaesm (bumpKer_nonneg n) (bumpKer_integral n)
      (bumpKer_aemeas n)
  have hFne : ∀ n, F n ≠ ∞ := fun n => ne_top_of_le_ne_top hLne (hbound n)
  have hmeas : ∀ n, AEMeasurable
      (fun z => ENNReal.ofReal (‖Work.MRMT.Weyl.moll (bumpKer n) f z‖ ^ 2))
      (volume : Measure ℂ) := by
    intro n
    apply AEMeasurable.ennreal_ofReal
    exact ((continuous_norm.pow 2).comp_aestronglyMeasurable (moll_memL2 hfaesm n)).aemeasurable
  have hfatou := lintegral_liminf_le' (μ := (volume : Measure ℂ)) (u := atTop)
    (f := fun n z => ENNReal.ofReal (‖Work.MRMT.Weyl.moll (bumpKer n) f z‖ ^ 2)) hmeas
  have hlim_eq : ∀ᵐ z ∂(volume : Measure ℂ),
      liminf (fun n => ENNReal.ofReal (‖Work.MRMT.Weyl.moll (bumpKer n) f z‖ ^ 2)) atTop
        = ENNReal.ofReal (‖f z‖ ^ 2) := by
    filter_upwards [ae_tendsto_moll_bumpKer (hf.locallyIntegrable (by norm_num))] with z hz
    have hz' : Tendsto (fun n => ENNReal.ofReal (‖Work.MRMT.Weyl.moll (bumpKer n) f z‖ ^ 2))
        atTop (𝓝 (ENNReal.ofReal (‖f z‖ ^ 2))) :=
      ((ENNReal.continuous_ofReal.comp (continuous_norm.pow 2)).tendsto _).comp hz
    exact hz'.liminf_eq
  have hcongr : ∫⁻ z,
      liminf (fun n => ENNReal.ofReal (‖Work.MRMT.Weyl.moll (bumpKer n) f z‖ ^ 2)) atTop = L := by
    rw [lintegral_congr_ae hlim_eq]
  have hinf : L ≤ liminf F atTop := by
    rw [← hcongr]
    exact hfatou
  have hT : Tendsto F atTop (𝓝 L) := by
    rw [tendsto_order]
    refine ⟨fun b hb => (le_liminf_iff (x := L)).1 hinf b hb, fun b hb => ?_⟩
    exact Eventually.of_forall (fun n => lt_of_le_of_lt (hbound n) hb)
  have hT' := (ENNReal.tendsto_toReal_iff hFne hLne).2 hT
  have hFn : ∀ n, (F n).toReal = ∫ z, ‖Work.MRMT.Weyl.moll (bumpKer n) f z‖ ^ 2 := by
    intro n
    rw [integral_eq_lintegral_of_nonneg_ae (μ := (volume : Measure ℂ))
      (f := fun z => ‖Work.MRMT.Weyl.moll (bumpKer n) f z‖ ^ 2)
      (Eventually.of_forall (fun z => by positivity))
      ((continuous_norm.pow 2).comp_aestronglyMeasurable (moll_memL2 hfaesm n))]
  have hLtr : L.toReal = ∫ z, ‖f z‖ ^ 2 := by
    rw [hL]; exact ENNReal.toReal_ofReal ha_nonneg
  rw [funext hFn, hLtr] at hT'
  exact hT'

/-- Pointwise `∂̄` of the bump-mollification agrees with the mollification of the weak `∂̄`. -/
theorem dzbar_moll_bumpKer {u q : ℂ → ℂ} (hq : Work.MRMT.IsDbarDeriv u q) (n : ℕ) (z : ℂ) :
    Work.MRMT.dzbar (Work.MRMT.Weyl.moll (bumpKer n) u) z
      = Work.MRMT.Weyl.moll (bumpKer n) q z := by
  have hρc : ContDiff ℝ (⊤ : ℕ∞) (fun w => (bumpKer n w : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (bumpKer_contDiff n)
  have hρccs : HasCompactSupport (fun w => (bumpKer n w : ℂ)) :=
    (bumpKer_hasCompactSupport n).comp_left (g := Complex.ofRealCLM) (by simp)
  have hFG : Work.MRMT.IsDbarDerivOn u q Set.univ := by
    obtain ⟨h1, h2, h3⟩ := hq
    exact ⟨MeasureTheory.locallyIntegrableOn_univ.2 h1, MeasureTheory.locallyIntegrableOn_univ.2 h2,
      fun ψ _ => h3 ψ⟩
  have hconv := Work.MRMT.Sobolev.dzbar_convolution_eq_of_isDbarDerivOn (U := Set.univ)
    (F := u) (G := q) (ρ := fun w => (bumpKer n w : ℂ)) hFG hq.1 hρc hρccs (z := z)
    (fun t _ => trivial)
  rwa [Work.MRMT.Weyl.convolution_mul_eq_moll (bumpKer n) u,
       Work.MRMT.Weyl.convolution_mul_eq_moll (bumpKer n) q] at hconv

theorem integral_norm_dz_eq_integral_norm_dzbar {u p q : ℂ → ℂ} (hus : HasCompactSupport u)
    (hp : Work.MRMT.IsDzDeriv u p) (hq : Work.MRMT.IsDbarDeriv u q)
    (hpm : MeasureTheory.MemLp p 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (hqm : MeasureTheory.MemLp q 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) :
    ∫ z, ‖p z‖ ^ 2 = ∫ z, ‖q z‖ ^ 2 := by
  have heq : (fun n : ℕ => ∫ z, ‖Work.MRMT.Weyl.moll (bumpKer n) p z‖ ^ 2)
      = (fun n : ℕ => ∫ z, ‖Work.MRMT.Weyl.moll (bumpKer n) q z‖ ^ 2) := by
    funext n
    have hcd : ContDiff ℝ 2 (Work.MRMT.Weyl.moll (bumpKer n) u) :=
      Work.MRMT.Weyl.contDiff_moll (N := (2 : ℕ∞)) (ρ := bumpKer n) (f := u)
        ((Work.MRMT.Weyl.bump n).contDiff_normed (n := (2 : ℕ∞)))
        (bumpKer_hasCompactSupport n) hq.1
    have hcs : HasCompactSupport (Work.MRMT.Weyl.moll (bumpKer n) u) := by
      have h := HasCompactSupport.convolution (L := ContinuousLinearMap.lsmul ℝ ℝ)
        (μ := (volume : Measure ℂ)) (bumpKer_hasCompactSupport n) hus
      simpa only [Work.MRMT.Weyl.moll] using h
    have hE := Work.MRMT.Beltrami.energy_identity_of_contDiff_two
      (Work.MRMT.Weyl.moll (bumpKer n) u) hcd hcs
    have hdz : Work.MRMT.dz (Work.MRMT.Weyl.moll (bumpKer n) u)
        = Work.MRMT.Weyl.moll (bumpKer n) p :=
      funext (fun z => Work.MRMT.Weyl.moll_aux_dz_eq hp (bumpKer_contDiff n)
        (bumpKer_hasCompactSupport n) z)
    have hdzb : Work.MRMT.dzbar (Work.MRMT.Weyl.moll (bumpKer n) u)
        = Work.MRMT.Weyl.moll (bumpKer n) q :=
      funext (fun z => dzbar_moll_bumpKer hq n z)
    rw [hdz, hdzb] at hE
    simpa using hE
  have hp_lim := tendsto_integral_norm_sq_moll_aux hpm
  have hq_lim := tendsto_integral_norm_sq_moll_aux hqm
  rw [heq] at hp_lim
  exact tendsto_nhds_unique hp_lim hq_lim

end

end Work.MRMT.QC
