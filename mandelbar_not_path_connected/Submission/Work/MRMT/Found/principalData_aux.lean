/-
Work.MRMT.Found — auxiliary lemmas for the `PrincipalData` construction.

These are the small glue lemmas used by `Work.MRMT.Found.principalData_exists`:
the everywhere Cauchy–Green representation, uniqueness of weak `∂`-derivatives, and the identity
`∂F - 1 = S (∂̄F)` for the `C¹` solutions.  They are stated here (in a module that does not import
`Work.MRMT.QC.principal_unique`) so that modules needing them can avoid the name collision between
`Work.MRMT.QC.principal_unique` and `Work.MRMT.QC.eq_zero_of_beltrami_of_decay`.
-/
import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.isDzDeriv_cauchyTransform_eq_beurlingL2
import Submission.Work.MRMT.Found.sub_id_ae_eq_cauchyTransform_dzbar
import Submission.Work.MRMT.Found.continuous_cauchyTransform_of_memLp
import Submission.Work.MRMT.Weyl.Defs
import Submission.Work.MRMT.Found.hsolA_spec
import Submission.Work.MRMT.Found.cauchyTransform_memLp_ball
import Submission.Work.MRMT.Found.exists_tendstoLocallyUniformly_of_l2_of_modulus
import Submission.Work.MRMT.Found.fw_admissible_of_tendsto_ae
import Submission.Work.MRMT.Found.fw_memLp_dzbar
import Submission.Work.MRMT.Found.fw_ae_eq_hsolA_of_ae_eq_mul_one_add
import Submission.Work.MRMT.Found.fw_hsolA_tendsto
import Submission.Work.MRMT.Found.fw_decay_cauchyTransform_le
import Submission.Work.MRMT.Found.fw_integral_normSq_cauchyTransform_le
import Submission.Work.MRMT.Found.fw_volume_image_ball_le
import Submission.Work.MRMT.Found.fw_exists_uniform_modulus
import Submission.Work.MRMT.Cauchy.integrable_cauchyKernel_of_memLp
import Submission.Work.MRMT.Beltrami.cauchyTransform_dz_memLp

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Filter Topology Complex Function
open scoped Distributions Topology ENNReal

namespace Work.MRMT.Found

open Work.MRMT

/-- Two continuous functions agreeing a.e. are equal. -/
theorem eq_of_ae_eq_of_continuous_pd {f g : ℂ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (h : f =ᵐ[volume] g) : f = g := by
  by_contra hne
  obtain ⟨z, hz⟩ : ∃ z, f z ≠ g z := by
    by_contra h
    exact hne (funext fun z => not_not.mp (not_exists.mp h z))
  have hzero : (volume : Measure ℂ) {z : ℂ | f z ≠ g z} = 0 := by
    have h' := h
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff] at h'
    exact h'
  have hopen : IsOpen {z : ℂ | f z ≠ g z} := (isClosed_eq hf hg).isOpen_compl
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hz)
  have hpos : 0 < (volume : Measure ℂ) {z : ℂ | f z ≠ g z} :=
    lt_of_lt_of_le (Metric.measure_ball_pos (volume : Measure ℂ) z hε) (measure_mono hball)
  rw [hzero] at hpos
  exact lt_irrefl 0 hpos

/-- A continuous compactly supported function lies in `L³`. -/
theorem memLp_three_of_continuous_hasCompactSupport_pd {g : ℂ → ℂ} (hc : Continuous g)
    (hs : HasCompactSupport g) : MemLp g 3 (volume : Measure ℂ) := by
  have hcs3 : HasCompactSupport (fun z : ℂ => ‖g z‖ ^ 3) :=
    hs.comp_left (g := fun w : ℂ => ‖w‖ ^ 3) (by simp)
  have hcont3 : Continuous (fun z : ℂ => ‖g z‖ ^ 3) := hc.norm.pow 3
  rw [← MeasureTheory.integrable_norm_rpow_iff hc.aestronglyMeasurable
    (by norm_num : (3 : ENNReal) ≠ 0) (by norm_num : (3 : ENNReal) ≠ ∞)]
  norm_num
  exact hcont3.integrable_of_hasCompactSupport hcs3

/-- The Cauchy transform of a continuous compactly supported function is continuous. -/
theorem continuous_cauchyTransform_pd {g : ℂ → ℂ} (hc : Continuous g)
    (hs : HasCompactSupport g) : Continuous (cauchyTransform g) :=
  continuous_cauchyTransform_of_memLp (p := 3) (by norm_num)
    (memLp_three_of_continuous_hasCompactSupport_pd hc hs) hs

/-- The Cauchy–Green representation, everywhere. -/
theorem sub_id_eq_cauchyTransform_dzbar_pd (F : ℂ → ℂ) (hF : ContDiff ℝ 1 F)
    (hs : HasCompactSupport (fun z => dzbar F z))
    (hdec : ∃ C R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖F z - z‖ ≤ C / ‖z‖) :
    ∀ z : ℂ, F z - z = cauchyTransform (fun w => dzbar F w) z := by
  have hae := sub_id_ae_eq_cauchyTransform_dzbar hF hs hdec
  have hfun : (fun z => F z - z) = cauchyTransform (fun w => dzbar F w) :=
    eq_of_ae_eq_of_continuous_pd (hF.continuous.sub continuous_id)
      (continuous_cauchyTransform_pd (Weyl.continuous_dzbar_of_contDiff hF (by norm_num)) hs) hae
  exact congrFun hfun

/-- The weak `∂`-derivative is unique a.e. -/
theorem is_dz_deriv_unique_pd {f g g' : ℂ → ℂ} (h : IsDzDeriv f g) (h' : IsDzDeriv f g') :
    ∀ᵐ z ∂(volume : Measure ℂ), g z = g' z := by
  refine ae_eq_of_integral_contDiff_smul_eq h.2.1 h'.2.1 ?_
  intro ψ hψ hψc
  let φ : 𝓓(⊤, ℂ) :=
    ⟨fun z => Complex.ofReal (ψ z),
      (ContinuousLinearMap.contDiff (Complex.ofRealCLM)).comp hψ,
      hψc.mono (fun z hz => by
        rw [Function.mem_support] at hz ⊢
        exact fun h => hz (by rw [h]; simp)),
      by intro z _; trivial⟩
  have hφ : ∀ z, (φ : ℂ → ℂ) z = Complex.ofReal (ψ z) := fun _ => rfl
  have key : ∫ z, g z * (φ : ℂ → ℂ) z = ∫ z, g' z * (φ : ℂ → ℂ) z := by
    have h1 : ∫ z, f z * dz (φ : ℂ → ℂ) z = - ∫ z, g z * (φ : ℂ → ℂ) z := (h.2.2 φ).2.2
    have h2 : ∫ z, f z * dz (φ : ℂ → ℂ) z = - ∫ z, g' z * (φ : ℂ → ℂ) z := (h'.2.2 φ).2.2
    have h3 : - ∫ z, g z * (φ : ℂ → ℂ) z = - ∫ z, g' z * (φ : ℂ → ℂ) z := h1.symm.trans h2
    simpa using h3
  have hfun : ∀ z, ψ z • g z = g z * (φ : ℂ → ℂ) z := by
    intro z
    rw [hφ z, RCLike.real_smul_eq_coe_mul]
    exact mul_comm _ _
  have hfun' : ∀ z, ψ z • g' z = g' z * (φ : ℂ → ℂ) z := by
    intro z
    rw [hφ z, RCLike.real_smul_eq_coe_mul]
    exact mul_comm _ _
  calc ∫ z, ψ z • g z = ∫ z, g z * (φ : ℂ → ℂ) z :=
        integral_congr_ae (Eventually.of_forall hfun)
    _ = ∫ z, g' z * (φ : ℂ → ℂ) z := key
    _ = ∫ z, ψ z • g' z := (integral_congr_ae (Eventually.of_forall hfun')).symm

/-- Closure of `IsDzDeriv` under subtraction. -/
theorem IsDzDeriv.sub_pd {f f' g g' : ℂ → ℂ} (h : IsDzDeriv f g) (h' : IsDzDeriv f' g') :
    IsDzDeriv (f - f') (g - g') := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  refine ⟨h1.sub h1', h2.sub h2', fun φ => ?_⟩
  obtain ⟨ha, hb, hc⟩ := h3 φ
  obtain ⟨ha', hb', hc'⟩ := h3' φ
  have e1 : (fun z => (f - f') z * dz (φ : ℂ → ℂ) z)
      = fun z => f z * dz (φ : ℂ → ℂ) z - f' z * dz (φ : ℂ → ℂ) z := by
    funext z; simp only [Pi.sub_apply]; ring
  have e2 : (fun z => (g - g') z * (φ : ℂ → ℂ) z)
      = fun z => g z * (φ : ℂ → ℂ) z - g' z * (φ : ℂ → ℂ) z := by
    funext z; simp only [Pi.sub_apply]; ring
  refine ⟨by rw [e1]; exact ha.sub ha', by rw [e2]; exact hb.sub hb', ?_⟩
  rw [e1, e2, integral_sub ha ha', integral_sub hb hb', hc, hc']
  ring

/-- The weak `∂`-derivatives of a function differing from the identity by a map with compactly
supported `∂̄` and decay. -/
theorem IsDzDeriv.sub_id_pd {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) :
    IsDzDeriv (fun z => F z - z) (fun z => dz F z - 1) := by
  have hid : IsDzDeriv (fun z : ℂ => z) (fun _ => (1 : ℂ)) := by
    have hh : IsDzDeriv (fun z : ℂ => z) (dz (fun z : ℂ => z)) :=
      Work.MRMT.Weyl.isDzDeriv_dz contDiff_id (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
    have hdz : (dz (fun z : ℂ => z)) = (fun _ => (1 : ℂ)) := funext fun z => dz_id z
    rwa [hdz] at hh
  have hF' : IsDzDeriv (fun z : ℂ => F z) (fun z => dz F z) :=
    Work.MRMT.Weyl.isDzDeriv_dz hF (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hsub := IsDzDeriv.sub_pd hF' hid
  have e1 : (fun z : ℂ => F z) - (fun z : ℂ => z) = (fun z : ℂ => F z - z) := rfl
  have e2 : (fun z : ℂ => dz F z) - (fun _ => (1 : ℂ)) = (fun z : ℂ => dz F z - 1) := rfl
  rwa [e1, e2] at hsub

/-- Changing the first argument of a weak `∂`-derivative on a null set. -/
theorem IsDzDeriv.congr_lhs_pd {f f' g : ℂ → ℂ} (h : IsDzDeriv f g) (hff' : f =ᵐ[volume] f')
    (hli : LocallyIntegrable f' volume) : IsDzDeriv f' g := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨hli, h2, fun φ => ?_⟩
  obtain ⟨ha, hb, hc⟩ := h3 φ
  have hae : (fun z => f z * dz (φ : ℂ → ℂ) z) =ᵐ[volume] (fun z => f' z * dz (φ : ℂ → ℂ) z) :=
    hff'.mul (EventuallyEq.refl (ae (volume : Measure ℂ)) (fun z => dz (φ : ℂ → ℂ) z))
  exact ⟨ha.congr hae, hb, by rw [← hc]; exact integral_congr_ae hae.symm⟩

/-- **`∂F - 1 = S (∂̄F)`**: the Wirtinger derivative of a quasiconformal solution is
`1` plus the Beurling transform of `∂̄F`, almost everywhere. -/
theorem dz_sub_one_eq_beurlingL2_pd {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F)
    (hdec : ∃ C R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖F z - z‖ ≤ C / ‖z‖)
    (hs : HasCompactSupport (fun z => dzbar F z))
    (hLp : MemLp (fun z => dzbar F z) 2 (volume : Measure ℂ)) :
    (fun z => dz F z - 1) =ᵐ[volume]
      (((beurlingL2 (hLp.toLp (fun z => dzbar F z)) :
        Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ)) := by
  have h1 : IsDzDeriv (fun z => F z - z) (fun z => dz F z - 1) := IsDzDeriv.sub_id_pd hF
  have h2 : IsDzDeriv (fun z => F z - z)
      (((beurlingL2 (hLp.toLp (fun z => dzbar F z)) : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ)) := by
    have haeeq : cauchyTransform (fun w => dzbar F w) =ᵐ[volume] (fun z => F z - z) :=
      Eventually.of_forall (fun z => (sub_id_eq_cauchyTransform_dzbar_pd F hF hs hdec z).symm)
    have hS := isDzDeriv_cauchyTransform_eq_beurlingL2 hLp hs
    exact IsDzDeriv.congr_lhs_pd hS haeeq (hF.continuous.sub continuous_id).locallyIntegrable
  exact is_dz_deriv_unique_pd h1 h2

end Work.MRMT.Found
