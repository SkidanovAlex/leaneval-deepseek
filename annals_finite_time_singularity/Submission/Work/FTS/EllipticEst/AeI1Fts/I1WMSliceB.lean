import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.AngAWeak.Basic
import Submission.Work.FTS.EllipticEst.remov.AeI1PaperDefs
import Submission.Work.FTS.EllipticEst.AeI1Fts.Defs
import Submission.Work.FTS.EllipticEst.AngAWeak.slicePairIneqFluxFree
import Submission.Work.FTS.EllipticEst.H2W.SlotA.sharpHardyOpen
import Submission.Work.FTS.EllipticEst.AeI1Fts.Upsi_A_integrable
import Submission.Work.FTS.EllipticEst.AeI1Fts.Upsi_P_integrable_ae
import Submission.Work.FTS.EllipticEst.AeI1Fts.I1WMSliceA
-- (inherited from the pre-split file: the chunks need the transitive imports of the module
-- `AeI1Fts/I1Paper_mixed` for such names as `contDiffOn_slice_U`)
import Submission.Work.FTS.EllipticEst.AeI1Fts.identity_defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.I1Paper_mixed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-! Split out of `AeI1Fts/I1PaperWeakMixed.lean` (the file was 45 KB, above the project's
per-file build guard): the `θ`-truncated slice bounds.  Names and namespace are unchanged. -/

namespace Work.FTS.EllipticEst.AeI1Fts

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)

/-- **The `κ`-improved slice bound for a `θ`-truncated slice — *no* flux hypothesis.**

For `ψ` whose support is separated from both endpoints (`support ψ ⊆ (a,b)` with
`0 < a < b < π/2`), the truncated slice `v·ψ` satisfies the flux condition of
`slice_second_le_flux` *automatically*: both `(v·ψ) ε` and `(v·ψ) (π/2-ε)` vanish for
`ε < min a (π/2-b)`, and `fluxG` is a multiple of the value of the slice, so the flux difference
is `0`.  Hence the flux obstruction of the `I₁` chain disappears under a `θ`-cutoff, and one is
left with the (routine) integrability of the four truncated integrands — which in practice comes
from the compact support of `ψ` together with the continuity of `v`, `ψ` and the weights on the
support. -/
theorem slice_second_le_cut (v ψ : ℝ → ℝ) (hv : ContDiffOn ℝ 2 v Iθo)
    (hψ : ContDiff ℝ 2 ψ)
    (hsep : ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < Real.pi / 2 ∧ Function.support ψ ⊆ Set.Ioo a b)
    (hD : MeasureTheory.IntegrableOn
      (fun θ => (deriv (v * ψ) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Iθo)
    (hA : MeasureTheory.IntegrableOn
      (fun θ => ((v * ψ) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Iθo)
    (hN : MeasureTheory.IntegrableOn
      (fun θ => ((v * ψ) θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))) Iθo)
    (hG : MeasureTheory.IntegrableOn
      (fun θ => (v * ψ) θ * deriv (deriv (v * ψ)) θ
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Iθo) :
    (∫ θ in Iθo, (v * ψ) θ * deriv (deriv (v * ψ)) θ
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      ≤ 2 * Work.Spaces.eta
          * (∫ θ in Iθo, ((v * ψ) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        - ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta))
          * (∫ θ in Iθo, (deriv (v * ψ) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  obtain ⟨a, b, ha, hab, hb, hsupp⟩ := hsep
  have hδpos : 0 < min a (Real.pi / 2 - b) := lt_min ha (by linarith)
  -- the flux condition of the truncated slice holds for `ε < min a (π/2-b)`
  have hflux : ∃ δ : ℝ, 0 < δ ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) δ,
      Work.FTS.EllipticEst.AngAWeak.fluxG Work.Spaces.eta (v * ψ) (Real.pi / 2 - ε)
        - Work.FTS.EllipticEst.AngAWeak.fluxG Work.Spaces.eta (v * ψ) ε ≤ 0 := by
    refine ⟨min a (Real.pi / 2 - b), hδpos, fun ε hε => ?_⟩
    have hεa : ε < a := lt_of_lt_of_le hε.2 (min_le_left _ _)
    have hεb : ε < Real.pi / 2 - b := lt_of_lt_of_le hε.2 (min_le_right _ _)
    have hleft : (v * ψ) ε = 0 := by
      rw [Pi.mul_apply]
      have hψ0 : ψ ε = 0 := by
        by_contra hne
        have hmem := hsupp (Function.mem_support.mpr hne)
        exact absurd (hmem.1) (not_lt.mpr (le_of_lt hεa))
      rw [hψ0, mul_zero]
    have hright : (v * ψ) (Real.pi / 2 - ε) = 0 := by
      rw [Pi.mul_apply]
      have hψ0 : ψ (Real.pi / 2 - ε) = 0 := by
        by_contra hne
        have hmem := hsupp (Function.mem_support.mpr hne)
        exact absurd (hmem.2) (not_lt.mpr (le_of_lt (by linarith [hεb])))
      rw [hψ0, mul_zero]
    have h1 : Work.FTS.EllipticEst.AngAWeak.fluxG Work.Spaces.eta (v * ψ)
        (Real.pi / 2 - ε) = 0 := by
      simp only [Work.FTS.EllipticEst.AngAWeak.fluxG, hright]
      ring
    have h2 : Work.FTS.EllipticEst.AngAWeak.fluxG Work.Spaces.eta (v * ψ) ε = 0 := by
      simp only [Work.FTS.EllipticEst.AngAWeak.fluxG, hleft]
      ring
    rw [h1, h2]
    norm_num
  exact slice_second_le_flux_small (v * ψ) (hv.mul hψ.contDiffOn) hflux hD hA hN hG

/-- **Integrability on `Iθ` of a function supported in a compact subinterval of `(0,π/2)`.**

If `f` is continuous on `[a,b]` (`0 < a ≤ b < π/2`) and vanishes off `[a,b]`, then `f` is
`IntegrableOn Iθ = [0,π/2]`: the integral sees only `[a,b]`, where `f` is continuous and bounded.
This is the routine input that discharges the four integrability hypotheses of
`slice_second_le_cut` for a `θ`-truncated slice. -/
theorem integrableOn_Iθo_of_compact_support {a b : ℝ} {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Icc a b))
    (hzero : ∀ θ, θ ∉ Set.Icc a b → f θ = 0) :
    MeasureTheory.IntegrableOn f Iθo := by
  have hInd : MeasureTheory.Integrable ((Set.Icc a b).indicator f) MeasureTheory.volume :=
    (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
      (hcont.integrableOn_compact isCompact_Icc)
  have hfun : f =ᵐ[MeasureTheory.volume.restrict Iθo]
      (Set.Icc a b).indicator f := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ _
    by_cases h : θ ∈ Set.Icc a b
    · rw [Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h]
      exact hzero θ h
  exact MeasureTheory.Integrable.congr (hInd.integrableOn (s := Iθo)) hfun.symm

/-- **The integrability transfer** used by the truncated slice bound: if `f` is integrable on
the compact interval `[a,b]` and vanishes off it, then it is `IntegrableOn Iθ`. -/
theorem integrableOn_Iθo_of_integrableOn_Icc {a b : ℝ} {f : ℝ → ℝ}
    (hIcc : MeasureTheory.IntegrableOn f (Set.Icc a b))
    (hzero : ∀ θ, θ ∉ Set.Icc a b → f θ = 0) :
    MeasureTheory.IntegrableOn f Iθo := by
  have hInd : MeasureTheory.Integrable ((Set.Icc a b).indicator f) MeasureTheory.volume :=
    (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr hIcc
  have hfun : f =ᵐ[MeasureTheory.volume.restrict Iθo] (Set.Icc a b).indicator f := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ _
    by_cases h : θ ∈ Set.Icc a b
    · rw [Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h]
      exact hzero θ h
  exact MeasureTheory.Integrable.congr (hInd.integrableOn (s := Iθo)) hfun.symm

/-- **The unconditional `κ`-improved bound for a `θ`-truncated slice.**

For a slice `v` of class `C²` on `(0,π/2)` and a smooth `ψ` whose *closed* support lies strictly
inside `(a,b) ⊂ (0,π/2)`, the truncated slice `v·ψ` satisfies

`∫_θ σ (vψ)(vψ)'' ≤ 2η ∫_θ σ (vψ)² − κ ∫_θ σ ((vψ)')²`,  `κ = (1-η)/(1+η)`,

with **no** flux hypothesis and **no** integrability hypothesis: both are automatic for a
truncated slice (`slice_second_le_cut`, resp. the compact support of `v·ψ` and the continuity of
`v`, `ψ` and their derivatives on `[a,b]`).  This is the input of the truncation route to the
weak-class `I₁` bound. -/
theorem slice_second_le_cut_auto (v ψ : ℝ → ℝ) (hv : ContDiffOn ℝ 2 v Iθo)
    (hψ : ContDiff ℝ 2 ψ)
    (hsep : ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < Real.pi / 2 ∧ tsupport ψ ⊆ Set.Ioo a b) :
    (∫ θ in Iθo, (v * ψ) θ * deriv (deriv (v * ψ)) θ
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      ≤ 2 * Work.Spaces.eta
          * (∫ θ in Iθo, ((v * ψ) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        - ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta))
          * (∫ θ in Iθo, (deriv (v * ψ) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  obtain ⟨a, b, ha, hab, hb, hsupp⟩ := hsep
  have hsub : Set.Icc a b ⊆ Iθo := fun θ hθ =>
    ⟨by linarith [hθ.1, ha], by linarith [hθ.2, hb]⟩
  have hsupp' : Function.support ψ ⊆ Set.Ioo a b := fun θ hθ =>
    hsupp (subset_tsupport ψ hθ)
  have hvan : ∀ θ, θ ∉ Set.Icc a b → ψ θ = 0 := fun θ hθ =>
    image_eq_zero_of_notMem_tsupport
      (fun hmem => hθ ⟨le_of_lt (hsupp hmem).1, le_of_lt (hsupp hmem).2⟩)
  -- continuity of the weights on `[a,b]`
  have hsin_pos : ∀ θ ∈ Set.Icc a b, Real.sin (2 * θ) ≠ 0 := fun θ hθ =>
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, ha])
      (by linarith [hθ.2, hb, Real.pi_pos]))
  have hcontσ : ContinuousOn (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (Set.Icc a b) :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
      (fun θ hθ => Or.inl (hsin_pos θ hθ))
  have hcontσ₂ : ContinuousOn (fun θ => (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)))
      (Set.Icc a b) :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
      (fun θ hθ => Or.inl (hsin_pos θ hθ))
  have hcontcos : ContinuousOn (fun θ => (Real.cos (2 * θ)) ^ 2) (Set.Icc a b) :=
    ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn).pow 2
  -- continuity of the slice and of its first two derivatives on `[a,b]`
  have hvC : ContinuousOn v (Set.Icc a b) := hv.continuousOn.mono hsub
  have hgC : ContinuousOn (v * ψ) (Set.Icc a b) := hvC.mul hψ.continuous.continuousOn
  have hg2 : ContDiffOn ℝ 2 (v * ψ) Iθo := hv.mul hψ.contDiffOn
  have huniq : UniqueDiffOn ℝ Iθo := isOpen_Ioo.uniqueDiffOn
  have hcd1 : ContinuousOn (fun θ => deriv (v * ψ) θ) (Set.Icc a b) := by
    have h1 : ContinuousOn (iteratedDerivWithin 1 (v * ψ) Iθo) Iθo :=
      hg2.continuousOn_iteratedDerivWithin (m := 1) (by norm_num) huniq
    refine (h1.mono hsub).congr (fun θ hθ => ?_)
    rw [iteratedDerivWithin_eq_iteratedDeriv huniq
        ((hg2.contDiffAt (isOpen_Ioo.mem_nhds (hsub hθ))).of_le (by norm_num)) (hsub hθ),
      iteratedDeriv_one]
  have hcd2 : ContinuousOn (fun θ => deriv (deriv (v * ψ)) θ) (Set.Icc a b) := by
    have h2 : ContinuousOn (iteratedDerivWithin 2 (v * ψ) Iθo) Iθo :=
      hg2.continuousOn_iteratedDerivWithin (m := 2) (by norm_num) huniq
    refine (h2.mono hsub).congr (fun θ hθ => ?_)
    rw [iteratedDerivWithin_eq_iteratedDeriv huniq
        ((hg2.contDiffAt (isOpen_Ioo.mem_nhds (hsub hθ))).of_le (by norm_num)) (hsub hθ),
      show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hvan_deriv : ∀ θ, θ ∉ Set.Icc a b → deriv (v * ψ) θ = 0 := by
    intro θ hθ
    have hmem : θ ∉ tsupport ψ :=
      fun hmem => hθ ⟨le_of_lt (hsupp hmem).1, le_of_lt (hsupp hmem).2⟩
    have hnb : ∀ᶠ τ in 𝓝 θ, ψ τ = 0 := by
      filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds hmem] with τ hτ
      exact image_eq_zero_of_notMem_tsupport hτ
    have heq : (v * ψ) =ᶠ[𝓝 θ] (fun _ => (0 : ℝ)) := by
      filter_upwards [hnb] with τ hτ
      rw [Pi.mul_apply, hτ, mul_zero]
    rw [Filter.EventuallyEq.deriv_eq heq, deriv_const]
  -- the four integrability hypotheses
  have hA : MeasureTheory.IntegrableOn
      (fun θ => ((v * ψ) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Iθo := by
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn ((hgC.pow 2).mul hcontσ)
    refine integrableOn_Iθo_of_integrableOn_Icc (MeasureTheory.IntegrableOn.of_bound
      measure_Icc_lt_top (((hgC.pow 2).mul hcontσ).aestronglyMeasurable measurableSet_Icc) M ?_)
      (fun θ hθ => by rw [Pi.mul_apply, hvan θ hθ, mul_zero]; ring)
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hM
  have hN : MeasureTheory.IntegrableOn
      (fun θ => ((v * ψ) θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))) Iθo := by
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (((hgC.pow 2).mul hcontcos).mul hcontσ₂)
    refine integrableOn_Iθo_of_integrableOn_Icc (MeasureTheory.IntegrableOn.of_bound
      measure_Icc_lt_top
      ((((hgC.pow 2).mul hcontcos).mul hcontσ₂).aestronglyMeasurable measurableSet_Icc) M ?_)
      (fun θ hθ => by rw [Pi.mul_apply, hvan θ hθ, mul_zero]; ring)
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hM
  have hD : MeasureTheory.IntegrableOn
      (fun θ => (deriv (v * ψ) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Iθo := by
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn ((hcd1.pow 2).mul hcontσ)
    refine integrableOn_Iθo_of_integrableOn_Icc (MeasureTheory.IntegrableOn.of_bound
      measure_Icc_lt_top (((hcd1.pow 2).mul hcontσ).aestronglyMeasurable measurableSet_Icc) M ?_)
      (fun θ hθ => by rw [hvan_deriv θ hθ]; ring)
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hM
  have hG : MeasureTheory.IntegrableOn
      (fun θ => (v * ψ) θ * deriv (deriv (v * ψ)) θ
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Iθo := by
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
      ((hgC.mul hcd2).mul hcontσ)
    refine integrableOn_Iθo_of_integrableOn_Icc (MeasureTheory.IntegrableOn.of_bound
      measure_Icc_lt_top
      (((hgC.mul hcd2).mul hcontσ).aestronglyMeasurable measurableSet_Icc) M ?_)
      (fun θ hθ => by simp only [Pi.mul_apply, hvan θ hθ, mul_zero, zero_mul])
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hM
  exact slice_second_le_cut v ψ hv hψ ⟨a, b, ha, hab, hb, hsupp'⟩ hD hA hN hG


end

end Work.FTS.EllipticEst.AeI1Fts
