import Mathlib
import Submission.Lib.Unif2.Helpers
import Submission.Lib.Unif2.PackagingOpen
import Submission.Lib.Unif2.Work.SimplyConnected.Plane
import Submission.Work.BasinSC.StepOneCrit.disc_automorphism
import Submission.Work.BasinSC.StepOneCrit.exists_analytic_diffeomorph_opens
import Submission.Work.BasinSC.StepOneCrit.no_diffeomorph_plane

open LeanEval.Geometry
open scoped Manifold ContDiff Topology
open TopologicalSpace
open Classical

noncomputable section

namespace Work.BasinSC.StepOneCrit

/-! Riemann mapping, in function form: an open nonempty simply connected proper plane domain is
biholomorphic to the unit disc, and the biholomorphism can be normalised to send a prescribed
point `a ∈ V` to `0`.  Suggested route in this workspace:
`Work.SC.uniformization_of_simplyConnected_of_injective_into_plane`
(module `Submission.Lib.Unif2.Work.SimplyConnected.Plane`) applied to `Subtype.val : ↥V → ℂ`
gives `↥V ≃ₘ ℂ` or `↥V ≃ₘ UpperHalfPlane`; the first case is excluded by Liouville (`V ≠ Set.univ`;
use `Commons.Analysis.Complex.Koebe.weak_koebe_of_landau` to rule out an injective entire map
omitting a value), the second is transported with
`Commons.Analysis.Complex.UpperHalfPlane.halfPlane_disc_diffeomorph`.  For the derivative
requirements use `Commons.Analysis.Complex.deriv_ne_zero_of_injective_analytic`. -/
theorem uniformization_to_ball {V : Set ℂ} (hVo : IsOpen V) (hVne : V.Nonempty)
    (hVsc : SimplyConnectedSpace ↥V) (hVproper : V ≠ Set.univ) {a : ℂ} (ha : a ∈ V) :
    ∃ (φ ψ : ℂ → ℂ),
      φ a = 0 ∧
      (∀ z ∈ V, φ z ∈ Metric.ball (0 : ℂ) 1) ∧
      (∀ w ∈ Metric.ball (0 : ℂ) 1, ψ w ∈ V) ∧
      (∀ z ∈ V, ψ (φ z) = z) ∧
      (∀ w ∈ Metric.ball (0 : ℂ) 1, φ (ψ w) = w) ∧
      (∀ z ∈ V, DifferentiableAt ℂ φ z) ∧
      (∀ w ∈ Metric.ball (0 : ℂ) 1, DifferentiableAt ℂ ψ w) ∧
      (∀ z ∈ V, deriv φ z ≠ 0) ∧
      (∀ w ∈ Metric.ball (0 : ℂ) 1, deriv ψ w ≠ 0) := by
  classical
  -- The open subset `V` as an open subset for the complex-manifold structure.
  let U : TopologicalSpace.Opens ℂ := ⟨V, hVo⟩
  have hUne : ((U : Set ℂ)).Nonempty := hVne
  haveI hSCU : SimplyConnectedSpace ↥U := hVsc
  -- The inclusion `↥U → ℂ` is holomorphic: the charts of an open subset are the coercion.
  have hhol : Submission.HolomorphicOnX (Subtype.val : ↥U → ℂ) Set.univ := by
    intro x _
    rw [Submission.HolomorphicOnXAt]
    have hev : (fun z : ℂ => (Subtype.val ((chartAt ℂ x).symm z) : ℂ)) =ᶠ[𝓝 ((x : ↥U) : ℂ)]
        (fun z : ℂ => z) := by
      have hmem : ((x : ↥U) : ℂ) ∈ U := x.2
      filter_upwards [IsOpen.mem_nhds (show IsOpen (U : Set ℂ) from hVo) hmem] with z hz
      exact Submission.opens_chartAt_symm_apply_cast U hz
    have hpt : (chartAt ℂ x) x = ((x : ↥U) : ℂ) := Submission.opens_chartAt_apply U x x
    rw [hpt]
    exact (analyticAt_id (z := ((x : ↥U) : ℂ))).congr hev.symm
  -- `↥U` is not compact, since `U` is a proper nonempty open subset of `ℂ`.
  have hnc : ¬ CompactSpace ↥U := by
    intro hc
    have hcomp : IsCompact (U : Set ℂ) := by
      have h1 : IsCompact (Set.univ : Set ↥U) := isCompact_univ
      have h2 := h1.image (continuous_subtype_val : Continuous (Subtype.val : ↥U → ℂ))
      simpa using h2
    have hcl : IsClosed (U : Set ℂ) := hcomp.isClosed
    exact hVproper (IsClopen.eq_univ (s := (U : Set ℂ)) ⟨hcl, hVo⟩ hUne)
  -- Uniformization of `↥U`, from the injective holomorphic map `Subtype.val`.
  rcases Work.SC.uniformization_of_simplyConnected_of_injective_into_plane (X := ↥U) hnc hhol
    Subtype.val_injective with hcase | hcase
  · -- impossible: `↥U ≃ₘ ℂ` would make `ℂ` biholomorphic to a proper domain
    obtain ⟨e⟩ := hcase
    exact absurd ⟨e⟩ (no_diffeomorph_plane hVo hVproper)
  · -- `↥U ≃ₘ ℍ`; transport to the unit disc
    obtain ⟨e⟩ := hcase
    obtain ⟨d⟩ := Commons.Analysis.Complex.UpperHalfPlane.halfPlane_disc_diffeomorph
    let D : ↥U ≃ₘ⟮mℂ, mℂ⟯ Submission.Helpers.DiscOpen := e.trans d
    -- `Φ` realises `D` as a function of `ℂ`; `Ψ` realises its inverse `D.symm`.
    obtain ⟨Φ, hΦeval, hΦan, hΦderiv⟩ := exists_analytic_diffeomorph_opens D
    obtain ⟨Ψ, hΨeval, hΨan, hΨderiv⟩ := exists_analytic_diffeomorph_opens D.symm
    have hDnorm : ∀ x : ↥U, ‖((D x : Submission.Helpers.DiscOpen) : ℂ)‖ < 1 := by
      intro x
      have h : ((D x : Submission.Helpers.DiscOpen) : ℂ) ∈ Metric.ball (0 : ℂ) 1 := (D x).2
      rwa [Metric.mem_ball, dist_zero_right] at h
    have hc : ‖Φ a‖ < 1 := by
      rw [hΦeval a ha]
      exact hDnorm ⟨a, ha⟩
    -- the disc automorphism sending `Φ a` to `0` normalises the biholomorphism
    obtain ⟨m, η, hmc, hmball, hηball, hηm, hmη, hmdiff, hηdiff, hmderiv, hηderiv⟩ :=
      disc_automorphism hc
    have hΦn : ∀ z (hz : z ∈ V), ‖Φ z‖ < 1 := by
      intro z hz
      have hzU : z ∈ (U : Set ℂ) := hz
      rw [hΦeval z hzU]
      exact hDnorm ⟨z, hzU⟩
    have hmem_of_lt : ∀ w : ℂ, ‖w‖ < 1 → w ∈ Metric.ball (0 : ℂ) 1 := by
      intro w hw
      rwa [Metric.mem_ball, dist_zero_right]
    have hlt_of_mem : ∀ w : ℂ, w ∈ Metric.ball (0 : ℂ) 1 → ‖w‖ < 1 := by
      intro w hw
      rwa [Metric.mem_ball, dist_zero_right] at hw
    refine ⟨fun z => m (Φ z), fun w => Ψ (η w), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show m (Φ a) = 0
      exact hmc
    · intro z hz
      show m (Φ z) ∈ Metric.ball (0 : ℂ) 1
      have hlt := hΦn z hz
      have h1 := hmball (Φ z) hlt
      rwa [Metric.mem_ball, dist_zero_right]
    · intro w hw
      show Ψ (η w) ∈ V
      have hwn := hlt_of_mem w hw
      have hηn := hηball w hwn
      rw [hΨeval (η w) (hmem_of_lt (η w) hηn)]
      exact (D.symm ⟨η w, hmem_of_lt (η w) hηn⟩ : ↥U).2
    · intro z hz
      show Ψ (η (m (Φ z))) = z
      have hzU : z ∈ (U : Set ℂ) := hz
      have hlt := hΦn z hz
      have hmem := hmem_of_lt (Φ z) hlt
      rw [hηm (Φ z) (le_of_lt hlt)]
      show Ψ (Φ z) = z
      rw [hΨeval (Φ z) hmem]
      show ((D.symm ⟨Φ z, hmem⟩ : ↥U) : ℂ) = z
      have hsub : (⟨Φ z, hmem⟩ : Submission.Helpers.DiscOpen) = D ⟨z, hzU⟩ := by
        apply Subtype.ext
        show Φ z = ((D ⟨z, hzU⟩ : Submission.Helpers.DiscOpen) : ℂ)
        exact hΦeval z hzU
      rw [hsub]
      have h2 := congrArg (fun y : ↥U => (y : ℂ)) (D.symm_apply_apply ⟨z, hzU⟩)
      simpa using h2
    · intro w hw
      show m (Φ (Ψ (η w))) = w
      have hwn := hlt_of_mem w hw
      have hηn := hηball w hwn
      have hηmem := hmem_of_lt (η w) hηn
      have hΨu : Ψ (η w) = ((D.symm ⟨η w, hηmem⟩ : ↥U) : ℂ) := hΨeval (η w) hηmem
      have hΨmem : Ψ (η w) ∈ (U : Set ℂ) := by
        rw [hΨu]
        exact (D.symm ⟨η w, hηmem⟩ : ↥U).2
      have hΦΨ : Φ (Ψ (η w)) = η w := by
        rw [hΦeval (Ψ (η w)) hΨmem]
        show ((D ⟨Ψ (η w), hΨmem⟩ : Submission.Helpers.DiscOpen) : ℂ) = η w
        have hsub : (⟨Ψ (η w), hΨmem⟩ : ↥U) = D.symm ⟨η w, hηmem⟩ := by
          apply Subtype.ext
          show Ψ (η w) = ((D.symm ⟨η w, hηmem⟩ : ↥U) : ℂ)
          exact hΨu
        rw [hsub]
        have h2 := congrArg (fun y : Submission.Helpers.DiscOpen => (y : ℂ))
          (D.apply_symm_apply ⟨η w, hηmem⟩)
        simpa using h2
      rw [hΦΨ]
      exact hmη w (le_of_lt hwn)
    · intro z hz
      show DifferentiableAt ℂ (fun z => m (Φ z)) z
      exact (hmdiff (Φ z) (le_of_lt (hΦn z hz))).comp z ((hΦan z hz).differentiableAt)
    · intro w hw
      show DifferentiableAt ℂ (fun w => Ψ (η w)) w
      have hwn := hlt_of_mem w hw
      have hηn := hηball w hwn
      exact (hΨan (η w) (hmem_of_lt (η w) hηn)).differentiableAt.comp w (hηdiff w (le_of_lt hwn))
    · intro z hz
      show deriv (fun z => m (Φ z)) z ≠ 0
      have hzU : z ∈ (U : Set ℂ) := hz
      have hlt := hΦn z hz
      have hdc : deriv (fun z => m (Φ z)) z = deriv m (Φ z) * deriv Φ z := by
        have h := deriv_comp (x := z) (h := Φ) (h₂ := m)
          (hmdiff (Φ z) (le_of_lt hlt)) ((hΦan z hzU).differentiableAt)
        simpa [Function.comp_def] using h
      rw [hdc]
      exact mul_ne_zero (hmderiv (Φ z) (le_of_lt hlt)) (hΦderiv z hzU)
    · intro w hw
      show deriv (fun w => Ψ (η w)) w ≠ 0
      have hwn := hlt_of_mem w hw
      have hηn := hηball w hwn
      have hdc : deriv (fun w => Ψ (η w)) w = deriv Ψ (η w) * deriv η w := by
        have h := deriv_comp (x := w) (h := η) (h₂ := Ψ)
          ((hΨan (η w) (hmem_of_lt (η w) hηn)).differentiableAt) (hηdiff w (le_of_lt hwn))
        simpa [Function.comp_def] using h
      rw [hdc]
      exact mul_ne_zero (hΨderiv (η w) (hmem_of_lt (η w) hηn)) (hηderiv w (le_of_lt hwn))

end Work.BasinSC.StepOneCrit
