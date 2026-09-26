/-
# Boundedness of `B₀core · 𝓛` on the low strip of the funnel

The funnel `Work.Asymptotics.Funnel` is `𝒟 ∩ {2 ≤ Im τ}`, where `𝒟` is the CKMRV
fundamental domain `{-1 < Re z < 1, |z ∓ 1/2| > 1/2}`.  On the *low* part of the funnel,
i.e. below a fixed height `H`, the region is contained in the Euclidean box
`{|Re τ| ≤ 1, 2 ≤ Im τ ≤ max H 2}`, whose closure is compact in `ℍ`.

The function `τ ↦ B₀core τ · 𝓛 τ = E₄(τ)² Ñ(τ) 𝓛(τ)/Δ(τ)` is continuous on all of `ℍ`
(the only possible poles of `B₀core` would come from `Δ = 0`, and `Δ` never vanishes on
`ℍ`; `𝓛` is holomorphic by `LogLambdaData.holo`).  So on the compact low strip it is
bounded, which is the statement proved here.

We reuse `Work.LayerCont.Glue.isCompact_closure_DomainD_inter` for the compactness of
`closure 𝒟 ∩ {δ ≤ Im ≤ T}`.
-/
import Mathlib
import Submission.Work.Asymptotics.Funnel24Aux
import Submission.Work.Residues.KMinusCuspDefs
import Submission.Work.LayerCont.Glue.CompactDomainD

namespace Work.CKFinal.LineDecay

open UpperHalfPlane

/-- The function `τ ↦ B₀core τ · 𝓛 τ` is continuous on the upper half plane. -/
lemma continuous_B0core_mul_L (ℓ : Work.Kernels.LogLambdaData) :
    Continuous (fun τ : UpperHalfPlane => Work.Residues.B0core τ * ℓ.L τ) := by
  have hE4 : Continuous (Work.Kernels.E4Fun : UpperHalfPlane → ℂ) :=
    Work.Kernels.ClassicalFacts.E4Fun_mem_InP.1.continuous
  have hE6 : Continuous (Work.Kernels.E6Fun : UpperHalfPlane → ℂ) :=
    Work.Kernels.ClassicalFacts.E6Fun_mem_InP.1.continuous
  have hD : Continuous (Work.Kernels.DeltaFun : UpperHalfPlane → ℂ) :=
    Work.Kernels.ClassicalFacts.DeltaFun_mem_InP.1.continuous
  have hU : Continuous (Work.Kernels.UFun : UpperHalfPlane → ℂ) :=
    (Work.Kernels.ClassicalFacts.theta00Fun_mem_InP.1.continuous).pow 4
  have hW : Continuous (Work.Kernels.WFun : UpperHalfPlane → ℂ) :=
    (Work.Kernels.ClassicalFacts.theta01Fun_mem_InP.1.continuous).pow 4
  have hV : Continuous (Work.Kernels.VFun : UpperHalfPlane → ℂ) :=
    (Work.Kernels.ClassicalFacts.theta10Fun_mem_InP.1.continuous).pow 4
  have hxi2 : Continuous (Work.Kernels.xi2Fun : UpperHalfPlane → ℂ) := by
    rw [show Work.Kernels.xi2Fun
        = fun τ : UpperHalfPlane => Work.Kernels.UFun τ + Work.Kernels.WFun τ from rfl]
    exact hU.add hW
  have hxi4 : Continuous (Work.Kernels.xi4Fun : UpperHalfPlane → ℂ) := by
    rw [show Work.Kernels.xi4Fun
        = fun τ : UpperHalfPlane => Work.Kernels.UFun τ ^ 2 + Work.Kernels.WFun τ ^ 2
            - 2 * Work.Kernels.VFun τ ^ 2 from rfl]
    exact ((hU.pow 2).add (hW.pow 2)).sub ((hV.pow 2).const_mul 2)
  have hNt : Continuous (Work.Residues.Ntfun : UpperHalfPlane → ℂ) := by
    rw [show Work.Residues.Ntfun = fun τ : UpperHalfPlane =>
        -2 * Work.Kernels.xi4Fun τ * Work.Kernels.E4Fun τ ^ 3
          + 3 * Work.Kernels.xi2Fun τ * Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ
          - Work.Kernels.xi4Fun τ * Work.Kernels.E6Fun τ ^ 2 from rfl]
    exact ((((continuous_const : Continuous fun _ : UpperHalfPlane => (-2 : ℂ))).mul hxi4).mul
        (hE4.pow 3)).add
      (((continuous_const.mul hxi2).mul (hE4.pow 2)).mul hE6)
      |>.sub (hxi4.mul (hE6.pow 2))
  have hB0 : Continuous (Work.Residues.B0core : UpperHalfPlane → ℂ) := by
    rw [show Work.Residues.B0core = fun τ : UpperHalfPlane =>
        Work.Kernels.E4Fun τ ^ 2 * Work.Residues.Ntfun τ / Work.Kernels.DeltaFun τ from rfl]
    exact ((hE4.pow 2).mul hNt).div hD
      (fun τ => Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ)
  exact hB0.mul ℓ.holo.continuous

theorem Ncusp24_V0L_lowstrip (ℓ : Work.Kernels.LogLambdaData) (H : ℝ) :
    ∃ D : ℝ, ∀ τ : UpperHalfPlane, Work.Asymptotics.Funnel τ → τ.im ≤ H →
      ‖Work.Residues.B0core τ * ℓ.L τ‖ ≤ D := by
  obtain ⟨D, hD⟩ := (Work.LayerCont.Glue.isCompact_closure_DomainD_inter
      (T := max H 2) (by norm_num : (0 : ℝ) < 2)).exists_bound_of_continuousOn
    (continuous_B0core_mul_L ℓ).continuousOn
  refine ⟨D, fun τ hτ hH => ?_⟩
  exact hD τ ⟨subset_closure hτ.1, hτ.2, le_trans hH (le_max_left H 2)⟩

end Work.CKFinal.LineDecay
