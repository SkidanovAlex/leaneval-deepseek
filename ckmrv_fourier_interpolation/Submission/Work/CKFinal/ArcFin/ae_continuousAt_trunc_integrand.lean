import Mathlib
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.Asymptotics.differentiableAt_Kfun_tau
import Submission.Work.Asymptotics.HalfFunnel.tangTailExpansion
import Submission.Work.Asymptotics.continuousOn_Kfun_clean

namespace Work.CKFinal.ArcFin

set_option linter.unusedVariables false

open MeasureTheory Filter Topology
open scoped Topology

/-- **Almost-everywhere continuity of the truncated contour integrand in `τ`.**

For every `τ₁` in the open ball `ball τ₀ ρ` and almost every `t ∈ [1,∞)`, the truncated
integrand
`τ ↦ (K^{(d)}(τ,it) - 𝒢(τ,it)) e^{-π r² t}`
of the CKMRV layer decomposition (5.2)--(5.3) is continuous at `τ₁`.

The only `t` for which continuity can fail are those with `j τ₁ = j (i t)`, i.e. the pullback
of the coincidence divisor to the contour; the hypothesis `hcoin` says that for each `τ` in the
closed ball this set is finite, hence of measure zero.  Off those `t` the kernel is continuous
in `τ` (`continuousAt_Kfun_of_clean`), and the cusp part `𝒢 = Aexp (Gcusp ℓ d)` is continuous in
`τ` because its coefficient functions are (`continuous_Aexp_tang`).  For `t ≤ 0` the truncated
kernel `Kaxis` vanishes identically in `τ`. -/
theorem ae_continuousAt_trunc_integrand (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (r : ℝ) {τ₀ : UpperHalfPlane} {ρ : ℝ} (hρ : 0 < ρ)
    (hcoin : ∀ τ : UpperHalfPlane, τ ∈ Metric.closedBall τ₀ ρ →
      ∃ S : Set ℝ, S.Finite ∧ ∀ (t : ℝ) (ht : 0 < t),
        Work.Kernels.jInvariantFun τ = Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) →
          t ∈ S) :
    ∀ τ₁ ∈ Metric.ball τ₀ ρ,
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ici (1 : ℝ))),
        ContinuousAt (fun τ : UpperHalfPlane =>
          (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) τ₁ := by
  intro τ₁ hτ₁
  -- The finite coincidence set of `τ₁` is null for the measure on `[1,∞)`.
  obtain ⟨S, hSfin, hSprop⟩ := hcoin τ₁ (Metric.ball_subset_closedBall hτ₁)
  have hSae : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ici (1 : ℝ))), t ∉ S := by
    rw [MeasureTheory.ae_iff]
    have h : {a : ℝ | ¬ a ∉ S} = S := by ext a; simp
    rw [h, MeasureTheory.Measure.restrict_apply hSfin.measurableSet]
    exact measure_mono_null Set.inter_subset_left (hSfin.measure_zero volume)
  filter_upwards [hSae] with t htS
  -- The cusp part is continuous in `τ`: its coefficients `Gcusp ℓ d i j` are.
  have hA : ContinuousAt (fun τ : UpperHalfPlane =>
      Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) τ₁ :=
    ((Work.Asymptotics.HalfFunnel.continuous_Aexp_tang ℓ d hd).comp
      (continuous_id.prodMk continuous_const)).continuousAt
  -- The truncated kernel is continuous in `τ`.
  have hK : ContinuousAt (fun τ : UpperHalfPlane =>
      Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t) τ₁ := by
    by_cases ht : 0 < t
    · have hJ : Work.Kernels.jInvariantFun τ₁
          ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) :=
        fun h => htS (hSprop t ht h)
      have h2 : ContinuousAt (fun τ : UpperHalfPlane =>
          Work.Kernels.Kfun ℓ d τ (Work.Kernels.imagAxis t ht)) τ₁ := by
        have h1 := Work.Asymptotics.continuousAt_Kfun_of_clean (ℓ := ℓ) (d := d) hd
          (p := (τ₁, Work.Kernels.imagAxis t ht)) hJ
        have hmap : ContinuousAt (fun τ : UpperHalfPlane =>
            (τ, Work.Kernels.imagAxis t ht)) τ₁ :=
          continuousAt_id.prodMk continuousAt_const
        exact ContinuousAt.comp (x := τ₁)
          (f := fun τ : UpperHalfPlane => (τ, Work.Kernels.imagAxis t ht))
          (g := fun q : UpperHalfPlane × UpperHalfPlane =>
            Work.Kernels.Kfun ℓ d q.1 q.2) h1 hmap
      refine h2.congr (Eventually.of_forall (fun τ => ?_))
      simp only [Work.Kernels.Kaxis, dif_pos ht]
    · refine (continuousAt_const : ContinuousAt (fun _ : UpperHalfPlane => (0 : ℂ)) τ₁).congr
        (Eventually.of_forall (fun τ => ?_))
      simp only [Work.Kernels.Kaxis, dif_neg ht]
  exact (hK.sub hA).mul continuousAt_const

end Work.CKFinal.ArcFin
