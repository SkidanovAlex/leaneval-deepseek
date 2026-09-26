import Mathlib
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.Asymptotics.continuousOn_Kfun_clean
import Submission.Work.Asymptotics.measurable_Kaxis_Kfun
import Submission.Work.Asymptotics.differentiableAt_Kfun_tau

set_option linter.unusedVariables false

namespace Work.CKFinal.ArcFin

open MeasureTheory UpperHalfPlane Filter Topology
open scoped Topology

/-- **Continuity of the low layer on a ball.**

The low piece of the CKMRV layer is
`layerLow ℓ d τ r = 4 sin²(πr²/2) ∫_t∈(0,1] K^{(d)}(τ, i t) e^{-π r² t} dt`.
On a ball on which the contour integrand is uniformly bounded (`hbound`) and on which the
coincidences `j τ = j (i t)` of the pole divisor with the contour occur only for finitely many
`t` per `τ` (`hcoin`), the parameter integral is continuous: the integrand converges pointwise
to the value at the limit point for all but finitely many `t`, and the uniform bound supplies an
integrable dominating function on the finite interval `(0,1]`. -/
theorem continuousOn_layerLow_ball (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (r : ℝ) {τ₀ : UpperHalfPlane} {ρ C : ℝ} (hρ : 0 < ρ) (hC : 0 ≤ C)
    (hbound : ∀ τ : UpperHalfPlane, τ ∈ Metric.closedBall τ₀ ρ → ∀ t : ℝ, 0 < t → t ≤ 1 →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ C)
    (hcoin : ∀ τ : UpperHalfPlane, τ ∈ Metric.closedBall τ₀ ρ →
      ∃ S : Set ℝ, S.Finite ∧ ∀ (t : ℝ) (ht : 0 < t),
        Work.Kernels.jInvariantFun τ = Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) →
          t ∈ S) :
    ContinuousOn (fun τ : UpperHalfPlane => Work.Asymptotics.layerLow ℓ d τ r)
      (Metric.ball τ₀ ρ) := by
  refine continuousOn_of_forall_continuousAt (fun τ₁ hτ₁ => ?_)
  -- The closed ball is a neighbourhood of any point of the open ball.
  have hclosed_mem : Metric.closedBall τ₀ ρ ∈ 𝓝 τ₁ :=
    Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hτ₁) Metric.ball_subset_closedBall
  -- Rewrite `layerLow` as the (constant) prefactor times an interval integral.
  have hEq : ∀ τ : UpperHalfPlane, Work.Asymptotics.layerLow ℓ d τ r =
      Work.Asymptotics.sinSq r * ∫ t in (0 : ℝ)..1,
        Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * Work.Asymptotics.gaussWeight r t := by
    intro τ
    simp only [Work.Asymptotics.layerLow, Work.Asymptotics.gaussWeight]
  -- Continuity of the interval integral, by dominated convergence.
  have hcont : ContinuousAt (fun τ : UpperHalfPlane => Work.Asymptotics.sinSq r *
      ∫ t in (0 : ℝ)..1, Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t *
        Work.Asymptotics.gaussWeight r t) τ₁ := by
    refine ContinuousAt.const_mul ?_ _
    refine intervalIntegral.continuousAt_of_dominated_interval (μ := volume) (a := 0) (b := 1)
      (bound := fun _ => C) ?_ ?_ ?_ ?_
    · -- Strong measurability in `t` of the integrand, for `τ` near `τ₁`.
      filter_upwards with x
      have h1 : Measurable (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) x t) :=
        Work.Asymptotics.measurable_Kaxis_Kfun ℓ d hd x
      have h2 : Measurable (fun t : ℝ => Work.Asymptotics.gaussWeight r t) := by
        unfold Work.Asymptotics.gaussWeight; fun_prop
      exact (h1.mul h2).aestronglyMeasurable
    · -- The uniform bound, a.e. in `t`.
      filter_upwards [hclosed_mem] with x hx
      filter_upwards with t ht
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
      have ht0 : 0 < t := ht.1
      have ht1 : t ≤ 1 := ht.2
      have hb := hbound x hx t ht0 ht1
      have hg : ‖Work.Asymptotics.gaussWeight r t‖ ≤ 1 := by
        rw [Work.Asymptotics.norm_gaussWeight, Real.exp_le_one_iff]
        exact neg_nonpos.mpr (mul_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg r)) ht0.le)
      rw [norm_mul]
      calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) x t‖
            * ‖Work.Asymptotics.gaussWeight r t‖ ≤ C * 1 :=
            mul_le_mul hb hg (norm_nonneg _) hC
        _ = C := mul_one C
    · -- The constant bound is interval integrable on `(0,1]`.
      exact intervalIntegrable_const
    · -- Continuity at `τ₁` of the integrand, for a.e. `t`: away from the finite coincidence set
      -- the kernel `Kfun` is continuous in its first variable (`continuousAt_Kfun_of_clean`).
      obtain ⟨S, hSfin, hSprop⟩ := hcoin τ₁ (Metric.ball_subset_closedBall hτ₁)
      have hSae : ∀ᵐ t ∂volume, t ∉ S := by
        rw [MeasureTheory.ae_iff]
        have h : {a : ℝ | ¬ a ∉ S} = S := by ext a; simp
        rw [h]; exact hSfin.measure_zero volume
      filter_upwards [hSae] with t htS htIoc
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at htIoc
      have ht0 : 0 < t := htIoc.1
      have hJ : Work.Kernels.jInvariantFun τ₁
          ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht0) := by
        intro h; exact htS (hSprop t ht0 h)
      have h2 : ContinuousAt (fun τ : UpperHalfPlane =>
          Work.Kernels.Kfun ℓ d τ (Work.Kernels.imagAxis t ht0)) τ₁ := by
        have h1 := Work.Asymptotics.continuousAt_Kfun_of_clean (ℓ := ℓ) (d := d) hd
          (p := (τ₁, Work.Kernels.imagAxis t ht0)) hJ
        have hmap : ContinuousAt (fun τ : UpperHalfPlane => (τ, Work.Kernels.imagAxis t ht0)) τ₁ :=
          continuousAt_id.prodMk continuousAt_const
        have h := ContinuousAt.comp (x := τ₁)
          (f := fun τ : UpperHalfPlane => (τ, Work.Kernels.imagAxis t ht0))
          (g := fun q : UpperHalfPlane × UpperHalfPlane => Work.Kernels.Kfun ℓ d q.1 q.2)
          h1 hmap
        exact h.congr (Eventually.of_forall (fun τ => rfl))
      have h3 : ContinuousAt (fun τ : UpperHalfPlane =>
          Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t) τ₁ := by
        refine h2.congr (Eventually.of_forall (fun τ => ?_))
        show Work.Kernels.Kfun ℓ d τ (Work.Kernels.imagAxis t ht0)
          = Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        rw [Work.Kernels.Kaxis, dif_pos ht0]
      exact h3.mul continuousAt_const
  -- Reassemble: `layerLow` equals the continuous parametrised integral pointwise.
  refine hcont.congr ?_
  filter_upwards with τ
  exact (hEq τ).symm

end Work.CKFinal.ArcFin
