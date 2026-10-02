import Submission.Work.PTGeometric.RieszProj.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Smoothness of the Riesz-projector integrand

The map `(x, θ) ↦ contIntegrand x θ = (contDen x θ)⁻¹ * contNum x θ` is `C^∞` on the open set where
`contDen x θ` is a unit; since `contDen x₀ θ` is a unit for all `θ ∈ [0, 2π]` in the situation of
interest, there is a product neighbourhood `s ×ˢ J` of `{x₀} × [0, 2π]` on which it is `C^∞`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped ContDiff InnerProduct
open Set Function MeasureTheory

namespace Work.PTGeometric

noncomputable section

variable {n : ℕ}

lemma contDiff_uncurry_contDen :
    ContDiff ℝ ∞ (fun p : EndOp n × ℝ => contDen p.1 p.2) := by
  simp only [contDen, cc, ss]
  fun_prop

lemma contDiff_uncurry_contNum :
    ContDiff ℝ ∞ (fun p : EndOp n × ℝ => contNum p.1 p.2) := by
  simp only [contNum, cc, ss]
  fun_prop

lemma continuous_uncurry_contDen : Continuous (fun p : EndOp n × ℝ => contDen p.1 p.2) :=
  contDiff_uncurry_contDen.continuous

lemma contDiffOn_ring_inverse_units :
    ContDiffOn ℝ ∞ (fun y : EndOp n => Ring.inverse y) {y | IsUnit y} := by
  rw [IsOpen.contDiffOn_iff Units.isOpen]
  intro y hy
  obtain ⟨u, rfl⟩ := hy
  exact contDiffAt_ringInverse (𝕜 := ℝ) u

lemma contDiffOn_uncurry_contIntegrand_units :
    ContDiffOn ℝ ∞ (fun p : EndOp n × ℝ => contIntegrand p.1 p.2)
      {p | IsUnit (contDen p.1 p.2)} := by
  have hinv : ContDiffOn ℝ ∞ (fun p : EndOp n × ℝ => Ring.inverse (contDen p.1 p.2))
      {p | IsUnit (contDen p.1 p.2)} :=
    (contDiffOn_ring_inverse_units (n := n)).comp contDiff_uncurry_contDen.contDiffOn
      (fun p hp => hp)
  exact hinv.mul contDiff_uncurry_contNum.contDiffOn

/-- Near a point `x₀` at which `contDen x₀ θ` is invertible for every `θ ∈ [0, 2π]`, the integrand
of the Riesz projection is `C^∞` on a product neighbourhood of `{x₀} × [0, 2π]`. -/
lemma contIntegrand_contDiffOn_nhds {x₀ : EndOp n}
    (h : ∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), IsUnit (contDen x₀ θ)) :
    ∃ s : Set (EndOp n), IsOpen s ∧ x₀ ∈ s ∧
      ∃ J : Set ℝ, IsOpen J ∧ Set.Icc (0:ℝ) (2 * Real.pi) ⊆ J ∧
        ContDiffOn ℝ ∞ (fun p : EndOp n × ℝ => contIntegrand p.1 p.2) (s ×ˢ J) := by
  have hVopen : IsOpen {p : EndOp n × ℝ | IsUnit (contDen p.1 p.2)} :=
    Units.isOpen.preimage continuous_uncurry_contDen
  have hKsub : ({x₀} ×ˢ Set.Icc (0:ℝ) (2 * Real.pi))
      ⊆ {p : EndOp n × ℝ | IsUnit (contDen p.1 p.2)} := by
    rintro ⟨p, t⟩ ⟨hp, ht⟩
    obtain rfl : p = x₀ := by simpa using hp
    exact h t ht
  obtain ⟨δ, hδpos, hδ⟩ :=
    (isCompact_singleton.prod isCompact_Icc).exists_thickening_subset_open hVopen hKsub
  refine ⟨Metric.ball x₀ (δ/2), Metric.isOpen_ball, Metric.mem_ball_self (by linarith),
    ⋃ t ∈ Set.Icc (0:ℝ) (2 * Real.pi), Metric.ball t (δ/2), ?_, ?_, ?_⟩
  · exact isOpen_iUnion fun t => isOpen_iUnion fun _ => Metric.isOpen_ball
  · intro t ht
    exact mem_iUnion.mpr ⟨t, mem_iUnion.mpr ⟨ht, Metric.mem_ball_self (by linarith)⟩⟩
  · refine (contDiffOn_uncurry_contIntegrand_units (n := n)).mono ?_
    rintro p hp
    obtain ⟨hx, ht⟩ := hp
    obtain ⟨t', ht'⟩ := mem_iUnion.mp ht
    obtain ⟨ht'Icc, ht'δ⟩ := mem_iUnion.mp ht'
    have hx1 : dist p.1 x₀ < δ/2 := Metric.mem_ball.mp hx
    have ht1 : dist p.2 t' < δ/2 := Metric.mem_ball.mp ht'δ
    refine hδ ?_
    rw [Metric.mem_thickening_iff]
    refine ⟨(x₀, t'), ⟨rfl, ht'Icc⟩, ?_⟩
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨by linarith, by linarith⟩

end

end Work.PTGeometric
