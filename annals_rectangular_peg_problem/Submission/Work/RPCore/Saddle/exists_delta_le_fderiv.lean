import Mathlib
import Submission.Work.RPCore.Flow.fderiv_eq_of_periodic
import Submission.Work.RPCore.Saddle.periodic_reduce_Icc
import Submission.Work.RPCore.Saddle.fderiv_coercive_lower_bound

set_option autoImplicit false

namespace Work.RPCore.Saddle

open scoped Topology
open Filter

theorem exists_delta_le_fderiv {k l : ℕ}
    (F : ℝ × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)) → ℝ)
    (hF : ContDiff ℝ 1 F) (Pd : ℝ) (hPd : 0 < Pd)
    (hper : ∀ a v, F (a + Pd, v) = F (a, v))
    (A₁ : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (A₂ : EuclideanSpace ℝ (Fin l) →L[ℝ] EuclideanSpace ℝ (Fin l))
    (lam C : ℝ) (hlam : 0 < lam) (hC : 0 ≤ C)
    (hA₁ : ∀ x, inner ℝ (A₁ x) x ≤ -lam * ‖x‖ ^ 2)
    (hA₂ : ∀ y, lam * ‖y‖ ^ 2 ≤ inner ℝ (A₂ y) y)
    (hC1 : ∀ a v w, |fderiv ℝ F (a, v) w - (inner ℝ (A₁ v.1) w.2.1 + inner ℝ (A₂ v.2) w.2.2)| ≤ C * ‖w‖)
    (hcrit : ∀ z, fderiv ℝ F z ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z, δ ≤ ‖fderiv ℝ F z‖ := by
  -- Coercive lower bound on the derivative, uniformly in `a`.
  have hA_bound : ∀ (z : ℝ × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l))),
      lam * ‖z.2‖ - C ≤ ‖fderiv ℝ F z‖ :=
    fderiv_coercive_lower_bound F A₁ A₂ lam C hlam hC hA₁ hA₂ hC1
  -- `fderiv F` is invariant under translation by `(Pd, 0)`.
  have hshift : ∀ x : ℝ × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)),
      fderiv ℝ F (x + (Pd, (0 : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)))) =
        fderiv ℝ F x := by
    intro x
    refine Work.RPCore.Flow.fderiv_eq_of_periodic F (hF.differentiable (by norm_num))
      (c := (Pd, (0 : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)))) ?_ x
    intro p
    obtain ⟨a, v⟩ := p
    simp only [Prod.mk_add_mk, add_zero]
    exact hper a v
  have hfderiv_cont : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by norm_num)
  have hg_cont : Continuous (fun z => ‖fderiv ℝ F z‖) := hfderiv_cont.norm
  set R : ℝ := (C + 1) / lam with hRdef
  have hRpos : 0 < R := by
    rw [hRdef]; exact div_pos (by linarith) hlam
  set K : Set (ℝ × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l))) :=
    Set.Icc (0 : ℝ) Pd ×ˢ
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)) R with hKdef
  have hKcompact : IsCompact K := by
    rw [hKdef]
    exact isCompact_Icc.prod (isCompact_closedBall 0 R)
  have hKne : K.Nonempty := by
    refine ⟨(0, (0, 0)), ?_⟩
    rw [hKdef, Set.mem_prod]
    exact ⟨⟨le_refl 0, le_of_lt hPd⟩,
      by rw [Metric.mem_closedBall, dist_zero_right]; simpa using hRpos.le⟩
  obtain ⟨z₀, _hz₀K, hz₀min⟩ := hKcompact.exists_isMinOn hKne hg_cont.continuousOn
  have hδ₀pos : 0 < ‖fderiv ℝ F z₀‖ := norm_pos_iff.mpr (hcrit z₀)
  refine ⟨min ‖fderiv ℝ F z₀‖ 1, lt_min hδ₀pos one_pos, ?_⟩
  intro z
  obtain ⟨a, v⟩ := z
  by_cases hv : v ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)) R
  · -- Reduce `a` into the fundamental interval `[0, Pd]`.
    have hfper : Function.Periodic (fun a' : ℝ => fderiv ℝ F (a', v)) Pd := by
      intro a'
      have := hshift (a', v)
      simpa using this
    obtain ⟨a', ha', hfa'⟩ := periodic_reduce_Icc hPd hfper a
    have hmem : (a', v) ∈ K := by
      rw [hKdef, Set.mem_prod]; exact ⟨ha', hv⟩
    have h1 : ‖fderiv ℝ F z₀‖ ≤ ‖fderiv ℝ F (a, v)‖ := by
      have h2 := (isMinOn_iff.mp hz₀min) (a', v) hmem
      rwa [hfa'] at h2
    exact le_trans (min_le_left _ _) h1
  · -- Outside the ball, the coercive bound gives a uniform positive lower bound.
    have hRlt : R < ‖v‖ := by
      have h1 : ¬ (dist v (0 : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)) ≤ R) := by
        rw [← Metric.mem_closedBall]; exact hv
      rw [dist_zero_right] at h1
      exact not_le.mp h1
    have h2 : lam * ‖v‖ - C ≤ ‖fderiv ℝ F (a, v)‖ := hA_bound (a, v)
    have h3 : lam * R - C = 1 := by
      rw [hRdef]
      field_simp
      ring
    have h4 : lam * R < lam * ‖v‖ := mul_lt_mul_of_pos_left hRlt hlam
    have h5 : 1 < ‖fderiv ℝ F (a, v)‖ := by linarith
    exact le_trans (min_le_right _ _) (le_of_lt h5)

end Work.RPCore.Saddle
