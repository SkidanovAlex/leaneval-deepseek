import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.setup
import Submission.Work.A14D.D_local_at_one
import Submission.Work.A14D.H_local_at_one
import Submission.Work.A14D.uh_ode

namespace Work.A14D

theorem D_local_at_one_refined (a b c : ℤ) (h : Submission.CDTPlan.ARel a b c)
    (HU HL : ℂ → ℂ)
    (hHU : DifferentiableOn ℂ HU Work.A14D.SU ∧
      (∀ z ∈ Work.A14D.SU, Work.A14D.LZ HU z = Work.A14D.rhsZ b c z) ∧
      ∀ z ∈ Work.A14D.SU ∩ Metric.ball 0 1, HU z = Work.A14D.Hfun a b c z)
    (hHL : DifferentiableOn ℂ HL Work.A14D.SL ∧
      (∀ z ∈ Work.A14D.SL, Work.A14D.LZ HL z = Work.A14D.rhsZ b c z) ∧
      ∀ z ∈ Work.A14D.SL ∩ Metric.ball 0 1, HL z = Work.A14D.Hfun a b c z)
    (D : ℂ → ℂ) (hD : DifferentiableOn ℂ D Work.A14D.Om1)
    (hDL : ∀ z ∈ Work.A14D.Om1, Work.A14D.LZ D z = 0)
    (hDj : ∀ z ∈ Work.A14D.SU ∩ Work.A14D.SL, D z = HU z - HL z) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 8 / 9 ∧ ∃ A : ℂ → ℂ,
      DifferentiableOn ℂ A (Metric.ball 1 δ) ∧
      ∀ z ∈ Metric.ball 1 δ ∩ Work.A14D.Om1,
        D z = A z + (Real.pi * Complex.I * (c : ℂ) / 4) * Work.A14D.uh z
          * Complex.log (z - 1) := by
  -- local structure of `Hfun` at `1` (`Work.A14D.H_local_at_one`)
  obtain ⟨δ₀, hδ₀pos, hδ₀89, e0, e1, he0d, he1d, hid⟩ := H_local_at_one a b c h
  have hδ₀89le : δ₀ ≤ 8 / 9 := le_of_lt hδ₀89
  obtain ⟨huhd, huh1, huhode⟩ := uh_ode
  -- the double-log coefficient `e2 = -(c/16) u_h`
  set e2 : ℂ → ℂ := fun z => -((c : ℂ) / 16) * uh z with he2def
  have he2d : DifferentiableOn ℂ e2 (Metric.ball (1 : ℂ) δ₀) := by
    rw [he2def]
    exact (huhd.mono (Metric.ball_subset_ball hδ₀89le)).const_mul _
  have hid2 : ∀ z ∈ lens1 δ₀, Hfun a b c z = e0 z + e1 z * ell z + e2 z * ell z ^ 2 := by
    intro z hz
    have h1 := hid z hz
    rw [h1]
    simp only [he2def]
    ring
  -- propagate the model to the two half-discs
  have hU := U_struct (a := a) (b := b) (c := c) hδ₀pos he0d he1d he2d hid2 hHU.1 hHU.2.2
  have hL := L_struct (a := a) (b := b) (c := c) hδ₀pos he0d he1d he2d hid2 hHL.1 hHL.2.2
  refine ⟨δ₀ / 4, by linarith, by linarith, fun z => (-2 * (Real.pi : ℂ) * Complex.I) * e1 z, ?_,
    ?_⟩
  · exact (he1d.mono (Metric.ball_subset_ball (by linarith : δ₀ / 4 ≤ δ₀))).const_mul _
  · intro z hz
    have hPsi : ∀ w ∈ Metric.ball (1 : ℂ) (δ₀ / 4) ∩ Om1,
        D w - (-2 * (Real.pi : ℂ) * Complex.I) * e1 w
          - (Real.pi * Complex.I * (c : ℂ) / 4) * uh w * Complex.log (w - 1) = 0 := by
      refine eqOn_zero_of_Om1ball_of_Ioo (δ := δ₀ / 4) (ε := δ₀ / 8)
        (by linarith) (by linarith) (by linarith) ?_ ?_
      · have hD' : DifferentiableOn ℂ D (Metric.ball (1 : ℂ) (δ₀ / 4) ∩ Om1) :=
          hD.mono Set.inter_subset_right
        have hA' : DifferentiableOn ℂ (fun w : ℂ => (-2 * (Real.pi : ℂ) * Complex.I) * e1 w)
            (Metric.ball (1 : ℂ) (δ₀ / 4) ∩ Om1) :=
          ((he1d.mono (Metric.ball_subset_ball (by linarith : δ₀ / 4 ≤ δ₀))).const_mul _).mono
            Set.inter_subset_left
        have huh' : DifferentiableOn ℂ uh (Metric.ball (1 : ℂ) (δ₀ / 4) ∩ Om1) :=
          (huhd.mono (Metric.ball_subset_ball (by linarith : δ₀ / 4 ≤ 8 / 9))).mono
            Set.inter_subset_left
        have hlog' : DifferentiableOn ℂ (fun w : ℂ => Complex.log (w - 1))
            (Metric.ball (1 : ℂ) (δ₀ / 4) ∩ Om1) :=
          differentiableOn_log_sub_one.mono Set.inter_subset_right
        exact (hD'.sub hA').sub
          (((differentiableOn_const (Real.pi * Complex.I * (c : ℂ) / 4)).mul huh').mul hlog')
      · intro t ht
        obtain ⟨ht1, ht2⟩ := ht
        have htδ : t - 1 < δ₀ := by linarith
        have hray := D_ray_value (δ := δ₀) hδ₀pos he0d he1d he2d hHU.1 hHL.1 hDj hU hL ht1 htδ
        have he2t : e2 (t : ℂ) = -((c : ℂ) / 16) * uh (t : ℂ) := by rw [he2def]
        rw [he2t] at hray
        have hlog : Complex.log ((t : ℂ) - 1) = ((Real.log (t - 1) : ℝ) : ℂ) := by
          rw [show (t : ℂ) - 1 = ((t - 1 : ℝ) : ℂ) by push_cast; ring]
          exact (Complex.ofReal_log (by linarith : (0 : ℝ) ≤ t - 1)).symm
        rw [hlog]
        have key : D (t : ℂ) = (-2 * (Real.pi : ℂ) * Complex.I) * e1 (t : ℂ)
            + (Real.pi * Complex.I * (c : ℂ) / 4) * uh (t : ℂ) * ((Real.log (t - 1) : ℝ) : ℂ) := by
          rw [hray]; ring
        rw [key]; ring
    have := hPsi z hz
    linear_combination this

end Work.A14D
