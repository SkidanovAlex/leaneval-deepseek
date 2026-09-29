import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.setup
import Submission.Work.A14D.uh_ode
import Submission.Work.C17g.linear_ode_convex
import Submission.Work.A14D.D_local_at_one
import Submission.Work.A14D.glue_three_LZ
import Submission.Work.A14D.crux_defs
import Submission.Work.A14D.crux_upper_extension
import Submission.Work.A14D.crux_lower_extension
import Submission.Work.A14D.exists_sol_LZ_convex
import Submission.Work.A14D.eqOn_of_sol_LZ
import Submission.Work.A14D.LZ_sub_const_mul
import Submission.Work.A14D.kjn_defs

namespace Work.A14D

open Complex Metric Filter
open scoped BigOperators Topology
open Work.A14D

noncomputable section

/-! ## 0.  The local structure of `D` at `z = 1` without the hypothesis `b ≠ 0`

`Work.A14D.D_local_at_one` proves the local model `D = A + (π i c/4)·u_h·log (·−1)` near `z = 1`
under the extra hypothesis `hb : b ≠ 0`, which its proof never uses.  We record the
hypothesis-free form together with the harmless extra bound `δ ≤ 8/9`, which the proof produces
anyway (`δ = δ₀/4` with `δ₀ < 8/9`). -/

theorem D_local_at_one_gen (a b c : ℤ) (h : Submission.CDTPlan.ARel a b c)
    (HU HL : ℂ → ℂ)
    (hHU : DifferentiableOn ℂ HU SU ∧ (∀ z ∈ SU, LZ HU z = rhsZ b c z) ∧
      ∀ z ∈ SU ∩ ball 0 1, HU z = Hfun a b c z)
    (hHL : DifferentiableOn ℂ HL SL ∧ (∀ z ∈ SL, LZ HL z = rhsZ b c z) ∧
      ∀ z ∈ SL ∩ ball 0 1, HL z = Hfun a b c z)
    (D : ℂ → ℂ) (hD : DifferentiableOn ℂ D Om1) (hDL : ∀ z ∈ Om1, LZ D z = 0)
    (hDj : ∀ z ∈ SU ∩ SL, D z = HU z - HL z) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 8 / 9 ∧ ∃ A : ℂ → ℂ,
      DifferentiableOn ℂ A (ball 1 δ) ∧
      ∀ z ∈ ball 1 δ ∩ Om1,
        D z = A z + (Real.pi * Complex.I * (c : ℂ) / 4) * uh z * Complex.log (z - 1) := by
  -- local structure of `Hfun` at `1`
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
  -- the two half-disc structures
  have hU := U_struct (a := a) (b := b) (c := c) hδ₀pos he0d he1d he2d hid2 hHU.1 hHU.2.2
  have hL := L_struct (a := a) (b := b) (c := c) hδ₀pos he0d he1d he2d hid2 hHL.1 hHL.2.2
  refine ⟨δ₀ / 4, by linarith, by linarith, fun z => (-2 * (Real.pi : ℂ) * Complex.I) * e1 z, ?_, ?_⟩
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


/-! ## 1.  The analytic crux -/

/-- **The analytic crux.**  The jump `D = HU - HL` of the continuations of `Hfun a b c` (a
solution of `LZ = 0` on `Om1 = ℂ ∖ (-∞,1]`) has a local holomorphic part at `z = 1` which
extends holomorphically across the real interval `(1/9,1)`: there is `E1` holomorphic on
`Om1 ∩ ball 1 (8/9)` with `D z = E1 z + (π i c/4)·uh z·log (z-1)` there, and `E1` is *also*
holomorphic at every real point `x ∈ (1/9,1)`.

This is the (only) nontrivial analytic input of the design's identity `(K)`: the two one-sided log
coefficients of `D` at `1/9` (they live on the two half-discs, whose closures meet only along
`(1/9,1)`) differ precisely because the factor `log (z-1)` jumps across that interval while `E1`
does not.

Two independent routes (both reviewed as valid):
* Pull back to the interval: the jump `j(x) := E1⁺(x) - E1⁻(x)` is real-analytic on `(1/9,1)`,
  and by `D_local_at_one` (`b ≠ 0`; the `b = 0` case is trivial since `ARel a 0 c` forces
  `a = c = 0`) it vanishes on a neighbourhood of `z = 1` inside the interval, hence identically on
  `(1/9,1)`.
* Or: put `E1 := D - (πic/4)·uh·log(z-1)`; it solves the explicit inhomogeneous ODE obtained from
  `LZ D = 0`, `LZ uh = 0` with `log(z-1)' = 1/(z-1)`, and `linear_ode_convex` gives local
  continuation across each `x ∈ (1/9,1)`. -/
theorem crux_jump (a b c : ℤ) (h : Submission.CDTPlan.ARel a b c)
    (HU HL : ℂ → ℂ)
    (hHU : DifferentiableOn ℂ HU SU ∧ (∀ z ∈ SU, LZ HU z = rhsZ b c z) ∧
      ∀ z ∈ SU ∩ ball 0 1, HU z = Hfun a b c z)
    (hHL : DifferentiableOn ℂ HL SL ∧ (∀ z ∈ SL, LZ HL z = rhsZ b c z) ∧
      ∀ z ∈ SL ∩ ball 0 1, HL z = Hfun a b c z)
    (D : ℂ → ℂ) (hD : DifferentiableOn ℂ D Om1) (hDL : ∀ z ∈ Om1, LZ D z = 0)
    (hDj : ∀ z ∈ SU ∩ SL, D z = HU z - HL z) :
    ∃ E1 : ℂ → ℂ,
      DifferentiableOn ℂ E1 (Om1 ∩ Metric.ball 1 (8 / 9)) ∧
      (∀ x : ℝ, x ∈ Set.Ioo (1 / 9) 1 → DifferentiableAt ℂ E1 (x : ℂ)) ∧
      ∀ z ∈ Om1 ∩ Metric.ball 1 (8 / 9),
        D z = E1 z + (Real.pi * Complex.I * (c : ℂ) / 4) * uh z * Complex.log (z - 1) := by
  -- ## 1. the local model of `D` at the regular singular point `z = 1`
  obtain ⟨δ, hδpos, hδ89, A, hAd, hAmodel⟩ :=
    D_local_at_one_gen a b c h HU HL hHU hHL D hD hDL hDj
  set k : ℂ := Real.pi * Complex.I * (c : ℂ) / 4 with hk
  -- ## 2. the two continuations of `D` from the two half-discs
  obtain ⟨Gu, hGu_d, hGu_ode, hGu_eq⟩ := crux_upper_extension D hD hDL
  obtain ⟨Gl, hGl_d, hGl_ode, hGl_eq⟩ := crux_lower_extension D hD hDL
  -- ## 3. the two candidate local holomorphic parts
  set Ψu : ℂ → ℂ := fun z => Gu z - k * uh z * Complex.log (1 - z)
      - (k * ((Real.pi : ℂ) * Complex.I)) * uh z with hΨu
  set Ψl : ℂ → ℂ := fun z => Gl z - k * uh z * Complex.log (1 - z)
      + (k * ((Real.pi : ℂ) * Complex.I)) * uh z with hΨl
  have huhV : DifferentiableOn ℂ uh cruxV :=
    uh_ode.1.mono (fun z hz => by
      rw [Metric.mem_ball, Complex.dist_eq]
      exact (mem_cruxV_iff.mp hz).1)
  have hlogV : DifferentiableOn ℂ (fun z : ℂ => Complex.log (1 - z)) cruxV := by
    intro z hz
    have hsp : (1 - z) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      left
      have hre : (1 - z).re = 1 - z.re := Complex.sub_re 1 z
      rw [hre]
      have h2 := (mem_cruxV_iff.mp hz).2
      linarith
    exact ((Complex.differentiableAt_log hsp).comp z
      ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id)).differentiableWithinAt
  have hΨu_d : DifferentiableOn ℂ Ψu cruxV := by
    rw [hΨu]
    exact (hGu_d.sub (((differentiableOn_const k).mul huhV).mul hlogV)).sub
      ((differentiableOn_const (k * ((Real.pi : ℂ) * Complex.I))).mul huhV)
  have hΨl_d : DifferentiableOn ℂ Ψl cruxV := by
    rw [hΨl]
    exact (hGl_d.sub (((differentiableOn_const k).mul huhV).mul hlogV)).add
      ((differentiableOn_const (k * ((Real.pi : ℂ) * Complex.I))).mul huhV)
  -- ## 4. `Ψu`, `Ψl` reproduce `D - k·uh·log (·-1)` on the two half-discs
  have hform_u : ∀ z ∈ cruxU ∩ cruxV,
      Ψu z = D z - k * uh z * Complex.log (z - 1) := by
    intro z hz
    have hzU : 0 < z.im := hz.1
    have hlog : Complex.log (1 - z) = Complex.log (z - 1) - (Real.pi : ℂ) * Complex.I := by
      have him : (1 - z).im < 0 := by
        have h1 : (1 - z).im = -z.im := by simp
        rw [h1]; linarith
      have h2 := log_neg_of_im_neg him
      rw [show -(1 - z) = z - 1 by ring] at h2
      rw [h2]; ring
    simp only [hΨu, hGu_eq hz, hlog]
    ring
  have hform_l : ∀ z ∈ cruxL ∩ cruxV,
      Ψl z = D z - k * uh z * Complex.log (z - 1) := by
    intro z hz
    have hzL : z.im < 0 := hz.1
    have hlog : Complex.log (1 - z) = Complex.log (z - 1) + (Real.pi : ℂ) * Complex.I := by
      have him : 0 < (1 - z).im := by
        have h1 : (1 - z).im = -z.im := by simp
        rw [h1]; linarith
      have h2 := log_neg_of_im_pos him
      rw [show -(1 - z) = z - 1 by ring] at h2
      rw [h2]; ring
    simp only [hΨl, hGl_eq hz, hlog]
    ring
  have hform_A : ∀ z ∈ Metric.ball (1 : ℂ) δ ∩ Om1,
      D z - k * uh z * Complex.log (z - 1) = A z := by
    intro z hz
    have h1 := hAmodel z hz
    linear_combination h1
  -- ## 5. `Ψu` and `Ψl` are both equal to `A` on the overlap with `ball 1 δ`, hence on `cruxV`
  have hΨu_A : ∀ z ∈ cruxV ∩ Metric.ball (1 : ℂ) δ, Ψu z = A z := by
    have hUo : IsOpen (cruxV ∩ Metric.ball (1 : ℂ) δ) := isOpen_cruxV.inter Metric.isOpen_ball
    have hUc : Convex ℝ (cruxV ∩ Metric.ball (1 : ℂ) δ) :=
      convex_cruxV.inter (convex_ball (1 : ℂ) δ)
    obtain ⟨z₀, ⟨hz₀U, hz₀V⟩, hz₀b⟩ := nonempty_cruxU_cruxV_ball δ hδpos
    have hnb : (cruxU ∩ cruxV ∩ Metric.ball (1 : ℂ) δ) ∈ 𝓝 z₀ :=
      ((isOpen_cruxU.inter isOpen_cruxV).inter Metric.isOpen_ball).mem_nhds
        ⟨⟨hz₀U, hz₀V⟩, hz₀b⟩
    have hev : Ψu =ᶠ[𝓝 z₀] A := by
      filter_upwards [hnb] with z hz
      obtain ⟨⟨hzU, hzV⟩, hzb⟩ := hz
      rw [hform_u z ⟨hzU, hzV⟩]
      exact hform_A z ⟨hzb, cruxU_subset_Om1 hzU⟩
    exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      ((hΨu_d.mono Set.inter_subset_left).analyticOnNhd hUo)
      ((hAd.mono Set.inter_subset_right).analyticOnNhd hUo)
      hUc.isPreconnected ⟨hz₀V, hz₀b⟩ hev
  have hΨl_A : ∀ z ∈ cruxV ∩ Metric.ball (1 : ℂ) δ, Ψl z = A z := by
    have hUo : IsOpen (cruxV ∩ Metric.ball (1 : ℂ) δ) := isOpen_cruxV.inter Metric.isOpen_ball
    have hUc : Convex ℝ (cruxV ∩ Metric.ball (1 : ℂ) δ) :=
      convex_cruxV.inter (convex_ball (1 : ℂ) δ)
    obtain ⟨z₀, ⟨hz₀U, hz₀V⟩, hz₀b⟩ := nonempty_cruxL_cruxV_ball δ hδpos
    have hnb : (cruxL ∩ cruxV ∩ Metric.ball (1 : ℂ) δ) ∈ 𝓝 z₀ :=
      ((isOpen_cruxL.inter isOpen_cruxV).inter Metric.isOpen_ball).mem_nhds
        ⟨⟨hz₀U, hz₀V⟩, hz₀b⟩
    have hev : Ψl =ᶠ[𝓝 z₀] A := by
      filter_upwards [hnb] with z hz
      obtain ⟨⟨hzL, hzV⟩, hzb⟩ := hz
      rw [hform_l z ⟨hzL, hzV⟩]
      exact hform_A z ⟨hzb, cruxL_subset_Om1 hzL⟩
    exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      ((hΨl_d.mono Set.inter_subset_left).analyticOnNhd hUo)
      ((hAd.mono Set.inter_subset_right).analyticOnNhd hUo)
      hUc.isPreconnected ⟨hz₀V, hz₀b⟩ hev
  have hΨul : ∀ z ∈ cruxV, Ψu z = Ψl z := by
    obtain ⟨z₀, ⟨hz₀U, hz₀V⟩, hz₀b⟩ := nonempty_cruxU_cruxV_ball δ hδpos
    have hnb : (cruxV ∩ Metric.ball (1 : ℂ) δ) ∈ 𝓝 z₀ :=
      (isOpen_cruxV.inter Metric.isOpen_ball).mem_nhds ⟨hz₀V, hz₀b⟩
    have hev : Ψu =ᶠ[𝓝 z₀] Ψl := by
      filter_upwards [hnb] with z hz
      rw [hΨu_A z hz, hΨl_A z hz]
    exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      (hΨu_d.analyticOnNhd isOpen_cruxV) (hΨl_d.analyticOnNhd isOpen_cruxV)
      convex_cruxV.isPreconnected hz₀V hev
  have hΦ : ∀ z ∈ cruxV ∩ Om1, Ψu z = D z - k * uh z * Complex.log (z - 1) := by
    intro z hz
    have hz' : z ∈ (cruxU ∩ cruxV) ∪ (cruxL ∩ cruxV) := by
      rw [← cruxV_inter_Om1_eq]; exact hz
    rcases hz' with h | h
    · exact hform_u z h
    · rw [hΨul z h.2, hform_l z h]
  -- ## 6. assembly: glue the formula on `Om1` with the extension `Ψu` on `cruxV`
  classical
  set Efun : ℂ → ℂ :=
    fun z => if z ∈ Om1 then D z - k * uh z * Complex.log (z - 1) else Ψu z with hEfun
  refine ⟨Efun, ?_, ?_, ?_⟩
  · -- differentiability on `Om1 ∩ ball 1 (8/9)`
    intro z hz
    have hzOm : z ∈ Om1 := hz.1
    have hzW : z ∈ Metric.ball (1 : ℂ) (8 / 9) := hz.2
    have hnhds : (Om1 ∩ Metric.ball (1 : ℂ) (8 / 9)) ∈ 𝓝 z :=
      (isOpen_Om1.inter Metric.isOpen_ball).mem_nhds hz
    have hEq : Efun =ᶠ[𝓝 z] (fun w => D w - k * uh w * Complex.log (w - 1)) := by
      filter_upwards [hnhds] with w hw
      simp only [hEfun, if_pos hw.1]
    have hd : DifferentiableAt ℂ (fun w => D w - k * uh w * Complex.log (w - 1)) z :=
      (hD.differentiableAt (isOpen_Om1.mem_nhds hzOm)).sub
        (((differentiableAt_const k).mul
          (uh_ode.1.differentiableAt (Metric.isOpen_ball.mem_nhds hzW))).mul
          (differentiableOn_log_sub_one.differentiableAt (isOpen_Om1.mem_nhds hzOm)))
    exact (hd.congr_of_eventuallyEq hEq).differentiableWithinAt
  · -- differentiability at the real points of the interval `(1/9,1)`
    intro x hx
    have hxV : (x : ℂ) ∈ cruxV := ofReal_mem_cruxV hx
    have hnhds : cruxV ∈ 𝓝 (x : ℂ) := isOpen_cruxV.mem_nhds hxV
    have hEq : Efun =ᶠ[𝓝 (x : ℂ)] Ψu := by
      filter_upwards [hnhds] with z hzV
      by_cases hzOm : z ∈ Om1
      · simp only [hEfun, if_pos hzOm]
        exact (hΦ z ⟨hzV, hzOm⟩).symm
      · simp only [hEfun, if_neg hzOm]
    exact (hΨu_d.differentiableAt hnhds).congr_of_eventuallyEq hEq
  · -- the defining identity
    intro z hz
    have hzOm : z ∈ Om1 := hz.1
    have hz1 : Efun z = D z - k * uh z * Complex.log (z - 1) := by
      simp only [hEfun, if_pos hzOm]
    rw [hz1]; ring

end

end Work.A14D
