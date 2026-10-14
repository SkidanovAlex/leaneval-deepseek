import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllSol.PkgK6.vopTransferKSharp
import Submission.Work.FTS.StrongEps.Jeps_contDiffOn
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.ProducerH.pzIterTwo_shiftSing_eq_PhiTil_add
import Submission.Work.FTS_EllLimOK.RulingELF
import Submission.Work.FTS_RegExport.RXT.landau_1d
import Submission.Work.FTS_RegExport.RXVP3.vz0_of_vopLower
import Submission.Work.FTS_StreamBdry.SB6.UprimeAux.OdeFacts
import Submission.Work.FTS_StreamBdry.SB6.clauses3
import Submission.Work.FTS_StreamBdry.SBpsiP.SelfUprime
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Stability.mul_rpow_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH

set_option autoImplicit false

/-! ## Auxiliary `rpow` identity -/

/-- The square of the weighted `z = 1` normalisation is `16 · sin(2θ)^{-η}` on `Iθ`. -/
theorem wOne_div_sin_sq (θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.w 1 / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = 16 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hw1 : Work.Spaces.w 1 = 4 := by norm_num [Work.Spaces.w]
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  rcases eq_or_lt_of_le hs with h0 | hpos
  · rw [← h0, hw1]
    have heta2 : Work.Spaces.eta / 2 ≠ 0 := by
      have := Work.Spaces.eta_pos; intro h; linarith [show Work.Spaces.eta / 2 > 0 from by linarith]
    have h1 : (0 : ℝ) ^ (Work.Spaces.eta / 2) = 0 := Real.zero_rpow heta2
    have h2 : (0 : ℝ) ^ (-(Work.Spaces.eta)) = 0 :=
      Real.zero_rpow (by linarith [Work.Spaces.eta_pos])
    rw [h1, h2]
    norm_num
  · rw [hw1, div_pow]
    have hsq : (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
        = Real.sin (2 * θ) ^ Work.Spaces.eta := by
      rw [pow_two, ← Real.rpow_add hpos,
        show Work.Spaces.eta / 2 + Work.Spaces.eta / 2 = Work.Spaces.eta from by ring]
    rw [hsq, Real.rpow_neg hpos.le, div_eq_mul_inv]
    ring

/-- **The gauge mode is excluded.**  `Work.FTS_StreamBdry.SB1.sb1_gauge_of_parts` says that a `C³`
function with bounded `U`/`V` slots equals `psiP α Φ + κ * gaugeMode α` on the open quadrant, where
`gaugeMode α z θ = z^(-3/α)/cos θ` (the `Uop = Vop = bslOp = 0` mode, invisible to the packages).
Here `Φ = PhiTil α g (E g)`; we show `κ = 0` from `EllClassOk 8`, i.e. from
`HkMem α 8 (fun z θ => z^2 ∂_z² Ψ')` where `Ψ' = shiftSing α g (E g) = Φ + Gbar α g * sin 2θ`
(`EllWeakPos`'s field; the `i = 0` slot of the `ℋ⁸`-integrand gives, at every `z ∈ Iz`, the
integrability of `(z² ∂_z² Ψ')² · w(z)² · sin(2θ)^{-η}` on `Iθ`).
Proof of `κ = 0`: `z² ∂_z² Ψ' = z² ∂_z² psiP + κ * (3/α)(3/α+1) z^(-3/α)/cos θ + sin 2θ * z² (Gbar)''`
on the open quadrant; `|z² ∂_z² psiP| ≤ 2 M sin 2θ` (`SB3.psiP_DzLe`: `|D_z^j psiP| ≤ M sin2θ` for
`j ≤ 2`, and `z²∂_z² = D_z² - D_z`), and `|sin 2θ * z² (Gbar)''| ≤ B * sin 2θ` for an explicit `B`
(from `D_z Gbar = β Gbar - (3/(4α)) F_*(g)`, sup bounds on `F_*(g)`, `D_z F_*(g)` and `Gbar`).
So if `κ ≠ 0` the function `(z²∂_z²Ψ'(1,·))² sin(2θ)^{-η}` behaves like `cos θ^(-2-η)` near
`θ → π/2` with a positive coefficient and hence is not integrable on `Iθ` — contradiction. -/
theorem kappa_eq_zero {α Ce : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fn}
    (hg : Work.FTS.ClassC.ClassC α g) (hok : Work.FTS.EllExist.EllClassOk 8 α g (E g))
    (hK : Work.FTS.ClassC.EllPkgK α 6 Ce g (E g)) :
    ∀ (M κ : ℝ), Work.FTS.StreamBdryIface.SlotBd α (Work.Construction.PhiTil α g (E g)) M →
      (∀ z θ, (z, θ) ∈ Work.Construction.Qd →
        Work.Construction.PhiTil α g (E g) z θ
          = Work.FTS.StreamBdryIface.psiP α (Work.Construction.PhiTil α g (E g)) z θ
            + κ * Work.FTS.StreamBdryIface.gaugeMode α z θ) →
      κ = 0 := by
  intro M κ hslot hdec
  by_contra hκ
  -- ## Abbreviations
  set Φ : ℝ → ℝ → ℝ := Work.Construction.PhiTil α g (E g) with hΦdef
  set Ψ' : ℝ → ℝ → ℝ := Work.FTS.EllExist.shiftSing α g (E g) with hΨ'def
  -- ## 1. Smoothness
  have hΦsm : Work.FTS.EllipticEst.SmoothOpen Φ := by
    rw [hΦdef]; exact Work.FTS.ClassC.smoothOpen_phiTil_gen hα hg hok
  have hΨ'sm : Work.FTS.EllipticEst.SmoothOpen Ψ' := by
    rw [hΨ'def]
    exact Work.FTS.EllipticEst.smoothOpen_of_forall
      (Work.FTS.EllipticEst.TT.EllWeakPos.smooth hok.2.2)
  have hgauge : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StreamBdryIface.gaugeMode α) :=
    (Work.FTS_StreamBdry.SB25.contDiffOn_uncurry_gaugeMode α).of_le le_top
  have hPsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StreamBdryIface.psiP α Φ) := by
    refine Work.FTS.EllipticEst.SmoothOpen.congr (hΦsm.add (hgauge.const_mul' (-κ))) ?_
    intro z θ hz hθ0 hθ1
    have h := hdec z θ ⟨hz, hθ0, hθ1⟩
    rw [h]; ring
  -- ## 2. Smoothness of `Gbar`
  have hGbar : ContDiffOn ℝ 2 (Work.Elliptic.Gbar α g) (Set.Ioi 0) :=
    (Work.FTS.EllipticEst.Cert.Gbar_contDiffOn_Ioi α g hα hg.fsm
      (Work.FTS.EllipticEst.FstarDivOpen.fstar_div_integrable_of_smoothOpen α 7 g hg.reg
        hg.mem)) 2
  -- ## 3. Integrability of the `θ`-square from the `ℋ⁸`-slot
  have hmemA : Work.Spaces.HkMem α 8 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ' z θ) := by
    rw [hΨ'def]; exact Work.FTS.EllipticEst.TT.EllWeakPos.memA hok.2.2
  have hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.pzIter 2 Ψ' 1 θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ := by
    have hFsm : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ' z θ) :=
      Work.FTS.EllipticEst.SmoothOpen.zsq_mul (hΨ'sm.pzIter 2)
    have h0 := Work.FTS.EllipticEst.integrableOn_zSummand α 8 hFsm hmemA 0 (by omega)
      (show (1 : ℝ) ∈ Work.Spaces.Iz from by simp [Work.Spaces.Iz])
    refine MeasureTheory.IntegrableOn.congr_fun (h0.const_mul (1 / 16)) ?_ measurableSet_Icc
    · intro θ hθ
      change 1 / 16 * (Work.Spaces.DzIter 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ' z θ) 1 θ
            * (Work.Spaces.w 1 / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = (Work.Spaces.pzIter 2 Ψ' 1 θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      have h1 : Work.Spaces.DzIter 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ' z θ) 1 θ
          = Work.Spaces.pzIter 2 Ψ' 1 θ := by
        simp only [Work.Spaces.DzIter_zero]
        norm_num
      rw [h1]
      rw [show (Work.Spaces.pzIter 2 Ψ' 1 θ
            * (Work.Spaces.w 1 / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          = (Work.Spaces.pzIter 2 Ψ' 1 θ) ^ 2
            * (Work.Spaces.w 1 / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 from
        mul_pow _ _ 2]
      rw [wOne_div_sin_sq θ hθ]
      ring
  -- ## 4. Abbreviations for the angular variable
  set pz2 : ℝ → ℝ := fun θ => Work.Spaces.pzIter 2 Ψ' 1 θ with hpz2def
  set S : ℝ → ℝ := fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) with hSdef
  set J : Set ℝ := Set.Ioo (Real.pi / 4) (Real.pi / 2) with hJdef
  -- ## 5. The pointwise deviation bound
  have hdev : ∀ θ ∈ J,
      |pz2 θ - κ * ((3 / α) * (3 / α + 1) / Real.cos θ)|
        ≤ (|2 * M| + |deriv (fun z => deriv (Work.Elliptic.Gbar α g) z) 1|)
          * Real.sin (2 * θ) := by
    intro θ hθ
    have hθQ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have hsin : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_mem_Icc (x := 2 * θ)
        ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
    have hd1 : Work.Spaces.pzIter 2 Ψ' 1 θ
        = Work.Spaces.pzIter 2 Φ 1 θ
          + (deriv (fun z => deriv (Work.Elliptic.Gbar α g) z) 1) * Real.sin (2 * θ) := by
      rw [hΨ'def, hΦdef]
      exact pzIterTwo_shiftSing_eq_PhiTil_add (hΦ := hΦsm) hGbar hθQ
    have hd2 : Work.Spaces.pzIter 2 Φ 1 θ
        = Work.Spaces.pzIter 2 (Work.FTS.StreamBdryIface.psiP α Φ) 1 θ
          + κ * ((3 / α) * (3 / α + 1) / Real.cos θ) := by
      rw [hΦdef]
      exact pzIterTwo_PhiTil_eq_psiP_add (hΦ := hΦsm) (hP := hPsm) (hdec := hdec) hθQ
    have hd3 : |Work.Spaces.pzIter 2 (Work.FTS.StreamBdryIface.psiP α Φ) 1 θ|
        ≤ 2 * M * Real.sin (2 * θ) :=
      abs_pzIterTwo_psiP_le hα (h3 := hΦsm.forall 3) hslot hPsm hθQ
    have hkey : Work.Spaces.pzIter 2 (Work.FTS.StreamBdryIface.psiP α Φ) 1 θ
          + κ * ((3 / α) * (3 / α + 1) / Real.cos θ)
          + (deriv (fun z => deriv (Work.Elliptic.Gbar α g) z) 1) * Real.sin (2 * θ)
        - κ * ((3 / α) * (3 / α + 1) / Real.cos θ)
        = Work.Spaces.pzIter 2 (Work.FTS.StreamBdryIface.psiP α Φ) 1 θ
          + (deriv (fun z => deriv (Work.Elliptic.Gbar α g) z) 1) * Real.sin (2 * θ) := by
      ring
    have hZpz : pz2 θ = Work.Spaces.pzIter 2 Ψ' 1 θ := rfl
    rw [hZpz, hd1, hd2, hkey]
    calc |Work.Spaces.pzIter 2 (Work.FTS.StreamBdryIface.psiP α Φ) 1 θ
            + (deriv (fun z => deriv (Work.Elliptic.Gbar α g) z) 1) * Real.sin (2 * θ)|
        ≤ |Work.Spaces.pzIter 2 (Work.FTS.StreamBdryIface.psiP α Φ) 1 θ|
            + |(deriv (fun z => deriv (Work.Elliptic.Gbar α g) z) 1)
              * Real.sin (2 * θ)| := abs_add_le _ _
      _ = |Work.Spaces.pzIter 2 (Work.FTS.StreamBdryIface.psiP α Φ) 1 θ|
            + |deriv (fun z => deriv (Work.Elliptic.Gbar α g) z) 1| * Real.sin (2 * θ) := by
          rw [abs_mul, abs_of_nonneg hsin]
      _ ≤ 2 * M * Real.sin (2 * θ)
            + |deriv (fun z => deriv (Work.Elliptic.Gbar α g) z) 1| * Real.sin (2 * θ) := by
          linarith [hd3]
      _ ≤ (|2 * M| + |deriv (fun z => deriv (Work.Elliptic.Gbar α g) z) 1|)
            * Real.sin (2 * θ) := by
          have h2M : 2 * M ≤ |2 * M| := le_abs_self _
          nlinarith [mul_le_mul_of_nonneg_right h2M hsin]
  set C₀ : ℝ := |2 * M| + |deriv (fun z => deriv (Work.Elliptic.Gbar α g) z) 1| with hC₀def
  -- ## 6. Integrability of the bounded piece, and the dominating function
  have hJsub : J ⊆ Work.Spaces.Iθ := by
    intro θ hθ
    exact ⟨le_of_lt (lt_trans (by linarith [Real.pi_pos]) hθ.1), le_of_lt hθ.2⟩
  have hintJ : MeasureTheory.IntegrableOn (fun θ : ℝ => pz2 θ ^ 2 * S θ) J :=
    hint.mono_set hJsub
  have hsinint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta)) J := by
    have hcont : Continuous (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta)) :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).rpow_const
        (fun x => Or.inr (by linarith [Work.Spaces.eta_lt_one]))
    have h1 := hcont.intervalIntegrable (μ := volume) (Real.pi / 4) (Real.pi / 2)
    rwa [intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith [Real.pi_pos])] at h1
  have hdom : MeasureTheory.IntegrableOn
      (fun θ : ℝ => 2 * (pz2 θ ^ 2 * S θ)
        + 2 * C₀ ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta)) J :=
    (hintJ.const_mul 2).add (hsinint.const_mul (2 * C₀ ^ 2))
  -- ## 7. The pointwise domination
  have hpt : ∀ θ ∈ J, ‖(κ * ((3 / α) * (3 / α + 1) / Real.cos θ)) ^ 2 * S θ‖
      ≤ 2 * (pz2 θ ^ 2 * S θ) + 2 * C₀ ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta) := by
    intro θ hθ
    have hθQ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have hcos : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos],
        by linarith [hθ.2, Real.pi_pos]⟩
    have hsin : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos])
        (by linarith [hθ.2, Real.pi_pos])
    have hS : 0 < S θ := Real.rpow_pos_of_pos hsin _
    have hdevθ := hdev θ hθ
    set A : ℝ := κ * ((3 / α) * (3 / α + 1) / Real.cos θ) with hAdef
    set Z : ℝ := pz2 θ with hZdef
    have h1 : |A| ≤ |Z| + C₀ * Real.sin (2 * θ) := by
      have h := abs_add_le Z (-(Z - A))
      rw [abs_neg] at h
      have heq : Z + -(Z - A) = A := by ring
      rw [heq] at h
      exact h.trans (add_le_add_right hdevθ |Z|)
    have h2 : A ^ 2 ≤ 2 * Z ^ 2 + 2 * (C₀ * Real.sin (2 * θ)) ^ 2 := by
      have h3 : |A| ^ 2 ≤ (|Z| + C₀ * Real.sin (2 * θ)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
      have h4 : (|Z| + C₀ * Real.sin (2 * θ)) ^ 2
          ≤ 2 * Z ^ 2 + 2 * (C₀ * Real.sin (2 * θ)) ^ 2 := by
        nlinarith [sq_nonneg (|Z| - C₀ * Real.sin (2 * θ)), sq_abs Z]
      calc A ^ 2 = |A| ^ 2 := by rw [sq_abs]
        _ ≤ (|Z| + C₀ * Real.sin (2 * θ)) ^ 2 := h3
        _ ≤ 2 * Z ^ 2 + 2 * (C₀ * Real.sin (2 * θ)) ^ 2 := h4
    have hs2 : (Real.sin (2 * θ)) ^ 2 * S θ = (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta) := by
      have hpow : (Real.sin (2 * θ)) ^ (2 : ℝ) = (Real.sin (2 * θ)) ^ 2 :=
        Real.rpow_natCast _ 2
      have hmain : (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta)
          = (Real.sin (2 * θ)) ^ (2 : ℝ) * S θ := by
        rw [show (2 : ℝ) - Work.Spaces.eta = (2 : ℝ) + (-(Work.Spaces.eta)) from by ring,
          Real.rpow_add hsin]
      rw [hmain, hpow]
    show ‖A ^ 2 * S θ‖ ≤ 2 * (Z ^ 2 * S θ) + 2 * C₀ ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg A) hS.le)]
    have h5 : A ^ 2 * S θ ≤ (2 * Z ^ 2 + 2 * (C₀ * Real.sin (2 * θ)) ^ 2) * S θ :=
      mul_le_mul_of_nonneg_right h2 hS.le
    have h6 : (2 * Z ^ 2 + 2 * (C₀ * Real.sin (2 * θ)) ^ 2) * S θ
        = 2 * (Z ^ 2 * S θ) + 2 * C₀ ^ 2 * ((Real.sin (2 * θ)) ^ 2 * S θ) := by ring
    rw [h6] at h5
    rw [← hs2]
    exact h5
  -- ## 8. Conclusion: integrability of `cos θ^{-2} sin(2θ)^{-η}`, contradicted
  have hAint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (κ * ((3 / α) * (3 / α + 1) / Real.cos θ)) ^ 2 * S θ) J := by
    refine MeasureTheory.Integrable.mono' hdom ?_ ?_
    · have hcont : ContinuousOn
          (fun θ : ℝ => (κ * ((3 / α) * (3 / α + 1) / Real.cos θ)) ^ 2 * S θ) J := by
        refine ContinuousOn.mul ?_ ?_
        · refine ContinuousOn.pow ?_ 2
          refine ContinuousOn.mul
            (continuousOn_const : ContinuousOn (fun _ : ℝ => κ) J) ?_
          refine ContinuousOn.div
            (continuousOn_const : ContinuousOn (fun _ : ℝ => ((3 : ℝ) / α) * (3 / α + 1)) J)
            Real.continuous_cos.continuousOn ?_
          intro θ hθ
          exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos],
            by linarith [hθ.2, Real.pi_pos]⟩)
        · refine (Real.continuous_sin.comp
            (continuous_const.mul continuous_id)).continuousOn.rpow_const ?_
          intro θ hθ
          have h2θ : 0 < 2 * θ := by linarith [hθ.1, Real.pi_pos]
          have h2π : 2 * θ < Real.pi := by linarith [hθ.2, Real.pi_pos]
          exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h2θ h2π))
      exact hcont.aestronglyMeasurable measurableSet_Ioo
    · exact ae_restrict_of_forall_mem measurableSet_Ioo hpt
  have hfin : MeasureTheory.IntegrableOn (fun θ : ℝ => (Real.cos θ) ^ (-2 : ℝ) * S θ) J := by
    have hqne : ((3 : ℝ) / α) * (3 / α + 1) ≠ 0 := by
      have h3 : 0 < 3 / α := by positivity
      have h4 : 0 < 3 / α + 1 := by linarith
      exact ne_of_gt (mul_pos h3 h4)
    refine MeasureTheory.IntegrableOn.congr_fun
      (hAint.const_mul (1 / (κ ^ 2 * (((3 : ℝ) / α) * (3 / α + 1)) ^ 2))) ?_ measurableSet_Ioo
    intro θ hθ
    change 1 / (κ ^ 2 * ((3 / α) * (3 / α + 1)) ^ 2)
        * ((κ * ((3 / α) * (3 / α + 1) / Real.cos θ)) ^ 2 * S θ)
      = (Real.cos θ) ^ (-2 : ℝ) * S θ
    have hcos' : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo (x := θ)
      ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
    have hcos : Real.cos θ ≠ 0 := ne_of_gt hcos'
    have hcos2 : (Real.cos θ) ^ (-2 : ℝ) = ((Real.cos θ) ^ 2)⁻¹ := by
      have h2 : ((Real.cos θ) ^ 2 : ℝ) = (Real.cos θ) ^ (2 : ℝ) := (Real.rpow_ofNat _ 2).symm
      rw [h2, Real.rpow_neg hcos'.le]
    rw [hcos2]
    field_simp
  exact not_integrableOn_cos_sq_mul_sin_rpow (a := Real.pi / 4) (η := Work.Spaces.eta)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    (le_of_lt Work.Spaces.eta_pos) (by norm_num [Work.Spaces.eta]) hfin


end Work.FTS_EllLimOK.ProducerH
