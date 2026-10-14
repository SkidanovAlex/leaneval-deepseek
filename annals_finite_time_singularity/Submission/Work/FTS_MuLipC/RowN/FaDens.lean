import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenCoer.SlotWCommon
import Submission.Work.FTS.StrongPersist.H6Aux.R.DthIbp
import Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.T1Hon.EasyLeibIntBound
import Submission.Work.FTS.StrongPersist.N6Trans.T1Hon.HardSlotLemGen
import Submission.Work.FTS.TransportS.T2Sup.GenSlot
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKjet.L12
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.H2W.FstarDzIterFourPsiAe
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.N4C.T4Honest.T4HardSlot =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.N4C.T4Honest

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **The "hard" summand of the `D_θ`-transport slot pairing with a `D`-sup coefficient.**

This is `Work.FTS.StrongPersist.N6Trans.T1Hon.HardSlotLemGen` with the coefficient hypothesis
weakened from `HkMem α 4 f` to `WDMem 4 f`, and the constant `C/√(γ-1)·HkNorm α 4 f` replaced by
`C·WDp 4 f`.  Only the pointwise bounds `|f| ≤ WDp 4 f` and `|D_θf| ≤ WDp 4 f`
(`Work.FTS.OpenPkg.WDMem_of_WDp_le ... le_rfl 0 0` resp. `0 1`) are used in the proof of that
sibling, so the IBP core `Work.FTS.StrongPersist.N6Trans.HardSlotAux.IbpSliceBound` and the slot
integrability `Work.FTS.StrongPersist.N6Trans.T1Hon.SlotIntegrableGen` apply verbatim; take
`C := 3 / 2 + B / 2` from `IbpSliceBound`. -/
theorem T4HardSlot : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ) (q : ℝ),
    0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.VocabO.WDMem 4 f →
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
    Work.Spaces.DecayAll 4 g →
    ∀ (a b : ℕ), a + b ≤ 4 →
      (a = 0 → q = 0 ∨ q = Work.Spaces.eta) →
      (1 ≤ a → q = 0 ∨ q = Work.Spaces.eta ∨ q = Work.Spaces.gam α) →
    ∀ z ∈ Work.Spaces.Iz,
      |∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q) * f z θ
          * Work.Spaces.Dth (Work.Spaces.mixed b a g) z θ * Work.Spaces.mixed b a g z θ|
        ≤ C * Work.FTS.VocabO.WDp 4 f
            * ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) := by
  obtain ⟨B, hBpos, hB⟩ := Work.FTS.StrongPersist.N6Trans.HardSlotAux.IbpSliceBound
  refine ⟨3 / 2 + B / 2, by linarith, ?_⟩
  intro α f g q hα hα1 hfsm hfmem hgsm hgmem hgdec a b hab hq0 hqa z hz
  set Kf : ℝ := Work.FTS.VocabO.WDp 4 f with hKf
  have hKf0 : 0 ≤ Kf := by
    rw [hKf]
    exact Work.FTS.OpenPkg.WDp_nonneg 4 f
  -- the only two facts about `q` used below
  have hqabs : |1 - q| ≤ 1 := by
    rcases Nat.eq_zero_or_pos a with ha0 | hapos
    · rcases hq0 ha0 with h | h
      · rw [h]; norm_num
      · rw [h]; norm_num [Work.Spaces.eta]
    · rcases hqa hapos with h | h | h
      · rw [h]; norm_num
      · rw [h]; norm_num [Work.Spaces.eta]
      · rw [h]
        rw [Work.Spaces.gam]
        have h2 : (1 : ℝ) - (1 + α / 10) = -(α / 10) := by ring
        rw [h2, abs_neg, abs_of_nonneg (by linarith)]
        linarith
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · -- the degenerate slice `z = 0`: the radial weight vanishes, so both sides are `0`
    subst hz0
    have hw0 : Work.Spaces.w 0 = 0 := by norm_num [Work.Spaces.w]
    have h0 : (fun θ : ℝ => (Work.Spaces.w 0) ^ 2 * (Real.sin (2 * θ)) ^ (-q) * f 0 θ
        * Work.Spaces.Dth (Work.Spaces.mixed b a g) 0 θ * Work.Spaces.mixed b a g 0 θ)
        = fun _ => (0 : ℝ) := by
      funext θ
      rw [hw0]
      ring
    rw [h0, MeasureTheory.integral_zero, abs_zero, hw0]
    simp
  · -- the genuine slice `z > 0`: strip the (constant) radial factor `w(z)²`, reduce to the
    -- angular slices `F`, `V` and apply the integration-by-parts bound
    set F : ℝ → ℝ := fun θ => f z θ with hF
    set V : ℝ → ℝ := fun θ => Work.Spaces.mixed b a g z θ with hV
    have hF1 : ContDiffOn ℝ 1 F (Set.Ioo 0 (π / 2)) := by
      rw [hF]
      exact (hfsm.curry_θ hzpos).of_le (by simp [Work.Stability.smoothOrder])
    have hV1 : ContDiffOn ℝ 1 V (Set.Ioo 0 (π / 2)) := by
      rw [hV]
      exact ((hgsm.mixed b a).curry_θ hzpos).of_le
        (by simp [Work.Stability.smoothOrder])
    have hFb : ∀ θ ∈ Set.Ioo 0 (π / 2), |F θ| ≤ Kf := by
      intro θ hθ
      have h := Work.FTS.OpenPkg.WDMem_of_WDp_le hfmem le_rfl 0 0 (by norm_num)
        z θ hzpos hθ.1 hθ.2
      simpa only [hF, hKf, Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero,
        Work.Spaces.DzIter_zero] using h
    have hFd : ∀ θ ∈ Set.Ioo 0 (π / 2), |Real.sin (2 * θ) * deriv F θ| ≤ Kf := by
      intro θ hθ
      have h := Work.FTS.OpenPkg.WDMem_of_WDp_le hfmem le_rfl 0 1 (by norm_num)
        z θ hzpos hθ.1 hθ.2
      simpa only [hF, hKf, Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ,
        Work.Spaces.DthIter_zero, Work.Spaces.DzIter_zero, Work.Spaces.Dth,
        Work.Spaces.pth] using h
    have hint : MeasureTheory.IntegrableOn
        (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) Work.Spaces.Iθ := by
      have h := Work.FTS.StrongPersist.N6Trans.T1Hon.SlotIntegrableGen α g a b q hα hgsm
        hgmem hab hq0 hqa hzpos
      simpa only [hV] using h
    have hslice := hB q Kf F V hKf0 hqabs hF1 hV1 hFb hFd hint
    have hcongr : (fun θ : ℝ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q) * f z θ
          * Work.Spaces.Dth (Work.Spaces.mixed b a g) z θ * Work.Spaces.mixed b a g z θ)
        = fun θ : ℝ => (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-q) * F θ
            * (Real.sin (2 * θ) * deriv V θ) * V θ) := by
      funext θ
      simp only [hF, hV, Work.Spaces.Dth, Work.Spaces.pth]
      ring
    calc |∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q) * f z θ
          * Work.Spaces.Dth (Work.Spaces.mixed b a g) z θ * Work.Spaces.mixed b a g z θ|
        = (Work.Spaces.w z) ^ 2 * |∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q) * F θ
            * (Real.sin (2 * θ) * deriv V θ) * V θ| := by
          rw [hcongr, MeasureTheory.integral_const_mul, abs_mul,
            abs_of_nonneg (sq_nonneg (Work.Spaces.w z))]
      _ ≤ (Work.Spaces.w z) ^ 2 * ((3 / 2 + B / 2) * Kf
            * ∫ θ in Work.Spaces.Iθ, (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) :=
          mul_le_mul_of_nonneg_left hslice (sq_nonneg _)
      _ = (3 / 2 + B / 2) * Work.FTS.VocabO.WDp 4 f
            * ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
                (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) := by
          rw [hKf]; ring
      _ = (3 / 2 + B / 2) * Work.FTS.VocabO.WDp 4 f
            * ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) := by
          simp only [hV]

end Work.FTS.StrongEps.E4R3.N4C.T4Honest
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.OpenCoer.LGammaCoercive.LGamma_coercive_O =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.OpenCoer.LGammaCoercive

set_option maxHeartbeats 1600000

theorem LGamma_coercive_O {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : Work.FTS.Galerkin.Fn}
    (hf : Work.FTS.StrongEps.EpsE4Thr.RegQo α 2 f)
    (hIP : Work.FTS.StrongEps.EpsE4Thr.IntPkgO α f)
    (hHH : Work.Coercivity.HardyHyp f) (hΓ : Work.Coercivity.GammaL2Bnd α) :
    (1 / 4) * Work.Coercivity.Ef f
      ≤ Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
          (Work.Coercivity.LGamma α f) f := by
  have hs : Work.FTS.EllipticEst.SmoothOpen f := hf.1
  set P : Measure (ℝ × ℝ) := (volume.restrict Work.Spaces.Iz).prod
    (volume.restrict Work.Spaces.Iθ) with hP
  have hc : Work.Spaces.c α ≠ 0 := Work.Coercivity.c_ne_zero hα hα1
  -- ## integrability of the two halves of `𝓛_Γ`
  have hintL : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Coercivity.L f z θ * f z θ * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := hIP.intL_f_one
  have hF1 : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Work.Coercivity.L f p.1 p.2 * f p.1 p.2 * Work.Spaces.w p.1 ^ 2) P :=
    Work.Coercivity.integrableOn_prod hintL
  have hF4 : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (2 * p.1 * Work.Spaces.Gam α p.2 / (Work.Spaces.c α * (1 + p.1) ^ 2))
        * Work.Coercivity.L12f f p.1 * f p.1 p.2 * Work.Spaces.w p.1 ^ 2) P :=
    Work.Coercivity.integrableOn_prod
      (Work.FTS.StrongEps.EpsE4Thr.OpenCoer.intT1_w2_O α hα hα1 hIP hs hHH)
  -- ## the two halves of the `L₁₂`-term
  have hintK : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      2 * Work.Spaces.K θ * f z θ * (Work.Spaces.w z / z * Work.Coercivity.L12f f z)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    have h := Work.FTS.StrongEps.EpsE4Thr.OpenCoer.intK_O α hα hIP hs hHH
    rw [MeasureTheory.IntegrableOn] at h ⊢
    exact (h.const_mul 2).congr (Filter.Eventually.of_forall fun p => by
      rcases p with ⟨z, θ⟩
      simp only [Function.uncurry_apply_pair]
      ring)
  have hintG : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      2 * (Work.Spaces.Gam α θ / Work.Spaces.c α - Work.Spaces.K θ) * f z θ
        * Work.Spaces.w z * (Work.Coercivity.L12f f z / z)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    have h := Work.FTS.StrongEps.EpsE4Thr.OpenCoer.intG_O α hα hα1 hIP hs hHH
    rw [MeasureTheory.IntegrableOn] at h ⊢
    exact (h.const_mul 2).congr (Filter.Eventually.of_forall fun p => by
      rcases p with ⟨z, θ⟩
      simp only [Function.uncurry_apply_pair]
      ring)
  have hF5 : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      2 * Work.Spaces.K p.2 * f p.1 p.2 * (Work.Spaces.w p.1 / p.1
        * Work.Coercivity.L12f f p.1)) P :=
    Work.Coercivity.integrableOn_prod hintK
  have hF6 : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      2 * (Work.Spaces.Gam α p.2 / Work.Spaces.c α - Work.Spaces.K p.2) * f p.1 p.2
        * Work.Spaces.w p.1 * (Work.Coercivity.L12f f p.1 / p.1)) P :=
    Work.Coercivity.integrableOn_prod hintG
  -- ## integrability of `𝓛_Γ f · f w²`
  have hintLG : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Coercivity.LGamma α f z θ * f z θ * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    have h := hintL.sub
      (Work.FTS.StrongEps.EpsE4Thr.OpenCoer.intT1_w2_O α hα hα1 hIP hs hHH)
    rw [MeasureTheory.IntegrableOn] at h ⊢
    refine h.congr (Filter.Eventually.of_forall fun p => ?_)
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair, Pi.sub_apply, Work.Coercivity.LGamma]
    ring
  -- ## the `wip`s as product-measure integrals
  have hwipLG : Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
      (Work.Coercivity.LGamma α f) f
      = ∫ p, Work.Coercivity.LGamma α f p.1 p.2 * f p.1 p.2 * Work.Spaces.w p.1 ^ 2 ∂P := by
    rw [hP]
    exact Work.Coercivity.wip_eq_integral_prod (fun z _ => Work.Spaces.w z ^ 2)
      (Work.Coercivity.LGamma α f) f hintLG
  have hwipL : Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2) (Work.Coercivity.L f) f
      = ∫ p, Work.Coercivity.L f p.1 p.2 * f p.1 p.2 * Work.Spaces.w p.1 ^ 2 ∂P := by
    rw [hP]
    exact Work.Coercivity.wip_eq_integral_prod (fun z _ => Work.Spaces.w z ^ 2)
      (Work.Coercivity.L f) f hintL
  -- ## `𝓛_Γ = 𝓛 - (2zΓ/(c(1+z)²))L₁₂(f)`
  have hsplit : (∫ p, Work.Coercivity.LGamma α f p.1 p.2 * f p.1 p.2
        * Work.Spaces.w p.1 ^ 2 ∂P)
      = (∫ p, Work.Coercivity.L f p.1 p.2 * f p.1 p.2 * Work.Spaces.w p.1 ^ 2 ∂P)
        - (∫ p, (2 * p.1 * Work.Spaces.Gam α p.2
            / (Work.Spaces.c α * (1 + p.1) ^ 2)) * Work.Coercivity.L12f f p.1
            * f p.1 p.2 * Work.Spaces.w p.1 ^ 2 ∂P) := by
    rw [← MeasureTheory.integral_sub hF1 hF4]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [Work.Coercivity.LGamma]
    ring
  -- ## the paper's identity `(LW)`: `(𝓛 f, f)_{w²} = ½|f w|²`
  have hLhalf : (∫ p, Work.Coercivity.L f p.1 p.2 * f p.1 p.2 * Work.Spaces.w p.1 ^ 2 ∂P)
      = (1 / 2) * Work.Coercivity.Ef f := by
    rw [← hwipL]
    have h1 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
        f z θ ^ 2 * Work.Spaces.w z ^ 2 * (fun _ => (1 : ℝ)) θ))
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
      refine (hIP.sqDzOne 0 (by norm_num)).congr_fun ?_
        (measurableSet_Ici.prod measurableSet_Icc)
      rintro ⟨z, θ⟩ _
      simp only [Function.uncurry_apply_pair, Work.Spaces.DzIter_zero]
      ring
    have h2 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
        Work.Coercivity.L f z θ * f z θ * Work.Spaces.w z ^ 2 * (fun _ => (1 : ℝ)) θ))
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
      refine hintL.congr_fun ?_ (measurableSet_Ici.prod measurableSet_Icc)
      rintro ⟨z, θ⟩ _
      simp only [Function.uncurry_apply_pair]
      ring
    have h := Work.FTS.CoercivityFix.Coer1SO.wip_L_self_QO f hIP.zibp_f
      (fun _ => (1 : ℝ)) h1 h2
    have hw : (fun z θ : ℝ => Work.Spaces.w z ^ 2 * (1 : ℝ))
        = fun z _ => Work.Spaces.w z ^ 2 := by funext z θ; ring
    rw [hw] at h
    rw [h, Work.FTS.CoercivityFix.Coer1.wip_one_self,
      Work.FTS.CoercivityFix.Coer1.Ef_eq_EnOne]
  -- ## splitting `Γ/c = K + (Γ/c - K)`
  have hTsum : (∫ p, (2 * p.1 * Work.Spaces.Gam α p.2
          / (Work.Spaces.c α * (1 + p.1) ^ 2)) * Work.Coercivity.L12f f p.1
          * f p.1 p.2 * Work.Spaces.w p.1 ^ 2 ∂P)
      = (∫ p, 2 * Work.Spaces.K p.2 * f p.1 p.2
          * (Work.Spaces.w p.1 / p.1 * Work.Coercivity.L12f f p.1) ∂P)
        + (∫ p, 2 * (Work.Spaces.Gam α p.2 / Work.Spaces.c α - Work.Spaces.K p.2)
            * f p.1 p.2 * Work.Spaces.w p.1
            * (Work.Coercivity.L12f f p.1 / p.1) ∂P) := by
    rw [← MeasureTheory.integral_add hF5 hF6]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    show 2 * p.1 * Work.Spaces.Gam α p.2 / (Work.Spaces.c α * (1 + p.1) ^ 2)
        * Work.Coercivity.L12f f p.1 * f p.1 p.2 * Work.Spaces.w p.1 ^ 2
      = 2 * Work.Spaces.K p.2 * f p.1 p.2
          * (Work.Spaces.w p.1 / p.1 * Work.Coercivity.L12f f p.1)
        + 2 * (Work.Spaces.Gam α p.2 / Work.Spaces.c α - Work.Spaces.K p.2)
            * f p.1 p.2 * Work.Spaces.w p.1
            * (Work.Coercivity.L12f f p.1 / p.1)
    by_cases hz : p.1 = 0
    · rw [hz]; simp [Work.Spaces.w]
    · simp only [Work.Spaces.w]
      field_simp
      ring
  -- ## the two radial integrals of the paper
  set Y : ℝ := ∫ z in Set.Ioi (0 : ℝ),
    (1 + z) / z ^ 3 * (Work.Coercivity.L12f f z) ^ 2 with hY
  set Z : ℝ := ∫ z in Set.Ioi (0 : ℝ),
    (Work.Coercivity.L12f f z) ^ 2 / z ^ 2 with hZ
  have hEL : Work.Coercivity.EL12z f = Z := by
    rw [hZ]
    simp only [Work.Coercivity.EL12z, Work.Coercivity.L2Sqz, Work.Spaces.Iz]
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    exact div_pow (Work.Coercivity.L12f f z) z 2
  have hWK : (∫ p, 2 * Work.Spaces.K p.2 * f p.1 p.2
        * (Work.Spaces.w p.1 / p.1 * Work.Coercivity.L12f f p.1) ∂P) = -2 * Y := by
    rw [hP, hY]
    exact Work.Coercivity.wip_K_part_eq f hHH hintK
  have hBsq : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.Gam α θ / Work.Spaces.c α - Work.Spaces.K θ) ^ 2)
      Work.Spaces.Iθ := Work.Coercivity.integrableOn_GammaK_sq α hα hα1
  have hWG : (∫ p, 2 * (Work.Spaces.Gam α p.2 / Work.Spaces.c α - Work.Spaces.K p.2)
        * f p.1 p.2 * Work.Spaces.w p.1
        * (Work.Coercivity.L12f f p.1 / p.1) ∂P)
      ≤ (7 / 5) * Real.sqrt (Work.Coercivity.Ef f) * Real.sqrt Z := by
    have h := (abs_le.mp (Work.Coercivity.wip_G_bound α hα hα1 f hHH
      (Work.FTS.StrongEps.EpsE4Thr.OpenCoer.hfw2_open hIP) hΓ hBsq hintG)).2
    rw [hEL] at h
    exact h
  have hZY : Z ≤ Y := by
    rw [hZ, hY]
    refine MeasureTheory.integral_mono_ae ?_ (Work.Coercivity.L12_z_byparts_rhs_integrable f hHH) ?_
    · refine (hHH.intA 1 (by norm_num)).congr_fun ?_ measurableSet_Ioi
      intro z _
      norm_num
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      have hz0 : 0 < z := hz
      rw [← sub_nonneg]
      have hsub : (1 + z) / z ^ 3 * (Work.Coercivity.L12f f z) ^ 2
          - (Work.Coercivity.L12f f z) ^ 2 / z ^ 2
          = (Work.Coercivity.L12f f z) ^ 2 / z ^ 3 := by
        field_simp
        ring
      rw [hsub]
      positivity
  -- ## the numerical conclusion `½x² + 2y² - (7/5)xy ≥ ¼x²`
  have hEfnn : 0 ≤ Work.Coercivity.Ef f := by
    rw [Work.Coercivity.Ef, Work.Spaces.L2Sq]
    exact integral_nonneg fun z => integral_nonneg fun θ => sq_nonneg _
  have hZnn : 0 ≤ Z := by
    rw [hZ]
    exact integral_nonneg fun z => div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hnum : (1 / 2) * Work.Coercivity.Ef f + 2 * Z
      - (7 / 5) * Real.sqrt (Work.Coercivity.Ef f) * Real.sqrt Z
      ≥ (1 / 4) * Work.Coercivity.Ef f := by
    nlinarith [Real.sq_sqrt hEfnn, Real.sq_sqrt hZnn,
      sq_nonneg (Real.sqrt (Work.Coercivity.Ef f) - 14 / 5 * Real.sqrt Z),
      sq_nonneg (Real.sqrt Z)]
  calc Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2) (Work.Coercivity.LGamma α f) f
      = (1 / 2) * Work.Coercivity.Ef f
          - (∫ p, 2 * Work.Spaces.K p.2 * f p.1 p.2
              * (Work.Spaces.w p.1 / p.1 * Work.Coercivity.L12f f p.1) ∂P)
          - (∫ p, 2 * (Work.Spaces.Gam α p.2 / Work.Spaces.c α - Work.Spaces.K p.2)
              * f p.1 p.2 * Work.Spaces.w p.1
              * (Work.Coercivity.L12f f p.1 / p.1) ∂P) := by
        rw [hwipLG, hsplit, hLhalf, hTsum]; ring
    _ = (1 / 2) * Work.Coercivity.Ef f + 2 * Y
          - (∫ p, 2 * (Work.Spaces.Gam α p.2 / Work.Spaces.c α - Work.Spaces.K p.2)
              * f p.1 p.2 * Work.Spaces.w p.1
              * (Work.Coercivity.L12f f p.1 / p.1) ∂P) := by
        rw [hWK]; ring
    _ ≥ (1 / 2) * Work.Coercivity.Ef f + 2 * Z
          - (7 / 5) * Real.sqrt (Work.Coercivity.Ef f) * Real.sqrt Z := by
        linarith [hWG, hZY]
    _ ≥ (1 / 4) * Work.Coercivity.Ef f := hnum

end Work.FTS.StrongEps.EpsE4Thr.OpenCoer.LGammaCoercive
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Aux.R.SlotsBlocks =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Aux.R

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 3200000
/-! ## Weight facts and block bounds (continued) -/
theorem sq_dz_le_Hk (α : ℝ) {h : Fn} {k : ℕ} (i : ℕ) (hi : i ≤ k) :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (Work.Spaces.DzIter i h p.1 p.2) ^ 2 * Rhoq Work.Spaces.eta p.1 p.2
        ≤ Work.Spaces.HkIntegrand α k h p.1 p.2 := by
  filter_upwards [ae_angle_Ioo] with p hp
  obtain ⟨z, θ⟩ := p
  obtain ⟨h1, h2⟩ := hp
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hkey : (Work.Spaces.DzIter i h z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.DzIter i h z θ) ^ 2 * Rhoq Work.Spaces.eta z θ := by
    rw [mul_pow, div_half_sq _ _ _ hs]
    simp only [Rhoq, Work.FTS.CoercivityFix.Coer1.Rho,
      Work.FTS.CoercivityFix.Coer1.sig]
  rw [← hkey]
  exact Work.Spaces.sq_le_HkIntegrand_z α k h z θ i hi

/-- The `ℋ²`-summand attached to a mixed block, with the `γ`-weight. -/
theorem sq_mixed_le_Hk_gam (α : ℝ) (hα : 0 < α) {h : Fn} {k j i : ℕ} (hi : 1 ≤ i)
    (hij : i + j ≤ k) :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (Work.Spaces.mixed j i h p.1 p.2) ^ 2 * Rhoq (Work.Spaces.gam α) p.1 p.2
        ≤ Work.Spaces.HkIntegrand α k h p.1 p.2 := by
  filter_upwards [ae_angle_Ioo] with p hp
  obtain ⟨z, θ⟩ := p
  obtain ⟨h1, h2⟩ := hp
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hkey : (Work.Spaces.mixed j i h z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.mixed j i h z θ) ^ 2 * Rhoq (Work.Spaces.gam α) z θ := by
    have hW : Work.Spaces.Wt α z θ
        = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := rfl
    rw [hW, mul_pow, mul_half_sq _ _ _ hs]
    simp only [Rhoq, Work.FTS.CoercivityFix.Coer1.Rho, Work.FTS.CoercivityFix.Coer1.sig]
  rw [← hkey]
  exact Work.Spaces.sq_le_HkIntegrand_mixed α k h z θ i j hi hij

/-- The mixed block with the `η`-weight is dominated through the `γ`-weight. -/
theorem sq_mixed_le_Hk_eta (α : ℝ) (hα : 0 < α) {h : Fn} {k j i : ℕ} (hi : 1 ≤ i)
    (hij : i + j ≤ k) :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (Work.Spaces.mixed j i h p.1 p.2) ^ 2 * Rhoq Work.Spaces.eta p.1 p.2
        ≤ Work.Spaces.HkIntegrand α k h p.1 p.2 := by
  filter_upwards [sq_mixed_le_Hk_gam (k := k) α hα hi hij, Rhoq_eta_le_gam α hα] with p hp hle
  refine le_trans ?_ hp
  exact mul_le_mul_of_nonneg_left hle (sq_nonneg _)



/-- The commutator defect `Ê₂h` against the `η`-weight. -/
theorem sq_E2_le_Hk (α : ℝ) (hα : 0 < α) {h : Fn} {k : ℕ} (hk : 1 ≤ k) :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (Work.FTS.CoercivityFix.E2hat h p.1 p.2) ^ 2 * Rhoq Work.Spaces.eta p.1 p.2
        ≤ 2 * Work.Spaces.HkIntegrand α k h p.1 p.2 := by
  filter_upwards [sq_dz_le_Hk (h := h) (k := k) α 0 (by omega),
    sq_mixed_le_Hk_eta (h := h) (k := k) (j := 0) (i := 1) α hα (by norm_num) (by omega),
    ae_radius_pos, ae_snd_mem_Iθ] with p h0 h1 hzp hθ
  obtain ⟨z, θ⟩ := p
  have hz : 0 ≤ z := le_of_lt hzp
  have he : |Work.FTS.CoercivityFix.E2hat h z θ|
      ≤ (2 * |h z θ| + 3 * |Work.Spaces.Dth h z θ|) / 4 :=
    Work.FTS.CoercivityFix.E2hat_abs_le h hz
  have hX : 0 ≤ (2 * |h z θ| + 3 * |Work.Spaces.Dth h z θ|) / 4 := by positivity
  have hsq : (Work.FTS.CoercivityFix.E2hat h z θ) ^ 2
      ≤ ((2 * |h z θ| + 3 * |Work.Spaces.Dth h z θ|) / 4) ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg hX]
    exact he
  have hcs : ((2 * |h z θ| + 3 * |Work.Spaces.Dth h z θ|) / 4) ^ 2
      ≤ (13 / 16) * ((h z θ) ^ 2 + (Work.Spaces.Dth h z θ) ^ 2) := by
    have h1'' : (2 * |h z θ| + 3 * |Work.Spaces.Dth h z θ|) ^ 2
        ≤ 13 * (|h z θ| ^ 2 + |Work.Spaces.Dth h z θ| ^ 2) := by
      nlinarith [sq_nonneg (3 * |h z θ| - 2 * |Work.Spaces.Dth h z θ|)]
    have h1' : (2 * |h z θ| + 3 * |Work.Spaces.Dth h z θ|) ^ 2
        ≤ 13 * ((h z θ) ^ 2 + (Work.Spaces.Dth h z θ) ^ 2) := by
      simpa only [sq_abs] using h1''
    have h5 : ((2 * |h z θ| + 3 * |Work.Spaces.Dth h z θ|) / 4) ^ 2
        = (2 * |h z θ| + 3 * |Work.Spaces.Dth h z θ|) ^ 2 / 16 := by ring
    rw [h5]
    linarith [h1']
  have hrho : 0 ≤ Rhoq Work.Spaces.eta z θ :=
    Work.FTS.CoercivityFix.Coer1.Rho_nonneg Work.Spaces.eta z θ hθ
  have hDth : (Work.Spaces.Dth h z θ) ^ 2 * Rhoq Work.Spaces.eta z θ
      ≤ Work.Spaces.HkIntegrand α k h z θ := h1
  have hh : (h z θ) ^ 2 * Rhoq Work.Spaces.eta z θ
      ≤ Work.Spaces.HkIntegrand α k h z θ := h0
  have hnn : 0 ≤ Work.Spaces.HkIntegrand α k h z θ :=
    Work.Spaces.HkIntegrand_nonneg α k h z θ
  calc (Work.FTS.CoercivityFix.E2hat h z θ) ^ 2 * Rhoq Work.Spaces.eta z θ
      ≤ (13 / 16) * ((h z θ) ^ 2 + (Work.Spaces.Dth h z θ) ^ 2)
          * Rhoq Work.Spaces.eta z θ :=
        mul_le_mul_of_nonneg_right (le_trans hsq hcs) hrho
    _ = (13 / 16) * ((h z θ) ^ 2 * Rhoq Work.Spaces.eta z θ)
          + (13 / 16) * ((Work.Spaces.Dth h z θ) ^ 2 * Rhoq Work.Spaces.eta z θ) := by
        ring
    _ ≤ (13 / 16) * Work.Spaces.HkIntegrand α k h z θ
          + (13 / 16) * Work.Spaces.HkIntegrand α k h z θ := by
        linarith [hh, hDth]
    _ ≤ 2 * Work.Spaces.HkIntegrand α k h z θ := by linarith [hnn]

/-! ## Continuity of the blocks on the open quadrant -/

theorem continuousOn_w2_Q0 : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2) Q0 := by
  have hfun : (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
      = fun p : ℝ × ℝ => ((1 + p.1) ^ 2 / p.1 ^ 2) ^ 2 := by
    funext p; rfl
  rw [hfun]
  exact (ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2)
    (fun p hp => pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1))).pow 2

theorem continuousOn_sinpow_Q0 (q : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-q)) Q0 := by
  have hsinpos : ∀ p ∈ Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    rw [Work.FTS.EllipticEst.mem_Q0] at hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
      (by linarith [hp.2.2, Real.pi_pos])
  exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))

theorem continuousOn_Rhoq_Q0 (q : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Rhoq q p.1 p.2) Q0 := by
  have hfun : (fun p : ℝ × ℝ => Rhoq q p.1 p.2)
      = fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-q) := by
    funext p
    simp only [Rhoq, Work.FTS.CoercivityFix.Coer1.Rho, Work.FTS.CoercivityFix.Coer1.sig]
  rw [hfun]
  exact continuousOn_w2_Q0.mul (continuousOn_sinpow_Q0 q)

theorem continuousOn_zdiv_sq_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => p.1 / (1 + p.1) ^ 2) Q0 :=
  continuousOn_fst.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (fun p hp => pow_ne_zero 2 (by linarith [(Work.FTS.EllipticEst.mem_Q0.mp hp).1]))

theorem continuousOn_E2hat_Q0 {h : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen h) :
    ContinuousOn (Function.uncurry (Work.FTS.CoercivityFix.E2hat h)) Q0 := by
  have hfun : Function.uncurry (Work.FTS.CoercivityFix.E2hat h)
      = fun p : ℝ × ℝ => (p.1 / (1 + p.1) ^ 2)
          * (2 * h p.1 p.2 + 3 * Work.Spaces.Dth h p.1 p.2) := by
    funext p
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry_apply_pair]
    rw [Work.FTS.CoercivityFix.E2hat_eq]
    ring
  rw [hfun]
  exact continuousOn_zdiv_sq_Q0.mul
    ((hs.continuousOn.const_mul 2).add (hs.Dth.continuousOn.const_mul 3))

theorem continuousOn_Lhat_Q0 {h : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen h) :
    ContinuousOn (Function.uncurry (Work.FTS.CoercivityFix.Lhat h)) Q0 := by
  have hfun : Function.uncurry (Work.FTS.CoercivityFix.Lhat h)
      = fun p : ℝ × ℝ => h p.1 p.2 + Work.Spaces.Dz h p.1 p.2
          - 2 * h p.1 p.2 / (1 + p.1) - 3 * Work.Spaces.Dth h p.1 p.2 / (1 + p.1) := by
    funext p
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry_apply_pair]
    rw [Work.FTS.CoercivityFix.Lhat_eq]
    try ring
  rw [hfun]
  have h1 : ContinuousOn (fun p : ℝ × ℝ => 2 * h p.1 p.2 / (1 + p.1)) Q0 :=
    ((hs.continuousOn.const_mul 2).div (continuousOn_const.add continuousOn_fst)
      (fun p hp => by linarith [(Work.FTS.EllipticEst.mem_Q0.mp hp).1]))
  have h2 : ContinuousOn (fun p : ℝ × ℝ => 3 * Work.Spaces.Dth h p.1 p.2 / (1 + p.1)) Q0 :=
    ((hs.Dth.continuousOn.const_mul 3).div (continuousOn_const.add continuousOn_fst)
      (fun p hp => by linarith [(Work.FTS.EllipticEst.mem_Q0.mp hp).1]))
  exact ((hs.continuousOn.add hs.Dz.continuousOn).sub h1).sub h2

/-! ## Integrability of weighted squares and of products -/

/-- A weighted square a.e. dominated by a multiple of `HkIntegrand α 2 h` is integrable. -/
theorem integrable_sq_of_bound (α : ℝ) (k : ℕ) {h X ρ : Fn}
    (hs : Work.FTS.EllipticEst.SmoothOpen h) (hm : Work.Spaces.HkMem α k h) {C : ℝ}
    (hC : 0 ≤ C)
    (hXc : ContinuousOn (Function.uncurry X) Q0)
    (hρc : ContinuousOn (Function.uncurry ρ) Q0)
    (hρnn : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), 0 ≤ ρ p.1 p.2)
    (hb : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
        (X p.1 p.2) ^ 2 * ρ p.1 p.2 ≤ C * Work.Spaces.HkIntegrand α k h p.1 p.2) :
    MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => (X z θ) ^ 2 * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  refine integrableOfHkDom (C := C) α k hs hm ?_ ?_
  · convert (hXc.mul hXc).mul hρc using 1
    funext p
    simp only [Function.uncurry, Pi.mul_apply]
    try ring
  · filter_upwards [hb, hρnn] with p hp hnn
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hnn)]
    exact hp

/-- The product of two blocks whose weighted squares are a.e. dominated by `HkIntegrand` is
integrable. -/
theorem integrable_mul_of_sq (α : ℝ) (k : ℕ) {h u v ρ : Fn}
    (hs : Work.FTS.EllipticEst.SmoothOpen h) (hm : Work.Spaces.HkMem α k h) {Cu Cv : ℝ}
    (hCu : 0 ≤ Cu) (hCv : 0 ≤ Cv)
    (huc : ContinuousOn (Function.uncurry u) Q0)
    (hvc : ContinuousOn (Function.uncurry v) Q0)
    (hρc : ContinuousOn (Function.uncurry ρ) Q0)
    (hρnn : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), 0 ≤ ρ p.1 p.2)
    (hu : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
        (u p.1 p.2) ^ 2 * ρ p.1 p.2 ≤ Cu * Work.Spaces.HkIntegrand α k h p.1 p.2)
    (hv : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
        (v p.1 p.2) ^ 2 * ρ p.1 p.2 ≤ Cv * Work.Spaces.HkIntegrand α k h p.1 p.2) :
    MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => u z θ * v z θ * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  refine integrableOfHkDom (C := Cu + Cv) α k hs hm ?_ ?_
  · exact (huc.mul hvc).mul hρc
  · filter_upwards [hu, hv, hρnn] with p hup hvp hnn
    have h2 : 2 * (|u p.1 p.2 * v p.1 p.2| * ρ p.1 p.2)
        ≤ (u p.1 p.2) ^ 2 * ρ p.1 p.2 + (v p.1 p.2) ^ 2 * ρ p.1 p.2 := by
      have := Work.FTS.CoercivityFix.Coer1.two_abs_mul_le (u p.1 p.2) (v p.1 p.2) (ρ p.1 p.2) hnn
      linarith [this]
    have h3 : |u p.1 p.2 * v p.1 p.2 * ρ p.1 p.2| ≤ (Cu + Cv) * Work.Spaces.HkIntegrand α k h p.1 p.2 := by
      rw [abs_mul, abs_of_nonneg hnn]
      nlinarith [h2, hup, hvp]
    simpa using h3

/-- `Rhoq 0 = w²`: the `q = 0` weight is the plain radial square. -/
theorem Rhoq_zero : Rhoq 0 = fun z _ => (Work.Spaces.w z) ^ 2 := by
  funext z θ
  simp only [Rhoq, Work.FTS.CoercivityFix.Coer1.Rho, Work.FTS.CoercivityFix.Coer1.sig,
    neg_zero, Real.rpow_zero, mul_one]

/-- A.e. `D_θ D_z h = mixed 1 1 h` on the open quadrant. -/
theorem ae_DthDz {h : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen h) :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      Work.Spaces.Dth (Work.Spaces.Dz h) p.1 p.2
        = Work.Spaces.mixed 1 1 h p.1 p.2 := by
  filter_upwards [ae_angle_Ioo, ae_radius_pos] with p hθ hz
  obtain ⟨z, θ⟩ := p
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := by
    rw [Work.FTS.EllipticEst.mem_Q0]; exact ⟨hz, hθ.1, hθ.2⟩
  have hcd : ContDiffAt ℝ 2 (Function.uncurry h) (z, θ) :=
    (hs.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)).of_le
      (by simp [Work.Stability.smoothOrder])
  exact (Work.Spaces.Dz_Dth_comm hcd).symm

/-- The mixed block `D_θ D_z h` against the `η`-weight. -/
theorem sq_DthDz_le_Hk (α : ℝ) (hα : 0 < α) {h : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen h)
    {k : ℕ} (hk : 2 ≤ k) :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (Work.Spaces.Dth (Work.Spaces.Dz h) p.1 p.2) ^ 2 * Rhoq Work.Spaces.eta p.1 p.2
        ≤ Work.Spaces.HkIntegrand α k h p.1 p.2 := by
  filter_upwards [sq_mixed_le_Hk_eta (h := h) (k := k) (j := 1) (i := 1) α hα
    (by norm_num) (by omega), ae_DthDz hs] with p hp hc
  rw [hc]; exact hp

/-! ## The `Lhat`-blocks -/

/-- Four-term AM–GM: `(a+b+c+d)² ≤ 4(a²+b²+c²+d²)`. -/
theorem four_sq_le (a b c d : ℝ) : (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c),
    sq_nonneg (b - d), sq_nonneg (c - d)]

/-- `(c·a)² ≤ C²·a²` when `0 ≤ C` and `|c| ≤ C`. -/
theorem sq_mul_le_abs {c a C : ℝ} (hC : 0 ≤ C) (h : |c| ≤ C) :
    (c * a) ^ 2 ≤ C ^ 2 * a ^ 2 := by
  have h1 : c ^ 2 ≤ C ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg hC]
    exact h
  nlinarith [h1, sq_nonneg a]

theorem abs_two_div_le {z : ℝ} (hz : 0 ≤ z) : |2 / (1 + z)| ≤ 2 := by
  rw [abs_of_nonneg (by positivity), div_le_iff₀ (by linarith : (0:ℝ) < 1 + z)]
  linarith

theorem abs_three_div_le {z : ℝ} (hz : 0 ≤ z) : |3 / (1 + z)| ≤ 3 := by
  rw [abs_of_nonneg (by positivity), div_le_iff₀ (by linarith : (0:ℝ) < 1 + z)]
  linarith


/-- `(Lhat (D_z h))²` against the `η`-weight. -/
theorem sq_LhatDz_le_Hk (α : ℝ) (hα : 0 < α) {h : Fn}
    (hs : Work.FTS.EllipticEst.SmoothOpen h) {k : ℕ} (hk : 2 ≤ k) :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz h) p.1 p.2) ^ 2
          * Rhoq Work.Spaces.eta p.1 p.2
        ≤ 60 * Work.Spaces.HkIntegrand α k h p.1 p.2 := by
  filter_upwards [sq_dz_le_Hk (h := h) (k := k) α 1 (by omega),
    sq_dz_le_Hk (h := h) (k := k) α 2 (by omega),
    sq_DthDz_le_Hk (h := h) (k := k) α hα hs hk,
    ae_radius_pos, ae_snd_mem_Iθ] with p h0 h1 h2 hzp hθ
  obtain ⟨z, θ⟩ := p
  dsimp only at h0 h1 h2 hzp hθ ⊢
  have hz : 0 ≤ z := le_of_lt hzp
  have hc1 : |-(2 / (1 + z))| ≤ 2 := by
    rw [abs_neg]; exact abs_two_div_le hz
  have hc2 : |-(3 / (1 + z))| ≤ 3 := by
    rw [abs_neg]; exact abs_three_div_le hz
  have hpt : (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz h) z θ) ^ 2
      ≤ 4 * (5 * (Work.Spaces.Dz h z θ) ^ 2 + (Work.Spaces.DzIter 2 h z θ) ^ 2
          + 9 * (Work.Spaces.Dth (Work.Spaces.Dz h) z θ) ^ 2) := by
    have hL := Work.FTS.CoercivityFix.Lhat_eq (Work.Spaces.Dz h) z θ
    have h4 := four_sq_le (Work.Spaces.Dz h z θ) (Work.Spaces.DzIter 2 h z θ)
      (-(2 / (1 + z)) * Work.Spaces.Dz h z θ)
      (-(3 / (1 + z)) * Work.Spaces.Dth (Work.Spaces.Dz h) z θ)
    have h5 := sq_mul_le_abs (C := 2) (by norm_num) hc1 (a := Work.Spaces.Dz h z θ)
    have h6 := sq_mul_le_abs (C := 3) (by norm_num) hc2
      (a := Work.Spaces.Dth (Work.Spaces.Dz h) z θ)
    rw [hL]
    have hL2 : Work.Spaces.Dz h z θ + Work.Spaces.Dz (Work.Spaces.Dz h) z θ
          - 2 * Work.Spaces.Dz h z θ / (1 + z)
          - 3 * Work.Spaces.Dth (Work.Spaces.Dz h) z θ / (1 + z)
        = Work.Spaces.Dz h z θ + Work.Spaces.DzIter 2 h z θ
          + -(2 / (1 + z)) * Work.Spaces.Dz h z θ
          + -(3 / (1 + z)) * Work.Spaces.Dth (Work.Spaces.Dz h) z θ := by
      rw [show Work.Spaces.Dz (Work.Spaces.Dz h) = Work.Spaces.DzIter 2 h from rfl]
      ring
    rw [hL2]
    nlinarith [h4, h5, h6]
  have hrho : 0 ≤ Rhoq Work.Spaces.eta z θ :=
    Work.FTS.CoercivityFix.Coer1.Rho_nonneg Work.Spaces.eta z θ hθ
  have hnn : 0 ≤ Work.Spaces.HkIntegrand α k h z θ :=
    Work.Spaces.HkIntegrand_nonneg α k h z θ
  have h0' : (Work.Spaces.Dz h z θ) ^ 2 * Rhoq Work.Spaces.eta z θ
      ≤ Work.Spaces.HkIntegrand α k h z θ := h0
  have h1' : (Work.Spaces.DzIter 2 h z θ) ^ 2 * Rhoq Work.Spaces.eta z θ
      ≤ Work.Spaces.HkIntegrand α k h z θ := h1
  have h2' : (Work.Spaces.Dth (Work.Spaces.Dz h) z θ) ^ 2 * Rhoq Work.Spaces.eta z θ
      ≤ Work.Spaces.HkIntegrand α k h z θ := h2
  calc (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz h) z θ) ^ 2
        * Rhoq Work.Spaces.eta z θ
      ≤ (4 * (5 * (Work.Spaces.Dz h z θ) ^ 2 + (Work.Spaces.DzIter 2 h z θ) ^ 2
          + 9 * (Work.Spaces.Dth (Work.Spaces.Dz h) z θ) ^ 2))
          * Rhoq Work.Spaces.eta z θ :=
        mul_le_mul_of_nonneg_right hpt hrho
    _ = 20 * ((Work.Spaces.Dz h z θ) ^ 2 * Rhoq Work.Spaces.eta z θ)
          + 4 * ((Work.Spaces.DzIter 2 h z θ) ^ 2 * Rhoq Work.Spaces.eta z θ)
          + 36 * ((Work.Spaces.Dth (Work.Spaces.Dz h) z θ) ^ 2
              * Rhoq Work.Spaces.eta z θ) := by ring
    _ ≤ 60 * Work.Spaces.HkIntegrand α k h z θ := by linarith [h0', h1', h2', hnn]


/-- The angular derivative `D_θ g` is continuous on the open quadrant for smooth `g`. -/
theorem continuousOn_Dth_Q0 {g : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen g) :
    ContinuousOn (Function.uncurry (Work.Spaces.Dth g)) Q0 := by
  have h : ContinuousOn (Function.uncurry (fun z θ =>
      Real.sin (2 * θ) * Work.Spaces.pth g z θ)) Q0 :=
    (((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).mul
      (hs.pth).continuousOn)
  convert h using 1
  funext p
  rfl

end Work.FTS.StrongPersist.H6Aux.R
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.T1Hon.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.T1Hon

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## Elementary facts -/

/-- Almost every point of `Iz = [0,∞)` is positive. -/
theorem ae_Iz_pos : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz), 0 < z := by
  rw [MeasureTheory.ae_iff]
  have hset : {z : ℝ | ¬ (0 < z)} = Set.Iic (0 : ℝ) := by
    ext z; simp only [Set.mem_ofPred_eq, not_lt, Set.mem_Iic]
  rw [hset, MeasureTheory.Measure.restrict_apply measurableSet_Iic]
  have h : Set.Iic (0 : ℝ) ∩ Work.Spaces.Iz = {0} := by
    ext x
    simp only [Work.Spaces.Iz, Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ici,
      Set.mem_singleton_iff]
    constructor
    · intro h; exact le_antisymm h.1 h.2
    · intro h; simp [h]
  rw [h, MeasureTheory.measure_singleton]

/-- Almost every point of `Iθ = [0,π/2]` lies in the open interval `(0,π/2)`. -/
theorem ae_Iθ_mem_Ioo :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (π / 2) :=
  Work.FTS.StrongPersist.N6Trans.HardSlotAux.ae_restrict_Iθ_of_forall_mem_Ioo
    (p := fun θ => θ ∈ Set.Ioo (0 : ℝ) (π / 2)) (fun _ hθ => hθ)

/-- `w²σ^{-q}` is nonnegative on the closed angular interval. -/
theorem weight_nonneg_of_Iθ (q : ℝ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q) :=
  mul_nonneg (sq_nonneg _) (Real.rpow_nonneg
    (Work.Spaces.sin_two_nonneg_of_Iθ hθ) _)

/-- **The weight `w²σ^{-q}` of an admissible leaf is dominated by the slot weight `slotW α a`**
on the open quadrant. -/
theorem weight_le_slotW {α q : ℝ} (hα : 0 < α) {a : ℕ}
    (hq0 : a = 0 → q = 0 ∨ q = Work.Spaces.eta)
    (hqa : 1 ≤ a → q = 0 ∨ q = Work.Spaces.eta ∨ q = Work.Spaces.gam α)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
      ≤ Work.FTS.TransportS.slotW α a z θ := by
  have hσ0 : 0 < Real.sin (2 * θ) := Work.FTS.H2.sin_two_pos_Qd hθ
  have hgam0 : 0 ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  rcases eq_or_ne a 0 with ha | ha
  · subst ha
    rw [Work.FTS.TransportS.slotW_zero]
    beta_reduce
    rw [Work.FTS.H2.Whz_sq z θ hσ0.le]
    rcases hq0 rfl with hq | hq
    · subst hq
      simpa only [neg_zero, Real.rpow_zero, mul_one] using
        mul_le_mul_of_nonneg_left
          (Work.FTS.TransportS.one_le_rpow_neg Work.Spaces.eta_nonneg hθ)
          (sq_nonneg (Work.Spaces.w z))
    · subst hq
      exact le_rfl
  · have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha
    rw [Work.FTS.TransportS.slotW_of_pos' α ha1]
    beta_reduce
    rw [Work.FTS.H2.Wm_sq α hα z θ hσ0.le]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    rcases hqa ha1 with hq | hq | hq
    · subst hq
      rw [neg_zero, Real.rpow_zero]
      exact Work.FTS.TransportS.one_le_rpow_neg hgam0 hθ
    · subst hq
      exact Work.FTS.StrongPersist.N6Trans.HardSlotAux.rpow_sin_two_neg_le
        (le_trans (le_of_lt Work.Spaces.eta_lt_one) (le_of_lt (Work.Spaces.one_lt_gam hα))) hθ
    · subst hq
      exact le_rfl

/-- A split identity: the (double) sum over `range (a+1) × range (b+1)` is its `(0,0)` term plus
the sum with the `(0,0)` term deleted. -/
theorem sum_split_zero {M : Type*} [AddCommMonoid M] (a b : ℕ) (F : ℕ → ℕ → M) :
    (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1), F a1 b1)
      = F 0 0 + ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
          (if a1 = 0 ∧ b1 = 0 then 0 else F a1 b1) := by
  have h0a : (0 : ℕ) ∈ Finset.range (a + 1) := Finset.mem_range.mpr (by omega)
  have h0b : (0 : ℕ) ∈ Finset.range (b + 1) := Finset.mem_range.mpr (by omega)
  have key : (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
      (if a1 = 0 ∧ b1 = 0 then F a1 b1 else 0)) = F 0 0 := by
    rw [Finset.sum_eq_single 0]
    · rw [Finset.sum_eq_single 0]
      · rw [if_pos ⟨rfl, rfl⟩]
      · intro b1 hb1 hne; rw [if_neg (fun h => hne h.2)]
      · intro h; exact absurd h0b h
    · intro a1 ha1 hne
      refine Finset.sum_eq_zero fun b1 _ => ?_
      rw [if_neg (fun h => hne h.1)]
    · intro h; exact absurd h0a h
  have hpt : ∀ a1 b1, F a1 b1
      = (if a1 = 0 ∧ b1 = 0 then F a1 b1 else 0)
        + (if a1 = 0 ∧ b1 = 0 then 0 else F a1 b1) := by
    intro a1 b1; by_cases h : a1 = 0 ∧ b1 = 0 <;> simp [h]
  calc (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1), F a1 b1)
      = ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
          ((if a1 = 0 ∧ b1 = 0 then F a1 b1 else 0)
            + (if a1 = 0 ∧ b1 = 0 then 0 else F a1 b1)) :=
        Finset.sum_congr rfl fun a1 _ =>
          Finset.sum_congr rfl fun b1 _ => (hpt a1 b1)
    _ = (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
            (if a1 = 0 ∧ b1 = 0 then F a1 b1 else 0))
          + (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
            (if a1 = 0 ∧ b1 = 0 then 0 else F a1 b1)) := by
        simp only [Finset.sum_add_distrib]
    _ = F 0 0 + ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
            (if a1 = 0 ∧ b1 = 0 then 0 else F a1 b1) := by rw [key]

end

end Work.FTS.StrongPersist.N6Trans.T1Hon
end
-- ===== merged: Submission.Work.FTS_MuLipC.RowN.FaDens =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS_MuLipC.RowN

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The density `L₁₂dens` is integrable when `Fa` is finite

`L₁₂dens f s = ∫_θ K(θ)·f(s,θ)/s dθ = s⁻¹ ∫_θ K(θ)·f(s,θ) dθ` for `s > 0`, hence

  `ofReal |L₁₂dens f s| ≤ ofReal s⁻¹ · ∫⁻_θ ofReal |K(θ)·f(s,θ)|`   (`s > 0`),

by `ofReal |∫| ≤ ∫⁻ ofReal |·|` (`norm_integral_le_lintegral_norm`) followed by pulling the
constant `s⁻¹` out of the lintegral.  Integrating this over `(0,∞)` in `s` gives exactly
`∫⁻_{s>0} ofReal |L₁₂dens f s| ≤ Fa f`, and `Fa f < ⊤` therefore yields
`HasFiniteIntegral (L₁₂dens f) (volume.restrict (Ioi 0))`.  Together with the assumed
a.e. strong measurability this is `IntegrableOn (L₁₂dens f) (Ioi 0)`. -/

/-- For a real-valued function on a measure space,
`ofReal |∫ x in s, h x| ≤ ∫⁻ x in s, ofReal |h x|` (no measurability needed: the
`lintegral` of the pointwise norm always dominates the norm of the Bochner integral). -/
private theorem ofReal_abs_integral_le (h : ℝ → ℝ) (μ : Measure ℝ) (s : Set ℝ) :
    ENNReal.ofReal |∫ x in s, h x ∂μ| ≤ ∫⁻ x in s, ENNReal.ofReal |h x| ∂μ := by
  have h3 := MeasureTheory.norm_integral_le_lintegral_norm h (μ := μ.restrict s)
  rw [Real.norm_eq_abs] at h3
  exact le_trans (ENNReal.ofReal_le_ofReal h3) ENNReal.ofReal_toReal_le

/-- The pointwise domination of the `L₁₂`-density by the `Fa`-integrand:
`ofReal |L₁₂dens f s| ≤ ofReal s⁻¹ · ∫⁻_θ ofReal |K(θ)·f(s,θ)|` for `s > 0`. -/
private theorem ofReal_abs_L12dens_le {f : ℝ → ℝ → ℝ} {s : ℝ} (hs : 0 < s) :
    ENNReal.ofReal |Work.Construction.L12dens f s|
      ≤ ENNReal.ofReal s⁻¹
        * ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * f s θ| := by
  -- the density is the integral of `K θ · f s θ / s`, so `ofReal |·| ≤ ∫⁻ ofReal |·|`
  have h1 : ENNReal.ofReal |Work.Construction.L12dens f s|
      ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * f s θ / s| := by
    rw [Work.Construction.L12dens, Work.FM.L12dens, Work.Spaces.Iθ]
    exact ofReal_abs_integral_le _ _ _
  -- the integrand factorises as `s⁻¹ · (K θ · f s θ)` for `s > 0`
  have hpt : (fun θ : ℝ => ENNReal.ofReal |Work.Spaces.K θ * f s θ / s|)
      = fun θ : ℝ => ENNReal.ofReal s⁻¹
          * ENNReal.ofReal |Work.Spaces.K θ * f s θ| := by
    funext θ
    have hdiv : Work.Spaces.K θ * f s θ / s = s⁻¹ * (Work.Spaces.K θ * f s θ) := by
      rw [div_eq_inv_mul]
    rw [hdiv, abs_mul, abs_of_pos (inv_pos.mpr hs),
      ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hs))]
  rw [hpt, MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h1
  exact h1

theorem FaDens {f : ℝ → ℝ → ℝ}
    (haesm : MeasureTheory.AEStronglyMeasurable (Work.Construction.L12dens f)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hfa : Work.FTS.Nonlinear.Pieces.Fa f < ⊤) :
    MeasureTheory.IntegrableOn (Work.Construction.L12dens f) (Set.Ioi (0 : ℝ)) := by
  have hfin : MeasureTheory.HasFiniteIntegral (Work.Construction.L12dens f)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    rw [MeasureTheory.hasFiniteIntegral_iff_norm]
    refine lt_of_le_of_lt ?_ hfa
    rw [Work.FTS.Nonlinear.Pieces.Fa]
    refine MeasureTheory.lintegral_mono_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
    rw [Real.norm_eq_abs]
    exact ofReal_abs_L12dens_le hs
  exact ⟨haesm, hfin⟩

end Work.FTS_MuLipC.RowN
end
end
