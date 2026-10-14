import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.ClassCHon.CmodeDefs
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceDefs
import Submission.Work.FTS.H2.ModalSol.Defs
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.H2.Transport1Aux
import Submission.Work.FTS_RegExport.RXT.contDiffOn_two_integral_Itheta
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.SolutionDelivery.Scaling.vorticityDecay_rescaleDatum
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.EllipticEst.Core.i0Aux.interpS_theta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllipticEst

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary facts about vanishing on the complement of the radial box -/

/-- A function vanishing on an open set has vanishing `∂_θ`. -/
lemma pth_eq_zero_of_eq_zero_on_open {F : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ∀ z θ : ℝ, (z, θ) ∈ V → F z θ = 0) :
    ∀ z θ : ℝ, (z, θ) ∈ V → Work.Spaces.pth F z θ = 0 := by
  intro z θ hzθ
  have hnb : ∀ᶠ θ' in 𝓝 θ, (z, θ') ∈ V :=
    (continuous_const.prodMk continuous_id).continuousAt (hV.mem_nhds hzθ)
  have hev : (fun θ' : ℝ => F z θ') =ᶠ[𝓝 θ] (fun _ => (0 : ℝ)) := by
    filter_upwards [hnb] with θ' hθ'
    exact h z θ' hθ'
  show deriv (fun θ' : ℝ => F z θ') θ = 0
  rw [hev.deriv_eq, deriv_const]

/-- A function vanishing on an open set has vanishing `∂_z`. -/
lemma pz_eq_zero_of_eq_zero_on_open {F : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ∀ z θ : ℝ, (z, θ) ∈ V → F z θ = 0) :
    ∀ z θ : ℝ, (z, θ) ∈ V → Work.Spaces.pz F z θ = 0 := by
  intro z θ hzθ
  have hnb : ∀ᶠ z' in 𝓝 z, (z', θ) ∈ V :=
    (continuous_id.prodMk continuous_const).continuousAt (hV.mem_nhds hzθ)
  have hev : (fun z' : ℝ => F z' θ) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [hnb] with z' hz'
    exact h z' θ hz'
  show deriv (fun z' : ℝ => F z' θ) z = 0
  rw [hev.deriv_eq, deriv_const]

/-- The vanishing set `{z ∉ [a,b]}` of the radial box hypothesis is open. -/
lemma isOpen_compl_Icc_fst {a b : ℝ} : IsOpen {p : ℝ × ℝ | p.1 ∉ Set.Icc a b} :=
  isClosed_Icc.isOpen_compl.preimage continuous_fst

/-- All the derivatives occurring in the estimate vanish off the radial box. -/
lemma vanish_all_off_box {F : ℝ → ℝ → ℝ} {a b : ℝ}
    (hsupp : ∀ z : ℝ, z ∉ Set.Icc a b → ∀ θ : ℝ, F z θ = 0) :
    (∀ z θ : ℝ, z ∉ Set.Icc a b → Work.Spaces.pz F z θ = 0) ∧
    (∀ z θ : ℝ, z ∉ Set.Icc a b → Work.Spaces.pth F z θ = 0) ∧
    (∀ z θ : ℝ, z ∉ Set.Icc a b → Work.Spaces.Dz F z θ = 0) ∧
    (∀ z θ : ℝ, z ∉ Set.Icc a b → Work.Spaces.pth (Work.Spaces.pth F) z θ = 0) ∧
    (∀ z θ : ℝ, z ∉ Set.Icc a b → Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth F)) z θ = 0) ∧
    (∀ z θ : ℝ, z ∉ Set.Icc a b → Work.Spaces.Dz (Work.Spaces.Dz F) z θ = 0) := by
  have hV := isOpen_compl_Icc_fst (a := a) (b := b)
  have hmem : ∀ z θ : ℝ, z ∉ Set.Icc a b → (z, θ) ∈ {p : ℝ × ℝ | p.1 ∉ Set.Icc a b} :=
    fun z θ hz => hz
  have h0 : ∀ z θ : ℝ, (z, θ) ∈ {p : ℝ × ℝ | p.1 ∉ Set.Icc a b} → F z θ = 0 :=
    fun z θ hz => hsupp z hz θ
  have hpz := pz_eq_zero_of_eq_zero_on_open hV h0
  have hpth := pth_eq_zero_of_eq_zero_on_open hV h0
  have hDz : ∀ z θ : ℝ, z ∉ Set.Icc a b → Work.Spaces.Dz F z θ = 0 := by
    intro z θ hz
    show z * Work.Spaces.pz F z θ = 0
    rw [hpz z θ (hmem z θ hz), mul_zero]
  have h2 : ∀ z θ : ℝ, (z, θ) ∈ {p : ℝ × ℝ | p.1 ∉ Set.Icc a b} →
      Work.Spaces.pth F z θ = 0 := hpth
  have hpth2 : ∀ z θ : ℝ, z ∉ Set.Icc a b →
      Work.Spaces.pth (Work.Spaces.pth F) z θ = 0 := by
    intro z θ hz
    exact pth_eq_zero_of_eq_zero_on_open hV h2 z θ (hmem z θ hz)
  have hDzh : ∀ z θ : ℝ, z ∉ Set.Icc a b →
      Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth F)) z θ = 0 := by
    intro z θ hz
    show z * Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth F)) z θ = 0
    have h2' : ∀ z θ : ℝ, (z, θ) ∈ {p : ℝ × ℝ | p.1 ∉ Set.Icc a b} →
        Work.Spaces.pth (Work.Spaces.pth F) z θ = 0 := fun z θ hz' => hpth2 z θ hz'
    rw [pz_eq_zero_of_eq_zero_on_open hV h2' z θ (hmem z θ hz), mul_zero]
  have hDz2 : ∀ z θ : ℝ, z ∉ Set.Icc a b → Work.Spaces.Dz (Work.Spaces.Dz F) z θ = 0 := by
    intro z θ hz
    show z * Work.Spaces.pz (Work.Spaces.Dz F) z θ = 0
    have hD' : ∀ z θ : ℝ, (z, θ) ∈ {p : ℝ × ℝ | p.1 ∉ Set.Icc a b} →
        Work.Spaces.Dz F z θ = 0 := fun z θ hz' => hDz z θ hz'
    rw [pz_eq_zero_of_eq_zero_on_open hV hD' z θ (hmem z θ hz), mul_zero]
  exact ⟨hpz, hpth, hDz, hpth2, hDzh, hDz2⟩

/-- The `θ`-slices of `D_z G` vanish at `θ = 0` when `G` does. -/
lemma dz_zero_theta {G : ℝ → ℝ → ℝ} (h0 : ∀ z : ℝ, G z 0 = 0) (z : ℝ) :
    Work.Spaces.Dz G z 0 = 0 := by
  show z * Work.Spaces.pz G z 0 = 0
  have hfun : (fun z' : ℝ => G z' 0) = fun _ => (0 : ℝ) := funext h0
  rw [show Work.Spaces.pz G z 0 = deriv (fun z' : ℝ => G z' 0) z from rfl, hfun, deriv_const,
    mul_zero]

/-- The `θ`-slices of `D_z G` vanish at `θ = π/2` when `G` does. -/
lemma dz_zero_pi {G : ℝ → ℝ → ℝ} (hpi : ∀ z : ℝ, G z (Real.pi / 2) = 0) (z : ℝ) :
    Work.Spaces.Dz G z (Real.pi / 2) = 0 := by
  show z * Work.Spaces.pz G z (Real.pi / 2) = 0
  have hfun : (fun z' : ℝ => G z' (Real.pi / 2)) = fun _ => (0 : ℝ) := funext hpi
  rw [show Work.Spaces.pz G z (Real.pi / 2) = deriv (fun z' : ℝ => G z' (Real.pi / 2)) z
      from rfl, hfun, deriv_const, mul_zero]

/-- The slice functional `mixIntS` written with the concrete integrand. -/
private def mixFun (G : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => (Work.Spaces.w z) ^ 2
    * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ)

/-- The slice functional `ddIntS` written with the concrete integrand. -/
private def ddFun (G : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => (Work.Spaces.w z) ^ 2
    * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ)

/-- The slice functional `ttIntS` written with the concrete integrand. -/
private def ttFun (G : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => (Work.Spaces.w z) ^ 2
    * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ)

/-- The slice functional `dIntS` written with the concrete integrand. -/
private def dFun (G : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => (Work.Spaces.w z) ^ 2
    * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ)

/-- The slice functional attached to the angular integrand of the IBP. -/
private def jFun (G : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => (Work.Spaces.w z) ^ 2
    * (∫ θ in Work.Spaces.Iθ, Work.Spaces.Dz G z θ
        * Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ
        * Work.FTS.EllipticEst.thEta θ)

/-- The slice functional attached to the angular integrand of the radial IBP. -/
private def eFun (G : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => (Work.Spaces.w z) ^ 2
    * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
        + Work.FTS.EllipticEst.ThetaU.bcoef z * Work.Spaces.Dz G z θ)
        * Work.Spaces.pth (Work.Spaces.pth G) z θ
        * Work.FTS.EllipticEst.thEta θ)

private lemma mixIntS_eq_mixFun (G : ℝ → ℝ → ℝ) :
    Work.EllipticEst.Core.mixIntS G = mixFun G := rfl

private lemma ddIntS_eq_ddFun (G : ℝ → ℝ → ℝ) :
    Work.EllipticEst.Core.ddIntS G = ddFun G := rfl

private lemma ttIntS_eq_ttFun (G : ℝ → ℝ → ℝ) :
    Work.EllipticEst.Core.ttIntS G = ttFun G := rfl

private lemma dIntS_eq_dFun (G : ℝ → ℝ → ℝ) :
    Work.EllipticEst.Core.dIntS G = dFun G := rfl

/-- **The mixed-derivative interpolation for `G` supported in `z ∈ [a,b] ⊂ (0,∞)`**, smooth on
the open strip `(0,∞) × (-1, π/2+1)` and vanishing at the two angular endpoints.

The proof applies the support-free angular slice inequality
`Work.FTS.EllipticEst.Alpha4.slice_key` to the slices `θ ↦ D_zG z θ` (slicewise in `z`), then
the radial integration by parts `Work.FTS.EllipticEst.ThetaU.radial_ibp_eta` (slicewise in
`θ`, legitimate because of the `z`-support), glues the two iterated integrals with
`Work.FTS.EllipticEst.ThetaU.fubini_w_thEta`, and finishes with the weighted AM–GM. -/
theorem interpStripZbox : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (G : ℝ → ℝ → ℝ) (a b : ℝ), 0 < α → α ≤ 1 / 4 → 0 < a → a < b →
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1))) →
      (∀ z : ℝ, G z 0 = 0) → (∀ z : ℝ, G z (Real.pi / 2) = 0) →
      (∀ z : ℝ, z ∉ Set.Icc a b → ∀ θ : ℝ, G z θ = 0) →
      α ^ 2 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z)
        ≤ C * (α ^ 4 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.ddIntS G z)
            + (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.ttIntS G z)
            + α ^ 2 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.dIntS G z)) := by
  obtain ⟨c₁, hc₁pos, hslice⟩ := Work.FTS.EllipticEst.Alpha4.slice_key
  have heta_lt : Work.Spaces.eta < 1 := Work.Spaces.eta_lt_one
  have hden : 0 < 1 - Work.Spaces.eta := by linarith
  have hnum : 0 < 1 + Work.Spaces.eta := by linarith [Work.Spaces.eta_pos]
  refine ⟨((1 + Work.Spaces.eta) / (1 - Work.Spaces.eta)) * (9 + c₁) + 1, by positivity, ?_⟩
  intro α G a b hα hα4 ha hab hs h0 hpi hsupp
  -- ### smoothness and continuity facts on the strip
  have hcDz : ContinuousOn (Function.uncurry (fun z θ => Work.Spaces.Dz G z θ)) ThetaU.OStrip :=
    (ThetaU.contDiffOn_uncurry_Dz_fin (n := 1) (hs 2)).continuousOn
  have hcDzpth : ContinuousOn (Function.uncurry (fun z θ => Work.Spaces.Dz (Work.Spaces.pth G) z θ))
      ThetaU.OStrip :=
    (ThetaU.contDiffOn_uncurry_Dz_fin (ThetaU.contDiffOn_uncurry_pth_fin (n := 2) (hs 3))).continuousOn
  have hcDzDz : ContinuousOn (Function.uncurry (fun z θ => Work.Spaces.Dz (Work.Spaces.Dz G) z θ))
      ThetaU.OStrip :=
    (ThetaU.contDiffOn_uncurry_Dz_fin (ThetaU.contDiffOn_uncurry_Dz_fin (n := 2) (hs 3))).continuousOn
  have hchh : ContinuousOn (Function.uncurry (fun z θ => Work.Spaces.pth (Work.Spaces.pth G) z θ))
      ThetaU.OStrip :=
    (ThetaU.contDiffOn_uncurry_pth_fin (ThetaU.contDiffOn_uncurry_pth_fin (n := 2) (hs 3))).continuousOn
  have hcDzhh : ContinuousOn
      (Function.uncurry (fun z θ => Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ))
      ThetaU.OStrip :=
    (ThetaU.contDiffOn_uncurry_Dz_fin
      (ThetaU.contDiffOn_uncurry_pth_fin
        (ThetaU.contDiffOn_uncurry_pth_fin (n := 3) (hs 4)))).continuousOn
  have hcbc : ContinuousOn (Function.uncurry (fun z θ => Work.FTS.EllipticEst.ThetaU.bcoef z))
      ThetaU.OStrip := by
    have h1 : ContinuousOn (fun z : ℝ => Work.FTS.EllipticEst.ThetaU.bcoef z) (Set.Ioi 0) := by
      unfold Work.FTS.EllipticEst.ThetaU.bcoef
      refine ContinuousOn.div (continuousOn_id.sub continuousOn_const)
        (continuousOn_const.add continuousOn_id) ?_
      intro z hz
      have hz' : (0 : ℝ) < z := hz
      exact ne_of_gt (by linarith : (0 : ℝ) < 1 + z)
    exact h1.comp continuousOn_fst (fun p hp => hp.1)
  have hquad : ∀ {F : ℝ → ℝ → ℝ}, ContinuousOn (Function.uncurry F) ThetaU.OStrip →
      ContinuousOn (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    fun hF => hF.mono (fun p hp =>
      ⟨hp.1, ⟨by linarith [hp.2.1], by linarith [hp.2.2, Real.pi_pos]⟩⟩)
  have hboxcont : ∀ {F : ℝ → ℝ → ℝ}, ContinuousOn (Function.uncurry F) ThetaU.OStrip →
      ContinuousOn (Function.uncurry F) (Set.Icc a b ×ˢ Work.Spaces.Iθ) :=
    fun hF => hF.mono (fun p hp =>
      ⟨ha.trans_le hp.1.1, ⟨by linarith [hp.2.1], by linarith [hp.2.2, Real.pi_pos]⟩⟩)
  have hbnd : ∀ {F : ℝ → ℝ → ℝ}, ContinuousOn (Function.uncurry F) ThetaU.OStrip →
      ∃ Mb : ℝ, ∀ z ∈ Set.Icc a b, ∀ θ ∈ Work.Spaces.Iθ, |F z θ| ≤ Mb := by
    intro F hF
    obtain ⟨Mb, -, hMb⟩ := ThetaU.exists_bound_box (δ := a) (R := b) ha hab (f := F) (hboxcont hF)
    exact ⟨Mb, hMb⟩
  -- ### the derived quantities vanish off the radial box
  obtain ⟨hvpz, hvpth, hvDz, hvh2, hvDzh, hvDz2⟩ :=
    vanish_all_off_box (F := G) (a := a) (b := b) hsupp
  have hvDzpth : ∀ z θ : ℝ, z ∉ Set.Icc a b → Work.Spaces.Dz (Work.Spaces.pth G) z θ = 0 := by
    intro z θ hz
    show z * Work.Spaces.pz (Work.Spaces.pth G) z θ = 0
    have h' : ∀ z θ : ℝ, (z, θ) ∈ {p : ℝ × ℝ | p.1 ∉ Set.Icc a b} →
        Work.Spaces.pth G z θ = 0 := fun z θ hz' => hvpth z θ hz'
    rw [pz_eq_zero_of_eq_zero_on_open isOpen_compl_Icc_fst h' z θ hz, mul_zero]
  -- ### integrability of the six slice functionals
  have integ (F : ℝ × ℝ → ℝ)
      (hc : ContinuousOn (Function.uncurry (fun z θ => F (z, θ))) ThetaU.OStrip)
      (hF0 : ∀ z, z ∉ Set.Icc a b → ∀ θ, F (z, θ) = 0) :
      MeasureTheory.Integrable (fun z => (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, F (z, θ) * Work.FTS.EllipticEst.thEta θ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    ThetaU.integrable_outer_of_bound (δ := a) (R := b) ha (hquad hc) hF0 (hbnd hc)
  have hintMix : MeasureTheory.Integrable (mixFun G) (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    integ (fun p : ℝ × ℝ => (Work.Spaces.Dz (Work.Spaces.pth G) p.1 p.2) ^ 2)
      (hcDzpth.pow 2)
      (fun z hz θ => by rw [hvDzpth z θ hz]; ring)
  have hintDd : MeasureTheory.Integrable (ddFun G) (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    integ (fun p : ℝ × ℝ => (Work.Spaces.Dz (Work.Spaces.Dz G) p.1 p.2) ^ 2)
      (hcDzDz.pow 2)
      (fun z hz θ => by rw [hvDz2 z θ hz]; ring)
  have hintTT : MeasureTheory.Integrable (ttFun G) (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    integ (fun p : ℝ × ℝ => (Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2) ^ 2)
      (hchh.pow 2)
      (fun z hz θ => by rw [hvh2 z θ hz]; ring)
  have hintDg : MeasureTheory.Integrable (dFun G) (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    integ (fun p : ℝ × ℝ => (Work.Spaces.Dz G p.1 p.2) ^ 2)
      (hcDz.pow 2)
      (fun z hz θ => by rw [hvDz z θ hz]; ring)
  have hintJ : MeasureTheory.Integrable (jFun G) (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    integ (fun p : ℝ × ℝ => Work.Spaces.Dz G p.1 p.2
        * Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) p.1 p.2)
      (hcDz.mul hcDzhh)
      (fun z hz θ => by rw [hvDz z θ hz, hvDzh z θ hz]; ring)
  have hintE : MeasureTheory.Integrable (eFun G) (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    integ (fun p : ℝ × ℝ => (Work.Spaces.Dz (Work.Spaces.Dz G) p.1 p.2
          + Work.FTS.EllipticEst.ThetaU.bcoef p.1 * Work.Spaces.Dz G p.1 p.2)
        * Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2)
      ((hcDzDz.add (hcbc.mul hcDz)).mul hchh)
      (fun z hz θ => by rw [hvDz2 z θ hz, hvDz z θ hz, hvh2 z θ hz]; ring)
  -- ### step 1: the angular slice inequality `slice_key`, slicewise in `z`
  have hDz_slice_cd : ∀ z : ℝ, 0 < z →
      ContDiffOn ℝ 2 (fun θ => Work.Spaces.Dz G z θ) (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := by
    intro z hz
    have hcomp : ContDiffOn ℝ 2 (fun θ : ℝ => (z, θ)) (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
      contDiffOn_const.prodMk contDiffOn_id
    have hmaps : Set.MapsTo (fun θ : ℝ => (z, θ)) (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1))
        ThetaU.OStrip := fun θ hθ => ⟨hz, hθ⟩
    have h := (ThetaU.contDiffOn_uncurry_Dz_fin (n := 2) (hs 3)).comp hcomp hmaps
    simpa [Function.comp_def] using h
  have hcd2 : ∀ z : ℝ, 0 < z → ∀ θ ∈ Work.Spaces.Iθ,
      ContDiffAt ℝ 2 (Function.uncurry G) (z, θ) := by
    intro z hz θ hθ
    exact (hs 2).contDiffAt (ThetaU.isOpen_OStrip.mem_nhds
      ⟨hz, ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩⟩)
  have hstep1 : ∀ z : ℝ, 0 < z →
      (1 - Work.Spaces.eta) / (1 + Work.Spaces.eta) * mixFun G z
        ≤ -((Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.Dz G z θ
              * Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ
              * Work.FTS.EllipticEst.thEta θ))
          + c₁ * dFun G z := by
    intro z hz
    have hkey := hslice (fun θ => Work.Spaces.Dz G z θ) (hDz_slice_cd z hz)
      (dz_zero_theta h0 z) (dz_zero_pi hpi z)
    have e1 : (∫ θ in Work.Spaces.Iθ,
          (deriv (fun θ' : ℝ => Work.Spaces.Dz G z θ') θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ)
        = (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
      rw [show deriv (fun θ' : ℝ => Work.Spaces.Dz G z θ') θ
          = Work.Spaces.pth (Work.Spaces.Dz G) z θ from rfl,
        ThetaU.pth_Dz_eq (hcd2 z hz θ hθ)]
    have e2 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.Dz G z θ
          * deriv (deriv (fun θ' : ℝ => Work.Spaces.Dz G z θ')) θ
          * Work.FTS.EllipticEst.thEta θ)
        = (∫ θ in Work.Spaces.Iθ, Work.Spaces.Dz G z θ
            * Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ
            * Work.FTS.EllipticEst.thEta θ) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
      rw [show deriv (deriv (fun θ' : ℝ => Work.Spaces.Dz G z θ')) θ
          = Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.Dz G)) z θ from rfl,
        ThetaU.pth_pth_Dz_eq (hs 3) hz
          ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩]
    rw [e1, e2] at hkey
    have hw := mul_le_mul_of_nonneg_left hkey (sq_nonneg (Work.Spaces.w z))
    have hL : (Work.Spaces.w z) ^ 2 * ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)
          * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2
                * Work.FTS.EllipticEst.thEta θ))
        = (1 - Work.Spaces.eta) / (1 + Work.Spaces.eta) * mixFun G z := by
      unfold mixFun; ring_nf
    have hR : (Work.Spaces.w z) ^ 2 * (-(∫ θ in Work.Spaces.Iθ, Work.Spaces.Dz G z θ
            * Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ
            * Work.FTS.EllipticEst.thEta θ)
          + c₁ * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.Dz G z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))
        = -((Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.Dz G z θ
              * Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ
              * Work.FTS.EllipticEst.thEta θ))
          + c₁ * dFun G z := by
      unfold dFun
      ring_nf
    rw [hL, hR] at hw
    exact hw
  -- ### step 2: integrate the slice inequality in `z`
  have haez : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
    rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl,
      ← MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioi
  have hintG : MeasureTheory.Integrable
      (fun z => -((Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.Dz G z θ
            * Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ
            * Work.FTS.EllipticEst.thEta θ)) + c₁ * dFun G z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    refine (hintJ.neg.add (hintDg.const_mul c₁)).congr
      (Filter.Eventually.of_forall fun z => ?_)
    simp only [Pi.add_apply, Pi.neg_apply, jFun]
  have hstep2 : (1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)
        * (∫ z in Work.Spaces.Iz, mixFun G z)
      ≤ ∫ z in Work.Spaces.Iz, (-((Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.Dz G z θ
              * Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ
              * Work.FTS.EllipticEst.thEta θ)) + c₁ * dFun G z) := by
    have h1 : (∫ z in Work.Spaces.Iz,
          (1 - Work.Spaces.eta) / (1 + Work.Spaces.eta) * mixFun G z)
        ≤ ∫ z in Work.Spaces.Iz, (-((Work.Spaces.w z) ^ 2
              * (∫ θ in Work.Spaces.Iθ, Work.Spaces.Dz G z θ
                * Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ
                * Work.FTS.EllipticEst.thEta θ)) + c₁ * dFun G z) := by
      refine MeasureTheory.integral_mono_ae (hintMix.const_mul _) hintG ?_
      filter_upwards [haez] with z hz
      exact hstep1 z hz
    rwa [MeasureTheory.integral_const_mul] at h1
  -- ### step 3: the radial integration by parts, slicewise in `θ`
  have hrad : ∀ θ ∈ Work.Spaces.Iθ,
      (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (Work.Spaces.Dz G z θ)
          * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ))
        = - (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
            * (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
                + Work.FTS.EllipticEst.ThetaU.bcoef z * Work.Spaces.Dz G z θ)
            * (Work.Spaces.pth (Work.Spaces.pth G) z θ)) := by
    intro θ hθ
    have hθmem : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) :=
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    have hφ : ContDiffOn ℝ 1 (fun z : ℝ => Work.Spaces.Dz G z θ) (Set.Ioi 0) := by
      have hcomp : ContDiffOn ℝ 1 (fun z : ℝ => (z, θ)) (Set.Ioi 0) :=
        contDiffOn_id.prodMk contDiffOn_const
      have hmaps : Set.MapsTo (fun z : ℝ => (z, θ)) (Set.Ioi 0) ThetaU.OStrip :=
        fun z hz => ⟨hz, hθmem⟩
      have h := (ThetaU.contDiffOn_uncurry_Dz_fin (n := 1) (hs 2)).comp hcomp hmaps
      simpa [Function.comp_def] using h
    have hψ : ContDiffOn ℝ 1 (fun z : ℝ => Work.Spaces.pth (Work.Spaces.pth G) z θ)
        (Set.Ioi 0) := by
      have hcomp : ContDiffOn ℝ 1 (fun z : ℝ => (z, θ)) (Set.Ioi 0) :=
        contDiffOn_id.prodMk contDiffOn_const
      have hmaps : Set.MapsTo (fun z : ℝ => (z, θ)) (Set.Ioi 0) ThetaU.OStrip :=
        fun z hz => ⟨hz, hθmem⟩
      have h := (ThetaU.contDiffOn_uncurry_pth_fin (n := 1)
        (ThetaU.contDiffOn_uncurry_pth_fin (n := 2) (hs 3))).comp hcomp hmaps
      simpa [Function.comp_def] using h
    have hsφ : ∀ z : ℝ, (0 < z ∧ z < a) ∨ b < z → Work.Spaces.Dz G z θ = 0 := by
      intro z hz
      refine hvDz z θ ?_
      rcases hz with hz | hz
      · exact fun hmem => absurd hmem.1 (not_le.mpr hz.2)
      · exact fun hmem => absurd hmem.2 (not_le.mpr hz)
    have hsψ : ∀ z : ℝ, (0 < z ∧ z < a) ∨ b < z →
        Work.Spaces.pth (Work.Spaces.pth G) z θ = 0 := by
      intro z hz
      refine hvh2 z θ ?_
      rcases hz with hz | hz
      · exact fun hmem => absurd hmem.1 (not_le.mpr hz.2)
      · exact fun hmem => absurd hmem.2 (not_le.mpr hz)
    have h := ThetaU.radial_ibp_eta (δ := a) (R := b) ha hab hφ hψ hsφ hsψ
    have eL : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * (fun z : ℝ => Work.Spaces.Dz G z θ) z
          * (z * deriv (fun z : ℝ => Work.Spaces.pth (Work.Spaces.pth G) z θ) z))
        = (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * Work.Spaces.Dz G z θ
            * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
      rfl
    have eR : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (-(z * deriv (fun z : ℝ => Work.Spaces.Dz G z θ) z)
              - (z - 3) / (1 + z) * Work.Spaces.Dz G z θ)
          * (fun z : ℝ => Work.Spaces.pth (Work.Spaces.pth G) z θ) z)
        = - (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
            * (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
                + Work.FTS.EllipticEst.ThetaU.bcoef z * Work.Spaces.Dz G z θ)
            * (Work.Spaces.pth (Work.Spaces.pth G) z θ)) := by
      rw [← MeasureTheory.integral_neg]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
      have hDzDz : z * deriv (fun z' : ℝ => Work.Spaces.Dz G z' θ) z
          = Work.Spaces.Dz (Work.Spaces.Dz G) z θ := rfl
      rw [hDzDz]
      simp only [Work.FTS.EllipticEst.ThetaU.bcoef]
      ring_nf
    rw [eL, eR] at h
    exact h
  -- ### step 3': the Fubini swaps, giving `∫ jFun = -∫ eFun`
  have hswapJ := ThetaU.fubini_w_thEta (δ := a) (R := b) ha
    (hquad (F := fun z θ => Work.Spaces.Dz G z θ
      * Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ) (hcDz.mul hcDzhh))
    (fun z hz θ => by rw [hvDz z θ hz, hvDzh z θ hz]; ring)
    (hbnd (F := fun z θ => Work.Spaces.Dz G z θ
      * Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ) (hcDz.mul hcDzhh))
  have hswapE := ThetaU.fubini_w_thEta (δ := a) (R := b) ha
    (hquad (F := fun z θ => (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
      + Work.FTS.EllipticEst.ThetaU.bcoef z * Work.Spaces.Dz G z θ)
      * Work.Spaces.pth (Work.Spaces.pth G) z θ) ((hcDzDz.add (hcbc.mul hcDz)).mul hchh))
    (fun z hz θ => by rw [hvDz2 z θ hz, hvDz z θ hz, hvh2 z θ hz]; ring)
    (hbnd (F := fun z θ => (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
      + Work.FTS.EllipticEst.ThetaU.bcoef z * Work.Spaces.Dz G z θ)
      * Work.Spaces.pth (Work.Spaces.pth G) z θ) ((hcDzDz.add (hcbc.mul hcDz)).mul hchh))
  have hstep3 : (∫ z in Work.Spaces.Iz, jFun G z) = -(∫ z in Work.Spaces.Iz, eFun G z) := by
    have e1 : (∫ z in Work.Spaces.Iz, jFun G z)
        = ∫ θ in Work.Spaces.Iθ, (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
            * (Work.Spaces.Dz G z θ * Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ))
            * Work.FTS.EllipticEst.thEta θ := by
      unfold jFun
      exact hswapJ
    have e2 : (∫ θ in Work.Spaces.Iθ, (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
            * (Work.Spaces.Dz G z θ * Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ))
            * Work.FTS.EllipticEst.thEta θ)
        = ∫ θ in Work.Spaces.Iθ, (-(∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
            * (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
                + Work.FTS.EllipticEst.ThetaU.bcoef z * Work.Spaces.Dz G z θ)
            * (Work.Spaces.pth (Work.Spaces.pth G) z θ)))
            * Work.FTS.EllipticEst.thEta θ := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
      rw [show (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
            * (Work.Spaces.Dz G z θ * Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ))
          = (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * Work.Spaces.Dz G z θ
              * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)) from by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => by ring),
        hrad θ hθ]
    have e3 : (∫ θ in Work.Spaces.Iθ, (-(∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
            * (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
                + Work.FTS.EllipticEst.ThetaU.bcoef z * Work.Spaces.Dz G z θ)
            * (Work.Spaces.pth (Work.Spaces.pth G) z θ)))
            * Work.FTS.EllipticEst.thEta θ)
        = - (∫ θ in Work.Spaces.Iθ, (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
            * (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
                + Work.FTS.EllipticEst.ThetaU.bcoef z * Work.Spaces.Dz G z θ)
            * (Work.Spaces.pth (Work.Spaces.pth G) z θ))
            * Work.FTS.EllipticEst.thEta θ) := by
      rw [← MeasureTheory.integral_neg]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
      ring
    have e4 : (∫ θ in Work.Spaces.Iθ, (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
            * (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
                + Work.FTS.EllipticEst.ThetaU.bcoef z * Work.Spaces.Dz G z θ)
            * (Work.Spaces.pth (Work.Spaces.pth G) z θ))
            * Work.FTS.EllipticEst.thEta θ) = ∫ z in Work.Spaces.Iz, eFun G z := by
      have hform : (∫ θ in Work.Spaces.Iθ, (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
            * (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
                + Work.FTS.EllipticEst.ThetaU.bcoef z * Work.Spaces.Dz G z θ)
            * (Work.Spaces.pth (Work.Spaces.pth G) z θ))
            * Work.FTS.EllipticEst.thEta θ)
          = ∫ θ in Work.Spaces.Iθ, (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
            * ((Work.Spaces.Dz (Work.Spaces.Dz G) z θ
                + Work.FTS.EllipticEst.ThetaU.bcoef z * Work.Spaces.Dz G z θ)
              * (Work.Spaces.pth (Work.Spaces.pth G) z θ)))
            * Work.FTS.EllipticEst.thEta θ := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
        refine congrArg (fun t => t * Work.FTS.EllipticEst.thEta θ) ?_
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => by ring)
      rw [hform]
      unfold eFun
      exact hswapE.symm
    rw [e1, e2, e3, e4]
  -- ### step 4: the weighted AM–GM, slicewise in `z`
  set δ : ℝ := α ^ 2 / 2 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have h2δ : 2 * δ = α ^ 2 := by rw [hδdef]; ring
  have h18δ : 18 * δ = 9 * α ^ 2 := by rw [hδdef]; ring
  have hδ4 : 1 / (4 * δ) = 1 / (2 * α ^ 2) := by rw [hδdef]; ring
  -- integrability of `F · σ` on `Iθ` for `F` continuous there (`σ = thEta` has only integrable
  -- endpoint singularities, and `{0, π/2}` is a null set)
  have hIntMul : ∀ {F : ℝ → ℝ}, ContinuousOn F Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ : ℝ => F θ * Work.FTS.EllipticEst.thEta θ)
        Work.Spaces.Iθ := by
    intro F hF
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hF
    have hmaj : MeasureTheory.IntegrableOn (fun θ : ℝ => M * Work.FTS.EllipticEst.thEta θ)
        Work.Spaces.Iθ := Work.FTS.EllipticEst.integrableOn_thEta.1.const_mul M
    have hcontIoo : ContinuousOn (fun θ : ℝ => F θ * Work.FTS.EllipticEst.thEta θ)
        (Set.Ioo 0 (Real.pi / 2)) := by
      refine (hF.mono ?_).mul ?_
      · intro θ hθ
        exact ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      · refine ContinuousOn.rpow_const ?_ ?_
        · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
        · intro θ hθ
          exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
            (by linarith [hθ.2, Real.pi_pos])))
    have haesm : AEStronglyMeasurable (fun θ : ℝ => F θ * Work.FTS.EllipticEst.thEta θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      show AEStronglyMeasurable (fun θ : ℝ => F θ * Work.FTS.EllipticEst.thEta θ)
        (MeasureTheory.volume.restrict (Set.Icc 0 (Real.pi / 2)))
      rw [(MeasureTheory.Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc
        (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := Real.pi / 2))).symm]
      exact hcontIoo.aestronglyMeasurable measurableSet_Ioo
    refine MeasureTheory.Integrable.mono' hmaj haesm ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    have hσ : 0 ≤ Work.FTS.EllipticEst.thEta θ := Work.FTS.EllipticEst.thEta_nonneg hθ
    calc ‖F θ * Work.FTS.EllipticEst.thEta θ‖ = ‖F θ‖ * Work.FTS.EllipticEst.thEta θ := by
          rw [norm_mul, Real.norm_of_nonneg hσ]
      _ ≤ M * Work.FTS.EllipticEst.thEta θ := mul_le_mul_of_nonneg_right (hM θ hθ) hσ
  have hstep4pt : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      eFun G z ≤ 2 * δ * ddFun G z + 18 * δ * dFun G z + (1 / (4 * δ)) * ttFun G z := by
    filter_upwards [haez] with z hz
    have hbc : (Work.FTS.EllipticEst.ThetaU.bcoef z) ^ 2 ≤ 9 := by
      have h := ThetaU.bcoef_abs_le hz.le
      nlinarith [abs_nonneg (Work.FTS.EllipticEst.ThetaU.bcoef z),
        sq_abs (Work.FTS.EllipticEst.ThetaU.bcoef z)]
    -- pointwise (in `θ`) continuity of the factors
    have hcomp : ContinuousOn (fun θ : ℝ => (z, θ)) Work.Spaces.Iθ :=
      continuousOn_const.prodMk continuousOn_id
    have hmaps : Set.MapsTo (fun θ : ℝ => (z, θ)) Work.Spaces.Iθ ThetaU.OStrip :=
      fun θ hθ => ⟨hz, ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩⟩
    have hc1 : ContinuousOn (fun θ : ℝ => Work.Spaces.Dz (Work.Spaces.Dz G) z θ)
        Work.Spaces.Iθ := hcDzDz.comp hcomp hmaps
    have hc2 : ContinuousOn (fun θ : ℝ => Work.Spaces.Dz G z θ) Work.Spaces.Iθ :=
      hcDz.comp hcomp hmaps
    have hc3 : ContinuousOn (fun θ : ℝ => Work.Spaces.pth (Work.Spaces.pth G) z θ)
        Work.Spaces.Iθ := hchh.comp hcomp hmaps
    have hc4 : ContinuousOn (fun θ : ℝ => Work.FTS.EllipticEst.ThetaU.bcoef z)
        Work.Spaces.Iθ := continuousOn_const
    have hcF : ContinuousOn (fun θ : ℝ => (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
          + Work.FTS.EllipticEst.ThetaU.bcoef z * Work.Spaces.Dz G z θ)
          * (Work.Spaces.pth (Work.Spaces.pth G) z θ)) Work.Spaces.Iθ :=
      (hc1.add (hc4.mul hc2)).mul hc3
    have hsq1 : MeasureTheory.IntegrableOn (fun θ : ℝ => (Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := hIntMul (hc1.pow 2)
    have hsq2 : MeasureTheory.IntegrableOn (fun θ : ℝ => (Work.Spaces.Dz G z θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := hIntMul (hc2.pow 2)
    have hsq3 : MeasureTheory.IntegrableOn (fun θ : ℝ => (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := hIntMul (hc3.pow 2)
    have hint1 : MeasureTheory.IntegrableOn (fun θ : ℝ => (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
          + Work.FTS.EllipticEst.ThetaU.bcoef z * Work.Spaces.Dz G z θ)
          * (Work.Spaces.pth (Work.Spaces.pth G) z θ) * Work.FTS.EllipticEst.thEta θ)
        Work.Spaces.Iθ := (hIntMul hcF).congr_fun (fun θ _ => by ring) measurableSet_Icc
    have hintA : MeasureTheory.IntegrableOn (fun θ : ℝ => 2 * δ
          * ((Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ)) Work.Spaces.Iθ := hsq1.const_mul (2 * δ)
    have hintB : MeasureTheory.IntegrableOn (fun θ : ℝ => 18 * δ
          * ((Work.Spaces.Dz G z θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ)) Work.Spaces.Iθ := hsq2.const_mul (18 * δ)
    have hintC : MeasureTheory.IntegrableOn (fun θ : ℝ => (1 / (4 * δ))
          * ((Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ)) Work.Spaces.Iθ := hsq3.const_mul (1 / (4 * δ))
    have hintAB : MeasureTheory.IntegrableOn (fun θ : ℝ => 2 * δ
          * ((Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          + 18 * δ * ((Work.Spaces.Dz G z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))
        Work.Spaces.Iθ := (hintA.add hintB).congr_fun (fun θ _ => rfl) measurableSet_Icc
    have hint2 : MeasureTheory.IntegrableOn (fun θ : ℝ => 2 * δ
          * ((Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          + 18 * δ * ((Work.Spaces.Dz G z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          + (1 / (4 * δ)) * ((Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ)) Work.Spaces.Iθ :=
      (hintAB.add hintC).congr_fun (fun θ _ => rfl) measurableSet_Icc
    -- the pointwise AM–GM in `θ`
    have hpt : ∀ θ ∈ Work.Spaces.Iθ, (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
          + Work.FTS.EllipticEst.ThetaU.bcoef z * Work.Spaces.Dz G z θ)
          * (Work.Spaces.pth (Work.Spaces.pth G) z θ) * Work.FTS.EllipticEst.thEta θ
        ≤ 2 * δ * ((Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ)
          + 18 * δ * ((Work.Spaces.Dz G z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          + (1 / (4 * δ)) * ((Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ) := by
      intro θ hθ
      have hσ : 0 ≤ Work.FTS.EllipticEst.thEta θ := Work.FTS.EllipticEst.thEta_nonneg hθ
      have h4δ : 0 < 4 * δ := by linarith
      have h1 : (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
            + Work.FTS.EllipticEst.ThetaU.bcoef z * Work.Spaces.Dz G z θ)
          * (Work.Spaces.pth (Work.Spaces.pth G) z θ)
          ≤ δ * (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
              + Work.FTS.EllipticEst.ThetaU.bcoef z * Work.Spaces.Dz G z θ) ^ 2
            + (1 / (4 * δ)) * (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2 := by
        refine le_of_mul_le_mul_left ?_ h4δ
        have hcert : 0 ≤ (2 * δ * (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
            + Work.FTS.EllipticEst.ThetaU.bcoef z * Work.Spaces.Dz G z θ)
            - (Work.Spaces.pth (Work.Spaces.pth G) z θ)) ^ 2 := sq_nonneg _
        have hkey : (4 * δ) * ((Work.Spaces.Dz (Work.Spaces.Dz G) z θ
              + Work.FTS.EllipticEst.ThetaU.bcoef z * Work.Spaces.Dz G z θ)
              * (Work.Spaces.pth (Work.Spaces.pth G) z θ))
            ≤ (4 * δ) * (δ * (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
                + Work.FTS.EllipticEst.ThetaU.bcoef z * Work.Spaces.Dz G z θ) ^ 2
              + (1 / (4 * δ)) * (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2) := by
          field_simp
          nlinarith [hcert]
        exact hkey
      have h2 : (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
            + Work.FTS.EllipticEst.ThetaU.bcoef z * Work.Spaces.Dz G z θ) ^ 2
          ≤ 2 * (Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2
            + 18 * (Work.Spaces.Dz G z θ) ^ 2 := by
        nlinarith [sq_nonneg (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
            - Work.FTS.EllipticEst.ThetaU.bcoef z * Work.Spaces.Dz G z θ), hbc,
          sq_nonneg (Work.Spaces.Dz G z θ)]
      have h3 : δ * (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
            + Work.FTS.EllipticEst.ThetaU.bcoef z * Work.Spaces.Dz G z θ) ^ 2
          ≤ 2 * δ * ((Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2)
            + 18 * δ * ((Work.Spaces.Dz G z θ) ^ 2) := by
        nlinarith [h2, hδpos.le]
      have h4 : ((Work.Spaces.Dz (Work.Spaces.Dz G) z θ
              + Work.FTS.EllipticEst.ThetaU.bcoef z * Work.Spaces.Dz G z θ)
            * (Work.Spaces.pth (Work.Spaces.pth G) z θ))
            * Work.FTS.EllipticEst.thEta θ
          ≤ (δ * (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
                + Work.FTS.EllipticEst.ThetaU.bcoef z * Work.Spaces.Dz G z θ) ^ 2
              + (1 / (4 * δ)) * (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2)
            * Work.FTS.EllipticEst.thEta θ :=
        mul_le_mul_of_nonneg_right h1 hσ
      have h5 : (δ * (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
                + Work.FTS.EllipticEst.ThetaU.bcoef z * Work.Spaces.Dz G z θ) ^ 2
              + (1 / (4 * δ)) * (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2)
            * Work.FTS.EllipticEst.thEta θ
          ≤ (2 * δ * ((Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2)
              + 18 * δ * ((Work.Spaces.Dz G z θ) ^ 2)
              + (1 / (4 * δ)) * ((Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2))
            * Work.FTS.EllipticEst.thEta θ := by
        refine mul_le_mul_of_nonneg_right ?_ hσ
        linarith [h3]
      have h6 : (2 * δ * ((Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2)
              + 18 * δ * ((Work.Spaces.Dz G z θ) ^ 2)
              + (1 / (4 * δ)) * ((Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2))
            * Work.FTS.EllipticEst.thEta θ
          = 2 * δ * ((Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2
                * Work.FTS.EllipticEst.thEta θ)
            + 18 * δ * ((Work.Spaces.Dz G z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
            + (1 / (4 * δ)) * ((Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2
                * Work.FTS.EllipticEst.thEta θ) := by ring
      linarith [h4, h5, h6]
    -- integrate in `θ`
    have hmono := MeasureTheory.integral_mono_ae hint1 hint2
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hpt)
    -- identify the two sides
    have hsplit : (∫ θ in Work.Spaces.Iθ, 2 * δ
          * ((Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          + 18 * δ * ((Work.Spaces.Dz G z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          + (1 / (4 * δ)) * ((Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ))
        = 2 * δ * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ)
          + 18 * δ * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ)
          + (1 / (4 * δ)) * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2
                * Work.FTS.EllipticEst.thEta θ) := by
      rw [MeasureTheory.integral_add (f := fun θ : ℝ => 2 * δ
            * ((Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
            + 18 * δ * ((Work.Spaces.Dz G z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))
          (g := fun θ : ℝ => (1 / (4 * δ)) * ((Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ)) hintAB hintC,
        MeasureTheory.integral_add (f := fun θ : ℝ => 2 * δ
            * ((Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))
          (g := fun θ : ℝ => 18 * δ * ((Work.Spaces.Dz G z θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ)) hintA hintB,
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul]
    have hsplit' : (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, 2 * δ
          * ((Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          + 18 * δ * ((Work.Spaces.Dz G z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          + (1 / (4 * δ)) * ((Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ))
        = 2 * δ * ddFun G z + 18 * δ * dFun G z + (1 / (4 * δ)) * ttFun G z := by
      rw [hsplit]
      unfold ddFun dFun ttFun
      ring
    have hmul := mul_le_mul_of_nonneg_left hmono (sq_nonneg (Work.Spaces.w z))
    have hgoal : eFun G z ≤ 2 * δ * ddFun G z + 18 * δ * dFun G z
        + (1 / (4 * δ)) * ttFun G z := by
      have hann : eFun G z ≤ (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, 2 * δ
            * ((Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
            + 18 * δ * ((Work.Spaces.Dz G z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
            + (1 / (4 * δ)) * ((Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ)) := by
        unfold eFun
        exact hmul
      rw [hsplit'] at hann
      exact hann
    exact hgoal
  -- ### step 4': integrate in `z`
  have hintR4 : MeasureTheory.Integrable
      (fun z => 2 * δ * ddFun G z + 18 * δ * dFun G z
        + (1 / (4 * δ)) * ttFun G z) (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    ((hintDd.const_mul (2 * δ)).add (hintDg.const_mul (18 * δ))).add
      (hintTT.const_mul (1 / (4 * δ)))
  have hstep4 : (∫ z in Work.Spaces.Iz, eFun G z)
      ≤ 2 * δ * (∫ z in Work.Spaces.Iz, ddFun G z)
        + 18 * δ * (∫ z in Work.Spaces.Iz, dFun G z)
        + (1 / (4 * δ)) * (∫ z in Work.Spaces.Iz, ttFun G z) := by
    have h := MeasureTheory.integral_mono_ae hintE hintR4 hstep4pt
    rw [MeasureTheory.integral_add
        (f := fun z : ℝ => 2 * δ * ddFun G z + 18 * δ * dFun G z)
        (g := fun z : ℝ => (1 / (4 * δ)) * ttFun G z)
        ((hintDd.const_mul (2 * δ)).add (hintDg.const_mul (18 * δ)))
        (hintTT.const_mul (1 / (4 * δ))),
      MeasureTheory.integral_add (f := fun z : ℝ => 2 * δ * ddFun G z)
        (g := fun z : ℝ => 18 * δ * dFun G z)
        (hintDd.const_mul (2 * δ)) (hintDg.const_mul (18 * δ)),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul] at h
    exact h
  -- ### nonnegativity of the three right-hand side functionals
  have hthEta_nn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Work.FTS.EllipticEst.thEta θ :=
    fun θ hθ => Work.FTS.EllipticEst.thEta_nonneg hθ
  have hddnn : 0 ≤ ∫ z in Work.Spaces.Iz, ddFun G z := by
    unfold ddFun
    refine MeasureTheory.integral_nonneg (fun z => ?_)
    refine mul_nonneg (sq_nonneg _) (MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (hthEta_nn θ hθ)))
  have httnn : 0 ≤ ∫ z in Work.Spaces.Iz, ttFun G z := by
    unfold ttFun
    refine MeasureTheory.integral_nonneg (fun z => ?_)
    refine mul_nonneg (sq_nonneg _) (MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (hthEta_nn θ hθ)))
  have hdgnn : 0 ≤ ∫ z in Work.Spaces.Iz, dFun G z := by
    unfold dFun
    refine MeasureTheory.integral_nonneg (fun z => ?_)
    refine mul_nonneg (sq_nonneg _) (MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (hthEta_nn θ hθ)))
  -- ### the arithmetic
  have hJ2 : (∫ z in Work.Spaces.Iz, -((Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, Work.Spaces.Dz G z θ
            * Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ
            * Work.FTS.EllipticEst.thEta θ)) + c₁ * dFun G z)
      = -(∫ z in Work.Spaces.Iz, jFun G z) + c₁ * (∫ z in Work.Spaces.Iz, dFun G z) := by
    rw [MeasureTheory.integral_add
        (f := fun z : ℝ => -((Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.Dz G z θ * Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ
            * Work.FTS.EllipticEst.thEta θ)))
        (g := fun z : ℝ => c₁ * dFun G z) hintJ.neg (hintDg.const_mul c₁),
      MeasureTheory.integral_neg, MeasureTheory.integral_const_mul]
    unfold jFun
    rfl
  have hcomb : (1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)
        * (∫ z in Work.Spaces.Iz, mixFun G z)
      ≤ 2 * δ * (∫ z in Work.Spaces.Iz, ddFun G z)
        + 18 * δ * (∫ z in Work.Spaces.Iz, dFun G z)
        + (1 / (4 * δ)) * (∫ z in Work.Spaces.Iz, ttFun G z)
        + c₁ * (∫ z in Work.Spaces.Iz, dFun G z) := by
    rw [hJ2, hstep3] at hstep2
    linarith [hstep2, hstep4]
  have hchain : (1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)
        * (∫ z in Work.Spaces.Iz, mixFun G z)
      ≤ α ^ 2 * (∫ z in Work.Spaces.Iz, ddFun G z)
        + 9 * α ^ 2 * (∫ z in Work.Spaces.Iz, dFun G z)
        + (1 / (2 * α ^ 2)) * (∫ z in Work.Spaces.Iz, ttFun G z)
        + c₁ * (∫ z in Work.Spaces.Iz, dFun G z) := by
    rw [h18δ, h2δ, hδ4] at hcomb
    linarith [hcomb]
  have halpha2le : α ^ 2 ≤ 1 := by nlinarith [hα, hα4]
  have halpha4le : α ^ 4 ≤ α ^ 2 := by
    have h := mul_le_mul_of_nonneg_left halpha2le (sq_nonneg α)
    nlinarith [h]
  have hposfac : 0 < (1 + Work.Spaces.eta) / (1 - Work.Spaces.eta) := div_pos hnum hden
  have hmain : α ^ 2 * (∫ z in Work.Spaces.Iz, mixFun G z)
      ≤ ((1 + Work.Spaces.eta) / (1 - Work.Spaces.eta)) * (9 + c₁)
        * (α ^ 4 * (∫ z in Work.Spaces.Iz, ddFun G z)
            + (∫ z in Work.Spaces.Iz, ttFun G z)
            + α ^ 2 * (∫ z in Work.Spaces.Iz, dFun G z)) := by
    have hmul := mul_le_mul_of_nonneg_left hchain (sq_nonneg α)
    have hstep : α ^ 2 * ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)
          * (∫ z in Work.Spaces.Iz, mixFun G z))
        ≤ (9 + c₁) * (α ^ 4 * (∫ z in Work.Spaces.Iz, ddFun G z)
            + (∫ z in Work.Spaces.Iz, ttFun G z)
            + α ^ 2 * (∫ z in Work.Spaces.Iz, dFun G z)) := by
      have h4 : α ^ 2 * ((1 / (2 * α ^ 2)) * (∫ z in Work.Spaces.Iz, ttFun G z))
          = (1 / 2) * (∫ z in Work.Spaces.Iz, ttFun G z) := by
        field_simp
      have h5 : α ^ 2 * (9 * α ^ 2 * (∫ z in Work.Spaces.Iz, dFun G z)
            + (1 / (2 * α ^ 2)) * (∫ z in Work.Spaces.Iz, ttFun G z))
          = 9 * α ^ 4 * (∫ z in Work.Spaces.Iz, dFun G z)
            + (1 / 2) * (∫ z in Work.Spaces.Iz, ttFun G z) := by
        rw [mul_add, h4]
        ring
      have h6 : α ^ 2 * (α ^ 2 * (∫ z in Work.Spaces.Iz, ddFun G z)
            + (9 * α ^ 2 * (∫ z in Work.Spaces.Iz, dFun G z)
            + (1 / (2 * α ^ 2)) * (∫ z in Work.Spaces.Iz, ttFun G z))
            + c₁ * (∫ z in Work.Spaces.Iz, dFun G z))
          = α ^ 4 * (∫ z in Work.Spaces.Iz, ddFun G z)
            + (9 * α ^ 4 * (∫ z in Work.Spaces.Iz, dFun G z)
            + (1 / 2) * (∫ z in Work.Spaces.Iz, ttFun G z))
            + c₁ * α ^ 2 * (∫ z in Work.Spaces.Iz, dFun G z) := by
        rw [mul_add, mul_add, h5]
        ring
      have h7 : 9 * α ^ 4 * (∫ z in Work.Spaces.Iz, dFun G z)
          ≤ 9 * α ^ 2 * (∫ z in Work.Spaces.Iz, dFun G z) := by
        have h := mul_le_mul_of_nonneg_right halpha4le hdgnn
        linarith
      have h8 : (1 / 2) * (∫ z in Work.Spaces.Iz, ttFun G z)
          ≤ (∫ z in Work.Spaces.Iz, ttFun G z) := by linarith
      have h9 : α ^ 4 * (∫ z in Work.Spaces.Iz, ddFun G z)
          ≤ 9 * α ^ 4 * (∫ z in Work.Spaces.Iz, ddFun G z) := by
        have h := mul_nonneg (pow_nonneg hα.le 4) hddnn
        linarith
      nlinarith [hmul, h6, h7, h8, h9,
        mul_nonneg hc₁pos.le (mul_nonneg (pow_nonneg hα.le 2) hdgnn),
        mul_nonneg (pow_nonneg hα.le 4) hddnn, mul_nonneg (pow_nonneg hα.le 2) hdgnn]
    have h5 : ((1 + Work.Spaces.eta) / (1 - Work.Spaces.eta))
        * ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)
          * (α ^ 2 * (∫ z in Work.Spaces.Iz, mixFun G z)))
        = α ^ 2 * (∫ z in Work.Spaces.Iz, mixFun G z) := by
      field_simp
    have h6 := mul_le_mul_of_nonneg_left hstep (le_of_lt hposfac)
    linarith [h6, h5]
  have hfinal : α ^ 2 * (∫ z in Work.Spaces.Iz, mixFun G z)
      ≤ (((1 + Work.Spaces.eta) / (1 - Work.Spaces.eta)) * (9 + c₁) + 1)
        * (α ^ 4 * (∫ z in Work.Spaces.Iz, ddFun G z)
            + (∫ z in Work.Spaces.Iz, ttFun G z)
            + α ^ 2 * (∫ z in Work.Spaces.Iz, dFun G z)) := by
    have h0 : 0 ≤ α ^ 4 * (∫ z in Work.Spaces.Iz, ddFun G z)
        + (∫ z in Work.Spaces.Iz, ttFun G z)
        + α ^ 2 * (∫ z in Work.Spaces.Iz, dFun G z) := by
      have h1 : 0 ≤ α ^ 4 * (∫ z in Work.Spaces.Iz, ddFun G z) :=
        mul_nonneg (by positivity) hddnn
      have h2 : 0 ≤ α ^ 2 * (∫ z in Work.Spaces.Iz, dFun G z) :=
        mul_nonneg (by positivity) hdgnn
      linarith
    nlinarith [hmain, h0]
  rw [mixIntS_eq_mixFun, ddIntS_eq_ddFun, ttIntS_eq_ttFun, dIntS_eq_dFun]
  exact hfinal

/-- `F · σ` is integrable on `Iθ` when `F` is continuous there: `σ = thEta` has only an
integrable endpoint singularity and `{0, π/2}` is a null set. -/
private lemma integrableOn_mul_thEta {F : ℝ → ℝ} (hF : ContinuousOn F Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => F θ * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hF
  have hmaj : MeasureTheory.IntegrableOn (fun θ : ℝ => M * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ := Work.FTS.EllipticEst.integrableOn_thEta.1.const_mul M
  have hcontIoo : ContinuousOn (fun θ : ℝ => F θ * Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine (hF.mono ?_).mul ?_
    · intro θ hθ
      exact ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    · refine ContinuousOn.rpow_const ?_ ?_
      · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
      · intro θ hθ
        exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos])))
  have haesm : AEStronglyMeasurable (fun θ : ℝ => F θ * Work.FTS.EllipticEst.thEta θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    show AEStronglyMeasurable (fun θ : ℝ => F θ * Work.FTS.EllipticEst.thEta θ)
      (MeasureTheory.volume.restrict (Set.Icc 0 (Real.pi / 2)))
    rw [(MeasureTheory.Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc
      (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := Real.pi / 2))).symm]
    exact hcontIoo.aestronglyMeasurable measurableSet_Ioo
  refine MeasureTheory.Integrable.mono' hmaj haesm ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
  have hσ : 0 ≤ Work.FTS.EllipticEst.thEta θ := Work.FTS.EllipticEst.thEta_nonneg hθ
  calc ‖F θ * Work.FTS.EllipticEst.thEta θ‖ = ‖F θ‖ * Work.FTS.EllipticEst.thEta θ := by
        rw [norm_mul, Real.norm_of_nonneg hσ]
    _ ≤ M * Work.FTS.EllipticEst.thEta θ := mul_le_mul_of_nonneg_right (hM θ hθ) hσ

/-- **Domination of the two cut-off corrections by the angular second derivative.**
For `G` smooth on the strip with `G z 0 = G z (π/2) = 0` and `z > 0`,
`w² ∫_θ (∂_θG)²σ ≤ CB · ttIntS G z` and `w² ∫_θ G²σ ≤ CE · ttIntS G z`. -/
private lemma sliceCorrectionBounds : ∃ CB CE : ℝ, 0 ≤ CB ∧ 0 ≤ CE ∧
    ∀ (G : ℝ → ℝ → ℝ), ThetaU.SmoothOpenθ G →
      (∀ z : ℝ, G z 0 = 0) → (∀ z : ℝ, G z (Real.pi / 2) = 0) →
      ∀ z : ℝ, 0 < z →
        ((Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth G z θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ) ≤ CB * ttFun G z) ∧
        ((Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
              ≤ CE * ttFun G z) := by
  set J : ℝ := ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ Work.Spaces.eta with hJ
  set S : ℝ := ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ with hS
  have hJnn : 0 ≤ J := by
    rw [hJ]
    refine MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => ?_)
    exact Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])) _
  have hSnn : 0 ≤ S := by
    rw [hS]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => Work.FTS.EllipticEst.thEta_nonneg hθ)
  refine ⟨J * S, (Real.pi / 2) ^ 2 * (J * S), by positivity, by positivity, ?_⟩
  intro G hsm h0 hpi z hz
  -- the slice data, common to the two conjuncts
  have hslice : ThetaU.SliceSmoothO (fun θ : ℝ => G z θ) := by
    rw [ThetaU.sliceSmoothO_iff]
    intro n
    have hcomp : ContDiffOn ℝ n (fun θ : ℝ => (z, θ)) (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
      contDiffOn_const.prodMk contDiffOn_id
    have hmaps : Set.MapsTo (fun θ : ℝ => (z, θ)) (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1))
        ThetaU.OStrip := fun θ hθ => ⟨hz, hθ⟩
    exact ((hsm n).comp hcomp hmaps)
  have hvcont : ContinuousOn (fun θ : ℝ =>
      Work.FTS.EllipticEst.sliceV (fun θ' : ℝ => G z θ') θ) Work.Spaces.Iθ := by
    have hcomp : ContinuousOn (fun θ : ℝ => (z, θ)) Work.Spaces.Iθ :=
      continuousOn_const.prodMk continuousOn_id
    have hmaps : Set.MapsTo (fun θ : ℝ => (z, θ)) Work.Spaces.Iθ ThetaU.OStrip :=
      fun θ hθ => ⟨hz, ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩⟩
    have hpth2 : ContinuousOn
        (Function.uncurry (fun z θ => Work.Spaces.pth (Work.Spaces.pth G) z θ)) ThetaU.OStrip :=
      (ThetaU.contDiffOn_uncurry_pth_fin (n := 1)
        (ThetaU.contDiffOn_uncurry_pth_fin (n := 2) (hsm 3))).continuousOn
    exact (hpth2.comp hcomp hmaps)
  have hAeq : (∫ θ in Work.Spaces.Iθ,
        (Work.FTS.EllipticEst.sliceV (fun θ' : ℝ => G z θ') θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ)
      = (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    rfl
  constructor
  · -- the first-derivative correction
    have hint : MeasureTheory.IntegrableOn (fun θ : ℝ =>
        (Work.FTS.EllipticEst.sliceV (fun θ' : ℝ => G z θ') θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ :=
      integrableOn_mul_thEta (hvcont.pow 2)
    have hkey := ThetaU.slice_deriv_sq_le_open hslice (by rw [h0 z, hpi z]) hint
    -- the pointwise data constant
    have hmono : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth G z θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ)
        ≤ (∫ θ in Work.Spaces.Iθ,
              (Work.FTS.EllipticEst.sliceV (fun θ' : ℝ => G z θ') θ) ^ 2
                * Work.FTS.EllipticEst.thEta θ) * J * S := by
      have hcontpth : ContinuousOn (fun θ : ℝ => (Work.Spaces.pth G z θ) ^ 2)
          Work.Spaces.Iθ := by
        have hcomp : ContinuousOn (fun θ : ℝ => (z, θ)) Work.Spaces.Iθ :=
          continuousOn_const.prodMk continuousOn_id
        have hmaps : Set.MapsTo (fun θ : ℝ => (z, θ)) Work.Spaces.Iθ ThetaU.OStrip :=
          fun θ hθ => ⟨hz, ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩⟩
        have hpth : ContinuousOn
            (Function.uncurry (fun z θ => Work.Spaces.pth G z θ)) ThetaU.OStrip :=
          (ThetaU.contDiffOn_uncurry_pth_fin (n := 1) (hsm 2)).continuousOn
        exact (hpth.comp hcomp hmaps).pow 2
      have h1 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth G z θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ)
          ≤ ∫ θ in Work.Spaces.Iθ, ((∫ θ' in Work.Spaces.Iθ,
                (Work.FTS.EllipticEst.sliceV (fun θ'' : ℝ => G z θ'') θ') ^ 2
                  * Work.FTS.EllipticEst.thEta θ') * J) * Work.FTS.EllipticEst.thEta θ := by
        refine MeasureTheory.integral_mono_ae (integrableOn_mul_thEta hcontpth)
          (Work.FTS.EllipticEst.integrableOn_thEta.1.const_mul _) ?_
        refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
        have hσ : 0 ≤ Work.FTS.EllipticEst.thEta θ := Work.FTS.EllipticEst.thEta_nonneg hθ
        have := hkey θ hθ
        rw [hJ]
        exact mul_le_mul_of_nonneg_right this hσ
      have h2 : (∫ θ in Work.Spaces.Iθ, ((∫ θ' in Work.Spaces.Iθ,
              (Work.FTS.EllipticEst.sliceV (fun θ'' : ℝ => G z θ'') θ') ^ 2
                * Work.FTS.EllipticEst.thEta θ') * J) * Work.FTS.EllipticEst.thEta θ)
          = (∫ θ' in Work.Spaces.Iθ,
              (Work.FTS.EllipticEst.sliceV (fun θ'' : ℝ => G z θ'') θ') ^ 2
                * Work.FTS.EllipticEst.thEta θ') * J * S := by
        rw [show (fun θ : ℝ => ((∫ θ' in Work.Spaces.Iθ,
              (Work.FTS.EllipticEst.sliceV (fun θ'' : ℝ => G z θ'') θ') ^ 2
                * Work.FTS.EllipticEst.thEta θ') * J) * Work.FTS.EllipticEst.thEta θ)
            = fun θ : ℝ => Work.FTS.EllipticEst.thEta θ
              * ((∫ θ' in Work.Spaces.Iθ,
                  (Work.FTS.EllipticEst.sliceV (fun θ'' : ℝ => G z θ'') θ') ^ 2
                    * Work.FTS.EllipticEst.thEta θ') * J) from by funext θ; ring,
          MeasureTheory.integral_mul_const, hS]
        ring
      rw [h2] at h1
      linarith [h1]
    rw [hAeq] at hmono
    have hstep := mul_le_mul_of_nonneg_left hmono (sq_nonneg (Work.Spaces.w z))
    calc (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth G z θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ)
        ≤ (Work.Spaces.w z) ^ 2 * ((∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2
                * Work.FTS.EllipticEst.thEta θ) * J * S) := hstep
      _ = (J * S) * ttFun G z := by
          unfold ttFun
          ring
  · -- the value correction
    have hint : MeasureTheory.IntegrableOn (fun θ : ℝ =>
        (Work.FTS.EllipticEst.sliceV (fun θ' : ℝ => G z θ') θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ :=
      integrableOn_mul_thEta (hvcont.pow 2)
    have hkey := ThetaU.slice_self_sq_le_open hslice (h0 z) (hpi z) hint
    have hmono : (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        ≤ (Real.pi / 2) ^ 2
          * ((∫ θ in Work.Spaces.Iθ,
                (Work.FTS.EllipticEst.sliceV (fun θ' : ℝ => G z θ') θ) ^ 2
                  * Work.FTS.EllipticEst.thEta θ) * J * S) := by
      have hcontG : ContinuousOn (fun θ : ℝ => (G z θ) ^ 2) Work.Spaces.Iθ := by
        have hcomp : ContinuousOn (fun θ : ℝ => (z, θ)) Work.Spaces.Iθ :=
          continuousOn_const.prodMk continuousOn_id
        have hmaps : Set.MapsTo (fun θ : ℝ => (z, θ)) Work.Spaces.Iθ ThetaU.OStrip :=
          fun θ hθ => ⟨hz, ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩⟩
        exact ((hsm 1).continuousOn.comp hcomp hmaps).pow 2
      have h1 : (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          ≤ ∫ θ in Work.Spaces.Iθ, ((Real.pi / 2) ^ 2 * ((∫ θ' in Work.Spaces.Iθ,
                (Work.FTS.EllipticEst.sliceV (fun θ'' : ℝ => G z θ'') θ') ^ 2
                  * Work.FTS.EllipticEst.thEta θ') * J)) * Work.FTS.EllipticEst.thEta θ := by
        refine MeasureTheory.integral_mono_ae (integrableOn_mul_thEta hcontG)
          (Work.FTS.EllipticEst.integrableOn_thEta.1.const_mul _) ?_
        refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
        have hσ : 0 ≤ Work.FTS.EllipticEst.thEta θ := Work.FTS.EllipticEst.thEta_nonneg hθ
        have := hkey θ hθ
        rw [hJ]
        exact mul_le_mul_of_nonneg_right this hσ
      have h2 : (∫ θ in Work.Spaces.Iθ, ((Real.pi / 2) ^ 2 * ((∫ θ' in Work.Spaces.Iθ,
              (Work.FTS.EllipticEst.sliceV (fun θ'' : ℝ => G z θ'') θ') ^ 2
                * Work.FTS.EllipticEst.thEta θ') * J)) * Work.FTS.EllipticEst.thEta θ)
          = (Real.pi / 2) ^ 2 * ((∫ θ' in Work.Spaces.Iθ,
              (Work.FTS.EllipticEst.sliceV (fun θ'' : ℝ => G z θ'') θ') ^ 2
                * Work.FTS.EllipticEst.thEta θ') * J * S) := by
        rw [show (fun θ : ℝ => ((Real.pi / 2) ^ 2 * ((∫ θ' in Work.Spaces.Iθ,
              (Work.FTS.EllipticEst.sliceV (fun θ'' : ℝ => G z θ'') θ') ^ 2
                * Work.FTS.EllipticEst.thEta θ') * J)) * Work.FTS.EllipticEst.thEta θ)
            = fun θ : ℝ => Work.FTS.EllipticEst.thEta θ
              * ((Real.pi / 2) ^ 2 * ((∫ θ' in Work.Spaces.Iθ,
                  (Work.FTS.EllipticEst.sliceV (fun θ'' : ℝ => G z θ'') θ') ^ 2
                    * Work.FTS.EllipticEst.thEta θ') * J)) from by funext θ; ring,
          MeasureTheory.integral_mul_const, hS]
        ring
      rw [h2] at h1
      linarith [h1]
    rw [hAeq] at hmono
    have hstep := mul_le_mul_of_nonneg_left hmono (sq_nonneg (Work.Spaces.w z))
    calc (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ)
        ≤ (Work.Spaces.w z) ^ 2 * ((Real.pi / 2) ^ 2 * ((∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2
                * Work.FTS.EllipticEst.thEta θ) * J * S)) := hstep
      _ = ((Real.pi / 2) ^ 2 * (J * S)) * ttFun G z := by
          unfold ttFun
          ring
/-! ## The radial truncation: from the box-supported estimate to the general class -/

/-- The extension of `G` by zero for `z ≤ 0` (the values for `z < 0` are irrelevant; this makes
the support hypothesis of the box estimate available). -/
private def zPosExt (G : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => if 0 < z then G z θ else 0

private lemma zPosExt_of_pos {G : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z) :
    zPosExt G z θ = G z θ := if_pos hz

private lemma zPosExt_of_nonpos {G : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : ¬ 0 < z) :
    zPosExt G z θ = 0 := if_neg hz

private lemma zPosExt_smooth {G : ℝ → ℝ → ℝ}
    (hs : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1))) :
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (zPosExt G))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
  fun n => (hs n).congr (fun p hp => zPosExt_of_pos hp.1)

/-- **Integrability of the four slice functionals of a box-supported smooth function.** -/
private lemma integrableOn_sliceFuns_of_zbox {F : ℝ → ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry F) ThetaU.OStrip)
    (hsupp : ∀ z : ℝ, z ∉ Set.Icc a b → ∀ θ : ℝ, F z θ = 0) :
    MeasureTheory.IntegrableOn (mixFun F) Work.Spaces.Iz ∧
    MeasureTheory.IntegrableOn (ddFun F) Work.Spaces.Iz ∧
    MeasureTheory.IntegrableOn (ttFun F) Work.Spaces.Iz ∧
    MeasureTheory.IntegrableOn (dFun F) Work.Spaces.Iz := by
  have hcDz : ContinuousOn (Function.uncurry (fun z θ => Work.Spaces.Dz F z θ)) ThetaU.OStrip :=
    (ThetaU.contDiffOn_uncurry_Dz_fin (n := 1) (hsm 2)).continuousOn
  have hcDzpth : ContinuousOn (Function.uncurry (fun z θ => Work.Spaces.Dz (Work.Spaces.pth F) z θ))
      ThetaU.OStrip :=
    (ThetaU.contDiffOn_uncurry_Dz_fin
      (ThetaU.contDiffOn_uncurry_pth_fin (n := 2) (hsm 3))).continuousOn
  have hcDzDz : ContinuousOn (Function.uncurry (fun z θ => Work.Spaces.Dz (Work.Spaces.Dz F) z θ))
      ThetaU.OStrip :=
    (ThetaU.contDiffOn_uncurry_Dz_fin (ThetaU.contDiffOn_uncurry_Dz_fin (n := 2) (hsm 3))).continuousOn
  have hchh : ContinuousOn (Function.uncurry (fun z θ => Work.Spaces.pth (Work.Spaces.pth F) z θ))
      ThetaU.OStrip :=
    (ThetaU.contDiffOn_uncurry_pth_fin
      (ThetaU.contDiffOn_uncurry_pth_fin (n := 2) (hsm 3))).continuousOn
  have hquad : ∀ {F' : ℝ → ℝ → ℝ}, ContinuousOn (Function.uncurry F') ThetaU.OStrip →
      ContinuousOn (Function.uncurry F') (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    fun hF => hF.mono (fun p hp =>
      ⟨hp.1, ⟨by linarith [hp.2.1], by linarith [hp.2.2, Real.pi_pos]⟩⟩)
  have hboxcont : ∀ {F' : ℝ → ℝ → ℝ}, ContinuousOn (Function.uncurry F') ThetaU.OStrip →
      ContinuousOn (Function.uncurry F') (Set.Icc a b ×ˢ Work.Spaces.Iθ) :=
    fun hF => hF.mono (fun p hp =>
      ⟨ha.trans_le hp.1.1, ⟨by linarith [hp.2.1], by linarith [hp.2.2, Real.pi_pos]⟩⟩)
  have hbnd : ∀ {F' : ℝ → ℝ → ℝ}, ContinuousOn (Function.uncurry F') ThetaU.OStrip →
      ∃ Mb : ℝ, ∀ z ∈ Set.Icc a b, ∀ θ ∈ Work.Spaces.Iθ, |F' z θ| ≤ Mb := by
    intro F' hF
    obtain ⟨Mb, -, hMb⟩ := ThetaU.exists_bound_box (δ := a) (R := b) ha hab (f := F') (hboxcont hF)
    exact ⟨Mb, hMb⟩
  obtain ⟨_, hvpth, hvDz, hvh2, hvDzh, hvDz2⟩ :=
    vanish_all_off_box (F := F) (a := a) (b := b) hsupp
  have hvDzpth : ∀ z θ : ℝ, z ∉ Set.Icc a b → Work.Spaces.Dz (Work.Spaces.pth F) z θ = 0 := by
    intro z θ hz
    show z * Work.Spaces.pz (Work.Spaces.pth F) z θ = 0
    have h' : ∀ z θ : ℝ, z ∉ Set.Icc a b → Work.Spaces.pth F z θ = 0 := fun z θ hz' => hvpth z θ hz'
    rw [pz_eq_zero_of_eq_zero_on_open isOpen_compl_Icc_fst h' z θ hz, mul_zero]
  have integ (F' : ℝ × ℝ → ℝ)
      (hc : ContinuousOn (Function.uncurry (fun z θ => F' (z, θ))) ThetaU.OStrip)
      (hF0 : ∀ z, z ∉ Set.Icc a b → ∀ θ, F' (z, θ) = 0) :
      MeasureTheory.Integrable (fun z => (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, F' (z, θ) * Work.FTS.EllipticEst.thEta θ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    ThetaU.integrable_outer_of_bound (δ := a) (R := b) ha (hquad hc) hF0 (hbnd hc)
  exact ⟨integ (fun p : ℝ × ℝ => (Work.Spaces.Dz (Work.Spaces.pth F) p.1 p.2) ^ 2)
      (hcDzpth.pow 2) (fun z hz θ => by rw [hvDzpth z θ hz]; ring),
    integ (fun p : ℝ × ℝ => (Work.Spaces.Dz (Work.Spaces.Dz F) p.1 p.2) ^ 2)
      (hcDzDz.pow 2) (fun z hz θ => by rw [hvDz2 z θ hz]; ring),
    integ (fun p : ℝ × ℝ => (Work.Spaces.pth (Work.Spaces.pth F) p.1 p.2) ^ 2)
      (hchh.pow 2) (fun z hz θ => by rw [hvh2 z θ hz]; ring),
    integ (fun p : ℝ × ℝ => (Work.Spaces.Dz F p.1 p.2) ^ 2)
      (hcDz.pow 2) (fun z hz θ => by rw [hvDz z θ hz]; ring)⟩

/-! ## Product rules for a factor depending only on `z` -/

/-- `D_z` respects equality on an open set. -/
private lemma Dz_congr_on {f g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) V) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dz f)) (Function.uncurry (Work.Spaces.Dz g)) V := by
  intro p hp
  obtain ⟨z, θ⟩ := p
  show z * deriv (fun z' : ℝ => f z' θ) z = z * deriv (fun z' : ℝ => g z' θ) z
  have hnb : ∀ᶠ z' in 𝓝 z, (z', θ) ∈ V :=
    (continuous_id.prodMk continuous_const).continuousAt (hV.mem_nhds hp)
  have hev : (fun z' : ℝ => f z' θ) =ᶠ[𝓝 z] (fun z' : ℝ => g z' θ) := by
    filter_upwards [hnb] with z' hz'
    exact h hz'
  rw [hev.deriv_eq]

/-- `D_z` is additive. -/
private lemma Dz_add {f g : ℝ → ℝ → ℝ} (z θ : ℝ)
    (hf : DifferentiableAt ℝ (fun z' : ℝ => f z' θ) z)
    (hg : DifferentiableAt ℝ (fun z' : ℝ => g z' θ) z) :
    Work.Spaces.Dz (f + g) z θ = Work.Spaces.Dz f z θ + Work.Spaces.Dz g z θ := by
  show z * deriv (fun z' : ℝ => (f + g) z' θ) z
      = z * Work.Spaces.pz f z θ + z * Work.Spaces.pz g z θ
  rw [show (fun z' : ℝ => (f + g) z' θ)
      = (fun z' : ℝ => f z' θ) + (fun z' : ℝ => g z' θ) from by funext z'; rfl,
    deriv_add hf hg]
  simp only [Work.Spaces.pz]
  ring

/-- The `θ`-slice of a strip-smooth function is differentiable. -/
private lemma diffAt_slice_of_strip {F : ℝ → ℝ → ℝ}
    (hF : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry F) ThetaU.OStrip) {z θ : ℝ}
    (hmem : (z, θ) ∈ ThetaU.OStrip) :
    DifferentiableAt ℝ (fun θ' : ℝ => F z θ') θ :=
  (Work.Spaces.hasDerivAt_slice_snd
    (((hF 1).contDiffAt (ThetaU.isOpen_OStrip.mem_nhds hmem)).differentiableAt
      one_ne_zero).hasFDerivAt).differentiableAt

/-- The `z`-slice of a strip-smooth function is differentiable. -/
private lemma diffAt_slice_z_of_strip {F : ℝ → ℝ → ℝ}
    (hF : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry F) ThetaU.OStrip) {z θ : ℝ}
    (hmem : (z, θ) ∈ ThetaU.OStrip) :
    DifferentiableAt ℝ (fun z' : ℝ => F z' θ) z :=
  (Work.Spaces.hasDerivAt_slice_fst
    (((hF 1).contDiffAt (ThetaU.isOpen_OStrip.mem_nhds hmem)).differentiableAt
      one_ne_zero).hasFDerivAt).differentiableAt

/-- `∂_θ` of `z ↦ c z` times `F`. -/
private lemma pth_mul_z {F : ℝ → ℝ → ℝ} {c : ℝ → ℝ}
    (hF : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry F) ThetaU.OStrip)
    {z θ : ℝ} (hmem : (z, θ) ∈ ThetaU.OStrip) :
    Work.Spaces.pth (fun z θ => c z * F z θ) z θ = c z * Work.Spaces.pth F z θ := by
  show deriv (fun θ' : ℝ => c z * F z θ') θ = c z * deriv (fun θ' : ℝ => F z θ') θ
  rw [show (fun θ' : ℝ => c z * F z θ') = (fun _ : ℝ => c z) * (fun θ' : ℝ => F z θ')
      from by funext θ'; rfl,
    deriv_mul (differentiableAt_const (c := c z)) (diffAt_slice_of_strip hF hmem)]
  simp

/-- `D_z` of `z ↦ c z` times `F`. -/
private lemma Dz_mul_z {F : ℝ → ℝ → ℝ} {c : ℝ → ℝ}
    (hF : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry F) ThetaU.OStrip)
    (hc : ∀ n : ℕ, ContDiffOn ℝ n c (Set.Ioi 0)) {z θ : ℝ} (hmem : (z, θ) ∈ ThetaU.OStrip) :
    Work.Spaces.Dz (fun z θ => c z * F z θ) z θ
      = c z * Work.Spaces.Dz F z θ + (z * deriv c z) * F z θ := by
  have hcd : DifferentiableAt ℝ c z :=
    ((hc 1).differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0)).differentiableAt
      (isOpen_Ioi.mem_nhds (show z ∈ Set.Ioi (0 : ℝ) from hmem.1))
  show z * deriv (fun z' : ℝ => c z' * F z' θ) z
      = c z * (z * deriv (fun z' : ℝ => F z' θ) z) + (z * deriv c z) * F z θ
  rw [show (fun z' : ℝ => c z' * F z' θ) = c * (fun z' : ℝ => F z' θ) from by
    funext z'; rfl, deriv_mul hcd (diffAt_slice_z_of_strip hF hmem)]
  ring

/-- `D_z²` of `z ↦ c z` times `F`. -/
private lemma DzDz_mul_z {F : ℝ → ℝ → ℝ} {c : ℝ → ℝ}
    (hF : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry F) ThetaU.OStrip)
    (hc : ∀ n : ℕ, ContDiffOn ℝ n c (Set.Ioi 0)) {z θ : ℝ} (hmem : (z, θ) ∈ ThetaU.OStrip) :
    Work.Spaces.Dz (Work.Spaces.Dz (fun z θ => c z * F z θ)) z θ
      = c z * Work.Spaces.Dz (Work.Spaces.Dz F) z θ
        + 2 * (z * deriv c z) * Work.Spaces.Dz F z θ
        + (z * deriv (fun y : ℝ => y * deriv c y) z) * F z θ := by
  have hζ : ∀ n : ℕ, ContDiffOn ℝ n (fun z : ℝ => z * deriv c z) (Set.Ioi 0) := by
    intro n
    have hd : ContDiffOn ℝ n (deriv c) (Set.Ioi 0) := (hc (n + 1)).deriv_of_isOpen isOpen_Ioi (by simp)
    exact contDiffOn_id.mul hd
  have hDzF : ∀ n : ℕ, ContDiffOn ℝ n
      (Function.uncurry (fun z θ => Work.Spaces.Dz F z θ)) ThetaU.OStrip :=
    fun n => ThetaU.contDiffOn_uncurry_Dz_fin (hF (n + 1))
  have hstep : Work.Spaces.Dz (Work.Spaces.Dz (fun z θ => c z * F z θ)) z θ
      = Work.Spaces.Dz (fun z θ => c z * Work.Spaces.Dz F z θ + (z * deriv c z) * F z θ) z θ :=
    Dz_congr_on (f := Work.Spaces.Dz (fun z θ => c z * F z θ))
      (g := fun z θ => c z * Work.Spaces.Dz F z θ + (z * deriv c z) * F z θ)
      ThetaU.isOpen_OStrip (fun p hp => Dz_mul_z hF hc hp) hmem
  rw [hstep]
  have hprod1 : ∀ n : ℕ,
      ContDiffOn ℝ n (Function.uncurry (fun z θ => c z * Work.Spaces.Dz F z θ)) ThetaU.OStrip := by
    intro n
    have hc1 : ContDiffOn ℝ n (fun p : ℝ × ℝ => c p.1) ThetaU.OStrip :=
      (hc n).comp contDiffOn_fst (fun p hp => hp.1)
    exact hc1.mul (hDzF n)
  have hprod2 : ∀ n : ℕ,
      ContDiffOn ℝ n (Function.uncurry (fun z θ => (z * deriv c z) * F z θ)) ThetaU.OStrip := by
    intro n
    have hζ1 : ContDiffOn ℝ n (fun p : ℝ × ℝ => p.1 * deriv c p.1) ThetaU.OStrip :=
      (hζ n).comp contDiffOn_fst (fun p hp => hp.1)
    exact hζ1.mul (hF n)
  rw [show (fun z θ : ℝ => c z * Work.Spaces.Dz F z θ + (z * deriv c z) * F z θ)
      = (fun z θ : ℝ => c z * Work.Spaces.Dz F z θ)
        + (fun z θ : ℝ => (z * deriv c z) * F z θ) from by funext z θ; rfl]
  rw [Dz_add (f := fun z θ : ℝ => c z * Work.Spaces.Dz F z θ)
      (g := fun z θ : ℝ => (z * deriv c z) * F z θ) z θ
      (diffAt_slice_z_of_strip hprod1 hmem) (diffAt_slice_z_of_strip hprod2 hmem)]
  rw [show Work.Spaces.Dz (fun z θ : ℝ => c z * Work.Spaces.Dz F z θ) z θ
      = c z * Work.Spaces.Dz (Work.Spaces.Dz F) z θ
        + (z * deriv c z) * Work.Spaces.Dz F z θ from Dz_mul_z hDzF hc hmem,
    show Work.Spaces.Dz (fun z θ : ℝ => (z * deriv c z) * F z θ) z θ
      = (z * deriv c z) * Work.Spaces.Dz F z θ
        + (z * deriv (fun y : ℝ => y * deriv c y) z) * F z θ from Dz_mul_z hF hζ hmem]
  ring

/-! ## The cut-off family and the truncation estimates -/

/-- The cut-off truncation of `G` by `χ k`. -/
private def trunc (χ : ℕ → ℝ → ℝ) (G : ℝ → ℝ → ℝ) (k : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => χ k z * zPosExt G z θ

/-- `D_z` of the cut-off `χ k`. -/
private def zeta (χ : ℕ → ℝ → ℝ) (k : ℕ) : ℝ → ℝ := fun z => z * deriv (χ k) z

/-- `D_z²` of the cut-off `χ k`. -/
private def xi (χ : ℕ → ℝ → ℝ) (k : ℕ) : ℝ → ℝ :=
  fun z => z * deriv (fun y : ℝ => y * deriv (χ k) y) z

/-- The logarithmic rate `K / log (k+2)` of the cut-off family. -/
private def ck (K : ℝ) (k : ℕ) : ℝ := K / Real.log ((k : ℝ) + 2)

/-- The correction functional attached to `∂_θG`. -/
private def Bfun (G : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => (Work.Spaces.w z) ^ 2
    * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth G z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)

/-- The correction functional attached to `G`. -/
private def Efun (G : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => (Work.Spaces.w z) ^ 2
    * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)

/-- The `z`-integral of `ddFun`. -/
private def ZDd (G : ℝ → ℝ → ℝ) : ℝ := ∫ z in Work.Spaces.Iz, ddFun G z

/-- The `z`-integral of `ttFun`. -/
private def ZTt (G : ℝ → ℝ → ℝ) : ℝ := ∫ z in Work.Spaces.Iz, ttFun G z

/-- The `z`-integral of `dFun`. -/
private def ZD (G : ℝ → ℝ → ℝ) : ℝ := ∫ z in Work.Spaces.Iz, dFun G z

/-- The `z`-integral of `mixFun`. -/
private def ZMx (G : ℝ → ℝ → ℝ) : ℝ := ∫ z in Work.Spaces.Iz, mixFun G z

/-- The limiting constant of the truncated estimate. -/
private def Abnd (C₀ α : ℝ) (G : ℝ → ℝ → ℝ) : ℝ :=
  C₀ * (3 * α ^ 4 * ZDd G + ZTt G + 2 * α ^ 2 * ZD G)


/-! ### Elementary lemmas on the strip -/

private lemma eventually_strip_snd {z θ : ℝ} (hmem : (z, θ) ∈ ThetaU.OStrip) :
    ∀ᶠ θ' in 𝓝 θ, (z, θ') ∈ ThetaU.OStrip :=
  (ThetaU.isOpen_OStrip.preimage (continuous_const.prodMk continuous_id)).mem_nhds hmem

private lemma eqOn_curry {f g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (h : ∀ z θ : ℝ, (z, θ) ∈ V → f z θ = g z θ) :
    Set.EqOn (Function.uncurry f) (Function.uncurry g) V :=
  fun p hp => h p.1 p.2 hp

private lemma eqOn_apply {f g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) V) {z θ : ℝ}
    (hm : (z, θ) ∈ V) : f z θ = g z θ := h hm

/-- `∂_θ` respects equality on an open set. -/
private lemma pth_congr_on {f g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) V) :
    Set.EqOn (Function.uncurry (Work.Spaces.pth f)) (Function.uncurry (Work.Spaces.pth g)) V := by
  intro p hp
  obtain ⟨z, θ⟩ := p
  show deriv (fun θ' : ℝ => f z θ') θ = deriv (fun θ' : ℝ => g z θ') θ
  have hnb : ∀ᶠ θ' in 𝓝 θ, (z, θ') ∈ V :=
    (hV.preimage (continuous_const.prodMk continuous_id)).mem_nhds hp
  have hev : (fun θ' : ℝ => f z θ') =ᶠ[𝓝 θ] (fun θ' : ℝ => g z θ') := by
    filter_upwards [hnb] with θ' hθ'
    exact h hθ'
  rw [hev.deriv_eq]

private lemma ae_restrict_Iz_of_Ioi {p : ℝ → Prop}
    (h : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)), p z) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), p z := by
  rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl,
    ← MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))]
  exact h

private lemma ae_Ioi_of_forall {p : ℝ → Prop} (h : ∀ z : ℝ, 0 < z → p z) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)), p z :=
  MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi h

/-- `smoothOrder`-smoothness is `C^n`-smoothness for every finite `n`. -/
private lemma cutoff_smooth_all {χ : ℕ → ℝ → ℝ}
    (hχ : ∀ k : ℕ, ContDiffOn ℝ Work.Stability.smoothOrder (χ k) (Set.Ioi (0 : ℝ))) (k : ℕ) :
    ∀ n : ℕ, ContDiffOn ℝ n (χ k) (Set.Ioi 0) :=
  fun n => contDiffOn_infty.mp (hχ k) n

/-- The truncated function is smooth on the strip. -/
private lemma trunc_smooth {G : ℝ → ℝ → ℝ}
    (hs : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G) ThetaU.OStrip)
    {χ : ℕ → ℝ → ℝ} (hχ : ∀ k n : ℕ, ContDiffOn ℝ n (χ k) (Set.Ioi 0)) (k : ℕ) :
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (trunc χ G k)) ThetaU.OStrip := by
  intro n
  have h1 : ContDiffOn ℝ n (fun p : ℝ × ℝ => χ k p.1) ThetaU.OStrip :=
    (hχ k n).comp contDiffOn_fst (fun p hp => hp.1)
  have h2 : ContDiffOn ℝ n (Function.uncurry (zPosExt G)) ThetaU.OStrip := zPosExt_smooth hs n
  show ContDiffOn ℝ n (fun p : ℝ × ℝ => χ k p.1 * zPosExt G p.1 p.2) ThetaU.OStrip
  exact h1.mul h2

/-- The truncation vanishes off the radial box `[1/((k+2)²), ((k+2)²)]`. -/
private lemma trunc_supp {G : ℝ → ℝ → ℝ} {χ : ℕ → ℝ → ℝ}
    (hvan : ∀ k : ℕ, ∀ z : ℝ, 0 < z →
      (z ≤ 1 / ((k : ℝ) + 1) ^ 2 ∨ ((k : ℝ) + 1) ^ 2 ≤ z) → χ k z = 0) (k : ℕ) :
    ∀ z : ℝ, z ∉ Set.Icc (1 / ((k : ℝ) + 2) ^ 2) (((k : ℝ) + 2) ^ 2) →
      ∀ θ : ℝ, trunc χ G k z θ = 0 := by
  intro z hz θ
  have hlt : z < 1 / ((k : ℝ) + 2) ^ 2 ∨ ((k : ℝ) + 2) ^ 2 < z := by
    by_contra h
    push_neg at h
    exact hz ⟨h.1, h.2⟩
  by_cases hz0 : 0 < z
  · have hk1 : (0 : ℝ) < ((k : ℝ) + 1) ^ 2 := by positivity
    have hle1 : 1 / ((k : ℝ) + 2) ^ 2 ≤ 1 / ((k : ℝ) + 1) ^ 2 :=
      one_div_le_one_div_of_le hk1
        (by nlinarith [show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k])
    have hle2 : ((k : ℝ) + 1) ^ 2 ≤ ((k : ℝ) + 2) ^ 2 :=
      by nlinarith [show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k]
    have hle : z ≤ 1 / ((k : ℝ) + 1) ^ 2 ∨ ((k : ℝ) + 1) ^ 2 ≤ z := by
      rcases hlt with h | h
      · exact Or.inl (le_trans (le_of_lt h) hle1)
      · exact Or.inr (le_trans hle2 (le_of_lt h))
    show χ k z * zPosExt G z θ = 0
    rw [hvan k z hz0 hle, zero_mul]
  · show χ k z * zPosExt G z θ = 0
    rw [zPosExt_of_nonpos (G := G) (z := z) (θ := θ) hz0, mul_zero]

/-! ### Transport of the truncation along the strip -/

private lemma trunc_eq_pt (G : ℝ → ℝ → ℝ) (χ : ℕ → ℝ → ℝ) (k : ℕ) :
    ∀ z θ : ℝ, (z, θ) ∈ ThetaU.OStrip → trunc χ G k z θ = χ k z * G z θ := by
  intro z θ hmem
  show χ k z * zPosExt G z θ = χ k z * G z θ
  rw [zPosExt_of_pos (G := G) (θ := θ) hmem.1]

private lemma trunc_eq_curry (G : ℝ → ℝ → ℝ) (χ : ℕ → ℝ → ℝ) (k : ℕ) :
    Set.EqOn (Function.uncurry (trunc χ G k))
      (Function.uncurry (fun z θ => χ k z * G z θ)) ThetaU.OStrip :=
  eqOn_curry (trunc_eq_pt G χ k)

private lemma pth_trunc_eq_pt (G : ℝ → ℝ → ℝ) (χ : ℕ → ℝ → ℝ) (k : ℕ) :
    ∀ z θ : ℝ, (z, θ) ∈ ThetaU.OStrip →
      Work.Spaces.pth (trunc χ G k) z θ
        = Work.Spaces.pth (fun z θ => χ k z * G z θ) z θ :=
  fun z θ hmem => eqOn_apply (pth_congr_on ThetaU.isOpen_OStrip (trunc_eq_curry G χ k)) hmem

private lemma Dz_trunc_eq_pt (G : ℝ → ℝ → ℝ) (χ : ℕ → ℝ → ℝ) (k : ℕ) :
    ∀ z θ : ℝ, (z, θ) ∈ ThetaU.OStrip →
      Work.Spaces.Dz (trunc χ G k) z θ
        = Work.Spaces.Dz (fun z θ => χ k z * G z θ) z θ :=
  fun z θ hmem => eqOn_apply (Dz_congr_on ThetaU.isOpen_OStrip (trunc_eq_curry G χ k)) hmem

private lemma DzDz_trunc_eq_pt (G : ℝ → ℝ → ℝ) (χ : ℕ → ℝ → ℝ) (k : ℕ) :
    ∀ z θ : ℝ, (z, θ) ∈ ThetaU.OStrip →
      Work.Spaces.Dz (Work.Spaces.Dz (trunc χ G k)) z θ
        = Work.Spaces.Dz (Work.Spaces.Dz (fun z θ => χ k z * G z θ)) z θ :=
  fun z θ hmem =>
    eqOn_apply (Dz_congr_on ThetaU.isOpen_OStrip (eqOn_curry (Dz_trunc_eq_pt G χ k))) hmem



/-! ### The value of the operators on the truncation -/


private lemma Dz_truncV (G : ℝ → ℝ → ℝ) (χ : ℕ → ℝ → ℝ) (k : ℕ)
    (hs : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G) ThetaU.OStrip)
    (hχ : ∀ k n : ℕ, ContDiffOn ℝ n (χ k) (Set.Ioi 0))
    {z θ : ℝ} (hmem : (z, θ) ∈ ThetaU.OStrip) :
    Work.Spaces.Dz (trunc χ G k) z θ
      = χ k z * Work.Spaces.Dz G z θ + zeta χ k z * G z θ := by
  rw [Dz_trunc_eq_pt G χ k z θ hmem]
  rw [Dz_mul_z (F := G) hs (hχ k) hmem]
  rfl

private lemma Dz_mul_eq_pt (G : ℝ → ℝ → ℝ) (χ : ℕ → ℝ → ℝ) (k : ℕ)
    (hs : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G) ThetaU.OStrip)
    (hχ : ∀ k n : ℕ, ContDiffOn ℝ n (χ k) (Set.Ioi 0)) :
    ∀ z θ : ℝ, (z, θ) ∈ ThetaU.OStrip →
      Work.Spaces.Dz (fun z θ => χ k z * G z θ) z θ
        = χ k z * Work.Spaces.Dz G z θ + zeta χ k z * G z θ := by
  intro z θ hmem
  rw [Dz_mul_z (F := G) hs (hχ k) hmem]
  rfl

private lemma Dz_mul_eq_curry (G : ℝ → ℝ → ℝ) (χ : ℕ → ℝ → ℝ) (k : ℕ)
    (hs : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G) ThetaU.OStrip)
    (hχ : ∀ k n : ℕ, ContDiffOn ℝ n (χ k) (Set.Ioi 0)) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dz (fun z θ => χ k z * G z θ)))
      (Function.uncurry (fun z θ => χ k z * Work.Spaces.Dz G z θ
        + zeta χ k z * G z θ)) ThetaU.OStrip :=
  eqOn_curry (Dz_mul_eq_pt G χ k hs hχ)

private lemma DzDz_truncV (G : ℝ → ℝ → ℝ) (χ : ℕ → ℝ → ℝ) (k : ℕ)
    (hs : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G) ThetaU.OStrip)
    (hχ : ∀ k n : ℕ, ContDiffOn ℝ n (χ k) (Set.Ioi 0))
    {z θ : ℝ} (hmem : (z, θ) ∈ ThetaU.OStrip) :
    Work.Spaces.Dz (Work.Spaces.Dz (trunc χ G k)) z θ
      = χ k z * Work.Spaces.Dz (Work.Spaces.Dz G) z θ
        + 2 * zeta χ k z * Work.Spaces.Dz G z θ + xi χ k z * G z θ := by
  rw [DzDz_trunc_eq_pt G χ k z θ hmem]
  rw [DzDz_mul_z (F := G) hs (hχ k) hmem]
  rfl

private lemma pthDz_truncV (G : ℝ → ℝ → ℝ) (χ : ℕ → ℝ → ℝ) (k : ℕ)
    (hs : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G) ThetaU.OStrip)
    (hχ : ∀ k n : ℕ, ContDiffOn ℝ n (χ k) (Set.Ioi 0))
    {z θ : ℝ} (hmem : (z, θ) ∈ ThetaU.OStrip) :
    Work.Spaces.pth (Work.Spaces.Dz (trunc χ G k)) z θ
      = χ k z * Work.Spaces.pth (Work.Spaces.Dz G) z θ
        + zeta χ k z * Work.Spaces.pth G z θ := by
  have hd1 : DifferentiableAt ℝ (fun θ' : ℝ => χ k z * Work.Spaces.Dz G z θ') θ :=
    (diffAt_slice_of_strip (fun n => ThetaU.contDiffOn_uncurry_Dz_fin (hs (n + 1))) hmem).const_mul _
  have hd2 : DifferentiableAt ℝ (fun θ' : ℝ => zeta χ k z * G z θ') θ :=
    (diffAt_slice_of_strip hs hmem).const_mul _
  show deriv (fun θ' : ℝ => Work.Spaces.Dz (trunc χ G k) z θ') θ
      = χ k z * Work.Spaces.pth (Work.Spaces.Dz G) z θ + zeta χ k z * Work.Spaces.pth G z θ
  have hev1 : (fun θ' : ℝ => Work.Spaces.Dz (trunc χ G k) z θ')
      =ᶠ[𝓝 θ] (fun θ' : ℝ => χ k z * Work.Spaces.Dz G z θ' + zeta χ k z * G z θ') := by
    filter_upwards [eventually_strip_snd hmem] with θ' hθ'
    rw [Dz_trunc_eq_pt G χ k z θ' hθ', eqOn_apply (Dz_mul_eq_curry G χ k hs hχ) hθ']
  rw [hev1.deriv_eq,
    show (fun θ' : ℝ => χ k z * Work.Spaces.Dz G z θ' + zeta χ k z * G z θ')
      = (fun θ' : ℝ => χ k z * Work.Spaces.Dz G z θ')
        + (fun θ' : ℝ => zeta χ k z * G z θ') from rfl,
    deriv_add hd1 hd2, deriv_const_mul_field, deriv_const_mul_field]
  rfl

private lemma pthpth_truncV (G : ℝ → ℝ → ℝ) (χ : ℕ → ℝ → ℝ) (k : ℕ)
    (hs : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G) ThetaU.OStrip)
    {z θ : ℝ} (hmem : (z, θ) ∈ ThetaU.OStrip) :
    Work.Spaces.pth (Work.Spaces.pth (trunc χ G k)) z θ
      = χ k z * Work.Spaces.pth (Work.Spaces.pth G) z θ := by
  show deriv (fun θ' : ℝ => Work.Spaces.pth (trunc χ G k) z θ') θ
      = χ k z * deriv (fun θ' : ℝ => Work.Spaces.pth G z θ') θ
  have hev2 : (fun θ' : ℝ => Work.Spaces.pth (trunc χ G k) z θ')
      =ᶠ[𝓝 θ] (fun θ' : ℝ => Work.Spaces.pth (fun z θ => χ k z * G z θ) z θ') := by
    filter_upwards [eventually_strip_snd hmem] with θ' hθ'
    exact pth_trunc_eq_pt G χ k z θ' hθ'
  have hev1 : (fun θ' : ℝ => Work.Spaces.pth (fun z θ => χ k z * G z θ) z θ')
      =ᶠ[𝓝 θ] (fun θ' : ℝ => χ k z * Work.Spaces.pth G z θ') := by
    filter_upwards [eventually_strip_snd hmem] with θ' hθ'
    exact pth_mul_z (F := G) hs hθ'
  rw [hev2.deriv_eq, hev1.deriv_eq, deriv_const_mul_field]

private lemma pthDz_eq_pt (G : ℝ → ℝ → ℝ)
    (hs : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G) ThetaU.OStrip)
    {z θ : ℝ} (hmem : (z, θ) ∈ ThetaU.OStrip) :
    Work.Spaces.pth (Work.Spaces.Dz G) z θ = Work.Spaces.Dz (Work.Spaces.pth G) z θ :=
  ThetaU.pth_Dz_eq ((hs 2).contDiffAt (ThetaU.isOpen_OStrip.mem_nhds hmem))

/-- The `D_z∂_θ` of the truncation, written with `D_z∂_θG`. -/
private lemma Dz_pth_truncV (G : ℝ → ℝ → ℝ) (χ : ℕ → ℝ → ℝ) (k : ℕ)
    (hs : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G) ThetaU.OStrip)
    (hχ : ∀ k n : ℕ, ContDiffOn ℝ n (χ k) (Set.Ioi 0))
    {z θ : ℝ} (hmem : (z, θ) ∈ ThetaU.OStrip) :
    Work.Spaces.Dz (Work.Spaces.pth (trunc χ G k)) z θ
      = χ k z * Work.Spaces.Dz (Work.Spaces.pth G) z θ
        + zeta χ k z * Work.Spaces.pth G z θ := by
  have hcd : ContDiffAt ℝ 2 (Function.uncurry (trunc χ G k)) (z, θ) :=
    (trunc_smooth hs hχ k 2).contDiffAt (ThetaU.isOpen_OStrip.mem_nhds hmem)
  rw [← ThetaU.pth_Dz_eq (G := trunc χ G k) (z := z) (θ := θ) hcd]
  rw [pthDz_truncV G χ k hs hχ hmem, pthDz_eq_pt G hs hmem]

/-! ### The angular slice inequalities -/

/-- **Lower bound for the square of a two-term sum**, integrated against `σ_η`. -/
private lemma slice_sq_lower {A B : ℝ → ℝ} (hA : ContinuousOn A Work.Spaces.Iθ)
    (hB : ContinuousOn B Work.Spaces.Iθ) (κ ζ : ℝ) :
    (1 / 2) * κ ^ 2 * (∫ θ in Work.Spaces.Iθ, A θ ^ 2 * Work.FTS.EllipticEst.thEta θ)
      - ζ ^ 2 * (∫ θ in Work.Spaces.Iθ, B θ ^ 2 * Work.FTS.EllipticEst.thEta θ)
      ≤ ∫ θ in Work.Spaces.Iθ,
          (κ * A θ + ζ * B θ) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      (1 / 2) * (κ * A θ) ^ 2 - (ζ * B θ) ^ 2 ≤ (κ * A θ + ζ * B θ) ^ 2 := by
    intro θ _
    nlinarith [sq_nonneg (κ * A θ + 2 * (ζ * B θ))]
  have hIA : MeasureTheory.IntegrableOn
      (fun θ : ℝ => ((1 / 2) * (κ * A θ) ^ 2 - (ζ * B θ) ^ 2)
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ :=
    integrableOn_mul_thEta
      ((((hA.const_mul κ).pow 2).const_mul (1 / 2)).sub ((hB.const_mul ζ).pow 2))
  have hIB : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (κ * A θ + ζ * B θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ :=
    integrableOn_mul_thEta (((hA.const_mul κ).add (hB.const_mul ζ)).pow 2)
  have hmono : (∫ θ in Work.Spaces.Iθ,
        ((1 / 2) * (κ * A θ) ^ 2 - (ζ * B θ) ^ 2) * Work.FTS.EllipticEst.thEta θ)
      ≤ ∫ θ in Work.Spaces.Iθ,
          (κ * A θ + ζ * B θ) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
    refine MeasureTheory.integral_mono_ae hIA hIB ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    exact mul_le_mul_of_nonneg_right (hpt θ hθ) (Work.FTS.EllipticEst.thEta_nonneg hθ)
  have hsplit : (∫ θ in Work.Spaces.Iθ,
        ((1 / 2) * (κ * A θ) ^ 2 - (ζ * B θ) ^ 2) * Work.FTS.EllipticEst.thEta θ)
      = (1 / 2) * κ ^ 2
          * (∫ θ in Work.Spaces.Iθ, A θ ^ 2 * Work.FTS.EllipticEst.thEta θ)
        - ζ ^ 2 * (∫ θ in Work.Spaces.Iθ, B θ ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
    rw [show (fun θ : ℝ => ((1 / 2) * (κ * A θ) ^ 2 - (ζ * B θ) ^ 2)
          * Work.FTS.EllipticEst.thEta θ)
        = (fun θ : ℝ => (1 / 2) * κ ^ 2 * (A θ ^ 2 * Work.FTS.EllipticEst.thEta θ)
            - ζ ^ 2 * (B θ ^ 2 * Work.FTS.EllipticEst.thEta θ)) from by funext θ; ring]
    rw [MeasureTheory.integral_sub
      (f := fun θ : ℝ => (1 / 2) * κ ^ 2 * (A θ ^ 2 * Work.FTS.EllipticEst.thEta θ))
      (g := fun θ : ℝ => ζ ^ 2 * (B θ ^ 2 * Work.FTS.EllipticEst.thEta θ))
      ((integrableOn_mul_thEta (hA.pow 2)).const_mul _)
      ((integrableOn_mul_thEta (hB.pow 2)).const_mul _)]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  linarith [hmono, hsplit]

/-- **Upper bound for the square of a two-term sum**, integrated against `σ_η`. -/
private lemma slice_sq_upper2 {A B : ℝ → ℝ} (hA : ContinuousOn A Work.Spaces.Iθ)
    (hB : ContinuousOn B Work.Spaces.Iθ) (κ ζ : ℝ) :
    (∫ θ in Work.Spaces.Iθ,
        (κ * A θ + ζ * B θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      ≤ 2 * κ ^ 2 * (∫ θ in Work.Spaces.Iθ, A θ ^ 2 * Work.FTS.EllipticEst.thEta θ)
        + 2 * ζ ^ 2 * (∫ θ in Work.Spaces.Iθ, B θ ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      (κ * A θ + ζ * B θ) ^ 2 ≤ 2 * (κ * A θ) ^ 2 + 2 * (ζ * B θ) ^ 2 := by
    intro θ _
    nlinarith [sq_nonneg (κ * A θ - ζ * B θ)]
  have hIA : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (κ * A θ + ζ * B θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ :=
    integrableOn_mul_thEta (((hA.const_mul κ).add (hB.const_mul ζ)).pow 2)
  have hIB : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (2 * (κ * A θ) ^ 2 + 2 * (ζ * B θ) ^ 2)
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ :=
    integrableOn_mul_thEta
      ((((hA.const_mul κ).pow 2).const_mul 2).add (((hB.const_mul ζ).pow 2).const_mul 2))
  have hmono : (∫ θ in Work.Spaces.Iθ,
        (κ * A θ + ζ * B θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      ≤ ∫ θ in Work.Spaces.Iθ,
          (2 * (κ * A θ) ^ 2 + 2 * (ζ * B θ) ^ 2) * Work.FTS.EllipticEst.thEta θ := by
    refine MeasureTheory.integral_mono_ae hIA hIB ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    exact mul_le_mul_of_nonneg_right (hpt θ hθ) (Work.FTS.EllipticEst.thEta_nonneg hθ)
  have hsplit : (∫ θ in Work.Spaces.Iθ,
        (2 * (κ * A θ) ^ 2 + 2 * (ζ * B θ) ^ 2) * Work.FTS.EllipticEst.thEta θ)
      = 2 * κ ^ 2 * (∫ θ in Work.Spaces.Iθ, A θ ^ 2 * Work.FTS.EllipticEst.thEta θ)
        + 2 * ζ ^ 2 * (∫ θ in Work.Spaces.Iθ, B θ ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
    rw [show (fun θ : ℝ => (2 * (κ * A θ) ^ 2 + 2 * (ζ * B θ) ^ 2)
          * Work.FTS.EllipticEst.thEta θ)
        = (fun θ : ℝ => 2 * κ ^ 2 * (A θ ^ 2 * Work.FTS.EllipticEst.thEta θ)
            + 2 * ζ ^ 2 * (B θ ^ 2 * Work.FTS.EllipticEst.thEta θ)) from by funext θ; ring]
    rw [MeasureTheory.integral_add
      (f := fun θ : ℝ => 2 * κ ^ 2 * (A θ ^ 2 * Work.FTS.EllipticEst.thEta θ))
      (g := fun θ : ℝ => 2 * ζ ^ 2 * (B θ ^ 2 * Work.FTS.EllipticEst.thEta θ))
      ((integrableOn_mul_thEta (hA.pow 2)).const_mul _)
      ((integrableOn_mul_thEta (hB.pow 2)).const_mul _)]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  linarith [hmono, hsplit]

/-- **Upper bound for the square of a three-term sum**, integrated against `σ_η`. -/
private lemma slice_sq_upper3 {A B C : ℝ → ℝ} (hA : ContinuousOn A Work.Spaces.Iθ)
    (hB : ContinuousOn B Work.Spaces.Iθ) (hC : ContinuousOn C Work.Spaces.Iθ)
    (κ ζ ξ : ℝ) :
    (∫ θ in Work.Spaces.Iθ,
        (κ * A θ + 2 * ζ * B θ + ξ * C θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      ≤ 3 * κ ^ 2 * (∫ θ in Work.Spaces.Iθ, A θ ^ 2 * Work.FTS.EllipticEst.thEta θ)
        + 12 * ζ ^ 2 * (∫ θ in Work.Spaces.Iθ, B θ ^ 2 * Work.FTS.EllipticEst.thEta θ)
        + 3 * ξ ^ 2 * (∫ θ in Work.Spaces.Iθ, C θ ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      (κ * A θ + 2 * ζ * B θ + ξ * C θ) ^ 2
        ≤ 3 * ((κ * A θ) ^ 2 + (2 * ζ * B θ) ^ 2 + (ξ * C θ) ^ 2) := by
    intro θ _
    nlinarith [sq_nonneg (κ * A θ - 2 * ζ * B θ), sq_nonneg (2 * ζ * B θ - ξ * C θ),
      sq_nonneg (κ * A θ - ξ * C θ)]
  have hIA : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (κ * A θ + 2 * ζ * B θ + ξ * C θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ :=
    integrableOn_mul_thEta
      ((((hA.const_mul κ).add ((hB.const_mul (2 * ζ)))).add (hC.const_mul ξ)).pow 2)
  have hIB : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (3 * ((κ * A θ) ^ 2 + (2 * ζ * B θ) ^ 2 + (ξ * C θ) ^ 2))
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ :=
    integrableOn_mul_thEta
      (((((hA.const_mul κ).pow 2).add ((hB.const_mul (2 * ζ)).pow 2)).add
        ((hC.const_mul ξ).pow 2)).const_mul 3)
  have hmono : (∫ θ in Work.Spaces.Iθ,
        (κ * A θ + 2 * ζ * B θ + ξ * C θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      ≤ ∫ θ in Work.Spaces.Iθ,
          (3 * ((κ * A θ) ^ 2 + (2 * ζ * B θ) ^ 2 + (ξ * C θ) ^ 2))
            * Work.FTS.EllipticEst.thEta θ := by
    refine MeasureTheory.integral_mono_ae hIA hIB ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    exact mul_le_mul_of_nonneg_right (hpt θ hθ) (Work.FTS.EllipticEst.thEta_nonneg hθ)
  have hsplit : (∫ θ in Work.Spaces.Iθ,
        (3 * ((κ * A θ) ^ 2 + (2 * ζ * B θ) ^ 2 + (ξ * C θ) ^ 2))
          * Work.FTS.EllipticEst.thEta θ)
      = 3 * κ ^ 2 * (∫ θ in Work.Spaces.Iθ, A θ ^ 2 * Work.FTS.EllipticEst.thEta θ)
        + 12 * ζ ^ 2 * (∫ θ in Work.Spaces.Iθ, B θ ^ 2 * Work.FTS.EllipticEst.thEta θ)
        + 3 * ξ ^ 2 * (∫ θ in Work.Spaces.Iθ, C θ ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
    rw [show (fun θ : ℝ => (3 * ((κ * A θ) ^ 2 + (2 * ζ * B θ) ^ 2 + (ξ * C θ) ^ 2))
          * Work.FTS.EllipticEst.thEta θ)
        = (fun θ : ℝ => (3 * κ ^ 2 * (A θ ^ 2 * Work.FTS.EllipticEst.thEta θ)
            + 12 * ζ ^ 2 * (B θ ^ 2 * Work.FTS.EllipticEst.thEta θ))
            + 3 * ξ ^ 2 * (C θ ^ 2 * Work.FTS.EllipticEst.thEta θ)) from by funext θ; ring]
    rw [MeasureTheory.integral_add
      (f := fun θ : ℝ => 3 * κ ^ 2 * (A θ ^ 2 * Work.FTS.EllipticEst.thEta θ)
        + 12 * ζ ^ 2 * (B θ ^ 2 * Work.FTS.EllipticEst.thEta θ))
      (g := fun θ : ℝ => 3 * ξ ^ 2 * (C θ ^ 2 * Work.FTS.EllipticEst.thEta θ))
      (((integrableOn_mul_thEta (hA.pow 2)).const_mul _).add
        ((integrableOn_mul_thEta (hB.pow 2)).const_mul _))
      ((integrableOn_mul_thEta (hC.pow 2)).const_mul _)]
    rw [MeasureTheory.integral_add
      (f := fun θ : ℝ => 3 * κ ^ 2 * (A θ ^ 2 * Work.FTS.EllipticEst.thEta θ))
      (g := fun θ : ℝ => 12 * ζ ^ 2 * (B θ ^ 2 * Work.FTS.EllipticEst.thEta θ))
      ((integrableOn_mul_thEta (hA.pow 2)).const_mul _)
      ((integrableOn_mul_thEta (hB.pow 2)).const_mul _)]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
  linarith [hmono, hsplit]


/-! ### Nonnegativity of the slice functionals -/

private lemma mixFun_nonneg (G : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ mixFun G z := by
  unfold mixFun
  exact mul_nonneg (sq_nonneg _) (MeasureTheory.setIntegral_nonneg measurableSet_Icc
    (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)))

private lemma ddFun_nonneg (G : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ ddFun G z := by
  unfold ddFun
  exact mul_nonneg (sq_nonneg _) (MeasureTheory.setIntegral_nonneg measurableSet_Icc
    (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)))

private lemma ttFun_nonneg (G : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ ttFun G z := by
  unfold ttFun
  exact mul_nonneg (sq_nonneg _) (MeasureTheory.setIntegral_nonneg measurableSet_Icc
    (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)))

private lemma dFun_nonneg (G : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ dFun G z := by
  unfold dFun
  exact mul_nonneg (sq_nonneg _) (MeasureTheory.setIntegral_nonneg measurableSet_Icc
    (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)))




private lemma ZTt_nonneg (G : ℝ → ℝ → ℝ) : 0 ≤ ZTt G := by
  unfold ZTt
  exact MeasureTheory.setIntegral_nonneg measurableSet_Ici (fun z _ => ttFun_nonneg G z)

private lemma ZD_nonneg (G : ℝ → ℝ → ℝ) : 0 ≤ ZD G := by
  unfold ZD
  exact MeasureTheory.setIntegral_nonneg measurableSet_Ici (fun z _ => dFun_nonneg G z)


/-- A.e. strong measurability of the squared cut-off on `I_z`. -/
private lemma aestronglyMeasurable_chi_sq {χ : ℕ → ℝ → ℝ}
    (hχ : ∀ k n : ℕ, ContDiffOn ℝ n (χ k) (Set.Ioi 0)) (k : ℕ) :
    AEStronglyMeasurable (fun z : ℝ => (χ k z) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  show AEStronglyMeasurable (fun z : ℝ => (χ k z) ^ 2)
    (MeasureTheory.volume.restrict (Set.Ici (0 : ℝ)))
  rw [← MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))]
  exact ((hχ k 1).continuousOn.pow 2).aestronglyMeasurable measurableSet_Ioi

/-! ### The pointwise comparison of the truncated functionals -/

/-- **The truncated `mixFun` dominates `(1/2)χ²mixFun G` up to the correction `ζ²Bfun G`.** -/
private lemma mixFun_compare (G : ℝ → ℝ → ℝ) (χ : ℕ → ℝ → ℝ) (k : ℕ)
    (hs : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G) ThetaU.OStrip)
    (hχ : ∀ k n : ℕ, ContDiffOn ℝ n (χ k) (Set.Ioi 0))
    {z : ℝ} (hz : 0 < z) :
    (1 / 2) * (χ k z) ^ 2 * mixFun G z
      ≤ mixFun (trunc χ G k) z + (zeta χ k z) ^ 2 * Bfun G z := by
  have hmemb : ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ → (z, θ) ∈ ThetaU.OStrip :=
    fun θ hθ => ⟨hz, ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩⟩
  have hAcont : ContinuousOn (fun θ : ℝ => Work.Spaces.Dz (Work.Spaces.pth G) z θ)
      Work.Spaces.Iθ := by
    have hc : ContinuousOn
        (Function.uncurry (fun z θ => Work.Spaces.Dz (Work.Spaces.pth G) z θ)) ThetaU.OStrip :=
      (ThetaU.contDiffOn_uncurry_Dz_fin
        (ThetaU.contDiffOn_uncurry_pth_fin (n := 1) (hs 2))).continuousOn
    exact hc.comp (continuousOn_const.prodMk continuousOn_id) (fun θ hθ => hmemb θ hθ)
  have hBcont : ContinuousOn (fun θ : ℝ => Work.Spaces.pth G z θ) Work.Spaces.Iθ := by
    have hc : ContinuousOn
        (Function.uncurry (fun z θ => Work.Spaces.pth G z θ)) ThetaU.OStrip :=
      (ThetaU.contDiffOn_uncurry_pth_fin (n := 1) (hs 2)).continuousOn
    exact hc.comp (continuousOn_const.prodMk continuousOn_id) (fun θ hθ => hmemb θ hθ)
  have hkey := slice_sq_lower hAcont hBcont (χ k z) (zeta χ k z)
  have hident : ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.Dz (Work.Spaces.pth (trunc χ G k)) z θ
        = χ k z * Work.Spaces.Dz (Work.Spaces.pth G) z θ
          + zeta χ k z * Work.Spaces.pth G z θ :=
    fun θ hθ => Dz_pth_truncV G χ k hs hχ (hmemb θ hθ)
  have hmixTrunc : mixFun (trunc χ G k) z
      = (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
          (χ k z * Work.Spaces.Dz (Work.Spaces.pth G) z θ
              + zeta χ k z * Work.Spaces.pth G z θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ) := by
    unfold mixFun
    congr 1
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    rw [hident θ hθ]
  have hw := mul_le_mul_of_nonneg_left hkey (sq_nonneg (Work.Spaces.w z))
  rw [← hmixTrunc] at hw
  have hL : (Work.Spaces.w z) ^ 2 * ((1 / 2) * (χ k z) ^ 2
        * (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ)
      - (zeta χ k z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pth G z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))
      = (1 / 2) * (χ k z) ^ 2 * mixFun G z - (zeta χ k z) ^ 2 * Bfun G z := by
    unfold mixFun Bfun
    ring
  rw [hL] at hw
  linarith [hw]

/-- **The truncated `ddFun` is bounded by the three untruncated functionals.** -/
private lemma ddFun_compare (G : ℝ → ℝ → ℝ) (χ : ℕ → ℝ → ℝ) (k : ℕ)
    (hs : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G) ThetaU.OStrip)
    (hχ : ∀ k n : ℕ, ContDiffOn ℝ n (χ k) (Set.Ioi 0))
    {z : ℝ} (hz : 0 < z) :
    ddFun (trunc χ G k) z ≤ 3 * (χ k z) ^ 2 * ddFun G z
      + 12 * (zeta χ k z) ^ 2 * dFun G z + 3 * (xi χ k z) ^ 2 * Efun G z := by
  have hmemb : ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ → (z, θ) ∈ ThetaU.OStrip :=
    fun θ hθ => ⟨hz, ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩⟩
  have hAcont : ContinuousOn
      (fun θ : ℝ => Work.Spaces.Dz (Work.Spaces.Dz G) z θ) Work.Spaces.Iθ := by
    have hc : ContinuousOn
        (Function.uncurry (fun z θ => Work.Spaces.Dz (Work.Spaces.Dz G) z θ)) ThetaU.OStrip :=
      (ThetaU.contDiffOn_uncurry_Dz_fin (ThetaU.contDiffOn_uncurry_Dz_fin (n := 1) (hs 2))).continuousOn
    exact hc.comp (continuousOn_const.prodMk continuousOn_id) (fun θ hθ => hmemb θ hθ)
  have hBcont : ContinuousOn (fun θ : ℝ => Work.Spaces.Dz G z θ) Work.Spaces.Iθ := by
    have hc : ContinuousOn
        (Function.uncurry (fun z θ => Work.Spaces.Dz G z θ)) ThetaU.OStrip :=
      (ThetaU.contDiffOn_uncurry_Dz_fin (n := 1) (hs 2)).continuousOn
    exact hc.comp (continuousOn_const.prodMk continuousOn_id) (fun θ hθ => hmemb θ hθ)
  have hCcont : ContinuousOn (fun θ : ℝ => G z θ) Work.Spaces.Iθ := by
    have hc : ContinuousOn (Function.uncurry G) ThetaU.OStrip := (hs 1).continuousOn
    exact hc.comp (continuousOn_const.prodMk continuousOn_id) (fun θ hθ => hmemb θ hθ)
  have hkey := slice_sq_upper3 hAcont hBcont hCcont (χ k z) (zeta χ k z) (xi χ k z)
  have hident : ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.Dz (Work.Spaces.Dz (trunc χ G k)) z θ
        = χ k z * Work.Spaces.Dz (Work.Spaces.Dz G) z θ
          + 2 * zeta χ k z * Work.Spaces.Dz G z θ + xi χ k z * G z θ :=
    fun θ hθ => DzDz_truncV G χ k hs hχ (hmemb θ hθ)
  have hddTrunc : ddFun (trunc χ G k) z
      = (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
          (χ k z * Work.Spaces.Dz (Work.Spaces.Dz G) z θ
              + 2 * zeta χ k z * Work.Spaces.Dz G z θ + xi χ k z * G z θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ) := by
    unfold ddFun
    congr 1
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    rw [hident θ hθ]
  have hw := mul_le_mul_of_nonneg_left hkey (sq_nonneg (Work.Spaces.w z))
  rw [← hddTrunc] at hw
  have hR : (Work.Spaces.w z) ^ 2
        * (3 * (χ k z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2
                * Work.FTS.EllipticEst.thEta θ)
          + 12 * (zeta χ k z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.Dz G z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          + 3 * (xi χ k z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
              (G z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))
      = 3 * (χ k z) ^ 2 * ddFun G z + 12 * (zeta χ k z) ^ 2 * dFun G z
        + 3 * (xi χ k z) ^ 2 * Efun G z := by
    unfold ddFun dFun Efun
    ring
  linarith [hw, hR]

/-- **The truncated `ttFun` is bounded by `ttFun G`.** -/
private lemma ttFun_compare (G : ℝ → ℝ → ℝ) (χ : ℕ → ℝ → ℝ) (k : ℕ)
    (hs : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G) ThetaU.OStrip)
    (hχ01 : ∀ k : ℕ, ∀ z : ℝ, 0 < z → 0 ≤ χ k z ∧ χ k z ≤ 1)
    {z : ℝ} (hz : 0 < z) :
    ttFun (trunc χ G k) z ≤ ttFun G z := by
  have hmemb : ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ → (z, θ) ∈ ThetaU.OStrip :=
    fun θ hθ => ⟨hz, ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩⟩
  have hident : ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.pth (Work.Spaces.pth (trunc χ G k)) z θ
        = χ k z * Work.Spaces.pth (Work.Spaces.pth G) z θ :=
    fun θ hθ => pthpth_truncV G χ k hs (hmemb θ hθ)
  have httTrunc : ttFun (trunc χ G k) z
      = (Work.Spaces.w z) ^ 2 * ((χ k z) ^ 2
          * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2
                * Work.FTS.EllipticEst.thEta θ)) := by
    unfold ttFun
    rw [show (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pth (Work.Spaces.pth (trunc χ G k)) z θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ)
        = (∫ θ in Work.Spaces.Iθ,
            (χ k z * Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ) from by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
      rw [hident θ hθ]]
    rw [show (fun θ : ℝ => (χ k z * Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ)
        = (fun θ : ℝ => (χ k z) ^ 2
            * ((Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ)) from by funext θ; ring]
    rw [MeasureTheory.integral_const_mul]
  obtain ⟨hχ0, hχle⟩ := hχ01 k z hz
  have hsq : (χ k z) ^ 2 ≤ 1 := by
    have h := mul_self_le_mul_self hχ0 hχle
    nlinarith [h]
  have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ))
  have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have hG : ttFun G z = (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) :=
    rfl
  rw [httTrunc, hG]
  calc (Work.Spaces.w z) ^ 2 * ((χ k z) ^ 2
        * (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))
      = ((Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2
                * Work.FTS.EllipticEst.thEta θ)) * (χ k z) ^ 2 := by ring
    _ ≤ ((Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2
                * Work.FTS.EllipticEst.thEta θ)) * 1 :=
        mul_le_mul_of_nonneg_left hsq (mul_nonneg hw2 hnn)
    _ = (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2
                * Work.FTS.EllipticEst.thEta θ) := by ring

/-- **The truncated `dFun` is bounded by `2χ²dFun G + 2ζ²Efun G`.** -/
private lemma dFun_compare (G : ℝ → ℝ → ℝ) (χ : ℕ → ℝ → ℝ) (k : ℕ)
    (hs : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G) ThetaU.OStrip)
    (hχ : ∀ k n : ℕ, ContDiffOn ℝ n (χ k) (Set.Ioi 0))
    {z : ℝ} (hz : 0 < z) :
    dFun (trunc χ G k) z ≤ 2 * (χ k z) ^ 2 * dFun G z
      + 2 * (zeta χ k z) ^ 2 * Efun G z := by
  have hmemb : ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ → (z, θ) ∈ ThetaU.OStrip :=
    fun θ hθ => ⟨hz, ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩⟩
  have hAcont : ContinuousOn (fun θ : ℝ => Work.Spaces.Dz G z θ) Work.Spaces.Iθ := by
    have hc : ContinuousOn
        (Function.uncurry (fun z θ => Work.Spaces.Dz G z θ)) ThetaU.OStrip :=
      (ThetaU.contDiffOn_uncurry_Dz_fin (n := 1) (hs 2)).continuousOn
    exact hc.comp (continuousOn_const.prodMk continuousOn_id) (fun θ hθ => hmemb θ hθ)
  have hBcont : ContinuousOn (fun θ : ℝ => G z θ) Work.Spaces.Iθ := by
    have hc : ContinuousOn (Function.uncurry G) ThetaU.OStrip := (hs 1).continuousOn
    exact hc.comp (continuousOn_const.prodMk continuousOn_id) (fun θ hθ => hmemb θ hθ)
  have hkey := slice_sq_upper2 hAcont hBcont (χ k z) (zeta χ k z)
  have hident : ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.Dz (trunc χ G k) z θ
        = χ k z * Work.Spaces.Dz G z θ + zeta χ k z * G z θ :=
    fun θ hθ => Dz_truncV G χ k hs hχ (hmemb θ hθ)
  have hdTrunc : dFun (trunc χ G k) z
      = (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
          (χ k z * Work.Spaces.Dz G z θ + zeta χ k z * G z θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ) := by
    unfold dFun
    congr 1
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    rw [hident θ hθ]
  have hw := mul_le_mul_of_nonneg_left hkey (sq_nonneg (Work.Spaces.w z))
  rw [← hdTrunc] at hw
  have hR : (Work.Spaces.w z) ^ 2
        * (2 * (χ k z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.Dz G z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          + 2 * (zeta χ k z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
              (G z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))
      = 2 * (χ k z) ^ 2 * dFun G z + 2 * (zeta χ k z) ^ 2 * Efun G z := by
    unfold dFun Efun
    ring
  linarith [hw, hR]

/-! ## The target theorem -/

theorem interpS_theta : ∃ C : ℝ, 0 < C ∧ Work.EllipticEst.Core.i0Aux.InterpStrip C := by
  obtain ⟨C₀, hC₀pos, hzbox⟩ := interpStripZbox
  obtain ⟨CB, CE, hCB0, hCE0, hcorr⟩ := sliceCorrectionBounds
  obtain ⟨χ, K, hK0, hχsm, hχ01, hχvan, hχmono, hχlim, hζb, hξb⟩ :=
    Work.EllipticEst.Core.zLogCut
  have hχall : ∀ k n : ℕ, ContDiffOn ℝ n (χ k) (Set.Ioi 0) :=
    fun k n => cutoff_smooth_all hχsm k n
  refine ⟨6 * C₀, by positivity, ?_⟩
  intro α G hα hα4 hs h0 hpi hmixI0 hddI0 httI0 hdI0
  have hmixI : MeasureTheory.IntegrableOn (mixFun G) Work.Spaces.Iz :=
    mixIntS_eq_mixFun G ▸ hmixI0
  have hddI : MeasureTheory.IntegrableOn (ddFun G) Work.Spaces.Iz :=
    ddIntS_eq_ddFun G ▸ hddI0
  have httI : MeasureTheory.IntegrableOn (ttFun G) Work.Spaces.Iz :=
    ttIntS_eq_ttFun G ▸ httI0
  have hdI : MeasureTheory.IntegrableOn (dFun G) Work.Spaces.Iz :=
    dIntS_eq_dFun G ▸ hdI0
  -- ### elementary consequences of the cut-off bounds
  have hchi2 : ∀ (k : ℕ) (z : ℝ), 0 < z → (χ k z) ^ 2 ≤ 1 := by
    intro k z hz
    obtain ⟨h0', h1'⟩ := hχ01 k z hz
    have h := mul_self_le_mul_self h0' h1'
    nlinarith [h]
  have hcksq : ∀ (ζ : ℝ) (k : ℕ) (z : ℝ), 0 < z → |ζ| ≤ ck K k → ζ ^ 2 ≤ (ck K k) ^ 2 := by
    intro ζ k z hz h
    have h2 := abs_le.mp h
    nlinarith [h2.1, h2.2]
  have hBfun : ∀ z : ℝ, 0 < z → Bfun G z ≤ CB * ttFun G z :=
    fun z hz => (hcorr G hs h0 hpi z hz).1
  have hEfun : ∀ z : ℝ, 0 < z → Efun G z ≤ CE * ttFun G z :=
    fun z hz => (hcorr G hs h0 hpi z hz).2
  -- ### integrability of the truncated functionals
  have hintTrunc : ∀ k : ℕ, MeasureTheory.IntegrableOn (mixFun (trunc χ G k)) Work.Spaces.Iz
      ∧ MeasureTheory.IntegrableOn (ddFun (trunc χ G k)) Work.Spaces.Iz
      ∧ MeasureTheory.IntegrableOn (ttFun (trunc χ G k)) Work.Spaces.Iz
      ∧ MeasureTheory.IntegrableOn (dFun (trunc χ G k)) Work.Spaces.Iz := by
    intro k
    have hk2 : (2 : ℝ) ≤ (k : ℝ) + 2 := by linarith [show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k]
    have hsq : (4 : ℝ) ≤ ((k : ℝ) + 2) ^ 2 := by nlinarith [hk2]
    have hpos : (0 : ℝ) < ((k : ℝ) + 2) ^ 2 := by linarith
    have ha : (0 : ℝ) < 1 / ((k : ℝ) + 2) ^ 2 := by positivity
    have hle : 1 / ((k : ℝ) + 2) ^ 2 ≤ 1 := by
      rw [div_le_one hpos]
      linarith
    have hab : 1 / ((k : ℝ) + 2) ^ 2 < ((k : ℝ) + 2) ^ 2 := by linarith
    exact integrableOn_sliceFuns_of_zbox ha hab (trunc_smooth hs hχall k) (trunc_supp hχvan k)
  -- ### the per-`k` estimate
  have hperk : ∀ k : ℕ, (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz, (χ k z) ^ 2 * mixFun G z)
      ≤ C₀ * (3 * α ^ 4 * ZDd G + ZTt G + 2 * α ^ 2 * ZD G)
        + (ck K k) ^ 2 * (C₀ * (12 * α ^ 4 * ZD G + 3 * α ^ 4 * CE * ZTt G
              + 2 * α ^ 2 * CE * ZTt G)
            + α ^ 2 * CB * ZTt G) := by
    intro k
    obtain ⟨hI1, hI2, hI3, hI4⟩ := hintTrunc k
    -- boundary values of the truncation
    have hb0 : ∀ z : ℝ, trunc χ G k z 0 = 0 := by
      intro z
      by_cases hz0 : 0 < z
      · show χ k z * zPosExt G z 0 = 0
        rw [zPosExt_of_pos (G := G) (θ := 0) hz0, h0 z, mul_zero]
      · show χ k z * zPosExt G z 0 = 0
        rw [zPosExt_of_nonpos (G := G) (z := z) (θ := 0) hz0, mul_zero]
    have hbpi : ∀ z : ℝ, trunc χ G k z (Real.pi / 2) = 0 := by
      intro z
      by_cases hz0 : 0 < z
      · show χ k z * zPosExt G z (Real.pi / 2) = 0
        rw [zPosExt_of_pos (G := G) (θ := Real.pi / 2) hz0, hpi z, mul_zero]
      · show χ k z * zPosExt G z (Real.pi / 2) = 0
        rw [zPosExt_of_nonpos (G := G) (z := z) (θ := Real.pi / 2) hz0, mul_zero]
    -- the box-supported estimate
    have hbox : α ^ 2 * (∫ z in Work.Spaces.Iz, mixFun (trunc χ G k) z)
        ≤ C₀ * (α ^ 4 * (∫ z in Work.Spaces.Iz, ddFun (trunc χ G k) z)
            + (∫ z in Work.Spaces.Iz, ttFun (trunc χ G k) z)
            + α ^ 2 * (∫ z in Work.Spaces.Iz, dFun (trunc χ G k) z)) := by
      have hk2 : (2 : ℝ) ≤ (k : ℝ) + 2 := by linarith [show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k]
      have hsq : (4 : ℝ) ≤ ((k : ℝ) + 2) ^ 2 := by nlinarith [hk2]
      have hpos : (0 : ℝ) < ((k : ℝ) + 2) ^ 2 := by linarith
      have ha : (0 : ℝ) < 1 / ((k : ℝ) + 2) ^ 2 := by positivity
      have hle : 1 / ((k : ℝ) + 2) ^ 2 ≤ 1 := by
        rw [div_le_one hpos]
        linarith
      have hab : 1 / ((k : ℝ) + 2) ^ 2 < ((k : ℝ) + 2) ^ 2 := by linarith
      exact hzbox α (trunc χ G k) (1 / ((k : ℝ) + 2) ^ 2) (((k : ℝ) + 2) ^ 2)
        hα hα4 ha hab (trunc_smooth hs hχall k) hb0 hbpi (trunc_supp hχvan k)
    -- ### step 1: the mixed functional, from below
    have hpt1 : ∀ z : ℝ, 0 < z →
        (1 / 2) * ((χ k z) ^ 2 * mixFun G z)
          ≤ mixFun (trunc χ G k) z + (ck K k) ^ 2 * CB * ttFun G z := by
      intro z hz
      have h1 := mixFun_compare G χ k hs hχall hz
      have hζ : |zeta χ k z| ≤ ck K k := hζb k z hz
      have hζsq : (zeta χ k z) ^ 2 ≤ (ck K k) ^ 2 := hcksq (zeta χ k z) k z hz hζ
      have hB : Bfun G z ≤ CB * ttFun G z := hBfun z hz
      have hle : (zeta χ k z) ^ 2 * Bfun G z ≤ (ck K k) ^ 2 * CB * ttFun G z := by
        have h2 : (zeta χ k z) ^ 2 * Bfun G z ≤ (zeta χ k z) ^ 2 * (CB * ttFun G z) :=
          mul_le_mul_of_nonneg_left hB (sq_nonneg _)
        have h3 : (zeta χ k z) ^ 2 * (CB * ttFun G z) ≤ (ck K k) ^ 2 * (CB * ttFun G z) :=
          mul_le_mul_of_nonneg_right hζsq (mul_nonneg hCB0 (ttFun_nonneg G z))
        linarith [h2, h3]
      linarith [h1, hle]
    have hint1 : MeasureTheory.IntegrableOn
        (fun z : ℝ => (1 / 2) * ((χ k z) ^ 2 * mixFun G z)) Work.Spaces.Iz := by
      refine MeasureTheory.Integrable.mono' (hmixI.const_mul (1 / 2)) ?_ ?_
      · exact ((aestronglyMeasurable_chi_sq hχall k).mul
          hmixI.aestronglyMeasurable).const_mul (1 / 2)
      · refine ae_restrict_Iz_of_Ioi (ae_Ioi_of_forall (fun z hz => ?_))
        rw [Real.norm_of_nonneg (mul_nonneg (by norm_num)
          (mul_nonneg (sq_nonneg _) (mixFun_nonneg G z)))]
        have hM : 0 ≤ mixFun G z := mixFun_nonneg G z
        have hc : (χ k z) ^ 2 ≤ 1 := hchi2 k z hz
        have h1 : (χ k z) ^ 2 * mixFun G z ≤ mixFun G z := mul_le_of_le_one_left hM hc
        linarith [h1]
    have hint2 : MeasureTheory.IntegrableOn
        (fun z : ℝ => mixFun (trunc χ G k) z + (ck K k) ^ 2 * CB * ttFun G z)
        Work.Spaces.Iz :=
      hI1.add (httI.const_mul ((ck K k) ^ 2 * CB))
    have hstep1 : (1 / 2) * (∫ z in Work.Spaces.Iz, (χ k z) ^ 2 * mixFun G z)
        ≤ (∫ z in Work.Spaces.Iz, mixFun (trunc χ G k) z) + (ck K k) ^ 2 * CB * ZTt G := by
      have hmono := MeasureTheory.integral_mono_ae hint1 hint2
        (ae_restrict_Iz_of_Ioi (ae_Ioi_of_forall hpt1))
      rw [MeasureTheory.integral_const_mul] at hmono
      rw [MeasureTheory.integral_add (f := mixFun (trunc χ G k))
        (g := fun z : ℝ => (ck K k) ^ 2 * CB * ttFun G z)
        hI1 (httI.const_mul ((ck K k) ^ 2 * CB))] at hmono
      rw [MeasureTheory.integral_const_mul] at hmono
      exact hmono
    -- ### step 2: the second radial functional
    have hpt2 : ∀ z : ℝ, 0 < z →
        ddFun (trunc χ G k) z ≤ 3 * ddFun G z + 12 * (ck K k) ^ 2 * dFun G z
          + 3 * CE * (ck K k) ^ 2 * ttFun G z := by
      intro z hz
      have h1 := ddFun_compare G χ k hs hχall hz
      have hχsq : (χ k z) ^ 2 ≤ 1 := hchi2 k z hz
      have hζsq : (zeta χ k z) ^ 2 ≤ (ck K k) ^ 2 :=
        hcksq (zeta χ k z) k z hz (hζb k z hz)
      have hξsq : (xi χ k z) ^ 2 ≤ (ck K k) ^ 2 :=
        hcksq (xi χ k z) k z hz (hξb k z hz)
      have hE : Efun G z ≤ CE * ttFun G z := hEfun z hz
      have h2 : 3 * (χ k z) ^ 2 * ddFun G z ≤ 3 * ddFun G z := by
        have h := mul_le_of_le_one_left (ddFun_nonneg G z) hχsq
        linarith [h]
      have h3 : 12 * (zeta χ k z) ^ 2 * dFun G z ≤ 12 * (ck K k) ^ 2 * dFun G z := by
        have h := mul_le_mul_of_nonneg_right hζsq (dFun_nonneg G z)
        linarith [h]
      have h4 : 3 * (xi χ k z) ^ 2 * Efun G z ≤ 3 * CE * (ck K k) ^ 2 * ttFun G z := by
        have hE' : (xi χ k z) ^ 2 * Efun G z ≤ (ck K k) ^ 2 * (CE * ttFun G z) := by
          calc (xi χ k z) ^ 2 * Efun G z ≤ (xi χ k z) ^ 2 * (CE * ttFun G z) :=
                mul_le_mul_of_nonneg_left hE (sq_nonneg _)
            _ ≤ (ck K k) ^ 2 * (CE * ttFun G z) :=
                mul_le_mul_of_nonneg_right hξsq (mul_nonneg hCE0 (ttFun_nonneg G z))
        nlinarith [hE']
      linarith [h1, h2, h3, h4]
    have hint3 : MeasureTheory.IntegrableOn
        (fun z : ℝ => 3 * ddFun G z + 12 * (ck K k) ^ 2 * dFun G z
          + 3 * CE * (ck K k) ^ 2 * ttFun G z) Work.Spaces.Iz :=
      ((hddI.const_mul 3).add (hdI.const_mul (12 * (ck K k) ^ 2))).add
        (httI.const_mul (3 * CE * (ck K k) ^ 2))
    have hstep2 : (∫ z in Work.Spaces.Iz, ddFun (trunc χ G k) z)
        ≤ 3 * ZDd G + 12 * (ck K k) ^ 2 * ZD G + 3 * CE * (ck K k) ^ 2 * ZTt G := by
      have hmono := MeasureTheory.integral_mono_ae hI2 hint3
        (ae_restrict_Iz_of_Ioi (ae_Ioi_of_forall hpt2))
      rw [MeasureTheory.integral_add
        (f := fun z : ℝ => 3 * ddFun G z + 12 * (ck K k) ^ 2 * dFun G z)
        (g := fun z : ℝ => 3 * CE * (ck K k) ^ 2 * ttFun G z)
        ((hddI.const_mul 3).add (hdI.const_mul (12 * (ck K k) ^ 2)))
        (httI.const_mul (3 * CE * (ck K k) ^ 2))] at hmono
      rw [MeasureTheory.integral_add
        (f := fun z : ℝ => 3 * ddFun G z) (g := fun z : ℝ => 12 * (ck K k) ^ 2 * dFun G z)
        (hddI.const_mul 3) (hdI.const_mul (12 * (ck K k) ^ 2))] at hmono
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul] at hmono
      exact hmono
    -- ### step 3: the angular functional
    have hstep3 : (∫ z in Work.Spaces.Iz, ttFun (trunc χ G k) z) ≤ ZTt G :=
      MeasureTheory.integral_mono_ae hI3 httI
        (ae_restrict_Iz_of_Ioi (ae_Ioi_of_forall (fun z hz =>
          ttFun_compare G χ k hs hχ01 hz)))
    -- ### step 4: the first radial functional
    have hpt4 : ∀ z : ℝ, 0 < z →
        dFun (trunc χ G k) z ≤ 2 * dFun G z + 2 * CE * (ck K k) ^ 2 * ttFun G z := by
      intro z hz
      have h1 := dFun_compare G χ k hs hχall hz
      have hχsq : (χ k z) ^ 2 ≤ 1 := hchi2 k z hz
      have hζsq : (zeta χ k z) ^ 2 ≤ (ck K k) ^ 2 :=
        hcksq (zeta χ k z) k z hz (hζb k z hz)
      have hE : Efun G z ≤ CE * ttFun G z := hEfun z hz
      have h2 : 2 * (χ k z) ^ 2 * dFun G z ≤ 2 * dFun G z := by
        have h := mul_le_of_le_one_left (dFun_nonneg G z) hχsq
        linarith [h]
      have h3 : 2 * (zeta χ k z) ^ 2 * Efun G z ≤ 2 * CE * (ck K k) ^ 2 * ttFun G z := by
        have hE' : (zeta χ k z) ^ 2 * Efun G z ≤ (ck K k) ^ 2 * (CE * ttFun G z) := by
          calc (zeta χ k z) ^ 2 * Efun G z ≤ (zeta χ k z) ^ 2 * (CE * ttFun G z) :=
                mul_le_mul_of_nonneg_left hE (sq_nonneg _)
            _ ≤ (ck K k) ^ 2 * (CE * ttFun G z) :=
                mul_le_mul_of_nonneg_right hζsq (mul_nonneg hCE0 (ttFun_nonneg G z))
        nlinarith [hE']
      linarith [h1, h2, h3]
    have hint4 : MeasureTheory.IntegrableOn
        (fun z : ℝ => 2 * dFun G z + 2 * CE * (ck K k) ^ 2 * ttFun G z) Work.Spaces.Iz :=
      (hdI.const_mul 2).add (httI.const_mul (2 * CE * (ck K k) ^ 2))
    have hstep4 : (∫ z in Work.Spaces.Iz, dFun (trunc χ G k) z)
        ≤ 2 * ZD G + 2 * CE * (ck K k) ^ 2 * ZTt G := by
      have hmono := MeasureTheory.integral_mono_ae hI4 hint4
        (ae_restrict_Iz_of_Ioi (ae_Ioi_of_forall hpt4))
      rw [MeasureTheory.integral_add
        (f := fun z : ℝ => 2 * dFun G z)
        (g := fun z : ℝ => 2 * CE * (ck K k) ^ 2 * ttFun G z)
        (hdI.const_mul 2) (httI.const_mul (2 * CE * (ck K k) ^ 2))] at hmono
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hmono
      exact hmono
    -- ### assembly
    have hcomb : α ^ 2 * (∫ z in Work.Spaces.Iz, mixFun (trunc χ G k) z)
        ≤ C₀ * (3 * α ^ 4 * ZDd G + ZTt G + 2 * α ^ 2 * ZD G)
          + (ck K k) ^ 2 * (C₀ * (12 * α ^ 4 * ZD G + 3 * α ^ 4 * CE * ZTt G
                + 2 * α ^ 2 * CE * ZTt G)) := by
      have hA1 : α ^ 4 * (∫ z in Work.Spaces.Iz, ddFun (trunc χ G k) z)
          ≤ α ^ 4 * (3 * ZDd G + 12 * (ck K k) ^ 2 * ZD G
              + 3 * CE * (ck K k) ^ 2 * ZTt G) :=
        mul_le_mul_of_nonneg_left hstep2 (pow_nonneg (le_of_lt hα) 4)
      have hA2 : (∫ z in Work.Spaces.Iz, ttFun (trunc χ G k) z) ≤ ZTt G := hstep3
      have hA3 : α ^ 2 * (∫ z in Work.Spaces.Iz, dFun (trunc χ G k) z)
          ≤ α ^ 2 * (2 * ZD G + 2 * CE * (ck K k) ^ 2 * ZTt G) :=
        mul_le_mul_of_nonneg_left hstep4 (pow_nonneg (le_of_lt hα) 2)
      have hsum : α ^ 4 * (∫ z in Work.Spaces.Iz, ddFun (trunc χ G k) z)
            + (∫ z in Work.Spaces.Iz, ttFun (trunc χ G k) z)
            + α ^ 2 * (∫ z in Work.Spaces.Iz, dFun (trunc χ G k) z)
          ≤ (3 * α ^ 4 * ZDd G + 12 * α ^ 4 * (ck K k) ^ 2 * ZD G
              + 3 * α ^ 4 * CE * (ck K k) ^ 2 * ZTt G) + ZTt G
            + (2 * α ^ 2 * ZD G + 2 * α ^ 2 * CE * (ck K k) ^ 2 * ZTt G) := by
        linarith [hA1, hA2, hA3]
      have hb := hbox
      have hC₀α : 0 ≤ C₀ := le_of_lt hC₀pos
      have hb' := mul_le_mul_of_nonneg_left hsum hC₀α
      linarith [hb, hb']
    have hstep1' : (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz, (χ k z) ^ 2 * mixFun G z)
        ≤ α ^ 2 * (∫ z in Work.Spaces.Iz, mixFun (trunc χ G k) z)
          + α ^ 2 * ((ck K k) ^ 2 * CB * ZTt G) := by
      have h := mul_le_mul_of_nonneg_left hstep1 (sq_nonneg α)
      linarith [h]
    linarith [hstep1', hcomb]
  -- ### the limit
  have hχtend : ∀ z : ℝ, 0 < z → Tendsto (fun k : ℕ => χ k z) atTop (𝓝 1) := by
    intro z hz
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := hχlim z hz ε hε
    refine ⟨N, fun k hk => ?_⟩
    rw [Real.dist_eq]
    have h1 : 1 - χ k z < ε := hN k hk
    have h2 : χ k z ≤ 1 := (hχ01 k z hz).2
    have h3 : 0 ≤ χ k z := (hχ01 k z hz).1
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hlimpt : ∀ z : ℝ, 0 < z →
      Tendsto (fun k : ℕ => (χ k z) ^ 2 * mixFun G z) atTop (𝓝 (mixFun G z)) := by
    intro z hz
    have h2 : Tendsto (fun k : ℕ => (χ k z) ^ 2) atTop (𝓝 1) := by
      have h := (hχtend z hz).pow 2
      simpa using h
    have h3 : Tendsto (fun k : ℕ => (χ k z) ^ 2 * mixFun G z) atTop (𝓝 (1 * mixFun G z)) :=
      h2.mul (tendsto_const_nhds (x := mixFun G z))
    simpa using h3
  have hbound : ∀ k : ℕ, ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ‖(χ k z) ^ 2 * mixFun G z‖ ≤ mixFun G z := by
    intro k
    refine ae_restrict_Iz_of_Ioi (ae_Ioi_of_forall (fun z hz => ?_))
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (mixFun_nonneg G z))]
    have hM : 0 ≤ mixFun G z := mixFun_nonneg G z
    have hc : (χ k z) ^ 2 ≤ 1 := hchi2 k z hz
    exact mul_le_of_le_one_left hM hc
  have hlimu : Tendsto (fun k : ℕ =>
        (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz, (χ k z) ^ 2 * mixFun G z))
      atTop (𝓝 ((α ^ 2 / 2) * ZMx G)) := by
    have hDCT := MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (F := fun k z => (χ k z) ^ 2 * mixFun G z) (f := fun z => mixFun G z) (mixFun G)
      (fun k => (aestronglyMeasurable_chi_sq hχall k).mul hmixI.aestronglyMeasurable)
      hmixI hbound
      (ae_restrict_Iz_of_Ioi (ae_Ioi_of_forall (fun z hz => hlimpt z hz)))
    have h2 := (tendsto_const_nhds (x := α ^ 2 / 2)).mul hDCT
    simpa [ZMx] using h2
  have hlogtend : Tendsto (fun k : ℕ => Real.log ((k : ℝ) + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Filter.tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
  have hcktend : Tendsto (fun k : ℕ => ck K k) atTop (𝓝 0) :=
    hlogtend.const_div_atTop K
  have hck2tend : Tendsto (fun k : ℕ => (ck K k) ^ 2) atTop (𝓝 0) := by
    simpa only [pow_two, mul_zero] using hcktend.mul hcktend
  have hlimv : Tendsto (fun k : ℕ =>
        C₀ * (3 * α ^ 4 * ZDd G + ZTt G + 2 * α ^ 2 * ZD G)
          + (ck K k) ^ 2 * (C₀ * (12 * α ^ 4 * ZD G + 3 * α ^ 4 * CE * ZTt G
                + 2 * α ^ 2 * CE * ZTt G) + α ^ 2 * CB * ZTt G))
      atTop (𝓝 (C₀ * (3 * α ^ 4 * ZDd G + ZTt G + 2 * α ^ 2 * ZD G))) := by
    have hB : Tendsto (fun k : ℕ => (ck K k) ^ 2 * (C₀ * (12 * α ^ 4 * ZD G
          + 3 * α ^ 4 * CE * ZTt G + 2 * α ^ 2 * CE * ZTt G) + α ^ 2 * CB * ZTt G)) atTop
        (𝓝 (0 * (C₀ * (12 * α ^ 4 * ZD G + 3 * α ^ 4 * CE * ZTt G
          + 2 * α ^ 2 * CE * ZTt G) + α ^ 2 * CB * ZTt G))) :=
      hck2tend.mul (tendsto_const_nhds (x := C₀ * (12 * α ^ 4 * ZD G + 3 * α ^ 4 * CE * ZTt G
        + 2 * α ^ 2 * CE * ZTt G) + α ^ 2 * CB * ZTt G))
    have h := (tendsto_const_nhds (x := C₀ * (3 * α ^ 4 * ZDd G + ZTt G + 2 * α ^ 2 * ZD G))).add hB
    simpa using h
  have hfin := le_of_tendsto_of_tendsto hlimu hlimv (Filter.Eventually.of_forall hperk)
  -- ### the final arithmetic
  have hfinal : α ^ 2 * ZMx G
      ≤ 6 * C₀ * (α ^ 4 * ZDd G + ZTt G + α ^ 2 * ZD G) := by
    have h1 : α ^ 2 * ZMx G = 2 * ((α ^ 2 / 2) * ZMx G) := by ring
    have h2 : 2 * (C₀ * (3 * α ^ 4 * ZDd G + ZTt G + 2 * α ^ 2 * ZD G))
        ≤ 6 * C₀ * (α ^ 4 * ZDd G + ZTt G + α ^ 2 * ZD G) := by
      have h3 : 0 ≤ C₀ * ZTt G := mul_nonneg (le_of_lt hC₀pos) (ZTt_nonneg G)
      have h4 : 0 ≤ C₀ * (α ^ 2 * ZD G) :=
        mul_nonneg (le_of_lt hC₀pos) (mul_nonneg (sq_nonneg α) (ZD_nonneg G))
      nlinarith [h3, h4]
    rw [h1]
    linarith [hfin, h2]
  show α ^ 2 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z)
      ≤ 6 * C₀ * (α ^ 4 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.ddIntS G z)
          + (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.ttIntS G z)
          + α ^ 2 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.dIntS G z))
  exact hfinal

end

end Work.EllipticEst.Core.i0Aux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeCrux.AeVLib.Slots =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Set Filter
open scoped Real Topology ENNReal

namespace Work.FTS.EllipticEst.AeCrux

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz

set_option linter.unusedSimpArgs false

/-! ## 6. Continuity of the slot integrands

(The two lemmas `continuousOn_slot` and `continuousOn_slotT` live in `AeVLib.Meas`, which this
module imports; they were duplicated here by the module split.) -/

/-! ## 5. A slot transfer -/

theorem ae_strip_mem :
    ∀ᵐ q ∂(MeasureTheory.Measure.prod (volume : Measure ℝ) (volume.restrict Iθ)),
      q.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  have hI : ∀ᵐ θ ∂(volume : Measure ℝ).restrict Iθ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    rw [Work.Spaces.Iθ]
    rw [← MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := Real.pi / 2))]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => hθ)
  rw [MeasureTheory.Measure.ae_prod_iff_ae_ae (p := fun q : ℝ × ℝ => q.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (measurableSet_Ioo.preimage measurable_snd)]
  exact Filter.Eventually.of_forall fun _ => hI

/-- A pointwise inequality on the open strip gives an a.e. statement on the product. -/
theorem ae_strip_of {p : ℝ → ℝ → Prop} (hp : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) → p t θ) :
    ∀ᵐ q ∂(MeasureTheory.Measure.prod (volume : Measure ℝ) (volume.restrict Iθ)), p q.1 q.2 := by
  filter_upwards [ae_strip_mem] with q hq
  exact hp q.1 q.2 hq

theorem ae_Iθ_Ioo : ∀ᵐ θ ∂(volume : Measure ℝ).restrict Iθ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  rw [Work.Spaces.Iθ]
  rw [← MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := Real.pi / 2))]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => hθ)



/-! ## 5. Slot transfers -/

/-- A pointwise inequality on the open strip gives an a.e. statement on the product. -/
theorem continuousOn_Phi {g Φ : ℝ → ℝ → ℝ}
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2)
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hid : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Φ t θ = g t θ ^ 2 * Work.FTS.EllSol.HeavyFlat.omw t * Work.FTS.EllipticEst.sEta θ) :
    ContinuousOn (Function.uncurry Φ) ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have h := continuousOn_slotT hg
  refine (continuousOn_congr ?_).mpr h
  intro p hp
  show Φ p.1 p.2 = g p.1 p.2 ^ 2 * Work.FTS.EllSol.HeavyFlat.omw p.1 * Work.FTS.EllipticEst.sEta p.2
  exact hid p.1 p.2 hp.2

theorem Phi_nonneg {g Φ : ℝ → ℝ → ℝ}
    (hid : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Φ t θ = g t θ ^ 2 * Work.FTS.EllSol.HeavyFlat.omw t * Work.FTS.EllipticEst.sEta θ) :
    ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) → 0 ≤ Φ t θ := by
  intro t θ hθ
  rw [hid t θ hθ]
  refine mul_nonneg (mul_nonneg (sq_nonneg _) ?_) ?_
  · rw [Work.FTS.EllSol.HeavyFlat.omw]
    positivity
  · exact le_of_lt (Real.rpow_pos_of_pos
      (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])) _)

theorem thEta_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ Work.FTS.EllipticEst.thEta θ :=
  Work.FTS.EllipticEst.thEta_nonneg hθ

theorem slot_integrableOn {F Φ : ℝ → ℝ → ℝ}
    (hFnn : ∀ z θ, 0 ≤ F z θ)
    (hΦnn : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) → 0 ≤ Φ t θ)
    (hid : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) → Φ t θ = Real.exp t * F (Real.exp t) θ)
    (hFcont : ContinuousOn (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hΦcont : ContinuousOn (Function.uncurry Φ) ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hslices : ∀ z ∈ Iz, Integrable (fun θ => F z θ) (volume.restrict Iθ))
    (houter : Integrable (fun z => ∫ θ, F z θ ∂(volume.restrict Iθ)) (volume.restrict Iz)) :
    IntegrableOn (Function.uncurry Φ) ((Set.univ : Set ℝ) ×ˢ Iθ) := by
  have hIz : (volume : Measure ℝ).restrict Iz = volume.restrict (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
  have hAEF : AEStronglyMeasurable (Function.uncurry F)
      ((volume : Measure ℝ).restrict Iz |>.prod (volume.restrict Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hFcont
  have hslice_ae : ∀ᵐ z ∂((volume : Measure ℝ).restrict Iz),
      Integrable (fun θ => F z θ) (volume.restrict Iθ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici
      (fun z hz => hslices z hz)
  obtain ⟨hFint, _⟩ := Work.Spaces.integrable_prod_of_iterated
    (μ := (volume : Measure ℝ).restrict Iz) (ν := volume.restrict Iθ)
    hFnn hAEF hslice_ae houter
  have hfinF : ∫⁻ p, ENNReal.ofReal (F p.1 p.2)
      ∂((volume : Measure ℝ).restrict Iz |>.prod (volume.restrict Iθ)) < ⊤ := by
    refine lt_of_eq_of_lt ?_ hFint.hasFiniteIntegral
    refine lintegral_congr fun p => ?_
    show ENNReal.ofReal (F p.1 p.2) = ‖F p.1 p.2‖ₑ
    rw [Real.enorm_eq_ofReal (hFnn p.1 p.2)]
  have hfinF' : ∫⁻ p, ENNReal.ofReal (F p.1 p.2)
      ∂((volume : Measure ℝ).restrict (Set.Ioi 0) |>.prod (volume.restrict Iθ)) < ⊤ := by
    rw [← hIz]
    exact hfinF
  have hGcont : ContinuousOn (Function.uncurry (fun t θ => F (Real.exp t) θ))
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hφ : Continuous (fun p : ℝ × ℝ => (Real.exp p.1, p.2)) := by fun_prop
    have hmap : Set.MapsTo (fun p : ℝ × ℝ => (Real.exp p.1, p.2))
        ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      fun p hp => ⟨Real.exp_pos p.1, hp.2⟩
    exact hFcont.comp (hφ.continuousOn (s := (Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2))) hmap
  have hAE1 : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (F p.1 p.2))
      ((volume : Measure ℝ).restrict (Set.Ioi 0) |>.prod (volume.restrict Iθ)) := by
    rw [← hIz]
    exact ENNReal.measurable_ofReal.comp_aemeasurable hAEF.aemeasurable
  have hAE2 : AEMeasurable (fun q : ℝ × ℝ =>
      ENNReal.ofReal (Real.exp q.1) * ENNReal.ofReal (F (Real.exp q.1) q.2))
      (MeasureTheory.Measure.prod (volume : Measure ℝ) (volume.restrict Iθ)) := by
    have h1 : AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal (Real.exp q.1))
        (MeasureTheory.Measure.prod (volume : Measure ℝ) (volume.restrict Iθ)) :=
      ENNReal.measurable_ofReal.comp_aemeasurable
        ((Real.measurable_exp.comp measurable_fst).aemeasurable)
    have h2 : AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal (F (Real.exp q.1) q.2))
        (MeasureTheory.Measure.prod (volume : Measure ℝ) (volume.restrict Iθ)) := by
      have h3 := aesm_prod_univ_Iθ (f := fun t θ => F (Real.exp t) θ) hGcont
      exact ENNReal.measurable_ofReal.comp_aemeasurable h3.aemeasurable
    exact h1.mul h2
  have hsub := lintegral_box_exp (F := fun z θ => ENNReal.ofReal (F z θ)) hAE1 hAE2
  rw [hsub] at hfinF'
  have hfinΦ : ∫⁻ q, ENNReal.ofReal (Φ q.1 q.2)
      ∂(MeasureTheory.Measure.prod (volume : Measure ℝ) (volume.restrict Iθ)) < ⊤ := by
    refine lt_of_eq_of_lt ?_ hfinF'
    refine lintegral_congr_ae ?_
    filter_upwards [ae_strip_of (fun t θ hθ => hθ)] with q hq
    rw [hid q.1 q.2 hq, ENNReal.ofReal_mul (le_of_lt (Real.exp_pos q.1))]
  have hAEΦ : AEStronglyMeasurable (fun q : ℝ × ℝ => Φ q.1 q.2)
      (MeasureTheory.Measure.prod (volume : Measure ℝ) (volume.restrict Iθ)) := by
    simpa only [Measure.restrict_univ] using (aesm_prod_univ_Iθ hΦcont)
  change MeasureTheory.Integrable (Function.uncurry Φ)
    ((volume : Measure (ℝ × ℝ)).restrict ((Set.univ : Set ℝ) ×ˢ Iθ))
  rw [show (volume : Measure (ℝ × ℝ)).restrict ((Set.univ : Set ℝ) ×ˢ Iθ)
      = MeasureTheory.Measure.prod (volume : Measure ℝ) (volume.restrict Iθ) from by
    rw [Measure.volume_eq_prod ℝ ℝ, ← MeasureTheory.Measure.prod_restrict,
      Measure.restrict_univ]]
  refine ⟨hAEΦ, ?_⟩
  refine lt_of_eq_of_lt ?_ hfinΦ
  refine lintegral_congr_ae ?_
  filter_upwards [ae_strip_of (fun t θ hθ => hθ)] with q hq
  show ‖Φ q.1 q.2‖ₑ = ENNReal.ofReal (Φ q.1 q.2)
  rw [Real.enorm_eq_ofReal (hΦnn q.1 q.2 hq)]


end Work.FTS.EllipticEst.AeCrux
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Alpha4.Assembly =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Alpha4

set_option autoImplicit false
set_option maxHeartbeats 2000000


















/-! ## Auxiliary continuity and integrability facts -/





/-! ## The one-dimensional slice inequality applied to the slices `θ ↦ D_zG(z,θ)` -/


/-! ## The integration-by-parts identity for the `B`-term -/

end Work.FTS.EllipticEst.Alpha4
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Alpha4.deriv_zc_eq_zero_of_notMem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology

namespace Work.FTS.EllipticEst.Alpha4




end Work.FTS.EllipticEst.Alpha4
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.hkMemSliceAbsIntegrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000

/-! ## Elementary angular facts -/

private lemma sinCos2_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.Elliptic.sinCos2 θ := by
  obtain ⟨h0, h1⟩ := hθ
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos])
  have hc : 0 ≤ Real.cos θ := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) h1
  rw [Work.Elliptic.sinCos2]
  positivity

private lemma continuous_sinCos2 : Continuous Work.Elliptic.sinCos2 := by
  show Continuous (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
  exact Real.continuous_sin.mul (Real.continuous_cos.pow 2)

private lemma sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])

/-- `(A * (b / s^{η/2}))² = A² b² s^{-η}` for `s ≥ 0`. -/
private lemma mul_div_rpow_sq (A b s : ℝ) (hs : 0 ≤ s) :
    (A * (b / s ^ (Work.Spaces.eta / 2))) ^ 2
      = A ^ 2 * b ^ 2 * s ^ (-(Work.Spaces.eta)) := by
  have h2 : (s ^ (Work.Spaces.eta / 2)) ^ 2 = s ^ (Work.Spaces.eta) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
    congr 1
    ring
  rw [mul_pow, div_pow, h2, Real.rpow_neg hs, div_eq_mul_inv]
  ring

/-! ## The main lemma -/

theorem hkMemSliceAbsIntegrable {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 1 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ)
    {z₀ z₁ : ℝ} (hz₀ : 0 < z₀) (hzlt : z₀ < z₁) :
    (∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
        (fun θ : ℝ => |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ)
        Work.Spaces.Iθ) ∧
    (MeasureTheory.IntegrableOn
        (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
          |Work.Spaces.pzIter 2 Ψ s θ| * Work.Elliptic.sinCos2 θ)
        (Set.Icc z₀ z₁)) ∧
    (MeasureTheory.Integrable
        (Function.uncurry (fun s θ : ℝ =>
          |Work.Spaces.pzIter 2 Ψ s θ| * Work.Elliptic.sinCos2 θ))
        ((MeasureTheory.volume.restrict (Set.uIoc z₀ z₁)).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))) ∧
    (∀ z ∈ Set.Icc z₀ z₁, ∫ θ in Work.Spaces.Iθ,
        |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ
      ≤ (1 / z ^ 2) * Real.sqrt (Real.pi / 2) * Real.sqrt
          (∫ θ in Work.Spaces.Iθ,
            ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
              * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2))
  := by
  have hk1 : 1 ≤ k := hk
  have hA : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hcont_abs : ContinuousOn (fun p : ℝ × ℝ =>
      |Work.Spaces.pzIter 2 Ψ p.1 p.2| * Work.Elliptic.sinCos2 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have h2 : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.sinCos2 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      (continuous_sinCos2.comp continuous_snd).continuousOn
    exact ((hA.pzIter 2).continuousOn.abs).mul h2
  -- ## Conjunct 1
  have hconc1 : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn (fun θ : ℝ =>
      |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
    intro z hz
    have hzIz : z ∈ Work.Spaces.Iz := by rw [Work.Spaces.Iz]; exact le_of_lt hz
    have hmem := h.memA.1 z hzIz
    have hdom : MeasureTheory.IntegrableOn (fun θ : ℝ => (1 / z ^ 4) * Work.Spaces.HkIntegrand α k
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ + 1) Work.Spaces.Iθ :=
      (hmem.const_mul (1 / z ^ 4)).add
        (MeasureTheory.integrableOn_const (C := (1 : ℝ))
          (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
    refine hdom.mono' ?_ ?_
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => |Work.Spaces.pzIter 2 Ψ p.1 p.2| * Work.Elliptic.sinCos2 p.2)
        hcont_abs hz
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
      have h1 : |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ
          ≤ (Work.Spaces.pzIter 2 Ψ z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1 := by
        have hh := Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted
          (f := fun θ => Work.Spaces.pzIter 2 Ψ z θ) hz hθ
        rwa [abs_mul, abs_of_nonneg (sinCos2_nonneg_Iθ hθ)] at hh
      have h2 : (Work.Spaces.pzIter 2 Ψ z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ (1 / z ^ 4) * Work.Spaces.HkIntegrand α k
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ := by
        have h3 := Work.Spaces.sq_le_HkIntegrand_z α k
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ 0 (Nat.zero_le k)
        simp only [Work.Spaces.DzIter_zero] at h3
        have hkey : ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            = z ^ 4 * ((Work.Spaces.pzIter 2 Ψ z θ)
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
          ring
        rw [hkey] at h3
        have hX : (Work.Spaces.pzIter 2 Ψ z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            = (z ^ 4)⁻¹ * (z ^ 4 * ((Work.Spaces.pzIter 2 Ψ z θ)
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
          rw [inv_mul_cancel_left₀ (pow_ne_zero 4 (ne_of_gt hz))]
        rw [hX, one_div]
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (sinCos2_nonneg_Iθ hθ))]
      linarith
  -- ## Conjunct 4 (the pointwise weighted bound)
  have hconc4 : ∀ z ∈ Set.Icc z₀ z₁, ∫ θ in Work.Spaces.Iθ,
        |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ
      ≤ (1 / z ^ 2) * Real.sqrt (Real.pi / 2) * Real.sqrt
          (∫ θ in Work.Spaces.Iθ,
            ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
              * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2) := by
    intro z hz
    have hzpos : 0 < z := lt_of_lt_of_le hz₀ hz.1
    have hS : MeasureTheory.Integrable (fun θ : ℝ =>
        (Work.Spaces.pzIter 2 Ψ z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := pzIter2WeightedSqIntegrable hk1 h z hzpos
    have hcs := sliceAbsSinCos2CS (f := fun θ => Work.Spaces.pzIter 2 Ψ z θ)
      (hA.aesm_slice_pzIter 2 hzpos) hS
    have hpoint : ∀ θ ∈ Work.Spaces.Iθ,
        ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
            * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
          = z ^ 4 * (Work.Spaces.w z) ^ 2
              * ((Work.Spaces.pzIter 2 Ψ z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
      intro θ hθ
      rw [mul_div_rpow_sq (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (Work.Spaces.w z)
        (Real.sin (2 * θ)) (sin_two_nonneg_Iθ hθ)]
      ring
    have hQz : (∫ θ in Work.Spaces.Iθ,
            ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
              * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
        = z ^ 4 * (Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
      have hae : (fun θ : ℝ => ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
            * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
          =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
          (fun θ : ℝ => z ^ 4 * (Work.Spaces.w z) ^ 2
            * ((Work.Spaces.pzIter 2 Ψ z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) :=
        MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hpoint
      rw [MeasureTheory.integral_congr_ae hae, MeasureTheory.integral_const_mul]
    have hQ2 : Real.sqrt (∫ θ in Work.Spaces.Iθ,
          ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
            * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
        = z ^ 2 * Work.Spaces.w z * Real.sqrt
            (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
      rw [hQz, show z ^ 4 * (Work.Spaces.w z) ^ 2 = (z ^ 2 * Work.Spaces.w z) ^ 2 by ring]
      have hwz : (0 : ℝ) ≤ Work.Spaces.w z := by
        rw [Work.Spaces.w]; positivity
      rw [Real.sqrt_mul (x := (z ^ 2 * Work.Spaces.w z) ^ 2) (by positivity),
        Real.sqrt_sq (mul_nonneg (by positivity) hwz)]
    calc (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ)
        ≤ Real.sqrt (Real.pi / 2) * Real.sqrt (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pzIter 2 Ψ z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := hcs
      _ ≤ (1 / z ^ 2) * Real.sqrt (Real.pi / 2) * Real.sqrt (∫ θ in Work.Spaces.Iθ,
            ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
              * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2) := by
          rw [hQ2]
          have hw1 : (1 : ℝ) ≤ Work.Spaces.w z := Work.FTS.EllipticEst.one_le_w hzpos
          have hzw : (1 / z ^ 2) * Real.sqrt (Real.pi / 2)
                * (z ^ 2 * Work.Spaces.w z * Real.sqrt (∫ θ in Work.Spaces.Iθ,
                    (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
              = Work.Spaces.w z * (Real.sqrt (Real.pi / 2) * Real.sqrt
                  (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ z θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) := by
            have h1 : (1 / z ^ 2) * Real.sqrt (Real.pi / 2)
                  * (z ^ 2 * Work.Spaces.w z * Real.sqrt (∫ θ in Work.Spaces.Iθ,
                      (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
                = ((1 / z ^ 2) * z ^ 2) * (Real.sqrt (Real.pi / 2)
                    * (Work.Spaces.w z * Real.sqrt (∫ θ in Work.Spaces.Iθ,
                      (Work.Spaces.pzIter 2 Ψ z θ) ^ 2
                        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))) := by ring
            rw [h1, one_div, inv_mul_cancel₀ (pow_ne_zero 2 (ne_of_gt hzpos)), one_mul]
            ring
          rw [hzw]
          exact le_mul_of_one_le_left
            (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hw1
  -- ## The `z`-weighted integral `J` and the domination `Q ≤ J`
  set J : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ with hJdef
  have hJIz : MeasureTheory.IntegrableOn J Work.Spaces.Iz := by
    simpa only [hJdef] using h.memA.2
  have hJint : MeasureTheory.IntegrableOn J (Set.Icc z₀ z₁) :=
    hJIz.mono_set (fun z hz => le_trans (le_of_lt hz₀) hz.1)
  have hJnn : ∀ z : ℝ, 0 ≤ J z := by
    intro z
    rw [hJdef]
    exact MeasureTheory.integral_nonneg
      (fun θ => Work.Spaces.HkIntegrand_nonneg α k _ z θ)
  have hQJ : ∀ z ∈ Set.Icc z₀ z₁,
      (∫ θ in Work.Spaces.Iθ,
            ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
              * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2) ≤ J z := by
    intro z hz
    have hzpos : 0 < z := lt_of_lt_of_le hz₀ hz.1
    have hzIz : z ∈ Work.Spaces.Iz := by rw [Work.Spaces.Iz]; exact le_of_lt hzpos
    have hmem := h.memA.1 z hzIz
    have hintL : MeasureTheory.IntegrableOn (fun θ : ℝ =>
        ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        Work.Spaces.Iθ := by
      refine hmem.mono' ?_ ?_
      · refine (Work.Spaces.aesm_slice_of_continuousOn_Qd
          (fun p : ℝ × ℝ => (p.1 ^ 2 * Work.Spaces.pzIter 2 Ψ p.1 p.2)
            * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)))
          (((continuousOn_fst.pow 2).mul (hA.pzIter 2).continuousOn).mul
            Work.FTS.EllipticEst.continuousOn_wdivsin_Q0) hzpos).pow 2
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ => ?_)
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact Work.Spaces.sq_le_HkIntegrand_z α k
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ 0 (Nat.zero_le k)
    rw [hJdef]
    exact MeasureTheory.integral_mono hintL hmem (fun θ =>
      Work.Spaces.sq_le_HkIntegrand_z α k
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ 0 (Nat.zero_le k))
  -- ## Conjunct 2
  have hconc2 : MeasureTheory.IntegrableOn (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
        |Work.Spaces.pzIter 2 Ψ s θ| * Work.Elliptic.sinCos2 θ) (Set.Icc z₀ z₁) := by
    have hDint : MeasureTheory.IntegrableOn
        (fun z : ℝ => (1 / z₀ ^ 2) * Real.sqrt (Real.pi / 2) * (1 + J z))
        (Set.Icc z₀ z₁) := by
      have h1 : MeasureTheory.IntegrableOn (fun z : ℝ => (1 : ℝ) + J z) (Set.Icc z₀ z₁) :=
        (MeasureTheory.integrableOn_const (C := (1 : ℝ))
          (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).add hJint
      exact h1.const_mul _
    have haesmF : MeasureTheory.AEStronglyMeasurable (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
        |Work.Spaces.pzIter 2 Ψ s θ| * Work.Elliptic.sinCos2 θ)
        (MeasureTheory.volume.restrict (Set.Icc z₀ z₁)) := by
      have hprod : MeasureTheory.AEStronglyMeasurable
          (fun p : ℝ × ℝ => |Work.Spaces.pzIter 2 Ψ p.1 p.2| * Work.Elliptic.sinCos2 p.2)
          ((MeasureTheory.volume.restrict (Set.Ioc z₀ z₁)).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
        Work.FTS.EllipticEst.aesm_uncurry_restrict_open
          (fun p : ℝ × ℝ => |Work.Spaces.pzIter 2 Ψ p.1 p.2| * Work.Elliptic.sinCos2 p.2)
          hcont_abs hz₀.le
      have h4 : MeasureTheory.AEStronglyMeasurable (fun s : ℝ => ∫ θ : ℝ,
          |Work.Spaces.pzIter 2 Ψ s θ| * Work.Elliptic.sinCos2 θ
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          (MeasureTheory.volume.restrict (Set.Ioc z₀ z₁)) :=
        hprod.integral_prod_right'
      rw [← MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioc_ae_eq_Icc (a := z₀) (b := z₁))]
      exact h4
    refine hDint.mono' haesmF ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun z hz => ?_)
    have hzpos : 0 < z := lt_of_lt_of_le hz₀ hz.1
    have hFnn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
        |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ := by
      refine MeasureTheory.integral_nonneg_of_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      exact mul_nonneg (abs_nonneg _) (sinCos2_nonneg_Iθ hθ)
    rw [Real.norm_eq_abs, abs_of_nonneg hFnn]
    have hcs := hconc4 z hz
    have h1 : (1 / z ^ 2) ≤ 1 / z₀ ^ 2 :=
      one_div_le_one_div_of_le (by positivity : (0 : ℝ) < z₀ ^ 2)
        (pow_le_pow_left₀ hz₀.le hz.1 2)
    have h3 : Real.sqrt (J z) ≤ 1 + J z := by
      have hJ0 := hJnn z
      nlinarith [Real.sq_sqrt hJ0, Real.sqrt_nonneg (J z)]
    have hc0 : (0 : ℝ) ≤ Real.sqrt (Real.pi / 2) := Real.sqrt_nonneg _
    have hz0inv : (0 : ℝ) ≤ 1 / z₀ ^ 2 := by positivity
    calc (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ)
        ≤ (1 / z ^ 2) * Real.sqrt (Real.pi / 2) * Real.sqrt (∫ θ in Work.Spaces.Iθ,
            ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
              * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2) := hcs
      _ ≤ (1 / z₀ ^ 2) * Real.sqrt (Real.pi / 2)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ,
            ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
              * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hc0) (Real.sqrt_nonneg _)
      _ ≤ (1 / z₀ ^ 2) * Real.sqrt (Real.pi / 2) * (1 + J z) :=
          (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hQJ z hz))
            (mul_nonneg hz0inv hc0)).trans (mul_le_mul_of_nonneg_left h3 (mul_nonneg hz0inv hc0))
  -- ## Conjunct 3
  have hconc3 : MeasureTheory.Integrable
      (Function.uncurry (fun s θ : ℝ =>
        |Work.Spaces.pzIter 2 Ψ s θ| * Work.Elliptic.sinCos2 θ))
      ((MeasureTheory.volume.restrict (Set.uIoc z₀ z₁)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    refine Work.FTS.EllipticEst.integrable_prod_ae
      (G := fun s θ : ℝ => |Work.Spaces.pzIter 2 Ψ s θ| * Work.Elliptic.sinCos2 θ) ?_ ?_ ?_ ?_
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc (fun a _ =>
        MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun b hb =>
          mul_nonneg (abs_nonneg _) (sinCos2_nonneg_Iθ hb)))
    · rw [Set.uIoc_of_le hzlt.le]
      exact Work.FTS.EllipticEst.aesm_uncurry_restrict_open
        (fun p : ℝ × ℝ => |Work.Spaces.pzIter 2 Ψ p.1 p.2| * Work.Elliptic.sinCos2 p.2)
        hcont_abs hz₀.le
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc (fun a ha => ?_)
      rw [Set.uIoc_of_le hzlt.le] at ha
      exact hconc1 a (lt_trans hz₀ ha.1)
    · have hsub : Set.uIoc z₀ z₁ ⊆ Set.Icc z₀ z₁ := by
        rw [Set.uIoc_of_le hzlt.le]; exact Set.Ioc_subset_Icc_self
      exact hconc2.mono_set hsub
  exact ⟨hconc1, hconc2, hconc3, hconc4⟩

end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.TransportS.SupDzWeighted.supDz_weighted_avg_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.SupDzWeighted

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## Elementary algebraic identities for the weights -/

/-- `sin(2θ) > 0` in the interior of `Iθ`. -/
theorem sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])



/-! ## Pointwise domination by the `ℋ⁴`-integrand -/



/-! ## Integrability of the weighted angular slice -/


/-! ## The main estimate -/


end Work.FTS.TransportS.SupDzWeighted
end
end
