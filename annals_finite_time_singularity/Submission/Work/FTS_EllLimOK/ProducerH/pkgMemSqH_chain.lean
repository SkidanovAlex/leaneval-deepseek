import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_EllLimOK.ProducerH.pkgMemSqH_helpers
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_EllLimOK.ProducerH.slotBd_phiTil
import Submission.Work.FTS_EllLimOK.ProducerH.kappa_eq_zero
import Submission.Work.FTS_EllLimOK.ProducerH.psiP_div_cos
import Submission.Work.FTS_EllLimOK.ProducerH.thetaDivCos_slice
import Submission.Work.FTS_StreamBdry.SB1.Engine
import Submission.Work.FTS_StreamBdry.SB1.psiP_ode
import Submission.Work.FTS_StreamBdry.SB1.psiP_diff
import Submission.Work.FTS_StreamBdry.SB1.psiP_Vop_bnd
import Submission.Work.FTS_StreamBdry.SB3.psiP_DzLe
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS_EllLimOK.Pinning.smoothOpen_div_cos

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FTS_EllLimOK.ProducerH.pkgMemSqH_chain`

The chain of the producer `pkgMemSqH_of_ellClassOk`: given the four producer lemmas
(`slotBd_phiTil`, `kappa_eq_zero`, `psiP_div_cos`, `thetaDivCos_slice`) and the numerical
constants `K, CB, CT, CS, CC` they provide, every class-`C` datum `gg` has both `E gg` and
`E gg / cos θ` in `ℋ⁰`, with the norms bounded by `CC * (1 + Xn6 α gg)^2` and the angular
slices by `CC * (1 + 1/z) * (1 + Xn6 α gg)^2`.

The route: `Φ̃ = PhiTil α gg (E gg)` solves nothing by itself, but
`Uprime α Φ̃ = Uop α Φ̃ / sin 2θ` is the package's `U`-slot, so `SlotBd` holds for `Φ̃` with
`M = K (Ce * Xn6 α gg)`; `sb1_gauge_of_parts` then gives
`Φ̃ = psiP α Φ̃ + κ gaugeMode α` with `gaugeMode α = z^{-3/α}/cos θ`, and `kappa_eq_zero`
(using `EllClassOk 8`, i.e. the `ℋ⁸`-honesty of `z²∂_z²` of the shifted unknown) gives `κ = 0`.
Hence `Φ̃ = psiP α Φ̃` and `psiP_div_cos` bounds `Φ̃/cos` by the `U`-slot, while `thetaDivCos_slice`
bounds `Θ α gg / cos`; `E gg / cos = Φ̃/cos + Θ/cos` by the definition of `PhiTil`, and `E gg` is
dominated by `E gg/cos` (`HkIntegrand_zero_le_cosDiv`, `cos(π/2)` being a single point).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- The chain of the assembly. -/
theorem pkgMemSqH_chain {α Ce K CB CT CS CC : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hKpos : 0 < K) (hCBpos : 0 < CB) (hCTpos : 0 < CT) (hCSpos : 0 < CS)
    (hSlotBd : ∀ (E : Fn →ₗ[ℝ] Fn) (g : Fn), Work.FTS.ClassC.ClassC α g →
      Work.FTS.ClassC.EllPkgK α 6 Ce g (E g) →
      Work.FTS.StreamBdryIface.SlotBd α (Work.Construction.PhiTil α g (E g))
        (K * (Ce * Work.FTS.StrongGlobal.Xn6 α g)))
    (hPsiP : ∀ (Φ : ℝ → ℝ → ℝ) (M : ℝ), 0 ≤ M → Work.FTS.EllipticEst.SmoothOpen Φ →
      (∀ z θ, (z, θ) ∈ Work.Construction.Qd →
        Φ z θ = Work.FTS.StreamBdryIface.psiP α Φ z θ) →
      (∀ z θ, (z, θ) ∈ Work.Construction.Qd →
        |Work.FTS.StreamBdryIface.Uprime α Φ z θ| ≤ M) →
      Work.Spaces.HkMem α 0 (Work.FTS.StreamBdryIface.Uprime α Φ) →
      Work.Spaces.HkMem α 0 (fun z θ => Φ z θ / Real.cos θ) ∧
      Work.Spaces.HkSq α 0 (fun z θ => Φ z θ / Real.cos θ)
        ≤ CB * Work.Spaces.HkSq α 0 (Work.FTS.StreamBdryIface.Uprime α Φ) ∧
      (∀ z : ℝ, 0 < z →
        (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) z θ)
          ≤ CB * (1 + 1 / z)
            * (M ^ 2 + Work.Spaces.HkSq α 0 (Work.FTS.StreamBdryIface.Uprime α Φ))))
    (hThetaB : ∀ g : Fn, Work.FTS.ClassC.ClassC α g →
      Work.Spaces.HkMem α 0
          (fun z θ => Work.Construction.Theta α g z θ / Real.cos θ) ∧
      Work.Spaces.HkSq α 0 (fun z θ => Work.Construction.Theta α g z θ / Real.cos θ)
        ≤ CT * (1 + Work.FTS.StrongGlobal.Xn6 α g) ^ 2)
    (hThetaS : ∀ g : Fn, Work.FTS.ClassC.ClassC α g → ∀ z : ℝ, 0 < z →
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
        (fun z θ => Work.Construction.Theta α g z θ / Real.cos θ) z θ)
        ≤ CS * (1 + 1 / z) * (Work.FTS.StrongGlobal.Xn6 α g) ^ 2)
    (hCC1 : 2 * CB * Ce ^ 2 + 2 * CT ≤ CC)
    (hCC2 : 2 * CB * (K ^ 2 * Ce ^ 2 + Ce ^ 2) + 2 * CS ≤ CC) :
    ∀ (E : Fn →ₗ[ℝ] Fn), (∀ g : Fn, Work.FTS.ClassC.ClassC α g →
        Work.FTS.EllExist.EllClassOk 8 α g (E g) ∧
          Work.FTS.VocabO.EllPkgGo α Ce g (E g) ∧
          Work.FTS.ClassC.EllPkgK α 6 Ce g (E g)) →
      ∀ gg : Fn, Work.FTS.ClassC.ClassC α gg →
      (Work.Spaces.HkMem α 0 (fun z θ => E gg z θ / Real.cos θ) ∧
        Work.Spaces.HkSq α 0 (fun z θ => E gg z θ / Real.cos θ)
          ≤ CC * (1 + Work.FTS.StrongGlobal.Xn6 α gg) ^ 2 ∧
        (∀ z : ℝ, 0 < z → (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 0 (fun z θ => E gg z θ / Real.cos θ) z θ)
            ≤ CC * (1 + 1 / z) * (1 + Work.FTS.StrongGlobal.Xn6 α gg) ^ 2)) ∧
      (Work.Spaces.HkMem α 0 (E gg) ∧
        Work.Spaces.HkSq α 0 (E gg) ≤ CC * (1 + Work.FTS.StrongGlobal.Xn6 α gg) ^ 2 ∧
        (∀ z : ℝ, 0 < z → (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 0 (E gg) z θ)
            ≤ CC * (1 + 1 / z) * (1 + Work.FTS.StrongGlobal.Xn6 α gg) ^ 2)) := by
  intro E hE gg hgg
  obtain ⟨hok, hGo, hKg⟩ := hE gg hgg
  set X : ℝ := Work.FTS.StrongGlobal.Xn6 α gg with hX
  have hXnn : 0 ≤ X := by
    rw [hX]; exact Work.Spaces.HkNorm_nonneg α 6 gg
  set Φ : ℝ → ℝ → ℝ := Work.Construction.PhiTil α gg (E gg) with hΦ
  have hΦsm : Work.FTS.EllipticEst.SmoothOpen Φ :=
    Work.FTS.GalFields.RHS.Sharp.smoothOpen_PhiTil hα hGo
  have hUdef : Work.FTS.StreamBdryIface.Uprime α Φ
      = fun z θ => Work.Construction.Uop α Φ z θ / Work.Construction.s2 θ := rfl
  have hUg : Work.FTS.VocabO.HQo α 6 (Work.FTS.StreamBdryIface.Uprime α Φ) := by
    rw [hUdef]
    simpa only [hΦ] using hKg.U.1
  have hUn : Work.Spaces.HkNorm α 6 (Work.FTS.StreamBdryIface.Uprime α Φ) ≤ Ce * X := by
    rw [hUdef]
    simpa only [hΦ, hX] using hKg.U.2
  have hU2 : Work.Spaces.HkSq α 0 (Work.FTS.StreamBdryIface.Uprime α Φ) ≤ (Ce * X) ^ 2 := by
    calc Work.Spaces.HkSq α 0 (Work.FTS.StreamBdryIface.Uprime α Φ)
        ≤ Work.Spaces.HkSq α 6 (Work.FTS.StreamBdryIface.Uprime α Φ) :=
          Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by norm_num) hUg.2
      _ = (Work.Spaces.HkNorm α 6 (Work.FTS.StreamBdryIface.Uprime α Φ)) ^ 2 :=
          Work.FTS.GalFields.Tail.HkSq_eq_HkNorm_sq α 6 _
      _ ≤ (Ce * X) ^ 2 := pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 6 _) hUn 2
  -- the slot bound and the gauge decomposition
  have hslotK : Work.FTS.StreamBdryIface.SlotBd α Φ (K * (Ce * X)) := by
    simpa only [hΦ, hX] using hSlotBd E gg hgg hKg
  set M : ℝ := max (K * (Ce * X)) 0 with hM
  have hMnn : 0 ≤ M := le_max_right _ _
  have hslot : Work.FTS.StreamBdryIface.SlotBd α Φ M := SlotBd_mono hslotK (le_max_left _ _)
  have h3 : ContDiffOn ℝ 3 (Function.uncurry Φ) Work.Construction.Qd :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall Φ).mp hΦsm 3
  obtain ⟨κ, hdec⟩ := Work.FTS_StreamBdry.SB1.sb1_gauge_of_parts hα h3 hslot
    (Work.FTS_StreamBdry.SB1.psiP_ode hα h3 hslot)
    (Work.FTS_StreamBdry.SB1.psiP_diff hα h3 hslot)
    (Work.FTS_StreamBdry.SB1.psiP_Vop_bnd hα h3 hslot)
  have hκ : κ = 0 := kappa_eq_zero hα hα1 hgg hok hKg M κ hslot hdec
  have hfix : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Φ z θ = Work.FTS.StreamBdryIface.psiP α Φ z θ := by
    intro z θ hz
    rw [hdec z θ hz, hκ]
    ring
  have hsupU : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.FTS.StreamBdryIface.Uprime α Φ z θ| ≤ M := by
    intro z θ hz
    have h1 := (hslot z θ hz).1 0 (by norm_num)
    simpa only [Work.Spaces.DzIter_zero] using h1
  have hmemU : Work.Spaces.HkMem α 0 (Work.FTS.StreamBdryIface.Uprime α Φ) :=
    Work.FTS_EllLimOK.PkgJets.HkMem_mono_le hUg.1 (by norm_num) hUg.2
  obtain ⟨hmemA, hsqA, hsliceA⟩ := hPsiP Φ M hMnn hΦsm hfix hsupU hmemU
  obtain ⟨hmemB, hsqB⟩ := hThetaB gg hgg
  have hsliceB : ∀ z : ℝ, 0 < z → (∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0
        (fun z θ => Work.Construction.Theta α gg z θ / Real.cos θ) z θ)
      ≤ CS * (1 + 1 / z) * X ^ 2 := by
    intro z hz
    simpa only [hX] using hThetaS gg hgg z hz
  -- the sum decomposition
  have hf_eq : (fun z θ => E gg z θ / Real.cos θ)
      = fun z θ => Φ z θ / Real.cos θ
          + Work.Construction.Theta α gg z θ / Real.cos θ := by
    funext z θ
    simp only [hΦ, Work.Construction.PhiTil]
    ring
  -- numerical ingredients
  have hsqA' : Work.Spaces.HkSq α 0 (fun z θ => Φ z θ / Real.cos θ)
      ≤ CB * (Ce * X) ^ 2 := by
    refine hsqA.trans ?_
    exact mul_le_mul_of_nonneg_left hU2 hCBpos.le
  have hM2 : M ^ 2 ≤ K ^ 2 * Ce ^ 2 * (1 + X) ^ 2 := by
    have h5 : X ^ 2 ≤ (1 + X) ^ 2 := by nlinarith [hXnn]
    have h6 : K ^ 2 * Ce ^ 2 * X ^ 2 ≤ K ^ 2 * Ce ^ 2 * (1 + X) ^ 2 :=
      mul_le_mul_of_nonneg_left h5 (by positivity)
    rcases le_total (K * (Ce * X)) 0 with hc | hc
    · have h3 : M = 0 := by rw [hM]; exact max_eq_right hc
      rw [h3]
      have hZ : (0:ℝ) ^ 2 ≤ (K * (Ce * X)) ^ 2 := by simpa using sq_nonneg (K * (Ce * X))
      have h4 : (K * (Ce * X)) ^ 2 = K ^ 2 * Ce ^ 2 * X ^ 2 := by ring
      rw [h4] at hZ
      linarith [hZ, h6]
    · have h3 : M = K * (Ce * X) := by rw [hM]; exact max_eq_left hc
      rw [h3]
      have h4 : (K * (Ce * X)) ^ 2 = K ^ 2 * Ce ^ 2 * X ^ 2 := by ring
      linarith [h6, h4.le, h4.ge]
  have hmemf : Work.Spaces.HkMem α 0 (fun z θ => E gg z θ / Real.cos θ) := by
    rw [hf_eq]
    refine Work.FTS.LocData.HkMem_of_majorant α 0
      (M := fun z θ => 2 * Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) z θ
        + 2 * Work.Spaces.HkIntegrand α 0
            (fun z θ => Work.Construction.Theta α gg z θ / Real.cos θ) z θ) ?_ ?_ ?_ ?_
    · have hsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => E gg z θ / Real.cos θ) :=
        Work.FTS_EllLimOK.Pinning.smoothOpen_div_cos hGo.smooth
      have hc := hsm.continuousOn_HkIntegrand α 0
      rwa [hf_eq] at hc
    · intro z hz
      exact ((hmemA.1 z hz).const_mul 2).add ((hmemB.1 z hz).const_mul 2)
    · have h1 : MeasureTheory.IntegrableOn (fun z => 2 * (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) z θ)) Work.Spaces.Iz :=
        hmemA.2.const_mul 2
      have h2 : MeasureTheory.IntegrableOn (fun z => 2 * (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0
            (fun z θ => Work.Construction.Theta α gg z θ / Real.cos θ) z θ)) Work.Spaces.Iz :=
        hmemB.2.const_mul 2
      refine (h1.add h2).congr_fun ?_ measurableSet_Ici
      intro z hz
      simp only [Pi.add_apply]
      rw [MeasureTheory.integral_add ((hmemA.1 z hz).const_mul 2) ((hmemB.1 z hz).const_mul 2),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    · intro z hz θ hθ
      exact HkIntegrand_zero_add_le α _ _ z θ
  have hsqf : Work.Spaces.HkSq α 0 (fun z θ => E gg z θ / Real.cos θ)
      ≤ CC * (1 + X) ^ 2 := by
    have hstep : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
          (fun z θ => Φ z θ / Real.cos θ
            + Work.Construction.Theta α gg z θ / Real.cos θ) z θ)
        ≤ 2 * Work.Spaces.HkSq α 0 (fun z θ => Φ z θ / Real.cos θ)
          + 2 * Work.Spaces.HkSq α 0
            (fun z θ => Work.Construction.Theta α gg z θ / Real.cos θ) := by
      have hinner : ∀ z ∈ Work.Spaces.Iz,
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
              (fun z θ => Φ z θ / Real.cos θ
                + Work.Construction.Theta α gg z θ / Real.cos θ) z θ)
            ≤ 2 * (∫ θ in Work.Spaces.Iθ,
                Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) z θ)
              + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
                  (fun z θ => Work.Construction.Theta α gg z θ / Real.cos θ) z θ) := by
        intro z hz
        have hint : MeasureTheory.IntegrableOn (fun θ => 2 * Work.Spaces.HkIntegrand α 0
              (fun z θ => Φ z θ / Real.cos θ) z θ
            + 2 * Work.Spaces.HkIntegrand α 0
              (fun z θ => Work.Construction.Theta α gg z θ / Real.cos θ) z θ) Work.Spaces.Iθ :=
          ((hmemA.1 z hz).const_mul 2).add ((hmemB.1 z hz).const_mul 2)
        have h2 := MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ) hint
          (Filter.Eventually.of_forall fun θ => HkIntegrand_zero_add_le α _ _ z θ)
        rw [MeasureTheory.integral_add ((hmemA.1 z hz).const_mul 2) ((hmemB.1 z hz).const_mul 2),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at h2
        exact h2
      have hinner_ae : (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
            (fun z θ => Φ z θ / Real.cos θ
              + Work.Construction.Theta α gg z θ / Real.cos θ) z θ)
          ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
            (fun z => 2 * (∫ θ in Work.Spaces.Iθ,
                Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) z θ)
              + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
                  (fun z θ => Work.Construction.Theta α gg z θ / Real.cos θ) z θ)) := by
        refine (MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici).mpr ?_
        exact Filter.Eventually.of_forall fun z hz => hinner z hz
      have hI : MeasureTheory.IntegrableOn (fun z => 2 * (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) z θ)
          + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
            (fun z θ => Work.Construction.Theta α gg z θ / Real.cos θ) z θ)) Work.Spaces.Iz :=
        (hmemA.2.const_mul 2).add (hmemB.2.const_mul 2)
      have h2 := MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg_of_ae
          (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ))
        hI hinner_ae
      rw [MeasureTheory.integral_add (hmemA.2.const_mul 2) (hmemB.2.const_mul 2),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at h2
      simpa only [Work.Spaces.HkSq] using h2
    rw [hf_eq]
    have hfinal : 2 * Work.Spaces.HkSq α 0 (fun z θ => Φ z θ / Real.cos θ)
        + 2 * Work.Spaces.HkSq α 0
          (fun z θ => Work.Construction.Theta α gg z θ / Real.cos θ)
        ≤ CC * (1 + X) ^ 2 := by
      refine norm_arith hCBpos.le hCTpos.le hXnn ?_ hCC1
      linarith [hsqA', hsqB]
    exact hstep.trans hfinal
  have hslicef : ∀ z : ℝ, 0 < z → (∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 (fun z θ => E gg z θ / Real.cos θ) z θ)
      ≤ CC * (1 + 1 / z) * (1 + X) ^ 2 := by
    intro z hz
    have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
    have hinner : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
          (fun z θ => Φ z θ / Real.cos θ
            + Work.Construction.Theta α gg z θ / Real.cos θ) z θ)
        ≤ 2 * (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) z θ)
          + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
              (fun z θ => Work.Construction.Theta α gg z θ / Real.cos θ) z θ) := by
      have hint : MeasureTheory.IntegrableOn (fun θ => 2 * Work.Spaces.HkIntegrand α 0
            (fun z θ => Φ z θ / Real.cos θ) z θ
          + 2 * Work.Spaces.HkIntegrand α 0
            (fun z θ => Work.Construction.Theta α gg z θ / Real.cos θ) z θ) Work.Spaces.Iθ :=
        ((hmemA.1 z hzI).const_mul 2).add ((hmemB.1 z hzI).const_mul 2)
      have h2 := MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ) hint
        (Filter.Eventually.of_forall fun θ => HkIntegrand_zero_add_le α _ _ z θ)
      rw [MeasureTheory.integral_add ((hmemA.1 z hzI).const_mul 2) ((hmemB.1 z hzI).const_mul 2),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at h2
      exact h2
    rw [hf_eq]
    have hCeX : (Ce * X) ^ 2 ≤ Ce ^ 2 * (1 + X) ^ 2 := by
      nlinarith [sq_nonneg Ce, sq_nonneg X, hXnn, sq_nonneg (1 + X)]
    exact hinner.trans (slice_arith hCBpos.le hCSpos.le hz hXnn (hsliceA z hz) (hsliceB z hz)
      hM2 (hU2.trans hCeX) hCC2)
  -- the `E gg` part
  have hmemE : Work.Spaces.HkMem α 0 (E gg) := by
    refine Work.FTS.LocData.HkMem_of_majorant α 0
      (M := fun z θ => Work.Spaces.HkIntegrand α 0 (fun z θ => E gg z θ / Real.cos θ) z θ)
      ?_ ?_ ?_ ?_
    · exact hGo.smooth.continuousOn_HkIntegrand α 0
    · intro z hz
      exact hmemf.1 z hz
    · exact hmemf.2
    · intro z hz θ hθ
      exact HkIntegrand_zero_le_cosDiv α (E gg) z θ
  have hsqE : Work.Spaces.HkSq α 0 (E gg) ≤ CC * (1 + X) ^ 2 := by
    have hmono_inner : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (E gg) z θ)
          ≤ ∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α 0 (fun z θ => E gg z θ / Real.cos θ) z θ := by
      refine (MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici).mpr ?_
      exact Filter.Eventually.of_forall fun z hz =>
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ)
          (hmemf.1 z hz)
          (Filter.Eventually.of_forall fun θ =>
            HkIntegrand_zero_le_cosDiv α (E gg) z θ)
    have hmono : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0 (E gg) z θ)
        ≤ ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 0 (fun z θ => E gg z θ / Real.cos θ) z θ :=
      MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg_of_ae
          (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ))
        hmemf.2 hmono_inner
    rw [Work.Spaces.HkSq] at hsqf
    rw [Work.Spaces.HkSq]
    exact hmono.trans hsqf
  have hsliceE : ∀ z : ℝ, 0 < z → (∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 (E gg) z θ)
      ≤ CC * (1 + 1 / z) * (1 + X) ^ 2 := by
    intro z hz
    refine le_trans ?_ (hslicef z hz)
    exact MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ)
      (hmemf.1 z (le_of_lt hz))
      (Filter.Eventually.of_forall fun θ => HkIntegrand_zero_le_cosDiv α (E gg) z θ)
  exact ⟨⟨hmemf, hsqf, hslicef⟩, hmemE, hsqE, hsliceE⟩

end Work.FTS_EllLimOK.ProducerH
