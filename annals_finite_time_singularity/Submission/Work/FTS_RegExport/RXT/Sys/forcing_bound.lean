import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS_RegExport.RXT.CoeffJetsDefs
import Submission.Work.FTS_RegExport.RXT.Sys.FBZhatB
import Submission.Work.FTS_RegExport.RXT.Sys.FBGamma
import Submission.Work.FTS_RegExport.RXT.Ftau_bounds
import Submission.Work.FTS_RegExport.RXT.datum_bound
import Submission.Work.FTS.LocData6.DthIter_Gam_abs_le6
import Submission.Work.FTS_RegExport.RXT.SysAux.SigR_eq_reduced

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

namespace Work.FTS_RegExport.RXT.Sys

theorem forcing_bound {S α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hS : 0 < S) (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hVP : Work.FTS_RegExport.RXT.CoeffJets (Work.FTS.Regularity.pExp α)
      (Work.FTS.RegExportIface.RXT.μR α Φs E g) (Work.FTS.RegExportIface.RXT.GR α g)
      (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) S)
    (hV2 : ∃ M : ℝ, ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ∀ Q ∈ ({(Work.Construction.Rop (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ)),
          Work.Construction.Vop
            (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ),
          fun z θ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ
            / Real.sin (2 * θ)} : Set (ℝ → ℝ → ℝ)),
        ∀ j i : ℕ, j + i ≤ 2 → |Work.Spaces.mixed j i Q z θ| ≤ M * min z 1)
    (hC2 : ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.VR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.bR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.cR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0)
    (hL12 : ∀ τ : ℝ, 0 ≤ τ → Work.Construction.L12 (Work.FTS.Galerkin.slice g τ) 0 = 0)
    (hw : ∃ C : ℝ, ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ →
      θ < Real.pi / 2 → |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ) z θ|
        ≤ C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)) :
    ∃ KS : ℝ, 0 ≤ KS ∧ ∀ k : Fin 6, ∀ z θ σ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ σ → σ ≤ S →
      |Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
        (Work.FTS.RegExportIface.RXT.idx k).2
        (Work.FTS.RegExportIface.RXT.SigR α Φs E g σ) z θ|
        ≤ KS * Work.FTS.RegExportIface.ω α z θ := by
  obtain ⟨K, hK0, hK⟩ :=
    Zhat_bound (C₀ := C₀) hα hα13 hS hOK hVP hV2 hC2 hL12 hw
  have hβ0 : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hβ1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  have hc0 : 0 < Work.Spaces.c (Work.FTS.Regularity.pExp α) := by
    have := (Work.Spaces.c_bounds (Work.FTS.Regularity.pExp α) hβ0 hβ1).1
    linarith
  refine ⟨(Work.FTS.Regularity.pExp α / Work.Spaces.c (Work.FTS.Regularity.pExp α))
      * 4 * 100000 * K, by positivity, ?_⟩
  intro k z θ σ hz hθ0 hθ1 hσ0 hσS
  have hσ : σ ∈ Set.Icc (0:ℝ) S := ⟨hσ0, hσS⟩
  have hji : (Work.FTS.RegExportIface.RXT.idx k).1
      + (Work.FTS.RegExportIface.RXT.idx k).2 ≤ 2 := by
    fin_cases k <;> decide
  have hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ0, hθ1⟩
  have hZc : ContDiffOn ℝ 2 (Function.uncurry (fun z θ =>
      Work.FTS.RegExportIface.RXT.VR α Φs E g z θ σ * A1f z θ
        + Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
            * B1f (Work.FTS.Regularity.pExp α) z θ
        + Work.FTS.RegExportIface.RXT.cR α Φs E g z θ σ * Fhf z θ))
      Work.FTS.EllipticEst.Q0 :=
    Zhat_contDiffOn (C₀ := C₀) hα hα13 hS hC2 σ hσ
  have hZb : |Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
      (Work.FTS.RegExportIface.RXT.idx k).2 (fun z θ =>
      Work.FTS.RegExportIface.RXT.VR α Φs E g z θ σ * A1f z θ
        + Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
            * B1f (Work.FTS.Regularity.pExp α) z θ
        + Work.FTS.RegExportIface.RXT.cR α Φs E g z θ σ * Fhf z θ) z θ|
      ≤ K * (z ^ 2 / (1 + z) ^ 2) :=
    hK σ hσ (Work.FTS.RegExportIface.RXT.idx k).1 (Work.FTS.RegExportIface.RXT.idx k).2
      hji z θ hz hθ0 hθ1
  have hEq : Set.EqOn (Function.uncurry (Work.FTS.RegExportIface.RXT.SigR α Φs E g σ))
      (Function.uncurry (fun z θ => (Work.FTS.Regularity.pExp α
        / Work.Spaces.c (Work.FTS.Regularity.pExp α))
        * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
        * (Work.FTS.RegExportIface.RXT.VR α Φs E g z θ σ * A1f z θ
            + Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
                * B1f (Work.FTS.Regularity.pExp α) z θ
            + Work.FTS.RegExportIface.RXT.cR α Φs E g z θ σ * Fhf z θ)))
      Work.FTS.EllipticEst.Q0 := by
    intro p hp
    obtain ⟨z', θ'⟩ := p
    exact Work.FTS_RegExport.RXT.SysAux.SigR_eq_reduced hα hα13 hS σ ⟨hσ0, hσS⟩
      z' θ' hp.1 hp.2.1 hp.2.2
  have hfGam : ContDiffOn ℝ ((Work.FTS.RegExportIface.RXT.idx k).1
      + (Work.FTS.RegExportIface.RXT.idx k).2)
      (Function.uncurry (fun _ θ : ℝ => Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ))
      Work.FTS.EllipticEst.Q0 := by
    have hG := Work.FTS_RegExport.RXT.ftau_contDiffOn_Gam_Q0 (Work.FTS.Regularity.pExp α)
      ((Work.FTS.RegExportIface.RXT.idx k).1 + (Work.FTS.RegExportIface.RXT.idx k).2)
    rw [Nat.cast_add] at hG
    exact hG
  have hbfGam : ∀ a b : ℕ, a + b ≤ (Work.FTS.RegExportIface.RXT.idx k).1
      + (Work.FTS.RegExportIface.RXT.idx k).2 →
      |Work.Spaces.mixed b a (fun z θ : ℝ => Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ) z θ|
        ≤ 100000 * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ := by
    intro a b hab
    rcases Nat.eq_zero_or_pos b with hb | hb
    · subst hb
      rw [Work.Spaces.mixed, Work.Spaces.DzIter_zero]
      rw [show Work.Spaces.DthIter a (fun z θ : ℝ => Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ) z θ
          = Work.Spaces.DthIter a (fun _ θ' : ℝ => Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ') z θ
          from rfl]
      rw [DthIter_z_indep (fun θ' => Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ') a z 0 θ]
      exact Work.FTS.LocData6.DthIter_Gam_abs_le6 a (by omega)
        (Work.FTS.Regularity.pExp α) hβ0 hβ1 ⟨hθ0.le, hθ1.le⟩
    · rw [mixed_theta_only (fun θ' => Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ') hb z θ,
        abs_zero]
      exact mul_nonneg (by norm_num) (Work.Spaces.Gam_bounds (Work.FTS.Regularity.pExp α)
        θ hβ0 ⟨hθ0.le, hθ1.le⟩).1
  have hbhZ : ∀ a b : ℕ, a + b ≤ (Work.FTS.RegExportIface.RXT.idx k).1
      + (Work.FTS.RegExportIface.RXT.idx k).2 →
      |Work.Spaces.mixed b a (fun z θ =>
        Work.FTS.RegExportIface.RXT.VR α Φs E g z θ σ * A1f z θ
          + Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
              * B1f (Work.FTS.Regularity.pExp α) z θ
          + Work.FTS.RegExportIface.RXT.cR α Φs E g z θ σ * Fhf z θ) z θ|
        ≤ K * (z ^ 2 / (1 + z) ^ 2) :=
      fun a b hab => hK σ hσ b a (by omega) z θ hz hθ0 hθ1
  have hGam : |Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
      (Work.FTS.RegExportIface.RXT.idx k).2 (fun z θ =>
        Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
        * (Work.FTS.RegExportIface.RXT.VR α Φs E g z θ σ * A1f z θ
            + Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
                * B1f (Work.FTS.Regularity.pExp α) z θ
            + Work.FTS.RegExportIface.RXT.cR α Φs E g z θ σ * Fhf z θ)) z θ|
      ≤ 4 * (100000 * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ)
        * (K * (z ^ 2 / (1 + z) ^ 2)) := by
    refine le_trans (abs_mixed_mul_bound (j := (Work.FTS.RegExportIface.RXT.idx k).1)
      (i := (Work.FTS.RegExportIface.RXT.idx k).2) (V := Work.FTS.EllipticEst.Q0)
      Work.FTS.EllipticEst.isOpen_Q0
      (by
        have hG := Work.FTS_RegExport.RXT.ftau_contDiffOn_Gam_Q0 (Work.FTS.Regularity.pExp α)
          ((Work.FTS.RegExportIface.RXT.idx k).1 + (Work.FTS.RegExportIface.RXT.idx k).2)
        rw [Nat.cast_add] at hG
        exact hG)
      (hZc.of_le (Nat.cast_le.mpr hji)) hzθ
      (Cf := 100000 * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ)
      (Cg := K * (z ^ 2 / (1 + z) ^ 2))
      (mul_nonneg (by norm_num) (Work.Spaces.Gam_bounds (Work.FTS.Regularity.pExp α) θ hβ0
        ⟨hθ0.le, hθ1.le⟩).1)
      (mul_nonneg hK0 (by positivity)) hbfGam hbhZ) ?_
    have hpow : (2 : ℝ) ^ ((Work.FTS.RegExportIface.RXT.idx k).1
        + (Work.FTS.RegExportIface.RXT.idx k).2) ≤ 4 := by
      calc (2 : ℝ) ^ ((Work.FTS.RegExportIface.RXT.idx k).1
            + (Work.FTS.RegExportIface.RXT.idx k).2) ≤ 2 ^ 2 :=
            pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hji
        _ = 4 := by norm_num
    have hCfCg : 0 ≤ (100000 * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ)
        * (K * (z ^ 2 / (1 + z) ^ 2)) :=
      mul_nonneg (mul_nonneg (by norm_num) (Work.Spaces.Gam_bounds (Work.FTS.Regularity.pExp α)
        θ hβ0 ⟨hθ0.le, hθ1.le⟩).1) (mul_nonneg hK0 (by positivity))
    calc (2 : ℝ) ^ ((Work.FTS.RegExportIface.RXT.idx k).1
          + (Work.FTS.RegExportIface.RXT.idx k).2)
          * ((100000 * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ)
            * (K * (z ^ 2 / (1 + z) ^ 2)))
        ≤ 4 * ((100000 * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ)
            * (K * (z ^ 2 / (1 + z) ^ 2))) := mul_le_mul_of_nonneg_right hpow hCfCg
      _ = 4 * (100000 * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ)
            * (K * (z ^ 2 / (1 + z) ^ 2)) := by ring
  calc |Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
        (Work.FTS.RegExportIface.RXT.idx k).2
        (Work.FTS.RegExportIface.RXT.SigR α Φs E g σ) z θ|
      = |Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
          (Work.FTS.RegExportIface.RXT.idx k).2 (fun z θ => (Work.FTS.Regularity.pExp α
            / Work.Spaces.c (Work.FTS.Regularity.pExp α))
            * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
            * (Work.FTS.RegExportIface.RXT.VR α Φs E g z θ σ * A1f z θ
                + Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
                    * B1f (Work.FTS.Regularity.pExp α) z θ
                + Work.FTS.RegExportIface.RXT.cR α Φs E g z θ σ * Fhf z θ)) z θ| := by
        rw [Work.FTS_RegExport.RXT.SysAux.mixed_congr_of_isOpen
          Work.FTS.EllipticEst.isOpen_Q0 hEq _ _ z θ hzθ]
    _ = |(Work.FTS.Regularity.pExp α / Work.Spaces.c (Work.FTS.Regularity.pExp α))
          * Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
              (Work.FTS.RegExportIface.RXT.idx k).2 (fun z θ =>
              Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
              * (Work.FTS.RegExportIface.RXT.VR α Φs E g z θ σ * A1f z θ
                  + Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
                      * B1f (Work.FTS.Regularity.pExp α) z θ
                  + Work.FTS.RegExportIface.RXT.cR α Φs E g z θ σ * Fhf z θ)) z θ| := by
        rw [show (fun z θ => (Work.FTS.Regularity.pExp α
              / Work.Spaces.c (Work.FTS.Regularity.pExp α))
              * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
              * (Work.FTS.RegExportIface.RXT.VR α Φs E g z θ σ * A1f z θ
                  + Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
                      * B1f (Work.FTS.Regularity.pExp α) z θ
                  + Work.FTS.RegExportIface.RXT.cR α Φs E g z θ σ * Fhf z θ))
            = fun z θ => (Work.FTS.Regularity.pExp α
              / Work.Spaces.c (Work.FTS.Regularity.pExp α))
              * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
              * (Work.FTS.RegExportIface.RXT.VR α Φs E g z θ σ * A1f z θ
                  + Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
                      * B1f (Work.FTS.Regularity.pExp α) z θ
                  + Work.FTS.RegExportIface.RXT.cR α Φs E g z θ σ * Fhf z θ)) from by
            funext z' θ'; ring,
          mixed_const_mul]
    _ = (Work.FTS.Regularity.pExp α / Work.Spaces.c (Work.FTS.Regularity.pExp α))
          * |Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
              (Work.FTS.RegExportIface.RXT.idx k).2 (fun z θ =>
              Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
              * (Work.FTS.RegExportIface.RXT.VR α Φs E g z θ σ * A1f z θ
                  + Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
                      * B1f (Work.FTS.Regularity.pExp α) z θ
                  + Work.FTS.RegExportIface.RXT.cR α Φs E g z θ σ * Fhf z θ)) z θ| := by
        rw [abs_mul, abs_of_nonneg (by positivity)]
    _ ≤ (Work.FTS.Regularity.pExp α / Work.Spaces.c (Work.FTS.Regularity.pExp α))
          * (4 * (100000 * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ)
              * (K * (z ^ 2 / (1 + z) ^ 2))) :=
        mul_le_mul_of_nonneg_left hGam (by positivity)
    _ = ((Work.FTS.Regularity.pExp α / Work.Spaces.c (Work.FTS.Regularity.pExp α))
          * 4 * 100000 * K) * Work.FTS.RegExportIface.ω α z θ := by
        rw [Work.FTS_RegExport.RXT.Gam_pExp_eq_Gamma, Work.FTS.RegExportIface.ω]
        ring

end Work.FTS_RegExport.RXT.Sys
