import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS_RegExport.RXT.CoeffJetsDefs
import Submission.Work.FTS_RegExport.RXT.jc3
import Submission.Work.FTS_RegExport.RXT.coeff_C2
import Submission.Work.FTS_RegExport.RXT.datum_bound
import Submission.Work.FTS_RegExport.RXT.velVanish2
import Submission.Work.FTS_RegExport.RXA2w.lim_mixed_weighted_proved
import Submission.Work.FTS_RegExport.RXB.l12_zero_lim_proved
import Submission.Work.FTS_RegExport.RXT.Sys.weighted_integrated_mp
import Submission.Work.FTS_RegExport.RXT.Sys.mixed_integral_identity
import Submission.Work.FTS_RegExport.RXT.Sys.gdot_system
import Submission.Work.FTS_RegExport.RXT.Sys.gdot_regular
import Submission.Work.FTS_RegExport.RXT.Sys.forcing_bound
import Submission.Work.FTS_RegExport.RXT.Sys.gdot_eq_profile
import Submission.Work.FTS_RegExport.RXT.Sys.intervalIntegrable_mixed_gdot
import Submission.Work.FTS_RegExport.RXT.Sys.intervalIntegrable_if_zero_add
import Submission.Work.FTS_RegExport.RXT.Sys.intervalIntegral_if_zero
import Submission.Work.FTS_RegExport.RXT.Sys.coeff_jets
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_z
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_theta
import Submission.Work.FTS_RegExport.RXT.Sys.datum_jets

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.weighted_system` — S8 of the RX-St1 leaf plan (the assembly)

The weighted `St1` bound for the six components `D_z^jD_θ^i (slice g τ)`, `(j,i) = idx k`:

  `∃ K, ∀ k, ∀ τ ∈ [0,S], ∀ (z,θ) ∈ Q0, |D^β_k(g(τ))(z,θ)| ≤ K·ω(z,θ)`, `ω = z²Γ(θ)/(1+z)²`.

Assembly (leaf-plan S8, with the closed-θ package `VelPkg` — whose `bnd`/`vz0`/`cont`/`axis`
clauses are false for the constructed profile — replaced by the true, open-θ
`Work.FTS_RegExport.RXT.CoeffJets`):

* `coeff_C2` (S4), `coeff_jets` (the `CoeffJets` producer), `gdot_eq_profile` (`hEqF`),
  X1 (`velVanish2`), RX-B (`l12_zero_lim_proved`), RX-A2w (`lim_mixed_weighted_proved`);
* `gdot_regular` (S5c) → `GdotLoc`; `gdot_system` (S5b); `forcing_bound` (S6);
  `mixed_integral_identity` (S5a); `intervalIntegrable_mixed_gdot`;
* `jc3` (S3) for the joint continuity of the six components, `hasDerivAt_mixed_z`/`_theta` for
  the partials, `datum_bound`/`datum_jets` for the `τ = 0` data;
* T5c (`weighted_integrated_mp`) with `w_k = D^β_k(g(τ))`, `wz_k = D^{β+z}_k(g(τ))`,
  `wθ_k = D^{β+θ}_k(g(τ))`, coefficients `Vz = Vz7`, `b = Vθ7/sin 2θ`, source
  `R_k = D^β_k(∂_τg) + Vz·wz_k + b·wθ_k` (the value at `τ = 0` is replaced by `0`; this changes
  the integrand on the null set `{0}` only, whence `intervalIntegral_if_zero`).
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT

open Work.FTS.Galerkin (Fn Fam slice gdot)
open Work.FTS.RegExportIface (ω Vz7 Vθ7 cs7 phiTil)
open Work.FTS.RegExportIface.RXT (idx VR bR cR SigR μR GR ΦR GdotLoc)
open Work.FTS.RegPkgGal (extG)
open Work.FTS.Regularity (pExp profFull)
open Work.FTS.FinalV2 (gS tauExt LimApprox DynOK' EllLimOK3 Sol)
open Work.FTS.Nonlin (PsiCan)

set_option autoImplicit false

theorem weighted_system {α Ce C₀ Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    {g : Work.FTS.Galerkin.Fam} (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hdat : ∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ,
      g z θ 0 = Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) L β z θ)
    (hμ : Work.FTS.RegExportIface.ClockBd α Φs E g) :
    ∀ S > 0, ∃ K : ℝ, ∀ k : Fin 6, ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z θ,
      0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
        (Work.FTS.RegExportIface.RXT.idx k).2
        (Work.FTS.Galerkin.slice g τ) z θ| ≤ K * Work.FTS.RegExportIface.ω α z θ := by
  intro S hS
  have hp : 0 < pExp α := Work.FTS.Regularity.pExp_pos hα
  have hp1 : pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  -- ## the ingredients
  have hC2 := coeff_C2 (α := α) (C₀ := C₀) (Cs := Cs) hα hα13 hEL3 hStar hOK
  have hVPall := Work.FTS_RegExport.RXT.Sys.coeff_jets (α := α) hα hα13 hEll hEL3 hStar hSol hOK hμ
  have hVP : CoeffJets (pExp α) (μR α Φs E g) (GR α g) (ΦR α Φs E g) S := hVPall S hS
  have hEqF := Work.FTS_RegExport.RXT.Sys.gdot_eq_profile (α := α) hS hα hα13 hEll hEL3 hStar
    hSol hOK hμ
  have hG : GdotLoc S g :=
    Work.FTS_RegExport.RXT.Sys.gdot_regular (α := α) hS hα hα13 hOK hVP hC2 hEqF
  obtain ⟨Cc, hCc0, hCc⟩ :=
    Work.FTS_RegExport.RXT.Sys.gdot_system (α := α) hS hα hα13 hOK hVP hC2 hEqF
  have hIdS5a := Work.FTS_RegExport.RXT.Sys.mixed_integral_identity (α := α) hS hα hα13 hSol hOK hG
  have hIntG :=
    Work.FTS_RegExport.RXT.Sys.intervalIntegrable_mixed_gdot (α := α) hS hα hα13 hSol hOK hG
  have hjc := jc3 (α := α) (C₀ := C₀) hα hα13 hOK S hS
  have hV2 := velVanish2 (α := α) hα hα13 hEll hEL3 hStar hSol hOK hμ S hS
  have hL12 : ∀ τ : ℝ, 0 ≤ τ → Work.Construction.L12 (slice g τ) 0 = 0 :=
    fun τ hτ => Work.FTS_RegExport.RXB.l12_zero_lim_proved (αG := pExp α) (C₀ := C₀) hp hOK.2 τ hτ
  obtain ⟨Ch, hCh0, hCh⟩ := Work.FTS_RegExport.RXA2w.lim_mixed_weighted_proved
    (αG := pExp α) (C₀ := C₀) hp hp1 hOK.2 S hS
  have hw : ∃ C : ℝ, ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ →
      θ < π / 2 → |Work.Spaces.mixed b a (slice g τ) z θ| ≤ C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) :=
    ⟨Ch, hCh⟩
  obtain ⟨KS, hKS0, hKS⟩ :=
    Work.FTS_RegExport.RXT.Sys.forcing_bound (α := α) hS hα hα13 hOK hVP hV2 hC2 hL12 hw
  obtain ⟨Ld, βd, hLd, hdatL⟩ := hdat
  obtain ⟨K₀, hK₀0, hK₀⟩ := datum_bound (α := α) hα hα13 hLd
  obtain ⟨Kd, hKd0, hKd⟩ := Work.FTS_RegExport.RXT.Sys.datum_jets (α := α) hα hα13 hLd
  obtain ⟨M, hMbd⟩ := hVP.dbnd
  have hM0 : 0 ≤ M := by
    have h := (hMbd 0 ⟨le_rfl, hS.le⟩ 0 0 (by norm_num) 1 (π / 4) one_pos
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])).1
    simp only [Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right,
      Work.Spaces.DthIter_zero, Work.Spaces.DzIter_zero] at h
    exact le_trans (abs_nonneg _) h
  -- ## index bookkeeping
  have hidx2 : ∀ k : Fin 6, (idx k).1 + (idx k).2 ≤ 2 := by
    intro k; fin_cases k <;> decide
  have hidx3 : ∀ k : Fin 6, (idx k).1 + (idx k).2 ≤ 3 := fun k => by have := hidx2 k; omega
  have hslice0 : slice g 0 = Work.FTS.LocData6.locG6 (pExp α) Ld βd := by
    funext z θ
    exact hdatL z θ
  have hω_nonneg : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → 0 ≤ ω α z θ :=
    fun z θ hz hθ hθ' => ((omega_facts α hα).1 z θ hz hθ hθ').le
  have hpath : ∀ z θ : ℝ, ContinuousOn (fun τ : ℝ => (z, θ, τ)) (Set.Icc 0 S) := fun z θ => by
    fun_prop
  -- ## T5c
  obtain ⟨K, hK⟩ := Work.FTS_RegExport.RXT.Sys.weighted_integrated_mp (n := 6) (α := α) (S := S)
    (M := M) (C := Cc) (K₀ := K₀) (Kσ := max KS (2 * M * Kd))
    (w := fun k z θ τ => Work.Spaces.mixed (idx k).1 (idx k).2 (slice g τ) z θ)
    (wz := fun k z θ τ => Work.Spaces.mixed ((idx k).1 + 1) (idx k).2 (slice g τ) z θ)
    (wθ := fun k z θ τ => Work.Spaces.mixed (idx k).1 ((idx k).2 + 1) (slice g τ) z θ)
    (R := fun k z θ τ =>
      (if τ = 0 then 0 else Work.Spaces.mixed (idx k).1 (idx k).2 (gdot g τ) z θ)
        + VR α Φs E g z θ τ * Work.Spaces.mixed ((idx k).1 + 1) (idx k).2 (slice g τ) z θ
        + bR α Φs E g z θ τ * Work.Spaces.mixed (idx k).1 ((idx k).2 + 1) (slice g τ) z θ)
    (Vz := fun z θ τ => VR α Φs E g z θ τ)
    (b := fun z θ τ => bR α Φs E g z θ τ)
    hα hS
    (fun k => hjc (idx k).1 (idx k).2 (hidx3 k))
    (fun k z θ τ hz hθ hθ' hτ =>
      Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_z ((hOK.1.1).c4 τ hτ.1)
        (idx k).1 (idx k).2 (hidx3 k) hz hθ hθ')
    (fun k z θ τ hz hθ hθ' hτ =>
      Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_theta ((hOK.1.1).c4 τ hτ.1)
        (idx k).1 (idx k).2 (hidx3 k) hz hθ hθ')
    (fun k => hjc ((idx k).1 + 1) (idx k).2 (by have := hidx2 k; omega))
    (fun k => hjc (idx k).1 ((idx k).2 + 1) (by have := hidx2 k; omega))
    (fun z θ hz hθ hθ' =>
      ⟨(hVP.cont z θ hz hθ hθ').fst, (hVP.cont z θ hz hθ hθ').snd.fst⟩)
    (fun z θ τ hz hθ hθ' hτ => by
      have h := hMbd τ hτ 0 0 (by norm_num) z θ hz hθ hθ'
      simp only [Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right,
        Work.Spaces.DthIter_zero, Work.Spaces.DzIter_zero] at h
      exact ⟨h.1, h.2.1⟩)
    (fun k z θ hz hθ hθ' => by
      refine Work.FTS_RegExport.RXT.Sys.intervalIntegrable_if_zero_add hS
        (hIntG k z θ hz hθ hθ') ?_ ?_
      · refine ContinuousOn.mul (hVP.cont z θ hz hθ hθ').fst ?_
        exact (hjc ((idx k).1 + 1) (idx k).2 (by have := hidx2 k; omega)).comp
          (hpath z θ) (fun τ hτ => ⟨hz, ⟨hθ, hθ'⟩, hτ⟩)
      · refine ContinuousOn.mul (hVP.cont z θ hz hθ hθ').snd.fst ?_
        exact (hjc (idx k).1 ((idx k).2 + 1) (by have := hidx2 k; omega)).comp
          (hpath z θ) (fun τ hτ => ⟨hz, ⟨hθ, hθ'⟩, hτ⟩))
    (fun k z θ τ hz hθ hθ' hτ => by
      by_cases h0 : τ = 0
      · subst h0
        have hω0 := hω_nonneg z θ hz hθ hθ'
        have hVR := (hMbd 0 ⟨le_rfl, hS.le⟩ 0 0 (by norm_num) z θ hz hθ hθ')
        simp only [Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right,
          Work.Spaces.DthIter_zero, Work.Spaces.DzIter_zero] at hVR
        have hwz : |Work.Spaces.mixed ((idx k).1 + 1) (idx k).2 (slice g 0) z θ|
            ≤ Kd * ω α z θ := by
          rw [hslice0]
          exact hKd ((idx k).1 + 1) (idx k).2 (by have := hidx2 k; omega)
            (by have := hidx2 k; omega) z θ hz hθ hθ'
        have hwθ : |Work.Spaces.mixed (idx k).1 ((idx k).2 + 1) (slice g 0) z θ|
            ≤ Kd * ω α z θ := by
          rw [hslice0]
          exact hKd (idx k).1 ((idx k).2 + 1) (by have := hidx2 k; omega)
            (by have := hidx2 k; omega) z θ hz hθ hθ'
        have hsrc : |(0:ℝ) + VR α Φs E g z θ 0 * Work.Spaces.mixed ((idx k).1 + 1) (idx k).2
                (slice g 0) z θ
              + bR α Φs E g z θ 0 * Work.Spaces.mixed (idx k).1 ((idx k).2 + 1) (slice g 0) z θ|
            ≤ (max KS (2 * M * Kd)) * ω α z θ := by
          have h3 := abs_add_le
            (VR α Φs E g z θ 0 * Work.Spaces.mixed ((idx k).1 + 1) (idx k).2 (slice g 0) z θ)
            (bR α Φs E g z θ 0 * Work.Spaces.mixed (idx k).1 ((idx k).2 + 1) (slice g 0) z θ)
          rw [abs_mul, abs_mul] at h3
          have h4 : |VR α Φs E g z θ 0|
                * |Work.Spaces.mixed ((idx k).1 + 1) (idx k).2 (slice g 0) z θ|
              ≤ M * (Kd * ω α z θ) := mul_le_mul hVR.1 hwz (abs_nonneg _) hM0
          have h5 : |bR α Φs E g z θ 0|
                * |Work.Spaces.mixed (idx k).1 ((idx k).2 + 1) (slice g 0) z θ|
              ≤ M * (Kd * ω α z θ) := mul_le_mul hVR.2.1 hwθ (abs_nonneg _) hM0
          have h6 : |(0:ℝ) + VR α Φs E g z θ 0 * Work.Spaces.mixed ((idx k).1 + 1) (idx k).2
                (slice g 0) z θ
              + bR α Φs E g z θ 0 * Work.Spaces.mixed (idx k).1 ((idx k).2 + 1)
                (slice g 0) z θ| ≤ 2 * M * Kd * ω α z θ := by
            calc |(0:ℝ) + VR α Φs E g z θ 0 * Work.Spaces.mixed ((idx k).1 + 1) (idx k).2
                  (slice g 0) z θ
                + bR α Φs E g z θ 0 * Work.Spaces.mixed (idx k).1 ((idx k).2 + 1)
                  (slice g 0) z θ|
                = |VR α Φs E g z θ 0 * Work.Spaces.mixed ((idx k).1 + 1) (idx k).2
                    (slice g 0) z θ
                  + bR α Φs E g z θ 0 * Work.Spaces.mixed (idx k).1 ((idx k).2 + 1)
                    (slice g 0) z θ| := by ring_nf
              _ ≤ (M * (Kd * ω α z θ)) + (M * (Kd * ω α z θ)) := by linarith
              _ = 2 * M * Kd * ω α z θ := by ring
          calc |(0:ℝ) + VR α Φs E g z θ 0 * Work.Spaces.mixed ((idx k).1 + 1) (idx k).2
                (slice g 0) z θ
              + bR α Φs E g z θ 0 * Work.Spaces.mixed (idx k).1 ((idx k).2 + 1)
                (slice g 0) z θ| ≤ 2 * M * Kd * ω α z θ := h6
            _ ≤ (max KS (2 * M * Kd)) * ω α z θ :=
                mul_le_mul_of_nonneg_right (le_max_right _ _) hω0
        have hfin : |(if (0:ℝ) = 0 then 0 else Work.Spaces.mixed (idx k).1 (idx k).2
                (gdot g 0) z θ)
              + VR α Φs E g z θ 0 * Work.Spaces.mixed ((idx k).1 + 1) (idx k).2 (slice g 0) z θ
              + bR α Φs E g z θ 0 * Work.Spaces.mixed (idx k).1 ((idx k).2 + 1)
                (slice g 0) z θ| ≤ (max KS (2 * M * Kd)) * ω α z θ := by
          simpa only [if_true] using hsrc
        calc |(if (0:ℝ) = 0 then 0 else Work.Spaces.mixed (idx k).1 (idx k).2 (gdot g 0) z θ)
              + VR α Φs E g z θ 0 * Work.Spaces.mixed ((idx k).1 + 1) (idx k).2 (slice g 0) z θ
              + bR α Φs E g z θ 0 * Work.Spaces.mixed (idx k).1 ((idx k).2 + 1)
                (slice g 0) z θ| ≤ (max KS (2 * M * Kd)) * ω α z θ := hfin
          _ ≤ Cc * ∑ j : Fin 6, |Work.Spaces.mixed (idx j).1 (idx j).2 (slice g 0) z θ|
                + (max KS (2 * M * Kd)) * ω α z θ :=
              le_add_of_nonneg_left (mul_nonneg hCc0 (Finset.sum_nonneg (fun j _ => abs_nonneg _)))
      · have hτpos : 0 < τ := lt_of_le_of_ne hτ.1 (Ne.symm h0)
        have hω0 := hω_nonneg z θ hz hθ hθ'
        have hA := hCc k z θ τ hz hθ hθ' hτpos hτ.2
        have hB := hKS k z θ τ hz hθ hθ' hτ.1 hτ.2
        have hsplit : |Work.Spaces.mixed (idx k).1 (idx k).2 (gdot g τ) z θ
              + (VR α Φs E g z θ τ * Work.Spaces.mixed ((idx k).1 + 1) (idx k).2 (slice g τ) z θ
                + bR α Φs E g z θ τ * Work.Spaces.mixed (idx k).1 ((idx k).2 + 1)
                  (slice g τ) z θ)|
            ≤ Cc * ∑ j : Fin 6, |Work.Spaces.mixed (idx j).1 (idx j).2 (slice g τ) z θ|
              + KS * ω α z θ := by
          have h4 : |Work.Spaces.mixed (idx k).1 (idx k).2 (gdot g τ) z θ
                + (VR α Φs E g z θ τ * Work.Spaces.mixed ((idx k).1 + 1) (idx k).2
                    (slice g τ) z θ
                  + bR α Φs E g z θ τ * Work.Spaces.mixed (idx k).1 ((idx k).2 + 1)
                    (slice g τ) z θ)|
              ≤ |Work.Spaces.mixed (idx k).1 (idx k).2 (gdot g τ) z θ
                  + (VR α Φs E g z θ τ * Work.Spaces.mixed ((idx k).1 + 1) (idx k).2
                      (slice g τ) z θ
                    + bR α Φs E g z θ τ * Work.Spaces.mixed (idx k).1 ((idx k).2 + 1)
                      (slice g τ) z θ)
                  + Work.Spaces.mixed (idx k).1 (idx k).2 (SigR α Φs E g τ) z θ|
                + |Work.Spaces.mixed (idx k).1 (idx k).2 (SigR α Φs E g τ) z θ| := by
            have h5 := abs_sub_le
              (Work.Spaces.mixed (idx k).1 (idx k).2 (gdot g τ) z θ
                + (VR α Φs E g z θ τ * Work.Spaces.mixed ((idx k).1 + 1) (idx k).2
                    (slice g τ) z θ
                  + bR α Φs E g z θ τ * Work.Spaces.mixed (idx k).1 ((idx k).2 + 1)
                    (slice g τ) z θ))
              (-(Work.Spaces.mixed (idx k).1 (idx k).2 (SigR α Φs E g τ) z θ)) 0
            simpa using h5
          linarith [h4, hA, hB]
        have hrw : (if τ = 0 then 0 else Work.Spaces.mixed (idx k).1 (idx k).2 (gdot g τ) z θ)
              + VR α Φs E g z θ τ * Work.Spaces.mixed ((idx k).1 + 1) (idx k).2 (slice g τ) z θ
              + bR α Φs E g z θ τ * Work.Spaces.mixed (idx k).1 ((idx k).2 + 1) (slice g τ) z θ
            = Work.Spaces.mixed (idx k).1 (idx k).2 (gdot g τ) z θ
              + (VR α Φs E g z θ τ * Work.Spaces.mixed ((idx k).1 + 1) (idx k).2 (slice g τ) z θ
                + bR α Φs E g z θ τ * Work.Spaces.mixed (idx k).1 ((idx k).2 + 1)
                  (slice g τ) z θ) := by
          rw [if_neg h0, add_assoc]
        rw [hrw]
        have hle : KS * ω α z θ ≤ (max KS (2 * M * Kd)) * ω α z θ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hω0
        linarith [hsplit, hle])
    (fun k z θ τ₁ τ₂ hz hθ hθ' h1 h12 h2 => by
      have h5 := hIdS5a k z θ hz hθ hθ' τ₁ τ₂ h1 h12 h2
      rw [h5]
      have hcongr : (∫ σ in τ₁..τ₂, ((if σ = 0 then 0 else
              Work.Spaces.mixed (idx k).1 (idx k).2 (gdot g σ) z θ)
            + VR α Φs E g z θ σ * Work.Spaces.mixed ((idx k).1 + 1) (idx k).2 (slice g σ) z θ
            + bR α Φs E g z θ σ * Work.Spaces.mixed (idx k).1 ((idx k).2 + 1) (slice g σ) z θ
          - (VR α Φs E g z θ σ * Work.Spaces.mixed ((idx k).1 + 1) (idx k).2 (slice g σ) z θ
            + bR α Φs E g z θ σ * Work.Spaces.mixed (idx k).1 ((idx k).2 + 1) (slice g σ) z θ)))
          = ∫ σ in τ₁..τ₂, (if σ = 0 then 0 else
              Work.Spaces.mixed (idx k).1 (idx k).2 (gdot g σ) z θ) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards with σ hσ
        have hσ0 : σ ≠ 0 := by
          have hlt : min τ₁ τ₂ < σ := hσ.1
          rw [min_eq_left h12] at hlt
          exact ne_of_gt (lt_of_le_of_lt h1 hlt)
        rw [if_neg hσ0]
        ring
      rw [hcongr, Work.FTS_RegExport.RXT.Sys.intervalIntegral_if_zero (f := fun σ =>
        Work.Spaces.mixed (idx k).1 (idx k).2 (gdot g σ) z θ) h1])
    (fun k z θ hz hθ hθ' => by
      rw [hslice0]
      exact hK₀ k z θ hz hθ hθ')
  exact ⟨K, fun k τ hτ z θ hz hθ hθ' => hK k z θ τ hz hθ hθ' hτ⟩

end Work.FTS_RegExport.RXT
