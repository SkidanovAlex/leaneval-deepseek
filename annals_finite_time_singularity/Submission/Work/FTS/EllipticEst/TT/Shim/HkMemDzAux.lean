/-
Copyright: work module for the Elgindi finite-time singularity project.

# The certificate `HkMem α k (D_z Ψ)`, assembled

This module proves `Work.FTS.EllipticEst.TT.HkMem_Dz_psi`: for `0 < α ≤ 1/4` and data
`(F, Ψ)` in the class `EllHyp α k` of §'Elliptic Regularity Estimates',
`D_z Ψ = z ∂_z Ψ` belongs to the weighted space `ℋ^k`.

It is the copy, in the `TT` namespace and free of `sorry`, of
`Submission/Work/FTS/EllipticEst/Cert/HkMem_Dz_psi.lean` with its two tainted inputs
(`Cert/ExcessR_integrable`, `Cert/ExcessM_integrable` and their Agmon input
`Cert/rDz_AMGM_diff`) replaced by the proved siblings `TT/ExcessR_integrable`,
`TT/ExcessM_integrable`, `TT/rDz_AMGM_fin`, and with the `D_θ`-bookkeeping input
`Cert/HkMem_Dth_of_pth` replaced by the `sorry`-free `TT/HkMem_Dth_of_pth` (module
`TT/DthAux.lean`).

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.TT.Shim.DzPsiAux
import Submission.Work.FTS.EllipticEst.Cert.HkIntegrand_Dz_le
import Submission.Work.FTS.EllipticEst.Cert.HkIntegrand_continuousOn_open
import Submission.Work.FTS.EllipticEst.TT.Shim.DthAux
import Submission.Work.FTS.EllipticEst.TT.Shim.ExcessR_integrable
import Submission.Work.FTS.EllipticEst.TT.Shim.ExcessM_integrable
import Submission.Work.FTS.LocData.HkMem_of_majorant

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## The four input terms

Each input term is a summand of an integrand whose honesty is a field of `EllHyp`, so
`Work.FTS.EllipticEst.Cert.DzAux.summand_props` delivers the four facts (slice integrability, integrability of the slice
integrals, `z`-integrability of the slices for a.e. angle, finiteness of the outer `∫⁻`). -/

private theorem PR_facts (α : ℝ) (k : ℕ) (Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ)
    (hmem : Work.Spaces.HkMem α k Ψ) :
    (∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => Work.FTS.EllipticEst.Cert.DzAux.PR Ψ k z θ) Work.Spaces.Iθ) ∧
      IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Cert.DzAux.PR Ψ k z θ) Work.Spaces.Iz ∧
      (∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        IntegrableOn (fun z => Work.FTS.EllipticEst.Cert.DzAux.PR Ψ k z θ) Work.Spaces.Iz) ∧
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
        (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.Cert.DzAux.PR Ψ k z θ)) < ⊤ :=
  Work.FTS.EllipticEst.Cert.DzAux.summand_props hmem (Work.FTS.EllipticEst.Cert.DzAux.aeMeas_ofReal_HkIntegrand α k hsm)
    (fun z θ => sq_nonneg _)
    (fun z θ => Work.Spaces.sq_le_HkIntegrand_z α k Ψ z θ k le_rfl)
    ((Work.Spaces.HPRZ.aesm_DzIter_H_weight_prod Ψ hsm k).pow 2)
    (fun z hz => Work.FTS.EllipticEst.Cert.DzAux.aesm_zSummand_slice α hsm k hz)
    (fun θ hθ => Work.FTS.EllipticEst.Cert.DzAux.aesm_zslice_zSummand hsm k hθ)

private theorem ZR_facts (α : ℝ) (k : ℕ) (Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ)
    (hmem : Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :
    (∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => Work.FTS.EllipticEst.Cert.DzAux.ZR Ψ k z θ) Work.Spaces.Iθ) ∧
      IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Cert.DzAux.ZR Ψ k z θ) Work.Spaces.Iz ∧
      (∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        IntegrableOn (fun z => Work.FTS.EllipticEst.Cert.DzAux.ZR Ψ k z θ) Work.Spaces.Iz) ∧
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
        (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.Cert.DzAux.ZR Ψ k z θ)) < ⊤ :=
  Work.FTS.EllipticEst.Cert.DzAux.summand_props hmem (Work.FTS.EllipticEst.Cert.DzAux.aeMeas_ofReal_HkIntegrand α k (Work.FTS.EllipticEst.Cert.DzAux.SmoothNbhd_zsq hsm))
    (fun z θ => sq_nonneg _)
    (fun z θ => Work.Spaces.sq_le_HkIntegrand_z α k
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ k le_rfl)
    ((Work.Spaces.HPRZ.aesm_DzIter_H_weight_prod (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      (Work.FTS.EllipticEst.Cert.DzAux.SmoothNbhd_zsq hsm) k).pow 2)
    (fun z hz => Work.FTS.EllipticEst.Cert.DzAux.aesm_zSummand_slice α (Work.FTS.EllipticEst.Cert.DzAux.SmoothNbhd_zsq hsm) k hz)
    (fun θ hθ => Work.FTS.EllipticEst.Cert.DzAux.aesm_zslice_zSummand (Work.FTS.EllipticEst.Cert.DzAux.SmoothNbhd_zsq hsm) k hθ)

private theorem PM_facts (α : ℝ) (k : ℕ) (Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ)
    (hk : 1 ≤ k) (hmem : Work.Spaces.HkMem α k Ψ) :
    (∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => Work.FTS.EllipticEst.Cert.DzAux.PM α Ψ k z θ) Work.Spaces.Iθ) ∧
      IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Cert.DzAux.PM α Ψ k z θ) Work.Spaces.Iz ∧
      (∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        IntegrableOn (fun z => Work.FTS.EllipticEst.Cert.DzAux.PM α Ψ k z θ) Work.Spaces.Iz) ∧
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
        (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.Cert.DzAux.PM α Ψ k z θ)) < ⊤ :=
  Work.FTS.EllipticEst.Cert.DzAux.summand_props hmem (Work.FTS.EllipticEst.Cert.DzAux.aeMeas_ofReal_HkIntegrand α k hsm)
    (fun z θ => sq_nonneg _)
    (fun z θ => Work.Spaces.sq_le_HkIntegrand_mixed α k Ψ z θ 1 (k - 1) le_rfl (by omega))
    (Work.Spaces.aesm_mixed_Wt_sq_prod α Ψ hsm (k - 1) 1)
    (fun z hz => Work.FTS.EllipticEst.Cert.DzAux.aesm_mixed_Wt_sq_slice α hsm (k - 1) 1 hz)
    (fun θ hθ => Work.FTS.EllipticEst.Cert.DzAux.aesm_zslice_mixedSummand α hsm (k - 1) 1 hθ)

private theorem ZM_facts (α : ℝ) (k : ℕ) (Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ)
    (hk : 1 ≤ k)
    (hmem : Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :
    (∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => Work.FTS.EllipticEst.Cert.DzAux.ZM α Ψ k z θ) Work.Spaces.Iθ) ∧
      IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Cert.DzAux.ZM α Ψ k z θ) Work.Spaces.Iz ∧
      (∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        IntegrableOn (fun z => Work.FTS.EllipticEst.Cert.DzAux.ZM α Ψ k z θ) Work.Spaces.Iz) ∧
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
        (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.Cert.DzAux.ZM α Ψ k z θ)) < ⊤ :=
  Work.FTS.EllipticEst.Cert.DzAux.summand_props hmem (Work.FTS.EllipticEst.Cert.DzAux.aeMeas_ofReal_HkIntegrand α k (Work.FTS.EllipticEst.Cert.DzAux.SmoothNbhd_zsq hsm))
    (fun z θ => sq_nonneg _)
    (fun z θ => Work.Spaces.sq_le_HkIntegrand_mixed α k
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ 1 (k - 1) le_rfl (by omega))
    (Work.Spaces.aesm_mixed_Wt_sq_prod α (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      (Work.FTS.EllipticEst.Cert.DzAux.SmoothNbhd_zsq hsm) (k - 1) 1)
    (fun z hz => Work.FTS.EllipticEst.Cert.DzAux.aesm_mixed_Wt_sq_slice α (Work.FTS.EllipticEst.Cert.DzAux.SmoothNbhd_zsq hsm) (k - 1) 1 hz)
    (fun θ hθ => Work.FTS.EllipticEst.Cert.DzAux.aesm_zslice_mixedSummand α (Work.FTS.EllipticEst.Cert.DzAux.SmoothNbhd_zsq hsm) (k - 1) 1 hθ)

/-! ## The two excess terms -/

/-- The `θ`-slice of the excess radial term is integrable. -/
private theorem EXR_slice (α : ℝ) (k : ℕ) (Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ)
    (hα : 0 < α) (hα1 : α ≤ 1) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    IntegrableOn (fun θ => Work.FTS.EllipticEst.Cert.DzAux.EXR Ψ k z θ) Work.Spaces.Iθ :=
  Work.FTS.EllipticEst.Cert.DzAux.EXR_slice_integrable k Ψ hsm hz

/-- The `θ`-slice of the excess mixed term is integrable. -/
private theorem EXM_slice (α : ℝ) (k : ℕ) (Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ)
    (hα : 0 < α) (hα1 : α ≤ 1) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    IntegrableOn (fun θ => Work.FTS.EllipticEst.Cert.DzAux.EXM α Ψ k z θ) Work.Spaces.Iθ :=
  Work.FTS.EllipticEst.Cert.DzAux.EXM_slice_integrable α k Ψ hsm hα hα1 hz

/-- Joint measurability of the excess radial term on the product measure. -/
private theorem EXR_aesm (α : ℝ) (k : ℕ) (Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => Work.FTS.EllipticEst.Cert.DzAux.EXR Ψ k p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
  (Work.Spaces.HPRZ.aesm_DzIter_H_weight_prod Ψ hsm (k + 1)).pow 2

/-- Joint measurability of the excess mixed term on the product measure. -/
private theorem EXM_aesm (α : ℝ) (k : ℕ) (Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => Work.FTS.EllipticEst.Cert.DzAux.EXM α Ψ k p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
  show AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (Work.Spaces.mixed k 0 (Work.Spaces.Dth Ψ) p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
    ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))
  exact Work.Spaces.aesm_mixed_Wt_sq_prod α (Work.Spaces.Dth Ψ)
    (Work.Spaces.SmoothNbhd.Dth hsm) k 0

/-! ## The certificate -/

theorem HkMem_Dz_psi (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hHyp : Work.FTS.EllipticEst.EllHyp α k F Ψ) :
    Work.Spaces.HkMem α k (Work.Spaces.Dz Ψ) := by
  have hα1 : α ≤ 1 := by linarith
  have hsm : Work.Spaces.SmoothNbhd Ψ := hHyp.smoothNbhd
  -- `EllHyp` provides the *plain* angular derivative `∂_θΨ`; the bookkeeping needs the
  -- weighted one `D_θΨ = sin(2θ)∂_θΨ`.
  have hDthMem : Work.Spaces.HkMem α k (Work.Spaces.Dth Ψ) :=
    HkMem_Dth_of_pth α hα hα1 k hsm hHyp.memDth
  rcases k with _ | k'
  · -- ## The case `k = 0`: the only excess term is the radial one
    obtain ⟨-, hPRz, hPRae, hPRlin⟩ := PR_facts α 0 Ψ hsm hHyp.memPsi
    obtain ⟨-, hZRz, hZRae, hZRlin⟩ := ZR_facts α 0 Ψ hsm hHyp.memZ2
    have hEXRsl : ∀ z ∈ Work.Spaces.Iz,
        IntegrableOn (fun θ => Work.FTS.EllipticEst.Cert.DzAux.EXR Ψ 0 z θ) Work.Spaces.Iθ :=
      fun z hz => EXR_slice α 0 Ψ hsm hα hα1 hz
    have hEXRint := ExcessR_integrable α 0 Ψ hsm hα hα1 hPRz hPRae hPRlin hZRz hZRae hZRlin
      hEXRsl (EXR_aesm α 0 Ψ hsm)
    refine Work.FTS.LocData.HkMem_of_majorant α 0 (f := Work.Spaces.Dz Ψ)
      (M := (fun z θ => Work.Spaces.HkIntegrand α 0 Ψ z θ)
        + (fun z θ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dth Ψ) z θ)
        + (fun z θ => Work.FTS.EllipticEst.Cert.DzAux.EXR Ψ 0 z θ))
      (Work.FTS.EllipticEst.Cert.HkIntegrand_continuousOn_open α 0 (Work.Spaces.SmoothNbhd.Dz hsm)) ?_ ?_ ?_
    · intro z hz
      have h := ((hHyp.memPsi.1 z hz).add (hDthMem.1 z hz)).add (hEXRsl z hz)
      simp only [Pi.add_apply] at h ⊢
      exact h
    · refine (((hHyp.memPsi.2).add hDthMem.2).add hEXRint).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
      simp only [Pi.add_apply]
      rw [integral_add (show Integrable (fun θ : ℝ => Work.Spaces.HkIntegrand α 0 Ψ z θ
            + Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dth Ψ) z θ)
              (volume.restrict Work.Spaces.Iθ) from
            (hHyp.memPsi.1 z hz).add (hDthMem.1 z hz))
          (hEXRsl z hz)]
      rw [integral_add (hHyp.memPsi.1 z hz) (hDthMem.1 z hz)]
    · intro z hz θ hθ
      have h1 : Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz Ψ) z θ
          = (Work.Spaces.DzIter 1 Ψ z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        simp [Work.Spaces.HkIntegrand]
      have h2 : Work.FTS.EllipticEst.Cert.DzAux.EXR Ψ 0 z θ = (Work.Spaces.DzIter 1 Ψ z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := rfl
      simp only [Pi.add_apply]
      rw [h1, h2]
      linarith [Work.Spaces.HkIntegrand_nonneg α 0 Ψ z θ,
        Work.Spaces.HkIntegrand_nonneg α 0 (Work.Spaces.Dth Ψ) z θ]
  · -- ## The case `k = k' + 1`: both excess terms occur
    have hk : 1 ≤ k' + 1 := by omega
    obtain ⟨-, hPRz, hPRae, hPRlin⟩ := PR_facts α (k' + 1) Ψ hsm hHyp.memPsi
    obtain ⟨-, hZRz, hZRae, hZRlin⟩ := ZR_facts α (k' + 1) Ψ hsm hHyp.memZ2
    obtain ⟨-, hPMz, hPMae, hPMlin⟩ := PM_facts α (k' + 1) Ψ hsm hk hHyp.memPsi
    obtain ⟨-, hZMz, hZMae, hZMlin⟩ := ZM_facts α (k' + 1) Ψ hsm hk hHyp.memZ2
    have hEXRsl : ∀ z ∈ Work.Spaces.Iz,
        IntegrableOn (fun θ => Work.FTS.EllipticEst.Cert.DzAux.EXR Ψ (k' + 1) z θ) Work.Spaces.Iθ :=
      fun z hz => EXR_slice α (k' + 1) Ψ hsm hα hα1 hz
    have hEXMsl : ∀ z ∈ Work.Spaces.Iz,
        IntegrableOn (fun θ => Work.FTS.EllipticEst.Cert.DzAux.EXM α Ψ (k' + 1) z θ) Work.Spaces.Iθ :=
      fun z hz => EXM_slice α (k' + 1) Ψ hsm hα hα1 hz
    have hEXRint := ExcessR_integrable α (k' + 1) Ψ hsm hα hα1 hPRz hPRae hPRlin hZRz hZRae
      hZRlin hEXRsl (EXR_aesm α (k' + 1) Ψ hsm)
    have hEXMint := ExcessM_integrable α (k' + 1) Ψ hsm hα hα1 hk hPMz hPMae hPMlin hZMz hZMae
      hZMlin hEXMsl (EXM_aesm α (k' + 1) Ψ hsm)
    refine Work.FTS.LocData.HkMem_of_majorant α (k' + 1) (f := Work.Spaces.Dz Ψ)
      (M := (fun z θ => Work.Spaces.HkIntegrand α (k' + 1) Ψ z θ)
        + (fun z θ => Work.Spaces.HkIntegrand α (k' + 1) (Work.Spaces.Dth Ψ) z θ)
        + (fun z θ => Work.FTS.EllipticEst.Cert.DzAux.EXR Ψ (k' + 1) z θ)
        + (fun z θ => Work.FTS.EllipticEst.Cert.DzAux.EXM α Ψ (k' + 1) z θ))
      (Work.FTS.EllipticEst.Cert.HkIntegrand_continuousOn_open α (k' + 1) (Work.Spaces.SmoothNbhd.Dz hsm)) ?_ ?_ ?_
    · intro z hz
      have h := (((hHyp.memPsi.1 z hz).add (hDthMem.1 z hz)).add (hEXRsl z hz)).add
        (hEXMsl z hz)
      simp only [Pi.add_apply] at h ⊢
      exact h
    · refine ((((hHyp.memPsi.2).add hDthMem.2).add hEXRint).add hEXMint).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
      simp only [Pi.add_apply]
      rw [integral_add (show Integrable (fun θ : ℝ =>
              (Work.Spaces.HkIntegrand α (k' + 1) Ψ z θ
                + Work.Spaces.HkIntegrand α (k' + 1) (Work.Spaces.Dth Ψ) z θ)
              + Work.FTS.EllipticEst.Cert.DzAux.EXR Ψ (k' + 1) z θ) (volume.restrict Work.Spaces.Iθ) from
            ((hHyp.memPsi.1 z hz).add (hDthMem.1 z hz)).add (hEXRsl z hz))
          (hEXMsl z hz)]
      rw [integral_add (show Integrable (fun θ : ℝ =>
            Work.Spaces.HkIntegrand α (k' + 1) Ψ z θ
              + Work.Spaces.HkIntegrand α (k' + 1) (Work.Spaces.Dth Ψ) z θ)
              (volume.restrict Work.Spaces.Iθ) from
            (hHyp.memPsi.1 z hz).add (hDthMem.1 z hz))
          (hEXRsl z hz)]
      rw [integral_add (hHyp.memPsi.1 z hz) (hDthMem.1 z hz)]
    · intro z hz θ hθ
      have h1 := Work.FTS.EllipticEst.Cert.HkIntegrand_Dz_le α (k' + 1) Ψ hsm hα z θ hz hθ
      have h2 : Work.FTS.EllipticEst.Cert.DzAux.EXR Ψ (k' + 1) z θ = (Work.Spaces.DzIter (k' + 1 + 1) Ψ z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := rfl
      have h3 : Work.FTS.EllipticEst.Cert.DzAux.EXM α Ψ (k' + 1) z θ = (Work.Spaces.DzIter (k' + 1) (Work.Spaces.Dth Ψ) z θ
          * Work.Spaces.Wt α z θ) ^ 2 := rfl
      simp only [Pi.add_apply] at h1 ⊢
      rw [h2, h3]
      simpa only [Work.Spaces.DzIter_succ] using h1


theorem HkMem_Dz_psi_a1 (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hHyp : Work.FTS.EllipticEst.EllHyp α k F Ψ) :
    Work.Spaces.HkMem α k (Work.Spaces.Dz Ψ) := by
  have hsm : Work.Spaces.SmoothNbhd Ψ := hHyp.smoothNbhd
  -- `EllHyp` provides the *plain* angular derivative `∂_θΨ`; the bookkeeping needs the
  -- weighted one `D_θΨ = sin(2θ)∂_θΨ`.
  have hDthMem : Work.Spaces.HkMem α k (Work.Spaces.Dth Ψ) :=
    HkMem_Dth_of_pth α hα hα1 k hsm hHyp.memDth
  rcases k with _ | k'
  · -- ## The case `k = 0`: the only excess term is the radial one
    obtain ⟨-, hPRz, hPRae, hPRlin⟩ := PR_facts α 0 Ψ hsm hHyp.memPsi
    obtain ⟨-, hZRz, hZRae, hZRlin⟩ := ZR_facts α 0 Ψ hsm hHyp.memZ2
    have hEXRsl : ∀ z ∈ Work.Spaces.Iz,
        IntegrableOn (fun θ => Work.FTS.EllipticEst.Cert.DzAux.EXR Ψ 0 z θ) Work.Spaces.Iθ :=
      fun z hz => EXR_slice α 0 Ψ hsm hα hα1 hz
    have hEXRint := ExcessR_integrable α 0 Ψ hsm hα hα1 hPRz hPRae hPRlin hZRz hZRae hZRlin
      hEXRsl (EXR_aesm α 0 Ψ hsm)
    refine Work.FTS.LocData.HkMem_of_majorant α 0 (f := Work.Spaces.Dz Ψ)
      (M := (fun z θ => Work.Spaces.HkIntegrand α 0 Ψ z θ)
        + (fun z θ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dth Ψ) z θ)
        + (fun z θ => Work.FTS.EllipticEst.Cert.DzAux.EXR Ψ 0 z θ))
      (Work.FTS.EllipticEst.Cert.HkIntegrand_continuousOn_open α 0 (Work.Spaces.SmoothNbhd.Dz hsm)) ?_ ?_ ?_
    · intro z hz
      have h := ((hHyp.memPsi.1 z hz).add (hDthMem.1 z hz)).add (hEXRsl z hz)
      simp only [Pi.add_apply] at h ⊢
      exact h
    · refine (((hHyp.memPsi.2).add hDthMem.2).add hEXRint).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
      simp only [Pi.add_apply]
      rw [integral_add (show Integrable (fun θ : ℝ => Work.Spaces.HkIntegrand α 0 Ψ z θ
            + Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dth Ψ) z θ)
              (volume.restrict Work.Spaces.Iθ) from
            (hHyp.memPsi.1 z hz).add (hDthMem.1 z hz))
          (hEXRsl z hz)]
      rw [integral_add (hHyp.memPsi.1 z hz) (hDthMem.1 z hz)]
    · intro z hz θ hθ
      have h1 : Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz Ψ) z θ
          = (Work.Spaces.DzIter 1 Ψ z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        simp [Work.Spaces.HkIntegrand]
      have h2 : Work.FTS.EllipticEst.Cert.DzAux.EXR Ψ 0 z θ = (Work.Spaces.DzIter 1 Ψ z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := rfl
      simp only [Pi.add_apply]
      rw [h1, h2]
      linarith [Work.Spaces.HkIntegrand_nonneg α 0 Ψ z θ,
        Work.Spaces.HkIntegrand_nonneg α 0 (Work.Spaces.Dth Ψ) z θ]
  · -- ## The case `k = k' + 1`: both excess terms occur
    have hk : 1 ≤ k' + 1 := by omega
    obtain ⟨-, hPRz, hPRae, hPRlin⟩ := PR_facts α (k' + 1) Ψ hsm hHyp.memPsi
    obtain ⟨-, hZRz, hZRae, hZRlin⟩ := ZR_facts α (k' + 1) Ψ hsm hHyp.memZ2
    obtain ⟨-, hPMz, hPMae, hPMlin⟩ := PM_facts α (k' + 1) Ψ hsm hk hHyp.memPsi
    obtain ⟨-, hZMz, hZMae, hZMlin⟩ := ZM_facts α (k' + 1) Ψ hsm hk hHyp.memZ2
    have hEXRsl : ∀ z ∈ Work.Spaces.Iz,
        IntegrableOn (fun θ => Work.FTS.EllipticEst.Cert.DzAux.EXR Ψ (k' + 1) z θ) Work.Spaces.Iθ :=
      fun z hz => EXR_slice α (k' + 1) Ψ hsm hα hα1 hz
    have hEXMsl : ∀ z ∈ Work.Spaces.Iz,
        IntegrableOn (fun θ => Work.FTS.EllipticEst.Cert.DzAux.EXM α Ψ (k' + 1) z θ) Work.Spaces.Iθ :=
      fun z hz => EXM_slice α (k' + 1) Ψ hsm hα hα1 hz
    have hEXRint := ExcessR_integrable α (k' + 1) Ψ hsm hα hα1 hPRz hPRae hPRlin hZRz hZRae
      hZRlin hEXRsl (EXR_aesm α (k' + 1) Ψ hsm)
    have hEXMint := ExcessM_integrable α (k' + 1) Ψ hsm hα hα1 hk hPMz hPMae hPMlin hZMz hZMae
      hZMlin hEXMsl (EXM_aesm α (k' + 1) Ψ hsm)
    refine Work.FTS.LocData.HkMem_of_majorant α (k' + 1) (f := Work.Spaces.Dz Ψ)
      (M := (fun z θ => Work.Spaces.HkIntegrand α (k' + 1) Ψ z θ)
        + (fun z θ => Work.Spaces.HkIntegrand α (k' + 1) (Work.Spaces.Dth Ψ) z θ)
        + (fun z θ => Work.FTS.EllipticEst.Cert.DzAux.EXR Ψ (k' + 1) z θ)
        + (fun z θ => Work.FTS.EllipticEst.Cert.DzAux.EXM α Ψ (k' + 1) z θ))
      (Work.FTS.EllipticEst.Cert.HkIntegrand_continuousOn_open α (k' + 1) (Work.Spaces.SmoothNbhd.Dz hsm)) ?_ ?_ ?_
    · intro z hz
      have h := (((hHyp.memPsi.1 z hz).add (hDthMem.1 z hz)).add (hEXRsl z hz)).add
        (hEXMsl z hz)
      simp only [Pi.add_apply] at h ⊢
      exact h
    · refine ((((hHyp.memPsi.2).add hDthMem.2).add hEXRint).add hEXMint).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
      simp only [Pi.add_apply]
      rw [integral_add (show Integrable (fun θ : ℝ =>
              (Work.Spaces.HkIntegrand α (k' + 1) Ψ z θ
                + Work.Spaces.HkIntegrand α (k' + 1) (Work.Spaces.Dth Ψ) z θ)
              + Work.FTS.EllipticEst.Cert.DzAux.EXR Ψ (k' + 1) z θ) (volume.restrict Work.Spaces.Iθ) from
            ((hHyp.memPsi.1 z hz).add (hDthMem.1 z hz)).add (hEXRsl z hz))
          (hEXMsl z hz)]
      rw [integral_add (show Integrable (fun θ : ℝ =>
            Work.Spaces.HkIntegrand α (k' + 1) Ψ z θ
              + Work.Spaces.HkIntegrand α (k' + 1) (Work.Spaces.Dth Ψ) z θ)
              (volume.restrict Work.Spaces.Iθ) from
            (hHyp.memPsi.1 z hz).add (hDthMem.1 z hz))
          (hEXRsl z hz)]
      rw [integral_add (hHyp.memPsi.1 z hz) (hDthMem.1 z hz)]
    · intro z hz θ hθ
      have h1 := Work.FTS.EllipticEst.Cert.HkIntegrand_Dz_le α (k' + 1) Ψ hsm hα z θ hz hθ
      have h2 : Work.FTS.EllipticEst.Cert.DzAux.EXR Ψ (k' + 1) z θ = (Work.Spaces.DzIter (k' + 1 + 1) Ψ z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := rfl
      have h3 : Work.FTS.EllipticEst.Cert.DzAux.EXM α Ψ (k' + 1) z θ = (Work.Spaces.DzIter (k' + 1) (Work.Spaces.Dth Ψ) z θ
          * Work.Spaces.Wt α z θ) ^ 2 := rfl
      simp only [Pi.add_apply] at h1 ⊢
      rw [h2, h3]
      simpa only [Work.Spaces.DzIter_succ] using h1

end Work.FTS.EllipticEst.TT
