import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_MuLamOK.Rows.Rl2Open
import Submission.Work.FTS_RegExport.RXT.C2Radial
import Submission.Work.FTS_RegExport.RXT.Sys.FBDefs
import Submission.Work.FTS_RegExport.RXT.Sys.FBZhatP
import Submission.Work.FTS_RegExport.RXT.Sys.L12FK_family_jets
import Submission.Work.FTS_RegExport.RXT.Sys.slice_contDiffOn_four
import Submission.Work.FTS_RegExport.RXT.SysAux.bR_decomp
import Submission.Work.FTS_RegExport.RXT.coeff_C2
import Submission.Work.FTS_RegExport.RXT.contDiffOn_two_integral_Itheta
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_RegExport.RXT.velVanish2Aux
import Submission.Work.FTS_RegExport.RXT0.L12FtauTauLip
import Submission.Work.FTS_RegExport.RXVP3.velPert_unif
import Submission.Work.FTS_RegExport.THL.Defs
import Submission.Work.FTS_RegExport.THL.vopPert_theta_holder
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Spaces.bt_integral_weight_id
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.FBZhatB =====
section

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

/-!
# `Work.FTS_RegExport.RXT.Sys.FBZhatB` — the weighted jet bound for `Ẑ`, assembled
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport.RXT.Sys

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem Zhat_contDiffOn {α C₀ S : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hS : 0 < S)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hC2 : ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.VR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.bR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.cR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0) :
    ∀ σ ∈ Set.Icc (0:ℝ) S,
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ =>
        Work.FTS.RegExportIface.RXT.VR α Φs E g z θ σ * A1f z θ
          + Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
              * B1f (Work.FTS.Regularity.pExp α) z θ
          + Work.FTS.RegExportIface.RXT.cR α Φs E g z θ σ * Fhf z θ))
        Work.FTS.EllipticEst.Q0 := by
  intro σ hσ
  obtain ⟨hVR, hbR, hcR⟩ := hC2 σ hσ.1
  have h1 : ContDiffOn ℝ 2 (Function.uncurry (fun z θ =>
      Work.FTS.RegExportIface.RXT.VR α Φs E g z θ σ * A1f z θ)) Work.FTS.EllipticEst.Q0 :=
    (hVR.mul (contDiffOn_A1f 2)).congr (fun p _ => rfl)
  have h2 : ContDiffOn ℝ 2 (Function.uncurry (fun z θ =>
      Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
        * B1f (Work.FTS.Regularity.pExp α) z θ)) Work.FTS.EllipticEst.Q0 :=
    (hbR.mul (contDiffOn_B1f 2 (Work.FTS.Regularity.pExp α))).congr (fun p _ => rfl)
  have h3 : ContDiffOn ℝ 2 (Function.uncurry (fun z θ =>
      Work.FTS.RegExportIface.RXT.cR α Φs E g z θ σ * Fhf z θ)) Work.FTS.EllipticEst.Q0 :=
    (hcR.mul (contDiffOn_Fhf 2)).congr (fun p _ => rfl)
  exact ((h1.add h2).add h3).congr (fun p _ => by
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry, Pi.add_apply])

theorem Zhat_bound {α C₀ S : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hS : 0 < S)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
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
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ ∈ Set.Icc (0:ℝ) S, ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ,
      0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (fun z θ =>
          Work.FTS.RegExportIface.RXT.VR α Φs E g z θ σ * A1f z θ
          + Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
              * B1f (Work.FTS.Regularity.pExp α) z θ
          + Work.FTS.RegExportIface.RXT.cR α Φs E g z θ σ * Fhf z θ) z θ|
        ≤ K * (z ^ 2 / (1 + z) ^ 2) := by
  obtain ⟨Mv, hMv⟩ := hVP.dbnd
  obtain ⟨M2, hM2⟩ := hV2
  obtain ⟨Ce, hCe0, hCe⟩ := Work.FTS_RegExport.RXT.SysAux.explicit_piece_bounds
  obtain ⟨Cl, hCl0, hCl⟩ := Work.FTS_RegExport.RXT.SysAux.LgKg_Ftau_facts hα hα13 hS hOK hL12 hw
  have hbr := Work.FTS_RegExport.RXT.SysAux.bR_decomp hα hα13 hS hOK hC2 hL12 hw
  have hβ0 : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hβ1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  have hL12d : ∀ σ ∈ Set.Icc (0:ℝ) S, ∀ z : ℝ, 0 < z →
      z * deriv (fun z' => Work.Construction.L12 (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) σ) z') z
        = -Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) σ) z :=
    fun σ hσ z hz => (hCl σ hσ).2.2.2.2.2.2.2 z hz
  have hVz' : ∃ M : ℝ, ∀ σ ∈ Set.Icc (0:ℝ) S, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.FTS.RegExportIface.Vz7 (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.μR α Φs E g)
        (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g)
        z θ σ| ≤ M :=
    ⟨Mv, fun σ hσ z θ hz hθ0 hθ1 => by
      have h := (hMv σ hσ 0 0 (by norm_num) z θ hz hθ0 hθ1).1
      simpa using h⟩
  have hVop' : ∃ M : ℝ, ∀ σ ∈ Set.Icc (0:ℝ) S, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Construction.Vop (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ)
        z θ| ≤ M * min z 1 :=
    ⟨M2, fun σ hσ z θ hz hθ0 hθ1 => by
      have h := hM2 σ hσ z θ hz hθ0 hθ1
        (Work.Construction.Vop (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ))
        (by rw [Set.mem_insert_iff]; right; rw [Set.mem_insert_iff]; left; rfl)
        0 0 (by norm_num)
      simpa using h⟩
  have hL12b : ∃ C : ℝ, ∀ σ ∈ Set.Icc (0:ℝ) S, ∀ z : ℝ, 0 < z →
      |Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) σ) z| ≤ C :=
    ⟨2 * Work.FTS.Regularity.pExp α + Cl, fun σ hσ z hz => by
      have hLK := Work.FTS_RegExport.RXT.SysAux.L12_FK_Ftau_split hα hα13 hS hOK hw σ hσ z hz
      rw [hLK.1]
      have hb := (hCl σ hσ).2.2.2.1 0 (by norm_num) z hz
      have hb2 : |Work.Construction.L12 (Work.FTS.Galerkin.slice
          (Work.FTS.RegExportIface.RXT.GR α g) σ) z| ≤ Cl := by
        refine le_trans hb ?_
        calc Cl * (z ^ ((3:ℝ)/2) / (1 + z) ^ 2) ≤ Cl * 1 :=
              mul_le_mul_of_nonneg_left (wt_le_one hz) hCl0.le
          _ = Cl := mul_one Cl
      have hnum : |2 * Work.FTS.Regularity.pExp α / (1 + z)| ≤ 2 * Work.FTS.Regularity.pExp α := by
        rw [abs_of_nonneg (by positivity)]
        rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 + z)]
        nlinarith [hβ0]
      calc |2 * Work.FTS.Regularity.pExp α / (1 + z)
            + Work.Construction.L12 (Work.FTS.Galerkin.slice
              (Work.FTS.RegExportIface.RXT.GR α g) σ) z|
          ≤ |2 * Work.FTS.Regularity.pExp α / (1 + z)|
            + |Work.Construction.L12 (Work.FTS.Galerkin.slice
              (Work.FTS.RegExportIface.RXT.GR α g) σ) z| := abs_add_le _ _
        _ ≤ 2 * Work.FTS.Regularity.pExp α + Cl := add_le_add hnum hb2⟩
  obtain ⟨Cmu, hCmu0, hCmu⟩ :=
    Work.FTS_RegExport.RXT.SysAux.muR_bound hα hα13 hS hVz' hVop' hL12b
  refine ⟨Ce * (1 + Cmu) + (4 * Cl * Ce * (1 + 1 / Work.FTS.Regularity.pExp α)
      + (4 * Cl * Ce * (1 + Work.FTS.Regularity.pExp α)
      + (8 * Work.FTS.Regularity.pExp α * max M2 0 * Ce
      + (8 * max M2 0 * Ce * Work.FTS.Regularity.pExp α + 8 * max M2 0 * Ce)))),
    by positivity, ?_⟩
  intro σ hσ j i hji z θ hz hθ0 hθ1
  -- the perturbation-slot smoothness
  have hps := Work.FTS_RegExport.RXT.SysAux.pertSlot_contDiffOn (C₀ := C₀) hα hα13 hS hC2 hbr
    (fun τ hτ => (hCl τ hτ).1) (fun τ hτ => (hCl τ hτ).2.2.2.2.2.2.1) σ hσ
  have hmemV : ∀ a b : ℕ, a + b ≤ 2 → ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      |Work.Spaces.mixed b a (Work.Construction.Vop (PtF α Φs E g σ)) z' θ'|
        ≤ max M2 0 * min z' 1 := by
    intro a b hab z' θ' hz' hθ0' hθ1'
    have h := hM2 σ hσ z' θ' hz' hθ0' hθ1'
      (Work.Construction.Vop (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ))
      (by rw [Set.mem_insert_iff]; right; rw [Set.mem_insert_iff]; left; rfl) b a (by omega)
    exact le_trans h (mul_le_mul_of_nonneg_right (le_max_left _ _) (le_min hz'.le zero_le_one))
  have hmemR : ∀ a b : ℕ, a + b ≤ 2 → ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      |Work.Spaces.mixed b a (Work.Construction.Rop (Work.FTS.Regularity.pExp α) (PtF α Φs E g σ))
        z' θ'| ≤ max M2 0 * min z' 1 := by
    intro a b hab z' θ' hz' hθ0' hθ1'
    have h := hM2 σ hσ z' θ' hz' hθ0' hθ1'
      (Work.Construction.Rop (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ))
      (by rw [Set.mem_insert_iff]; left; rfl) b a (by omega)
    exact le_trans h (mul_le_mul_of_nonneg_right (le_max_left _ _) (le_min hz'.le zero_le_one))
  have hmemU : ∀ a b : ℕ, a + b ≤ 2 → ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      |Work.Spaces.mixed b a (fun z θ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
        (PtF α Φs E g σ) z θ / Real.sin (2 * θ)) z' θ'| ≤ max M2 0 * min z' 1 := by
    intro a b hab z' θ' hz' hθ0' hθ1'
    have h := hM2 σ hσ z' θ' hz' hθ0' hθ1'
      (fun z θ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ) z θ
        / Real.sin (2 * θ))
      (by rw [Set.mem_insert_iff]; right; rw [Set.mem_insert_iff]; right; rfl) b a (by omega)
    exact le_trans h (mul_le_mul_of_nonneg_right (le_max_left _ _) (le_min hz'.le zero_le_one))
  -- the per-piece bounds
  have b0 : |Work.Spaces.mixed j i (Pp0 α Φs E g σ) z θ|
      ≤ Ce * (1 + Cmu) * (z ^ 2 / (1 + z) ^ 2) :=
    Pp0_bound hCe0 hCmu0 (fun j' i' hj'i' z' θ' hz' hθ0' hθ1' =>
      (hCe z' θ' hz' hθ0' hθ1' (Work.FTS.RegExportIface.RXT.μR α Φs E g σ)
        (Work.FTS.Regularity.pExp α) hβ0 hβ1).1 j' i' hj'i') (hCmu σ hσ)
      j i hji z θ hz hθ0 hθ1
  have b1 : |Work.Spaces.mixed j i (Pp1 α g σ) z θ|
      ≤ 4 * (Cl * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2))
        * (Ce * (1 + 1 / Work.FTS.Regularity.pExp α) * (z / (1 + z) ^ 2)) :=
    Pp1_bound hCe0 hCl0 hβ0 (hCl σ hσ).2.2.2.2.2.1 (hCl σ hσ).2.2.2.1
      (fun j' i' hj'i' z' θ' hz' hθ0' hθ1' =>
        (hCe z' θ' hz' hθ0' hθ1' (Work.FTS.RegExportIface.RXT.μR α Φs E g σ)
          (Work.FTS.Regularity.pExp α) hβ0 hβ1).2.2.2.2.1 j' i' hj'i')
      j i hji z θ hz hθ0 hθ1
  have b2 : |Work.Spaces.mixed j i (Pp2 α g σ) z θ|
      ≤ 4 * (Cl * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2))
        * (Ce * (1 + Work.FTS.Regularity.pExp α) * (z / (1 + z) ^ 2)) :=
    Pp2_bound hCe0 hCl0 hβ0 (hCl σ hσ).2.2.2.2.1 (hCl σ hσ).2.2.1
      (fun j' i' hj'i' z' θ' hz' hθ0' hθ1' =>
        (hCe z' θ' hz' hθ0' hθ1' (Work.FTS.RegExportIface.RXT.μR α Φs E g σ)
          (Work.FTS.Regularity.pExp α) hβ0 hβ1).2.2.2.2.2 j' i' hj'i')
      j i hji z θ hz hθ0 hθ1
  have b3 : |Work.Spaces.mixed j i (Pp3 α Φs E g σ) z θ|
      ≤ 4 * (2 * Work.FTS.Regularity.pExp α * max M2 0 * min z 1)
        * (Ce * (z / (1 + z) ^ 2)) :=
    Pp3_bound hCe0 (le_max_right _ _) hβ0 hps.1 hmemV
      (fun j' i' hj'i' z' θ' hz' hθ0' hθ1' =>
        (hCe z' θ' hz' hθ0' hθ1' (Work.FTS.RegExportIface.RXT.μR α Φs E g σ)
          (Work.FTS.Regularity.pExp α) hβ0 hβ1).2.1 j' i' hj'i')
      j i hji z θ hz hθ0 hθ1
  have b4 : |Work.Spaces.mixed j i (Pp4 α Φs E g σ) z θ|
      ≤ 4 * (2 * max M2 0 * min z 1)
        * (Ce * Work.FTS.Regularity.pExp α * (z / (1 + z) ^ 2)) :=
    Pp4_bound hCe0 (le_max_right _ _) hβ0 hps.2.1 hmemU
      (fun j' i' hj'i' z' θ' hz' hθ0' hθ1' =>
        (hCe z' θ' hz' hθ0' hθ1' (Work.FTS.RegExportIface.RXT.μR α Φs E g σ)
          (Work.FTS.Regularity.pExp α) hβ0 hβ1).2.2.2.1 j' i' hj'i')
      j i hji z θ hz hθ0 hθ1
  have b5 : |Work.Spaces.mixed j i (Pp5 α Φs E g σ) z θ|
      ≤ 4 * (2 * max M2 0 * min z 1) * (Ce * (z / (1 + z) ^ 2)) :=
    Pp5_bound hCe0 (le_max_right _ _) hβ0 hps.2.2 hmemR
      (fun j' i' hj'i' z' θ' hz' hθ0' hθ1' =>
        (hCe z' θ' hz' hθ0' hθ1' (Work.FTS.RegExportIface.RXT.μR α Φs E g σ)
          (Work.FTS.Regularity.pExp α) hβ0 hβ1).2.2.1 j' i' hj'i')
      j i hji z θ hz hθ0 hθ1
  -- smoothness of the pieces and additivity of `mixed`
  have hcd0 : ContDiffOn ℝ 2 (Function.uncurry (Pp0 α Φs E g σ)) Work.FTS.EllipticEst.Q0 :=
    (contDiffOn_Ef 2 _ _).congr (fun p _ => rfl)
  have hLgC2 : ContDiffOn ℝ 2 (LgF α g σ) (Set.Ioi 0) :=
    ContDiffOn.of_le ((hCl σ hσ).2.2.2.2.2.1) (Nat.cast_le.mpr (by norm_num : 2 ≤ 3))
  have hKgC2 : ContDiffOn ℝ 2 (KgF α g σ) (Set.Ioi 0) := (hCl σ hσ).2.2.2.2.1
  have hcd1 : ContDiffOn ℝ 2 (Function.uncurry (Pp1 α g σ)) Work.FTS.EllipticEst.Q0 :=
    ((contDiffOn_uncurry_fst hLgC2).mul (contDiffOn_al1f 2 (Work.FTS.Regularity.pExp α))).congr (fun p _ => rfl)
  have hcd2 : ContDiffOn ℝ 2 (Function.uncurry (Pp2 α g σ)) Work.FTS.EllipticEst.Q0 :=
    ((contDiffOn_uncurry_fst hKgC2).mul (contDiffOn_al2f 2 (Work.FTS.Regularity.pExp α))).congr (fun p _ => rfl)
  have hcd3 : ContDiffOn ℝ 2 (Function.uncurry (Pp3 α Φs E g σ)) Work.FTS.EllipticEst.Q0 := by
    have hc : ContDiffOn ℝ 2 (Function.const (ℝ × ℝ) ((2 : ℝ) * Work.FTS.Regularity.pExp α))
        Work.FTS.EllipticEst.Q0 := contDiffOn_const
    have h1 : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => 2 * Work.FTS.Regularity.pExp α
        * Work.Construction.Vop (PtF α Φs E g σ) z θ)) Work.FTS.EllipticEst.Q0 :=
      (hc.mul hps.1).congr (fun p _ => rfl)
    exact (h1.mul (contDiffOn_A1f 2)).congr (fun p _ => by
      obtain ⟨z', θ'⟩ := p
      simp only [Function.uncurry, Pp3, PtF])
  have hcd4 : ContDiffOn ℝ 2 (Function.uncurry (Pp4 α Φs E g σ)) Work.FTS.EllipticEst.Q0 := by
    have hc : ContDiffOn ℝ 2 (Function.const (ℝ × ℝ) (2 : ℝ)) Work.FTS.EllipticEst.Q0 :=
      contDiffOn_const
    have h1 : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => 2 *
        (Work.Construction.Uop (Work.FTS.Regularity.pExp α) (PtF α Φs E g σ) z θ
          / Real.sin (2 * θ)))) Work.FTS.EllipticEst.Q0 :=
      (hc.mul hps.2.1).congr (fun p _ => rfl)
    exact (h1.mul (contDiffOn_B1f 2 (Work.FTS.Regularity.pExp α))).congr (fun p _ => by
      obtain ⟨z', θ'⟩ := p
      simp only [Function.uncurry, Pp4, PtF])
  have hcd5 : ContDiffOn ℝ 2 (Function.uncurry (Pp5 α Φs E g σ)) Work.FTS.EllipticEst.Q0 := by
    have hc : ContDiffOn ℝ 2 (Function.const (ℝ × ℝ) (-2 : ℝ)) Work.FTS.EllipticEst.Q0 :=
      contDiffOn_const
    have h1 : ContDiffOn ℝ 2 (Function.uncurry (fun z θ =>
        (-2 : ℝ) * Work.Construction.Rop (Work.FTS.Regularity.pExp α) (PtF α Φs E g σ) z θ))
        Work.FTS.EllipticEst.Q0 :=
      (hc.mul hps.2.2).congr (fun p _ => rfl)
    exact (h1.mul (contDiffOn_Fhf 2)).congr (fun p _ => by
      obtain ⟨z', θ'⟩ := p
      simp only [Function.uncurry, Pp5, PtF])
  have hcd01 : ContDiffOn ℝ 2 (Function.uncurry (Pp0 α Φs E g σ + Pp1 α g σ))
      Work.FTS.EllipticEst.Q0 := (hcd0.add hcd1).congr (fun p _ => rfl)
  have hcd012 : ContDiffOn ℝ 2 (Function.uncurry ((Pp0 α Φs E g σ + Pp1 α g σ) + Pp2 α g σ))
      Work.FTS.EllipticEst.Q0 := (hcd01.add hcd2).congr (fun p _ => rfl)
  have hcd0123 : ContDiffOn ℝ 2 (Function.uncurry
      (((Pp0 α Φs E g σ + Pp1 α g σ) + Pp2 α g σ) + Pp3 α Φs E g σ))
      Work.FTS.EllipticEst.Q0 := (hcd012.add hcd3).congr (fun p _ => rfl)
  have hcd01234 : ContDiffOn ℝ 2 (Function.uncurry
      ((((Pp0 α Φs E g σ + Pp1 α g σ) + Pp2 α g σ) + Pp3 α Φs E g σ) + Pp4 α Φs E g σ))
      Work.FTS.EllipticEst.Q0 := (hcd0123.add hcd4).congr (fun p _ => rfl)
  have hcdS : ContDiffOn ℝ 2 (Function.uncurry (SSF α Φs E g σ)) Work.FTS.EllipticEst.Q0 :=
    (hcd01234.add hcd5).congr (fun p _ => rfl)
  have hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ0, hθ1⟩
  have hEqS : Set.EqOn (Function.uncurry (fun z θ =>
      Work.FTS.RegExportIface.RXT.VR α Φs E g z θ σ * A1f z θ
        + Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
            * B1f (Work.FTS.Regularity.pExp α) z θ
        + Work.FTS.RegExportIface.RXT.cR α Φs E g z θ σ * Fhf z θ))
      (Function.uncurry (SSF α Φs E g σ)) Work.FTS.EllipticEst.Q0 := by
    intro p hp
    obtain ⟨z', θ'⟩ := p
    have hdec := forcing_decomp hα hα13 hS hOK hC2 hL12 hw hL12d σ hσ z' θ' hp.1 hp.2.1 hp.2.2
    simpa only [Function.uncurry, SSF, Pp0, Pp1, Pp2, Pp3, Pp4, Pp5,
      LgF, KgF, PtF] using hdec
  have hmix : Work.Spaces.mixed j i (SSF α Φs E g σ) z θ
      = Work.Spaces.mixed j i (Pp0 α Φs E g σ) z θ + Work.Spaces.mixed j i (Pp1 α g σ) z θ
        + Work.Spaces.mixed j i (Pp2 α g σ) z θ + Work.Spaces.mixed j i (Pp3 α Φs E g σ) z θ
        + Work.Spaces.mixed j i (Pp4 α Φs E g σ) z θ
        + Work.Spaces.mixed j i (Pp5 α Φs E g σ) z θ := by
    have e5 := Work.FTS.CoercivityFix.Transfer.E2pkg.mixed_add_of_contDiffOn
      (V := Work.FTS.EllipticEst.Q0) Work.FTS.EllipticEst.isOpen_Q0 hcd01234 hcd5 i j
      (by rw [Nat.add_comm i j]; exact hji) (z, θ) hzθ
    have e4 := Work.FTS.CoercivityFix.Transfer.E2pkg.mixed_add_of_contDiffOn
      (V := Work.FTS.EllipticEst.Q0) Work.FTS.EllipticEst.isOpen_Q0 hcd0123 hcd4 i j
      (by rw [Nat.add_comm i j]; exact hji) (z, θ) hzθ
    have e3 := Work.FTS.CoercivityFix.Transfer.E2pkg.mixed_add_of_contDiffOn
      (V := Work.FTS.EllipticEst.Q0) Work.FTS.EllipticEst.isOpen_Q0 hcd012 hcd3 i j
      (by rw [Nat.add_comm i j]; exact hji) (z, θ) hzθ
    have e2 := Work.FTS.CoercivityFix.Transfer.E2pkg.mixed_add_of_contDiffOn
      (V := Work.FTS.EllipticEst.Q0) Work.FTS.EllipticEst.isOpen_Q0 hcd01 hcd2 i j
      (by rw [Nat.add_comm i j]; exact hji) (z, θ) hzθ
    have e1 := Work.FTS.CoercivityFix.Transfer.E2pkg.mixed_add_of_contDiffOn
      (V := Work.FTS.EllipticEst.Q0) Work.FTS.EllipticEst.isOpen_Q0 hcd0 hcd1 i j
      (by rw [Nat.add_comm i j]; exact hji) (z, θ) hzθ
    show Work.Spaces.mixed j i (((((Pp0 α Φs E g σ + Pp1 α g σ) + Pp2 α g σ)
        + Pp3 α Φs E g σ) + Pp4 α Φs E g σ) + Pp5 α Φs E g σ) z θ = _
    rw [e5, e4, e3, e2, e1]
  have hstep : Ce * (1 + Cmu) * (z ^ 2 / (1 + z) ^ 2)
      + 4 * (Cl * (z ^ ((3:ℝ)/2) / (1 + z) ^ 2))
          * (Ce * (1 + 1 / Work.FTS.Regularity.pExp α) * (z / (1 + z) ^ 2))
      + 4 * (Cl * (z ^ ((3:ℝ)/2) / (1 + z) ^ 2))
          * (Ce * (1 + Work.FTS.Regularity.pExp α) * (z / (1 + z) ^ 2))
      + 4 * (2 * Work.FTS.Regularity.pExp α * max M2 0 * min z 1)
          * (Ce * (z / (1 + z) ^ 2))
      + 4 * (2 * max M2 0 * min z 1) * (Ce * Work.FTS.Regularity.pExp α * (z / (1 + z) ^ 2))
      + 4 * (2 * max M2 0 * min z 1) * (Ce * (z / (1 + z) ^ 2))
      ≤ (Ce * (1 + Cmu) + (4 * Cl * Ce * (1 + 1 / Work.FTS.Regularity.pExp α)
          + (4 * Cl * Ce * (1 + Work.FTS.Regularity.pExp α)
          + (8 * Work.FTS.Regularity.pExp α * max M2 0 * Ce
          + (8 * max M2 0 * Ce * Work.FTS.Regularity.pExp α + 8 * max M2 0 * Ce)))))
          * (z ^ 2 / (1 + z) ^ 2) := by
    have hb1 : Cl * (z ^ ((3:ℝ)/2) / (1 + z) ^ 2)
        * (Ce * (1 + 1 / Work.FTS.Regularity.pExp α) * (z / (1 + z) ^ 2))
        ≤ Cl * Ce * (1 + 1 / Work.FTS.Regularity.pExp α) * (z ^ 2 / (1 + z) ^ 2) := by
      have h := wt_mul_le hz
      have hC : 0 ≤ Cl * Ce * (1 + 1 / Work.FTS.Regularity.pExp α) := by positivity
      calc Cl * (z ^ ((3:ℝ)/2) / (1 + z) ^ 2)
            * (Ce * (1 + 1 / Work.FTS.Regularity.pExp α) * (z / (1 + z) ^ 2))
          = (Cl * Ce * (1 + 1 / Work.FTS.Regularity.pExp α))
            * ((z ^ ((3:ℝ)/2) / (1 + z) ^ 2) * (z / (1 + z) ^ 2)) := by ring
        _ ≤ (Cl * Ce * (1 + 1 / Work.FTS.Regularity.pExp α)) * (z ^ 2 / (1 + z) ^ 2) :=
            mul_le_mul_of_nonneg_left h hC
        _ = Cl * Ce * (1 + 1 / Work.FTS.Regularity.pExp α) * (z ^ 2 / (1 + z) ^ 2) := by ring
    have hb2 : Cl * (z ^ ((3:ℝ)/2) / (1 + z) ^ 2)
        * (Ce * (1 + Work.FTS.Regularity.pExp α) * (z / (1 + z) ^ 2))
        ≤ Cl * Ce * (1 + Work.FTS.Regularity.pExp α) * (z ^ 2 / (1 + z) ^ 2) := by
      have h := wt_mul_le hz
      have hC : 0 ≤ Cl * Ce * (1 + Work.FTS.Regularity.pExp α) := by positivity
      calc Cl * (z ^ ((3:ℝ)/2) / (1 + z) ^ 2)
            * (Ce * (1 + Work.FTS.Regularity.pExp α) * (z / (1 + z) ^ 2))
          = (Cl * Ce * (1 + Work.FTS.Regularity.pExp α))
            * ((z ^ ((3:ℝ)/2) / (1 + z) ^ 2) * (z / (1 + z) ^ 2)) := by ring
        _ ≤ (Cl * Ce * (1 + Work.FTS.Regularity.pExp α)) * (z ^ 2 / (1 + z) ^ 2) :=
            mul_le_mul_of_nonneg_left h hC
        _ = Cl * Ce * (1 + Work.FTS.Regularity.pExp α) * (z ^ 2 / (1 + z) ^ 2) := by ring
    have hb3 : 2 * Work.FTS.Regularity.pExp α * max M2 0 * min z 1 * (Ce * (z / (1 + z) ^ 2))
        ≤ 2 * Work.FTS.Regularity.pExp α * max M2 0 * Ce * (z ^ 2 / (1 + z) ^ 2) := by
      have h := min_mul_le hz
      have hC : 0 ≤ 2 * Work.FTS.Regularity.pExp α * max M2 0 * Ce := by positivity
      calc 2 * Work.FTS.Regularity.pExp α * max M2 0 * min z 1 * (Ce * (z / (1 + z) ^ 2))
          = (2 * Work.FTS.Regularity.pExp α * max M2 0 * Ce)
            * (min z 1 * (z / (1 + z) ^ 2)) := by ring
        _ ≤ (2 * Work.FTS.Regularity.pExp α * max M2 0 * Ce) * (z ^ 2 / (1 + z) ^ 2) :=
            mul_le_mul_of_nonneg_left h hC
        _ = 2 * Work.FTS.Regularity.pExp α * max M2 0 * Ce * (z ^ 2 / (1 + z) ^ 2) := by ring
    have hb4 : 2 * max M2 0 * min z 1 * (Ce * Work.FTS.Regularity.pExp α * (z / (1 + z) ^ 2))
        ≤ 2 * max M2 0 * Ce * Work.FTS.Regularity.pExp α * (z ^ 2 / (1 + z) ^ 2) := by
      have h := min_mul_le hz
      have hC : 0 ≤ 2 * max M2 0 * Ce * Work.FTS.Regularity.pExp α := by positivity
      calc 2 * max M2 0 * min z 1 * (Ce * Work.FTS.Regularity.pExp α * (z / (1 + z) ^ 2))
          = (2 * max M2 0 * Ce * Work.FTS.Regularity.pExp α)
            * (min z 1 * (z / (1 + z) ^ 2)) := by ring
        _ ≤ (2 * max M2 0 * Ce * Work.FTS.Regularity.pExp α) * (z ^ 2 / (1 + z) ^ 2) :=
            mul_le_mul_of_nonneg_left h hC
        _ = 2 * max M2 0 * Ce * Work.FTS.Regularity.pExp α * (z ^ 2 / (1 + z) ^ 2) := by ring
    have hb5 : 2 * max M2 0 * min z 1 * (Ce * (z / (1 + z) ^ 2))
        ≤ 2 * max M2 0 * Ce * (z ^ 2 / (1 + z) ^ 2) := by
      have h := min_mul_le hz
      have hC : 0 ≤ 2 * max M2 0 * Ce := by positivity
      calc 2 * max M2 0 * min z 1 * (Ce * (z / (1 + z) ^ 2))
          = (2 * max M2 0 * Ce) * (min z 1 * (z / (1 + z) ^ 2)) := by ring
        _ ≤ (2 * max M2 0 * Ce) * (z ^ 2 / (1 + z) ^ 2) := mul_le_mul_of_nonneg_left h hC
        _ = 2 * max M2 0 * Ce * (z ^ 2 / (1 + z) ^ 2) := by ring
    linarith [hb1, hb2, hb3, hb4, hb5]
  calc |Work.Spaces.mixed j i (fun z θ =>
        Work.FTS.RegExportIface.RXT.VR α Φs E g z θ σ * A1f z θ
          + Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
              * B1f (Work.FTS.Regularity.pExp α) z θ
          + Work.FTS.RegExportIface.RXT.cR α Φs E g z θ σ * Fhf z θ) z θ|
      = |Work.Spaces.mixed j i (SSF α Φs E g σ) z θ| := by
        rw [Work.FTS_RegExport.RXT.SysAux.mixed_congr_of_isOpen
          Work.FTS.EllipticEst.isOpen_Q0 hEqS j i z θ hzθ]
    _ = |Work.Spaces.mixed j i (Pp0 α Φs E g σ) z θ + Work.Spaces.mixed j i (Pp1 α g σ) z θ
          + Work.Spaces.mixed j i (Pp2 α g σ) z θ + Work.Spaces.mixed j i (Pp3 α Φs E g σ) z θ
          + Work.Spaces.mixed j i (Pp4 α Φs E g σ) z θ
          + Work.Spaces.mixed j i (Pp5 α Φs E g σ) z θ| := by rw [hmix]
    _ ≤ |Work.Spaces.mixed j i (Pp0 α Φs E g σ) z θ| + |Work.Spaces.mixed j i (Pp1 α g σ) z θ|
          + |Work.Spaces.mixed j i (Pp2 α g σ) z θ| + |Work.Spaces.mixed j i (Pp3 α Φs E g σ) z θ|
          + |Work.Spaces.mixed j i (Pp4 α Φs E g σ) z θ|
          + |Work.Spaces.mixed j i (Pp5 α Φs E g σ) z θ| := abs_add_six_le _ _ _ _ _ _
    _ ≤ Ce * (1 + Cmu) * (z ^ 2 / (1 + z) ^ 2)
          + 4 * (Cl * (z ^ ((3:ℝ)/2) / (1 + z) ^ 2))
              * (Ce * (1 + 1 / Work.FTS.Regularity.pExp α) * (z / (1 + z) ^ 2))
          + 4 * (Cl * (z ^ ((3:ℝ)/2) / (1 + z) ^ 2))
              * (Ce * (1 + Work.FTS.Regularity.pExp α) * (z / (1 + z) ^ 2))
          + 4 * (2 * Work.FTS.Regularity.pExp α * max M2 0 * min z 1)
              * (Ce * (z / (1 + z) ^ 2))
          + 4 * (2 * max M2 0 * min z 1)
              * (Ce * Work.FTS.Regularity.pExp α * (z / (1 + z) ^ 2))
          + 4 * (2 * max M2 0 * min z 1) * (Ce * (z / (1 + z) ^ 2)) := by
        linarith [b0, b1, b2, b3, b4, b5]
    _ ≤ (Ce * (1 + Cmu) + (4 * Cl * Ce * (1 + 1 / Work.FTS.Regularity.pExp α)
          + (4 * Cl * Ce * (1 + Work.FTS.Regularity.pExp α)
          + (8 * Work.FTS.Regularity.pExp α * max M2 0 * Ce
          + (8 * max M2 0 * Ce * Work.FTS.Regularity.pExp α + 8 * max M2 0 * Ce)))))
          * (z ^ 2 / (1 + z) ^ 2) := hstep

end Work.FTS_RegExport.RXT.Sys
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.explicit_pieces_coeff =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Sys

/-!
# `Work.FTS_RegExport.RXT.Sys.explicit_pieces_coeff`

The four explicit pieces of the forcing decomposition whose `mixed`-jets of order `≤ 2` are
bounded uniformly in `τ ∈ [0,S]` on the open quadrant:

* `L₁₂(F(τ))(z)·c2m θ` and `L₁₂(F(τ))(z)` (`F(τ) = Ftau (pExp α) (GR α g) τ`);
* `sin²θ·𝔽K(F(τ))(z)`;
* `Uop (pExp α) (Θ (pExp α) F(τ))(z,θ) / sin 2θ`, which on the open quadrant is the radial
  combination `-(3/(4β))·L₁₂(F(τ))(z) + (1/4)·𝔽K(F(τ))(z)` (`β = pExp α ≤ 1`).

The proof reduces everything to the iterated radial jets of `L₁₂(F(τ))` and `𝔽K(F(τ))`
(`L12_FK_jets_of_datum`, fed by the datum witness `Ftau_datum_of_LimApprox`), and to the
elementary angular jets of `c2m` and `sin²` computed below.

`C⁴`-smoothness of the slices of `g` (hence `C²` of `F(τ)`) is extracted from `LimApprox` by
`sliceC4_of_LimApprox` via the subsequence-extraction `slice_contDiffOn_four`.
-/

/-! ## §1 The `C⁴`-regularity of the slices of a `LimApprox` family -/

/-- **The `C⁴`-regularity of the slices**, extracted from `LimApprox` by the subsequence
extraction `slice_contDiffOn_four` (the limit of the locally uniformly convergent subsequence
is `slice g τ`, by uniqueness of limits, since the whole sequence converges pointwise to it). -/
theorem sliceC4_of_LimApprox {α C₀ T : ℝ} (hα : 0 < α) (hT : 0 < T)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hA : Work.FTS.FinalV2.LimApprox α C₀ Φs E g) :
    ∀ τ ∈ Set.Icc (0 : ℝ) T,
      ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice g τ))
        Work.FTS.EllipticEst.Q0 := by
  obtain ⟨gn, B, L, hC, -, hjet, -⟩ := hA T hT
  intro τ hτ
  refine Work.FTS_RegExport.RXT.Sys.slice_contDiffOn_four (B := B) hα
    (G := fun n => Work.FTS.Galerkin.slice (gn n) τ) (f := Work.FTS.Galerkin.slice g τ)
    ?_ ?_ ?_ ?_
  · intro n k
    exact (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp (hC n τ hτ).1.reg k
  · intro n
    exact Work.FTS.OpenPkg.HkMem_mono_open (hC n τ hτ).1.reg 6 (by norm_num) (hC n τ hτ).1.mem
  · intro n
    exact (hC n τ hτ).2.2
  · intro z θ hzθ
    exact hjet τ hτ 0 0 (by norm_num) z θ hzθ

/-! ## §2 Separable data: the product rule for `mixed` -/

/-- The `θ`-iterated operator commutes with multiplication by a `z`-only factor. -/
theorem DthIter_mul_left_z (i : ℕ) (c : ℝ → ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => c z * g z θ)
      = fun z θ => c z * Work.Spaces.DthIter i g z θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ, ih, Work.Spaces.DthIter_succ]
      funext z θ
      simp only [Work.Spaces.Dth, Work.Spaces.pth]
      rw [deriv_const_mul_field]
      ring

/-- The `z`-iterated operator commutes with multiplication by a `θ`-only factor. -/
theorem DzIter_mul_theta_factor (j : ℕ) (A : ℝ → ℝ) (B : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter j (fun z θ => A θ * B z θ)
      = fun z θ => A θ * Work.Spaces.DzIter j B z θ := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DzIter_succ, ih, Work.Spaces.DzIter_succ]
      funext z θ
      simp only [Work.Spaces.Dz, Work.Spaces.pz]
      rw [deriv_const_mul_field]
      ring

/-- **The `mixed`-jets of a separable datum `h(z)·G(θ)` split.** -/
theorem mixed_mul_rad_ang (h : ℝ → ℝ) (G : ℝ → ℝ) (j i : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed j i (fun z θ => h z * G θ) z θ
      = Work.Elliptic.DzdIter j h z * Work.Spaces.DthIter i (fun _ θ' => G θ') 0 θ := by
  rw [Work.Spaces.mixed, DthIter_mul_left_z i h (fun _ θ' => G θ')]
  rw [show (fun z θ => h z * Work.Spaces.DthIter i (fun _ θ' => G θ') z θ)
      = fun z θ => Work.Spaces.DthIter i (fun _ θ' => G θ') 0 θ * h z from by
    funext z θ
    rw [mul_comm, DthIter_z_indep G i z 0 θ]]
  rw [DzIter_mul_theta_factor j (fun θ => Work.Spaces.DthIter i (fun _ θ' => G θ') 0 θ)
    (fun z _ => h z)]
  simp only
  have hrad : Work.Spaces.DzIter j (fun z x => h z) z θ = Work.Elliptic.DzdIter j h z :=
    Work.Elliptic.DzIter_rad h j z θ
  rw [hrad, mul_comm]

/-- **The `mixed`-jets of a radial datum** vanish as soon as one `θ`-derivative is taken. -/
theorem mixed_radial (h : ℝ → ℝ) (j i : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed j i (fun z θ => h z) z θ
      = if i = 0 then Work.Elliptic.DzdIter j h z else 0 := by
  rcases i with _ | k
  · rw [Work.Spaces.mixed, Work.Spaces.DthIter_zero, if_pos rfl]
    exact Work.Elliptic.DzIter_rad h j z θ
  · rw [Work.Spaces.mixed, if_neg (by omega), Work.Elliptic.DthIter_rad_succ h k,
      DzIter_zero_fun]

/-! ## §3 The angular jets of `c2m` and `sin²` -/

theorem deriv_c2m (θ : ℝ) : deriv Work.Construction.c2m θ = -3 * Real.sin (2 * θ) := by
  have hcos : HasDerivAt (fun θ' : ℝ => Real.cos (2 * θ')) (-2 * Real.sin (2 * θ)) θ := by
    have h1 : HasDerivAt (fun θ' : ℝ => (2 : ℝ) * θ') (2 : ℝ) θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    refine (HasDerivAt.congr_of_eventuallyEq
      ((Real.hasDerivAt_cos (2 * θ)).comp θ h1)
      (Filter.Eventually.of_forall (fun x => rfl))).congr_deriv ?_
    ring
  have hsin : HasDerivAt (fun θ' : ℝ => Real.sin θ' ^ 2)
      (2 * Real.sin θ * Real.cos θ) θ := by
    have hp := (Real.hasDerivAt_sin θ).pow 2
    refine (HasDerivAt.congr_of_eventuallyEq hp
      (Filter.Eventually.of_forall (fun x => rfl))).congr_deriv ?_
    norm_num
  have hd : deriv ((fun θ' : ℝ => Real.cos (2 * θ')) - (fun θ' : ℝ => Real.sin θ' ^ 2)) θ
      = -2 * Real.sin (2 * θ) - 2 * Real.sin θ * Real.cos θ := (hcos.sub hsin).deriv
  change deriv (fun θ' : ℝ => Real.cos (2 * θ') - Real.sin θ' ^ 2) θ = -3 * Real.sin (2 * θ)
  rw [show deriv (fun θ' : ℝ => Real.cos (2 * θ') - Real.sin θ' ^ 2) θ
      = deriv ((fun θ' : ℝ => Real.cos (2 * θ')) - (fun θ' : ℝ => Real.sin θ' ^ 2)) θ
      from rfl, hd, Real.sin_two_mul]
  ring

theorem deriv_sinsq (θ : ℝ) :
    deriv (fun θ' : ℝ => Real.sin θ' ^ 2) θ = 2 * Real.sin θ * Real.cos θ := by
  have hp := (Real.hasDerivAt_sin θ).pow 2
  rw [(HasDerivAt.congr_of_eventuallyEq hp
    (Filter.Eventually.of_forall (fun x => rfl)) : HasDerivAt
      (fun θ' : ℝ => Real.sin θ' ^ 2) (2 * Real.sin θ ^ (2 - 1) * Real.cos θ) θ).deriv]
  norm_num

theorem deriv_sinsq_two (θ : ℝ) :
    deriv (fun θ' : ℝ => Real.sin (2 * θ') ^ 2) θ
      = 4 * Real.sin (2 * θ) * Real.cos (2 * θ) := by
  have h0 : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
    have h1 : HasDerivAt (fun θ' : ℝ => (2 : ℝ) * θ') (2 : ℝ) θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    refine (HasDerivAt.congr_of_eventuallyEq
      ((Real.hasDerivAt_sin (2 * θ)).comp θ h1)
      (Filter.Eventually.of_forall (fun x => rfl))).congr_deriv ?_
    ring
  rw [(HasDerivAt.congr_of_eventuallyEq (h0.pow 2)
    (Filter.Eventually.of_forall (fun x => rfl)) : HasDerivAt
      (fun θ' : ℝ => Real.sin (2 * θ') ^ 2)
      (2 * Real.sin (2 * θ) ^ (2 - 1) * (2 * Real.cos (2 * θ))) θ).deriv]
  norm_num
  ring

theorem DthIter_one_c2m (θ : ℝ) :
    Work.Spaces.DthIter 1 (fun _ θ' => Work.Construction.c2m θ') 0 θ
      = -3 * Real.sin (2 * θ) ^ 2 := by
  rw [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero]
  simp only [Work.Spaces.Dth, Work.Spaces.pth]
  rw [deriv_c2m]
  ring

theorem DthIter_two_c2m (θ : ℝ) :
    Work.Spaces.DthIter 2 (fun _ θ' => Work.Construction.c2m θ') 0 θ
      = -12 * Real.sin (2 * θ) ^ 2 * Real.cos (2 * θ) := by
  rw [Work.Spaces.DthIter_succ]
  simp only [Work.Spaces.Dth, Work.Spaces.pth]
  rw [show (fun θ' : ℝ => Work.Spaces.DthIter 1
        (fun _ θ' => Work.Construction.c2m θ') 0 θ') = fun θ' => -3 * Real.sin (2 * θ') ^ 2
      from funext DthIter_one_c2m]
  rw [deriv_const_mul_field, deriv_sinsq_two]
  ring

/-- `|D_θ^i c2m| ≤ 12` for `i ≤ 2`. -/
theorem DthIter_c2m_le (i : ℕ) (hi : i ≤ 2) (θ : ℝ) :
    |Work.Spaces.DthIter i (fun _ θ' => Work.Construction.c2m θ') 0 θ| ≤ 12 := by
  interval_cases i
  · show |Work.Construction.c2m θ| ≤ 12
    rw [Work.Construction.c2m]
    have h1 : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
    have h2 : |Real.sin θ ^ 2| ≤ 1 := by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact Real.sin_sq_le_one θ
    have h3 : |Real.cos (2 * θ) - Real.sin θ ^ 2| ≤ |Real.cos (2 * θ)| + |Real.sin θ ^ 2| :=
      abs_sub _ _
    linarith
  · rw [DthIter_one_c2m, abs_mul, abs_neg,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3), abs_of_nonneg (sq_nonneg _)]
    nlinarith [Real.sin_sq_le_one (2 * θ)]
  · rw [DthIter_two_c2m, abs_mul, abs_mul, abs_neg,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 12), abs_of_nonneg (sq_nonneg _)]
    have h3 : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
    nlinarith [Real.sin_sq_le_one (2 * θ)]

theorem DthIter_one_sinsq (θ : ℝ) :
    Work.Spaces.DthIter 1 (fun _ θ' => Real.sin θ' ^ 2) 0 θ = Real.sin (2 * θ) ^ 2 := by
  rw [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero]
  simp only [Work.Spaces.Dth, Work.Spaces.pth]
  rw [deriv_sinsq, Real.sin_two_mul]
  ring

theorem DthIter_two_sinsq (θ : ℝ) :
    Work.Spaces.DthIter 2 (fun _ θ' => Real.sin θ' ^ 2) 0 θ
      = 4 * Real.sin (2 * θ) ^ 2 * Real.cos (2 * θ) := by
  rw [Work.Spaces.DthIter_succ]
  simp only [Work.Spaces.Dth, Work.Spaces.pth]
  rw [show (fun θ' : ℝ => Work.Spaces.DthIter 1
        (fun _ θ' => Real.sin θ' ^ 2) 0 θ') = fun θ' => Real.sin (2 * θ') ^ 2
      from funext DthIter_one_sinsq]
  rw [deriv_sinsq_two]
  ring

/-- `|D_θ^i (sin²)| ≤ 4` for `i ≤ 2`. -/
theorem DthIter_sinsq_le (i : ℕ) (hi : i ≤ 2) (θ : ℝ) :
    |Work.Spaces.DthIter i (fun _ θ' => Real.sin θ' ^ 2) 0 θ| ≤ 4 := by
  interval_cases i
  · show |Real.sin θ ^ 2| ≤ 4
    rw [abs_of_nonneg (sq_nonneg _)]
    linarith [Real.sin_sq_le_one θ]
  · rw [DthIter_one_sinsq, abs_of_nonneg (sq_nonneg _)]
    linarith [Real.sin_sq_le_one (2 * θ)]
  · rw [DthIter_two_sinsq, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4), abs_of_nonneg (sq_nonneg _)]
    have h3 : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
    nlinarith [Real.sin_sq_le_one (2 * θ)]

/-! ## §4 The closed form of `Uop (Θ F)/sin 2θ` on the open quadrant -/

/-- On the open quadrant, `Uop α (Θ α F) / sin 2θ = -(3/(4α))·L₁₂(F) + (1/4)·𝔽K(F)`, given the
index-raising identity `∂_z L₁₂(F) = -𝔽K(F)/z`. -/
theorem Uop_Theta_div {β : ℝ} (hβ : 0 < β) {F : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hder : HasDerivAt (fun z' => Work.Construction.L12 F z')
      (-(Work.Construction.FK F z) / z) z) :
    Work.Construction.Uop β (Work.Construction.Theta β F) z θ / Real.sin (2 * θ)
      = -(3 / (4 * β)) * Work.Construction.L12 F z
        + (1 / 4) * Work.Construction.FK F z := by
  have hs : Real.sin (2 * θ) ≠ 0 := by
    refine ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ?_ ?_) <;> linarith
  have hT : Work.Construction.Theta β F z θ
      = ((1 / (4 * β)) * Real.sin (2 * θ)) * Work.Construction.L12 F z := by
    rw [Work.Construction.Theta, Work.Construction.s2_eq]
  have hDt : deriv (fun z' : ℝ => Work.Construction.Theta β F z' θ) z
      = ((1 / (4 * β)) * Real.sin (2 * θ)) * (-(Work.Construction.FK F z) / z) := by
    rw [show (fun z' : ℝ => Work.Construction.Theta β F z' θ)
        = fun z' => ((1 / (4 * β)) * Real.sin (2 * θ)) * Work.Construction.L12 F z' from by
      funext z'; rw [Work.Construction.Theta, Work.Construction.s2_eq]]
    rw [deriv_const_mul_field, hder.deriv]
  rw [Work.Construction.Uop]
  simp only [Work.Spaces.pz]
  rw [hT, hDt]
  have hb : β ≠ 0 := ne_of_gt hβ
  have hz' : z ≠ 0 := ne_of_gt hz
  field_simp
  ring

/-! ## §5 The target -/

theorem explicit_pieces_coeff {α C₀ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hA : Work.FTS.FinalV2.LimApprox (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (S : ℝ) (hS : 0 < S) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ j i : ℕ, j + i ≤ 2 →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (fun z θ => Work.Construction.L12
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) τ) z * Work.Construction.c2m θ) z θ| ≤ C ∧
      |Work.Spaces.mixed j i (fun z θ => Work.Construction.L12
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) τ) z) z θ| ≤ C ∧
      |Work.Spaces.mixed j i (fun z θ => (Real.sin θ) ^ 2 * Work.Construction.FK
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) τ) z) z θ| ≤ C ∧
      |Work.Spaces.mixed j i (fun z θ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
          (Work.Construction.Theta (Work.FTS.Regularity.pExp α)
            (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) τ)) z θ
          / Real.sin (2 * θ)) z θ| ≤ C := by
  have hβ : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hc4 := sliceC4_of_LimApprox (α := Work.FTS.Regularity.pExp α) (C₀ := C₀) (T := S)
    hβ hS hA
  have hc2 : ∀ τ ∈ Set.Icc (0 : ℝ) S,
      ContDiffOn ℝ 2 (Function.uncurry (Work.FTS.Galerkin.slice g τ))
        Work.FTS.EllipticEst.Q0 :=
    fun τ hτ => (hc4 τ hτ).of_le (by norm_num)
  obtain ⟨Cd, hCd1, hCd⟩ := Ftau_datum_of_LimApprox hα hα13 hA S hS hc2
  obtain ⟨K, hK0, hK⟩ := L12_FK_jets_of_datum
  have hM0 : 0 ≤ K * Cd ^ 4 := mul_nonneg hK0.le (by positivity)
  have hQ0 : 0 ≤ 3 / (4 * Work.FTS.Regularity.pExp α) + 1 / 4 := by positivity
  have hQM : 0 ≤ (3 / (4 * Work.FTS.Regularity.pExp α) + 1 / 4) * (K * Cd ^ 4) :=
    mul_nonneg hQ0 hM0
  set Cbig : ℝ := 12 * (K * Cd ^ 4) + (3 / (4 * Work.FTS.Regularity.pExp α) + 1 / 4)
    * (K * Cd ^ 4) + 1 with hCbig
  have hCpos : 0 < Cbig := by rw [hCbig]; linarith
  have hb12 : 12 * (K * Cd ^ 4) ≤ Cbig := by rw [hCbig]; linarith
  have hb1 : K * Cd ^ 4 ≤ Cbig := by rw [hCbig]; linarith
  have hb4 : 4 * (K * Cd ^ 4) ≤ Cbig := by rw [hCbig]; linarith
  have hbQ : (3 / (4 * Work.FTS.Regularity.pExp α) + 1 / 4) * (K * Cd ^ 4) ≤ Cbig := by
    rw [hCbig]; linarith
  refine ⟨Cbig, hCpos, ?_⟩
  intro τ hτ j i hji z θ hz hθ0 hθ1
  have hj2 : j ≤ 2 := by omega
  have hi2 : i ≤ 2 := by omega
  have hzmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ0, hθ1⟩
  have hKg := hK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
    (Work.FTS.RegExportIface.RXT.GR α g) τ) Cd hCd1 (hCd τ hτ)
  have hLb := (hKg z hz).1 j hj2 |>.1
  have hFb := (hKg z hz).1 j hj2 |>.2.1
  have hCb := (hKg z hz).1 j hj2 |>.2.2 (-(3 / (4 * Work.FTS.Regularity.pExp α))) (1 / 4)
  have hzle : (0 : ℝ) ≤ Cbig := le_of_lt hCpos
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mixed_mul_rad_ang (fun z => Work.Construction.L12 (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) z)
      Work.Construction.c2m j i z θ, abs_mul]
    have h2 := DthIter_c2m_le i hi2 θ
    have hmm := mul_le_mul hLb h2 (abs_nonneg _) hM0
    linarith
  · rw [mixed_radial (fun z => Work.Construction.L12 (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) z) j i z θ]
    split_ifs with hi0
    · linarith
    · simp only [abs_zero]
      exact hzle
  · have hf : (fun z θ : ℝ => (Real.sin θ) ^ 2 * Work.Construction.FK
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ) z)
        = fun z θ => Work.Construction.FK (Work.Construction.Ftau
            (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) τ) z * (Real.sin θ) ^ 2 := by
      funext z' θ'; ring
    rw [hf, mixed_mul_rad_ang (fun z => Work.Construction.FK (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) z)
      (fun θ => (Real.sin θ) ^ 2) j i z θ, abs_mul]
    have h2 := DthIter_sinsq_le i hi2 θ
    have hmm := mul_le_mul hFb h2 (abs_nonneg _) hM0
    linarith
  · have hEq : Set.EqOn (Function.uncurry (fun z θ => Work.Construction.Uop
          (Work.FTS.Regularity.pExp α) (Work.Construction.Theta (Work.FTS.Regularity.pExp α)
            (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) τ)) z θ / Real.sin (2 * θ)))
        (Function.uncurry (fun z θ => -(3 / (4 * Work.FTS.Regularity.pExp α))
            * Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) τ) z
          + (1 / 4) * Work.Construction.FK (Work.Construction.Ftau
              (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) z))
        Work.FTS.EllipticEst.Q0 := by
      intro p hp
      simp only [Function.uncurry]
      exact Uop_Theta_div hβ hp.1 hp.2.1 hp.2.2 ((hKg p.1 hp.1).2.2.1)
    rw [mixed_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEq j i z θ hzmem,
      mixed_radial (fun z => -(3 / (4 * Work.FTS.Regularity.pExp α))
        * Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ) z
        + (1 / 4) * Work.Construction.FK (Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) z) j i z θ]
    split_ifs with hi0
    · have habs : |-(3 / (4 * Work.FTS.Regularity.pExp α))|
          = 3 / (4 * Work.FTS.Regularity.pExp α) := by
        rw [abs_neg, abs_of_pos (by positivity : 0 < 3 / (4 * Work.FTS.Regularity.pExp α))]
      have habs2 : |(1 / 4 : ℝ)| = 1 / 4 := abs_of_nonneg (by norm_num)
      rw [habs, habs2] at hCb
      linarith
    · simp only [abs_zero]
      exact hzle

end Work.FTS_RegExport.RXT.Sys
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT0.RXJets.CJShared =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT0.RXJets.CJShared` — the common facts about `CJHyps`

The `(z,θ)`-regularity of the star residual, the perturbation residual, `L₁₂(F_τ)`, `𝔽K(F_τ)`,
the split identity `Φ̃_τ = Φ̃_* + Ξ_τ` on the open quadrant, the clock `μR`, `hL12` in the
`DzdIter` shape, and the three star-slot jet continuities.  Everything is a theorem about the
hypothesis bundle `CJHyps`, so the three coefficient modules and the statement file share it.
-/

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT0.RXJets

set_option autoImplicit false

open Work.FTS_RegExport.RXT (v2_PhiT v2_PhiStar v2_PhiPert v2_phiTil_split)

variable {α C₀ Ce Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
  {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}

/-- The star residual is `C³` on the open quadrant. -/
theorem CJHyps.hStar3 (H : CJHyps α C₀ Ce Cs Φs E g) :
    ContDiffOn ℝ 3 (Function.uncurry (v2_PhiStar α Φs)) Work.FTS.EllipticEst.Q0 := by
  have hαG : (0 : ℝ) < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos H.hα
  have hαG1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one H.hα13
  exact (Work.FTS.PhiStar.CoreAux.fields_smooth hαG hαG1 H.hStar.smooth).1.of_le
    (by simp [Work.Stability.smoothOrder])

theorem CJHyps.hStar1 (H : CJHyps α C₀ Ce Cs Φs E g) :
    ContDiffOn ℝ 1 (Function.uncurry (v2_PhiStar α Φs)) Work.FTS.EllipticEst.Q0 :=
  H.hStar3.of_le (by norm_num)

/-- The perturbation residual is `C³` on the open quadrant at every `τ ≥ 0`. -/
theorem CJHyps.hPert3 (H : CJHyps α C₀ Ce Cs Φs E g) :
    ∀ τ : ℝ, 0 ≤ τ → ContDiffOn ℝ 3 (Function.uncurry (v2_PhiPert α E g τ))
      Work.FTS.EllipticEst.Q0 := by
  intro τ hτ
  exact (Work.FTS_RegExport.RXT.Sys.pert_tilde_contDiffOn H.hα H.hα13 H.hEL3 H.hOK τ hτ).congr
    (fun q _ => rfl)

theorem CJHyps.hPert1g (H : CJHyps α C₀ Ce Cs Φs E g) :
    ∀ τ : ℝ, 0 ≤ τ → ContDiffOn ℝ 1 (Function.uncurry (v2_PhiPert α E g τ))
      Work.FTS.EllipticEst.Q0 :=
  fun τ hτ => (H.hPert3 τ hτ).of_le (by norm_num)

/-- `Φ̃_τ = Φ̃_* + Ξ_τ` on the open quadrant. -/
theorem CJHyps.hagQ (H : CJHyps α C₀ Ce Cs Φs E g) :
    ∀ τ : ℝ, 0 ≤ τ → Work.FTS_RegExport.RXR5.AgreeOnQ (v2_PhiT α Φs E g τ)
      (v2_PhiStar α Φs + v2_PhiPert α E g τ) := fun τ hτ z θ hz hθ hθ2 => by
  simp only [Pi.add_apply]
  exact v2_phiTil_split (C₀ := C₀) H.hα H.hα13 H.hOK hτ z θ ⟨hz, hθ, hθ2⟩

/-- `slice (ΦR) τ = Φ̃_τ + Θ(F_τ)` as functions. -/
theorem CJHyps.hSliceFun (H : CJHyps α C₀ Ce Cs Φs E g) (τ : ℝ) :
    Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ
      = fun z θ => v2_PhiT α Φs E g τ z θ + Work.Construction.Theta (Work.FTS.Regularity.pExp α)
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) τ) z θ := by
  funext z θ
  simp only [Work.FTS.Galerkin.slice, v2_PhiT, Work.Construction.PhiTil]
  ring

/-- `Φ̃_τ` and `Θ(F_τ)` are `C³` on the open quadrant, uniformly on `[0,S]`. -/
theorem CJHyps.hResC3 (H : CJHyps α C₀ Ce Cs Φs E g) (S : ℝ) :
    ∀ τ ∈ Set.Icc (0:ℝ) S,
      ContDiffOn ℝ 3 (Function.uncurry (v2_PhiT α Φs E g τ)) Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 3 (Function.uncurry (Work.Construction.Theta (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ))) Work.FTS.EllipticEst.Q0 := by
  intro τ hτ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h12, h13⟩ :=
    Work.FTS_RegExport.RXT.Sys.coeff_pieces_contDiffOn (τ := τ) H.hα H.hα13 H.hEL3 H.hStar
      H.hOK hτ.1
  exact ⟨h12, h13⟩

/-- `L₁₂(F_τ)` and `𝔽K(F_τ)` are `C²` on `(0,∞)`. -/
theorem CJHyps.hRegR (H : CJHyps α C₀ Ce Cs Φs E g) (S : ℝ) :
    ∀ τ ∈ Set.Icc (0:ℝ) S,
      ContDiffOn ℝ 2 (Work.Construction.L12 (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ)) (Set.Ioi 0) ∧
      ContDiffOn ℝ 2 (Work.Construction.FK (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ)) (Set.Ioi 0) := by
  intro τ hτ
  have hF2 := Work.FTS_RegExport.RXT.contDiffOn_Ftau_Q0 (C₀ := C₀) H.hα H.hα13 H.hOK τ hτ.1
  obtain ⟨Cf, hCf0, hbd⟩ := Work.FTS_RegExport.RXT.Ftau_bounds (C₀ := C₀) H.hα H.hα13 H.hOK τ hτ.1
  have hFK2 : ContDiffOn ℝ 2 (Work.Construction.FK (Work.Construction.Ftau
      (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ)) (Set.Ioi 0) :=
    Work.FTS_RegExport.RXT.contDiffOn_two_integral_Itheta (φ := Work.Spaces.K)
      Work.FTS_RegExport.RXT.Sys.sys_continuousOn_K_Iθ hF2
      (fun z θ hz hθ hθ2 => ⟨(hbd z θ hz hθ hθ2).1, (hbd z θ hz hθ hθ2).2.1,
        (hbd z θ hz hθ hθ2).2.2⟩)
  exact ⟨(Work.FTS_RegExport.RXT.contDiffOn_three_L12 hFK2).of_le (by norm_num), hFK2⟩

/-- `z ∂_z L₁₂(F_τ) = -𝔽K(F_τ)`. -/
theorem CJHyps.hderL12 (H : CJHyps α C₀ Ce Cs Φs E g) (S : ℝ) :
    ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z : ℝ, 0 < z →
      HasDerivAt (fun z' => Work.Construction.L12 (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) z')
        (-(Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ) z) / z) z := by
  obtain ⟨CF, hCF0, -, -, hL12der, -, -⟩ :=
    Work.FTS_RegExport.RXT.Sys.L12FK_family_jets (C₀ := C₀) (Φs := Φs) (E := E) (g := g)
      H.hα H.hα13 H.hOK.2 (max S 1) (lt_max_of_lt_right zero_lt_one)
  intro τ hτ z hz
  have hτ' : τ ∈ Set.Icc (0:ℝ) (max S 1) := ⟨hτ.1, le_trans hτ.2 (le_max_left S 1)⟩
  have h0 := hL12der τ hτ' z hz
  have h2 : Work.Spaces.DzIter 1 (fun z _ => Work.Construction.L12 (Work.Construction.Ftau
      (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) z) z 0
      = z * deriv (fun z'' => Work.Construction.L12 (Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) z'') z := by
    rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]; rfl
  rw [h2] at h0
  have hd : deriv (fun z' => Work.Construction.L12 (Work.Construction.Ftau
      (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) z') z
      = -(Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ) z) / z := by
    rw [eq_div_iff (ne_of_gt hz)]
    rw [mul_comm]
    exact h0
  have hdiff : DifferentiableAt ℝ (fun z' => Work.Construction.L12 (Work.Construction.Ftau
      (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) z') z :=
    ((H.hRegR S τ hτ).1.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz)
  rw [← hd]
  exact hdiff.hasDerivAt

/-- `hL12` in the `DzdIter` shape. -/
theorem CJHyps.hdzd (H : CJHyps α C₀ Ce Cs Φs E g) (S : ℝ) (hS : 0 < S) :
    ∀ j : ℕ, j ≤ 2 →
      ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.DzdIter j
        (fun z => Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) p.2) z) p.1)
        (Set.Ioi (0:ℝ) ×ˢ Set.Icc (0:ℝ) S) ∧
      ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.DzdIter j
        (fun z => Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) p.2) z) p.1)
        (Set.Ioi (0:ℝ) ×ˢ Set.Icc (0:ℝ) S) := by
  intro j hj
  obtain ⟨h1, h2⟩ := H.hL12 S hS j hj
  exact ⟨h1.congr (fun p hp => (Work.Elliptic.DzIter_rad _ j p.1 0).symm),
         h2.congr (fun p hp => (Work.Elliptic.DzIter_rad _ j p.1 0).symm)⟩

/-- The clock `μR` is continuous on `[0,S]`. -/
theorem CJHyps.hμRc (H : CJHyps α C₀ Ce Cs Φs E g) (S : ℝ) :
    ContinuousOn (fun τ : ℝ => Work.FTS.RegExportIface.RXT.μR α Φs E g τ) (Set.Icc (0:ℝ) S) := by
  have hμRc' : ContinuousOn (fun τ : ℝ => Work.FTS.RegExportIface.RXT.μR α Φs E g τ)
      (Set.Ici 0) := by
    refine H.hμ.2.congr (fun τ hτ => ?_)
    show Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
        (Work.FTS.Nonlin.PsiCan Φs E g) g (max τ 0)
      = Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
        (Work.FTS.Nonlin.PsiCan Φs E g) g τ
    rw [max_eq_left (show (0 : ℝ) ≤ τ from hτ)]
  exact hμRc'.mono (fun τ hτ => hτ.1)

/-- The three star-slot jet continuities. -/
theorem CJHyps.hStarSlots (H : CJHyps α C₀ Ce Cs Φs E g) (S : ℝ) (k l : ℕ) (hkl : k + l ≤ 2) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
        (fun z θ => Work.Construction.Vop (v2_PhiStar α Φs) z θ) p.1 p.2.1) (slb S) ∧
      ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
        (fun z θ => Work.Construction.Rop (Work.FTS.Regularity.pExp α)
          (v2_PhiStar α Φs) z θ) p.1 p.2.1) (slb S) ∧
      ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
        (fun z θ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
          (v2_PhiStar α Φs) z θ / Real.sin (2 * θ)) p.1 p.2.1) (slb S) :=
  Work.FTS_RegExport.RXT0.RXJets.starSlots H.hα H.hα13 H.hStar S k l hkl

end Work.FTS_RegExport.RXT0.RXJets
end
end
