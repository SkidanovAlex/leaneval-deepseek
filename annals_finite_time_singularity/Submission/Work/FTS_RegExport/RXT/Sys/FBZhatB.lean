import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_RegExport.RXT.Sys.FBZhatP

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
