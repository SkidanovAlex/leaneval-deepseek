import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_RegExport.RXT.SysAux.FK_jet_pkg_uniform
import Submission.Work.FTS_RegExport.RXT.SysAux.L12_jet_pkg_uniform
import Submission.Work.FTS_RegExport.RXT.C2Radial
import Submission.Work.FTS_RegExport.RXT.SysAux.L12_FK_Ftau_split
import Submission.Work.FTS_RegExport.RXT.Sys.JetCalc.RHSSmooth
import Submission.Work.FTS_RegExport.RXR5.Basic
import Submission.Work.FTS.RegExportIface.RXT.Leaves

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.SysAux

open scoped Real Topology

set_option maxHeartbeats 1600000

theorem LgKg_Ftau_facts {α C₀ S : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hS : 0 < S)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hL12 : ∀ τ : ℝ, 0 ≤ τ →
      Work.Construction.L12 (Work.FTS.Galerkin.slice g τ) 0 = 0)
    (hw : ∃ C : ℝ, ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ →
      θ < Real.pi / 2 → |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ) z θ|
        ≤ C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (0:ℝ) S,
      ContDiffOn ℝ 2 (fun z => Work.Construction.FK (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) σ) z) (Set.Ioi 0) ∧
      ContDiffOn ℝ 3 (fun z => Work.Construction.L12 (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) σ) z) (Set.Ioi 0) ∧
      (∀ j : ℕ, j ≤ 2 → ∀ z : ℝ, 0 < z →
        |Work.Spaces.DzIter j (fun z (_ : ℝ) => Work.Construction.FK (Work.FTS.Galerkin.slice
          (Work.FTS.RegExportIface.RXT.GR α g) σ) z) z 0|
          ≤ C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)) ∧
      (∀ j : ℕ, j ≤ 2 → ∀ z : ℝ, 0 < z →
        |Work.Spaces.DzIter j (fun z (_ : ℝ) => Work.Construction.L12 (Work.FTS.Galerkin.slice
          (Work.FTS.RegExportIface.RXT.GR α g) σ) z) z 0|
          ≤ C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)) ∧
      ContDiffOn ℝ 2 (fun z => Work.Construction.FK (Work.FTS.Galerkin.slice
        (Work.FTS.RegExportIface.RXT.GR α g) σ) z) (Set.Ioi 0) ∧
      ContDiffOn ℝ 3 (fun z => Work.Construction.L12 (Work.FTS.Galerkin.slice
        (Work.FTS.RegExportIface.RXT.GR α g) σ) z) (Set.Ioi 0) ∧
      (∀ z : ℝ, 0 < z → HasDerivAt (fun z' => Work.Construction.L12 (Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) σ) z')
        (-(Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) σ) z) / z) z) ∧
      (∀ z : ℝ, 0 < z → z * deriv (fun z' => Work.Construction.L12 (Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) σ) z') z
        = -(Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) σ) z)) := by
  -- the two uniform datum packages, at the common constant `B` of the hypothesis `hw`
  obtain ⟨B, hB⟩ := hw
  obtain ⟨CFK, hCFKpos, hFKpkg⟩ := FK_jet_pkg_uniform B
  obtain ⟨CL12, hCL12pos, hL12pkg⟩ := L12_jet_pkg_uniform B
  refine ⟨max CFK CL12, lt_of_lt_of_le hCFKpos (le_max_left _ _), fun σ hσ => ?_⟩
  have hσ0 : 0 ≤ σ := hσ.1
  -- the sanitiser `GR α g` agrees with `g` on the open quadrant, so every jet bound transfers
  have hagree : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) σ z θ
        = Work.FTS.Galerkin.slice g σ z θ := by
    intro z θ hz hθ hθ2
    have h1 := Work.FTS_RegExport.RXR5.SG_slice_agreeOnQ α g σ z θ hz hθ hθ2
    rw [Work.FTS.FinalV2.slice_tauExt g hσ0] at h1
    exact h1
  have hEqOn : Set.EqOn (Function.uncurry (Work.FTS.Galerkin.slice
        (Work.FTS.RegExportIface.RXT.GR α g) σ))
      (Function.uncurry (Work.FTS.Galerkin.slice g σ)) Work.FTS.EllipticEst.Q0 :=
    fun p hp => hagree p.1 p.2 hp.1 hp.2.1 hp.2.2
  have hmixedEq : ∀ b a : ℕ, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed b a (Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) σ) z θ
        = Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g σ) z θ := by
    intro b a z θ hz hθ hθ2
    have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ, hθ2⟩
    have h1 := Work.FTS.H2.DthIter_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEqOn a
    have h2 := Work.FTS.H2.DzIter_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 h1 b
    simpa only [Function.uncurry, Work.Spaces.mixed] using h2 hmem
  have hCd : ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice
      (Work.FTS.RegExportIface.RXT.GR α g) σ)) Work.FTS.EllipticEst.Q0 :=
    (hOK.1.1.c4 σ hσ0).congr (fun p hp => hagree p.1 p.2 hp.1 hp.2.1 hp.2.2)
  have hb : ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice
        (Work.FTS.RegExportIface.RXT.GR α g) σ) z θ|
        ≤ B * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by
    intro b a hba z θ hz hθ hθ2
    rw [hmixedEq b a z θ hz hθ hθ2]
    exact hB σ hσ b a hba z θ hz hθ hθ2
  have h0 : Work.Construction.L12 (Work.FTS.Galerkin.slice
      (Work.FTS.RegExportIface.RXT.GR α g) σ) 0 = 0 := by
    rw [Work.FTS_RegExport.RXR5.L12_congr_of_agreeOnQ hagree (le_refl (0:ℝ))]
    exact hL12 σ hσ0
  obtain ⟨hFKjets, hFKpt, hFKc2, hgint, hgcont⟩ := hFKpkg _ hCd hb
  obtain ⟨hL12jets, hL12c3, hL12deriv⟩ := hL12pkg _ hCd hb h0
  -- the `F_* + slice`-split of both transforms at the profile `F(σ)`
  have hsplit : ∀ z : ℝ, 0 < z →
      (Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) σ) z
        = 2 * Work.FTS.Regularity.pExp α / (1 + z)
          + Work.Construction.L12 (Work.FTS.Galerkin.slice
              (Work.FTS.RegExportIface.RXT.GR α g) σ) z) ∧
      (Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) σ) z
        = Work.FTS.Regularity.pExp α * (2 * z / (1 + z) ^ 2)
          + Work.Construction.FK (Work.FTS.Galerkin.slice
              (Work.FTS.RegExportIface.RXT.GR α g) σ) z) :=
    fun z hz => L12_FK_Ftau_split hα hα13 hS hOK ⟨B, hB⟩ σ hσ z hz
  have hFKFtau : ContDiffOn ℝ 2 (fun z => Work.Construction.FK (Work.Construction.Ftau
      (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) σ) z) (Set.Ioi 0) := by
    have h1 : ContDiffOn ℝ 2 (fun z : ℝ => Work.FTS.Regularity.pExp α
        * (2 * z / (1 + z) ^ 2)) (Set.Ioi 0) := by
      have hnum : ContDiffOn ℝ 2 (fun z : ℝ => 2 * z) (Set.Ioi 0) :=
        contDiffOn_const.mul contDiffOn_id
      have hden : ContDiffOn ℝ 2 (fun z : ℝ => (1 + z) ^ 2) (Set.Ioi 0) :=
        (contDiffOn_const.add contDiffOn_id).pow 2
      exact contDiffOn_const.mul (hnum.div hden (fun z hz => by
        have hz' : (0:ℝ) < z := hz; positivity))
    exact (h1.add hFKc2).congr (fun z hz => (hsplit z hz).2)
  have hL12Ftau : ContDiffOn ℝ 3 (fun z => Work.Construction.L12 (Work.Construction.Ftau
      (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) σ) z) (Set.Ioi 0) := by
    have h1 : ContDiffOn ℝ 3 (fun z : ℝ => 2 * Work.FTS.Regularity.pExp α / (1 + z))
        (Set.Ioi 0) := by
      have hden : ContDiffOn ℝ 3 (fun z : ℝ => 1 + z) (Set.Ioi 0) :=
        contDiffOn_const.add contDiffOn_id
      exact contDiffOn_const.div hden (fun z hz => by
        have hz' : (0:ℝ) < z := hz; positivity)
    exact (h1.add hL12c3).congr (fun z hz => (hsplit z hz).1)
  have hderivFtau : ∀ z : ℝ, 0 < z → HasDerivAt (fun z' => Work.Construction.L12
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g)
        σ) z')
      (-(Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) σ) z) / z) z := by
    intro z hz
    have h1 : HasDerivAt (fun z' : ℝ => 2 * Work.FTS.Regularity.pExp α / (1 + z'))
        (-(2 * Work.FTS.Regularity.pExp α) / (1 + z) ^ 2) z := by
      have hden : HasDerivAt (fun z' : ℝ => 1 + z') 1 z := (hasDerivAt_id z).const_add 1
      have h := (hasDerivAt_const (x := z) (c := 2 * Work.FTS.Regularity.pExp α)).div hden
        (by positivity)
      have hv : (0 * (1 + z) - (2 * Work.FTS.Regularity.pExp α) * 1) / (1 + z) ^ 2
          = -(2 * Work.FTS.Regularity.pExp α) / (1 + z) ^ 2 := by ring
      rwa [hv] at h
    have hsum : HasDerivAt (fun w : ℝ => 2 * Work.FTS.Regularity.pExp α / (1 + w)
        + Work.Construction.L12 (Work.FTS.Galerkin.slice
            (Work.FTS.RegExportIface.RXT.GR α g) σ) w)
        (-(2 * Work.FTS.Regularity.pExp α) / (1 + z) ^ 2
          + (-(Work.Construction.FK (Work.FTS.Galerkin.slice
              (Work.FTS.RegExportIface.RXT.GR α g) σ) z) / z)) z :=
      h1.add (hL12deriv z hz)
    have hval : -(2 * Work.FTS.Regularity.pExp α) / (1 + z) ^ 2
          + (-(Work.Construction.FK (Work.FTS.Galerkin.slice
              (Work.FTS.RegExportIface.RXT.GR α g) σ) z) / z)
        = -(Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) σ) z) / z := by
      rw [(hsplit z hz).2]
      field_simp
      ring
    rw [hval] at hsum
    exact hsum.congr_of_eventuallyEq (by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
      exact (hsplit w hw).1)
  refine ⟨hFKFtau, hL12Ftau, ?_, ?_, hFKc2, hL12c3, hderivFtau, ?_⟩
  · intro j hj z hz
    have hnn : 0 ≤ z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2 := by positivity
    calc |Work.Spaces.DzIter j (fun z (_ : ℝ) => Work.Construction.FK (Work.FTS.Galerkin.slice
          (Work.FTS.RegExportIface.RXT.GR α g) σ) z) z 0|
        ≤ CFK * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := hFKjets j hj z hz
      _ ≤ max CFK CL12 * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hnn
  · intro j hj z hz
    have hnn : 0 ≤ z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2 := by positivity
    calc |Work.Spaces.DzIter j (fun z (_ : ℝ) => Work.Construction.L12 (Work.FTS.Galerkin.slice
          (Work.FTS.RegExportIface.RXT.GR α g) σ) z) z 0|
        ≤ CL12 * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := hL12jets j hj z hz
      _ ≤ max CFK CL12 * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hnn
  · intro z hz
    rw [(hderivFtau z hz).deriv]
    field_simp

end Work.FTS_RegExport.RXT.SysAux
