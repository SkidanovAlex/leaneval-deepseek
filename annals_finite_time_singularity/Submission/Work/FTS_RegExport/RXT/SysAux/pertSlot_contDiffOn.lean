import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS_RegExport.RXT.CoeffJetsDefs
import Submission.Work.FTS_RegExport.RXT.C2Radial
import Submission.Work.FTS_RegExport.RXT.SysAux.Theta_ops
import Submission.Work.FTS_RegExport.RXT.SysAux.L12_FK_Ftau_split
import Submission.Work.FTS_RegExport.RXT.SysAux.SigR_eq_reduced

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.SysAux

open scoped Real Topology
open Set Filter

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.RegExportIface (phiTil Vz7 Vθ7 cs7)
open Work.FTS.RegExportIface.RXT (VR bR cR μR ΦR GR)
open Work.Construction (Vop Uop Rop Theta Ftau PhiTil L12 FK c2m)

set_option linter.unusedVariables false

/-! ## `ContDiffOn`-calculus helpers on the open quadrant -/

/-- A radial function of `z` alone is `C^n` on the open quadrant. -/
private theorem contDiffOn_slice_fst_Q0 {n : WithTop ℕ∞} {a : ℝ → ℝ}
    (ha : ContDiffOn ℝ n a (Set.Ioi 0)) :
    ContDiffOn ℝ n (fun p : ℝ × ℝ => a p.1) Work.FTS.EllipticEst.Q0 :=
  ha.comp contDiffOn_fst (fun p hp => hp.1)

/-- `θ ↦ c2m θ = cos 2θ − sin²θ` is `C²` on the open quadrant. -/
private theorem contDiffOn_c2m_Q0 :
    ContDiffOn ℝ 2 (fun p : ℝ × ℝ => c2m p.2) Work.FTS.EllipticEst.Q0 := by
  have h1 : ContDiffOn ℝ 2 (fun θ : ℝ => Real.cos (2 * θ)) (Set.Ioo 0 (π / 2)) :=
    (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)).contDiffOn
  have h2 : ContDiffOn ℝ 2 (fun θ : ℝ => Real.sin θ ^ 2) (Set.Ioo 0 (π / 2)) :=
    (Real.contDiff_sin.contDiffOn).pow 2
  have hc : ContDiffOn ℝ 2 c2m (Set.Ioo 0 (π / 2)) :=
    (h1.sub h2).congr (fun θ _ => by simp only [c2m])
  exact hc.comp contDiffOn_snd (fun p hp => hp.2)

/-- `θ ↦ sin²θ` is `C²` on the open quadrant. -/
private theorem contDiffOn_sinsq_Q0 :
    ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.sin p.2 ^ 2) Work.FTS.EllipticEst.Q0 :=
  ((Real.contDiff_sin.contDiffOn).pow 2).comp contDiffOn_snd (fun p hp => hp.2)

/-! ## The pointwise identities expressing the perturbation slots through the coefficients -/

/-- Solved for `𝒱(Φ̃)`: `Vz7 = (1−μ) + L₁₂(F)·c2m + 2α·𝒱(Φ̃)`. -/
private lemma Vop_phiTil_eq {αG : ℝ} (hne : αG ≠ 0) {μ : ℝ → ℝ} {G Φ : Fam} {τ z θ : ℝ} :
    Vop (phiTil αG G Φ τ) z θ
      = (Vz7 αG μ G Φ z θ τ - (1 - μ τ) - L12 (Ftau αG G τ) z * c2m θ) / (2 * αG) := by
  rw [eq_div_iff (mul_ne_zero two_ne_zero hne)]
  simp only [Vz7]
  ring

/-- Solved for `ℛ(Φ̃)`: `cs7 = (1+μ) − L₁₂(F)/α + sin²θ·𝔽K(F) − 2ℛ(Φ̃)`. -/
private lemma Rop_phiTil_eq {αG : ℝ} {μ : ℝ → ℝ} {G Φ : Fam} {τ z θ : ℝ} :
    Rop αG (phiTil αG G Φ τ) z θ
      = ((1 + μ τ) - L12 (Ftau αG G τ) z / αG + Real.sin θ ^ 2 * FK (Ftau αG G τ) z
          - cs7 αG μ G Φ z θ τ) / 2 := by
  rw [eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)]
  simp only [cs7]
  ring

/-- Solved for `𝒰(Φ̃)/sin 2θ`: the two `Θ`-pieces of `bR` collapse, by `Theta_ops`, to the
closed form `−(3/(2α))·L₁₂(F) + (1/2)·𝔽K(F)`. -/
private lemma Uop_phiTil_div_sin_eq {α αG : ℝ} (hαG : 0 < αG) {Φs : Fn}
    {E : Fn →ₗ[ℝ] Fn} {g : Fam} {μ : ℝ → ℝ} {G Φ : Fam} {τ : ℝ}
    (hb : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      bR α Φs E g z θ τ
        = 2 * (Uop αG (phiTil αG G Φ τ) z θ / Real.sin (2 * θ))
          + 2 * (Uop αG (Theta αG (Ftau αG G τ)) z θ / Real.sin (2 * θ)))
    (hL12d : ∀ z : ℝ, 0 < z →
      z * deriv (fun z' => L12 (Ftau αG G τ) z') z = -FK (Ftau αG G τ) z) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Uop αG (phiTil αG G Φ τ) z θ / Real.sin (2 * θ)
        = (bR α Φs E g z θ τ
            - (-(3 / (2 * αG)) * L12 (Ftau αG G τ) z
                + (1 / 2) * FK (Ftau αG G τ) z)) / 2 := by
  intro z θ hz hθ hθ2
  have hs : Real.sin (2 * θ) ≠ 0 :=
    ne_of_gt (Work.FTS_RegExport.RXT.sin_two_pos_Q0 ⟨hz, hθ, hθ2⟩)
  have ht := (Theta_ops hαG hL12d z θ hz hθ hθ2).2.1
  have ht' : 2 * Uop αG (Theta αG (Ftau αG G τ)) z θ
      = Real.sin (2 * θ) * (-(3 / (2 * αG)) * L12 (Ftau αG G τ) z
          + (1 / 2) * FK (Ftau αG G τ) z) := by
    rw [ht]; ring
  have hΘ : 2 * (Uop αG (Theta αG (Ftau αG G τ)) z θ / Real.sin (2 * θ))
      = -(3 / (2 * αG)) * L12 (Ftau αG G τ) z + (1 / 2) * FK (Ftau αG G τ) z := by
    rw [show 2 * (Uop αG (Theta αG (Ftau αG G τ)) z θ / Real.sin (2 * θ))
        = (2 * Uop αG (Theta αG (Ftau αG G τ)) z θ) / Real.sin (2 * θ) from by ring]
    rw [ht', div_eq_iff hs]
    ring
  rw [hb z θ hz hθ hθ2, hΘ]
  ring

theorem pertSlot_contDiffOn {α C₀ S : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hS : 0 < S)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hC2 : ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.VR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.bR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.cR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0)
    (hbr : ∀ σ ∈ Set.Icc (0:ℝ) S, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
        = 2 * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ)
              z θ / Real.sin (2 * θ))
          + 2 * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
              (Work.Construction.Theta (Work.FTS.Regularity.pExp α)
                (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                  (Work.FTS.RegExportIface.RXT.GR α g) σ)) z θ / Real.sin (2 * θ)))
    (hFK : ∀ σ ∈ Set.Icc (0:ℝ) S, ContDiffOn ℝ 2 (fun z => Work.Construction.FK
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) σ) z) (Set.Ioi 0))
    (hderL12 : ∀ σ ∈ Set.Icc (0:ℝ) S, ∀ z : ℝ, 0 < z →
      HasDerivAt (fun z' => Work.Construction.L12
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) σ) z')
        (-(Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) σ) z) / z) z) :
    ∀ σ ∈ Set.Icc (0:ℝ) S,
      ContDiffOn ℝ 2 (Function.uncurry (Work.Construction.Vop
        (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ)))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.Construction.Uop
        (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ) z θ
        / Real.sin (2 * θ))) Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (Work.Construction.Rop (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ)))
        Work.FTS.EllipticEst.Q0 := by
  intro σ hσ
  have hσ0 : 0 ≤ σ := hσ.1
  have hαG : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαGne : Work.FTS.Regularity.pExp α ≠ 0 := ne_of_gt hαG
  obtain ⟨hVRc, hbRc, hcRc⟩ := hC2 σ hσ0
  have hVR' : ContDiffOn ℝ 2 (fun p : ℝ × ℝ =>
      Vz7 (Work.FTS.Regularity.pExp α) (μR α Φs E g) (GR α g) (ΦR α Φs E g) p.1 p.2 σ)
      Work.FTS.EllipticEst.Q0 := hVRc
  have hbR' : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => bR α Φs E g p.1 p.2 σ)
      Work.FTS.EllipticEst.Q0 := hbRc
  have hcR' : ContDiffOn ℝ 2 (fun p : ℝ × ℝ =>
      cs7 (Work.FTS.Regularity.pExp α) (μR α Φs E g) (GR α g) (ΦR α Φs E g) p.1 p.2 σ)
      Work.FTS.EllipticEst.Q0 := hcRc
  -- the two radial profiles `𝔽K(F(σ))` and `L₁₂(F(σ))`
  have hFK2 : ContDiffOn ℝ 2
      (FK (Ftau (Work.FTS.Regularity.pExp α) (GR α g) σ)) (Set.Ioi 0) := hFK σ hσ
  have hL12_3 : ContDiffOn ℝ 3
      (L12 (Ftau (Work.FTS.Regularity.pExp α) (GR α g) σ)) (Set.Ioi 0) :=
    Work.FTS_RegExport.RXT.contDiffOn_three_L12 hFK2
  have hL12_2 : ContDiffOn ℝ 2
      (L12 (Ftau (Work.FTS.Regularity.pExp α) (GR α g) σ)) (Set.Ioi 0) :=
    hL12_3.of_le (by norm_num)
  have hL12slice : ContDiffOn ℝ 2 (fun p : ℝ × ℝ =>
      L12 (Ftau (Work.FTS.Regularity.pExp α) (GR α g) σ) p.1)
      Work.FTS.EllipticEst.Q0 := contDiffOn_slice_fst_Q0 hL12_2
  have hFKslice : ContDiffOn ℝ 2 (fun p : ℝ × ℝ =>
      FK (Ftau (Work.FTS.Regularity.pExp α) (GR α g) σ) p.1)
      Work.FTS.EllipticEst.Q0 := contDiffOn_slice_fst_Q0 hFK2
  -- the index-raising identity `z ∂_z L₁₂(F) = −𝔽K(F)` of `Theta_ops`
  have hL12d : ∀ z : ℝ, 0 < z →
      z * deriv (fun z' => L12 (Ftau (Work.FTS.Regularity.pExp α) (GR α g) σ) z') z
        = -FK (Ftau (Work.FTS.Regularity.pExp α) (GR α g) σ) z := by
    intro z hz
    rw [(hderL12 σ hσ z hz).deriv]
    have hz0 : z ≠ 0 := ne_of_gt hz
    field_simp
  refine ⟨?_, ?_, ?_⟩
  · -- the `𝒱`-slot
    refine (((hVR'.sub (contDiffOn_const (c := 1 - μR α Φs E g σ))).sub
      (hL12slice.mul contDiffOn_c2m_Q0)).div_const
        (2 * Work.FTS.Regularity.pExp α)).congr (fun p hp => ?_)
    simpa only [Function.uncurry] using
      Vop_phiTil_eq (αG := Work.FTS.Regularity.pExp α) (μ := μR α Φs E g)
        (G := GR α g) (Φ := ΦR α Φs E g) (τ := σ) (z := p.1) (θ := p.2) hαGne
  · -- the `𝒰/sin 2θ`-slot
    have hB : ContDiffOn ℝ 2 (fun p : ℝ × ℝ =>
        -(3 / (2 * Work.FTS.Regularity.pExp α))
            * L12 (Ftau (Work.FTS.Regularity.pExp α) (GR α g) σ) p.1
          + (1 / 2) * FK (Ftau (Work.FTS.Regularity.pExp α) (GR α g) σ) p.1)
        Work.FTS.EllipticEst.Q0 :=
      ((contDiffOn_const (c := -(3 / (2 * Work.FTS.Regularity.pExp α)))).mul hL12slice).add
        ((contDiffOn_const (c := ((1 : ℝ) / 2))).mul hFKslice)
    have hA : ContDiffOn ℝ 2 (fun p : ℝ × ℝ =>
        (bR α Φs E g p.1 p.2 σ
          - (-(3 / (2 * Work.FTS.Regularity.pExp α))
                * L12 (Ftau (Work.FTS.Regularity.pExp α) (GR α g) σ) p.1
              + (1 / 2) * FK (Ftau (Work.FTS.Regularity.pExp α) (GR α g) σ) p.1)) / 2)
        Work.FTS.EllipticEst.Q0 :=
      (hbR'.sub hB).div_const 2
    exact hA.congr (fun p hp => by
      simpa only [Function.uncurry] using
        Uop_phiTil_div_sin_eq (α := α) (αG := Work.FTS.Regularity.pExp α)
          (Φs := Φs) (E := E) (g := g) (μ := μR α Φs E g)
          (G := GR α g) (Φ := ΦR α Φs E g) (τ := σ) hαG (hbr σ hσ) hL12d
          p.1 p.2 hp.1 hp.2.1 hp.2.2)
  · -- the `ℛ`-slot
    refine (((((contDiffOn_const (c := 1 + μR α Φs E g σ)).sub
      (hL12slice.div_const (Work.FTS.Regularity.pExp α))).add
        (contDiffOn_sinsq_Q0.mul hFKslice)).sub hcR').div_const 2).congr (fun p hp => ?_)
    simpa only [Function.uncurry] using
      Rop_phiTil_eq (αG := Work.FTS.Regularity.pExp α) (μ := μR α Φs E g)
        (G := GR α g) (Φ := ΦR α Φs E g) (τ := σ) (z := p.1) (θ := p.2)

end Work.FTS_RegExport.RXT.SysAux
