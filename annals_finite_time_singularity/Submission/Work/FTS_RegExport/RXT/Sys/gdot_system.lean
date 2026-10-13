import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS_RegExport.RXT.CoeffJetsDefs
import Submission.Work.FTS_RegExport.RXT.Sys.GdotCore
import Submission.Work.FTS_RegExport.RXT.Sys.GdotBound
import Submission.Work.FTS_RegExport.RXT.Sys.GdotAux.Fstar_Q0_c4

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.gdot_system` — S5b of the RX-St1 leaf plan

The differentiated equation, pointwise, for the six components `(j,i) = idx k`: Leibniz for
`D_z`, `D_θ` applied to the `(E)`-form of the equation, with `D_θ` commuted past `D_z^j`, the
principal parts collected as `Vz·w_{β+z} + b̂·w_{β+θ}`, every commutator bounded by the order-`≤2`
coefficient jets and the `F_*`-forcing `Σ` kept on the left.

The statement is the leaf-plan statement S5b (`RegExportIface/RXT/Leaves.lean`) with the package
hypothesis `VelPkg` replaced by `Work.FTS_RegExport.RXT.CoeffJets` (open `θ`).  The proof factors
as

* `gdot_eq_rhs_pt'` below, or `GdotAux.gdot_eq_rhs_pt` — the pointwise `(E)`-form of the equation
  for `gdot g σ` (the value clause of `hEqF`, transferred from `extG (GR α g)` to `g`);
* `GdotExp.mixed_transport_expand` — the Leibniz expansion of `D_z^j D_θ^i` on the transport
  expression `a·D_zX + d·D_θX + c·X`, in the shifted form in which the principal parts are
  `a·w_{β+z}`, `d·w_{β+θ}`;
* `GdotBound.sys_bound` — the commutator bound: the difference between that expansion and its
  principal part is controlled by the order-`≤2` coefficient jets times the six order-`≤2` jets;
* the assembly inside `gdot_system` below: `hVP.dbnd` supplies the coefficient jets, `hC2` and
  `RegPkgMin.c4` the smoothness, and `hEqF` the pointwise equation.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT.Sys

open Work.FTS.Galerkin (Fn Fam slice gdot)
open Work.FTS.RegExportIface (Vz7 Vθ7 cs7 ω phiTil)
open Work.FTS.RegExportIface.RXT (VR bR cR SigR μR GR ΦR idx)
open Work.FTS.RegPkgGal (extG)
open Work.FTS.Regularity (pExp)
open Work.FTS.FinalV2 (gS tauExt LimApprox DynOK' EllLimOK3 Sol)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

variable {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}

/-- **The pointwise `(E)`-form of the fake-time equation for `gdot`**: the value clause of `hEqF`,
transferred from the extension `extG (GR α g)` (which agrees with `g` on the open quadrant at
times `τ ≥ 0`) to `g` itself. -/
theorem gdot_eq_rhs_pt' {S α C₀ : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}
    (hS : 0 < S) (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : DynOK' (pExp α) C₀ Φs E g)
    (hEqF : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S →
      HasDerivAt (fun s => Work.FTS.Regularity.profFull α (extG (GR α g)) z θ s)
        (-(VR α Φs E g z θ τ
            * Work.Spaces.Dz (fun z θ => Work.FTS.Regularity.profFull α (extG (GR α g)) z θ τ) z θ
          + Vθ7 (pExp α) (ΦR α Φs E g) z θ τ
            * Work.Spaces.pth (fun z θ => Work.FTS.Regularity.profFull α (extG (GR α g)) z θ τ) z θ
          + cR α Φs E g z θ τ
            * Work.FTS.Regularity.profFull α (extG (GR α g)) z θ τ)) τ) :
    ∀ z θ σ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < σ → σ ≤ S →
      gdot g σ z θ
        = -(VR α Φs E g z θ σ
              * Work.Spaces.Dz (fun z θ => Work.FTS.Regularity.profFull α (extG (GR α g)) z θ σ) z θ
            + Vθ7 (pExp α) (ΦR α Φs E g) z θ σ
              * Work.Spaces.pth (fun z θ => Work.FTS.Regularity.profFull α (extG (GR α g)) z θ σ) z θ
            + cR α Φs E g z θ σ
              * Work.FTS.Regularity.profFull α (extG (GR α g)) z θ σ) := by
  intro z θ σ hz hθ0 hθ1 hσ hσS
  have hnb : ∀ᶠ s in 𝓝 σ, (0 : ℝ) < s :=
    isOpen_Ioi.mem_nhds (show σ ∈ Set.Ioi (0 : ℝ) from hσ)
  have h1 : (fun s => g z θ s) =ᶠ[𝓝 σ] (fun s => extG (GR α g) z θ s) := by
    filter_upwards [hnb] with s hs
    rw [Work.FTS.RegPkgGal.extG_of_pos hz (le_of_lt hs),
      GR_of_quad (le_of_lt hs) hz (le_of_lt hθ0) (le_of_lt hθ1)]
  have h2 : deriv (fun s => extG (GR α g) z θ s) σ
      = deriv (fun s => Work.FTS.Regularity.profFull α (extG (GR α g)) z θ s) σ := by
    rw [show (fun s => Work.FTS.Regularity.profFull α (extG (GR α g)) z θ s)
        = (fun s => Work.Construction.Fstar (pExp α) z θ + extG (GR α g) z θ s) from rfl]
    rw [deriv_const_add]
  calc gdot g σ z θ = deriv (fun s => g z θ s) σ := rfl
    _ = deriv (fun s => extG (GR α g) z θ s) σ := h1.deriv_eq
    _ = deriv (fun s => Work.FTS.Regularity.profFull α (extG (GR α g)) z θ s) σ := h2
    _ = -(VR α Φs E g z θ σ
            * Work.Spaces.Dz (fun z θ => Work.FTS.Regularity.profFull α (extG (GR α g)) z θ σ) z θ
          + Vθ7 (pExp α) (ΦR α Φs E g) z θ σ
            * Work.Spaces.pth (fun z θ => Work.FTS.Regularity.profFull α (extG (GR α g)) z θ σ) z θ
          + cR α Φs E g z θ σ
            * Work.FTS.Regularity.profFull α (extG (GR α g)) z θ σ) :=
        (hEqF z θ σ hz hθ0 hθ1 hσ hσS).deriv

theorem gdot_system {S α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hS : 0 < S) (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hVP : Work.FTS_RegExport.RXT.CoeffJets (Work.FTS.Regularity.pExp α)
      (Work.FTS.RegExportIface.RXT.μR α Φs E g) (Work.FTS.RegExportIface.RXT.GR α g)
      (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) S)
    (hC2 : ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.VR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.bR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.cR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0)
    (hEqF : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S →
      HasDerivAt (fun s => Work.FTS.Regularity.profFull α
          (Work.FTS.RegPkgGal.extG (Work.FTS.RegExportIface.RXT.GR α g)) z θ s)
        (-(Work.FTS.RegExportIface.RXT.VR α Φs E g z θ τ
            * Work.Spaces.Dz (fun z θ => Work.FTS.Regularity.profFull α
                (Work.FTS.RegPkgGal.extG (Work.FTS.RegExportIface.RXT.GR α g)) z θ τ) z θ
          + Work.FTS.RegExportIface.Vθ7 (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) z θ τ
            * Work.Spaces.pth (fun z θ => Work.FTS.Regularity.profFull α
                (Work.FTS.RegPkgGal.extG (Work.FTS.RegExportIface.RXT.GR α g)) z θ τ) z θ
          + Work.FTS.RegExportIface.RXT.cR α Φs E g z θ τ
            * Work.FTS.Regularity.profFull α
                (Work.FTS.RegPkgGal.extG (Work.FTS.RegExportIface.RXT.GR α g)) z θ τ)) τ) :
    ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ k : Fin 6, ∀ z θ σ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < σ → σ ≤ S →
      |Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
          (Work.FTS.RegExportIface.RXT.idx k).2 (Work.FTS.Galerkin.gdot g σ) z θ
        + (Work.FTS.RegExportIface.RXT.VR α Φs E g z θ σ * Work.Spaces.mixed
            ((Work.FTS.RegExportIface.RXT.idx k).1 + 1)
            (Work.FTS.RegExportIface.RXT.idx k).2 (Work.FTS.Galerkin.slice g σ) z θ
          + Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ * Work.Spaces.mixed
            (Work.FTS.RegExportIface.RXT.idx k).1
            ((Work.FTS.RegExportIface.RXT.idx k).2 + 1) (Work.FTS.Galerkin.slice g σ) z θ)
        + Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
            (Work.FTS.RegExportIface.RXT.idx k).2
            (Work.FTS.RegExportIface.RXT.SigR α Φs E g σ) z θ|
        ≤ Cc * ∑ j : Fin 6, |Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx j).1
            (Work.FTS.RegExportIface.RXT.idx j).2 (Work.FTS.Galerkin.slice g σ) z θ| := by
  obtain ⟨M, hMdbnd⟩ := hVP.dbnd
  refine ⟨200 * (|M| + 1), by positivity, ?_⟩
  intro k z θ σ hz hθ0 hθ1 hσ hσS
  have hσ0 : 0 ≤ σ := le_of_lt hσ
  have hji : (idx k).1 + (idx k).2 ≤ 2 := by fin_cases k <;> decide
  have hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩
  set a : ℝ → ℝ → ℝ := fun z' θ' => VR α Φs E g z' θ' σ with ha
  set d : ℝ → ℝ → ℝ := fun z' θ' => bR α Φs E g z' θ' σ with hd
  set c : ℝ → ℝ → ℝ := fun z' θ' => cR α Φs E g z' θ' σ with hc
  set X : ℝ → ℝ → ℝ :=
    fun z' θ' => Work.FTS.Regularity.profFull α (extG (GR α g)) z' θ' σ with hX
  set P : ℝ → ℝ → ℝ := Work.Construction.Fstar (pExp α) with hP
  set Gc : ℝ → ℝ → ℝ := slice g σ with hGc
  -- smoothness
  have ha2 : ContDiffOn ℝ 2 (Function.uncurry a) Work.FTS.EllipticEst.Q0 := (hC2 σ hσ0).1
  have hd2 : ContDiffOn ℝ 2 (Function.uncurry d) Work.FTS.EllipticEst.Q0 := (hC2 σ hσ0).2.1
  have hc2 : ContDiffOn ℝ 2 (Function.uncurry c) Work.FTS.EllipticEst.Q0 := (hC2 σ hσ0).2.2
  have hP4 : ContDiffOn ℝ 4 (Function.uncurry P) Work.FTS.EllipticEst.Q0 := by
    rw [hP]
    exact GdotAux.Fstar_Q0_c4 (Work.FTS.Regularity.pExp_pos hα)
      (Work.FTS.Regularity.pExp_le_one hα13)
  have hP3 : ContDiffOn ℝ 3 (Function.uncurry P) Work.FTS.EllipticEst.Q0 :=
    hP4.of_le (by norm_num)
  have hG4 : ContDiffOn ℝ 4 (Function.uncurry Gc) Work.FTS.EllipticEst.Q0 := by
    rw [hGc]
    exact hOK.1.1.c4 σ hσ0
  have hG3 : ContDiffOn ℝ 3 (Function.uncurry Gc) Work.FTS.EllipticEst.Q0 :=
    hG4.of_le (by norm_num)
  -- the pointwise splitting `X = P + G`
  have hXPG : ∀ z' θ', 0 < z' → 0 < θ' → θ' < Real.pi / 2 → X z' θ' = P z' θ' + Gc z' θ' := by
    intro z' θ' hz' hθ'0 hθ'1
    simp only [hX, hP, hGc, Work.FTS.Regularity.profFull_apply]
    rw [Work.FTS.RegPkgGal.extG_of_pos hz' hσ0,
      GR_of_quad hσ0 hz' (le_of_lt hθ'0) (le_of_lt hθ'1)]
    rfl
  -- the coefficient jet bounds
  have hM : ∀ z' θ', 0 < z' → 0 < θ' → θ' < Real.pi / 2 → ∀ p q : ℕ, p + q ≤ 2 →
      |Work.Spaces.mixed p q a z' θ'| ≤ M ∧ |Work.Spaces.mixed p q d z' θ'| ≤ M ∧
        |Work.Spaces.mixed p q c z' θ'| ≤ M := by
    intro z' θ' hz' hθ'0 hθ'1 p q hpq
    have h0 := hMdbnd σ ⟨hσ0, hσS⟩ p q hpq z' θ' hz' hθ'0 hθ'1
    exact ⟨by simpa only [ha] using h0.1, by simpa only [hd] using h0.2.1,
      by simpa only [hc] using h0.2.2.1⟩
  -- the pointwise `(E)`-form for `gdot`
  have hpt1 : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      gdot g σ z' θ'
        = -(a z' θ' * Work.Spaces.Dz X z' θ' + d z' θ' * Work.Spaces.Dth X z' θ'
            + c z' θ' * X z' θ') := by
    intro z' θ' hz' hθ'0 hθ'1
    have hs : Real.sin (2 * θ') ≠ 0 := by
      apply ne_of_gt
      apply Real.sin_pos_of_pos_of_lt_pi
      · linarith
      · linarith [Real.pi_pos]
    have hkey : a z' θ' * Work.Spaces.Dz X z' θ' + d z' θ' * Work.Spaces.Dth X z' θ'
        + c z' θ' * X z' θ'
        = VR α Φs E g z' θ' σ * Work.Spaces.Dz X z' θ'
          + Vθ7 (pExp α) (ΦR α Φs E g) z' θ' σ * Work.Spaces.pth X z' θ'
          + cR α Φs E g z' θ' σ * X z' θ' := by
      simp only [ha, hc, hd, Work.Spaces.Dth, bR]
      field_simp
    rw [show Work.FTS.Galerkin.gdot g σ z' θ'
        = -(VR α Φs E g z' θ' σ
              * Work.Spaces.Dz (fun z θ => Work.FTS.Regularity.profFull α
                  (extG (GR α g)) z θ σ) z' θ'
            + Vθ7 (pExp α) (ΦR α Φs E g) z' θ' σ
              * Work.Spaces.pth (fun z θ => Work.FTS.Regularity.profFull α
                  (extG (GR α g)) z θ σ) z' θ'
            + cR α Φs E g z' θ' σ
              * Work.FTS.Regularity.profFull α (extG (GR α g)) z' θ' σ) from
        gdot_eq_rhs_pt' hS hα hα13 hOK hEqF z' θ' σ hz' hθ'0 hθ'1 hσ hσS]
    rw [hkey]
  -- the pointwise form of the forcing `Σ`
  have hpt2 : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      SigR α Φs E g σ z' θ'
        = a z' θ' * Work.Spaces.Dz P z' θ' + d z' θ' * Work.Spaces.Dth P z' θ'
            + c z' θ' * P z' θ' := by
    intro z' θ' hz' hθ'0 hθ'1
    have hs : Real.sin (2 * θ') ≠ 0 := by
      apply ne_of_gt
      apply Real.sin_pos_of_pos_of_lt_pi
      · linarith
      · linarith [Real.pi_pos]
    simp only [SigR, ha, hc, hd, hP, Work.Spaces.Dth, bR]
    field_simp
  -- transfer the two pointwise identities to the jets
  have hE1 : Work.Spaces.mixed (idx k).1 (idx k).2 (Work.FTS.Galerkin.gdot g σ) z θ
      = Work.Spaces.mixed (idx k).1 (idx k).2
          (fun z' θ' => -(a z' θ' * Work.Spaces.Dz X z' θ'
            + d z' θ' * Work.Spaces.Dth X z' θ' + c z' θ' * X z' θ')) z θ :=
    mixed_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0
      (f := fun z' θ' => Work.FTS.Galerkin.gdot g σ z' θ')
      (f' := fun z' θ' => -(a z' θ' * Work.Spaces.Dz X z' θ'
        + d z' θ' * Work.Spaces.Dth X z' θ' + c z' θ' * X z' θ'))
      (fun p hp => hpt1 p.1 p.2 hp.1 hp.2.1 hp.2.2) (idx k).1 (idx k).2 z θ hzθ
  have hE2 : Work.Spaces.mixed (idx k).1 (idx k).2 (SigR α Φs E g σ) z θ
      = Work.Spaces.mixed (idx k).1 (idx k).2
          (fun z' θ' => a z' θ' * Work.Spaces.Dz P z' θ'
            + d z' θ' * Work.Spaces.Dth P z' θ' + c z' θ' * P z' θ') z θ :=
    mixed_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0
      (f := fun z' θ' => SigR α Φs E g σ z' θ')
      (f' := fun z' θ' => a z' θ' * Work.Spaces.Dz P z' θ'
        + d z' θ' * Work.Spaces.Dth P z' θ' + c z' θ' * P z' θ')
      (fun p hp => hpt2 p.1 p.2 hp.1 hp.2.1 hp.2.2) (idx k).1 (idx k).2 z θ hzθ
  have hbound := sys_bound ha2 hd2 hc2 hP3 hG3 hXPG hM hji hz hθ0 hθ1
  rw [hE1, hE2]
  exact hbound

end Work.FTS_RegExport.RXT.Sys
