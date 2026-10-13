import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_RegExport.RXT.Sys.FBDefs
import Submission.Work.FTS_RegExport.RXT.SysAux.bR_decomp
import Submission.Work.FTS_RegExport.RXT.SysAux.L12_FK_Ftau_split
import Submission.Work.FTS_RegExport.RXT.SysAux.Theta_ops
import Submission.Work.FTS_RegExport.RXT.SysAux.SigR_eq_reduced

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.FBDecomp` — the algebraic decomposition of `Ẑ`

With `β = pExp α`, `μ = μR α Φs E g`, `Φ̃ = phiTil β (GR α g) (ΦR α Φs E g) σ`,
`F = Ftau β (GR α g) σ` and `Lg = L₁₂(F) - 2β/(1+z)`, `Kg = 𝔽K(F) - β·2z/(1+z)²`, the three
coefficients

  `VR = (1-μ) + L₁₂(F)·c2m + 2β·Vop Φ̃`,
  `bR = 2·Uop Φ / sin 2θ`,
  `cR = (1+μ) - L₁₂(F)/β + sin²θ·𝔽K(F) - 2·Rop Φ̃`

expand, using the `F_* + g̃`-split of `L₁₂`/`𝔽K` (`SysAux.L12_FK_Ftau_split`), the additivity of
`Uop` over `Φ = Φ̃ + Θ(F)` (`SysAux.bR_decomp`) and the closed form of `2·Uop(Θ(F))`
(`SysAux.Theta_ops`), into

  `VR·A1 + bR·B1 + cR·F̂ = E + Lg·α₁ + Kg·α₂ + (2β·Vop Φ̃)·A1 + (2·Uop Φ̃/sin 2θ)·B1 - (2·Rop Φ̃)·F̂`

with `E`, `α₁`, `α₂`, `A1`, `B1`, `F̂` the explicit pieces of `Sys.FBDefs`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport.RXT.Sys

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-- The algebraic decomposition of `Ẑ` (`= VR·A1 + bR·B1 + cR·F̂`) into its six explicit
pieces. -/
theorem forcing_decomp {α C₀ S : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hS : 0 < S)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
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
        ≤ C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2))
    (hL12d : ∀ σ ∈ Set.Icc (0:ℝ) S, ∀ z : ℝ, 0 < z →
      z * deriv (fun z' => Work.Construction.L12 (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) σ) z') z
        = -Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) σ) z) :
    ∀ σ ∈ Set.Icc (0:ℝ) S, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.RegExportIface.RXT.VR α Φs E g z θ σ * A1f z θ
        + Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
            * B1f (Work.FTS.Regularity.pExp α) z θ
        + Work.FTS.RegExportIface.RXT.cR α Φs E g z θ σ * Fhf z θ
      = Ef (Work.FTS.RegExportIface.RXT.μR α Φs E g σ) (Work.FTS.Regularity.pExp α) z θ
        + Work.Construction.L12 (Work.FTS.Galerkin.slice
            (Work.FTS.RegExportIface.RXT.GR α g) σ) z * al1f (Work.FTS.Regularity.pExp α) z θ
        + Work.Construction.FK (Work.FTS.Galerkin.slice
            (Work.FTS.RegExportIface.RXT.GR α g) σ) z * al2f (Work.FTS.Regularity.pExp α) z θ
        + (2 * Work.FTS.Regularity.pExp α
            * Work.Construction.Vop (Work.FTS.RegExportIface.phiTil
                (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g)
                (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ) z θ)
          * A1f z θ
        + (2 * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g)
              (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ) z θ
            / Real.sin (2 * θ))) * B1f (Work.FTS.Regularity.pExp α) z θ
        + (-2 * Work.Construction.Rop (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g)
              (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ) z θ)
          * Fhf z θ := by
  intro σ hσ z θ hz hθ0 hθ1
  have hβpos : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  -- the `F_* + g̃`-split of the two radial transforms
  have hLK := Work.FTS_RegExport.RXT.SysAux.L12_FK_Ftau_split hα hα13 hS hOK hw σ hσ z hz
  have hL := hLK.1
  have hK := hLK.2
  -- the closed form of `2·Uop(Θ(F))`
  obtain ⟨-, hU2, -⟩ := Work.FTS_RegExport.RXT.SysAux.Theta_ops
    (αG := Work.FTS.Regularity.pExp α) hβpos
    (fun z' hz' => hL12d σ hσ z' hz') z θ hz hθ0 hθ1
  -- the additivity of `Uop` over `Φ = Φ̃ + Θ(F)`, from `bR_decomp`
  have hb := Work.FTS_RegExport.RXT.SysAux.bR_decomp hα hα13 hS hOK hC2 hL12 hw σ hσ
    z θ hz hθ0 hθ1
  have hs : Real.sin (2 * θ) ≠ 0 := by
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hθ1, Real.pi_pos]))
  have hbΘ : 2 * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
        (Work.Construction.Theta (Work.FTS.Regularity.pExp α) (Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) σ)) z θ
        / Real.sin (2 * θ))
      = -(3 / (2 * Work.FTS.Regularity.pExp α)) * Work.Construction.L12 (Work.Construction.Ftau
            (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) σ) z
        + Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) σ) z / 2 := by
    rw [show 2 * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
          (Work.Construction.Theta (Work.FTS.Regularity.pExp α) (Work.Construction.Ftau
            (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) σ)) z θ
          / Real.sin (2 * θ))
        = (2 * Work.Construction.Uop (Work.FTS.Regularity.pExp α)
            (Work.Construction.Theta (Work.FTS.Regularity.pExp α) (Work.Construction.Ftau
              (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) σ)) z θ)
          / Real.sin (2 * θ) from by ring]
    rw [hU2]
    field_simp
  simp only [Work.FTS.RegExportIface.RXT.VR, Work.FTS.RegExportIface.RXT.cR,
    Work.FTS.RegExportIface.Vz7, Work.FTS.RegExportIface.cs7,
    Ef, V0f, C0f, b0f, A1f, Fhf, B1f, al1f, al2f]
  rw [hb, hbΘ, hL, hK]
  field_simp
  ring

end Work.FTS_RegExport.RXT.Sys
