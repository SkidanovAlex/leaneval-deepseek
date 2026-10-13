/-
# `Work.FTS.EllSol.EllPkgGo` — item (d): `ellPkgGo_of_class` from the four transfers

This module assembles item (d) of the design,

  `ellPkgGo_of_class : ∃ Ce α₀, 0 < Ce ∧ 0 < α₀ ∧ ∀ α g Ψ, 0 < α → α ≤ α₀ →
      GalClass α g → EllClassO α g Ψ → EllPkgGo α Ce g Ψ`

as `EllPkgGoOfClass`, from the four analytic transfers of the chapter (each of which is proved in
its own module of this directory):

* `ellRop_transfer`/`ellUop_transfer`/`ellVop_transfer` — the `ℛ`, `U/sin2θ`, `V` estimates of the
  paper's §Modulation (the `I^𝒩₂`/`I^𝒩`/`V`-slots) on the solution class `EllClassO`;
* `ellVth_transfer` — the `V^{th}` sup-norm slot (`CoefThMem 1`/`CoefTh 1`, the `α^{-1/2}` gain);

together with the three fields that come straight from the class:

* `sol`/`smooth` are the first two conjuncts of `EllClassO`;
* `vanishU` is proved below from the Dirichlet data (`EllResid` vanishes identically on the two
  angular boundaries, and so does its `z`-derivative).

The rewrites `Construction.Rop/Uop/Vop (Construction.PhiTil α g Ψ) = EllipticEst.Rop/Uop/Vop α
(Elliptic.EllResid α g Ψ)` are the definitional identifications of the frozen packages
(`Work.FTS.EllipticEst.Rop_PhiTil_eq`, `Uop_PhiTil_eq`, `Vop_PhiTil_eq`).
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllSol.Defs
import Submission.Work.FTS.EllipticEst.RegQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The three fields that come from the class -/

theorem EllResid_at_zero {α : ℝ} {g Ψ : Fn} (h : EllClassO α g Ψ) (z : ℝ) :
    Work.Elliptic.EllResid α g Ψ z 0 = 0 := by
  rw [Work.Elliptic.EllResid]
  simp [h.sol.2.1 z]

theorem EllResid_at_pi_half {α : ℝ} {g Ψ : Fn} (h : EllClassO α g Ψ) (z : ℝ) :
    Work.Elliptic.EllResid α g Ψ z (π / 2) = 0 := by
  rw [Work.Elliptic.EllResid]
  simp only [show (2 : ℝ) * (π / 2) = π by ring, Real.sin_pi]
  simp [h.sol.2.2.1 z]

/-- `∂_z` of a function vanishing identically on an angular boundary vanishes there. -/
theorem pz_eq_zero_of_forall_eq_zero {f : Fn} {θ₀ : ℝ} (h : ∀ z, f z θ₀ = 0) (z : ℝ) :
    Work.Spaces.pz f z θ₀ = 0 := by
  have hfun : (fun z' : ℝ => f z' θ₀) = fun _ => (0 : ℝ) := funext h
  simp only [Work.Spaces.pz, hfun]
  exact deriv_const z (0 : ℝ)

/-- The `U`-slot vanishes identically on the angular boundary. -/
theorem vanishU_of_class {α : ℝ} {g Ψ : Fn} (h : EllClassO α g Ψ) :
    Work.Spaces.VanishTheta
      (Work.FTS.EllipticEst.Uop α (Work.Elliptic.EllResid α g Ψ)) := by
  constructor
  · intro z
    have h0 := EllResid_at_zero h z
    have h1 := pz_eq_zero_of_forall_eq_zero (fun z' => EllResid_at_zero h z') z
    simp only [Work.FTS.EllipticEst.Uop, h0, h1]
    ring
  · intro z
    have h0 := EllResid_at_pi_half h z
    have h1 := pz_eq_zero_of_forall_eq_zero (fun z' => EllResid_at_pi_half h z') z
    simp only [Work.FTS.EllipticEst.Uop, h0, h1]
    ring

/-! ## The assembly of item (d) -/

/-- **Item (d), assembled from the four transfers.** -/
theorem ellPkgGo_of_transfers
    (hR : ∃ Ce α₀ : ℝ, 0 < Ce ∧ 0 < α₀ ∧ ∀ (α : ℝ) (g Ψ : Fn),
      0 < α → α ≤ α₀ → Work.FTS.Nonlin.GalClass α g → EllClassO α g Ψ →
      Work.FTS.VocabO.HQo α 4
          (Work.FTS.EllipticEst.Rop α (Work.Elliptic.EllResid α g Ψ)) ∧
      Work.Spaces.HkNorm α 4 (Work.FTS.EllipticEst.Rop α (Work.Elliptic.EllResid α g Ψ))
        ≤ Ce * Work.Spaces.HkNorm α 4 g)
    (hU : ∃ Ce α₀ : ℝ, 0 < Ce ∧ 0 < α₀ ∧ ∀ (α : ℝ) (g Ψ : Fn),
      0 < α → α ≤ α₀ → Work.FTS.Nonlin.GalClass α g → EllClassO α g Ψ →
      Work.FTS.VocabO.HQo α 4
          (fun z θ => Work.FTS.EllipticEst.Uop α (Work.Elliptic.EllResid α g Ψ) z θ
            / Real.sin (2 * θ)) ∧
      Work.Spaces.HkNorm α 4
          (fun z θ => Work.FTS.EllipticEst.Uop α (Work.Elliptic.EllResid α g Ψ) z θ
            / Real.sin (2 * θ))
        ≤ Ce * Work.Spaces.HkNorm α 4 g)
    (hV : ∃ Ce α₀ : ℝ, 0 < Ce ∧ 0 < α₀ ∧ ∀ (α : ℝ) (g Ψ : Fn),
      0 < α → α ≤ α₀ → Work.FTS.Nonlin.GalClass α g → EllClassO α g Ψ →
      Work.FTS.VocabO.HQo α 4
          (Work.FTS.EllipticEst.Vop α (Work.Elliptic.EllResid α g Ψ)) ∧
      Work.Spaces.HkNorm α 4 (Work.FTS.EllipticEst.Vop α (Work.Elliptic.EllResid α g Ψ))
        ≤ Ce * Work.Spaces.HkNorm α 4 g)
    (hVth : ∃ Ce α₀ : ℝ, 0 < Ce ∧ 0 < α₀ ∧ ∀ (α : ℝ) (g Ψ : Fn),
      0 < α → α ≤ α₀ → Work.FTS.Nonlin.GalClass α g → EllClassO α g Ψ →
      Work.FTS.VocabO.CoefThMem 1
          (Work.FTS.EllipticEst.Vop α (Work.Elliptic.EllResid α g Ψ)) ∧
      Work.FTS.VocabO.CoefTh 1 (Work.FTS.EllipticEst.Vop α (Work.Elliptic.EllResid α g Ψ))
        ≤ Ce * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 4 g) :
    EllPkgGoOfClass := by
  obtain ⟨CR, αR, hCR, hαR, hR⟩ := hR
  obtain ⟨CU, αU, hCU, hαU, hU⟩ := hU
  obtain ⟨CV, αV, hCV, hαV, hV⟩ := hV
  obtain ⟨CT, αT, hCT, hαT, hT⟩ := hVth
  refine ⟨CR + CU + CV + CT, min (min αR αU) (min αV αT),
    by positivity, lt_min (lt_min hαR hαU) (lt_min hαV hαT), ?_⟩
  intro α hα hαm g Ψ hg hcl
  have hαR' : α ≤ αR := le_trans hαm (le_trans (min_le_left _ _) (min_le_left _ _))
  have hαU' : α ≤ αU := le_trans hαm (le_trans (min_le_left _ _) (min_le_right _ _))
  have hαV' : α ≤ αV := le_trans hαm (le_trans (min_le_right _ _) (min_le_left _ _))
  have hαT' : α ≤ αT := le_trans hαm (le_trans (min_le_right _ _) (min_le_right _ _))
  have hRle : CR ≤ CR + CU + CV + CT := by linarith
  have hUle : CU ≤ CR + CU + CV + CT := by linarith
  have hVle : CV ≤ CR + CU + CV + CT := by linarith
  have hTle : CT ≤ CR + CU + CV + CT := by linarith
  have hgnn : 0 ≤ Work.Spaces.HkNorm α 4 g := by
    rw [Work.Spaces.HkNorm]; exact Real.sqrt_nonneg _
  obtain ⟨hRM, hRn⟩ := hR α g Ψ hα hαR' hg hcl
  obtain ⟨hUM, hUn⟩ := hU α g Ψ hα hαU' hg hcl
  obtain ⟨hVM, hVn⟩ := hV α g Ψ hα hαV' hg hcl
  obtain ⟨hTM, hTn⟩ := hT α g Ψ hα hαT' hg hcl
  have hRs := Work.FTS.EllipticEst.Rop_PhiTil_eq α g Ψ
  have hUs := Work.FTS.EllipticEst.Uop_PhiTil_eq α g Ψ
  have hVs := Work.FTS.EllipticEst.Vop_PhiTil_eq α g Ψ
  refine ⟨hcl.sol, hcl.smooth, ?_, ?_, ?_, vanishU_of_class hcl, ?_⟩
  · rw [hRs]
    exact ⟨hRM, le_trans hRn (mul_le_mul_of_nonneg_right hRle hgnn)⟩
  · rw [hUs]
    exact ⟨hUM, le_trans hUn (mul_le_mul_of_nonneg_right hUle hgnn)⟩
  · rw [hVs]
    exact ⟨hVM, le_trans hVn (mul_le_mul_of_nonneg_right hVle hgnn)⟩
  · rw [hVs]
    refine ⟨hTM, le_trans hTn ?_⟩
    have h1 : CT * α ^ (-(1 / 2 : ℝ)) ≤ (CR + CU + CV + CT) * α ^ (-(1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_right hTle (Real.rpow_nonneg (le_of_lt hα) _)
    calc CT * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 4 g
        ≤ ((CR + CU + CV + CT) * α ^ (-(1 / 2 : ℝ))) * Work.Spaces.HkNorm α 4 g :=
          mul_le_mul_of_nonneg_right h1 hgnn
      _ = (CR + CU + CV + CT) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 4 g := by ring

end Work.FTS.EllSol
