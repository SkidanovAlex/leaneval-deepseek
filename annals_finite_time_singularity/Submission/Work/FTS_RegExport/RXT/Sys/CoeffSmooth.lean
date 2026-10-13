import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS_RegExport.RXT.C2Final
import Submission.Work.FTS_RegExport.RXT.C2Assemble
import Submission.Work.FTS_RegExport.RXT.C2Psi
import Submission.Work.FTS_RegExport.RXT.C2Radial
import Submission.Work.FTS_RegExport.RXT.Ftau_bounds
import Submission.Work.FTS_RegExport.RXT.contDiffOn_two_integral_Itheta
import Submission.Work.FTS_RegExport.RXT.velVanish2Aux
import Submission.Work.FTS_RegExport.RXT.Sys.GdotCore

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.CoeffSmooth` — the `C²`-regularity of the coefficient pieces

Every *piece* of the three transport coefficients (and the residual `Φ̃_τ` and the singular part
`Θ(F_τ)`) is `C²` (resp. `C³`) on the open quadrant.  This is the assembly of
`RXT.coeff_C2_assembly` with the pieces exposed, and it is stated as an explicit list of
conjuncts so that the bound lemmas of `Sys.CoeffBounds` can consume the ones they need.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT.Sys

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.RegExportIface.RXT (GR ΦR μR)
open Work.FTS_RegExport.RXT (v2_PhiT v2_SlotR v2_SlotV v2_SlotU)
open Work.FTS.Regularity (pExp)
open Work.Construction (L12 FK Ftau Theta Uop Vop Rop c2m Fstar)

set_option autoImplicit false

variable {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}

/-- `K` is continuous on the closed angular interval (the weight of `𝔽K`). -/
theorem sys_continuousOn_K_Iθ : ContinuousOn Work.Spaces.K Work.Spaces.Iθ :=
  ((continuous_const.mul Real.continuous_sin).mul (Real.continuous_cos.pow 2)).continuousOn

/-! ## §2 Smoothness of the pieces -/

/-- Every piece of the three transport coefficients is `C²` on the open quadrant. -/
theorem coeff_pieces_contDiffOn {g : Fam} {τ : ℝ}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (pExp α) Cs Φs)
    (hOK : Work.FTS.FinalV2.DynOK' (pExp α) C₀ Φs E g)
    (hτ : 0 ≤ τ) :
    ContDiffOn ℝ 2 (Function.uncurry (fun z θ => (1 - μR α Φs E g τ)
        + L12 (Ftau (pExp α) (GR α g) τ) z * c2m θ)) Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => 2 * pExp α
        * Vop (v2_PhiT α Φs E g τ) z θ)) Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => L12 (Ftau (pExp α) (GR α g) τ) z
        * c2m θ)) Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => L12 (Ftau (pExp α) (GR α g) τ) z)) Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => L12 (Ftau (pExp α) (GR α g) τ) z
        / pExp α)) Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => (1 + μR α Φs E g τ)
        - L12 (Ftau (pExp α) (GR α g) τ) z / pExp α)) Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => (Real.sin θ) ^ 2
        * FK (Ftau (pExp α) (GR α g) τ) z)) Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => ((1 + μR α Φs E g τ)
        - L12 (Ftau (pExp α) (GR α g) τ) z / pExp α)
        + (Real.sin θ) ^ 2 * FK (Ftau (pExp α) (GR α g) τ) z)) Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => 2 * Rop (pExp α)
        (v2_PhiT α Φs E g τ) z θ)) Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => 2 * Uop (pExp α)
        (v2_PhiT α Φs E g τ) z θ / Real.sin (2 * θ))) Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => 2 * Uop (pExp α)
        (Theta (pExp α) (Ftau (pExp α) (GR α g) τ)) z θ / Real.sin (2 * θ))) Q0 ∧
      ContDiffOn ℝ 3 (Function.uncurry (v2_PhiT α Φs E g τ)) Q0 ∧
      ContDiffOn ℝ 3 (Function.uncurry (Theta (pExp α) (Ftau (pExp α) (GR α g) τ))) Q0 := by
  have hαG : (0 : ℝ) < pExp α := Work.FTS.Regularity.pExp_pos hα
  have hΦ3 := Work.FTS_RegExport.RXT.contDiffOn_slice_PhiR_Q0 (α := α) hEL3 hStar hOK τ hτ
  have hF2 := Work.FTS_RegExport.RXT.contDiffOn_Ftau_Q0 (C₀ := C₀) hα hα13 hOK τ hτ
  obtain ⟨Cf, hCf0, hbd⟩ := Work.FTS_RegExport.RXT.Ftau_bounds (C₀ := C₀) hα hα13 hOK τ hτ
  have hFK2 : ContDiffOn ℝ 2 (FK (Ftau (pExp α) (GR α g) τ)) (Set.Ioi 0) :=
    Work.FTS_RegExport.RXT.contDiffOn_two_integral_Itheta (φ := Work.Spaces.K)
      sys_continuousOn_K_Iθ hF2 hbd
  have hL12 : ContDiffOn ℝ 3 (L12 (Ftau (pExp α) (GR α g) τ)) (Set.Ioi 0) :=
    Work.FTS_RegExport.RXT.contDiffOn_three_L12 hFK2
  have hL2 : ContDiffOn ℝ 2 (L12 (Ftau (pExp α) (GR α g) τ)) (Set.Ioi 0) :=
    hL12.of_le (by norm_num)
  have hsin2θ : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Q0 :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
  have hsin3 : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Q0 :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
  have hsin2 : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.sin p.2 ^ 2) Q0 :=
    ((Real.contDiff_sin.contDiffOn).pow 2).comp contDiffOn_snd (fun p hp => hp.2)
  have hTheta : ContDiffOn ℝ 3 (Function.uncurry (Theta (pExp α)
      (Ftau (pExp α) (GR α g) τ))) Q0 := by
    have h1 : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => (1 / (4 * pExp α)) * Real.sin (2 * p.2)) Q0 :=
      contDiffOn_const.mul hsin3
    have h2 := Work.FTS_RegExport.RXT.contDiffOn_slice_fst hL12
    refine (h1.mul h2).congr ?_
    intro p _
    simp only [Function.uncurry, Theta, Work.Construction.s2]
  have hPsi : ContDiffOn ℝ 3 (Function.uncurry (v2_PhiT α Φs E g τ)) Q0 := by
    have h := hΦ3.sub hTheta
    refine h.congr ?_
    intro p _
    simp only [Function.uncurry, Pi.sub_apply, v2_PhiT, Work.Construction.PhiTil]
  -- the radial and angular pieces, in uncurried form
  have hLmul : ContDiffOn ℝ 2 (fun p : ℝ × ℝ =>
      L12 (Ftau (pExp α) (GR α g) τ) p.1 * c2m p.2) Q0 :=
    (Work.FTS_RegExport.RXT.contDiffOn_slice_fst hL2).mul
      (Work.FTS_RegExport.RXT.contDiffOn_c2m.comp contDiffOn_snd (fun p hp => hp.2))
  have hLf : ContDiffOn ℝ 2 (fun p : ℝ × ℝ =>
      L12 (Ftau (pExp α) (GR α g) τ) p.1) Q0 :=
    Work.FTS_RegExport.RXT.contDiffOn_slice_fst hL2
  have hLdiv : ContDiffOn ℝ 2 (fun p : ℝ × ℝ =>
      L12 (Ftau (pExp α) (GR α g) τ) p.1 / pExp α) Q0 :=
    hLf.div_const (pExp α)
  have hFKmul : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => (Real.sin p.2) ^ 2
      * FK (Ftau (pExp α) (GR α g) τ) p.1) Q0 :=
    hsin2.mul (hFK2.comp contDiffOn_fst (fun p hp => hp.1))
  have hVop := Work.FTS_RegExport.RXT.contDiffOn_uncurry_Vop hPsi
  have hUop := Work.FTS_RegExport.RXT.contDiffOn_uncurry_Uop (α := pExp α) hPsi
  have hUopT := Work.FTS_RegExport.RXT.contDiffOn_uncurry_Uop (α := pExp α) hTheta
  have hRop := Work.FTS_RegExport.RXT.contDiffOn_uncurry_Rop (α := pExp α) hPsi
  have hV2 : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => (2 : ℝ) * pExp α
      * Vop (v2_PhiT α Φs E g τ) p.1 p.2) Q0 :=
    contDiffOn_const.mul hVop
  have hR2 : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => (2 : ℝ)
      * Rop (pExp α) (v2_PhiT α Φs E g τ) p.1 p.2) Q0 :=
    contDiffOn_const.mul hRop
  have hUdiv : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => (2 : ℝ) * Uop (pExp α)
      (v2_PhiT α Φs E g τ) p.1 p.2 / Real.sin (2 * p.2)) Q0 :=
    (contDiffOn_const.mul hUop).div hsin2θ
      (fun p hp => ne_of_gt (Work.FTS_RegExport.RXT.sin_two_pos_Q0 hp))
  have hUdivT : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => (2 : ℝ) * Uop (pExp α)
      (Theta (pExp α) (Ftau (pExp α) (GR α g) τ)) p.1 p.2 / Real.sin (2 * p.2)) Q0 :=
    (contDiffOn_const.mul hUopT).div hsin2θ
      (fun p hp => ne_of_gt (Work.FTS_RegExport.RXT.sin_two_pos_Q0 hp))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hPsi, hTheta⟩
  · refine ((contDiffOn_const (c := 1 - μR α Φs E g τ)).add hLmul).congr ?_
    intro p _
    simp only [Function.uncurry, Pi.add_apply]
  · refine hV2.congr ?_
    intro p _
    simp only [Function.uncurry]
  · refine hLmul.congr ?_
    intro p _
    simp only [Function.uncurry]
  · refine hLf.congr ?_
    intro p _
    simp only [Function.uncurry]
  · refine hLdiv.congr ?_
    intro p _
    simp only [Function.uncurry]
  · refine ((contDiffOn_const (c := 1 + μR α Φs E g τ)).sub hLdiv).congr ?_
    intro p _
    simp only [Function.uncurry, Pi.sub_apply]
  · refine hFKmul.congr ?_
    intro p _
    simp only [Function.uncurry]
  · refine (((contDiffOn_const (c := 1 + μR α Φs E g τ)).sub hLdiv).add hFKmul).congr ?_
    intro p _
    simp only [Function.uncurry, Pi.add_apply, Pi.sub_apply]
  · refine hR2.congr ?_
    intro p _
    simp only [Function.uncurry]
  · refine hUdiv.congr ?_
    intro p _
    simp only [Function.uncurry]
  · refine hUdivT.congr ?_
    intro p _
    simp only [Function.uncurry]

end Work.FTS_RegExport.RXT.Sys
