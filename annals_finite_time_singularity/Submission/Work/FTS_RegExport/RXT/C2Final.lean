import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS_RegExport.RXT.C2Assemble
import Submission.Work.FTS_RegExport.RXT.C2Psi

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.C2Final` — the assembly of S4 (`coeff_C2`)

`coeff_C2_assembly` takes the three inputs of the pointwise argument — the `C³`-regularity of
the stream-function slice `slice (psiR α Φs E (tauExt g)) τ` on the open quadrant
(`C2Psi.contDiffOn_slice_PhiR_Q0`) and the `C²`/`C³`-regularity of the two radial functions
`𝔽K(F(τ))`, `L₁₂(F(τ))` on `(0,∞)` — and produces the three `C²`-statements for `Vz7`, `Vθ7`,
`cs7`; `coeff_C2` instantiates them (the radial inputs come from the parametric-integral and
primitive lemmas, applied to `Ftau_bounds`).
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.FinalV2 (DynOK' LimApprox)
open Work.FTS.RegExportIface.RXT (GR ΦR μR VR bR cR)

set_option autoImplicit false

/-- `c2m` is `C²` on the open interval. -/
theorem contDiffOn_c2m : ContDiffOn ℝ 2 Work.Construction.c2m (Set.Ioo 0 (π / 2)) := by
  have h1 : ContDiffOn ℝ 2 (fun θ : ℝ => Real.cos (2 * θ)) (Set.Ioo 0 (π / 2)) :=
    (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)).contDiffOn
  have h2 : ContDiffOn ℝ 2 (fun θ : ℝ => Real.sin θ ^ 2) (Set.Ioo 0 (π / 2)) :=
    (Real.contDiff_sin.contDiffOn).pow 2
  refine (h1.sub h2).congr (fun θ _ => ?_)
  simp only [Work.Construction.c2m]

/-- The stream function slice is `C^n` on `(0,∞)` when it is `C^n` at the fixed angle. -/
theorem contDiffOn_slice_fst {n : ℕ} {a : ℝ → ℝ}
    (ha : ContDiffOn ℝ n a (Set.Ioi 0)) :
    ContDiffOn ℝ n (fun p : ℝ × ℝ => a p.1) Work.FTS.EllipticEst.Q0 :=
  ha.comp contDiffOn_fst (fun p hp => hp.1)

/-- **The pointwise assembly.**  Given the `C³`-stream function and the two radial profiles,
the three coefficients of `(E)` are `C²` on the open quadrant. -/
theorem coeff_C2_assembly {α αG C₀ Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam} {τ : ℝ}
    (hαG : αG ≠ 0)
    (hΦ3 : ContDiffOn ℝ 3 (Function.uncurry (slice (ΦR α Φs E g) τ))
      Work.FTS.EllipticEst.Q0)
    (hFK2 : ContDiffOn ℝ 2 (Work.Construction.FK (Work.Construction.Ftau αG (GR α g) τ))
      (Set.Ioi 0))
    (hL12 : ContDiffOn ℝ 3 (Work.Construction.L12 (Work.Construction.Ftau αG (GR α g) τ))
      (Set.Ioi 0)) :
    ContDiffOn ℝ 2 (Function.uncurry (fun z θ =>
        Work.FTS.RegExportIface.Vz7 αG (μR α Φs E g) (GR α g) (ΦR α Φs E g) z θ τ))
      Work.FTS.EllipticEst.Q0 ∧
    ContDiffOn ℝ 2 (Function.uncurry (fun z θ =>
        Work.FTS.RegExportIface.Vθ7 αG (ΦR α Φs E g) z θ τ / Real.sin (2 * θ)))
      Work.FTS.EllipticEst.Q0 ∧
    ContDiffOn ℝ 2 (Function.uncurry (fun z θ =>
        Work.FTS.RegExportIface.cs7 αG (μR α Φs E g) (GR α g) (ΦR α Φs E g) z θ τ))
      Work.FTS.EllipticEst.Q0 := by
  have hL2 : ContDiffOn ℝ 2 (Work.Construction.L12 (Work.Construction.Ftau αG (GR α g) τ))
      (Set.Ioi 0) := hL12.of_le (by norm_num)
  have hc2m := contDiffOn_c2m
  -- the `θ`-weights
  have hsin2 : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.sin p.2 ^ 2)
      Work.FTS.EllipticEst.Q0 :=
    ((Real.contDiff_sin.contDiffOn).pow 2).comp contDiffOn_snd (fun p hp => hp.2)
  have hsin2θ : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
  have hsin : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
  -- Θ and Φ̃
  have hTheta : ContDiffOn ℝ 3
      (Function.uncurry (Work.Construction.Theta αG (Work.Construction.Ftau αG (GR α g) τ)))
      Work.FTS.EllipticEst.Q0 := by
    have h1 : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => (1 / (4 * αG)) * Real.sin (2 * p.2))
        Work.FTS.EllipticEst.Q0 :=
      contDiffOn_const.mul hsin
    have h2 := contDiffOn_slice_fst hL12
    refine (h1.mul h2).congr ?_
    intro p _
    simp only [Function.uncurry, Work.Construction.Theta, Work.Construction.s2]
  have hPsi : ContDiffOn ℝ 3 (Function.uncurry (Work.Construction.PhiTil αG
      (Work.Construction.Ftau αG (GR α g) τ) (slice (ΦR α Φs E g) τ)))
      Work.FTS.EllipticEst.Q0 := hΦ3.sub hTheta
  have hVop := contDiffOn_uncurry_Vop hPsi
  have hUop := contDiffOn_uncurry_Uop (α := αG) hΦ3
  have hRop := contDiffOn_uncurry_Rop (α := αG) hPsi
  refine ⟨?_, ?_, ?_⟩
  · -- Vz7
    have hLmul : ContDiffOn ℝ 2 (fun p : ℝ × ℝ =>
        Work.Construction.L12 (Work.Construction.Ftau αG (GR α g) τ) p.1
          * Work.Construction.c2m p.2) Work.FTS.EllipticEst.Q0 :=
      (contDiffOn_slice_fst hL2).mul (hc2m.comp contDiffOn_snd (fun p hp => hp.2))
    have hV : ContDiffOn ℝ 2 (fun p : ℝ × ℝ =>
        (2 * αG) * Work.Construction.Vop (Work.Construction.PhiTil αG
          (Work.Construction.Ftau αG (GR α g) τ) (slice (ΦR α Φs E g) τ)) p.1 p.2)
        Work.FTS.EllipticEst.Q0 :=
      contDiffOn_const.mul hVop
    refine (((contDiffOn_const (c := 1 - μR α Φs E g τ)).add hLmul).add hV).congr ?_
    intro p _
    simp only [Function.uncurry, Work.FTS.RegExportIface.Vz7,
      Work.FTS.RegExportIface.phiTil]
  · -- Vθ7 / sin 2θ
    refine (((contDiffOn_const (c := (2 : ℝ))).mul hUop).div hsin2θ
      (fun p hp => ne_of_gt (sin_two_pos_Q0 hp))).congr ?_
    intro p _
    simp only [Pi.div_apply, Function.uncurry, Work.FTS.RegExportIface.Vθ7]
  · -- cs7
    have hLdiv : ContDiffOn ℝ 2 (fun p : ℝ × ℝ =>
        Work.Construction.L12 (Work.Construction.Ftau αG (GR α g) τ) p.1 / αG)
        Work.FTS.EllipticEst.Q0 :=
      (contDiffOn_slice_fst hL2).div contDiffOn_const (fun p hp => hαG)
    have hFKmul : ContDiffOn ℝ 2 (fun p : ℝ × ℝ =>
        Real.sin p.2 ^ 2 * Work.Construction.FK (Work.Construction.Ftau αG (GR α g) τ) p.1)
        Work.FTS.EllipticEst.Q0 :=
      hsin2.mul (hFK2.comp contDiffOn_fst (fun p hp => hp.1))
    have hR : ContDiffOn ℝ 2 (fun p : ℝ × ℝ =>
        (2 : ℝ) * Work.Construction.Rop αG (Work.Construction.PhiTil αG
          (Work.Construction.Ftau αG (GR α g) τ) (slice (ΦR α Φs E g) τ)) p.1 p.2)
        Work.FTS.EllipticEst.Q0 :=
      contDiffOn_const.mul hRop
    refine ((((contDiffOn_const (c := 1 + μR α Φs E g τ)).sub hLdiv).add hFKmul).sub hR).congr ?_
    intro p _
    simp only [Function.uncurry, Work.FTS.RegExportIface.cs7,
      Work.FTS.RegExportIface.phiTil]

end Work.FTS_RegExport.RXT
