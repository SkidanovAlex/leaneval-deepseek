import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_RegExport.RXR5L.ProdDefs
import Submission.Work.FTS_RegExport.RXT.Sys.CoeffSmooth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXR5L

open scoped Real Topology
open Set Filter

set_option autoImplicit false

/-! ## Slice differentiability from `C²` on the open quadrant

The two slices of a function `H` which is `C²` on the open quadrant `Q0` are differentiable at
every point of `Q0`: `Q0` is open, so `ContDiffOn.differentiableOn` gives `DifferentiableAt` of the
uncurried `H`, and a slice is that map composed with `z' ↦ (z', θ)` (resp. `θ' ↦ (z, θ')`). -/

/-- The `z`-slice of a function that is `C²` on the open quadrant is differentiable. -/
theorem differentiableAt_slice_fst_of_contDiffOn_two {H : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ 2 (Function.uncurry H) Work.FTS.EllipticEst.Q0) {z θ : ℝ}
    (hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    DifferentiableAt ℝ (fun z' => H z' θ) z := by
  have hd : DifferentiableAt ℝ (Function.uncurry H) (z, θ) :=
    (h.differentiableOn two_ne_zero).differentiableAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hzθ)
  have hlin : DifferentiableAt ℝ (fun z' : ℝ => (z', θ)) z := by fun_prop
  simpa [Function.comp_def, Function.uncurry] using hd.comp z hlin

/-- The `θ`-slice of a function that is `C²` on the open quadrant is differentiable. -/
theorem differentiableAt_slice_snd_of_contDiffOn_two {H : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ 2 (Function.uncurry H) Work.FTS.EllipticEst.Q0) {z θ : ℝ}
    (hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    DifferentiableAt ℝ (fun θ' => H z θ') θ := by
  have hd : DifferentiableAt ℝ (Function.uncurry H) (z, θ) :=
    (h.differentiableOn two_ne_zero).differentiableAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hzθ)
  have hlin : DifferentiableAt ℝ (fun θ' : ℝ => (z, θ')) θ := by fun_prop
  simpa [Function.comp_def, Function.uncurry] using hd.comp θ hlin

/-- Differentiability of the two slices of the three slots `CoefR/CoefV/CoefU` of
`PhiT α Φs E g τ` on the open quadrant.

Route: `RXT.Sys.coeff_pieces_contDiffOn` (last two conjuncts) supplies
`ContDiffOn ℝ 3 (Function.uncurry (v2_PhiT α Φs E g τ)) Q0` (and the same for
`Theta (pExp α) (Ftau (pExp α) (GR α g) τ)`) for `τ ≥ 0`; `Q0 = Ioi 0 ×ˢ Ioo 0 (π/2)` is open, so
at `(z,θ) ∈ Q0` the slices `z ↦ Φ̃(z,θ)`, `z ↦ pz Φ̃(z,θ)`, `z ↦ pz(pz Φ̃)(z,θ)`,
`z ↦ pth Φ̃(z,θ)`, `z ↦ pz(pth Φ̃)(z,θ)` (and the `θ`-slices) are differentiable, using
`GalBasis.contDiffAt_slice_fst_of_uncurry` together with
`GalBasis.contDiffOn_uncurry_pzIter_le` / `contDiffOn_uncurry_pthIter_le` (the `z`-slices of the
iterated partials are again smooth of the expected order).  Since `Rop α Ψ = (2 sinθ·Ψ + α sinθ·z·pz Ψ
+ cosθ·pth Ψ)/cosθ`, `Vop Ψ = pth Ψ - tanθ·Ψ`, `Uop α Ψ = -3Ψ - α z·pz Ψ`, the slice
differentiability follows from the chain/product/quotient rules (`cos θ > 0` and `sin 2θ ≠ 0` on the
open interval, so the divisions are honest there). -/
theorem coef_diff {α Ce C₀ Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g) :
    ∀ S > 0, ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      DifferentiableAt ℝ (fun z' => Work.FTS_RegExport.RXR5L.CoefR α Φs E g τ z' θ) z ∧
      DifferentiableAt ℝ (fun θ' => Work.FTS_RegExport.RXR5L.CoefR α Φs E g τ z θ') θ ∧
      DifferentiableAt ℝ (fun z' => Work.FTS_RegExport.RXR5L.CoefV α Φs E g τ z' θ) z ∧
      DifferentiableAt ℝ (fun θ' => Work.FTS_RegExport.RXR5L.CoefV α Φs E g τ z θ') θ ∧
      DifferentiableAt ℝ (fun z' => Work.FTS_RegExport.RXR5L.CoefU α Φs E g τ z' θ) z ∧
      DifferentiableAt ℝ (fun θ' => Work.FTS_RegExport.RXR5L.CoefU α Φs E g τ z θ') θ := by
  intro S hS τ hτ z θ hz hθ hθ2
  -- `C³` smoothness of `Φ̃_τ = v2_PhiT α Φs E g τ` on the open quadrant
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hΨ3, -⟩ :=
    Work.FTS_RegExport.RXT.Sys.coeff_pieces_contDiffOn (C₀ := C₀) (Cs := Cs) (g := g)
      hα hα13 hEL3 hStar hOK hτ.1
  have hQ0 : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ, hθ2⟩
  -- the three coefficient *pieces* are `C²` on the open quadrant
  have hR2 : ContDiffOn ℝ 2 (Function.uncurry (Work.Construction.Rop
      (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ)))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS_RegExport.RXT.contDiffOn_uncurry_Rop hΨ3
  have hV2 : ContDiffOn ℝ 2 (Function.uncurry (Work.Construction.Vop
      (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ))) Work.FTS.EllipticEst.Q0 :=
    Work.FTS_RegExport.RXT.contDiffOn_uncurry_Vop hΨ3
  have hU2 : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.Construction.Uop
      (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ) z θ
        / Real.sin (2 * θ))) Work.FTS.EllipticEst.Q0 :=
    Work.FTS_RegExport.RXT.contDiffOn_uncurry_div_sin_two
      (Work.FTS_RegExport.RXT.contDiffOn_uncurry_Uop
        (α := Work.FTS.Regularity.pExp α) hΨ3)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact differentiableAt_slice_fst_of_contDiffOn_two hR2 hQ0
  · exact differentiableAt_slice_snd_of_contDiffOn_two hR2 hQ0
  · exact differentiableAt_slice_fst_of_contDiffOn_two hV2 hQ0
  · exact differentiableAt_slice_snd_of_contDiffOn_two hV2 hQ0
  · exact differentiableAt_slice_fst_of_contDiffOn_two hU2 hQ0
  · exact differentiableAt_slice_snd_of_contDiffOn_two hU2 hQ0

end Work.FTS_RegExport.RXR5L
