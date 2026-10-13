/-
Copyright: work module for the Elgindi finite-time singularity project.

# `α D_z W` in `ℋ^k`, `W = EllResid α F Ψ` (the residual of §Modulation)

This module owns the statement `Work.FTS.EllipticEst.alphaDzW_Hk_le`

  `α |D_z W|_{ℋ^k} ≤ C (|F|_{ℋ^k} + |∂_θθ W|_{ℋ^k} + α² |z²∂_zzΨ|_{ℋ^k})`,

`W = Ψ - (1/(4α)) sin 2θ · L₁₂(F)` (paper §Modulation, tex 1450--1480: the `α z∂_z`-term of
the transport operator `U(Φ_g - (1/4α) sin 2θ L₁₂(g))`).

## The algebraic reduction

Write `F_* = Work.Elliptic.Fstar F`, `Ψ̂ = Ψ + Gsing α F · sin 2θ` (the solution with the
singular term added; `Work.Elliptic.bslOp_sing_source` gives `L Ψ̂ = orthSource F`), and
`SF = sin 2θ · F_*`.  The identities proved below are

* `Dz_EllResid`:  `D_z W = D_z Ψ + (3/(4α)) · SF`  (from `z ∂_z L₁₂(F) = -3F_*`);
* `Lzero_EllResid_eq`: `L₀ W = L₀ Ψ = L₀ Ψ̂` (`L₀` kills the radial multiples of `sin 2θ`);
* `alphaDzEllResid_eq`:
  `(5 + α) · α · D_z W = α² D_z²Ψ̂ + 5α D_zΨ̂ - α² (z² ∂_zzΨ) + (3α/4) · SF`.

The last identity is the exact form of the paper's manipulation: the source `F` cancels
against `orthSource F` (`orthSource F - F + (15/4) SF = 0`), and the remaining terms are
precisely the quantities controlled by Theorem `RemovingL12` (`α² z²∂_zzΨ` and the residual
`∂_θθ W`) together with the `O(|F|_{ℋ^k})` quantities `Ḡ · sin 2θ` (`Gbar_Hk_fts`) and
`F_* · sin 2θ` (`Fstar_Hk_le`).

## Status of the target (read before continuing)

Proved here: `Dz_EllResid`, `Lzero_radial_sin_two`, `DzIter_add_eq`,
`alphaDzEllResid_eq` (the algebraic identity (☆), with the three splitting hypotheses
`hLzero_split`, `hDz_split`, `hDz2_split` — these are `Work.Elliptic.bslOp_add` /
`Work.Coercivity.E2Mixed.DzIter_add_of_isOpen` / `Work.Spaces.Lzero_sin_two_mul` for
smooth data).

Remaining for the target `alphaDzW_Hk_le`:

1. **(☆) at `ℋ^k` level — DONE.**  `HkNorm_alphaDzEllResid_eq` transports the identity to
   `HkSq` (`HkSq_congr_open`) and takes the constant out of the norm; `HkNorm_sum4_le` is the
   sub-additivity chain (with `hadd` = `HkNorm_add_le` and `hcm` = `HkNorm_const_mul` as
   parameters, plus smoothness/`HkMem` of the four pieces and the two partial sums);
   `alphaDzW_Hk_le_first_link` assembles them into
   `α|D_z W| ≤ (1+α)⁻¹·2·(α²|D_z²Ψ̂| + 5α|D_zΨ̂| + α²|z²∂_zzΨ| + (3α/4)|SF|)`.
2. **The three analytic inputs.**  `HkNorm_Dz_le_open` (the radial AM–GM),
   `HkNorm_le_pth2_open` (the angular Poincaré), `Gbar_Hk_fts`, `Fstar_Hk_le`;
   the identity
   `∂_θθΨ̂ = ∂_θθW - 4 Ḡ sin 2θ` and
   `α² z² ∂_zzΨ̂ = α² z² ∂_zzΨ + (15/4) SF + 5(5+α) Ḡ sin 2θ`
   (from `Work.Elliptic.Gsing_ode`) then bound the remaining terms, together with
   `|Ψ̂| ≤ C|∂_θθΨ̂|` and `α|D_zΨ̂| ≤ C(|Ψ̂| + α²|z²∂_zzΨ̂|)`.
3. **Obstacle (interface).**  `Fstar_Hk_le` and `Gbar_Hk_fts` are stated with the hypothesis
   `SmoothNbhd F`, which is *not* available for the `F` of `EllHyp` (only the equation
   `bslOp α Ψ = F` on the open quadrant is).  The natural repair is to replace
   `SmoothNbhd F` by smoothness on the open quadrant
   `∀ n, ContDiffOn ℝ n (Function.uncurry F) (Ioi 0 ×ˢ Ioo 0 (π/2))`, which *is* available.
   Note also that `SmoothNbhd (fun z θ => bslOp α Ψ z θ)` is **false** in general
   (`Real.tan (π/2) = 0` by totalised division, so `θ ↦ tan θ · Ψ z θ` jumps at `π/2` when
   `Ψ z (π/2) = 0` and `∂_θΨ z (π/2) ≠ 0`), so the "replace `F` by `bslOp α Ψ`" device does
   not work; the open-quadrant formulation is the way.

-/

import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Algebra
import Submission.Work.Elliptic.bslOp_add
import Submission.Work.Elliptic.bslOp_sinG
import Submission.Work.Elliptic.bslOp_sing_source
import Submission.Work.Elliptic.L12Iterate
import Submission.Work.FTS.EllipticEst.DzIter_mul_of_radial
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.EllipticEst.HkNorm_const_mul
import Submission.Work.FTS.LocData.HkIntegrand_const_mul
import Submission.Work.Coercivity.E2Mixed.E2model_mixed_split
import Submission.Work.FTS.EllipticEst.Gsing_deriv_rel
import Submission.Work.Elliptic.Gsing_ode
import Submission.Work.FTS.EllipticEst.Cert.FstarSmoothOfSol
import Submission.Work.FTS.EllipticEst.Cert.FstarDivIntegrableOfSolHk
import Submission.Work.FTS.EllipticEst.Cert.Gsing_smooth_ode_of_facts
import Submission.Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts
import Submission.Work.FTS.EllipticEst.HkNorm_add_fts
import Submission.Work.FTS.EllipticEst.EllHyp_F_smoothOpen
import Submission.Work.FTS.EllipticEst.Fstar_Hk_le_open
import Submission.Work.FTS.EllipticEst.Straight_DzHk_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

/-! ## `L₀` and the radial multiples of `sin 2θ` -/

/-- `L₀(G(z) sin 2θ) = 0`: the `sin 2θ`-direction lies in the kernel of the `α = 0` operator. -/
theorem Lzero_radial_sin_two (g : ℝ → ℝ) (z θ : ℝ) (hθ : Real.cos θ ≠ 0) :
    Work.Elliptic.Lzero (fun z θ => g z * Real.sin (2 * θ)) z θ = 0 :=
  Work.Elliptic.Lzero_sin_two_mul g z θ hθ

/-! ## Additivity of `D_z^j` on functions smooth on an open set -/

/-- On functions smooth on an open set, the iterated `D_z`-operator is additive.  (This is
`Work.Coercivity.E2Mixed.DzIter_add_of_isOpen`, restated in the local vocabulary; it supplies
the `hDz_split`/`hDz2_split` hypotheses of `alphaDzEllResid_eq` for smooth data.) -/
theorem DzIter_add_eq (F G : ℝ → ℝ → ℝ) {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hF : ContDiffOn ℝ ⊤ (Function.uncurry F) V)
    (hG : ContDiffOn ℝ ⊤ (Function.uncurry G) V) (j : ℕ) {z θ : ℝ} (hy : (z, θ) ∈ V) :
    Work.Spaces.DzIter j (fun z θ => F z θ + G z θ) z θ
      = Work.Spaces.DzIter j F z θ + Work.Spaces.DzIter j G z θ :=
  Work.Coercivity.E2Mixed.DzIter_add_of_isOpen hV hF hG j hy

/-! ## The `D_z`-derivative of the residual -/

/-- `D_z` of the residual: `D_z(Ψ - (1/(4α)) sin 2θ L₁₂(F)) = D_zΨ + (3/(4α)) sin 2θ F_*`. -/
theorem Dz_EllResid (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) {z θ : ℝ} (hα : 0 < α) (hz : 0 < z)
    (hΨ : DifferentiableAt ℝ (fun z' => Ψ z' θ) z)
    (hL12 : HasDerivAt (Work.Elliptic.L12 F) (-(3 * Work.Elliptic.Fstar F z / z)) z) :
    Work.Spaces.Dz (Work.Elliptic.EllResid α F Ψ) z θ
      = Work.Spaces.Dz Ψ z θ
        + (3 / (4 * α)) * (Real.sin (2 * θ) * Work.Elliptic.Fstar F z) := by
  have hfun : (fun z' => Work.Elliptic.EllResid α F Ψ z' θ)
      = fun z' => Ψ z' θ - ((1 / (4 * α)) * Real.sin (2 * θ)) * Work.Elliptic.L12 F z' := by
    funext z'
    simp only [Work.Elliptic.EllResid]
  have hsplit : (fun z' => Ψ z' θ - ((1 / (4 * α)) * Real.sin (2 * θ)) * Work.Elliptic.L12 F z')
      = ((fun z' => Ψ z' θ)
          - (fun z' => ((1 / (4 * α)) * Real.sin (2 * θ)) * Work.Elliptic.L12 F z')) := rfl
  have hderiv : deriv (fun z' => Work.Elliptic.EllResid α F Ψ z' θ) z
      = deriv (fun z' => Ψ z' θ) z
        - ((1 / (4 * α)) * Real.sin (2 * θ)) * deriv (Work.Elliptic.L12 F) z := by
    rw [hfun]
    rw [hsplit, deriv_sub hΨ (hL12.differentiableAt.const_mul _)]
    rw [deriv_const_mul ((1 / (4 * α)) * Real.sin (2 * θ)) hL12.differentiableAt]
  have hzL : z * deriv (Work.Elliptic.L12 F) z = -(3 * Work.Elliptic.Fstar F z) := by
    rw [hL12.deriv]
    field_simp
  simp only [Work.Spaces.Dz, Work.Spaces.pz]
  rw [hderiv]
  linear_combination (-(((1 / (4 * α)) * Real.sin (2 * θ)))) * hzL

/-! ## The identity for `α D_z W` -/

/-- **The algebraic identity of `α D_z W`.**  On the open strip `z > 0`, `cos θ ≠ 0`, with
`Ψ̂ = Ψ + Gsing α F · sin 2θ`: if `L Ψ = F` at `(z,θ)`, `L Ψ̂ = orthSource F` (the singular-term
ODE), and if `L₀` and the `D_z`-derivatives split over the sum `Ψ̂ = Ψ + Gsin 2θ` (the three
hypotheses `hLzero_split`, `hDz_split`, `hDz2_split`, which hold for smooth data by
`Work.Elliptic.bslOp_add`, `Work.Coercivity.E2Mixed.DzIter_add_of_isOpen` and
`Work.Spaces.Lzero_sin_two_mul`), then

  `(5 + α) · α · D_z W = α² D_z²Ψ̂ + 5α D_zΨ̂ - α² (z² ∂_zzΨ) + (3α/4) · sin 2θ · F_*`,

where `W = EllResid α F Ψ`. -/
theorem alphaDzEllResid_eq (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α) {z θ : ℝ}
    (hz : 0 < z) (hcos : Real.cos θ ≠ 0)
    (hsol : Work.Elliptic.bslOp α Ψ z θ = F z θ)
    (hΨc2 : ContDiffAt ℝ 2 (Function.uncurry Ψ) (z, θ))
    (hGc2 : ContDiffAt ℝ 2 (Work.Elliptic.Gsing α F) z)
    (hGode : α ^ 2 * z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α F) z') z
        + α * (5 + α) * z * deriv (Work.Elliptic.Gsing α F) z
      = (15 / 4) * Work.Elliptic.Fstar F z)
    (hL12 : HasDerivAt (Work.Elliptic.L12 F) (-(3 * Work.Elliptic.Fstar F z / z)) z)
    (hΨd : DifferentiableAt ℝ (fun z' => Ψ z' θ) z)
    (hΨd2 : DifferentiableAt ℝ (fun z' => Work.Spaces.pz Ψ z' θ) z)
    (hdP : DifferentiableAt ℝ
      (fun z' => (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z' θ) z)
    (hdP2 : DifferentiableAt ℝ
      (fun z' => Work.Spaces.pz
        (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z' θ) z)
    (hLzero_split : Work.Elliptic.Lzero
        (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
      = Work.Elliptic.Lzero Ψ z θ)
    (hDz_split : Work.Spaces.Dz
        (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
      = Work.Spaces.Dz Ψ z θ
        + Real.sin (2 * θ) * Work.Spaces.Dz (fun z θ => Work.Elliptic.Gsing α F z) z θ)
    (hDz2_split : Work.Spaces.DzIter 2
        (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
      = Work.Spaces.DzIter 2 Ψ z θ
        + Real.sin (2 * θ) * Work.Spaces.DzIter 2 (fun z θ => Work.Elliptic.Gsing α F z) z θ)
    (hGsd : DifferentiableAt ℝ (Work.Elliptic.Gsing α F) z)
    (hGsd2 : DifferentiableAt ℝ (fun z' => deriv (Work.Elliptic.Gsing α F) z') z) :
    (5 + α) * (α * Work.Spaces.Dz (Work.Elliptic.EllResid α F Ψ) z θ)
      = α ^ 2 * Work.Spaces.DzIter 2
            (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
        + 5 * α * Work.Spaces.Dz
            (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
        - α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        + (3 * α / 4) * (Real.sin (2 * θ) * Work.Elliptic.Fstar F z) := by
  set SF : ℝ := Real.sin (2 * θ) * Work.Elliptic.Fstar F z with hSF
  -- the two equations in `D_z` form
  have hL1 : -α ^ 2 * Work.Spaces.DzIter 2 Ψ z θ - 5 * α * Work.Spaces.Dz Ψ z θ
      + Work.Elliptic.Lzero Ψ z θ = F z θ := by
    rw [← bslOp_eq_Dz α Ψ hΨd hΨd2]
    exact hsol
  have hL2 : -α ^ 2 * Work.Spaces.DzIter 2
          (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
        - 5 * α * Work.Spaces.Dz
          (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
        + Work.Elliptic.Lzero
          (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
      = Work.Elliptic.orthSource F z θ := by
    rw [← bslOp_eq_Dz α _ hdP hdP2]
    exact Work.Elliptic.bslOp_sing_source α F Ψ z θ hcos hΨc2 hGc2 hsol hGode
  -- the algebra
  have hstep : α * Work.Spaces.Dz (Work.Elliptic.EllResid α F Ψ) z θ
      = α * Work.Spaces.Dz Ψ z θ + (3 / 4) * SF := by
    rw [Dz_EllResid α F Ψ hα hz hΨd hL12]
    simp only [hSF]
    have hαne : α ≠ 0 := ne_of_gt hα
    field_simp
  have horth : Work.Elliptic.orthSource F z θ = F z θ - (15 / 4) * SF := by
    rw [Work.Elliptic.orthSource, hSF]
    ring
  have hmain : α ^ 2 * Work.Spaces.DzIter 2
          (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
        + 5 * α * Work.Spaces.Dz
          (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
      = α ^ 2 * Work.Spaces.DzIter 2 Ψ z θ + 5 * α * Work.Spaces.Dz Ψ z θ
        + (15 / 4) * SF := by
    rw [hLzero_split] at hL2
    linarith [hL1, hL2, horth]
  have hzsq : z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
      = Work.Spaces.DzIter 2 Ψ z θ - Work.Spaces.Dz Ψ z θ :=
    zsq_pzIter2_eq Ψ hΨd hΨd2
  simp only [hSF] at hmain hstep ⊢
  linear_combination (5 + α) * hstep - hmain + α ^ 2 * hzsq

/-! ## The identity (☆) of `alphaDzEllResid_eq`, discharged from `EllHyp`

The pointwise hypotheses of `alphaDzEllResid_eq` are supplied from the data class `EllHyp`
(the smoothness of `Ψ` on a neighbourhood of the closed quadrant, the elliptic law
`bslOp α Ψ = F`, the smoothness of `F_*`/`Gsing` and the ODE for `Gsing`); the public
statement is `alphaDzEllResid_eq_of_EllHyp_local`.  (This is the content of the module
`alphaDzEllResid_eq_of_Hyp`, inlined here because that module imports this one; its helper
lemmas are `private`, so inlining them creates no name clashes.) -/

private theorem contDiffAt_two_of_smoothNbhd {Ψ : ℝ → ℝ → ℝ} (h : Work.Spaces.SmoothNbhd Ψ)
    {z θ : ℝ} (hz : -1 < z) (hθ : -1 < θ) (hθ' : θ < π / 2 + 1) :
    ContDiffAt ℝ 2 (Function.uncurry Ψ) (z, θ) :=
  ((show ContDiffOn ℝ ⊤ (Function.uncurry Ψ)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1)) from h).contDiffAt
    ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds
      (show (z, θ) ∈ Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1) from ⟨hz, hθ, hθ'⟩))).of_le
      le_top

/-! ## `C²` of `Φ(z,θ) = G(z) sin 2θ` at a point -/

private theorem contDiffAt_two_uncurry_radial_sin2 {G : ℝ → ℝ} {z θ : ℝ}
    (hG : ContDiffAt ℝ 2 G z) :
    ContDiffAt ℝ 2 (Function.uncurry (fun z θ => G z * Real.sin (2 * θ))) (z, θ) := by
  show ContDiffAt ℝ 2 (fun p : ℝ × ℝ => G p.1 * Real.sin (2 * p.2)) (z, θ)
  have h1 : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => G p.1) (z, θ) := by
    have h := hG.comp (z, θ) (by fun_prop : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => p.1) (z, θ))
    simpa [Function.comp_def] using h
  have h2 : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Real.sin (2 * p.2)) (z, θ) := by fun_prop
  exact h1.mul h2

/-! ## The `z`-slices of `Ψ` -/

/-- For `Ψ` smooth near the closed quadrant and `θ ∈ (-1, π/2+1)`, the `z`-slices
`z' ↦ Ψ z' θ` are differentiable at every point of a neighbourhood of `z`. -/
private theorem eventually_differentiableAt_slice_fst {Ψ : ℝ → ℝ → ℝ}
    (hsm : Work.Spaces.SmoothNbhd Ψ) {z θ : ℝ} (hz : -1 < z)
    (hθ : θ ∈ Set.Ioo (-1) (π / 2 + 1)) :
    ∀ᶠ z' in 𝓝 z, DifferentiableAt ℝ (fun z'' => Ψ z'' θ) z' := by
  filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
  have hmem : (z', θ) ∈ Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1) := ⟨hz', hθ⟩
  have hd : DifferentiableAt ℝ (Function.uncurry Ψ) (z', θ) :=
    ((show ContDiffOn ℝ ⊤ (Function.uncurry Ψ)
        (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1)) from hsm).differentiableOn
      (by simp)).differentiableAt ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds hmem)
  exact Work.Spaces.differentiableAt_curry_left hd

/-! ## The product rule along a `z`-slice -/

/-- On a neighbourhood of `z`, the derivative of the `z`-slice of `Ψ + G·sin 2θ` is the sum
of the derivatives of the `z`-slices of `Ψ` and of `G·sin 2θ`. -/
private theorem eventually_deriv_slice_add_radial_sin2 {G : ℝ → ℝ} {Ψ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hΨ : ∀ᶠ z' in 𝓝 z, DifferentiableAt ℝ (fun z'' => Ψ z'' θ) z')
    (hG : ∀ᶠ z' in 𝓝 z, DifferentiableAt ℝ G z') :
    (fun z' => deriv (fun z'' => Ψ z'' θ + G z'' * Real.sin (2 * θ)) z')
      =ᶠ[𝓝 z]
      (fun z' => deriv (fun z'' => Ψ z'' θ) z'
        + deriv (fun z'' => G z'' * Real.sin (2 * θ)) z') := by
  filter_upwards [hΨ, hG] with z' h1 h2
  have h3 : HasDerivAt (fun z'' => G z'' * Real.sin (2 * θ))
      (deriv G z' * Real.sin (2 * θ)) z' := by
    simpa only [mul_comm] using h2.hasDerivAt.mul_const (Real.sin (2 * θ))
  have h4 := (h1.hasDerivAt.add h3).deriv
  rw [← deriv_mul_const_field (u := G) (x := z') (Real.sin (2 * θ))] at h4
  exact h4

/-! ## Additivity of `D_z` and `D_z²` from the product rule

`D_z^j` is a composition of derivatives, so it is additive on functions that are
differentiable at the point; the analyticity demanded by the general additivity lemmas of the
workspace (`DzIter_add_of_isOpen`) is not available for `G = Gsing α F`, so the two additivity
statements needed below are proved from the product rule instead. -/

/-- `D_z` is additive at `(z,θ)` on functions whose slices are differentiable at `z`. -/
private theorem Dz_add_of_differentiableAt {f g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hf : DifferentiableAt ℝ (fun z'' => f z'' θ) z)
    (hg : DifferentiableAt ℝ (fun z'' => g z'' θ) z) :
    Work.Spaces.Dz (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.Dz f z θ + Work.Spaces.Dz g z θ := by
  simp only [Work.Spaces.Dz, Work.Spaces.pz]
  rw [show deriv (fun z'' => f z'' θ + g z'' θ) z
      = deriv (fun z'' => f z'' θ) z + deriv (fun z'' => g z'' θ) z from deriv_add hf hg]
  ring

/-- `D_z²f = z·∂_z(z · ∂_zf(·,θ))` at `(z,θ)`, by definition. -/
private theorem DzIter_two_eq_mul_deriv (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DzIter 2 f z θ
      = z * deriv (fun z' => z' * deriv (fun z'' => f z'' θ) z') z := rfl

/-- `D_z²` is additive at `(z,θ)` as soon as `∂_zf` and `∂_zg` are differentiable at `z` and
the derivative of the slice of the sum is the sum of the derivatives of the slices. -/
private theorem DzIter_two_add_of_deriv_eventuallyEq {f g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hf : DifferentiableAt ℝ (fun z' => Work.Spaces.pz f z' θ) z)
    (hg : DifferentiableAt ℝ (fun z' => Work.Spaces.pz g z' θ) z)
    (hev : (fun z' => deriv (fun z'' => f z'' θ + g z'' θ) z')
      =ᶠ[𝓝 z] (fun z' => deriv (fun z'' => f z'' θ) z' + deriv (fun z'' => g z'' θ) z')) :
    Work.Spaces.DzIter 2 (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.DzIter 2 f z θ + Work.Spaces.DzIter 2 g z θ := by
  have ha : DifferentiableAt ℝ (fun z' => deriv (fun z'' => f z'' θ) z') z := by
    simpa only [Work.Spaces.pz] using hf
  have hb : DifferentiableAt ℝ (fun z' => deriv (fun z'' => g z'' θ) z') z := by
    simpa only [Work.Spaces.pz] using hg
  have h1 : (fun z' => z' * deriv (fun z'' => f z'' θ + g z'' θ) z')
      =ᶠ[𝓝 z]
      (fun z' => z' * (deriv (fun z'' => f z'' θ) z' + deriv (fun z'' => g z'' θ) z')) := by
    filter_upwards [hev] with z' hz'
    rw [hz']
  rw [DzIter_two_eq_mul_deriv (fun z θ => f z θ + g z θ) z θ, h1.deriv_eq,
    DzIter_two_eq_mul_deriv f z θ, DzIter_two_eq_mul_deriv g z θ]
  have hsplit : deriv (fun z' => z' * (deriv (fun z'' => f z'' θ) z'
        + deriv (fun z'' => g z'' θ) z')) z
      = deriv (fun z' => z' * deriv (fun z'' => f z'' θ) z') z
        + deriv (fun z' => z' * deriv (fun z'' => g z'' θ) z') z := by
    have hA : DifferentiableAt ℝ (fun z' => z' * deriv (fun z'' => f z'' θ) z') z :=
      differentiableAt_id.mul ha
    have hB : DifferentiableAt ℝ (fun z' => z' * deriv (fun z'' => g z'' θ) z') z :=
      differentiableAt_id.mul hb
    have hfun : (fun z' => z' * (deriv (fun z'' => f z'' θ) z' + deriv (fun z'' => g z'' θ) z'))
        = fun z' => z' * deriv (fun z'' => f z'' θ) z'
          + z' * deriv (fun z'' => g z'' θ) z' := by
      funext w; ring
    rw [hfun]
    rw [show (fun z' => z' * deriv (fun z'' => f z'' θ) z' + z' * deriv (fun z'' => g z'' θ) z')
        = (fun z' => z' * deriv (fun z'' => f z'' θ) z')
          + (fun z' => z' * deriv (fun z'' => g z'' θ) z') from rfl]
    rw [deriv_add hA hB]
  rw [hsplit]
  ring

/-! ## The target identity -/

theorem alphaDzEllResid_eq_of_EllHyp_local (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hα1 : α ≤ 1 / 4) (hHyp : Work.FTS.EllipticEst.EllHyp α k F Ψ) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      α * Work.Spaces.Dz (Work.Elliptic.EllResid α F Ψ) z θ
        = (1 / (5 + α)) *
            (α ^ 2 * Work.Spaces.DzIter 2
                (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
              + 5 * α * Work.Spaces.Dz
                (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
              - α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
              + (3 * α / 4) * (Real.sin (2 * θ) * Work.Elliptic.Fstar F z)) := by
  -- the facts about `F_*` and about `G = Gsing α F` that the identity needs
  have hFstar_sm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar F) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.Cert.FstarSmoothOfSol α F Ψ hHyp.smoothNbhd hHyp.sol
  have hFstar_int : MeasureTheory.IntegrableOn
      (fun r => Work.Elliptic.Fstar F r / r) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.Cert.FstarDivIntegrableOfSolHk α k F Ψ hα hHyp.smoothNbhd hHyp.sol
      hHyp.memF
  have hL12 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.L12 F) (-(3 * Work.Elliptic.Fstar F z / z)) z :=
    HasDerivAt_L12_of_Fstar_facts F hFstar_sm hFstar_int
  obtain ⟨hG_sm, hG_ode⟩ :=
    Work.FTS.EllipticEst.Cert.Gsing_smooth_ode_of_facts α F hα hFstar_sm hFstar_int hL12
  set G : ℝ → ℝ := Work.Elliptic.Gsing α F with hG_def
  intro z θ hz hθ0 hθ1
  have hcos : Real.cos θ ≠ 0 := by
    have hp : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩
    exact ne_of_gt hp
  -- `Ψ` is `C²` at the point, by smoothness on a neighbourhood of the closed quadrant
  have hΨc2 : ContDiffAt ℝ 2 (Function.uncurry Ψ) (z, θ) :=
    contDiffAt_two_of_smoothNbhd hHyp.smoothNbhd (by linarith) (by linarith)
      (by linarith [hθ1, Real.pi_pos])
  have hΨslice : ContDiffAt ℝ 2 (fun z' => Ψ z' θ) z :=
    Work.Elliptic.contDiffAt_uncurry_slice_fst Ψ z θ hΨc2
  have hΨd : DifferentiableAt ℝ (fun z' => Ψ z' θ) z :=
    ContDiffAt.differentiableAt hΨslice (by norm_num)
  have hΨd2 : DifferentiableAt ℝ (fun z' => Work.Spaces.pz Ψ z' θ) z := by
    have h := ContDiffAt.derivWithin hΨslice (m := 1) (by norm_num)
    simpa only [Work.Spaces.pz] using h.differentiableAt (by norm_num)
  -- the facts about `G`
  have hGc2 : ContDiffAt ℝ 2 G z := by
    rw [hG_def]
    exact ContDiffOn.contDiffAt (hG_sm 2) (isOpen_Ioi.mem_nhds hz)
  have hGd : DifferentiableAt ℝ G z :=
    DifferentiableOn.differentiableAt ((hG_sm 1).differentiableOn (by norm_num))
      (isOpen_Ioi.mem_nhds hz)
  have hGd2 : DifferentiableAt ℝ (fun z' => deriv G z') z := by
    have h2 := ContDiffAt.derivWithin hGc2 (m := 1) (by norm_num)
    exact h2.differentiableAt (by norm_num)
  -- eventual differentiability, used for the product rule along the slice
  have hevΨ : ∀ᶠ z' in 𝓝 z, DifferentiableAt ℝ (fun z'' => Ψ z'' θ) z' :=
    eventually_differentiableAt_slice_fst hHyp.smoothNbhd (by linarith)
      ⟨by linarith, by linarith [hθ1, Real.pi_pos]⟩
  have hevG : ∀ᶠ z' in 𝓝 z, DifferentiableAt ℝ G z' := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact DifferentiableOn.differentiableAt ((hG_sm 1).differentiableOn (by norm_num))
      (isOpen_Ioi.mem_nhds hz')
  have hev_raw : (fun z' => deriv (fun z'' => Ψ z'' θ + G z'' * Real.sin (2 * θ)) z')
      =ᶠ[𝓝 z]
      (fun z' => deriv (fun z'' => Ψ z'' θ) z'
        + deriv (fun z'' => G z'' * Real.sin (2 * θ)) z') :=
    eventually_deriv_slice_add_radial_sin2 hevΨ hevG
  have hev : (fun z' => deriv (fun z'' => Ψ z'' θ + G z'' * Real.sin (2 * θ)) z')
      =ᶠ[𝓝 z]
      (fun z' => deriv (fun z'' => Ψ z'' θ) z' + deriv G z' * Real.sin (2 * θ)) := by
    filter_upwards [hev_raw] with z' hz'
    rw [hz', deriv_mul_const_field (u := G) (x := z') (Real.sin (2 * θ))]
  -- the differentiability facts required by `alphaDzEllResid_eq`
  have hΦpz : ∀ z' : ℝ, Work.Spaces.pz (fun z θ => G z * Real.sin (2 * θ)) z' θ
      = deriv G z' * Real.sin (2 * θ) := by
    intro z'
    simp only [Work.Spaces.pz]
    exact deriv_mul_const_field (u := G) (x := z') (Real.sin (2 * θ))
  have hΦd2 : DifferentiableAt ℝ
      (fun z' => Work.Spaces.pz (fun z θ => G z * Real.sin (2 * θ)) z' θ) z := by
    simp only [hΦpz]
    exact hGd2.mul_const _
  have hdP : DifferentiableAt ℝ (fun z' => Ψ z' θ + G z' * Real.sin (2 * θ)) z :=
    hΨd.add (hGd.mul_const _)
  have hdP2 : DifferentiableAt ℝ
      (fun z' => Work.Spaces.pz (fun z θ => Ψ z θ + G z * Real.sin (2 * θ)) z' θ) z := by
    have hR : DifferentiableAt ℝ
        (fun z' => deriv (fun z'' => Ψ z'' θ) z' + deriv G z' * Real.sin (2 * θ)) z :=
      hΨd2.add (hGd2.mul_const _)
    have hgoal : DifferentiableAt ℝ
        (fun z' => deriv (fun z'' => Ψ z'' θ + G z'' * Real.sin (2 * θ)) z') z :=
      DifferentiableAt.congr_of_eventuallyEq hR hev
    simpa only [Work.Spaces.pz] using hgoal
  -- the two splittings of `D_z` and `D_z²` over the sum
  have hDzΦ : Work.Spaces.Dz (fun z θ => G z * Real.sin (2 * θ)) z θ
      = Real.sin (2 * θ) * Work.Spaces.Dz (fun z θ => G z) z θ := by
    simp only [Work.Spaces.Dz, Work.Spaces.pz]
    rw [deriv_mul_const_field (u := G) (x := z) (Real.sin (2 * θ))]
    ring
  have hDz2Φ : Work.Spaces.DzIter 2 (fun z θ => G z * Real.sin (2 * θ)) z θ
      = Real.sin (2 * θ) * Work.Spaces.DzIter 2 (fun z θ => G z) z θ := by
    have hr := Work.FTS.EllipticEst.DzIter_mul_of_radial 2 G (fun θ => Real.sin (2 * θ)) z θ
    have hrad : ∀ j : ℕ, Work.Spaces.DzIter j (fun z θ => G z) z θ
        = Work.FTS.EllipticEst.rDzIter j G z := by
      intro j
      have hfun : ∀ j : ℕ, Work.Spaces.DzIter j (fun z θ => G z)
          = fun z θ => Work.FTS.EllipticEst.rDzIter j G z := by
        intro j
        induction j with
        | zero => rfl
        | succ n ih =>
          rw [Work.Spaces.DzIter_succ, ih, Work.FTS.EllipticEst.rDzIter_succ]
          funext a b
          simp only [Work.Spaces.Dz, Work.Spaces.pz, Work.FTS.EllipticEst.rDz]
      exact congrFun (congrFun (hfun j) z) θ
    rw [hr, hrad 2]
    ring
  have hDz_split : Work.Spaces.Dz (fun z θ => Ψ z θ + G z * Real.sin (2 * θ)) z θ
      = Work.Spaces.Dz Ψ z θ + Real.sin (2 * θ) * Work.Spaces.Dz (fun z θ => G z) z θ := by
    rw [Dz_add_of_differentiableAt (f := Ψ) (g := fun z θ => G z * Real.sin (2 * θ))
      (z := z) (θ := θ) hΨd (hGd.mul_const _), hDzΦ]
  have hDz2_split : Work.Spaces.DzIter 2 (fun z θ => Ψ z θ + G z * Real.sin (2 * θ)) z θ
      = Work.Spaces.DzIter 2 Ψ z θ
        + Real.sin (2 * θ) * Work.Spaces.DzIter 2 (fun z θ => G z) z θ := by
    rw [DzIter_two_add_of_deriv_eventuallyEq (f := Ψ)
      (g := fun z θ => G z * Real.sin (2 * θ)) (z := z) (θ := θ) hΨd2 hΦd2 hev_raw, hDz2Φ]
  -- the splitting of `L₀`
  have hLzero_split : Work.Elliptic.Lzero (fun z θ => Ψ z θ + G z * Real.sin (2 * θ)) z θ
      = Work.Elliptic.Lzero Ψ z θ := by
    have h := Work.Elliptic.Lzero_add Ψ (fun z θ => G z * Real.sin (2 * θ)) z θ hcos hΨc2
      (contDiffAt_two_uncurry_radial_sin2 (G := G) hGc2)
    rw [h, Work.Elliptic.Lzero_sin_two_mul G z θ hcos, add_zero]
  -- assemble with the algebraic identity `(☆)` of `alphaDzW_Hk_le`
  have hcore := alphaDzEllResid_eq α F Ψ hα hz hcos
    (hHyp.sol.1 z hz θ hθ0 hθ1) hΨc2 hGc2 (hG_ode z hz)
    (hL12 z hz) hΨd hΨd2 hdP hdP2 hLzero_split hDz_split hDz2_split hGd hGd2
  rw [← hcore, ← mul_assoc, one_div,
    inv_mul_cancel₀ (by linarith : (5 : ℝ) + α ≠ 0), one_mul]

/-! ## The first link: `α D_z W` as a multiple of the right-hand side of (☆)

The identity `alphaDzEllResid_eq` is a pointwise statement on the open quadrant; because the
`ℋ^k`-norm only sees the quadrant up to a null set, it can be transported to a statement about
`HkSq` (`HkSq_congr_open`), and the constant factor taken out of the norm
(`HkNorm_const_mul`).  This reduces the estimate to the sub-additivity chain. -/

/-- `HkSq` is homogeneous of degree two: `HkSq α k (β·f) = β² HkSq α k f`. -/
theorem HkSq_const_mul (α : ℝ) (k : ℕ) (β : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α k (fun z θ => β * f z θ) = β ^ 2 * Work.Spaces.HkSq α k f := by
  simp only [Work.Spaces.HkSq]
  have hslice : ∀ z : ℝ,
      (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (fun z θ => β * f z θ) z θ)
        = β ^ 2 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
    intro z
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      (fun θ _ => Work.FTS.LocData.HkIntegrand_const_mul α k β f z θ)
  have hout : (∫ z in Work.Spaces.Iz,
        ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (fun z θ => β * f z θ) z θ)
      = ∫ z in Work.Spaces.Iz,
          β ^ 2 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ :=
    MeasureTheory.setIntegral_congr_fun (s := Work.Spaces.Iz) measurableSet_Ici
      (fun z _ => hslice z)
  rw [hout, MeasureTheory.integral_const_mul]

/-- **The identity (☆) at the level of `HkNorm`:** `α D_z W` has the same norm as the
right-hand side of (☆), divided by `5 + α`. -/
theorem HkNorm_alphaDzEllResid_eq (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hid : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      α * Work.Spaces.Dz (Work.Elliptic.EllResid α F Ψ) z θ
        = (1 / (5 + α)) *
            (α ^ 2 * Work.Spaces.DzIter 2
                (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
              + 5 * α * Work.Spaces.Dz
                (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
              - α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
              + (3 * α / 4) * (Real.sin (2 * θ) * Work.Elliptic.Fstar F z))) :
    Work.Spaces.HkNorm α k (fun z θ => α * Work.Spaces.Dz (Work.Elliptic.EllResid α F Ψ) z θ)
      = (1 / (5 + α)) * Work.Spaces.HkNorm α k (fun z θ =>
          α ^ 2 * Work.Spaces.DzIter 2
              (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
            + 5 * α * Work.Spaces.Dz
              (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
            - α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
            + (3 * α / 4) * (Real.sin (2 * θ) * Work.Elliptic.Fstar F z)) := by
  have hsq : Work.Spaces.HkSq α k
        (fun z θ => α * Work.Spaces.Dz (Work.Elliptic.EllResid α F Ψ) z θ)
      = Work.Spaces.HkSq α k (fun z θ => (1 / (5 + α)) *
          (α ^ 2 * Work.Spaces.DzIter 2
              (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
            + 5 * α * Work.Spaces.Dz
              (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
            - α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
            + (3 * α / 4) * (Real.sin (2 * θ) * Work.Elliptic.Fstar F z))) :=
    Work.FTS.EllipticEst.HkSq_congr_open α k hid
  have hβ : 0 < 1 / (5 + α) := by positivity
  rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, hsq, HkSq_const_mul, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq_eq_abs, abs_of_pos hβ]


/-- **The sub-additivity chain of the first link.**  For four functions `u₁,…,u₄` smooth and
honest on the open quadrant, the `ℋ^k`-norm of `c₁u₁ + c₂u₂ + c₃u₃ + c₄u₄` is bounded by
`2√2` times the sum of the (`|cᵢ|`-weighted) norms.

This isolates the purely norm-theoretic step of the first link of the assembly: the
sub-additivity `hadd` (i.e. `Work.FTS.EllipticEst.HkNorm_add_le`), homogeneity
(`HkNorm_const_mul`) and `sqrt`-arithmetic.  In the assembly `u₁ = D_z²Ψ̂`, `u₂ = D_zΨ̂`,
`u₃ = z²∂_zzΨ`, `u₄ = sin 2θ · F_*` and `c₁ = α²`, `c₂ = 5α`, `c₃ = -α²`, `c₄ = 3α/4`. -/
theorem HkNorm_sum4_le (α : ℝ) (k : ℕ) (u1 u2 u3 u4 : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hsm1 : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hsm2 : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hsm3 : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u3) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hsm4 : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u4) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hm1 : Work.Spaces.HkMem α k (fun z θ => α ^ 2 * u1 z θ))
    (hm2 : Work.Spaces.HkMem α k (fun z θ => 5 * α * u2 z θ))
    (hm3 : Work.Spaces.HkMem α k (fun z θ => -(α ^ 2) * u3 z θ))
    (hm4 : Work.Spaces.HkMem α k (fun z θ => (3 * α / 4) * u4 z θ))
    (hm12 : Work.Spaces.HkMem α k (fun z θ => α ^ 2 * u1 z θ + 5 * α * u2 z θ))
    (hm34 : Work.Spaces.HkMem α k (fun z θ => -(α ^ 2) * u3 z θ + (3 * α / 4) * u4 z θ))
    (hadd : ∀ {f g : ℝ → ℝ → ℝ},
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) →
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) →
      Work.Spaces.HkMem α k f → Work.Spaces.HkMem α k g →
      Work.Spaces.HkNorm α k (fun z θ => f z θ + g z θ)
        ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k f + Work.Spaces.HkNorm α k g))
    (hcm : ∀ (c : ℝ) (f : ℝ → ℝ → ℝ),
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) →
      Work.Spaces.HkNorm α k (fun z θ => c * f z θ) = |c| * Work.Spaces.HkNorm α k f) :
    Work.Spaces.HkNorm α k (fun z θ =>
        α ^ 2 * u1 z θ + 5 * α * u2 z θ + (-(α ^ 2)) * u3 z θ + (3 * α / 4) * u4 z θ)
      ≤ 2 * (α ^ 2 * Work.Spaces.HkNorm α k u1
          + 5 * α * Work.Spaces.HkNorm α k u2
          + α ^ 2 * Work.Spaces.HkNorm α k u3
          + (3 * α / 4) * Work.Spaces.HkNorm α k u4) := by
  have hαnn : (0 : ℝ) ≤ α := le_of_lt hα
  -- smoothness of the scaled pieces and of the partial sums
  have hsmA : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (fun z θ => α ^ 2 * u1 z θ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    intro n
    have h : (fun z θ => α ^ 2 * u1 z θ) = fun z θ => (α ^ 2) • u1 z θ := rfl
    rw [h]
    exact (hsm1 n).const_smul (α ^ 2)
  have hsmB : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (fun z θ => 5 * α * u2 z θ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    intro n
    have h : (fun z θ => 5 * α * u2 z θ) = fun z θ => (5 * α) • u2 z θ := rfl
    rw [h]
    exact (hsm2 n).const_smul (5 * α)
  have hsmC : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (fun z θ => (-(α ^ 2)) * u3 z θ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    intro n
    have h : (fun z θ => (-(α ^ 2)) * u3 z θ) = fun z θ => (-(α ^ 2)) • u3 z θ := rfl
    rw [h]
    exact (hsm3 n).const_smul (-(α ^ 2))
  have hsmD : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (fun z θ => (3 * α / 4) * u4 z θ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    intro n
    have h : (fun z θ => (3 * α / 4) * u4 z θ) = fun z θ => (3 * α / 4) • u4 z θ := rfl
    rw [h]
    exact (hsm4 n).const_smul (3 * α / 4)
  have hsmAB : ∀ n : ℕ, ContDiffOn ℝ n
      (Function.uncurry (fun z θ => α ^ 2 * u1 z θ + 5 * α * u2 z θ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := fun n => (hsmA n).add (hsmB n)
  have hsmCD : ∀ n : ℕ, ContDiffOn ℝ n
      (Function.uncurry (fun z θ => (-(α ^ 2)) * u3 z θ + (3 * α / 4) * u4 z θ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := fun n => (hsmC n).add (hsmD n)
  have h1 := hadd hsmAB hsmCD hm12 hm34
  have h2 := hadd hsmA hsmB hm1 hm2
  have h3 := hadd hsmC hsmD hm3 hm4
  -- homogeneity of the four scaled pieces
  have hNA : Work.Spaces.HkNorm α k (fun z θ => α ^ 2 * u1 z θ)
      = α ^ 2 * Work.Spaces.HkNorm α k u1 := by
    rw [hcm (α ^ 2) u1 hsm1, abs_of_nonneg (by positivity)]
  have hNB : Work.Spaces.HkNorm α k (fun z θ => 5 * α * u2 z θ)
      = 5 * α * Work.Spaces.HkNorm α k u2 := by
    rw [hcm (5 * α) u2 hsm2, abs_of_nonneg (by linarith)]
  have hNC : Work.Spaces.HkNorm α k (fun z θ => (-(α ^ 2)) * u3 z θ)
      = α ^ 2 * Work.Spaces.HkNorm α k u3 := by
    rw [hcm (-(α ^ 2)) u3 hsm3, abs_of_nonpos (by nlinarith [hαnn]), neg_neg]
  have hND : Work.Spaces.HkNorm α k (fun z θ => (3 * α / 4) * u4 z θ)
      = (3 * α / 4) * Work.Spaces.HkNorm α k u4 := by
    rw [hcm (3 * α / 4) u4 hsm4, abs_of_nonneg (by linarith)]
  have hfun : (fun z θ => α ^ 2 * u1 z θ + 5 * α * u2 z θ + (-(α ^ 2)) * u3 z θ
        + (3 * α / 4) * u4 z θ)
      = fun z θ => (α ^ 2 * u1 z θ + 5 * α * u2 z θ)
          + ((-(α ^ 2)) * u3 z θ + (3 * α / 4) * u4 z θ) := by
    funext z θ; ring_nf
  rw [hfun]
  have h2' : Work.Spaces.HkNorm α k (fun z θ => α ^ 2 * u1 z θ + 5 * α * u2 z θ)
      ≤ Real.sqrt 2 * (α ^ 2 * Work.Spaces.HkNorm α k u1
          + 5 * α * Work.Spaces.HkNorm α k u2) := by
    rw [← hNA, ← hNB]; exact h2
  have h3' : Work.Spaces.HkNorm α k (fun z θ => (-(α ^ 2)) * u3 z θ + (3 * α / 4) * u4 z θ)
      ≤ Real.sqrt 2 * (α ^ 2 * Work.Spaces.HkNorm α k u3
          + (3 * α / 4) * Work.Spaces.HkNorm α k u4) := by
    rw [← hNC, ← hND]; exact h3
  have hs2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hN1 := Work.Spaces.HkNorm_nonneg α k u1
  have hN2 := Work.Spaces.HkNorm_nonneg α k u2
  have hN3 := Work.Spaces.HkNorm_nonneg α k u3
  have hN4 := Work.Spaces.HkNorm_nonneg α k u4
  calc Work.Spaces.HkNorm α k (fun z θ => (α ^ 2 * u1 z θ + 5 * α * u2 z θ)
          + ((-(α ^ 2)) * u3 z θ + (3 * α / 4) * u4 z θ))
      ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k (fun z θ => α ^ 2 * u1 z θ + 5 * α * u2 z θ)
          + Work.Spaces.HkNorm α k (fun z θ => (-(α ^ 2)) * u3 z θ + (3 * α / 4) * u4 z θ)) :=
        h1
    _ ≤ Real.sqrt 2 * (Real.sqrt 2 * (α ^ 2 * Work.Spaces.HkNorm α k u1
            + 5 * α * Work.Spaces.HkNorm α k u2)
          + Real.sqrt 2 * (α ^ 2 * Work.Spaces.HkNorm α k u3
            + (3 * α / 4) * Work.Spaces.HkNorm α k u4)) := by
        nlinarith [hs2, h2', h3']
    _ = 2 * (α ^ 2 * Work.Spaces.HkNorm α k u1
          + 5 * α * Work.Spaces.HkNorm α k u2
          + α ^ 2 * Work.Spaces.HkNorm α k u3
          + (3 * α / 4) * Work.Spaces.HkNorm α k u4) := by
        ring_nf
        rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
        ring

/-- **The first link of the assembly, assembled.**  Combining the identity (☆) at the level of
`HkNorm` with the sub-additivity chain:

`α |D_z W| ≤ (1 + α)⁻¹ · 2(α²|D_z²Ψ̂| + 5α|D_zΨ̂| + α²|z²∂_zzΨ| + (3α/4)|sin 2θ F_*|)`. -/
theorem alphaDzW_Hk_le_first_link (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hid : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      α * Work.Spaces.Dz (Work.Elliptic.EllResid α F Ψ) z θ
        = (1 / (5 + α)) *
            (α ^ 2 * Work.Spaces.DzIter 2
                (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
              + 5 * α * Work.Spaces.Dz
                (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
              - α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
              + (3 * α / 4) * (Real.sin (2 * θ) * Work.Elliptic.Fstar F z)))
    (hsm1 : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.DzIter 2
        (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ))))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hsm2 : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dz
        (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ))))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hsm3 : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (fun z θ =>
        z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hsm4 : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (fun z θ =>
        Real.sin (2 * θ) * Work.Elliptic.Fstar F z)) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hm1 : Work.Spaces.HkMem α k (fun z θ => α ^ 2 * Work.Spaces.DzIter 2
        (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ))
    (hm2 : Work.Spaces.HkMem α k (fun z θ => 5 * α * Work.Spaces.Dz
        (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ))
    (hm3 : Work.Spaces.HkMem α k (fun z θ => -(α ^ 2) * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)))
    (hm4 : Work.Spaces.HkMem α k (fun z θ =>
        (3 * α / 4) * (Real.sin (2 * θ) * Work.Elliptic.Fstar F z)))
    (hm12 : Work.Spaces.HkMem α k (fun z θ =>
        α ^ 2 * Work.Spaces.DzIter 2
            (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
          + 5 * α * Work.Spaces.Dz
            (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ))
    (hm34 : Work.Spaces.HkMem α k (fun z θ =>
        -(α ^ 2) * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + (3 * α / 4) * (Real.sin (2 * θ) * Work.Elliptic.Fstar F z)))
    (hadd : ∀ {f g : ℝ → ℝ → ℝ},
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) →
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) →
      Work.Spaces.HkMem α k f → Work.Spaces.HkMem α k g →
      Work.Spaces.HkNorm α k (fun z θ => f z θ + g z θ)
        ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k f + Work.Spaces.HkNorm α k g))
    (hcm : ∀ (c : ℝ) (f : ℝ → ℝ → ℝ),
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) →
      Work.Spaces.HkNorm α k (fun z θ => c * f z θ) = |c| * Work.Spaces.HkNorm α k f) :
    Work.Spaces.HkNorm α k (fun z θ => α * Work.Spaces.Dz (Work.Elliptic.EllResid α F Ψ) z θ)
      ≤ (1 / (5 + α)) * 2 *
          (α ^ 2 * Work.Spaces.HkNorm α k (Work.Spaces.DzIter 2
              (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)))
            + 5 * α * Work.Spaces.HkNorm α k (Work.Spaces.Dz
              (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)))
            + α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
            + (3 * α / 4) * Work.Spaces.HkNorm α k
                (fun z θ => Real.sin (2 * θ) * Work.Elliptic.Fstar F z)) := by
  have h1 := Work.FTS.EllipticEst.HkNorm_alphaDzEllResid_eq α k F Ψ hα hid
  have h2 := Work.FTS.EllipticEst.HkNorm_sum4_le α k
    (Work.Spaces.DzIter 2 (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)))
    (Work.Spaces.Dz (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)))
    (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
    (fun z θ => Real.sin (2 * θ) * Work.Elliptic.Fstar F z)
    hα hsm1 hsm2 hsm3 hsm4 hm1 hm2 hm3 hm4 hm12 hm34 hadd hcm
  have hfun : (fun z θ => α ^ 2 * Work.Spaces.DzIter 2
          (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
        + 5 * α * Work.Spaces.Dz
          (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
        - α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        + (3 * α / 4) * (Real.sin (2 * θ) * Work.Elliptic.Fstar F z))
      = fun z θ => α ^ 2 * Work.Spaces.DzIter 2
            (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
          + 5 * α * Work.Spaces.Dz
            (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
          + (-(α ^ 2)) * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + (3 * α / 4) * (Real.sin (2 * θ) * Work.Elliptic.Fstar F z) := by
    funext z θ; ring
  have hcongr : Work.Spaces.HkNorm α k (fun z θ => α ^ 2 * Work.Spaces.DzIter 2
          (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
        + 5 * α * Work.Spaces.Dz
          (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
        - α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        + (3 * α / 4) * (Real.sin (2 * θ) * Work.Elliptic.Fstar F z))
      = Work.Spaces.HkNorm α k (fun z θ => α ^ 2 * Work.Spaces.DzIter 2
            (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
          + 5 * α * Work.Spaces.Dz
            (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
          + (-(α ^ 2)) * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + (3 * α / 4) * (Real.sin (2 * θ) * Work.Elliptic.Fstar F z)) := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm,
      Work.FTS.EllipticEst.HkSq_congr_open α k (fun z θ _ _ _ => congrFun (congrFun hfun z) θ)]
  have h2' : Work.Spaces.HkNorm α k (fun z θ => α ^ 2 * Work.Spaces.DzIter 2
          (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
        + 5 * α * Work.Spaces.Dz
          (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
        + (-(α ^ 2)) * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        + (3 * α / 4) * (Real.sin (2 * θ) * Work.Elliptic.Fstar F z))
      ≤ 2 * (α ^ 2 * Work.Spaces.HkNorm α k (Work.Spaces.DzIter 2
              (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)))
            + 5 * α * Work.Spaces.HkNorm α k (Work.Spaces.Dz
              (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)))
            + α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
            + (3 * α / 4) * Work.Spaces.HkNorm α k
                (fun z θ => Real.sin (2 * θ) * Work.Elliptic.Fstar F z)) := h2
  calc Work.Spaces.HkNorm α k (fun z θ => α * Work.Spaces.Dz (Work.Elliptic.EllResid α F Ψ) z θ)
      = (1 / (5 + α)) * Work.Spaces.HkNorm α k (fun z θ => α ^ 2 * Work.Spaces.DzIter 2
            (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
          + 5 * α * Work.Spaces.Dz
            (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
          - α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + (3 * α / 4) * (Real.sin (2 * θ) * Work.Elliptic.Fstar F z)) := h1
    _ = (1 / (5 + α)) * Work.Spaces.HkNorm α k (fun z θ => α ^ 2 * Work.Spaces.DzIter 2
            (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
          + 5 * α * Work.Spaces.Dz
            (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
          + (-(α ^ 2)) * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + (3 * α / 4) * (Real.sin (2 * θ) * Work.Elliptic.Fstar F z)) := by rw [hcongr]
    _ ≤ (1 / (5 + α)) * (2 * (α ^ 2 * Work.Spaces.HkNorm α k (Work.Spaces.DzIter 2
              (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)))
            + 5 * α * Work.Spaces.HkNorm α k (Work.Spaces.Dz
              (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)))
            + α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
            + (3 * α / 4) * Work.Spaces.HkNorm α k
                (fun z θ => Real.sin (2 * θ) * Work.Elliptic.Fstar F z))) :=
        mul_le_mul_of_nonneg_left h2' (by positivity)
    _ = (1 / (5 + α)) * 2 *
          (α ^ 2 * Work.Spaces.HkNorm α k (Work.Spaces.DzIter 2
              (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)))
            + 5 * α * Work.Spaces.HkNorm α k (Work.Spaces.Dz
              (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)))
            + α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
            + (3 * α / 4) * Work.Spaces.HkNorm α k
                (fun z θ => Real.sin (2 * θ) * Work.Elliptic.Fstar F z)) := by ring


/-! ## The straightened solution `Ψ + Gsing α F · sin 2θ` and the transfer identities

Write `Ψ̂ := fun z θ => Ψ z θ + Gsing α F z * Real.sin (2 * θ)` (the `Straight` of
Theorem `RemovingL12`) and `W := EllResid α F Ψ`.  Since `EllResid α F Ψ = Ψ + Gstar α F · sin 2θ`
and `Gsing = Gstar + Gbar`, one has the pointwise identity

  `W = Ψ̂ - Gbar α F · sin 2θ`,

and the three identities below record the effect of this on the derivatives used by the
estimate: the `D_z`-transfer (`α D_zΨ̂ = α D_zΨ - 5 Ḡ sin 2θ`), the `∂_θθ`-transfer
(`∂_θθW = ∂_θθΨ̂ + 4 Ḡ sin 2θ`) and the `z²∂_zz`-transfer
(`α² z²∂_zzΨ̂ = α²z²∂_zzΨ + (15/4) sin 2θ · F_* + 5(5+α) sin 2θ · Ḡ`). -/

/-- `∂_θ(sin 2θ) = 2 cos 2θ`. -/
theorem deriv_sin_two (θ : ℝ) : deriv (fun θ' => Real.sin (2 * θ')) θ = 2 * Real.cos (2 * θ) := by
  have h : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (Real.cos (2 * θ) * 2) θ :=
    (Real.hasDerivAt_sin (2 * θ)).comp θ (by simpa using (hasDerivAt_id θ).const_mul (2 : ℝ))
  rw [h.deriv]; ring

/-- `∂_θ(cos 2θ) = -2 sin 2θ`. -/
theorem deriv_cos_two (θ : ℝ) : deriv (fun θ' => Real.cos (2 * θ')) θ = -2 * Real.sin (2 * θ) := by
  have h : HasDerivAt (fun θ' : ℝ => Real.cos (2 * θ')) (-(Real.sin (2 * θ)) * 2) θ :=
    (Real.hasDerivAt_cos (2 * θ)).comp θ (by simpa using (hasDerivAt_id θ).const_mul (2 : ℝ))
  rw [h.deriv]; ring

/-- `∂_θθ(sin 2θ) = -4 sin 2θ`. -/
theorem deriv_deriv_sin_two (θ : ℝ) :
    deriv (fun θ' => deriv (fun θ'' => Real.sin (2 * θ'')) θ') θ = -4 * Real.sin (2 * θ) := by
  have hfun : (fun θ' => deriv (fun θ'' => Real.sin (2 * θ'')) θ')
      = fun θ' => 2 * Real.cos (2 * θ') := by
    funext θ'; exact deriv_sin_two θ'
  rw [hfun]
  have h : HasDerivAt (fun θ' : ℝ => 2 * Real.cos (2 * θ')) (2 * (-(Real.sin (2 * θ)) * 2)) θ :=
    ((Real.hasDerivAt_cos (2 * θ)).comp θ
      (by simpa using (hasDerivAt_id θ).const_mul (2 : ℝ))).const_mul 2
  rw [h.deriv]; ring

/-- **`∂_θθ` of a radial multiple of `sin 2θ`**: `∂_θθ(g(z) sin 2θ) = -4 g(z) sin 2θ`. -/
theorem pthIter2_radial_sin_two (g : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter 2 (fun z θ => g z * Real.sin (2 * θ)) z θ
      = -(4 * (g z * Real.sin (2 * θ))) := by
  have hbase : Work.Spaces.pthIter 2 (fun z θ => g z * Real.sin (2 * θ)) z θ
      = deriv (fun θ' => deriv (fun θ'' => g z * Real.sin (2 * θ'')) θ') θ := rfl
  rw [hbase]
  have h1 : (fun θ' => deriv (fun θ'' => g z * Real.sin (2 * θ'')) θ')
      = fun θ' => g z * (2 * Real.cos (2 * θ')) := by
    funext θ'
    rw [deriv_const_mul (g z)
      (by fun_prop : DifferentiableAt ℝ (fun θ'' : ℝ => Real.sin (2 * θ'')) θ')]
    rw [deriv_sin_two]
  rw [h1]
  have h2 : deriv (fun θ' : ℝ => g z * (2 * Real.cos (2 * θ'))) θ
      = g z * (2 * (-(Real.sin (2 * θ)) * 2)) := by
    rw [deriv_const_mul (g z)
      (by fun_prop : DifferentiableAt ℝ (fun θ' : ℝ => 2 * Real.cos (2 * θ')) θ)]
    congr 1
    exact ((Real.hasDerivAt_cos (2 * θ)).comp θ
      (by simpa using (hasDerivAt_id θ).const_mul (2 : ℝ))).const_mul 2 |>.deriv
  rw [h2]; ring

/-- **`∂_zz` of a radial multiple**: `∂_zz(g(z) u(θ)) = g''(z) u(θ)`. -/
theorem pzIter2_radial_mul (g u : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pzIter 2 (fun z θ => g z * u θ) z θ
      = deriv (fun z' => deriv g z') z * u θ := by
  have hbase : Work.Spaces.pzIter 2 (fun z θ => g z * u θ) z θ
      = deriv (fun z' => deriv (fun z'' => g z'' * u θ) z') z := rfl
  rw [hbase]
  rw [show (fun z' => deriv (fun z'' => g z'' * u θ) z') = fun z' => deriv g z' * u θ from
    funext fun z' => deriv_mul_radial g (u θ) z']
  exact deriv_mul_radial (fun z' => deriv g z') (u θ) z

/-! ## Differentiability of the slices of a `SmoothOpen` function -/

/-- The `θ`-slice of a function of class `C^n` on the open quadrant is `C^n` on `(0,π/2)`. -/
theorem contDiffOn_slice_theta_nat {f : ℝ → ℝ → ℝ} {n : ℕ}
    (hf : ContDiffOn ℝ n (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    {z : ℝ} (hz : 0 < z) :
    ContDiffOn ℝ n (fun θ => f z θ) (Set.Ioo 0 (π / 2)) :=
  (hf.comp ((contDiffOn_const (c := z)).prodMk
      (contDiffOn_id : ContDiffOn ℝ n (fun θ : ℝ => θ) (Set.Ioo 0 (π / 2))))
    (fun θ hθ => ⟨hz, hθ⟩)).congr (fun θ _ => rfl)

/-- The `z`-slice of a function of class `C^n` on the open quadrant is `C^n` on `(0,∞)`. -/
theorem contDiffOn_slice_z_nat {f : ℝ → ℝ → ℝ} {n : ℕ}
    (hf : ContDiffOn ℝ n (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ContDiffOn ℝ n (fun z => f z θ) (Set.Ioi 0) :=
  (hf.comp ((contDiffOn_id : ContDiffOn ℝ n (fun z : ℝ => z) (Set.Ioi 0)).prodMk
      (contDiffOn_const (c := θ))) (fun z hz => ⟨hz, hθ⟩)).congr (fun z _ => rfl)

/-- The `θ`-slice of a `SmoothOpen` function is differentiable at every interior angle. -/
theorem SmoothOpen.differentiableAt_slice_theta {f : ℝ → ℝ → ℝ} (hf : SmoothOpen f)
    {z θ : ℝ} (hz : 0 < z) (hθ1 : 0 < θ) (hθ2 : θ < π / 2) :
    DifferentiableAt ℝ (fun θ' : ℝ => f z θ') θ :=
  ((contDiffOn_slice_theta_nat (hf.forall 2) hz).differentiableOn
    (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).differentiableAt
      (isOpen_Ioo.mem_nhds ⟨hθ1, hθ2⟩)

/-- The `z`-slice of a `SmoothOpen` function is differentiable at every interior radius. -/
theorem SmoothOpen.differentiableAt_slice_z {f : ℝ → ℝ → ℝ} (hf : SmoothOpen f)
    {z θ : ℝ} (hz : 0 < z) (hθ1 : 0 < θ) (hθ2 : θ < π / 2) :
    DifferentiableAt ℝ (fun z' : ℝ => f z' θ) z :=
  ((contDiffOn_slice_z_nat (hf.forall 2) ⟨hθ1, hθ2⟩).differentiableOn
    (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).differentiableAt (isOpen_Ioi.mem_nhds hz)

/-- `SmoothOpen` is closed under addition. -/
theorem SmoothOpen.add {f g : ℝ → ℝ → ℝ} (hf : SmoothOpen f) (hg : SmoothOpen g) :
    SmoothOpen (fun z θ => f z θ + g z θ) := by
  refine smoothOpen_of_forall fun n => ?_
  have h1 : Function.uncurry (fun z θ => f z θ + g z θ)
      = (Function.uncurry f) + (Function.uncurry g) := by
    funext p; rfl
  rw [h1]
  exact (hf.forall n).add (hg.forall n)

/-! ## Additivity of the slice derivatives on `SmoothOpen` data -/

/-- `∂_θθ` is additive on `SmoothOpen` data. -/
theorem pthIter2_add {f g : ℝ → ℝ → ℝ} (hf : SmoothOpen f) (hg : SmoothOpen g)
    {z θ : ℝ} (hz : 0 < z) (hθ1 : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Spaces.pthIter 2 (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.pthIter 2 f z θ + Work.Spaces.pthIter 2 g z θ := by
  have hnb : Set.Ioo (0 : ℝ) (π / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds ⟨hθ1, hθ2⟩
  have hfun : ∀ θ' ∈ Set.Ioo (0 : ℝ) (π / 2),
      Work.Spaces.pth (fun z θ => f z θ + g z θ) z θ'
        = Work.Spaces.pth f z θ' + Work.Spaces.pth g z θ' := by
    intro θ' hθ'
    rw [Work.Spaces.pth, Work.Spaces.pth, Work.Spaces.pth]
    have heq : (fun θ'' : ℝ => f z θ'' + g z θ'')
        =ᶠ[𝓝 θ'] ((fun θ'' : ℝ => f z θ'') + fun θ'' : ℝ => g z θ'') :=
      Filter.Eventually.of_forall fun _ => rfl
    rw [Filter.EventuallyEq.deriv_eq heq, deriv_add
      (hf.differentiableAt_slice_theta hz hθ'.1 hθ'.2)
      (hg.differentiableAt_slice_theta hz hθ'.1 hθ'.2)]
  have hev : Work.Spaces.pth (fun z θ => f z θ + g z θ) z
      =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.pth f z θ' + Work.Spaces.pth g z θ') :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨_, hnb, hfun⟩
  have hbase : Work.Spaces.pthIter 2 (fun z θ => f z θ + g z θ) z θ
      = deriv (Work.Spaces.pth (fun z θ => f z θ + g z θ) z) θ := rfl
  rw [hbase, Filter.EventuallyEq.deriv_eq hev]
  have heq2 : (fun θ' : ℝ => Work.Spaces.pth f z θ' + Work.Spaces.pth g z θ')
      =ᶠ[𝓝 θ] ((Work.Spaces.pth f z) + Work.Spaces.pth g z) :=
    Filter.Eventually.of_forall fun _ => rfl
  rw [Filter.EventuallyEq.deriv_eq heq2, deriv_add
    (hf.pth.differentiableAt_slice_theta hz hθ1 hθ2)
    (hg.pth.differentiableAt_slice_theta hz hθ1 hθ2)]
  rfl

/-- `∂_θθ` is additive on `SmoothOpen` data, subtraction form. -/
theorem pthIter2_sub {f g : ℝ → ℝ → ℝ} (hf : SmoothOpen f) (hg : SmoothOpen g)
    {z θ : ℝ} (hz : 0 < z) (hθ1 : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Spaces.pthIter 2 (fun z θ => f z θ - g z θ) z θ
      = Work.Spaces.pthIter 2 f z θ - Work.Spaces.pthIter 2 g z θ := by
  have hnb : Set.Ioo (0 : ℝ) (π / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds ⟨hθ1, hθ2⟩
  have hfun : ∀ θ' ∈ Set.Ioo (0 : ℝ) (π / 2),
      Work.Spaces.pth (fun z θ => f z θ - g z θ) z θ'
        = Work.Spaces.pth f z θ' - Work.Spaces.pth g z θ' := by
    intro θ' hθ'
    rw [Work.Spaces.pth, Work.Spaces.pth, Work.Spaces.pth]
    have heq : (fun θ'' : ℝ => f z θ'' - g z θ'')
        =ᶠ[𝓝 θ'] ((fun θ'' : ℝ => f z θ'') - fun θ'' : ℝ => g z θ'') :=
      Filter.Eventually.of_forall fun _ => rfl
    rw [Filter.EventuallyEq.deriv_eq heq, deriv_sub
      (hf.differentiableAt_slice_theta hz hθ'.1 hθ'.2)
      (hg.differentiableAt_slice_theta hz hθ'.1 hθ'.2)]
  have hev : Work.Spaces.pth (fun z θ => f z θ - g z θ) z
      =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.pth f z θ' - Work.Spaces.pth g z θ') :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨_, hnb, hfun⟩
  have hbase : Work.Spaces.pthIter 2 (fun z θ => f z θ - g z θ) z θ
      = deriv (Work.Spaces.pth (fun z θ => f z θ - g z θ) z) θ := rfl
  rw [hbase, Filter.EventuallyEq.deriv_eq hev]
  have heq2 : (fun θ' : ℝ => Work.Spaces.pth f z θ' - Work.Spaces.pth g z θ')
      =ᶠ[𝓝 θ] ((Work.Spaces.pth f z) - Work.Spaces.pth g z) :=
    Filter.Eventually.of_forall fun _ => rfl
  rw [Filter.EventuallyEq.deriv_eq heq2, deriv_sub
    (hf.pth.differentiableAt_slice_theta hz hθ1 hθ2)
    (hg.pth.differentiableAt_slice_theta hz hθ1 hθ2)]
  rfl

/-- `∂_z` is additive on `SmoothOpen` data. -/
theorem pz_add {f g : ℝ → ℝ → ℝ} (hf : SmoothOpen f) (hg : SmoothOpen g)
    {z θ : ℝ} (hz : 0 < z) (hθ1 : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Spaces.pz (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.pz f z θ + Work.Spaces.pz g z θ := by
  rw [Work.Spaces.pz, Work.Spaces.pz, Work.Spaces.pz]
  have heq : (fun z' : ℝ => f z' θ + g z' θ) =ᶠ[𝓝 z] ((fun z' : ℝ => f z' θ)
      + fun z' : ℝ => g z' θ) := Filter.Eventually.of_forall fun _ => rfl
  rw [Filter.EventuallyEq.deriv_eq heq, deriv_add (hf.differentiableAt_slice_z hz hθ1 hθ2)
    (hg.differentiableAt_slice_z hz hθ1 hθ2)]

/-- `D_z` is additive on `SmoothOpen` data. -/
theorem Dz_add {f g : ℝ → ℝ → ℝ} (hf : SmoothOpen f) (hg : SmoothOpen g)
    {z θ : ℝ} (hz : 0 < z) (hθ1 : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Spaces.Dz (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.Dz f z θ + Work.Spaces.Dz g z θ := by
  rw [Work.Spaces.Dz, Work.Spaces.Dz, Work.Spaces.Dz, pz_add hf hg hz hθ1 hθ2]
  ring

/-- `∂_zz` is additive on `SmoothOpen` data. -/
theorem pzIter2_add {f g : ℝ → ℝ → ℝ} (hf : SmoothOpen f) (hg : SmoothOpen g)
    {z θ : ℝ} (hz : 0 < z) (hθ1 : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Spaces.pzIter 2 (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.pzIter 2 f z θ + Work.Spaces.pzIter 2 g z θ := by
  have hfun : ∀ z' ∈ Set.Ioi (0 : ℝ),
      Work.Spaces.pz (fun z θ => f z θ + g z θ) z' θ
        = Work.Spaces.pz f z' θ + Work.Spaces.pz g z' θ :=
    fun z' hz' => pz_add hf hg hz' hθ1 hθ2
  have hev : (fun z' : ℝ => Work.Spaces.pz (fun z θ => f z θ + g z θ) z' θ)
      =ᶠ[𝓝 z] (fun z' => Work.Spaces.pz f z' θ + Work.Spaces.pz g z' θ) :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨_, isOpen_Ioi.mem_nhds hz,
      fun z' hz' => hfun z' hz'⟩
  have hbase : Work.Spaces.pzIter 2 (fun z θ => f z θ + g z θ) z θ
      = deriv (fun z' => Work.Spaces.pz (fun z θ => f z θ + g z θ) z' θ) z := by
    rw [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero]; rfl
  rw [hbase, Filter.EventuallyEq.deriv_eq hev]
  have heq2 : (fun z' : ℝ => Work.Spaces.pz f z' θ + Work.Spaces.pz g z' θ)
      =ᶠ[𝓝 z] ((fun z' : ℝ => Work.Spaces.pz f z' θ)
        + fun z' : ℝ => Work.Spaces.pz g z' θ) :=
    Filter.Eventually.of_forall fun _ => rfl
  rw [Filter.EventuallyEq.deriv_eq heq2, deriv_add
    (hf.pz.differentiableAt_slice_z hz hθ1 hθ2)
    (hg.pz.differentiableAt_slice_z hz hθ1 hθ2)]
  rfl

/-! ## The transfer identities -/

/-- `EllResid α F Ψ = Ψ̂ - Ḡ · sin 2θ` where `Ψ̂ = Ψ + Gsing α F · sin 2θ`. -/
theorem EllResid_eq_Straight_sub (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Elliptic.EllResid α F Ψ z θ
      = (Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ))
        - Work.Elliptic.Gbar α F z * Real.sin (2 * θ) := by
  simp only [Work.Elliptic.EllResid, Work.Elliptic.Gsing, Work.Elliptic.Gstar]
  ring

/-- **Transfer 1**: `α D_z(Ψ̂) = α D_zΨ - 5 sin 2θ · Ḡ`. -/
theorem alpha_Dz_Straight_eq (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (hΨ : SmoothOpen Ψ)
    (hGs : SmoothOpen (fun z θ => Work.Elliptic.Gsing α F z * Real.sin (2 * θ)))
    {z θ : ℝ} (hz : 0 < z) (hθ1 : 0 < θ) (hθ2 : θ < π / 2)
    (hGrel : α * z * deriv (Work.Elliptic.Gsing α F) z = -5 * Work.Elliptic.Gbar α F z) :
    α * Work.Spaces.Dz (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
      = α * Work.Spaces.Dz Ψ z θ - 5 * (Real.sin (2 * θ) * Work.Elliptic.Gbar α F z) := by
  rw [Dz_add hΨ hGs hz hθ1 hθ2]
  have hrad : Work.Spaces.Dz (fun z θ => Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
      = Real.sin (2 * θ) * (z * deriv (Work.Elliptic.Gsing α F) z) := by
    rw [Dz_radial_mul]
    simp only [rDz]
    ring
  rw [hrad]
  have h2 : α * (z * deriv (Work.Elliptic.Gsing α F) z) = -5 * Work.Elliptic.Gbar α F z := by
    linarith [hGrel]
  have h3 : α * (Real.sin (2 * θ) * (z * deriv (Work.Elliptic.Gsing α F) z))
      = -5 * (Real.sin (2 * θ) * Work.Elliptic.Gbar α F z) := by
    calc α * (Real.sin (2 * θ) * (z * deriv (Work.Elliptic.Gsing α F) z))
        = Real.sin (2 * θ) * (α * (z * deriv (Work.Elliptic.Gsing α F) z)) := by ring
      _ = Real.sin (2 * θ) * (-5 * Work.Elliptic.Gbar α F z) := by rw [h2]
      _ = -5 * (Real.sin (2 * θ) * Work.Elliptic.Gbar α F z) := by ring
  have h4 : α * (Work.Spaces.Dz Ψ z θ
        + Real.sin (2 * θ) * (z * deriv (Work.Elliptic.Gsing α F) z))
      = α * Work.Spaces.Dz Ψ z θ
        + α * (Real.sin (2 * θ) * (z * deriv (Work.Elliptic.Gsing α F) z)) := by ring
  rw [h4, h3]; ring

/-- **Transfer 2**: `∂_θθ W = ∂_θθ Ψ̂ + 4 sin 2θ · Ḡ`. -/
theorem pthIter2_EllResid_eq (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (hΨ : SmoothOpen Ψ)
    (hGs : SmoothOpen (fun z θ => Work.Elliptic.Gsing α F z * Real.sin (2 * θ)))
    (hGb : SmoothOpen (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)))
    {z θ : ℝ} (hz : 0 < z) (hθ1 : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ) z θ
      = Work.Spaces.pthIter 2
          (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
        + 4 * (Real.sin (2 * θ) * Work.Elliptic.Gbar α F z) := by
  have hWeq : Work.Elliptic.EllResid α F Ψ
      = fun z θ => (Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ))
          - Work.Elliptic.Gbar α F z * Real.sin (2 * θ) := by
    funext z θ; exact EllResid_eq_Straight_sub α F Ψ z θ
  rw [hWeq, pthIter2_sub (f := fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ))
    (g := fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ))
    (hΨ.add hGs) hGb hz hθ1 hθ2]
  rw [show Work.Spaces.pthIter 2 (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) z θ
      = -(4 * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ))) from
    pthIter2_radial_sin_two (Work.Elliptic.Gbar α F) z θ]
  ring

/-- **Transfer 3**: `α² z² ∂_zz Ψ̂ = α² z² ∂_zz Ψ + (15/4) sin 2θ · F_* + 5(5+α) sin 2θ · Ḡ`. -/
theorem alpha_sq_zsq_pzIter2_Straight_eq (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hΨ : SmoothOpen Ψ)
    (hGs : SmoothOpen (fun z θ => Work.Elliptic.Gsing α F z * Real.sin (2 * θ)))
    {z θ : ℝ} (hz : 0 < z) (hθ1 : 0 < θ) (hθ2 : θ < π / 2)
    (hOde : α ^ 2 * z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α F) z') z
        + α * (5 + α) * z * deriv (Work.Elliptic.Gsing α F) z
      = (15 / 4) * Work.Elliptic.Fstar F z)
    (hGrel : α * z * deriv (Work.Elliptic.Gsing α F) z = -5 * Work.Elliptic.Gbar α F z) :
    α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2
        (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ)
      = α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        + (15 / 4) * (Real.sin (2 * θ) * Work.Elliptic.Fstar F z)
        + 5 * (5 + α) * (Real.sin (2 * θ) * Work.Elliptic.Gbar α F z) := by
  have hsplit : Work.Spaces.pzIter 2
      (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
      = Work.Spaces.pzIter 2 Ψ z θ
        + deriv (fun z' => deriv (Work.Elliptic.Gsing α F) z') z * Real.sin (2 * θ) := by
    rw [pzIter2_add hΨ hGs hz hθ1 hθ2]
    rw [show Work.Spaces.pzIter 2
        (fun z θ => Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
        = deriv (fun z' => deriv (Work.Elliptic.Gsing α F) z') z * Real.sin (2 * θ) from
      pzIter2_radial_mul (Work.Elliptic.Gsing α F) (fun θ => Real.sin (2 * θ)) z θ]
  have hstep : α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2
        (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ)
      = α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        + (α ^ 2 * z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α F) z') z)
          * Real.sin (2 * θ) := by
    rw [hsplit]; ring
  have hG : α ^ 2 * z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α F) z') z
      = (15 / 4) * Work.Elliptic.Fstar F z
        + 5 * (5 + α) * Work.Elliptic.Gbar α F z := by
    have h1 : α * (5 + α) * z * deriv (Work.Elliptic.Gsing α F) z
        = -5 * (5 + α) * Work.Elliptic.Gbar α F z := by
      have hc := congrArg (fun t => (5 + α) * t) hGrel
      linear_combination hc
    linarith [hOde, h1]
  rw [hstep, hG]; ring

/-! ## The assembly of the estimate -/

/-- **The assembly.**  The first link (the identity (☆) plus sub-additivity) reduces the
target to

  `α²|D_z²Ψ̂| + 5α|D_zΨ̂| ≤ C(|F| + |∂_θθW| + α²|z²∂_zzΨ|)`   (`hZ`, delegated),

and the bound `(3α/4)|sin 2θ F_*| ≤ (3/4)C₄|F|` (`hFS`).  This lemma performs that final
step, with the universal constant `1000 (1 + C) (1 + C₄)`. -/
theorem alphaDzW_Hk_le_assembly (k : ℕ) (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hα4 : α ≤ 1 / 4)
    (hid : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      α * Work.Spaces.Dz (Work.Elliptic.EllResid α F Ψ) z θ
        = (1 / (5 + α)) *
            (α ^ 2 * Work.Spaces.DzIter 2 (fun z θ => Ψ z θ
                + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
              + 5 * α * Work.Spaces.Dz (fun z θ => Ψ z θ
                + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
              - α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
              + (3 * α / 4) * (Real.sin (2 * θ) * Work.Elliptic.Fstar F z)))
    (hsm1 : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.DzIter 2
        (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ))))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hsm2 : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dz
        (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ))))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hsm3 : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (fun z θ =>
        z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hsm4 : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (fun z θ =>
        Real.sin (2 * θ) * Work.Elliptic.Fstar F z)) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hm1 : Work.Spaces.HkMem α k (fun z θ => α ^ 2 * Work.Spaces.DzIter 2
        (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ))
    (hm2 : Work.Spaces.HkMem α k (fun z θ => 5 * α * Work.Spaces.Dz
        (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ))
    (hm3 : Work.Spaces.HkMem α k (fun z θ => -(α ^ 2) * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)))
    (hm4 : Work.Spaces.HkMem α k (fun z θ =>
        (3 * α / 4) * (Real.sin (2 * θ) * Work.Elliptic.Fstar F z)))
    (hm12 : Work.Spaces.HkMem α k (fun z θ =>
        α ^ 2 * Work.Spaces.DzIter 2 (fun z θ => Ψ z θ
            + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
          + 5 * α * Work.Spaces.Dz (fun z θ => Ψ z θ
            + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ))
    (hm34 : Work.Spaces.HkMem α k (fun z θ =>
        -(α ^ 2) * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + (3 * α / 4) * (Real.sin (2 * θ) * Work.Elliptic.Fstar F z)))
    (hadd : ∀ {f g : ℝ → ℝ → ℝ},
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) →
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) →
      Work.Spaces.HkMem α k f → Work.Spaces.HkMem α k g →
      Work.Spaces.HkNorm α k (fun z θ => f z θ + g z θ)
        ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k f + Work.Spaces.HkNorm α k g))
    (hcm : ∀ (c : ℝ) (f : ℝ → ℝ → ℝ),
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) →
      Work.Spaces.HkNorm α k (fun z θ => c * f z θ) = |c| * Work.Spaces.HkNorm α k f)
    (K C4 : ℝ) (hK : 0 ≤ K) (hC4 : 0 < C4)
    (hZ : α ^ 2 * Work.Spaces.HkNorm α k (Work.Spaces.DzIter 2 (fun z θ => Ψ z θ
            + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)))
          + 5 * α * Work.Spaces.HkNorm α k (Work.Spaces.Dz (fun z θ => Ψ z θ
              + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)))
        ≤ K * (Work.Spaces.HkNorm α k F
            + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ))
            + α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)))
    (hFS : Work.Spaces.HkNorm α k (fun z θ => Real.sin (2 * θ) * Work.Elliptic.Fstar F z)
      ≤ C4 * Work.Spaces.HkNorm α k F) :
    Work.Spaces.HkNorm α k (fun z θ => α * Work.Spaces.Dz (Work.Elliptic.EllResid α F Ψ) z θ)
      ≤ 1000 * (1 + K) * (1 + C4)
        * (Work.Spaces.HkNorm α k F
          + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ))
          + α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) := by
  have hlink := Work.FTS.EllipticEst.alphaDzW_Hk_le_first_link α k F Ψ hα hid
    hsm1 hsm2 hsm3 hsm4 hm1 hm2 hm3 hm4 hm12 hm34 hadd hcm
  set A : ℝ := Work.Spaces.HkNorm α k F with hA
  set Bg : ℝ := Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ))
    with hB
  set D : ℝ := α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
    with hD
  set ZS : ℝ := Work.Spaces.HkNorm α k (fun z θ => Real.sin (2 * θ) * Work.Elliptic.Fstar F z)
    with hZS
  have hAnn : 0 ≤ A := Work.Spaces.HkNorm_nonneg _ _ _
  have hBnn : 0 ≤ Bg := Work.Spaces.HkNorm_nonneg _ _ _
  have hDnn : 0 ≤ D := by
    rw [hD]; exact mul_nonneg (sq_nonneg α) (Work.Spaces.HkNorm_nonneg _ _ _)
  have hZSnn : 0 ≤ ZS := Work.Spaces.HkNorm_nonneg _ _ _
  have hα0 : (0 : ℝ) < 5 + α := by linarith
  have hfac : (1 / (5 + α)) * 2 ≤ 1 := by
    rw [one_div_mul_eq_div]; rw [div_le_one hα0]; linarith
  have hZSle : (3 * α / 4) * ZS ≤ (3 / 4) * C4 * A := by
    have h2 : ZS ≤ C4 * A := by
      rw [hZS, hA]
      exact hFS
    nlinarith [h2, hα, hα4, hAnn, hZSnn, hC4]
  have hS : α ^ 2 * Work.Spaces.HkNorm α k (Work.Spaces.DzIter 2 (fun z θ => Ψ z θ
            + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)))
          + 5 * α * Work.Spaces.HkNorm α k (Work.Spaces.Dz (fun z θ => Ψ z θ
              + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)))
          + D + (3 * α / 4) * ZS
      ≤ (K + 1 + (3 / 4) * C4) * (A + Bg + D) := by
    have h3 : D ≤ 1 * (A + Bg + D) := by linarith
    have h4 : (3 / 4) * C4 * A ≤ (3 / 4) * C4 * (A + Bg + D) := by
      have : (0:ℝ) ≤ (3/4) * C4 := by positivity
      nlinarith [hAnn, hBnn, hDnn]
    nlinarith [hZ, h3, h4, hZSle, hAnn, hBnn, hDnn, hK]
  have hfin : (K + 1 + (3 / 4) * C4) ≤ 1000 * (1 + K) * (1 + C4) := by
    nlinarith [hK, hC4]
  calc Work.Spaces.HkNorm α k (fun z θ => α * Work.Spaces.Dz (Work.Elliptic.EllResid α F Ψ) z θ)
      ≤ (1 / (5 + α)) * 2 * (α ^ 2 * Work.Spaces.HkNorm α k (Work.Spaces.DzIter 2
              (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)))
            + 5 * α * Work.Spaces.HkNorm α k (Work.Spaces.Dz (fun z θ => Ψ z θ
                + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)))
            + α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
            + (3 * α / 4) * ZS) := hlink
    _ = (1 / (5 + α)) * 2 * (α ^ 2 * Work.Spaces.HkNorm α k (Work.Spaces.DzIter 2
              (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)))
            + 5 * α * Work.Spaces.HkNorm α k (Work.Spaces.Dz (fun z θ => Ψ z θ
                + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)))
            + D + (3 * α / 4) * ZS) := by rw [hD]
    _ ≤ (1 / (5 + α)) * 2 * ((K + 1 + (3 / 4) * C4) * (A + Bg + D)) :=
        mul_le_mul_of_nonneg_left hS (by positivity)
    _ ≤ (K + 1 + (3 / 4) * C4) * (A + Bg + D) := by
        have h1 : (1 / (5 + α)) * 2 ≤ 1 := hfac
        have h2 : (0 : ℝ) ≤ (K + 1 + (3 / 4) * C4) * (A + Bg + D) := by
          apply mul_nonneg <;> nlinarith [hK, hC4, hAnn, hBnn, hDnn]
        calc (1 / (5 + α)) * 2 * ((K + 1 + (3 / 4) * C4) * (A + Bg + D))
            ≤ 1 * ((K + 1 + (3 / 4) * C4) * (A + Bg + D)) :=
              mul_le_mul_of_nonneg_right h1 h2
          _ = (K + 1 + (3 / 4) * C4) * (A + Bg + D) := one_mul _
    _ ≤ 1000 * (1 + K) * (1 + C4) * (A + Bg + D) := by
        have hnn : (0:ℝ) ≤ A + Bg + D := by linarith
        nlinarith [hfin, hnn]
    _ = 1000 * (1 + K) * (1 + C4)
        * (Work.Spaces.HkNorm α k F
          + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ))
          + α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) := by
        rw [hA, hB, hD]

/-! ## The estimate -/

theorem alphaDzW_Hk_le (k : ℕ) (hk : 2 ≤ k) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.EllHyp α k F Ψ →
      Work.Elliptic.OrthCond (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) →
      Work.Spaces.HkNorm α k (fun z θ => α * Work.Spaces.Dz (Work.Elliptic.EllResid α F Ψ) z θ)
        ≤ C * (Work.Spaces.HkNorm α k F
            + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ))
            + α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) := by
  obtain ⟨K, hKpos, hZ⟩ := Work.FTS.EllipticEst.Straight_DzHk_le k hk
  obtain ⟨C4, hC4pos, hFS⟩ := Work.FTS.EllipticEst.Fstar_Hk_le_open k
  refine ⟨1000 * (1 + K) * (1 + C4), by positivity, ?_⟩
  intro α F Ψ hα hα4 hHyp hOrth
  obtain ⟨hsm1, hsm2, hsm3, hsm4, hm1, hm2, hm3, hm4, hm12, hm34⟩ :=
    Work.FTS.EllipticEst.EllHyp_certificates α k F Ψ hα hα4 hHyp
  have hid := alphaDzEllResid_eq_of_EllHyp_local α k F Ψ hα hα4 hHyp
  have hZ' := hZ α F Ψ hα hα4 hHyp hOrth
  have hFsm := Work.FTS.EllipticEst.EllHyp_F_smoothOpen α k F Ψ hα hHyp
  have hFS' : Work.Spaces.HkNorm α k
        (fun z θ => Real.sin (2 * θ) * Work.Elliptic.Fstar F z)
      ≤ C4 * Work.Spaces.HkNorm α k F := by
    have hcongr : Work.Spaces.HkNorm α k
          (fun z θ => Real.sin (2 * θ) * Work.Elliptic.Fstar F z)
        = Work.Spaces.HkNorm α k (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) := by
      rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
      refine congrArg Real.sqrt ?_
      refine Work.FTS.EllipticEst.HkSq_congr_open α k (fun z θ _ _ _ => ?_)
      ring
    rw [hcongr]
    exact hFS α F hα (le_trans hα4 (by norm_num)) hFsm hHyp.memF
  exact Work.FTS.EllipticEst.alphaDzW_Hk_le_assembly k α F Ψ hα hα4 hid
    hsm1 hsm2 hsm3 hsm4 hm1 hm2 hm3 hm4 hm12 hm34
    (fun hf hg hmf hmg => Work.FTS.EllipticEst.HkNorm_add_fts α k hf hg hmf hmg)
    (fun c f hf => Work.FTS.EllipticEst.HkNorm_const_mul α k c hf)
    K C4 hKpos.le hC4pos hZ' hFS'



/-!

## Status, and how to finish `alphaDzW_Hk_le`

**Proved in this file.**  `Lzero_radial_sin_two`, `DzIter_add_eq`, `Dz_EllResid`,
`alphaDzEllResid_eq` (the algebraic identity (☆)), `HkSq_const_mul`,
`HkNorm_alphaDzEllResid_eq`, `HkNorm_sum4_le`, `alphaDzW_Hk_le_first_link` (the "first
link"), the calculus lemmas `deriv_sin_two`, `deriv_cos_two`, `deriv_deriv_sin_two`,
`pthIter2_radial_sin_two`, `pzIter2_radial_mul`, the `SmoothOpen` slice/additivity API
(`SmoothOpen.differentiableAt_slice_theta/z`, `SmoothOpen.add`, `pthIter2_add/sub`,
`pzIter2_add`, `pz_add`, `Dz_add`), the transfer identities (`EllResid_eq_Straight_sub`,
`alpha_Dz_Straight_eq`, `pthIter2_EllResid_eq`, `alpha_sq_zsq_pzIter2_Straight_eq`) — all
`sorry`-free — and the **assembly** `alphaDzW_Hk_le_assembly`, which derives the target
estimate from the first link, the single input `hZ`

  `α²|D_z²Ψ̂| + 5α|D_zΨ̂| ≤ K (|F| + |∂_θθW| + α²|z²∂_zzΨ|)`,

the bound `|sin 2θ · F_*| ≤ C₄|F|` (`Fstar_Hk_le_open`, proved) and the sub-additivity /
homogeneity parameters `hadd` (`HkNorm_add_le`) and `hcm` (`HkNorm_const_mul`).

**What remains.**  Only the wiring: import
`alphaDzEllResid_eq_of_Hyp` (proved: supplies `hid`), `HkNorm_add_fts` (i.e.
`HkNorm_add_le`), `Fstar_Hk_le_open` (proved), `Straight_DzHk_le` (supplies `hZ`),
`EllHyp_F_smoothOpen` (open-quadrant smoothness of `F` from the equation),
`EllHyp_certificates` / `Straight_certs_open` / `HkMem_FstarSin_open` (the `∀n ContDiffOn`
and `HkMem` certificates for the four pieces of the first link and their partial sums,
the latter via `HkMem_add_smoothOpen`), and then instantiate the assembly with `K` from
`Straight_DzHk_le` and `C₄` from `Fstar_Hk_le_open`.  Note the multiplication order:
`Fstar_Hk_le_open` bounds `fun z θ => Fstar F z * sin 2θ`, whereas `hFS` above uses
`fun z θ => sin 2θ * Fstar F z`; convert with `HkSq_congr_open` and `ring`.

**Workspace note (blocks the wiring, not this file).**
`Submission/Work/FTS/EllipticEst/IntegrableOn_Fstar_div_of_HkMem.lean` declares
`Work.FTS.EllipticEst.HkIntegrand_zero`, a name that already exists in
`Submission/Work/FTS/EllipticEst/Defs.lean` with a different signature.  Any module importing
both therefore fails with

  `import ...IntegrableOn_Fstar_div_of_HkMem failed, environment already contains
   'Work.FTS.EllipticEst.HkIntegrand_zero' from ...Defs`

— this is what currently breaks `alphaDzEllResid_eq_of_Hyp.lean` and `Straight_DzHk_le.lean`
(both `sorry`-free) and, transitively, everything of the node that imports them.  Renaming the
copy in `IntegrableOn_Fstar_div_of_HkMem.lean` (e.g. to `HkIntegrand_zero_k0`) repairs the
whole neighbourhood.
-/

end Work.FTS.EllipticEst
