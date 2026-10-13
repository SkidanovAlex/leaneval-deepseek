/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Straight_DzHk_le` — the radial `D_z`-estimate for the straightened solution

This module proves `Work.FTS.EllipticEst.Straight_DzHk_le`:

  `α²|D_z²Ψ̂|_{ℋ^k} + 5α|D_zΨ̂|_{ℋ^k} ≤ C (|F|_{ℋ^k} + |∂_θθ W|_{ℋ^k} + α²|z²∂_zzΨ|_{ℋ^k})`

for the data of `EllHyp α k F Ψ` with `OrthCond Ψ̂`, where

  `Ψ̂ = Ψ + Gsing α F · sin 2θ`,   `W = EllResid α F Ψ = Ψ - (1/(4α)) sin 2θ L₁₂(F)`.

## The maths

Write `V = Ψ̂`, `G = Gsing α F`, `Ḡ = Gbar α F` (so `G = Gstar + Ḡ` with `Gstar = -(1/(4α))L₁₂(F)`
and `V = W + Ḡ·sin 2θ`).  The two *straightening identities* (`EllHyp_certificates`, proved there
from the ODE `α²z²G'' + α(5+α)zG' = (15/4)F_*` and the first-order relation `α z G' = -5Ḡ`) are

* `α²D_z²V = α²D_z²Ψ + (15/4)·(sin 2θ · F_*) + 25·(Ḡ·sin 2θ)`,
* `5αD_zV = 5αD_zΨ - 25·(Ḡ·sin 2θ)`.

Combining them with the algebraic identity `D_z²f = z²∂_zzf + D_zf` gives the transfer

* `α²z²∂_zzV = α²z²∂_zzΨ + (15/4)(sin 2θ F_*) + (25+5α)(Ḡ sin 2θ)`,

and then every remaining norm is controlled by the right-hand side:

* `α²|D_z²V| ≤ α²(|z²∂_zzV| + |D_zV|)` (subadditivity, `HkNorm_add_fts`);
* `α²|z²∂_zzV| ≤ 2α²|z²∂_zzΨ| + 8|sin 2θ F_*| + 53|Ḡ sin 2θ|` (the transfer + three-term
  subadditivity); the last two are `≤ C|F|_{ℋ^k}` (`Fstar_Hk_le_open`, `Gbar_Hk_le_open`);
* `α|D_zV| ≤ C (|V| + α²|z²∂_zzV|)` — the radial Agmon–Nirenberg (`HkNorm_Dz_amgm`);
* `|V| ≤ C(|F| + |∂_θθV| + α²|z²∂_zzΨ|)` (`Straight_Hk_input`, the slicewise angular coercivity,
  which uses `OrthCond Ψ̂`);
* `|∂_θθV| ≤ 2(|∂_θθW| + 4|Ḡ sin 2θ|)` — the transfer `∂_θθV = ∂_θθW - 4 Ḡ sin 2θ` plus
  subadditivity, for which the honesty of `∂_θθW` is the certificate
  `Cert.HkMem_pthIter2_EllResid`.

## What is proved here, and what is imported

Proved here (from proved modules): the additivity of `∂_θθ` on `SmoothOpen` data, the
commutation of `∂_θθ` with radial multiples of `sin 2θ`, the two transfers, the three-term
subadditivity, and the constant bookkeeping of the assembly.

Imported: the radial Agmon–Nirenberg estimate (`Work.Blocks.DzVamgm.HkNorm_Dz_amgm`, proved and
axiom-clean), the straightened-solution estimate
(`Work.FTS.EllipticEst.Straight.coercive_input`, the same statement as `Straight_Hk_input`, proved
in `Straight/CoerciveInput.lean`), the two Hardy-type layer bounds
(`Cert.GbarSin_layer`, `Cert.FstarSin_layer`), the membership
`Cert.HkMem_pthIter2_EllResid` (through the clash-free shim `TT.Shim.HkMem_pthIter2_EllResid`) and
the smoothness/ODE package (`Cert.Gsing_smooth_ode_of_facts`, `Gsing_deriv_rel`,
`Cert.FstarSmoothOfSol`, `Cert.FstarDivIntegrableOfSolHk`, `HasDerivAt_L12_of_Fstar_facts`,
`Cert.Jfun_hasDerivAt_of_Fstar`).

The whole cone of the proof is free of the unproved-declaration axiom:
`#print axioms Work.FTS.EllipticEst.Straight_DzHk_le` reports
`[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
-- The `EllHyp` bookkeeping certificates are consumed through their **clash-free shim**
-- `TT.Shim.EllHyp_certificates`.  The original `EllHyp_certificates` pulls in `Fstar_Hk_le`
-- (via `Cert.DzPsiAux`) and therefore cannot be loaded in the same environment as `OpenQDefs`:
-- both declare `Work.FTS.EllipticEst.integrableOn_zSummand`.  The shim declares exactly the
-- same names with a clash-free import cone.
import Submission.Work.FTS.EllipticEst.HkNorm_add_fts
import Submission.Work.FTS.EllipticEst.HkNorm_const_mul
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.LocData.HkSq_const_mul
import Submission.Work.FTS.LocData.HkIntegrand_const_mul
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.EllipticEst.Gsing_deriv_rel
import Submission.Work.Elliptic.Gsing_ode
import Submission.Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts
import Submission.Work.FTS.EllipticEst.Cert.Jfun_hasDerivAt_of_Fstar
import Submission.Work.FTS.EllipticEst.Cert.FstarSmoothOfSol
import Submission.Work.FTS.EllipticEst.Cert.Gsing_smooth_ode_of_facts
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.SmoothOpen_bslOp
import Submission.Work.FTS.EllipticEst.Cert.FstarSin_layer
import Submission.Work.FTS.EllipticEst.Cert.GbarSin_layer
import Submission.Work.FTS.EllipticEst.TT.Shim.HkMem_pthIter2_EllResid
-- The slicewise angular coercivity of the straightened solution (`Straight_Hk_input`).
-- The assignment-path file is still a bare placeholder; the proved, axiom-clean copy -- the same
-- proof as `Work.Blocks.straight_Hk_input_clean`, rehomed with the clash-free imports of the
-- `TT.Shim` layer -- lives in `Straight/CoerciveInput.lean` and is consumed here as
-- `Work.FTS.EllipticEst.Straight.coercive_input`.
import Submission.Work.FTS.EllipticEst.Straight.CoerciveInput
-- The radial Agmon--Nirenberg interpolation.  The assignment-path statement `HkNorm_Dz_amgm`
-- is still a bare placeholder; the proved, axiom-clean copy lives in the `Blocks` rework of the
-- chain (`Work.Blocks.DzVamgm.HkNorm_Dz_amgm`, same statement, clash-free import cone).
import Submission.Work.Blocks.DzV_amgm_clean

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
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The straightened solution -/

/-- **The straightened solution** `V = Ψ + Gsing α F · sin 2θ` (the `Straight α F Ψ` of
`StraightDefs`), written out so that it is *definitionally* the function appearing in the
statement of `Straight_DzHk_le`. -/
def Vf (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)

@[simp] theorem Vf_apply (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Vf α F Ψ z θ = Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ) := rfl

/-- `V = W + Ḡ·sin 2θ` where `W = EllResid α F Ψ`. -/
theorem Vf_eq_EllResid_add (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) :
    Vf α F Ψ = fun z θ => Work.Elliptic.EllResid α F Ψ z θ
      + Work.Elliptic.Gbar α F z * Real.sin (2 * θ) := by
  funext z θ
  simp only [Vf, Work.Elliptic.EllResid, Work.Elliptic.Gsing, Work.Elliptic.Gstar]
  ring

/-! ## The elementary `∂_θ`-calculus -/

/-- `SmoothOpen` is closed under the `∂_θ`-iterates. -/
theorem SmoothOpen_pthIter {F : ℝ → ℝ → ℝ} (hF : SmoothOpen F) (i : ℕ) :
    SmoothOpen (Work.Spaces.pthIter i F) := by
  induction i with
  | zero => simpa using hF
  | succ i ih => rw [Work.Spaces.pthIter_succ]; exact ih.pth

/-- `∂_θ`-iterates are additive on data which are `C^∞` on the open quadrant. -/
theorem pthIter_add_of_smoothOpen {f g : ℝ → ℝ → ℝ} (hf : SmoothOpen f) (hg : SmoothOpen g)
    (i : ℕ) : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.pthIter i (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.pthIter i f z θ + Work.Spaces.pthIter i g z θ := by
  induction i with
  | zero => intro z θ _ _ _; rfl
  | succ n ih =>
      intro z θ hz h1 h2
      have hθ : θ ∈ Set.Ioo 0 (π / 2) := ⟨h1, h2⟩
      have heq : (fun θ' : ℝ => Work.Spaces.pthIter n (fun z θ => f z θ + g z θ) z θ')
          =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.pthIter n f z θ' + Work.Spaces.pthIter n g z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact ih z θ' hz hθ'.1 hθ'.2
      have hd1 : DifferentiableAt ℝ (fun θ' => Work.Spaces.pthIter n f z θ') θ :=
        (((SmoothOpen_pthIter hf n).curry_θ hz).differentiableOn (by simp)).differentiableAt
          (isOpen_Ioo.mem_nhds hθ)
      have hd2 : DifferentiableAt ℝ (fun θ' => Work.Spaces.pthIter n g z θ') θ :=
        (((SmoothOpen_pthIter hg n).curry_θ hz).differentiableOn (by simp)).differentiableAt
          (isOpen_Ioo.mem_nhds hθ)
      rw [Work.Spaces.pthIter_succ]
      show deriv (fun θ' => Work.Spaces.pthIter n (fun z θ => f z θ + g z θ) z θ') θ
        = deriv (fun θ' => Work.Spaces.pthIter n f z θ') θ
          + deriv (fun θ' => Work.Spaces.pthIter n g z θ') θ
      rw [heq.deriv_eq]
      exact deriv_add hd1 hd2

/-- `∂_θθ(g(z)·sin 2θ) = -4 g(z) sin 2θ`. -/
theorem pthIter_two_radialSin (g : ℝ → ℝ) :
    Work.Spaces.pthIter 2 (fun z θ => g z * Real.sin (2 * θ))
      = fun z θ => -4 * (g z * Real.sin (2 * θ)) := by
  funext z θ
  have h1 : ∀ θ' : ℝ, deriv (fun x : ℝ => g z * Real.sin (2 * x)) θ'
      = g z * (Real.cos (2 * θ') * 2) := by
    intro θ'
    have h4 : HasDerivAt (fun x : ℝ => (2 : ℝ) * x) 2 θ' := by
      simpa using (hasDerivAt_id θ').const_mul (2 : ℝ)
    exact (h4.sin.const_mul (g z)).deriv
  have h2 : deriv (fun x : ℝ => g z * (Real.cos (2 * x) * 2)) θ
      = -4 * (g z * Real.sin (2 * θ)) := by
    have hfun : (fun x : ℝ => g z * (Real.cos (2 * x) * 2))
        = fun x : ℝ => (g z * 2) * Real.cos (2 * x) := by
      funext x; ring
    rw [hfun]
    have h6 : HasDerivAt (fun x : ℝ => Real.cos (2 * x)) (-(Real.sin (2 * θ)) * 2) θ := by
      have h4 : HasDerivAt (fun x : ℝ => (2 : ℝ) * x) 2 θ := by
        simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
      exact h4.cos
    have h7 := h6.const_mul (g z * 2)
    rw [h7.deriv]; ring
  simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth,
    Function.comp_apply]
  rw [show (fun θ' : ℝ => deriv (fun x : ℝ => g z * Real.sin (2 * x)) θ')
      = fun θ' => g z * (Real.cos (2 * θ') * 2) from funext h1]
  exact h2

/-! ## The transfers -/

/-- **Transfer `∂_θθ`**: `∂_θθV = ∂_θθW - 4 (Ḡ·sin 2θ)`, from `V = W + Ḡ sin 2θ`. -/
theorem pthIter_two_Vf (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (hW : SmoothOpen (Work.Elliptic.EllResid α F Ψ))
    (hGb : SmoothOpen (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.pthIter 2 (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
      = Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ) z θ
        + (-4) * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) := by
  have hV : (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ))
      = fun z θ => Work.Elliptic.EllResid α F Ψ z θ
        + Work.Elliptic.Gbar α F z * Real.sin (2 * θ) := by
    funext z θ
    simp only [Work.Elliptic.EllResid, Work.Elliptic.Gsing, Work.Elliptic.Gstar]
    ring
  rw [hV, pthIter_add_of_smoothOpen hW hGb 2 z θ hz hθ.1 hθ.2, pthIter_two_radialSin]

/-- **Transfer `α²z²∂_zz`**: from the straightening identities and `D_z²f = z²∂_zzf + D_zf`,

  `α²z²∂_zzV = α²z²∂_zzΨ + (15/4)(sin 2θ · F_*) + (25+5α)(Ḡ·sin 2θ)`. -/
theorem zsq_pzIter_two_Vf (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hΨso : SmoothOpen Ψ)
    (hGso : SmoothOpen (fun z θ => Work.Elliptic.Gsing α F z * Real.sin (2 * θ)))
    (hSso : SmoothOpen (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)))
    (hGderiv : ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (fun z' => deriv (Work.Elliptic.Gsing α F) z') z)
    (hode : ∀ z ∈ Set.Ioi (0 : ℝ),
      α ^ 2 * z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α F) z') z
        + α * (5 + α) * z * deriv (Work.Elliptic.Gsing α F) z
      = (15 / 4) * Work.Elliptic.Fstar F z)
    (hrel : ∀ z ∈ Set.Ioi (0 : ℝ),
      α * z * deriv (Work.Elliptic.Gsing α F) z = -5 * Work.Elliptic.Gbar α F z)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ)
      = α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        + (15 / 4) * (Work.Elliptic.Fstar F z * Real.sin (2 * θ))
        + (25 + 5 * α) * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) := by
  have h1 := alphaDzIter2_straight_eq α F Ψ hα hz hθ hΨso hGso (hGderiv z hz) (hode z hz)
    (hrel z hz)
  have h2 := alphaDz_straight_eq α F Ψ hz hθ hΨso hGso (hrel z hz)
  have h3 := DzIter2_eq_zsq_pzIter2_add_Dz (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) hSso hz hθ
  have h4 := DzIter2_eq_zsq_pzIter2_add_Dz Ψ hΨso hz hθ
  have h3' : α ^ 2 * Work.Spaces.DzIter 2 (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
      = α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ)
        + α ^ 2 * Work.Spaces.Dz (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ := by
    rw [h3]; ring
  have h4' : α ^ 2 * Work.Spaces.DzIter 2 Ψ z θ
      = α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        + α ^ 2 * Work.Spaces.Dz Ψ z θ := by
    rw [h4]; ring
  have h5' : α ^ 2 * Work.Spaces.Dz (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
      = α ^ 2 * Work.Spaces.Dz Ψ z θ
        - 5 * α * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) := by
    linear_combination (α / 5) * h2
  have hswapped : α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ)
      = α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        + (15 / 4) * (Real.sin (2 * θ) * Work.Elliptic.Fstar F z)
        + (25 + 5 * α) * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) := by
    linear_combination (h1) - (h3') + (h4') - (h5')
  rw [hswapped]; ring

/-! ## Three-term subadditivity -/

/-- A property of angles holding on the open interval `(0,π/2)` holds almost everywhere on
`Iθ`. -/
private theorem ae_restrict_Iθ_of_Ioo' {p : ℝ → Prop} (h : ∀ θ ∈ Set.Ioo 0 (π / 2), p θ) :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), p θ := by
  have hIoo : Set.Ioo 0 (π / 2) =ᵐ[volume] Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc
  refine (MeasureTheory.ae_restrict_congr_set hIoo).mp ?_
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo fun θ hθ => h θ hθ

/-- **Pointwise three-term subadditivity of the `ℋ^k`-integrand** on the open quadrant. -/
theorem HkIntegrand_add3_le_open {α : ℝ} {k : ℕ} {f g h : ℝ → ℝ → ℝ}
    (hf : SmoothOpen f) (hg : SmoothOpen g) (hh : SmoothOpen h) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ + h z θ) z θ
      ≤ 4 * Work.Spaces.HkIntegrand α k f z θ + 4 * Work.Spaces.HkIntegrand α k g z θ
        + 2 * Work.Spaces.HkIntegrand α k h z θ := by
  have hfg : SmoothOpen (fun z θ => f z θ + g z θ) := smoothOpen_add hf hg
  have h1 : Work.Spaces.HkIntegrand α k
      (fun z θ => (fun z θ => f z θ + g z θ) z θ + h z θ) z θ
      ≤ 2 * (Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ
        + Work.Spaces.HkIntegrand α k h z θ) :=
    HkIntegrand_add_le_open_Ioo (α := α) (k := k) (f := fun z θ => f z θ + g z θ) (g := h)
      hfg hh hz hθ
  have h2 : Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ
      ≤ 2 * (Work.Spaces.HkIntegrand α k f z θ + Work.Spaces.HkIntegrand α k g z θ) :=
    HkIntegrand_add_le_open_Ioo (α := α) (k := k) (f := f) (g := g) hf hg hz hθ
  linarith [h1, h2]

/-- **Three-term subadditivity of the squared norm**: `|f+g+h|² ≤ 4|f|² + 4|g|² + 2|h|²`. -/
theorem HkSq_add3_le (α : ℝ) (k : ℕ) {f g h : ℝ → ℝ → ℝ}
    (hf : SmoothOpen f) (hg : SmoothOpen g) (hh : SmoothOpen h)
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g)
    (hmh : Work.Spaces.HkMem α k h) :
    Work.Spaces.HkSq α k (fun z θ => f z θ + g z θ + h z θ)
      ≤ 4 * Work.Spaces.HkSq α k f + 4 * Work.Spaces.HkSq α k g
        + 2 * Work.Spaces.HkSq α k h := by
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ + h z θ) z θ)
        ≤ 4 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
          + 4 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)
          + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h z θ) := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      simp [Work.FTS.LocData.HkIntegrand_zero_fst]
    · have hle : (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ + h z θ) z θ)
          ≤ ∫ θ in Work.Spaces.Iθ,
              (4 * Work.Spaces.HkIntegrand α k f z θ
                + 4 * Work.Spaces.HkIntegrand α k g z θ
                + 2 * Work.Spaces.HkIntegrand α k h z θ) :=
        MeasureTheory.integral_mono_of_nonneg
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
            (fun θ _ => Work.Spaces.HkIntegrand_nonneg α k
              (fun z θ => f z θ + g z θ + h z θ) z θ))
          ((((hmf.1 z hz).const_mul 4).add ((hmg.1 z hz).const_mul 4)).add
            ((hmh.1 z hz).const_mul 2))
          (ae_restrict_Iθ_of_Ioo' (fun θ hθ => HkIntegrand_add3_le_open hf hg hh hz0 hθ))
      have hInt : (∫ θ in Work.Spaces.Iθ, 4 * Work.Spaces.HkIntegrand α k f z θ
              + 4 * Work.Spaces.HkIntegrand α k g z θ
              + 2 * Work.Spaces.HkIntegrand α k h z θ)
          = 4 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
            + 4 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)
            + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h z θ) := by
        rw [MeasureTheory.integral_add
              (f := fun θ => 4 * Work.Spaces.HkIntegrand α k f z θ
                + 4 * Work.Spaces.HkIntegrand α k g z θ)
              (g := fun θ => 2 * Work.Spaces.HkIntegrand α k h z θ)
              (((hmf.1 z hz).const_mul 4).add ((hmg.1 z hz).const_mul 4))
              ((hmh.1 z hz).const_mul 2),
            MeasureTheory.integral_add ((hmf.1 z hz).const_mul 4)
              ((hmg.1 z hz).const_mul 4),
            MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
            MeasureTheory.integral_const_mul]
      linarith [hle, hInt]
  have hmono : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ + h z θ) z θ)
      ≤ ∫ z in Work.Spaces.Iz,
          (4 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
            + 4 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)
            + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h z θ)) :=
    MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun z => integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α k (fun z θ => f z θ + g z θ + h z θ) z θ)
      (((hmf.2.const_mul 4).add (hmg.2.const_mul 4)).add (hmh.2.const_mul 2))
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => hinner z hz)
  have hIntO : (∫ z in Work.Spaces.Iz,
        4 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
          + 4 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)
          + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h z θ))
      = 4 * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k f z θ)
        + 4 * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k g z θ)
        + 2 * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k h z θ) := by
    rw [MeasureTheory.integral_add
          (f := fun z => 4 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
            + 4 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ))
          (g := fun z => 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h z θ))
          ((hmf.2.const_mul 4).add (hmg.2.const_mul 4)) (hmh.2.const_mul 2),
        MeasureTheory.integral_add (hmf.2.const_mul 4) (hmg.2.const_mul 4),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul]
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq, Work.Spaces.HkSq, Work.Spaces.HkSq]
  refine le_trans hmono ?_
  rw [hIntO]

/-- `√(4a+4b+2c) ≤ 2√a + 2√b + 2√c` for `a,b,c ≥ 0`. -/
theorem sqrt_four_add_le (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    Real.sqrt (4 * a + 4 * b + 2 * c) ≤ 2 * Real.sqrt a + 2 * Real.sqrt b + 2 * Real.sqrt c := by
  have h0 : 0 ≤ 2 * Real.sqrt a + 2 * Real.sqrt b + 2 * Real.sqrt c := by
    have h1 := Real.sqrt_nonneg a
    have h2 := Real.sqrt_nonneg b
    have h3 := Real.sqrt_nonneg c
    linarith
  have hs : 4 * a + 4 * b + 2 * c
      ≤ (2 * Real.sqrt a + 2 * Real.sqrt b + 2 * Real.sqrt c) ^ 2 := by
    have hsa : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha
    have hsb : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt hb
    have hsc : (Real.sqrt c) ^ 2 = c := Real.sq_sqrt hc
    have h1 := Real.sqrt_nonneg a
    have h2 := Real.sqrt_nonneg b
    have h3 := Real.sqrt_nonneg c
    nlinarith [mul_nonneg h1 h2, mul_nonneg h1 h3, mul_nonneg h2 h3, hsa, hsb, hsc]
  exact le_trans (Real.sqrt_le_sqrt hs) (le_of_eq (Real.sqrt_sq h0))

/-- **Three-term subadditivity of the norm**: `|f+g+h| ≤ 2(|f|+|g|) + 2|h|`. -/
theorem HkNorm_add3_le (α : ℝ) (k : ℕ) {f g h : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hh : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry h) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g)
    (hmh : Work.Spaces.HkMem α k h) :
    Work.Spaces.HkNorm α k (fun z θ => f z θ + g z θ + h z θ)
      ≤ 2 * (Work.Spaces.HkNorm α k f + Work.Spaces.HkNorm α k g)
        + 2 * Work.Spaces.HkNorm α k h := by
  have hfS : SmoothOpen f := smoothOpen_of_forall (by simpa [Q0] using hf)
  have hgS : SmoothOpen g := smoothOpen_of_forall (by simpa [Q0] using hg)
  have hhS : SmoothOpen h := smoothOpen_of_forall (by simpa [Q0] using hh)
  have hsq := HkSq_add3_le α k hfS hgS hhS hmf hmg hmh
  rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, Work.Spaces.HkNorm, Work.Spaces.HkNorm]
  refine le_trans (Real.sqrt_le_sqrt hsq)
    (le_trans (sqrt_four_add_le _ _ _ (Work.Spaces.HkSq_nonneg α k f)
      (Work.Spaces.HkSq_nonneg α k g) (Work.Spaces.HkSq_nonneg α k h)) ?_)
  ring_nf <;> linarith

/-! ## The assembly -/

/-- The constant of `Straight_DzHk_le`, as a function of the four imported constants. -/
def straightC (C1 C2 C3 C4 : ℝ) : ℝ :=
  4 + 2 * (8 * C4 + 53 * C3)
    + (11 / 2) * C1 * (3 * C2 * (1 + 8 * C3) + 2 + (8 * C4 + 53 * C3))

theorem straightC_pos {C1 C2 C3 C4 : ℝ} (h1 : 0 < C1) (h2 : 0 < C2) (h3 : 0 < C3)
    (h4 : 0 < C4) : 0 < straightC C1 C2 C3 C4 := by
  have hb : 0 < 8 * C4 + 53 * C3 := by linarith
  have hA : 0 < 3 * C2 * (1 + 8 * C3) + 2 + (8 * C4 + 53 * C3) := by positivity
  rw [straightC]
  have h5 : 0 < (11 / 2 : ℝ) * C1 * (3 * C2 * (1 + 8 * C3) + 2 + (8 * C4 + 53 * C3)) := by
    positivity
  have h6 : 0 < 2 * (8 * C4 + 53 * C3) := by linarith
  linarith

set_option maxHeartbeats 4000000 in
theorem Straight_DzHk_le (k : ℕ) (hk : 2 ≤ k) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.EllHyp α k F Ψ →
      Work.Elliptic.OrthCond (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) →
      α ^ 2 * Work.Spaces.HkNorm α k (Work.Spaces.DzIter 2
          (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)))
        + 5 * α * Work.Spaces.HkNorm α k (Work.Spaces.Dz
          (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)))
      ≤ C * (Work.Spaces.HkNorm α k F
          + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ))
          + α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) := by
  obtain ⟨C1, hC1pos, hAGM⟩ := Work.Blocks.DzVamgm.HkNorm_Dz_amgm k
  obtain ⟨C2, hC2pos, hSH⟩ := Work.FTS.EllipticEst.Straight.coercive_input k hk
  obtain ⟨C3, hC3pos, hGb⟩ := Cert.GbarSin_layer k
  obtain ⟨C4, hC4pos, hFS⟩ := Cert.FstarSin_layer k
  refine ⟨straightC C1 C2 C3 C4, straightC_pos hC1pos hC2pos hC3pos hC4pos, ?_⟩
  intro α F Ψ hα hα4 hHyp hOrth
  have hα1 : α ≤ 1 := by linarith
  change α ^ 2 * Work.Spaces.HkNorm α k (Work.Spaces.DzIter 2 (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)))
      + 5 * α * Work.Spaces.HkNorm α k (Work.Spaces.Dz (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)))
      ≤ straightC C1 C2 C3 C4 * (Work.Spaces.HkNorm α k F
          + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ))
          + α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
  set A : ℝ := Work.Spaces.HkNorm α k F with hA
  set Bg : ℝ := Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ))
    with hB
  set D : ℝ := α ^ 2 * Work.Spaces.HkNorm α k
    (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) with hD
  set P : ℝ := Work.Spaces.HkNorm α k (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) with hP
  set Q : ℝ := Work.Spaces.HkNorm α k (Work.Spaces.Dz (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ))) with hQ
  set R : ℝ := α ^ 2 * Work.Spaces.HkNorm α k
    (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ) with hR
  set E : ℝ := Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ))) with hE
  set S : ℝ := Work.Spaces.HkNorm α k
    (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) with hS
  set G : ℝ := Work.Spaces.HkNorm α k
    (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) with hG
  -- ## smoothess and ODE facts
  have hFsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry F)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    intro n
    have h := (Cert.GbarSin.SmoothOpen_bslOp α hHyp.smoothNbhd).forall n
    refine h.congr ?_
    intro p hp
    obtain ⟨hz, hθ0, hθ1⟩ := mem_Q0.mp hp
    simpa [Function.uncurry] using (hHyp.sol.1 p.1 hz p.2 hθ0 hθ1).symm
  have hFstSm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar F) (Set.Ioi 0) :=
    Cert.FstarSmoothOfSol α F Ψ hHyp.smoothNbhd hHyp.sol
  have hFint : IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar F r / r) (Set.Ioi 0) :=
    Cert.FstarDivIntegrableOfSolHk α k F Ψ hα hHyp.smoothNbhd hHyp.sol hHyp.memF
  have hL12deriv : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.L12 F) (-(3 * Work.Elliptic.Fstar F z / z)) z :=
    HasDerivAt_L12_of_Fstar_facts F hFstSm hFint
  have hFc : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.Fstar F) (deriv (Work.Elliptic.Fstar F) z) z := by
    intro z hz
    exact (((hFstSm 1).differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds hz)).hasDerivAt
  have hJ : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z' => ∫ s in (0 : ℝ)..z',
          s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s)
        (z ^ ((5 - α) / α) * Work.Elliptic.Fstar F z) z :=
    Cert.Jfun_hasDerivAt_of_Fstar α F hFstSm hFint hα hα1
  have hrel := Gsing_deriv_rel α F hα hL12deriv hFc hJ
  obtain ⟨hGsSm, hGode⟩ := Cert.Gsing_smooth_ode_of_facts α F hα hFstSm hFint hL12deriv
  have hGderiv : ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (fun z' => deriv (Work.Elliptic.Gsing α F) z') z := by
    intro z hz
    have hd : ContDiffOn ℝ (1 : WithTop ℕ∞) (deriv (Work.Elliptic.Gsing α F))
        (Set.Ioi 0) := (hGsSm 2).deriv_of_isOpen isOpen_Ioi (by norm_num)
    exact (hd.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz)
  -- ## smoothness of the pieces
  have hΨso : SmoothOpen Ψ := SmoothNbhd_smoothOpen hHyp.smoothNbhd
  have hsin2 : ContDiff ℝ ⊤ (fun θ : ℝ => Real.sin (2 * θ)) := by fun_prop
  have hGsin : SmoothOpen (fun z θ => Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) :=
    SmoothOpen.sep_mul hGsSm hsin2
  have hSso : SmoothOpen (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) := smoothOpen_add hΨso hGsin
  have hGbSin : SmoothOpen (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) :=
    SmoothOpen_GbarSin α F Ψ hα hrel hGsSm hΨso hSso
  have hFstarSin : SmoothOpen (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) :=
    SmoothOpen.sep_mul hFstSm hsin2
  have hWso : SmoothOpen (Work.Elliptic.EllResid α F Ψ) := by
    refine (smoothOpen_sub hSso hGbSin).congr ?_
    intro z θ hz hθ1 hθ2
    show (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
        - Work.Elliptic.Gbar α F z * Real.sin (2 * θ)
      = Work.Elliptic.EllResid α F Ψ z θ
    simp only [Work.Elliptic.EllResid, Work.Elliptic.Gsing, Work.Elliptic.Gstar]
    ring
  -- ## the imported memberships
  have hMemFS : Work.Spaces.HkMem α k
      (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) :=
    (hFS α F Ψ hα hα4 hHyp).1
  have hMemGb : Work.Spaces.HkMem α k
      (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) :=
    (hGb α F Ψ hα hα4 hHyp).1
  have hGbnorm : Work.Spaces.HkNorm α k
      (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) ≤ C3 * A := by
    have h := (hGb α F Ψ hα hα4 hHyp).2
    rw [← hG, ← hA] at h
    exact h
  obtain ⟨hMemW2, hW2sm⟩ := Cert.HkMem_pthIter2_EllResid k hk α F Ψ hα hα4 hHyp hOrth
  -- ## the imported estimates
  obtain ⟨hMemV, hMemZ2V, hVbound⟩ := hSH α F Ψ hα hα4 hHyp hOrth
  obtain ⟨hMemDzV, hAGMv⟩ := hAGM α (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) hα hα1 hSso.forall hMemV hMemZ2V
  have hQbound : α * Q ≤ C1 * (P + R) := by
    have h := hAGMv
    rw [← hQ, ← hP, ← hR] at h
    exact h
  have hPbound : P ≤ C2 * (A + E + D) := by
    have h := hVbound
    rw [← hP, ← hA, ← hE, ← hD] at h
    exact h
  have hGbound : G ≤ C3 * A := hGbnorm
  have hSbound : S ≤ C4 * A := by
    have h := (hFS α F Ψ hα hα4 hHyp).2
    rw [← hS, ← hA] at h
    exact h
  -- ## the transfer `∂_θθV = ∂_θθW - 4(Ḡ sin 2θ)`
  have hEbound : E ≤ 2 * (Bg + 4 * G) := by
    have hsq : Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)))
        = Work.Spaces.HkSq α k
            (fun z θ => Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ) z θ
              + (-4) * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ))) :=
      HkSq_congr_open α k (fun z θ hz hθ1 hθ2 => by
        rw [pthIter_two_Vf α F Ψ hWso hGbSin hz ⟨hθ1, hθ2⟩])
    have hnormeq : Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)))
        = Work.Spaces.HkNorm α k
            (fun z θ => Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ) z θ
              + (-4) * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ))) := by
      rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, hsq]
    have hsm4 : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry
        (fun z θ => (-4) * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ))))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := (hGbSin.const_mul' (-4)).forall
    have hm4 : Work.Spaces.HkMem α k
        (fun z θ => (-4) * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ))) :=
      Work.FTS.LocData.HkMem_const_mul α k (-4) hMemGb
    have hsplit := HkNorm_add_fts α k hW2sm hsm4 hMemW2 hm4
    have hc : Work.Spaces.HkNorm α k
        (fun z θ => (-4) * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ)))
        = 4 * Work.Spaces.HkNorm α k
            (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) := by
      rw [HkNorm_const_mul α k (-4) (f := fun z θ =>
        Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) hGbSin.forall]
      norm_num
    have hs2 : Real.sqrt 2 ≤ 2 := by
      have h : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have h0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      nlinarith
    have hmain : Work.Spaces.HkNorm α k
        (fun z θ => Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ) z θ
          + (-4) * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ)))
        ≤ 2 * (Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ))
          + 4 * Work.Spaces.HkNorm α k
              (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ))) := by
      have hn : 0 ≤ Work.Spaces.HkNorm α k
          (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ))
          + 4 * Work.Spaces.HkNorm α k
              (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) := by
        have h1 := Work.Spaces.HkNorm_nonneg α k
          (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ))
        have h2 := Work.Spaces.HkNorm_nonneg α k
          (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ))
        linarith
      calc Work.Spaces.HkNorm α k
            (fun z θ => Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ) z θ
              + (-4) * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ)))
          ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k
              (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ))
            + Work.Spaces.HkNorm α k
              (fun z θ => (-4) * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ)))) := hsplit
        _ = Real.sqrt 2 * (Work.Spaces.HkNorm α k
              (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ))
            + 4 * Work.Spaces.HkNorm α k
              (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ))) := by rw [hc]
        _ ≤ 2 * (Work.Spaces.HkNorm α k
              (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ))
            + 4 * Work.Spaces.HkNorm α k
              (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ))) :=
            mul_le_mul_of_nonneg_right hs2 hn
    calc E = Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ))) := hE.symm
      _ = Work.Spaces.HkNorm α k
            (fun z θ => Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ) z θ
              + (-4) * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ))) := hnormeq
      _ ≤ 2 * (Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ))
            + 4 * Work.Spaces.HkNorm α k
                (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ))) := hmain
      _ = 2 * (Bg + 4 * G) := by rw [← hB, ← hG]
  -- ## the transfer for `α²z²∂_zzV` and the bound on `R`
  have hRbound : R ≤ 2 * D + (8 * C4 + 53 * C3) * A := by
    have hcm : Work.Spaces.HkNorm α k
          (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ))
        = α ^ 2 * Work.Spaces.HkNorm α k
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ) := by
      rw [HkNorm_const_mul α k (α ^ 2) (f := fun z θ =>
        z ^ 2 * Work.Spaces.pzIter 2 (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ) ((hSso.pzIter 2).zsq_mul).forall,
        abs_of_nonneg (sq_nonneg α)]
    have hsq : Work.Spaces.HkSq α k
          (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ))
        = Work.Spaces.HkSq α k
          (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
            + (15 / 4) * (Work.Elliptic.Fstar F z * Real.sin (2 * θ))
            + (25 + 5 * α) * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ))) :=
      HkSq_congr_open α k (fun z θ hz hθ1 hθ2 =>
        zsq_pzIter_two_Vf α F Ψ hα hΨso hGsin hSso hGderiv hGode hrel hz ⟨hθ1, hθ2⟩)
    have h3 := HkSq_add3_le α k
      (f := fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
      (g := fun z θ => (15 / 4) * (Work.Elliptic.Fstar F z * Real.sin (2 * θ)))
      (h := fun z θ => (25 + 5 * α) * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ)))
      ((hΨso.pzIter 2).zsq_mul.const_mul' (α ^ 2))
      (hFstarSin.const_mul' (15 / 4))
      (hGbSin.const_mul' (25 + 5 * α))
      (Work.FTS.LocData.HkMem_const_mul α k (α ^ 2) hHyp.memZ2)
      (Work.FTS.LocData.HkMem_const_mul α k (15 / 4) hMemFS)
      (Work.FTS.LocData.HkMem_const_mul α k (25 + 5 * α) hMemGb)
    have hSq1 : Work.Spaces.HkSq α k
          (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
        = (α ^ 2) ^ 2 * Work.Spaces.HkSq α k
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
      Work.FTS.LocData.HkSq_const_mul α k (α ^ 2) hHyp.memZ2
    have hSq2 : Work.Spaces.HkSq α k
          (fun z θ => (15 / 4) * (Work.Elliptic.Fstar F z * Real.sin (2 * θ)))
        = (15 / 4) ^ 2 * Work.Spaces.HkSq α k
            (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) :=
      Work.FTS.LocData.HkSq_const_mul α k (15 / 4) hMemFS
    have hSq3 : Work.Spaces.HkSq α k
          (fun z θ => (25 + 5 * α) * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ)))
        = (25 + 5 * α) ^ 2 * Work.Spaces.HkSq α k
            (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) :=
      Work.FTS.LocData.HkSq_const_mul α k (25 + 5 * α) hMemGb
    calc R = α ^ 2 * Work.Spaces.HkNorm α k
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ) := hR.symm
      _ = Work.Spaces.HkNorm α k
            (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ)) := hcm.symm
      _ = Real.sqrt (Work.Spaces.HkSq α k
            (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ))) := rfl
      _ = Real.sqrt (Work.Spaces.HkSq α k
            (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
              + (15 / 4) * (Work.Elliptic.Fstar F z * Real.sin (2 * θ))
              + (25 + 5 * α) * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ)))) := by
          rw [hsq]
      _ ≤ Real.sqrt (4 * Work.Spaces.HkSq α k
              (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
            + 4 * Work.Spaces.HkSq α k
              (fun z θ => (15 / 4) * (Work.Elliptic.Fstar F z * Real.sin (2 * θ)))
            + 2 * Work.Spaces.HkSq α k
              (fun z θ => (25 + 5 * α) * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ)))) :=
          Real.sqrt_le_sqrt h3
      _ ≤ 2 * Real.sqrt (Work.Spaces.HkSq α k
              (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)))
            + 2 * Real.sqrt (Work.Spaces.HkSq α k
              (fun z θ => (15 / 4) * (Work.Elliptic.Fstar F z * Real.sin (2 * θ))))
            + 2 * Real.sqrt (Work.Spaces.HkSq α k
              (fun z θ => (25 + 5 * α) * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ)))) :=
          sqrt_four_add_le _ _ _ (Work.Spaces.HkSq_nonneg α k _)
            (Work.Spaces.HkSq_nonneg α k _) (Work.Spaces.HkSq_nonneg α k _)
      _ = 2 * Work.Spaces.HkNorm α k
              (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
            + 2 * Work.Spaces.HkNorm α k
              (fun z θ => (15 / 4) * (Work.Elliptic.Fstar F z * Real.sin (2 * θ)))
            + 2 * Work.Spaces.HkNorm α k
              (fun z θ => (25 + 5 * α) * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ))) := rfl
      _ = 2 * (α ^ 2 * Work.Spaces.HkNorm α k
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
            + 2 * ((15 / 4) * Work.Spaces.HkNorm α k
              (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)))
            + 2 * ((25 + 5 * α) * Work.Spaces.HkNorm α k
              (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ))) := by
          rw [HkNorm_const_mul α k (α ^ 2) (f := fun z θ =>
                z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ((hΨso.pzIter 2).zsq_mul).forall,
              HkNorm_const_mul α k (15 / 4) (f := fun z θ =>
                Work.Elliptic.Fstar F z * Real.sin (2 * θ)) hFstarSin.forall,
              HkNorm_const_mul α k (25 + 5 * α) (f := fun z θ =>
                Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) hGbSin.forall,
              abs_of_nonneg (sq_nonneg α), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 15 / 4),
              abs_of_nonneg (by linarith : (0 : ℝ) ≤ 25 + 5 * α)]
      _ ≤ 2 * D + (8 * C4 + 53 * C3) * A := by
          have hS0 : 0 ≤ S := by rw [hS]; exact Work.Spaces.HkNorm_nonneg α k _
          have hG0 : 0 ≤ G := by rw [hG]; exact Work.Spaces.HkNorm_nonneg α k _
          have hA0 : 0 ≤ A := by rw [hA]; exact Work.Spaces.HkNorm_nonneg α k F
          have hD0 : 0 ≤ D := by
            rw [hD]
            exact mul_nonneg (sq_nonneg α) (Work.Spaces.HkNorm_nonneg α k _)
          nlinarith [hSbound, hGbound, hα, hα4, hS0, hG0, hA0, hD0]
  -- ## the bound on `α²|D_z²V|`
  have hD2bound : α ^ 2 * Work.Spaces.HkNorm α k (Work.Spaces.DzIter 2 (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)))
      ≤ 2 * R + (1 / 2) * (α * Q) := by
    have hsq : Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)))
        = Work.Spaces.HkSq α k
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
              + Work.Spaces.Dz (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ) :=
      HkSq_congr_open α k (fun z θ hz hθ1 hθ2 =>
        DzIter2_eq_zsq_pzIter2_add_Dz (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) hSso hz ⟨hθ1, hθ2⟩)
    have hnormeq : Work.Spaces.HkNorm α k (Work.Spaces.DzIter 2 (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)))
        = Work.Spaces.HkNorm α k
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
              + Work.Spaces.Dz (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ) := by
      rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, hsq]
    have hsplit := HkNorm_add_fts α k ((hSso.pzIter 2).zsq_mul).forall (hSso.Dz).forall
      hMemZ2V hMemDzV
    have hs2 : Real.sqrt 2 ≤ 2 := by
      have h : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have h0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      nlinarith
    have hQ0 : 0 ≤ Q := by rw [hQ]; exact Work.Spaces.HkNorm_nonneg α k _
    calc α ^ 2 * Work.Spaces.HkNorm α k (Work.Spaces.DzIter 2 (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)))
        = α ^ 2 * Work.Spaces.HkNorm α k
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
              + Work.Spaces.Dz (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ) := by rw [hnormeq]
      _ ≤ α ^ 2 * (Real.sqrt 2 * (Work.Spaces.HkNorm α k
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ)
            + Work.Spaces.HkNorm α k (Work.Spaces.Dz (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ))))) :=
          mul_le_mul_of_nonneg_left hsplit (sq_nonneg α)
      _ ≤ 2 * R + (1 / 2) * (α * Q) := by
          set X : ℝ := Work.Spaces.HkNorm α k
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ) with hX
          set Y : ℝ := Work.Spaces.HkNorm α k
            (Work.Spaces.Dz (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ))) with hY
          have hX0 : 0 ≤ X := by
            rw [hX]; exact Work.Spaces.HkNorm_nonneg α k _
          have hY0 : 0 ≤ Y := by
            rw [hY]; exact Work.Spaces.HkNorm_nonneg α k _
          have hRX : R = α ^ 2 * X := hR
          have hQY : Q = Y := hQ
          have hXY : Real.sqrt 2 * (X + Y) ≤ 2 * (X + Y) :=
            mul_le_mul_of_nonneg_right hs2 (by linarith)
          have hαY : 0 ≤ α * Y := mul_nonneg (le_of_lt hα) hY0
          have hprod : 2 * α * (α * Y) ≤ (1 / 2) * (α * Y) := by
            have h1 : 2 * α ≤ 1 / 2 := by linarith
            exact mul_le_mul_of_nonneg_right h1 hαY
          have hkey2 : α ^ 2 * (Real.sqrt 2 * (X + Y)) ≤ 2 * (R + α ^ 2 * Q) := by
            rw [hRX, hQY]
            have h1 : α ^ 2 * (Real.sqrt 2 * (X + Y)) ≤ α ^ 2 * (2 * (X + Y)) :=
              mul_le_mul_of_nonneg_left hXY (sq_nonneg α)
            have h2 : α ^ 2 * (2 * (X + Y)) = 2 * α ^ 2 * X + 2 * α ^ 2 * Y := by ring
            have h3 : 2 * α ^ 2 * Y ≤ (1 / 2) * (α * Y) := by
              have h4 : α ^ 2 * Y = α * (α * Y) := by ring
              linarith [h4, hprod]
            linarith [h1, h2, h3]
          have hfin2 : 2 * (R + α ^ 2 * Q) ≤ 2 * R + (1 / 2) * (α * Q) := by
            rw [hRX, hQY]
            have h4 : α ^ 2 * Y = α * (α * Y) := by ring
            linarith [h4, hprod]
          linarith [hkey2, hfin2]
  -- ## the final arithmetic
  have hLHS : α ^ 2 * Work.Spaces.HkNorm α k (Work.Spaces.DzIter 2 (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)))
        + 5 * α * Work.Spaces.HkNorm α k (Work.Spaces.Dz (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)))
      ≤ 2 * R + (11 / 2) * (α * Q) := by
    have h5 : 5 * α * Work.Spaces.HkNorm α k (Work.Spaces.Dz (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ))) = 5 * (α * Q) := by
      rw [← hQ]; ring
    linarith [hD2bound, h5]
  have hstep : 2 * R + (11 / 2) * (α * Q) ≤ straightC C1 C2 C3 C4 * (A + Bg + D) := by
    have hA0 : 0 ≤ A := by rw [hA]; exact Work.Spaces.HkNorm_nonneg α k F
    have hB0 : 0 ≤ Bg := by rw [hB]; exact Work.Spaces.HkNorm_nonneg α k _
    have hD0 : 0 ≤ D := by
      rw [hD]; exact mul_nonneg (sq_nonneg α) (Work.Spaces.HkNorm_nonneg α k _)
    have hP0 : 0 ≤ P := by rw [hP]; exact Work.Spaces.HkNorm_nonneg α k _
    have hQ0 : 0 ≤ Q := by rw [hQ]; exact Work.Spaces.HkNorm_nonneg α k _
    have hR0 : 0 ≤ R := by
      rw [hR]; exact mul_nonneg (sq_nonneg α) (Work.Spaces.HkNorm_nonneg α k _)
    have hE0 : 0 ≤ E := by rw [hE]; exact Work.Spaces.HkNorm_nonneg α k _
    have hG0 : 0 ≤ G := by rw [hG]; exact Work.Spaces.HkNorm_nonneg α k _
    have hE' : E ≤ 2 * Bg + 8 * G := by linarith [hEbound]
    have hP' : P ≤ C2 * (A + E + D) := hPbound
    have hPR : P ≤ C2 * (A + 2 * Bg + 8 * G + D) := by
      nlinarith [hP', hE', hC2pos]
    have hPG : P ≤ C2 * (A + 2 * Bg + 8 * C3 * A + D) := by
      nlinarith [hPR, hGbound, hC2pos, hA0, hB0, hD0, hG0]
    have hR' : R ≤ 2 * D + (8 * C4 + 53 * C3) * A := hRbound
    have hPRA : P + R ≤ C2 * (A + 2 * Bg + 8 * C3 * A + D)
        + (2 * D + (8 * C4 + 53 * C3) * A) := by linarith [hPG, hR']
    have hkey : 2 * R + (11 / 2) * (α * Q)
        ≤ 2 * (2 * D + (8 * C4 + 53 * C3) * A)
          + (11 / 2) * C1 * (C2 * (A + 2 * Bg + 8 * C3 * A + D)
            + (2 * D + (8 * C4 + 53 * C3) * A)) := by
      have h1 : (11 / 2) * (α * Q) ≤ (11 / 2) * (C1 * (P + R)) := by
        nlinarith [hQbound]
      nlinarith [h1, hR', hPRA, hC1pos]
    have hfin : 2 * (2 * D + (8 * C4 + 53 * C3) * A)
          + (11 / 2) * C1 * (C2 * (A + 2 * Bg + 8 * C3 * A + D)
            + (2 * D + (8 * C4 + 53 * C3) * A))
        ≤ straightC C1 C2 C3 C4 * (A + Bg + D) := by
      rw [straightC]
      have hc5 : 0 ≤ 8 * C4 + 53 * C3 := by linarith
      have hS1 : C2 * (A + 2 * Bg + 8 * C3 * A + D)
          ≤ C2 * (2 + 8 * C3) * (A + Bg + D) := by
        have hnn : 0 ≤ C2 * (A + 8 * C3 * Bg + (1 + 8 * C3) * D) := by
          have h1 : 0 ≤ 8 * C3 * Bg := mul_nonneg (by linarith) hB0
          have h2 : 0 ≤ (1 + 8 * C3) * D := mul_nonneg (by linarith) hD0
          have h3 : 0 ≤ A + 8 * C3 * Bg + (1 + 8 * C3) * D := by linarith
          exact mul_nonneg (le_of_lt hC2pos) h3
        nlinarith [hnn]
      have hS2 : 2 * D + (8 * C4 + 53 * C3) * A
          ≤ (2 + (8 * C4 + 53 * C3)) * (A + Bg + D) := by
        nlinarith [hA0, hB0, hD0, hc5]
      have hS3 : 2 * (2 * D + (8 * C4 + 53 * C3) * A)
          ≤ (4 + 2 * (8 * C4 + 53 * C3)) * (A + Bg + D) := by
        nlinarith [hS2]
      have hS4 : (11 / 2) * C1 * (C2 * (A + 2 * Bg + 8 * C3 * A + D)
            + (2 * D + (8 * C4 + 53 * C3) * A))
          ≤ (11 / 2) * C1 * (C2 * (2 + 8 * C3) + 2 + (8 * C4 + 53 * C3))
              * (A + Bg + D) := by
        have h11 : 0 ≤ (11 / 2 : ℝ) * C1 * (A + Bg + D) := by
          have hABD : 0 ≤ A + Bg + D := by linarith
          positivity
        have hsum : C2 * (A + 2 * Bg + 8 * C3 * A + D)
            + (2 * D + (8 * C4 + 53 * C3) * A)
            ≤ (C2 * (2 + 8 * C3) + 2 + (8 * C4 + 53 * C3)) * (A + Bg + D) := by
          have hS2' : 2 * D + (8 * C4 + 53 * C3) * A
              ≤ (2 + (8 * C4 + 53 * C3)) * (A + Bg + D) := hS2
          have h1 : C2 * (2 + 8 * C3) * (A + Bg + D)
              ≤ (C2 * (2 + 8 * C3) + 2 + (8 * C4 + 53 * C3)) * (A + Bg + D) := by
            have hABD : 0 ≤ A + Bg + D := by linarith
            nlinarith [hABD, hc5]
          linarith [hS1, hS2', h1]
        calc (11 / 2) * C1 * (C2 * (A + 2 * Bg + 8 * C3 * A + D)
              + (2 * D + (8 * C4 + 53 * C3) * A))
            ≤ (11 / 2) * C1 * ((C2 * (2 + 8 * C3) + 2 + (8 * C4 + 53 * C3))
                * (A + Bg + D)) := by
              have h11' : 0 ≤ (11 / 2 : ℝ) * C1 := by linarith
              exact mul_le_mul_of_nonneg_left hsum h11'
          _ = (11 / 2) * C1 * (C2 * (2 + 8 * C3) + 2 + (8 * C4 + 53 * C3))
                * (A + Bg + D) := by ring
      have hcoef : (4 + 2 * (8 * C4 + 53 * C3))
            + (11 / 2) * C1 * (C2 * (2 + 8 * C3) + 2 + (8 * C4 + 53 * C3))
          ≤ 4 + 2 * (8 * C4 + 53 * C3)
            + (11 / 2) * C1 * (3 * C2 * (1 + 8 * C3) + 2 + (8 * C4 + 53 * C3)) := by
        have hle : C2 * (2 + 8 * C3) ≤ 3 * C2 * (1 + 8 * C3) := by
          nlinarith [hC2pos, hC3pos]
        have h11 : 0 ≤ (11 / 2 : ℝ) * C1 := by linarith
        have hmul : (11 / 2) * C1 * (C2 * (2 + 8 * C3))
            ≤ (11 / 2) * C1 * (3 * C2 * (1 + 8 * C3)) :=
          mul_le_mul_of_nonneg_left hle h11
        linarith [hmul]
      have hABD : 0 ≤ A + Bg + D := by linarith
      nlinarith [hS3, hS4, hcoef, hABD]
    linarith [hkey, hfin]
  calc α ^ 2 * Work.Spaces.HkNorm α k (Work.Spaces.DzIter 2 (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)))
        + 5 * α * Work.Spaces.HkNorm α k (Work.Spaces.Dz (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)))
      ≤ 2 * R + (11 / 2) * (α * Q) := hLHS
    _ ≤ straightC C1 C2 C3 C4 * (A + Bg + D) := hstep
    _ = straightC C1 C2 C3 C4 * (Work.Spaces.HkNorm α k F
          + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ))
          + α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) := by
        rw [hA, hB, hD]

end Work.FTS.EllipticEst
