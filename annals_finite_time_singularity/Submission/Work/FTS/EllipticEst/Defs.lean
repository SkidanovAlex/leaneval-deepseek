/-
Copyright: work module for the Elgindi finite-time singularity project.

# The elliptic chapter of §'Elliptic Regularity Estimates': conventions and vocabulary

This module is the entry point of the subproject `Submission/Work/FTS/EllipticEst/`, the
re-audit and restatement of §'Elliptic Regularity Estimates' (LaTeX lines 709--1039) of

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
  incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021).

Everything *definitional* lives in `Submission/Work/Elliptic/Defs.lean` (`bslOp`, `Lzero`,
`Fstar`, `OrthCond`, `L12`, `Gstar`, `Gbar`, `Gsing`, `orthSource`, `EllResid`, `IsBslSol`,
`IsEstData`) and is imported here, not redefined.  The three operators `Uop`, `Vop`, `Rop` of
(Relations) (tex 1320) and the unweighted `L²` norm live in
`Submission/Work/Elliptic/Estimates.lean`, the module whose nine `sorry`s this chapter replaces;
because that module carries `sorry`s, its definitions are **duplicated** here, definitionally
unchanged, so that a caller can use this chapter without inheriting `sorryAx`.  The duplicates
are `rfl`-equal to the originals, so rewiring a consumer from one to the other is definitional.

## Convention pinned by this chapter (the sign)

The elliptic law of §'Elliptic Regularity Estimates' is `L(Ψ) = F` (paper (PolarBSL), tex 716),
with `L = bslOp α`.  The *vorticity* interpretation of `F` carries a sign: for the stream
function `ψ = ρ²Ψ(ρ^α,θ)` of the no-swirl field `Work.Cyl.psiField ψ`, the delivered curl
identity `Work.Cyl.vorticity_psiField` together with the polar reduction
`Work.Elliptic.cylOp_polar` gives

  `vorticity (psiField (ρ²Ψ(ρ^α,θ))) = -(bslOp α Ψ (ρ^α) θ) • e_θ`,

i.e. **the `e_θ`-coefficient `Ω` of the vorticity and the source `F` of (PolarBSL) are related by
`F = -Ω`.**  This chapter keeps the paper's convention `L(Ψ) = F` (so that every statement of
`Work.Elliptic.Defs` and of `Work.Construction` applies verbatim) and records the bridge in
`VorticityBridge.lean`.  The sign is *harmless for the estimates*: `IsBslSol_neg`, `L2Norm_neg`,
`HkNorm_neg`, `OrthCond_neg`, `EllResid_neg` below say that every estimate of the chapter is
invariant under `(F, Ψ) ↦ (-F, -Ψ)`; a caller who has the vorticity profile `Ω` applies the
estimates to `F = -Ω` and `Ψ = -Φ`.

## The audit corrections recorded here

1. *(sign)* see above: `Work.Construction.StatEqPhi` and this chapter use `bslOp α Φ = F`; the
   honest law in terms of the vorticity is `bslOp α Φ = -Ω`.  Both conventions give the *same*
   estimates, by the invariance lemmas of this file.
2. *(decay for the integrations by parts)* The nine statements of
   `Work.Elliptic.Estimates` take `IsBslSol α F Ψ` (equation, Dirichlet data, pointwise decay
   `Ψ → 0` at `z → ∞`) and `Work.Spaces.SmoothNbhd Ψ`.  Neither hypothesis controls the
   boundary terms `z ^ 2 * ∂_zΨ * Ψ` and `z * Ψ ^ 2` at `z → ∞`, and the proofs of the four
   estimates integrate by parts in `z`
   (`MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul`), where exactly those terms must vanish.
   The corrected statements therefore carry the named hypothesis `ZDecay Ψ` defined below.
3. *(honesty of the energy identities)* `Work.Spaces.L2Sq` and `Work.Spaces.HkSq` are
   (iterated) integrals, and a non-integrable nonnegative integral is `0` by the totalised
   convention, so an *identity* between two integrals needs both sides honest.  The corrected
   statements carry `Work.Spaces.HkMem` on the left-hand quantities as well, which is exactly
   the assertion that the corresponding `H^k`-(semi)norms are honest numbers.
4. *(the `OrthCond Ψ` hypothesis)* `OrthCond Ψ` (i.e. `Fstar Ψ ≡ 0`) is *not* a restriction of
   the paper's setting: it is Step 1 of the proof of Proposition `prop:L2` (tex 740--750) and is
   proved in `Submission/Work/Elliptic/PsiStar_zero.lean` from `OrthCond F` and the decay of the
   solution.  It is kept as an explicit hypothesis, as in the paper's Fourier step.
-/
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.Interval.Basic
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.ProductTools

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The unweighted `L²` norm (definitionally the one of `Work.Elliptic.Estimates`) -/

/-- The unweighted `L²` norm `|g|_{L²}` of `g` over `[0,∞) × [0,π/2]` with the measure `dz dθ`
(the Warning of §Notation: *not* `r dr dθ`).  Definitionally equal to
`Work.Elliptic.L2Norm`. -/
def L2Norm (g : ℝ → ℝ → ℝ) : ℝ := Real.sqrt (Work.Spaces.L2Sq g)

theorem L2Norm_nonneg (g : ℝ → ℝ → ℝ) : 0 ≤ L2Norm g := Real.sqrt_nonneg _

theorem L2Norm_eq_sqrt (g : ℝ → ℝ → ℝ) : L2Norm g = Real.sqrt (Work.Spaces.L2Sq g) := rfl

theorem L2Sq_congr {f g : ℝ → ℝ → ℝ} (h : ∀ z θ, f z θ = g z θ) :
    Work.Spaces.L2Sq f = Work.Spaces.L2Sq g := by
  simp only [Work.Spaces.L2Sq]
  refine setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
  exact setIntegral_congr_fun measurableSet_Icc fun θ _ => by rw [h z θ]

theorem L2Norm_congr {f g : ℝ → ℝ → ℝ} (h : ∀ z θ, f z θ = g z θ) : L2Norm f = L2Norm g := by
  rw [L2Norm_eq_sqrt, L2Norm_eq_sqrt, L2Sq_congr h]

theorem L2Sq_neg (g : ℝ → ℝ → ℝ) : Work.Spaces.L2Sq (-g) = Work.Spaces.L2Sq g := by
  simp only [Work.Spaces.L2Sq]
  refine setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
  refine setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
  simp only [Pi.neg_apply]
  ring

theorem L2Norm_neg (g : ℝ → ℝ → ℝ) : L2Norm (-g) = L2Norm g := by
  rw [L2Norm_eq_sqrt, L2Norm_eq_sqrt, L2Sq_neg]

theorem L2Sq_zero : Work.Spaces.L2Sq (fun _ _ => (0 : ℝ)) = 0 := by
  simp [Work.Spaces.L2Sq]

theorem L2Norm_zero : L2Norm (fun _ _ => (0 : ℝ)) = 0 := by
  rw [L2Norm_eq_sqrt, L2Sq_zero, Real.sqrt_zero]

/-! ## The operators `U`, `V`, `ℛ` of §Modulation (tex 1320) -/

/-- `U(Ψ) := -3Ψ - α z ∂_z Ψ` (paper (Relations), tex 1320): the coefficient of `∂_θΩ`. -/
def Uop (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -3 * Ψ z θ - α * z * Work.Spaces.pz Ψ z θ

/-- `V(Ψ) := ∂_θΨ - tan θ · Ψ`: the coefficient of `α z ∂_zΩ`. -/
def Vop (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.Spaces.pth Ψ z θ - Real.tan θ * Ψ z θ

/-- `ℛ(Ψ) := (1/cos θ)(2 sin θ · Ψ + α sin θ · z ∂_zΨ + cos θ · ∂_θΨ)`: the coefficient of
`Ω` in the self-similar vorticity equation (paper (Relations), tex 1320). -/
def Rop (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (2 * Real.sin θ * Ψ z θ + α * Real.sin θ * z * Work.Spaces.pz Ψ z θ
    + Real.cos θ * Work.Spaces.pth Ψ z θ) / Real.cos θ

/-! ## The calculus of pointwise negation

The totalised `deriv` is odd (`deriv.neg`), so every operator of the chapter commutes with
pointwise negation; these lemmas are the formal content of "the estimates are sign-invariant". -/

theorem deriv_neg_apply (f : ℝ → ℝ) (x : ℝ) : deriv (fun y => -(f y)) x = -deriv f x := by
  simpa using deriv.neg (f := f) (x := x)

theorem pz_neg (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pz (-f) = fun z θ => -(Work.Spaces.pz f z θ) := by
  funext z θ
  simp only [Work.Spaces.pz, Pi.neg_apply]
  exact deriv_neg_apply _ _

theorem pth_neg (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pth (-f) = fun z θ => -(Work.Spaces.pth f z θ) := by
  funext z θ
  simp only [Work.Spaces.pth, Pi.neg_apply]
  exact deriv_neg_apply _ _

theorem pzIter_neg (f : ℝ → ℝ → ℝ) (n : ℕ) :
    Work.Spaces.pzIter n (-f) = fun z θ => -(Work.Spaces.pzIter n f z θ) := by
  induction n with
  | zero => funext z θ; simp
  | succ n ih =>
      calc Work.Spaces.pzIter (n + 1) (-f)
          = Work.Spaces.pz (Work.Spaces.pzIter n (-f)) := Work.Spaces.pzIter_succ n (-f)
        _ = Work.Spaces.pz (fun z θ => -(Work.Spaces.pzIter n f z θ)) := by rw [ih]
        _ = fun z θ => -(Work.Spaces.pz (Work.Spaces.pzIter n f) z θ) := pz_neg _
        _ = fun z θ => -(Work.Spaces.pzIter (n + 1) f z θ) := by
              rw [Work.Spaces.pzIter_succ]

theorem pthIter_neg (f : ℝ → ℝ → ℝ) (n : ℕ) :
    Work.Spaces.pthIter n (-f) = fun z θ => -(Work.Spaces.pthIter n f z θ) := by
  induction n with
  | zero => funext z θ; simp
  | succ n ih =>
      calc Work.Spaces.pthIter (n + 1) (-f)
          = Work.Spaces.pth (Work.Spaces.pthIter n (-f)) := Work.Spaces.pthIter_succ n (-f)
        _ = Work.Spaces.pth (fun z θ => -(Work.Spaces.pthIter n f z θ)) := by rw [ih]
        _ = fun z θ => -(Work.Spaces.pth (Work.Spaces.pthIter n f) z θ) := pth_neg _
        _ = fun z θ => -(Work.Spaces.pthIter (n + 1) f z θ) := by
              rw [Work.Spaces.pthIter_succ]

theorem Dz_neg (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dz (-f) = fun z θ => -(Work.Spaces.Dz f z θ) := by
  funext z θ
  simp only [Work.Spaces.Dz, pz_neg, Pi.neg_apply]
  ring

theorem Dth_neg (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dth (-f) = fun z θ => -(Work.Spaces.Dth f z θ) := by
  funext z θ
  simp only [Work.Spaces.Dth, pth_neg, Pi.neg_apply]
  ring

theorem DzIter_neg (f : ℝ → ℝ → ℝ) (n : ℕ) :
    Work.Spaces.DzIter n (-f) = fun z θ => -(Work.Spaces.DzIter n f z θ) := by
  induction n with
  | zero => funext z θ; simp
  | succ n ih =>
      calc Work.Spaces.DzIter (n + 1) (-f)
          = Work.Spaces.Dz (Work.Spaces.DzIter n (-f)) := Work.Spaces.DzIter_succ n (-f)
        _ = Work.Spaces.Dz (fun z θ => -(Work.Spaces.DzIter n f z θ)) := by rw [ih]
        _ = fun z θ => -(Work.Spaces.Dz (Work.Spaces.DzIter n f) z θ) := Dz_neg _
        _ = fun z θ => -(Work.Spaces.DzIter (n + 1) f z θ) := by
              rw [Work.Spaces.DzIter_succ]

theorem DthIter_neg (f : ℝ → ℝ → ℝ) (n : ℕ) :
    Work.Spaces.DthIter n (-f) = fun z θ => -(Work.Spaces.DthIter n f z θ) := by
  induction n with
  | zero => funext z θ; simp
  | succ n ih =>
      calc Work.Spaces.DthIter (n + 1) (-f)
          = Work.Spaces.Dth (Work.Spaces.DthIter n (-f)) := Work.Spaces.DthIter_succ n (-f)
        _ = Work.Spaces.Dth (fun z θ => -(Work.Spaces.DthIter n f z θ)) := by rw [ih]
        _ = fun z θ => -(Work.Spaces.Dth (Work.Spaces.DthIter n f) z θ) := Dth_neg _
        _ = fun z θ => -(Work.Spaces.DthIter (n + 1) f z θ) := by
              rw [Work.Spaces.DthIter_succ]

theorem mixed_neg (f : ℝ → ℝ → ℝ) (j i : ℕ) :
    Work.Spaces.mixed j i (-f) = fun z θ => -(Work.Spaces.mixed j i f z θ) := by
  have h1 := DthIter_neg f i
  have h2 := DzIter_neg (Work.Spaces.DthIter i f) j
  simp only [Work.Spaces.mixed]
  rw [h1]
  exact h2

/-! ## The boundary decay used by the integrations by parts in `z` -/

/-- The decay hypothesis at `z → ∞` that makes the integration by parts in the radial variable
of the elliptic section legitimate: for every angle `θ ∈ [0,π/2]`,

  `z ^ 2 * ((Ψ z θ) ^ 2 + (∂_zΨ z θ) ^ 2 + (∂_zzΨ z θ) ^ 2 + (∂_θΨ z θ) ^ 2
      + (∂_θθΨ z θ) ^ 2) → 0`,

so that every boundary term of the form `z ^ 2 * ∂_zΨ * Ψ` or `z * Ψ ^ 2` (and their analogues
for the derivatives used in the proof) vanishes at infinity.  Every function of `z`-decay
`O(z ^ (-1-ε))`, uniformly in `θ`, satisfies this; in particular every compactly supported
function. -/
def ZDecay (Ψ : ℝ → ℝ → ℝ) : Prop :=
  ∀ θ ∈ Work.Spaces.Iθ, Tendsto (fun z => z ^ 2 * ((Ψ z θ) ^ 2 + (Work.Spaces.pz Ψ z θ) ^ 2
    + (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 + (Work.Spaces.pth Ψ z θ) ^ 2
    + (Work.Spaces.pthIter 2 Ψ z θ) ^ 2)) atTop (𝓝 0)

theorem ZDecay_of_neg {Ψ : ℝ → ℝ → ℝ} (h : ZDecay Ψ) : ZDecay (-Ψ) := by
  intro θ hθ
  have h1 := h θ hθ
  have hfun : (fun z => z ^ 2 * ((-Ψ) z θ ^ 2 + (Work.Spaces.pz (-Ψ) z θ) ^ 2
        + (Work.Spaces.pzIter 2 (-Ψ) z θ) ^ 2 + (Work.Spaces.pth (-Ψ) z θ) ^ 2
        + (Work.Spaces.pthIter 2 (-Ψ) z θ) ^ 2))
      = fun z => z ^ 2 * ((Ψ z θ) ^ 2 + (Work.Spaces.pz Ψ z θ) ^ 2
        + (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 + (Work.Spaces.pth Ψ z θ) ^ 2
        + (Work.Spaces.pthIter 2 Ψ z θ) ^ 2) := by
    funext z
    simp only [Pi.neg_apply, pz_neg, pth_neg, pzIter_neg, pthIter_neg]
    ring
  rw [hfun]
  exact h1

/-! ## Sign invariance of the vocabulary of the elliptic section -/

theorem Uop_neg (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : Uop α (-Ψ) = fun z θ => -(Uop α Ψ z θ) := by
  funext z θ
  simp only [Uop, pz_neg, Pi.neg_apply]
  ring

theorem Vop_neg (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : Vop α (-Ψ) = fun z θ => -(Vop α Ψ z θ) := by
  funext z θ
  simp only [Vop, pth_neg, Pi.neg_apply]
  ring

theorem Rop_neg (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : Rop α (-Ψ) = fun z θ => -(Rop α Ψ z θ) := by
  funext z θ
  simp only [Rop, pz_neg, pth_neg, Pi.neg_apply]
  ring

/-- `Fstar` is odd in the source. -/
theorem Fstar_neg (F : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Elliptic.Fstar (-F) z = -Work.Elliptic.Fstar F z := by
  simp only [Work.Elliptic.Fstar, Pi.neg_apply]
  rw [show (∫ θ in Work.Spaces.Iθ, -F z θ * Work.Elliptic.sinCos2 θ)
      = ∫ θ in Work.Spaces.Iθ, -(F z θ * Work.Elliptic.sinCos2 θ) from
    setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)]
  rw [integral_neg (f := fun θ => F z θ * Work.Elliptic.sinCos2 θ)
    (μ := volume.restrict Work.Spaces.Iθ)]

/-- The solvability condition is invariant under negation of the source. -/
theorem OrthCond_neg (F : ℝ → ℝ → ℝ) :
    Work.Elliptic.OrthCond (-F) ↔ Work.Elliptic.OrthCond F := by
  constructor
  · intro h z
    have hz := h z
    rw [Fstar_neg] at hz
    linarith
  · intro h z
    rw [Fstar_neg, h z]; ring

/-- `L₁₂` is odd in the source. -/
theorem L12dens_neg (F : ℝ → ℝ → ℝ) (s : ℝ) :
    Work.Elliptic.L12dens (-F) s = -Work.Elliptic.L12dens F s := by
  simp only [Work.Elliptic.L12dens, Pi.neg_apply]
  rw [show (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ * -F s θ / s)
      = ∫ θ in Work.Spaces.Iθ, -(Work.Elliptic.Ktheta θ * F s θ / s) from
    setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)]
  rw [integral_neg (f := fun θ => Work.Elliptic.Ktheta θ * F s θ / s)
    (μ := volume.restrict Work.Spaces.Iθ)]

theorem L12_neg (F : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Elliptic.L12 (-F) z = -Work.Elliptic.L12 F z := by
  have hfun : (fun r => Work.Elliptic.L12dens (-F) r)
      = fun r => -(Work.Elliptic.L12dens F r) := by
    funext r; exact L12dens_neg F r
  simp only [Work.Elliptic.L12]
  rw [hfun, integral_neg (f := fun r => Work.Elliptic.L12dens F r)
    (μ := volume.restrict (Set.Ioi z))]

theorem L12rad_neg (F : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Elliptic.L12rad (-F) z = -Work.Elliptic.L12rad F z := by
  simp only [Work.Elliptic.L12rad]
  rw [show (∫ r in Set.Ioi z, Work.Elliptic.Fstar (-F) r / r)
      = ∫ r in Set.Ioi z, -(Work.Elliptic.Fstar F r / r) from
    setIntegral_congr_fun measurableSet_Ioi (fun r _ => by rw [Fstar_neg]; ring)]
  rw [integral_neg (f := fun r => Work.Elliptic.Fstar F r / r)
    (μ := volume.restrict (Set.Ioi z))]

theorem Gstar_neg (α : ℝ) (F : ℝ → ℝ → ℝ) :
    Work.Elliptic.Gstar α (-F) = fun z => -(Work.Elliptic.Gstar α F z) := by
  funext z
  simp only [Work.Elliptic.Gstar, L12_neg]
  ring

theorem Gbar_neg (α : ℝ) (F : ℝ → ℝ → ℝ) :
    Work.Elliptic.Gbar α (-F) = fun z => -(Work.Elliptic.Gbar α F z) := by
  funext z
  have hfun : (fun s => s ^ ((5 - α) / α) * Work.Elliptic.Fstar (-F) s)
      = fun s => -(s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s) := by
    funext s; rw [Fstar_neg]; ring
  simp only [Work.Elliptic.Gbar, hfun]
  rw [intervalIntegral.integral_neg]
  ring

theorem Gsing_neg (α : ℝ) (F : ℝ → ℝ → ℝ) :
    Work.Elliptic.Gsing α (-F) = fun z => -(Work.Elliptic.Gsing α F z) := by
  funext z
  simp only [Work.Elliptic.Gsing, Gstar_neg, Gbar_neg]
  ring

theorem orthSource_neg (F : ℝ → ℝ → ℝ) :
    Work.Elliptic.orthSource (-F) = fun z θ => -(Work.Elliptic.orthSource F z θ) := by
  funext z θ
  simp only [Work.Elliptic.orthSource, Fstar_neg, Pi.neg_apply]
  ring

/-- The residual of Theorem `RemovingL12` is odd in `(F, Ψ)`. -/
theorem EllResid_neg (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) :
    Work.Elliptic.EllResid α (-F) (-Ψ)
      = fun z θ => -(Work.Elliptic.EllResid α F Ψ z θ) := by
  funext z θ
  simp only [Work.Elliptic.EllResid, Pi.neg_apply, L12_neg]
  ring

/-- The elliptic operator is odd. -/
theorem bslOp_neg (α : ℝ) (Ψ : ℝ → ℝ → ℝ) :
    Work.Elliptic.bslOp α (-Ψ) = fun z θ => -(Work.Elliptic.bslOp α Ψ z θ) := by
  funext z θ
  have h2 : Work.Spaces.pzIter 2 (-Ψ) z θ = -(Work.Spaces.pzIter 2 Ψ z θ) := by
    simpa using congrFun (congrFun (pzIter_neg Ψ 2) z) θ
  have h1 : Work.Spaces.pz (-Ψ) z θ = -(Work.Spaces.pz Ψ z θ) := by
    simpa using congrFun (congrFun (pz_neg Ψ) z) θ
  have ht2 : Work.Spaces.pthIter 2 (-Ψ) z θ = -(Work.Spaces.pthIter 2 Ψ z θ) := by
    simpa using congrFun (congrFun (pthIter_neg Ψ 2) z) θ
  have ht1 : Work.Spaces.pth (fun z θ => Real.tan θ * -Ψ z θ) z θ
      = -(Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ) := by
    have hfun : (fun z θ => Real.tan θ * -Ψ z θ)
        = (fun z θ => -(Real.tan θ * Ψ z θ)) := by
      funext a b; ring
    rw [hfun]
    simp only [Work.Spaces.pth]
    exact deriv_neg_apply (f := fun θ' => Real.tan θ' * Ψ z θ') θ
  simp only [Work.Elliptic.bslOp, Work.Elliptic.Lzero, Pi.neg_apply]
  rw [h2, h1, ht2, ht1]
  ring

/-- `IsBslSol` is invariant under `(F, Ψ) ↦ (-F, -Ψ)`: the sign convention of the source does
not change the class of solutions. -/
theorem IsBslSol_neg (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) :
    Work.Elliptic.IsBslSol α (-F) (-Ψ) ↔ Work.Elliptic.IsBslSol α F Ψ := by
  simp only [Work.Elliptic.IsBslSol, Pi.neg_apply]
  constructor
  · intro h
    refine ⟨fun z hz θ h0 h1 => ?_, fun z => ?_, fun z => ?_, fun θ hθ => ?_⟩
    · have hb := h.1 z hz θ h0 h1
      rw [bslOp_neg] at hb
      simp only [Pi.neg_apply] at hb
      linarith
    · exact neg_eq_zero.mp (h.2.1 z)
    · exact neg_eq_zero.mp (h.2.2.1 z)
    · simpa using (h.2.2.2 θ hθ).neg
  · intro h
    refine ⟨fun z hz θ h0 h1 => ?_, fun z => ?_, fun z => ?_, fun θ hθ => ?_⟩
    · rw [bslOp_neg]
      simp only [Pi.neg_apply]
      rw [h.1 z hz θ h0 h1]
    · simp [h.2.1 z]
    · simp [h.2.2.1 z]
    · simpa using (h.2.2.2 θ hθ).neg

/-! ## `H^k`-norm invariance under negation -/

theorem HkIntegrand_neg (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkIntegrand α k (-f) = Work.Spaces.HkIntegrand α k f := by
  funext z θ
  simp only [Work.Spaces.HkIntegrand, DzIter_neg, mixed_neg]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => ?_)
    (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_)
  · ring
  · split_ifs <;> ring

theorem HkSq_neg (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α k (-f) = Work.Spaces.HkSq α k f := by
  simp only [Work.Spaces.HkSq]
  refine setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
  refine setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
  exact congrFun (congrFun (HkIntegrand_neg α k f) z) θ

theorem HkNorm_neg (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkNorm α k (-f) = Work.Spaces.HkNorm α k f := by
  simp only [Work.Spaces.HkNorm, HkSq_neg]

/-! ## The zero function: `HkIntegrand`, `HkMem`, `L2Mem`, `ZDecay` are inhabited -/

theorem pz_zero_fun : Work.Spaces.pz (0 : ℝ → ℝ → ℝ) = 0 := by
  funext z θ; simp [Work.Spaces.pz]

theorem pth_zero_fun : Work.Spaces.pth (0 : ℝ → ℝ → ℝ) = 0 := by
  funext z θ; simp [Work.Spaces.pth]

theorem pzIter_zero_fun (n : ℕ) : Work.Spaces.pzIter n (0 : ℝ → ℝ → ℝ) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Work.Spaces.pzIter_succ, ih, pz_zero_fun]

theorem pthIter_zero_fun (n : ℕ) : Work.Spaces.pthIter n (0 : ℝ → ℝ → ℝ) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Work.Spaces.pthIter_succ, ih, pth_zero_fun]

theorem Dz_zero_fun : Work.Spaces.Dz (0 : ℝ → ℝ → ℝ) = 0 := by
  funext z θ; simp [Work.Spaces.Dz, pz_zero_fun]

theorem Dth_zero_fun : Work.Spaces.Dth (0 : ℝ → ℝ → ℝ) = 0 := by
  funext z θ; simp [Work.Spaces.Dth, pth_zero_fun]

theorem DzIter_zero_fun (n : ℕ) : Work.Spaces.DzIter n (0 : ℝ → ℝ → ℝ) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Work.Spaces.DzIter_succ, ih, Dz_zero_fun]

theorem DthIter_zero_fun (n : ℕ) : Work.Spaces.DthIter n (0 : ℝ → ℝ → ℝ) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Work.Spaces.DthIter_succ, ih, Dth_zero_fun]

theorem mixed_zero_fun (j i : ℕ) : Work.Spaces.mixed j i (0 : ℝ → ℝ → ℝ) = 0 := by
  rw [Work.Spaces.mixed, DthIter_zero_fun, DzIter_zero_fun]

theorem pz_const_zero (z θ : ℝ) : Work.Spaces.pz (fun _ _ => (0 : ℝ)) z θ = 0 := by
  simp [Work.Spaces.pz]

theorem pth_const_zero (z θ : ℝ) : Work.Spaces.pth (fun _ _ => (0 : ℝ)) z θ = 0 := by
  simp [Work.Spaces.pth]

theorem pzIter_const_zero (n : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter n (fun _ _ => (0 : ℝ)) z θ = 0 := by
  have h : (fun _ _ => (0 : ℝ)) = (0 : ℝ → ℝ → ℝ) := rfl
  rw [h, pzIter_zero_fun n]; rfl

theorem pthIter_const_zero (n : ℕ) (z θ : ℝ) :
    Work.Spaces.pthIter n (fun _ _ => (0 : ℝ)) z θ = 0 := by
  have h : (fun _ _ => (0 : ℝ)) = (0 : ℝ → ℝ → ℝ) := rfl
  rw [h, pthIter_zero_fun n]; rfl

theorem HkIntegrand_zero (α : ℝ) (k : ℕ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k (0 : ℝ → ℝ → ℝ) z θ = 0 := by
  simp only [Work.Spaces.HkIntegrand, DzIter_zero_fun, mixed_zero_fun]
  simp

theorem HkSq_zero (α : ℝ) (k : ℕ) : Work.Spaces.HkSq α k (0 : ℝ → ℝ → ℝ) = 0 := by
  rw [Work.Spaces.HkSq]
  have h : (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (0 : ℝ → ℝ → ℝ) z θ) = fun _ => (0 : ℝ) := by
    funext z; simp [HkIntegrand_zero α k z]
  rw [h]; simp

theorem HkNorm_zero (α : ℝ) (k : ℕ) : Work.Spaces.HkNorm α k (0 : ℝ → ℝ → ℝ) = 0 := by
  rw [Work.Spaces.HkNorm, HkSq_zero, Real.sqrt_zero]

theorem HkMem_zero (α : ℝ) (k : ℕ) : Work.Spaces.HkMem α k (0 : ℝ → ℝ → ℝ) := by
  constructor
  · intro z hz
    have h : (fun θ : ℝ => Work.Spaces.HkIntegrand α k (0 : ℝ → ℝ → ℝ) z θ)
        = fun _ => (0 : ℝ) := by
      funext θ; exact HkIntegrand_zero α k z θ
    rw [h]; exact integrableOn_zero
  · have h : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (0 : ℝ → ℝ → ℝ) z θ) = fun _ => (0 : ℝ) := by
      funext z; simp [HkIntegrand_zero α k z]
    rw [h]; exact integrableOn_zero

theorem L2Mem_zero : Work.Spaces.L2Mem (0 : ℝ → ℝ → ℝ) := by
  constructor
  · intro z hz
    have h : (fun θ : ℝ => ((0 : ℝ → ℝ → ℝ) z θ) ^ 2) = fun _ => (0 : ℝ) := by
      funext θ; simp
    rw [h]; exact integrableOn_zero
  · have h : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, ((0 : ℝ → ℝ → ℝ) z θ) ^ 2)
        = fun _ => (0 : ℝ) := by
      funext z; simp
    rw [h]; exact integrableOn_zero

theorem ZDecay_zero : ZDecay (0 : ℝ → ℝ → ℝ) := by
  intro θ hθ
  have h : (fun z => z ^ 2 * (((0 : ℝ → ℝ → ℝ) z θ) ^ 2
      + (Work.Spaces.pz (0 : ℝ → ℝ → ℝ) z θ) ^ 2
      + (Work.Spaces.pzIter 2 (0 : ℝ → ℝ → ℝ) z θ) ^ 2
      + (Work.Spaces.pth (0 : ℝ → ℝ → ℝ) z θ) ^ 2
      + (Work.Spaces.pthIter 2 (0 : ℝ → ℝ → ℝ) z θ) ^ 2)) = fun _ => (0 : ℝ) := by
    funext z
    rw [pz_zero_fun, pth_zero_fun, pzIter_zero_fun, pthIter_zero_fun]
    simp
  rw [h]; exact tendsto_const_nhds

theorem SmoothNbhd_zero : Work.Spaces.SmoothNbhd (0 : ℝ → ℝ → ℝ) := by
  simp only [Work.Spaces.SmoothNbhd, Function.uncurry]
  exact contDiffOn_const

/-- The zero datum is `SmoothInt`: it is the constant `0` on the open quadrant and on every
`z`-slice.  (The companion of `SmoothNbhd_zero` for the re-scoped `smooth` field of `EllHyp`.) -/
theorem SmoothInt_zero : Work.Spaces.SmoothInt (0 : ℝ → ℝ → ℝ) := by
  refine ⟨?_, fun θ hθ => ?_⟩
  · exact contDiffOn_const
  · exact contDiffOn_const

theorem IsBslSol_zero (α : ℝ) :
    Work.Elliptic.IsBslSol α (0 : ℝ → ℝ → ℝ) (0 : ℝ → ℝ → ℝ) := by
  refine ⟨fun z hz θ h0 h1 => ?_, fun z => rfl, fun z => rfl, fun θ hθ => ?_⟩
  · simp [Work.Elliptic.bslOp, Work.Elliptic.Lzero, pz_zero_fun, pth_zero_fun,
      pzIter_zero_fun, pthIter_zero_fun, pz_const_zero, pth_const_zero,
      pzIter_const_zero, pthIter_const_zero, Pi.zero_apply]
  · simp only [Pi.zero_apply]
    exact tendsto_const_nhds

/-- **The class of data of the elliptic a-priori estimates.**

This bundles the hypotheses of Propositions `prop:L2`, `prop:H2`, `prop:Hk` and Theorem
`RemovingL12` of §'Elliptic Regularity Estimates':

* `smooth` and `sol`: `Ψ` is a smooth solution of (PolarBSL) with source `F`, vanishing at
  `θ = 0, π/2` and decaying at `z → ∞` (the paper's class of solutions);
* `memF`: the honesty of the weighted `H^k`-norm of the source, `Work.Spaces.HkMem α k F`;

together with the two formal corrections recorded in the module docstring:

* `zdecay`: the boundary terms of the integration by parts in `z` vanish at infinity;
* the `Work.Spaces.HkMem`/`Work.Spaces.L2Mem` fields: the honesty of the left-hand quantities,
  i.e. that the integrals which the estimates bound are the honest squares of norms rather than
  the junk value `0` of the totalised integral.

The class is inhabited by the zero function: `ellHyp_zero`.

**Re-scope of the `smooth` field (2024, at the lead's direction).**  The field was
`Work.Spaces.SmoothNbhd Ψ`.  In this Mathlib pin `SmoothNbhd Ψ = ContDiffOn ℝ ⊤ (uncurry Ψ) U`
with `⊤ : WithTop ℕ∞` the *analytic* level (`ContDiff ℝ ⊤ f ↔ AnalyticOnNhd ℝ f univ`), so
`EllHyp` was the class of *analytic-on-`U`* solutions; and since `U` is preconnected, any such
datum vanishing on an open subset of `U` is identically zero.  That is fatal for the
"removal-of-hypotheses by cutoff" design (`Mine.CutoffApprox`, `Mine.NOTES_CutoffApproxHolds.md`):
no datum produced by truncating with a `C^∞` cutoff can be `EllHyp`.  The field is therefore the
*non-analytic* smoothness `Work.Spaces.SmoothInt Ψ` (`C^∞` on the open quadrant `(-1,∞) × (0,π/2)`
together with `C^∞` `z`-slices down to `z = 0`) — which is the smoothness the estimates of
§'Elliptic Regularity Estimates' actually use.  Every previously available provider of
`SmoothNbhd Ψ` still yields an `EllHyp` datum through `Work.Spaces.SmoothInt.of_SmoothNbhd`
(`Spaces/WProductRule.lean`); consequently only the *consumers* that passed `h.smooth` into a
lemma whose statement demands `SmoothNbhd` have to be weakened — the checklist of such lemmas is
recorded in `Mine/CutoffPieces/NOTES_SmoothIntRescope.md`. -/
structure EllHyp (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) : Prop where
  /-- `Ψ` is `C^∞` on the open quadrant `(-1,∞) × (0,π/2)` and its `z`-slices are `C^∞` down to
  `z = 0` (`Work.Spaces.SmoothInt`).  (*Not* analyticity: see the note above.) -/
  smooth : Work.Spaces.SmoothInt Ψ
  /-- `Ψ` solves (PolarBSL) with source `F`, with Dirichlet data and decay. -/
  sol : Work.Elliptic.IsBslSol α F Ψ
  /-- The `H^k`-integral of `F` is honest. -/
  memF : Work.Spaces.HkMem α k F
  memPsi : Work.Spaces.HkMem α k Ψ
  memDth : Work.Spaces.HkMem α k (Work.Spaces.pth Ψ)
  memDth2 : Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 Ψ)
  memZ2 : Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
  memDivCos : Work.Spaces.HkMem α k (fun z θ => Ψ z θ / Real.cos θ)
  l2Dth2 : Work.Spaces.L2Mem (Work.Spaces.pthIter 2 Ψ)
  l2Z2 : Work.Spaces.L2Mem (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
  l2DivCos : Work.Spaces.L2Mem (fun z θ => Ψ z θ / Real.cos θ)
  l2F : Work.Spaces.L2Mem F
  /-- The boundary terms of the integration by parts in `z` vanish at infinity. -/
  zdecay : ZDecay Ψ
  /-- **The closed-quadrant regularity of the certificates.**  `Ψ` is smooth on an open
  neighbourhood of the closed quadrant, `Work.Spaces.SmoothNbhd Ψ`.

  `smooth : SmoothInt Ψ` above constrains the angular slice only on the *open* interval
  `(0, π/2)`, so it does not determine the one-sided limits at `θ → 0⁺`, `θ → (π/2)⁻`.  Two
  independent reviewers exhibited, from `SmoothInt` alone, the failure of the constrained slice
  Poincaré gap `L2Sq_pth_ge_nine` and of the `θ`-energy identity `PropL2Cut.energy1_inf` (see
  `SmoothInt_rescope_blocker.md`, `Final/NOTES_energy1_inf_int_FALSE.md`), and the statement
  "`F_*` is `C^m` on `(0,∞)` for `EllHyp`-data" was refuted
  (`SmoothIntRescope/Fstar_smooth_of_EllHyp_smoothInt`; cf. `Spaces/SmoothStripDefs.lean`).

  This field is the *closed-quadrant* regularity that the hypotheses of the original statements
  of `Work.Elliptic.Estimates` carry (`Work.Spaces.SmoothNbhd Ψ`) and that the level-`0` and
  certificate layers of this chapter need.  It is *not* implied by `smooth`; a datum carrying it
  is `EllHypN`-data (`EllHypN.toEllHyp`), and every provider of `SmoothNbhd`-data supplies both
  fields.  The `smooth` field is kept so that every consumer of the re-scoped (2026) interface
  keeps working. -/
  smoothNbhd : Work.Spaces.SmoothNbhd Ψ
  /-- **The diagonal second-order honesty** of the datum: `HkMem α k (∂_θθ(z∂_zΨ))`, i.e.
  `Work.Spaces.HkMem α k (fun z θ => z * ∂_z∂_θθΨ)`.  This is the conjunct that the weak class
  `TT.EllWeakPos` carries (`AeI1Paper_repair.md`, `TT/WeakDescent.lean`) and that every datum
  fed into the level-`k` estimate `TT.EllEstUnif` must satisfy;
  `TT.ellWeakPos_of_hyps` consumes it as its last argument.  It is *not* implied by the other
  fields (`H2W/AeWAux/NOTES_aeI1Data_FALSE.md`), so it is carried here. -/
  memZPth2 : Work.Spaces.HkMem α k (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)

theorem ellHyp_zero (α : ℝ) (k : ℕ) :
    EllHyp α k (0 : ℝ → ℝ → ℝ) (0 : ℝ → ℝ → ℝ) := by
  refine ⟨SmoothInt_zero, IsBslSol_zero α, HkMem_zero α k, HkMem_zero α k, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, L2Mem_zero, ZDecay_zero, SmoothNbhd_zero, ?_⟩
  · rw [pth_zero_fun]; exact HkMem_zero α k
  · rw [pthIter_zero_fun]; exact HkMem_zero α k
  · have h : (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (0 : ℝ → ℝ → ℝ) z θ) = 0 := by
      funext z θ; rw [pzIter_zero_fun]; simp
    rw [h]; exact HkMem_zero α k
  · have h : (fun z θ => (0 : ℝ → ℝ → ℝ) z θ / Real.cos θ) = 0 := by
      funext z θ; simp
    rw [h]; exact HkMem_zero α k
  · rw [pthIter_zero_fun]; exact L2Mem_zero
  · have h : (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (0 : ℝ → ℝ → ℝ) z θ) = 0 := by
      funext z θ; rw [pzIter_zero_fun]; simp
    rw [h]; exact L2Mem_zero
  · have h : (fun z θ => (0 : ℝ → ℝ → ℝ) z θ / Real.cos θ) = 0 := by
      funext z θ; simp
    rw [h]; exact L2Mem_zero
  · have h : (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 (0 : ℝ → ℝ → ℝ)) z θ) = 0 := by
      funext z θ; rw [pthIter_zero_fun]; simp [Work.Spaces.pz]
    rw [h]; exact HkMem_zero α k

/-! ## The closed-quadrant-regular twin `EllHypN` of the hypothesis bundle

The `smooth` field of `EllHyp` is `Work.Spaces.SmoothInt Ψ`: `C^∞` on the *open* quadrant
together with `C^∞` `z`-slices.  That class is strictly weaker than the one the estimates of
`prop:L2` are stated for, and *strictly weaker than what the level-`0` estimates need*:
`SmoothInt` constrains the angular slice only on `(0, π/2)`, so the conditions `Ψ z 0 = 0`,
`Ψ z (π/2) = 0` are conditions on a null set and do not control the one-sided limits of the slice
at `θ → 0⁺` and `θ → (π/2)⁻`.  Two independent reviewers exhibited, from `SmoothInt` alone, the
failure of the constrained slice Poincaré gap `L2Sq_pth_ge_nine` and of the `θ`-energy identity
`PropL2Cut.energy1_inf` (see `SmoothInt_rescope_blocker.md` and
`Final/NOTES_energy1_inf_int_FALSE.md`), and a third refuted the resulting smoothness of the
angular moment `F_*` (`Spaces/SmoothStripDefs.lean`).  The honest classes carrying the angular
traces are

* `Work.Spaces.SmoothStrip` — `C^∞` (*not* analytic) on the open neighbourhood
  `(-1,∞) × (-1, π/2+1)` of the closed quadrant, so it admits cutoff data *and* determines the
  traces; and
* `Work.Spaces.SmoothNbhd` — analytic on that neighbourhood, the class in which the *original*
  statements of `Work.Elliptic.Estimates` are phrased.

`EllHypN` is the twin of `EllHyp` in the `SmoothNbhd` class: the same twelve hypothesis fields
with `smooth : Work.Spaces.SmoothNbhd Ψ`.  It is the class in which the level-`0` cluster
(`propL2_fts`, `PropL2Cut.energy1_inf`, `energy2_aux`, `z2_pz2_int_dev`, `L2Mem_zpz_aux`,
`L2Mem_pthDiv_aux`, `HkMem_zero_imp_L2Mem`) is *proved*, so a target restated on `EllHypN` is
provable without touching the auxiliary development.  Every provider of `SmoothNbhd`-data feeds
it, and `EllHypN → EllHyp` (`SmoothNbhd ⊆ SmoothInt`), so it can be used wherever `EllHyp` is. -/
structure EllHypN (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) : Prop where
  /-- `Ψ` is smooth on an open neighbourhood of the closed quadrant: `Work.Spaces.SmoothNbhd Ψ`.
  This is the class in which the original statements are phrased and in which the level-`0`
  cluster is proved. -/
  smooth : Work.Spaces.SmoothNbhd Ψ
  /-- `Ψ` solves (PolarBSL) with source `F`, with Dirichlet data and decay. -/
  sol : Work.Elliptic.IsBslSol α F Ψ
  /-- The `H^k`-integral of `F` is honest. -/
  memF : Work.Spaces.HkMem α k F
  memPsi : Work.Spaces.HkMem α k Ψ
  memDth : Work.Spaces.HkMem α k (Work.Spaces.pth Ψ)
  memDth2 : Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 Ψ)
  memZ2 : Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
  memDivCos : Work.Spaces.HkMem α k (fun z θ => Ψ z θ / Real.cos θ)
  l2Dth2 : Work.Spaces.L2Mem (Work.Spaces.pthIter 2 Ψ)
  l2Z2 : Work.Spaces.L2Mem (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
  l2DivCos : Work.Spaces.L2Mem (fun z θ => Ψ z θ / Real.cos θ)
  l2F : Work.Spaces.L2Mem F
  /-- The boundary terms of the integration by parts in `z` vanish at infinity. -/
  zdecay : ZDecay Ψ
  /-- The diagonal second-order honesty `HkMem α k (∂_θθ(z∂_zΨ))`; see the corresponding field
  of `EllHyp`. -/
  memZPth2 : Work.Spaces.HkMem α k (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)

/-- `SmoothNbhd`-data are `SmoothInt`-data: the open-quadrant component is the restriction of the
joint component to the open strip, and the `z`-component is the restriction of the joint
component to a horizontal line at an angle `θ ∈ Iθ`. -/
theorem SmoothInt_of_SmoothNbhd {f : ℝ → ℝ → ℝ} (h : Work.Spaces.SmoothNbhd f) :
    Work.Spaces.SmoothInt f := by
  refine ⟨h.mono (fun p hp => ⟨hp.1, ⟨by linarith [hp.2.1], by linarith [hp.2.2, Real.pi_pos]⟩⟩),
    fun θ hθ => ?_⟩
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  have h2 : ContDiffOn ℝ ⊤ (fun z : ℝ => ((z, θ) : ℝ × ℝ)) (Set.Ioi (-1)) := by fun_prop
  have hc := h.comp h2 fun z hz =>
    ⟨hz, ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩⟩
  simpa only [Function.comp_def, Function.uncurry] using hc

/-- **`EllHypN`-data are `EllHyp`-data**: `SmoothNbhd ⊆ SmoothInt`, so the `SmoothNbhd`-class
bundle yields the re-scoped one field by field (and its `smooth` field supplies the closed-quadrant
field `EllHyp.smoothNbhd`). -/
theorem EllHypN.toEllHyp {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (h : EllHypN α k F Ψ) :
    EllHyp α k F Ψ :=
  ⟨SmoothInt_of_SmoothNbhd h.smooth, h.sol, h.memF, h.memPsi, h.memDth, h.memDth2, h.memZ2,
    h.memDivCos, h.l2Dth2, h.l2Z2, h.l2DivCos, h.l2F, h.zdecay, h.smooth, h.memZPth2⟩

theorem ellHypN_zero (α : ℝ) (k : ℕ) :
    EllHypN α k (0 : ℝ → ℝ → ℝ) (0 : ℝ → ℝ → ℝ) := by
  refine ⟨SmoothNbhd_zero, IsBslSol_zero α, HkMem_zero α k, HkMem_zero α k, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, L2Mem_zero, ZDecay_zero, ?_⟩
  · rw [pth_zero_fun]; exact HkMem_zero α k
  · rw [pthIter_zero_fun]; exact HkMem_zero α k
  · have h : (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (0 : ℝ → ℝ → ℝ) z θ) = 0 := by
      funext z θ; rw [pzIter_zero_fun]; simp
    rw [h]; exact HkMem_zero α k
  · have h : (fun z θ => (0 : ℝ → ℝ → ℝ) z θ / Real.cos θ) = 0 := by
      funext z θ; simp
    rw [h]; exact HkMem_zero α k
  · rw [pthIter_zero_fun]; exact L2Mem_zero
  · have h : (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (0 : ℝ → ℝ → ℝ) z θ) = 0 := by
      funext z θ; rw [pzIter_zero_fun]; simp
    rw [h]; exact L2Mem_zero
  · have h : (fun z θ => (0 : ℝ → ℝ → ℝ) z θ / Real.cos θ) = 0 := by
      funext z θ; simp
    rw [h]; exact L2Mem_zero
  · have h : (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 (0 : ℝ → ℝ → ℝ)) z θ) = 0 := by
      funext z θ; rw [pthIter_zero_fun]; simp [Work.Spaces.pz]
    rw [h]; exact HkMem_zero α k

end Work.FTS.EllipticEst
