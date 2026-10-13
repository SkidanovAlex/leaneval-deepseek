import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.EllipticEst.RegQ
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs
import Submission.Work.Elliptic.bslOp_sing_source
import Submission.Work.Elliptic.Fstar_orthSource
import Submission.Work.Elliptic.integral_sin_two_mul_sinCos2
import Submission.Work.Elliptic.Gsing_ode
import Submission.Work.FTS.EllipticEst.HkNorm_add_le
import Submission.Work.FTS.EllipticEst.HkNorm_const_mul
import Submission.Work.FTS.EllipticEst.Blocks.HkIntegrand_mul_angular_le
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.LocData.HkIntegrand_const_mul
import Submission.Work.FTS.LocData.HkSq_const_mul
import Submission.Work.FTS.LocData.HkMem_of_majorant

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Vop_bound_reg`: the `ℋ⁴`-bound for the `V`-operator of the elliptic residual

Target (`Work.FTS.EllipticEst.Vop_bound_reg`): there is a universal constant `C > 0` such that
for every `0 < α ≤ 1/4` and every pair `(F, Ψ)` with `EllHypQ α 4 F Ψ` (the interior data class
of `RegQ.lean`) and `OrthCond (Ψ + Gsing α F · sin 2θ)`,

* `SmoothQuad` of `Vop α (EllResid α F Ψ)`,
* `HkMem α 4` of it,
* `Xn α (Vop α (EllResid α F Ψ)) ≤ C * Xn α F`   (`Xn α f = HkNorm α 4 f`).

The operator is `Vop α Ψ = ∂_θΨ - tan θ · Ψ` (paper (Relations), tex 1320), and the residual is
`EllResid α F Ψ = Ψ - (1/(4α)) sin 2θ · L₁₂(F)`.

## The structure of the argument — and the state of this file

**The key structural point (proved here).**  The three operators of (Relations) (tex 1320) are
*not* independent:

  `Vop α Ψ = Rop α Ψ + tan θ · Uop α Ψ`,   i.e. `V = R + tan θ · U`

(`Vop_eq_Rop_add_tan_Uop`), and `tan θ · U = 2 sin²θ · (U / sin 2θ)` on the open quadrant
(`tan_mul_Uop_eq`).  Since `2 sin²θ` is bounded and vanishes on the angular boundary, the
`ℋ⁴`-bound for `V` follows from the two bounds for `R` and for `U / sin 2θ`:

  `Xn α (Vop α W) ≤ C · (Xn α (Rop α W) + Xn α (Uop α W / sin 2θ))`

(`Xn_Vop_le`, proved below, built on `HkSq_two_sinsq_mul_le`, `HkMem_two_sinsq_mul`,
`HkIntegrand_two_sinsq_mul_le`, `HkSq_le_of_pointwise`).  In particular `Vop_bound_reg` is a
*corollary* of the two sibling targets `Rop_bound_reg` and `Uop_bound_reg`.

**What the residual `W = EllResid α F Ψ` carries.**  `W = Ψ + Gstar α F · sin 2θ`
(`EllResid_eq_Psi_add_Gstar`) and `W = Ψ̂ - Gbar α F · sin 2θ` with
`Ψ̂ = Ψ + Gsing α F · sin 2θ` (`EllResid_eq_PsiHat_sub_Gbar`); `Vop` of a radial `sin 2θ`-multiple
is `λ · (2cos 2θ - tan θ sin 2θ) = λ · 2(1 - 3 sin²θ)` on the open quadrant
(`Vop_sin_two_mul`, `vop_factor_eq`, `vop_factor_abs_le`), whence `Vop_EllResid_eq`.

**What is still missing (the analytic content).**  For `W := EllResid α F Ψ` with
`EllHypQ α 4 F Ψ` and `OrthCond (Ψ + Gsing α F sin 2θ)` one still needs

* `SmoothOpen`/`HkMem α 4` of `Rop α W` and of `Uop α W / sin 2θ` (and of `Vop α W`, here
  derived from them), and
* the two *bounds* `Xn α (Rop α W) ≤ C Xn α F`, `Xn α (Uop α W / sin 2θ) ≤ C Xn α F`

— i.e. the `ℛ`- and `U`-halves of the paper's Theorem `RemovingL12` together with the
`DivisionBySin` proposition (the contents of the sibling files
`EllipticEst/Rop_bound_reg.lean` and `EllipticEst/Uop_bound_reg.lean`).  The present file proves
everything around that reduction: the algebra, the operator identity `V = R + tan θ U`, and the
`HkSq`/`HkMem` transfers for the bounded angular profile `2 sin²θ`.

An equivalent route, also recorded here, works with the *straightened* stream function
`Ψ̂ = Ψ + Gsing α F · sin 2θ = W + Gbar α F · sin 2θ`: by `bslOp_sing_source`,
`bslOp α Ψ̂ = orthSource F`, and `F_*(orthSource F) = 0` (`Fstar_orthSource`) while the hypothesis
is exactly `F_*(Ψ̂) = 0`; so `(orthSource F, Ψ̂)` is a datum of the *orthogonal* elliptic problem,
and the `V`-companion of Theorem `RemovingL12` (with the `Gbar` layer, controlled by the paper's
Lemma `HardyInequality4`) gives the bound.  That is the route of the in-flight request
`EllipticEst/RegQ/Vop_orth_le_k4`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-! ## The algebraic reduction -/

/-- `EllResid α F Ψ = Ψ + Gstar α F · sin 2θ`: the residual is the stream function plus the main
term `G_* = -(1/(4α)) L₁₂(F)` of the singular part, multiplied by the kernel direction
`sin 2θ` of `L₀`. -/
theorem EllResid_eq_Psi_add_Gstar (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) :
    Work.Elliptic.EllResid α F Ψ
      = fun z θ => Ψ z θ + Work.Elliptic.Gstar α F z * Real.sin (2 * θ) := by
  funext z θ
  simp only [Work.Elliptic.EllResid, Work.Elliptic.Gstar]
  ring

/-- `EllResid α F Ψ = Ψ̂ - Gbar α F · sin 2θ` with `Ψ̂ = Ψ + Gsing α F · sin 2θ`: the residual is
the *straightened* stream function minus the remainder `Gbar` of the singular part. -/
theorem EllResid_eq_PsiHat_sub_Gbar (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) :
    Work.Elliptic.EllResid α F Ψ
      = fun z θ => (Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ))
          - Work.Elliptic.Gbar α F z * Real.sin (2 * θ) := by
  funext z θ
  simp only [Work.Elliptic.EllResid, Work.Elliptic.Gsing, Work.Elliptic.Gstar]
  ring

/-- `Vop` of a `sin 2θ`-multiple with radial amplitude `λ`: `λ(z)·(2cos 2θ - tan θ sin 2θ)`.
(`Real.tan` is totalised, so the value at `θ = π/2` is junk; the identity is used on the open
quadrant.) -/
theorem Vop_sin_two_mul (α : ℝ) (lam : ℝ → ℝ) :
    Vop α (fun z θ => lam z * Real.sin (2 * θ))
      = fun z θ => lam z * (2 * Real.cos (2 * θ) - Real.tan θ * Real.sin (2 * θ)) := by
  funext z θ
  have h1 : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
    have h := (Real.hasDerivAt_sin (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul (2 : ℝ))
    simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using h
  have h2 := h1.const_mul (lam z)
  show deriv (fun θ' : ℝ => lam z * Real.sin (2 * θ')) θ - Real.tan θ * (lam z * Real.sin (2 * θ))
      = lam z * (2 * Real.cos (2 * θ) - Real.tan θ * Real.sin (2 * θ))
  rw [h2.deriv]
  ring

/-- On the open interval `(-π/2, π/2)` the angular factor is the bounded trigonometric
polynomial `2(1 - 3 sin²θ)`. -/
theorem vop_factor_eq (θ : ℝ) (hθ : θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    2 * Real.cos (2 * θ) - Real.tan θ * Real.sin (2 * θ)
      = 2 * (1 - 3 * Real.sin θ ^ 2) := by
  have hcos : Real.cos θ ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo hθ)
  have ht : Real.tan θ = Real.sin θ / Real.cos θ := Real.tan_eq_sin_div_cos θ
  have hs : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := Real.sin_two_mul θ
  have hc : Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := Real.cos_two_mul θ
  have hsc := Real.sin_sq_add_cos_sq θ
  rw [ht, hs, hc]
  field_simp
  nlinarith [hsc]

/-- The angular factor is bounded by `4` on the *closed* interval (in particular at `π/2`,
where `Real.tan` takes its junk value). -/
theorem vop_factor_abs_le (θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    |2 * Real.cos (2 * θ) - Real.tan θ * Real.sin (2 * θ)| ≤ 4 := by
  rcases eq_or_lt_of_le hθ.2 with h | h
  · have h1 : Real.sin (2 * θ) = 0 := by
      rw [h, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
    have h2 : Real.cos (2 * θ) = -1 := by
      rw [h, show 2 * (Real.pi / 2) = Real.pi by ring, Real.cos_pi]
    rw [h1, h2]
    norm_num
  · have hIoo : θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith [hθ.1, Real.pi_pos], h⟩
    rw [vop_factor_eq θ hIoo]
    have hsin0 : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])
    have hsin : Real.sin θ ^ 2 ≤ 1 := by nlinarith [Real.sin_le_one θ]
    rw [abs_le]
    constructor <;> nlinarith

/-- **`Vop` of the residual, in terms of `Vop Ψ̂`.**  At every point where the `θ`-slice of `Ψ`
is differentiable,

`Vop α W = Vop α Ψ̂ - Gbar α F · (2cos 2θ - tan θ sin 2θ)`,  `W = EllResid α F Ψ`,
`Ψ̂ = Ψ + Gsing α F · sin 2θ`. -/
theorem Vop_EllResid_eq (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hΨ : DifferentiableAt ℝ (fun θ' => Ψ z θ') θ) :
    Vop α (Work.Elliptic.EllResid α F Ψ) z θ
      = Vop α (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
        - Work.Elliptic.Gbar α F z
            * (2 * Real.cos (2 * θ) - Real.tan θ * Real.sin (2 * θ)) := by
  have hsin : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
    have h := (Real.hasDerivAt_sin (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul (2 : ℝ))
    simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using h
  have hA : HasDerivAt (fun θ' : ℝ => Ψ z θ' + Work.Elliptic.Gsing α F z * Real.sin (2 * θ'))
      (deriv (fun θ' : ℝ => Ψ z θ') θ
        + Work.Elliptic.Gsing α F z * (2 * Real.cos (2 * θ))) θ := by
    have h1 : HasDerivAt (fun θ' : ℝ => Ψ z θ') (deriv (fun θ' : ℝ => Ψ z θ') θ) θ :=
      hΨ.hasDerivAt
    exact h1.add (hsin.const_mul (Work.Elliptic.Gsing α F z))
  have hB : HasDerivAt (fun θ' : ℝ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ'))
      (Work.Elliptic.Gbar α F z * (2 * Real.cos (2 * θ))) θ :=
    hsin.const_mul (Work.Elliptic.Gbar α F z)
  have hsub : HasDerivAt
      (fun θ' : ℝ => (Ψ z θ' + Work.Elliptic.Gsing α F z * Real.sin (2 * θ'))
        - Work.Elliptic.Gbar α F z * Real.sin (2 * θ'))
      ((deriv (fun θ' : ℝ => Ψ z θ') θ + Work.Elliptic.Gsing α F z * (2 * Real.cos (2 * θ)))
        - Work.Elliptic.Gbar α F z * (2 * Real.cos (2 * θ))) θ := hA.sub hB
  have hEq : (fun θ' : ℝ => Work.Elliptic.EllResid α F Ψ z θ')
      = fun θ' : ℝ => (Ψ z θ' + Work.Elliptic.Gsing α F z * Real.sin (2 * θ'))
          - Work.Elliptic.Gbar α F z * Real.sin (2 * θ') := by
    funext θ'
    have h := congrFun (congrFun (EllResid_eq_PsiHat_sub_Gbar α F Ψ) z) θ'
    simpa using h
  have hderiv : deriv (fun θ' : ℝ => Work.Elliptic.EllResid α F Ψ z θ') θ
      = (deriv (fun θ' : ℝ => Ψ z θ') θ + Work.Elliptic.Gsing α F z * (2 * Real.cos (2 * θ)))
        - Work.Elliptic.Gbar α F z * (2 * Real.cos (2 * θ)) := by
    rw [hEq]
    exact hsub.deriv
  have hEll : Work.Elliptic.EllResid α F Ψ z θ
      = (Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ))
        - Work.Elliptic.Gbar α F z * Real.sin (2 * θ) := by
    have h := congrFun (congrFun (EllResid_eq_PsiHat_sub_Gbar α F Ψ) z) θ
    simpa using h
  show deriv (fun θ' : ℝ => Work.Elliptic.EllResid α F Ψ z θ') θ
      - Real.tan θ * Work.Elliptic.EllResid α F Ψ z θ
    = (deriv (fun θ' : ℝ => Ψ z θ' + Work.Elliptic.Gsing α F z * Real.sin (2 * θ')) θ
        - Real.tan θ * (Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)))
      - Work.Elliptic.Gbar α F z
          * (2 * Real.cos (2 * θ) - Real.tan θ * Real.sin (2 * θ))
  rw [hderiv, hEll, hA.deriv]
  ring

/-! ## The transfer identities of the `R`-`U`-`V` triangle (paper (Relations), tex 1320) -/

/-- **`V = R + tan θ · U`.**  The three operators of (Relations) are not independent:
`Rop α Ψ + tan θ · Uop α Ψ = Vop α Ψ`.  Consequently the `ℋ⁴`-bound for `Vop` follows from the
two bounds for `Rop` and for `Uop / sin 2θ` (`Xn_Vop_le` below). -/
theorem Vop_eq_Rop_add_tan_Uop (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) (hcos : Real.cos θ ≠ 0) :
    Vop α Ψ z θ = Rop α Ψ z θ + Real.tan θ * Uop α Ψ z θ := by
  simp only [Vop, Rop, Uop]
  rw [Real.tan_eq_sin_div_cos]
  field_simp
  ring

/-- `HkNorm` only sees the open quadrant. -/
theorem HkNorm_congr_open' (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ) :
    Work.Spaces.HkNorm α k f = Work.Spaces.HkNorm α k g := by
  rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, Work.FTS.EllipticEst.HkSq_congr_open α k h]

/-- `tan θ · Uop = 2 sin²θ · (Uop / sin 2θ)` on the open quadrant: the second factor is the
quantity of the paper's `DivisionBySin` proposition, and `2 sin²θ` is the bounded angular
profile of `Blocks.HkIntegrand_mul_angular_le`. -/
theorem tan_mul_Uop_eq (α : ℝ) (Ψ : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Real.tan θ * Uop α Ψ z θ
      = (2 * Real.sin θ ^ 2) * (Uop α Ψ z θ / Real.sin (2 * θ)) := by
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩)
  have hsin : Real.sin (2 * θ) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos]))
  rw [Real.tan_eq_sin_div_cos, Real.sin_two_mul]
  field_simp

/-! ## The `HkSq`-transfer for the bounded angular profile `2 sin²θ` -/

/-- The `HkIntegrand` is nonnegative, so a pointwise domination on the *open* quadrant (where the
two boundary lines have integrand `0` on both sides) integrates to a `HkSq`-domination, provided
the dominating integrand is honest. -/
theorem HkSq_le_of_pointwise (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hmg : Work.Spaces.HkMem α k g)
    (hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k f z θ ≤ C * Work.Spaces.HkIntegrand α k g z θ) :
    Work.Spaces.HkSq α k f ≤ C * Work.Spaces.HkSq α k g := by
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
        ≤ C * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ := by
    intro z hz
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (μ := volume.restrict Work.Spaces.Iθ)
      (f := fun θ => Work.Spaces.HkIntegrand α k f z θ)
      (g := fun θ => C * Work.Spaces.HkIntegrand α k g z θ)
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ)
      ((hmg.1 z hz).const_mul C)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => hpt z hz θ hθ))
    refine hmono.trans_eq ?_
    rw [MeasureTheory.integral_const_mul]
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  have houter := MeasureTheory.integral_mono_of_nonneg
    (μ := volume.restrict Work.Spaces.Iz)
    (f := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
    (g := fun z => C * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)
    (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α k f z θ)
    (hmg.2.const_mul C)
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => hinner z hz)
  refine houter.trans_eq ?_
  rw [MeasureTheory.integral_const_mul]

/-- The `HkIntegrand` vanishes on the axis `z = 0` (the radial weight `w` has a zero there). -/
theorem HkIntegrand_eq_zero_of_z_eq_zero' (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k f 0 θ = 0 := by
  simp [Work.Spaces.HkIntegrand, Work.Spaces.w, Work.Spaces.Wt]

/-- The `HkIntegrand` vanishes on the angular boundary `sin 2θ = 0` (both weights are singular
powers of `sin 2θ`, and `0^p = 0` for `p ≠ 0`). -/
theorem HkIntegrand_eq_zero_of_sin_eq_zero' (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (hα : 0 < α)
    {z θ : ℝ} (h : Real.sin (2 * θ) = 0) : Work.Spaces.HkIntegrand α k f z θ = 0 := by
  have hη : (0 : ℝ) ^ (Work.Spaces.eta / 2) = 0 :=
    Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)
  have hgam : Work.Spaces.gam α / 2 ≠ 0 := by
    rw [Work.Spaces.gam]; intro hc; linarith
  have hγ : (0 : ℝ) ^ (-(Work.Spaces.gam α / 2)) = 0 := Real.zero_rpow (neg_ne_zero.mpr hgam)
  simp only [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.wTheta, h, hη, hγ]
  simp

/-- The pointwise multiplication bound of `Blocks.HkIntegrand_mul_angular_le` for the profile
`2 sin²θ`. -/
theorem HkIntegrand_two_sinsq_mul_le (k : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (g : ℝ → ℝ → ℝ),
    0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen g → ∀ z θ : ℝ, 0 < z → 0 < θ →
      θ < Real.pi / 2 →
      Work.Spaces.HkIntegrand α k (fun z θ => (2 * Real.sin θ ^ 2) * g z θ) z θ
        ≤ C * Work.Spaces.HkIntegrand α k g z θ := by
  obtain ⟨Ca, hCapos, hCaf⟩ :=
    Work.FTS.EllipticEst.Blocks.HkIntegrand_mul_angular_le k
  refine ⟨4 * Ca, by positivity, ?_⟩
  intro α g hα hα1 hg z θ hz hθ0 hθ1
  obtain ⟨_hCa1, hCa2⟩ := hCaf α g hα hα1 hg
  have h1 : Work.Spaces.HkIntegrand α k (fun z θ => (2 * Real.sin θ ^ 2) * g z θ) z θ
      = 4 * Work.Spaces.HkIntegrand α k
          (fun z θ => Real.sin θ ^ 2 * g z θ) z θ := by
    rw [show (fun z θ => (2 * Real.sin θ ^ 2) * g z θ)
          = fun z θ => (2 : ℝ) * (Real.sin θ ^ 2 * g z θ) from by
        funext z' θ'; ring,
      Work.FTS.LocData.HkIntegrand_const_mul]
    norm_num
  rw [h1]
  have h2 := hCa2 z θ hz hθ0 hθ1
  have h3 := Work.Spaces.HkIntegrand_nonneg α k g z θ
  nlinarith [h2, h3, hCapos.le]

/-- The `HkSq`-form of the multiplication bound for `2 sin²θ`. -/
theorem HkSq_two_sinsq_mul_le (k : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (g : ℝ → ℝ → ℝ),
    0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α k g →
    Work.Spaces.HkSq α k (fun z θ => (2 * Real.sin θ ^ 2) * g z θ)
      ≤ C * Work.Spaces.HkSq α k g := by
  obtain ⟨C, hCpos, hC⟩ := HkIntegrand_two_sinsq_mul_le k
  refine ⟨C, hCpos, ?_⟩
  intro α g hα hα1 hg hmem
  refine HkSq_le_of_pointwise α k hCpos.le hmem ?_
  intro z hz θ hθ
  rcases eq_or_lt_of_le (show (0:ℝ) ≤ z from hz) with h0 | h0
  · rw [← h0, HkIntegrand_eq_zero_of_z_eq_zero']
    exact mul_nonneg hCpos.le (Work.Spaces.HkIntegrand_nonneg α k g 0 θ)
  · by_cases hs : Real.sin (2 * θ) = 0
    · rw [HkIntegrand_eq_zero_of_sin_eq_zero' α k _ hα hs]
      exact mul_nonneg hCpos.le (Work.Spaces.HkIntegrand_nonneg α k g z θ)
    · have hθ' : 0 < θ ∧ θ < Real.pi / 2 := by
        rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
        refine ⟨?_, ?_⟩
        · rcases eq_or_lt_of_le hθ.1 with h | h
          · rw [← h] at hs; exact absurd (by simp) hs
          · exact h
        · rcases lt_or_eq_of_le hθ.2 with h | h
          · exact h
          · rw [h] at hs
            exact absurd (by rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]) hs
      exact hC α g hα hα1 hg z θ h0 hθ'.1 hθ'.2

/-- The `HkMem`-form of the multiplication bound for `2 sin²θ`. -/
theorem HkMem_two_sinsq_mul (k : ℕ) {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkMem α k (fun z θ => (2 * Real.sin θ ^ 2) * g z θ) := by
  obtain ⟨C, hCpos, hC⟩ := HkIntegrand_two_sinsq_mul_le k
  have hfsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => (2 * Real.sin θ ^ 2) * g z θ) := by
    show ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (fun z θ => (2 * Real.sin θ ^ 2) * g z θ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))
    have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => (2 : ℝ) * Real.sin p.2 ^ 2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by fun_prop
    have h2 : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hg
    exact h1.mul h2
  refine Work.FTS.LocData.HkMem_of_majorant α k
    (f := fun z θ => (2 * Real.sin θ ^ 2) * g z θ)
    (M := fun z θ => C * Work.Spaces.HkIntegrand α k g z θ)
    (hfsm.continuousOn_HkIntegrand α k) ?_ ?_ ?_
  · intro z hz
    exact (hmem.1 z hz).const_mul C
  · refine (hmem.2.const_mul C).congr ?_
    filter_upwards with z
    rw [MeasureTheory.integral_const_mul]
  · intro z hz θ hθ
    rcases eq_or_lt_of_le (show (0:ℝ) ≤ z from hz) with h0 | h0
    · rw [← h0, HkIntegrand_eq_zero_of_z_eq_zero']
      exact mul_nonneg hCpos.le (Work.Spaces.HkIntegrand_nonneg α k g 0 θ)
    · by_cases hs : Real.sin (2 * θ) = 0
      · rw [HkIntegrand_eq_zero_of_sin_eq_zero' α k _ hα hs]
        exact mul_nonneg hCpos.le (Work.Spaces.HkIntegrand_nonneg α k g z θ)
      · have hθ' : 0 < θ ∧ θ < Real.pi / 2 := by
          rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
          refine ⟨?_, ?_⟩
          · rcases eq_or_lt_of_le hθ.1 with h | h
            · rw [← h] at hs; exact absurd (by simp) hs
            · exact h
          · rcases lt_or_eq_of_le hθ.2 with h | h
            · exact h
            · rw [h] at hs
              exact absurd (by rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]) hs
        exact hC α g hα hα1 hg z θ h0 hθ'.1 hθ'.2

/-- **The `V`-bound from the `R`- and `U`-bounds.**  For `W` whose `R`- and `U`-transforms are
smooth and honest on the open quadrant,

`Xn α (Vop α W) ≤ C · (Xn α (Rop α W) + Xn α (Uop α W / sin 2θ))`.

This is the identity `V = R + tan θ · U` combined with `tan θ U = 2 sin²θ (U/sin 2θ)` and the
`HkSq`-bound for the bounded angular profile `2 sin²θ`. -/
theorem Xn_Vop_le (α : ℝ) (W : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hRsm : Work.FTS.EllipticEst.SmoothOpen (Rop α W))
    (hUsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Uop α W z θ / Real.sin (2 * θ)))
    (hRmem : Work.Spaces.HkMem α 4 (Rop α W))
    (hUmem : Work.Spaces.HkMem α 4 (fun z θ => Uop α W z θ / Real.sin (2 * θ))) :
    ∃ C : ℝ, 0 < C ∧ Work.FTS.Nonlin.Xn α (Vop α W)
      ≤ C * (Work.FTS.Nonlin.Xn α (Rop α W)
          + Work.FTS.Nonlin.Xn α (fun z θ => Uop α W z θ / Real.sin (2 * θ))) := by
  obtain ⟨C, hCpos, hC⟩ := HkSq_two_sinsq_mul_le 4
  set GU : ℝ → ℝ → ℝ := fun z θ => Uop α W z θ / Real.sin (2 * θ) with hGUdef
  set G2 : ℝ → ℝ → ℝ := fun z θ => (2 * Real.sin θ ^ 2) * GU z θ with hG2def
  have hG2mem : Work.Spaces.HkMem α 4 G2 := HkMem_two_sinsq_mul 4 hα hα1 hUsm hUmem
  have hG2sq : Work.Spaces.HkSq α 4 G2 ≤ C * Work.Spaces.HkSq α 4 GU :=
    hC α GU hα hα1 hUsm hUmem
  have hG2sm : Work.FTS.EllipticEst.SmoothOpen G2 := by
    show ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (fun z θ => (2 * Real.sin θ ^ 2) * GU z θ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))
    have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => (2 : ℝ) * Real.sin p.2 ^ 2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by fun_prop
    have h2 : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry GU)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hUsm
    exact h1.mul h2
  -- the pointwise identity `V = R + G2` on the open quadrant
  have hVop : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Vop α W z θ = Rop α W z θ + G2 z θ := by
    intro z θ hz hθ0 hθ1
    have hcos : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ0], hθ1⟩)
    rw [Vop_eq_Rop_add_tan_Uop α W z θ hcos,
      tan_mul_Uop_eq α W (show θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) from ⟨hθ0, hθ1⟩)]
  have hnorm : Work.FTS.Nonlin.Xn α (Vop α W)
      = Work.FTS.Nonlin.Xn α (fun z θ => Rop α W z θ + G2 z θ) :=
    HkNorm_congr_open' α 4 hVop
  -- the squared estimate
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (fun z θ => Rop α W z θ + G2 z θ) z θ
        ≤ 2 * Work.Spaces.HkIntegrand α 4 (Rop α W) z θ
          + 2 * Work.Spaces.HkIntegrand α 4 G2 z θ :=
    HkIntegrand_add_le_of_contDiffOn α 4 hRsm hG2sm
  have hsqsum : Work.Spaces.HkSq α 4 (fun z θ => Rop α W z θ + G2 z θ)
      ≤ 2 * Work.Spaces.HkSq α 4 (Rop α W) + 2 * Work.Spaces.HkSq α 4 G2 :=
    HkSq_add_le_of_pointwise α 4 hRmem hG2mem hpt
  have hXR : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 4 (Rop α W)) := Real.sqrt_nonneg _
  have hXG : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 4 GU) := Real.sqrt_nonneg _
  refine ⟨Real.sqrt 2 * (1 + Real.sqrt C), by positivity, ?_⟩
  rw [hnorm]
  have hstep1 : Real.sqrt (Work.Spaces.HkSq α 4 (fun z θ => Rop α W z θ + G2 z θ))
      ≤ Real.sqrt 2 * (Real.sqrt (Work.Spaces.HkSq α 4 (Rop α W))
          + Real.sqrt C * Real.sqrt (Work.Spaces.HkSq α 4 GU)) := by
    refine (Real.sqrt_le_sqrt hsqsum).trans ?_
    have h2 : Real.sqrt (2 * Work.Spaces.HkSq α 4 (Rop α W) + 2 * Work.Spaces.HkSq α 4 G2)
        ≤ Real.sqrt 2 * (Real.sqrt (Work.Spaces.HkSq α 4 (Rop α W))
            + Real.sqrt (Work.Spaces.HkSq α 4 G2)) :=
      sqrt_two_mul_add_le (Work.Spaces.HkSq_nonneg α 4 (Rop α W))
        (Work.Spaces.HkSq_nonneg α 4 G2)
    refine h2.trans ?_
    have h3 : Real.sqrt (Work.Spaces.HkSq α 4 G2)
        ≤ Real.sqrt C * Real.sqrt (Work.Spaces.HkSq α 4 GU) := by
      refine (Real.sqrt_le_sqrt hG2sq).trans (le_of_eq ?_)
      rw [Real.sqrt_mul hCpos.le]
    have h4 := Real.sqrt_nonneg C
    nlinarith [h3, h4, hXR, hXG, Real.sqrt_nonneg (2 : ℝ)]
  refine hstep1.trans ?_
  have hXR' : 0 ≤ Work.FTS.Nonlin.Xn α (Rop α W) := Real.sqrt_nonneg _
  have hXG' : 0 ≤ Work.FTS.Nonlin.Xn α GU := Real.sqrt_nonneg _
  have h6 : Real.sqrt 2 * (Work.FTS.Nonlin.Xn α (Rop α W)
        + Real.sqrt C * Work.FTS.Nonlin.Xn α GU)
      ≤ (Real.sqrt 2 * (1 + Real.sqrt C)) * (Work.FTS.Nonlin.Xn α (Rop α W)
        + Work.FTS.Nonlin.Xn α GU) := by
    have h7 : 0 ≤ Real.sqrt C := Real.sqrt_nonneg C
    have h8 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg (2 : ℝ)
    have hkey : Real.sqrt 2 * (Work.FTS.Nonlin.Xn α (Rop α W)
          + Real.sqrt C * Work.FTS.Nonlin.Xn α GU)
        = Real.sqrt 2 * Work.FTS.Nonlin.Xn α (Rop α W)
          + (Real.sqrt 2 * Real.sqrt C) * Work.FTS.Nonlin.Xn α GU := by ring
    have hkey2 : (Real.sqrt 2 * (1 + Real.sqrt C)) * (Work.FTS.Nonlin.Xn α (Rop α W)
          + Work.FTS.Nonlin.Xn α GU)
        = Real.sqrt 2 * Work.FTS.Nonlin.Xn α (Rop α W)
          + Real.sqrt 2 * Work.FTS.Nonlin.Xn α GU
          + (Real.sqrt 2 * Real.sqrt C) * Work.FTS.Nonlin.Xn α (Rop α W)
          + (Real.sqrt 2 * Real.sqrt C) * Work.FTS.Nonlin.Xn α GU := by ring
    rw [hkey, hkey2]
    nlinarith [mul_nonneg h8 hXR', mul_nonneg (mul_nonneg h8 h7) hXR']
  exact h6

theorem Vop_bound_reg : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.EllHypQ α 4 F Ψ →
    Work.Elliptic.OrthCond (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) →
    Work.FTS.LocData.SmoothQuad (Work.FTS.EllipticEst.Vop α (Work.Elliptic.EllResid α F Ψ)) ∧
      Work.Spaces.HkMem α 4 (Work.FTS.EllipticEst.Vop α (Work.Elliptic.EllResid α F Ψ)) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.EllipticEst.Vop α (Work.Elliptic.EllResid α F Ψ))
        ≤ C * Work.FTS.Nonlin.Xn α F := by
  sorry

end Work.FTS.EllipticEst
