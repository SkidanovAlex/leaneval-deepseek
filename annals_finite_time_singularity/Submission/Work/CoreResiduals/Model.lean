/-
# `Work.CoreResiduals.Model` — the inhabitant, and the rate rigidity of the self-similar profile

## 1. The inhabitant

`profileData_inhabited` produces a `ProfileData α` with `g = 0`, `T = 2`, `λ̄(t) = 1 - t/2`,
`K = 1/2`, `Cg = Cg' = 0`, `L = 4^{1/p}+1`, `R = 2L`, `M = 20p`, `M₁ = 10p`.  We bundle it as
`Inhabitant α` so that the four residual statements can be read at *concrete* data.

## 2. The rate of the model modulation, and the rigidity of `F_*`

The design's `(λ̄, μ̄) ↔ (κ, b)` dictionary (`Work.Stability.Defs`, `NOTES_LEAD_Stability.md`
St2) reads `κ = -λ̄'` and `λ̄ = amp s = e^{-s}`, `ds/dt = κ/λ̄`; the rescaled (self-similar)
vorticity equation at *constant* rates is

  `DynEqConst α κ b f φ :  κ·(f + b·D_z f) + UVR α f φ = 0`   on the open quadrant,

which is `Work.Stability.DynEq` for `s`-independent `f`, `φ` (the case of a self-similar profile;
the general equivalence `SelfSimEulerS ↔ DynEq` is `Work.Stability.DynEqOfSelfSimEulerS`).

The **model modulation** `λ̄(t) = 1 - t/2` has `λ̄' = -1/2`.  The paper's reference rates are
`(κ*, b*) = (kappaStar μ, bStar μ) = (1+μ, 1+λ(μ))`, and the profile `F_*` is the stationary
solution at `μ = 0`, i.e. `(κ*, b*) = (1, 1)` (`Work.Construction.Fstar_stationary_identity`,
`Work.Stability.DynEqOfSelfSimEulerS`).

**The factor `2` of the time dilation (audited).**  The rate that enters the *profile* equation is
not `-λ̄'` but `2·(-λ̄')`, and at the inhabitant the two differ by exactly the factor that makes the
bookkeeping consistent:

* the paper's self-similar equation `(1/2)∂_tΩ + U(Ψ)∂_θΩ + V(Ψ)αR∂_RΩ = ℛ(Ψ)Ω` (tex 1319, the
  `1/2` is the paper's explicitly announced "time dilation") carries the coefficient `1/2` on
  `∂_t`; its ansatz `Ω = λ̄(t)⁻¹F(R/λ̄(t),θ)` therefore produces the profile equation
  `κ_p(F + b D_zF) + UVR α F Φ = 0` with `κ_p = -dλ̄/dt_paper`;
* the *delivered* residual R1 is the **physical** vorticity equation
  (`Work.LWP.VorticityEquation`, no `1/2` in sight: `∂ₜω + (u·∇)ω = (ω·∇)u`), so substituting the
  ansatz there produces the *same* profile equation with the effective rate `κ_phys = 2·(-λ̄')`
  (multiplying the substituted equation by `2λ̄²` to normalise the coefficient of `F + z∂_zF`);
* since the delivered `λ̄` is the paper's `λ̄` written in the *physical* time
  (`ProfileData_T_eq_two` forces `T = 2`, and the paper's blow-up `T* = 1` in the dilated time is
  exactly `t_phys = 2`), we get `κ_phys = 2·(1/2) = 1 = κ*` at the inhabitant.  See
  `model_rate_physical`, `model_rate_physical_eq_reference`.

**Consequence (this corrects an earlier reading of this area): there is no rate mismatch at the
delivered inhabitant.**  The profile `F_*` is stationary at the inhabitant's effective rate
`(κ, b) = (1, 1)`, so the profile equation and `Work.Construction.Fstar_stationary_identity` are
*consistent*; the fact that the design's `κ := -λ̄'` (the `1/2`-dilation trap note of
`Work.Stability.Defs`) is `1/2` at the inhabitant is a statement in the paper's dilated time and
does not apply to the physical residual R1.

**The rate rigidity** (`dynEqConst_sub`, `fstar_rate_rigid`): `UVR α f φ` depends on the
stream function `φ` but *not* on the rates, so two constant-rate instances of the equation for
the *same* profile and the *same* stream function differ by an explicitly computable,
`φ`-free identity
  `(κ - κ')·f + (κ·b - κ'·b')·D_z f = 0`
on the quadrant.  For `f = F_*` this forces `κ = κ'`: at `(z,θ) = (1,π/4)` one has
`D_z F_*(1,π/4) = 0` (`Work.Construction.Dz_Fstar_eq`) while `F_*(1,π/4) ≠ 0`.

Consequence for residual R1: if the model field's self-similar profile `F_*` satisfied the
constant-rate rescaled equation at *both* the reference rate `(1,1)` (the paper's normalisation)
and the model's rate `(1/2,1)`, we would get `1/2 = 1` — a contradiction.  The stream function
is determined by the vorticity through the elliptic law (`Work.Construction.StatEqPhi`,
`Work.Elliptic.bslOp`), so "the same `φ`" is not an extra hypothesis in the intended reading; the
missing link is the *identification* of that elliptic inverse (see `NOTES.md` §findings).
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Gradient.Basic
import Submission.Work.CoreResiduals.Defs
import Submission.Work.CoreResiduals.ProfileData_T_eq_two
import Submission.Work.Spaces.c_bounds
import Submission.Work.FM.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.CoreResiduals

/-! ## The inhabitant -/

/-- **The delivered inhabitant of `ProfileData α`**, with its defining data recorded. -/
structure Inhabitant (α : NNReal) where
  /-- the profile/modulation data -/
  P : Work.ConstructionInstance.ProfileData α
  /-- the perturbation is zero -/
  hg : P.g = (fun _ _ => (0 : ℝ))
  /-- the blow-up time is `2` -/
  hT : P.T = 2
  /-- the rate constant is `1/2` -/
  hK : P.K = 1 / 2
  /-- the cut-off parameter is `4^{1/p}+1` -/
  hL : P.L = (4 : ℝ) ^ (1 / Work.ConstructionInstance.profExp α) + 1
  /-- the vorticity box is `20p` -/
  hM : P.M = 20 * Work.ConstructionInstance.profExp α
  /-- the `∂ₜ` box is `10p` -/
  hM₁ : P.M₁ = 10 * Work.ConstructionInstance.profExp α
  /-- the modulation is the affine function `1 - t/2` -/
  hlam : ∀ t : ℝ, P.lam t = 1 - t / 2

theorem inhabitant_exists {α : NNReal} (hα : 0 < (α : ℝ)) (hα13 : (α : ℝ) ≤ 1 / 3) :
    Nonempty (Inhabitant α) := by
  obtain ⟨D, hg, hT, hM, hM₁, hK, _hCg, _hCg', hL, hlam⟩ :=
    Work.ConstructionInstance.profileData_inhabited hα hα13
  exact ⟨D, hg, hT, hK, hL, hM, hM₁, hlam⟩

/-- The model data is a `ProfileData` with the recorded data (this is `IsModelData`). -/
theorem inhabitant_isModelData {α : NNReal} (I : Inhabitant α) :
    IsModelData I.P :=
  ⟨I.hT, I.hg, funext I.hlam, I.hL, I.hM, I.hM₁⟩

/-! ## `T` is forced

The delivered interface's own modulation fields force `T = 2` (`ProfileData_T_eq_two`), so the
`T = 2` conjunct of `IsModelData` is *not* a choice: it is the only value a `ProfileData` admits.
The paper's normalisation `T* = 1` is therefore excluded by the interface (see `NOTES.md` §4(a')). -/

/-- **Every `ProfileData` has blow-up time `2`.** -/
theorem two_le_T {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) : 2 ≤ P.T :=
  le_of_eq (ProfileData_T_eq_two P).symm

/-- **`T = 2` for every profile/modulation data** (a restatement of `ProfileData_T_eq_two` in the
vocabulary of this area). -/
theorem model_T_eq_two {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) : P.T = 2 :=
  ProfileData_T_eq_two P

/-! ## The rate of the model modulation -/

/-- The model modulation is the affine function `1 - t/2` everywhere, so its derivative is the
constant `-(1/2)`: the *rate* `κ = -λ̄'` of the design is `1/2`. -/
theorem model_deriv_lam {α : NNReal} (I : Inhabitant α) :
    ∀ t : ℝ, deriv I.P.lam t = -(1 / 2) := by
  intro t
  rw [show I.P.lam = fun s : ℝ => 1 - s / 2 from funext I.hlam]
  have h : HasDerivAt (fun s : ℝ => 1 - s / 2) (-(1 / 2)) t := by
    simpa using ((hasDerivAt_id t).div_const 2).const_sub 1
  exact h.deriv

/-- The model modulation's derivative in the design's (paper dilated-time) normalisation:
`-λ̄' = 1/2` at `t = 1`.  **This is *not* the rate entering the physical profile equation** — that
one is `2·(-λ̄')` (see the module header and `model_rate_physical`), and it equals `κ* = 1`. -/
theorem model_rate {α : NNReal} (I : Inhabitant α) : -(deriv I.P.lam 1) = 1 / 2 := by
  rw [model_deriv_lam I 1]; norm_num

/-- The reference rate of the paper's normalisation (`μ = 0`): `κ* = 1`. -/
theorem kappaStar_zero : Work.Stability.kappaStar 0 = 1 := by
  rw [Work.Stability.kappaStar_eq]; norm_num

/-- The reference spatial rate of the paper's normalisation (`μ = 0`): `b* = 1`. -/
theorem bStar_zero : Work.Stability.bStar 0 = 1 := by
  rw [Work.Stability.bStar_eq]; norm_num

/-- The design's normalisation `κ = -λ̄'` differs from the reference rate `κ* = 1` at the inhabitant.

**This is a discrepancy of conventions, not of mathematics**: `-λ̄'` is the rate in the paper's
dilated time, while the *physical* rate entering the delivered residual R1's profile equation is
`2·(-λ̄') = κ*` (`model_rate_physical_eq_reference`).  It is recorded here only so that the
`1/2`-dilation trap of `Work.Stability.Defs` is visible where the reader meets the inhabitant. -/
theorem model_rate_ne_reference {α : NNReal} (I : Inhabitant α) :
    -(deriv I.P.lam 1) ≠ Work.Stability.kappaStar 0 := by
  rw [model_rate I, kappaStar_zero]; norm_num

/-! ## The constant-rate rescaled vorticity equation -/

/-- **The rescaled (self-similar) vorticity equation at constant rates** `(κ,b)`: this is
`Work.Stability.DynEq` for `s`-independent profiles `f, φ`, i.e. the `(z,θ)`-form of the
self-similar vorticity equation, with `UVR` evaluated on the stream function `φ`. -/
def DynEqConst (α κ b : ℝ) (f φ : ℝ → ℝ → ℝ) : Prop :=
  ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
    κ * (f z θ + b * Work.Spaces.Dz f z θ) + Work.Construction.UVR α f φ z θ = 0

/-- **The `φ`-free difference of two constant-rate instances.**  `UVR α f φ` does not depend on
the rates, so the difference of the equations at `(κ,b)` and `(κ',b')` is the explicit identity
below — no hypothesis on the stream function is needed. -/
theorem dynEqConst_sub {α κ b κ' b' : ℝ} {f φ : ℝ → ℝ → ℝ}
    (h1 : DynEqConst α κ b f φ) (h2 : DynEqConst α κ' b' f φ) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      (κ - κ') * f z θ + (κ * b - κ' * b') * Work.Spaces.Dz f z θ = 0 := by
  intro z θ hzθ
  have h1' := h1 z θ hzθ
  have h2' := h2 z θ hzθ
  linarith

/-! ## The rigidity of the model profile -/

/-- `F_*(1,π/4) ≠ 0` (for `0 < α`, `α ≤ 1`): the profile at the point `z = 1` of the angular
maximum `θ = π/4`. -/
theorem Fstar_one_pi_div_four_ne_zero {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Construction.Fstar α 1 (Real.pi / 4) ≠ 0 := by
  have hc : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    intro h0; rw [h0] at h; norm_num at h
  have hGam : Work.Spaces.Gam α (Real.pi / 4) ≠ 0 := by
    rw [Work.Spaces.Gam]
    refine ne_of_gt (Real.rpow_pos_of_pos ?_ _)
    rw [Real.sin_pi_div_four, Real.cos_pi_div_four]
    norm_num
  rw [Work.Construction.Fstar]
  have : Work.FM.Fstar 1 = 1 / 2 := by
    rw [Work.FM.Fstar]; norm_num
  rw [this]
  exact mul_ne_zero (mul_ne_zero (ne_of_gt hα) (div_ne_zero hGam hc))
    (by norm_num)

/-- `D_z F_*(1,π/4) = 0`: `z∂_z F_*` vanishes at `z = 1` (the profile's maximum). -/
theorem Dz_Fstar_one_pi_div_four_eq_zero {α : ℝ} (hα : 0 < α) :
    Work.Spaces.Dz (Work.Construction.Fstar α) 1 (Real.pi / 4) = 0 := by
  rw [Work.Construction.Dz_Fstar_eq hα (by norm_num : (-1 : ℝ) < 1)]
  norm_num

/-- **THE RATE RIGIDITY (the model profile).**  If the model profile `F_*` satisfies the
constant-rate rescaled vorticity equation at the *reference* rates `(κ,b) = (1,1)` (the paper's
normalisation `μ = 0`) and also at the rates `(κ,b)` — for the *same* stream function `φ` — then
`κ = 1`.

This is a *conditional* rigidity statement about the profile equation alone.  **It does not, by
itself, obstruct the delivered residual R1**: as the module header records (the factor-2 audit), the
effective rate entering R1's profile equation at the inhabitant is `2·(-λ̄') = 1 = κ*`, i.e. the
*reference* rate — the hypothesis `h2` with `κ = 1/2` is not the one that R1 produces.  The lemma
remains useful as the sharp form of `DynEqConst`'s dependence on the rates: it is what forces the
bookkeeping to be done in the right time convention. -/
theorem fstar_rate_rigid {α κ b : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {φ : ℝ → ℝ → ℝ}
    (h1 : DynEqConst α 1 1 (Work.Construction.Fstar α) φ)
    (h2 : DynEqConst α κ b (Work.Construction.Fstar α) φ) : κ = 1 := by
  have hpt := dynEqConst_sub h1 h2 1 (Real.pi / 4)
    ⟨by norm_num, by
      constructor
      · positivity
      · linarith [Real.pi_pos]⟩
  rw [Dz_Fstar_one_pi_div_four_eq_zero hα, mul_zero, add_zero] at hpt
  have hne := Fstar_one_pi_div_four_ne_zero hα hα1
  have : 1 - κ = 0 := by
    rcases mul_eq_zero.mp hpt with h | h
    · exact h
    · exact absurd h hne
  linarith

/-! ## The audited rate of the inhabitant (the factor `2` of the time dilation) -/

/-- **The rate of the inhabitant's modulation in the physical time**: `-λ̄' = 1/2`, so the rate
entering the *physical* profile equation of residual R1, namely `2·(-λ̄')`, is `1`. -/
theorem model_rate_physical {α : NNReal} (I : Inhabitant α) :
    2 * (-(deriv I.P.lam 1)) = 1 := by
  rw [model_deriv_lam I 1]
  norm_num

/-- **The audited rate identity**: the effective rate of the delivered inhabitant *equals* the
paper's reference rate `κ* = 1`.

The paper's self-similar equation carries the `1/2` time dilation (tex 1319), so its profile
equation has the rate `-dλ̄/dt_paper`; the delivered residual R1 is the *physical* vorticity
equation (no `1/2`), so its profile equation has the rate `2·(-dλ̄/dt_phys)`.  Since
`ProfileData_T_eq_two` forces `T = 2` — which is the paper's blow-up time `T* = 1` in the physical
time — the two conventions give the same profile equation, and the inhabitant's effective rate is
`2·(1/2) = 1 = κ*`.  There is therefore **no rate mismatch** at the delivered inhabitant: the
profile `F_*` is stationary at the inhabitant's effective rates `(κ, b) = (1, 1)`. -/
theorem model_rate_physical_eq_reference {α : NNReal} (I : Inhabitant α) :
    2 * (-(deriv I.P.lam 1)) = Work.Stability.kappaStar 0 := by
  rw [model_rate_physical I, kappaStar_zero]

end Work.CoreResiduals
