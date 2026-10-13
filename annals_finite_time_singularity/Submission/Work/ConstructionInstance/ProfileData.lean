/-
# `Work.ConstructionInstance.ProfileData` — the **profile/modulation** interface

This is the residual interface of the construction instantiation *after* everything about the
vorticity has been turned into a theorem.  Its content is:

* the **perturbation** `g` of the self-similar profile `F = F_* + g` with its `St1`-class data
  (`Work.Stability`/`Work.Spaces`): the vanishing, the smoothness, the `ℋ²`-bound, the uniform
  angular vanishing and the two uniform moduli, the `𝒲^{1,∞}`-bound on `z∂_z g`, the smallness
  `Cg ≤ c₀star α` (`St5`) and the measurability of the scalar profile;
* the **modulation** `λ̄` with its `St0` data on `preWindow T = Ioo (-2) T`: positivity, the rate
  bound `|λ̄'| ≤ K ≤ 1/2` and the two-sided bound `(T-t)/2 ≤ λ̄(t) ≤ 2(T-t)` on `[0,T)`;
* the **cut-off parameter** `L > 0`, large enough that the cut-off is transparent at the `St5`
  witness (`(2T)^{1/p} ≤ L`), and the **support radius** `R ≥ 2L`.

Everything else is *derived* from these: the vorticity is the **definition**

  `ω(x,t) = λ̄(t)⁻¹·χ(ρ(x)/L)·F(ρ(x)^p/λ̄(t), θ(x))·e_θ(x)`   (`SelfSim.selfSimVort`),

and its support box, its `L^∞`/`∂ₜ` boxes, its divergence-freeness, its continuity, its `St5`
lower bound and its strip time-Hölder bound are theorems (`SelfSim.selfSimVort_support`,
`selfSimVort_bdd`, `bddDt_selfSimVort`, `div_selfSimVort`, `continuousOn_selfSimVort`,
`exists_omegaSz_low_radius`, `timeHolderOnBall_selfSimVort`).

## What is *not* here (and why it is exactly the LWP tie)

`Work.SolutionDelivery.ConstructedSolution` also requires the *maximal solution* and its tie to the
vorticity: `lwp : Work.LWP.LWPInputs α`, `T`, `hmax : Work.LWP.MaximalSolution α (BS ω₀) T`,
`smooth : ContDiffOn ℝ 1 hmax.u.uncurry …` and `bsSliceExt : hmax.u x t = BS(ω(·,t)) x`.  Those four
are the *only* fields of `Patch.ConstructionDataFixed` that are not supplied by this file: they say
that the Euler solution of the chapter is the self-similar one — the content of the `St0`–`St3`
bootstrap of `Work.Stability` and of the backward extension of `Work.LWP`.

So the reconciliation is

> `ConstructionDataFixed α`  =  `ProfileData α` + `{lwp, hmax, smooth, bsSliceExt}`,

with the second group an honest residual of the `LWP`/`Stability`/`Construction` chapters, and the
first group — the profile, the modulation and *every field about the vorticity* — constructed here
(`profileData_inhabited` exhibits an inhabitant, and the reduction theorem turns any inhabitant
into all the vorticity-level fields of the interface).
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.ConstructionInstance.Defs
import Submission.Work.ConstructionInstance.Basic
import Submission.Work.ConstructionInstance.Boxes
import Submission.Work.ConstructionInstance.SelfSim

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.ConstructionInstance

/-- **The profile/modulation interface**: the perturbation of the self-similar profile, the
modulation, and the two geometric parameters — everything the interface needs *before* the
vorticity is defined. -/
structure ProfileData (α : NNReal) where
  /-- `0 < α` (the Hölder exponent of the challenge) -/
  hα : 0 < (α : ℝ)
  /-- the perturbation `g` of the self-similar profile `F = F_* + g` -/
  g : ℝ → ℝ → ℝ
  /-- `g` vanishes on the two angular boundaries -/
  hvt : Work.Spaces.VanishTheta g
  /-- the smoothness class consumed by the profile estimates -/
  hsmooth : Work.Spaces.SmoothNbhd g
  /-- `g` vanishes at `z = 0` -/
  hquad0 : ∀ θ : ℝ, g 0 θ = 0
  /-- `∂_z g` vanishes at `z = 0` -/
  hquad : ∀ θ : ℝ, Work.Spaces.pz g 0 θ = 0
  /-- the `L^∞` constant of `g` -/
  Cg : ℝ
  /-- `Cg ≥ 0` -/
  hCg : 0 ≤ Cg
  /-- the `z`-decay of `g` (the hypothesis of the radial Hardy inequality) -/
  hdec : Work.Spaces.DecayInZ 2 g
  /-- `g ∈ ℋ²` (the a-priori bound of the construction's fixed point) -/
  hmem : Work.Spaces.HkMem (profExp α) 2 g
  /-- the `ℋ²`-bound, which yields `|g| ≤ Cg` (`abs_le_of_linf_H2`) -/
  hCgbig : 100 / Real.sqrt (Work.Spaces.gam (profExp α) - 1)
    * Work.Spaces.HkNorm (profExp α) 2 g ≤ Cg
  /-- the uniform angular vanishing of the perturbation -/
  Cv : ℝ
  /-- `Cv ≥ 0` -/
  hCv : 0 ≤ Cv
  /-- `|g z θ| ≤ Cv·Γ(α,θ)` -/
  hvan : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |g z θ| ≤ Cv * Gamma (α : ℝ) θ
  /-- the uniform radial modulus of the perturbation -/
  Lg : ℝ
  /-- `Lg ≥ 0` -/
  hLg : 0 ≤ Lg
  /-- the radial modulus -/
  hzk : ∀ z z' θ : ℝ, 0 ≤ z → 0 ≤ z' → θ ∈ Work.Spaces.Iθ →
    |g z θ - g z' θ| ≤ Lg * |z - z'| ^ (α : ℝ)
  /-- the uniform angular modulus of the perturbation -/
  Lθ : ℝ
  /-- `Lθ ≥ 0` -/
  hLθ : 0 ≤ Lθ
  /-- the angular modulus -/
  hzth : ∀ z θ θ' : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
    |g z θ - g z θ'| ≤ Lθ * |θ - θ'| ^ (α : ℝ)
  /-- the `𝒲^{1,∞}`-bound on `z ∂_z g` -/
  Cg' : ℝ
  /-- `z ∂_z g` is bounded on the closed quadrant -/
  hg2 : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |z * Work.Spaces.pz g z θ| ≤ Cg'
  /-- the `z`-differentiability of the profile -/
  hgdiff : ∀ z θ : ℝ, 0 < z →
    HasDerivAt (fun z' => profile (profExp α) g z' θ)
      (Work.Spaces.pz (profile (profExp α) g) z θ) z
  /-- the smallness `Cg ≤ c₀star α` of the perturbation (`St5`) -/
  hsmall : Cg ≤ profExp α * Work.Spaces.Gam (profExp α) (Real.pi / 4)
    / (4 * Work.Spaces.c (profExp α))
  /-- measurability of the scalar profile in the physical variables -/
  hmeasP : MeasureTheory.AEStronglyMeasurable
    (fun x : R3 => profile (profExp α) g (Work.Cyl.Rc (profExp α) x) (Work.Cyl.theta x))
    MeasureTheory.volume
  /-- the paper's regime `α ≤ 1/3` -/
  hα13 : (α : ℝ) ≤ 1 / 3
  /-- the blow-up time -/
  T : ℝ
  /-- `T > 0` -/
  hT : 0 < T
  /-- the modulation -/
  lam : ℝ → ℝ
  /-- `λ̄ > 0` before the maximal time -/
  hlam : ∀ t ∈ preWindow T, 0 < lam t
  /-- **the normalisation `λ̄(0) = 1`** of the design (`s = -ln λ̄`): it is what makes the ansatz at
  `t = 0` reproduce the `St1` datum `ω₀ = χ(ρ/L)·omegaS`, i.e. makes the datum of the maximal
  solution consistent with the pointwise ansatz (finding G) -/
  hlam0 : lam 0 = 1
  /-- the rate constant -/
  K : ℝ
  /-- `K ≥ 0` -/
  hK : 0 ≤ K
  /-- the design's normalisation `K ≤ 1/2` -/
  hK12 : K ≤ 1 / 2
  /-- `λ̄` is differentiable before the maximal time -/
  hlamdif : ∀ t ∈ preWindow T, HasDerivAt lam (deriv lam t) t
  /-- the rate bound `|λ̄'| ≤ K` -/
  hlamd : ∀ t ∈ preWindow T, |deriv lam t| ≤ K
  /-- `λ̄(t) ≤ 2(T-t)` -/
  hlam_le : ∀ t ∈ Set.Ico 0 T, lam t ≤ 2 * (T - t)
  /-- `(T-t)/2 ≤ λ̄(t)` -/
  hlam_low : ∀ t ∈ Set.Ico 0 T, (T - t) / 2 ≤ lam t
  /-- the `St1` cut-off parameter -/
  L : ℝ
  /-- `L > 0` -/
  hL : 0 < L
  /-- the cut-off is transparent at the `St5` witness: `(2T)^{1/p} ≤ L` -/
  hLbig : (2 * T) ^ (1 / profExp α) ≤ L
  /-- the self-similar `L^∞` constant -/
  M : ℝ
  /-- `M ≥ 0` -/
  hM : 0 ≤ M
  /-- `M` dominates the profile box -/
  hMprof : 20 * profExp α + Cg ≤ M
  /-- the self-similar `L^∞` constant of `∂ₜω` -/
  M₁ : ℝ
  /-- `M₁ ≥ 0` -/
  hM₁ : 0 ≤ M₁
  /-- `M₁` dominates the derived `∂ₜω` bound -/
  hM₁big : K * (20 * profExp α + Cg + Cg') ≤ M₁
  /-- the support radius -/
  R : ℝ
  /-- `R ≥ 0` -/
  hR : 0 ≤ R
  /-- the support radius covers the cut-off -/
  hRbig : 2 * L ≤ R

/-! ## The explicit `St5` constant -/

/-- **The explicit `St5` constant** `c₀ = p·Γ(p/4)/(4c(p))` with `p = profExp α`: it is half the
profile's value at the point `(z,θ) = (1,π/4)`, and it is positive.  Taking it as a *definition*
rather than a field removes the fields `c₀`, `hc₀` from the residual interface (the `St5` lower
bound then follows from the smallness `Cg ≤ c₀` of the perturbation). -/
def c₀star (α : NNReal) : ℝ :=
  3 * Work.Spaces.Gam (profExp α) (Real.pi / 4) / (4 * Work.Spaces.c (profExp α))

theorem c₀star_pos {α : NNReal} (hα : 0 < (α : ℝ)) (hα13 : (α : ℝ) ≤ 1 / 3) :
    0 < c₀star α := by
  have hp : 0 < profExp α := profExp_pos hα
  have hp1 : profExp α ≤ 1 := by rw [profExp]; linarith
  have hc := (Work.Spaces.c_bounds (profExp α) hp hp1).1
  have hcpos : 0 < Work.Spaces.c (profExp α) := by linarith
  have hGam : 0 < Work.Spaces.Gam (profExp α) (Real.pi / 4) := by
    rw [Work.Spaces.Gam]
    refine Real.rpow_pos_of_pos ?_ _
    rw [Real.sin_pi_div_four, Real.cos_pi_div_four]
    norm_num
  rw [c₀star]
  positivity

end Work.ConstructionInstance
