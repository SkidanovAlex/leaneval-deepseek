/-
# `Work.ConstructionInstance.Data` — the residual interface, and the instantiation

`ConstructionData α` collects, field by field, exactly what the delivered chapters
(`Construction`, `Stability`, `LWP`, `Cyl`, `Spaces`, `FM`) do *not* provide about the
constructed self-similar solution, *together with* the honest objects this directory defines
(`g`, `omegaS (profExp α) g`, the cut-off datum `omega₀`).  `constructedSolution` then produces
`Work.SolutionDelivery.ConstructedSolution α` from it, deriving every field that the delivered
lemmas do provide (measurability of the vorticity, its `L¹`/`L^∞` bounds, the parity of the datum,
the maximal solution, the two Biot–Savart slices, …).

**This interface is the *unrepaired* one.**  It is kept because the deliverable asks for the
literal call shape `Work.SolutionDelivery.theorem_1_of_constructed (constructedSolution α hα hα1 D)
hα hα1`, and `Check.lean` certifies it; but it is **vacuous**:

* `Obstruction.not_nonempty_constructedSolution` proves `¬ Nonempty (ConstructedSolution α)` for
  `0 < α` (its fields `hBdd`/`hBddDt` bound `ω`/`∂ₜω` uniformly in `t`, which contradicts
  `hansatz` + `hlam_le`) — finding (B);
* `Refute.not_isContDiffHolder_omegaS_of_data` proves that the field `hcdh` is *false* for the
  honest vorticity — finding (A).

The **repaired** interface is `ConstructionDataFixed` in `Patch.lean`, with the derivations of
`hgbdd` (from the `ℋ²`-bound via `abs_le_of_linf_H2`) and of `hDivω` (from the `Cyl` divergence
dictionary via `div_selfSim_field`), the `λ̄`-weighted boxes on the half-window `preWindow T`
(findings B, C), and the reduction to the *inhabited* interface `ModulatedData`.  See `NOTES.md`
for the field-by-field attribution.

## The fields (chapter attribution in `NOTES.md` §4)

* `lwp` — the LWP chapter's analytic inputs; `T`/`hmax` are a *choice* of the LWP maximal solution
  (`exists_maximal_of_data`), not new content.
* `g` and its class data (`hvt`, `hsmooth`, `hquad0`, `hquad`, `Cg`/`hgbdd`, `hmeasP`, the
  uniform angular vanishing `Cv`/`hvan` and radial/angular moduli `Lg`,`Lθ`) — the perturbation of
  `§Modulation`, with the `L^∞` bound from `Work.Spaces.Linf_H2`.
* `hcdh` — the `C^{1,α}` clause demanded by `Work.SolutionDelivery.ConstructedSolution`, **false**
  for the honest profile (`Refute.lean`); `Repair.lean` certifies that the weaker `Holder α`
  clause is all the assembly consumes.
* `L` — the `St1` cut-off parameter.
* the solution side `R, M, M₁, smooth, ω, bsSliceExt, hSupp, hBdd, hBddDt, hDivω, hωcore, lam,
  hlam_pos, hlam_le, c₀, hc₀, hansatz` — the outputs of the `St0`–`St3` bootstrap and of the
  far-field transport.

## What is *derived* here

`ωS := omegaS (profExp α) g` (not a field); `ωS_meas` from `hmeasP`; `ωS_bdd` from `hgbdd` and
the explicit `F_*`-bound (`Basic.omegaS_norm_le`); `ωS_holder` from the Hölder chain
(`holder_omegaS_of_data`); `ωS_odd` from the parity dictionary (`isOddVorticity_omegaS` +
`isAxiNoSwirl_omega₀` + `Work.SolutionDelivery.isOdd_biotSavart_of_axiNoSwirl`); `ωS_div` from
`div_omega0_all` (proved for **every** `x`); and `hT`, `p`, `u`, `sol`, `odd`, … from `hmax`
through `Work.SolutionDelivery`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.ConstructionInstance.Defs
import Submission.Work.ConstructionInstance.Basic
import Submission.Work.ConstructionInstance.isOddVorticity_omegaS
import Submission.Work.ConstructionInstance.Meas
import Submission.Work.ConstructionInstance.isAxiNoSwirl_biotSavart
import Submission.Work.ConstructionInstance.div_omega0_all
import Submission.Work.ConstructionInstance.Repair
import Submission.Work.ConstructionInstance.holder_omegaS_of_data
import Submission.Work.SolutionDelivery.DatumOdd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.ConstructionInstance

/-- `Work.Cyl.rho` is invariant under the reflection `Work.LWP.reflZ`. -/
theorem rho_reflZ (x : R3) : Work.Cyl.rho (Work.LWP.reflZ x) = Work.Cyl.rho x := by
  have h1 : Work.Cyl.radSq (Work.LWP.reflZ x) = Work.Cyl.radSq x := by
    simp [Work.Cyl.radSq, Work.LWP.reflZ]
  have h2 : Work.Cyl.axial (Work.LWP.reflZ x) = -Work.Cyl.axial x := by
    simp [Work.Cyl.axial, Work.LWP.reflZ]
  rw [Work.Cyl.rho, Work.Cyl.rho, h1, h2, neg_sq]

theorem flipZ_smul (c : ℝ) (v : R3) : Work.LWP.flipZ (c • v) = c • Work.LWP.flipZ v := by
  ext i
  fin_cases i <;> simp [Work.LWP.flipZ]

/-- The cut-off is applied to a field of parity `IsOddVorticity`: the radial cut-off factor is
invariant under `reflZ` and `flipZ` is linear, so the parity is preserved. -/
theorem isOddVorticity_cutDatum {L : ℝ} {ω : R3 → R3}
    (hω : Work.LWP.IsOddVorticity ω) :
    Work.LWP.IsOddVorticity (Work.SolutionDelivery.cutDatum L ω) := by
  intro x
  rw [Work.SolutionDelivery.cutDatum, Work.Stability.omegaCut, Work.Stability.omegaCut,
    rho_reflZ, hω x, flipZ_smul, smul_neg]

/-- **The `Cyl` rotation dictionary for the cut-off datum, unconditionally**: the Biot–Savart
field of `omega₀ p g L = χ(ρ/L)·omegaS p g` is axisymmetric without swirl.  Indeed `omegaS p g` is
of the form `f(radial, axial) • e_θ` (take
`f r z = profile p g (rhoP r z ^ p) (thetaP r z)`) and the cut-off factor is radial, so the same
holds for `omega₀`; `isAxiNoSwirl_biotSavart` (this directory, a proof by rotation equivariance of
the Boole integral) then applies.  No hypothesis on `g` is used. -/
theorem isAxiNoSwirl_omega₀ (p : ℝ) (g : ℝ → ℝ → ℝ) (L : ℝ) :
    Work.Cyl.IsAxiNoSwirl (Work.LWP.biotSavart (omega₀ p g L)) := by
  refine isAxiNoSwirl_biotSavart (f := fun r z =>
    Work.Stability.chi (Work.Cyl.rhoP r z / L) *
      profile p g (Work.Cyl.rhoP r z ^ p) (Work.Cyl.thetaP r z)) (fun x => ?_)
  have hrho : Work.Cyl.rho x = Work.Cyl.rhoP (Work.Cyl.radial x) (Work.Cyl.axial x) := by
    rw [Work.Cyl.rho, Work.Cyl.rhoP, Work.Cyl.radial]
    congr 1
    simp only [Work.Cyl.radSq, Work.Cyl.axial]
    rw [Real.sq_sqrt (by positivity)]
  have hth : Work.Cyl.theta x = Work.Cyl.thetaP (Work.Cyl.radial x) (Work.Cyl.axial x) := rfl
  rw [omega₀_apply, omegaS_apply', hrho, hth, smul_smul]

/-- **The residual interface of the construction.**  Every field is a statement about the objects
of another chapter; `NOTES.md` records which chapter delivers it and which are proved here. -/
structure ConstructionData (α : NNReal) where
  /-- the LWP chapter's analytic inputs -/
  lwp : Work.LWP.LWPInputs α
  /-- the perturbation `g` of the self-similar profile `F = F_* + g` -/
  g : ℝ → ℝ → ℝ
  /-- `g` vanishes on the two angular boundaries -/
  hvt : Work.Spaces.VanishTheta g
  /-- `g` is `C^∞` on a neighbourhood of the closed quadrant (the `St1`-class of the fixed point) -/
  hsmooth : Work.Stability.SmoothFar g
  /-- `g` vanishes at `z = 0` (`Work.Stability.QuadVanish`) -/
  hquad0 : ∀ θ : ℝ, g 0 θ = 0
  /-- `∂_z g` vanishes at `z = 0` (`Work.Stability.QuadVanish`) -/
  hquad : ∀ θ : ℝ, Work.Spaces.pz g 0 θ = 0
  /-- the `L^∞` bound of `g`, from `Work.Spaces.Linf_H2` and the `ℋ²`-bound of the fixed point -/
  Cg : ℝ
  /-- `Cg ≥ 0` -/
  hCg : 0 ≤ Cg
  /-- `|g| ≤ Cg` on the closed quadrant -/
  hgbdd : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |g z θ| ≤ Cg
  /-- the scalar profile `x ↦ F(ρ(x)^p, θ(x))` is measurable in the physical variables (it is
  `C^∞` off the axis and the plane, and the odd extension is measurable); `Meas.lean` derives the
  measurability of the vector-valued vorticity from this -/
  hmeasP : MeasureTheory.AEStronglyMeasurable
    (fun x : R3 => profile (profExp α) g (Work.Cyl.Rc (profExp α) x) (Work.Cyl.theta x))
    MeasureTheory.volume
  /-- the `St1` cut-off parameter -/
  L : ℝ
  /-- `L > 0` -/
  hL : 0 < L
  /-- the **uniform angular vanishing** of the perturbation: `|g| ≤ Cv·Γ(α,θ)` (this is what
  makes `g` compatible with the `Γ`-vanishing of `F_*` and kills the direction jumps of `e_θ` near
  the axis) -/
  Cv : ℝ
  /-- `Cv ≥ 0` -/
  hCv : 0 ≤ Cv
  /-- `|g z θ| ≤ Cv·Γ(α,θ)` on the closed quadrant -/
  hvan : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |g z θ| ≤ Cv * Gamma (α : ℝ) θ
  /-- the **uniform radial modulus** of the perturbation: `|g(z,θ)-g(z',θ)| ≤ Lg·|z-z'|^α`
  (without it `omegaS` oscillates at the self-similar scale `z = ρ^{3α}` faster than `α`-Hölder
  allows; `NOTES.md` §4 records the counterexample) -/
  Lg : ℝ
  /-- `Lg ≥ 0` -/
  hLg : 0 ≤ Lg
  /-- the radial modulus -/
  hzk : ∀ z z' θ : ℝ, 0 ≤ z → 0 ≤ z' → θ ∈ Work.Spaces.Iθ →
    |g z θ - g z' θ| ≤ Lg * |z - z'| ^ (α : ℝ)
  /-- the **uniform angular modulus** of the perturbation: `|g(z,θ)-g(z,θ')| ≤ Lθ·|θ-θ'|^α`
  (idem, `NOTES.md` §4) -/
  Lθ : ℝ
  /-- `Lθ ≥ 0` -/
  hLθ : 0 ≤ Lθ
  /-- the angular modulus -/
  hzth : ∀ z θ θ' : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
    |g z θ - g z θ'| ≤ Lθ * |θ - θ'| ^ (α : ℝ)
  /-- **the paper's regime `α ≤ 1/3`** (equivalently profile exponent `p = 3α ≤ 1`), in which the
  construction is run -/
  hα13 : (α : ℝ) ≤ 1 / 3
  /-- **the `C^{1,α}` clause demanded by `Work.SolutionDelivery.ConstructedSolution`.**  This is
  *not* a property of the construction: `Refute.lean` proves that for every profile exponent
  `p < 1` the field `omegaS p 0` is not even differentiable at the origin, so for `α < 1/3`
  (the paper's regime, and in particular at `p = profExp α`) this field is *false*.  It is
  recorded here so that the interface can be instantiated at all; the repair is certified in
  `Repair.lean`. -/
  hcdh : IsContDiffHolder ℝ α (omegaS (profExp α) g)
  /-- the support radius of the vorticity -/
  R : ℝ
  /-- `R > 0` -/
  hR : 0 < R
  /-- the `L^∞` bound for the vorticity -/
  M : ℝ
  /-- `M ≥ 0` -/
  hM : 0 ≤ M
  /-- the profile is bounded by `M` (so that the same `M` bounds both `ωS` and `ω`); this is what
  `Basic.omegaS_norm_le` produces, from `hgbdd` and `Gamma ≤ 1` -/
  hMprof : 20 * profExp α + Cg ≤ M
  /-- the `L^∞` bound for `∂ₜω` -/
  M₁ : ℝ
  /-- `M₁ ≥ 0` -/
  hM₁ : 0 ≤ M₁
  /-- the maximal time -/
  T : ℝ
  /-- the LWP chapter's maximal solution with datum `u₀ = BS ω₀` -/
  hmax : Work.LWP.MaximalSolution α (Work.LWP.biotSavart (omega₀ (profExp α) g L)) T
  /-- `u.uncurry` is `C¹` on a neighbourhood of the two-sided window -/
  smooth : ContDiffOn ℝ 1 hmax.u.uncurry (Set.univ ×ˢ Work.SolutionDelivery.extWindow T)
  /-- the vorticity of the constructed solution -/
  ω : R3 → ℝ → R3
  /-- `u(x,t) = BS(ω(·,t)) x` on the open extended window -/
  bsSliceExt : ∀ t ∈ Work.SolutionDelivery.extWindow T, ∀ x : R3,
    hmax.u x t = Work.LWP.biotSavart (fun y => ω y t) x
  /-- the vorticity slices are supported in `B(0,R)` -/
  hSupp : ∀ t ∈ Work.SolutionDelivery.extWindow T, ∀ y : R3,
    ω y t ≠ 0 → y ∈ Metric.closedBall 0 R
  /-- `ω` is bounded by `M` -/
  hBdd : ∀ t ∈ Work.SolutionDelivery.extWindow T, ∀ y : R3, ‖ω y t‖ ≤ M
  /-- `∂ₜω` is bounded by `M₁` -/
  hBddDt : ∀ t ∈ Work.SolutionDelivery.extWindow T, ∀ y : R3, ‖timeDeriv ω y t‖ ≤ M₁
  /-- the vorticity slices are divergence free -/
  hDivω : ∀ t ∈ Work.SolutionDelivery.extWindow T,
    FiniteTimeSingularity.div (ω · t) = 0
  /-- the core `C^{1,α}` regularity of the vorticity -/
  hωcore : IsContDiffHolderOn ℝ α ω.uncurry
    (Work.StabilityFar.coreRegion (R + 1) ×ˢ Work.SolutionDelivery.extWindow T)
  /-- the modulation -/
  lam : ℝ → ℝ
  /-- `λ̄ > 0` on `[0,T)` -/
  hlam_pos : ∀ t ∈ Set.Ico 0 T, 0 < lam t
  /-- `λ̄(t) ≤ 2(T-t)` -/
  hlam_le : ∀ t ∈ Set.Ico 0 T, lam t ≤ 2 * (T - t)
  /-- the profile constant of `Work.StabilityFar.Profile.exists_Fstar_add_ge` -/
  c₀ : ℝ
  /-- `c₀ > 0` -/
  hc₀ : 0 < c₀
  /-- the `St5` interface -/
  hansatz : ∀ t ∈ Set.Ico 0 T, ∃ x : R3, c₀ * (α : ℝ) ≤ lam t * ‖ω x t‖

/-- **The construction instantiated.**  The self-similar vorticity is the *definition*
`omegaS (profExp α) D.g`; its measurability, its `L^∞` bound and its parity are *derived* from
the data (the last through the parity dictionary of `Cyl`); everything else is the data of
`ConstructionData`. -/
def constructedSolution (α : NNReal) (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) ≤ 1)
    (D : ConstructionData α) : Work.SolutionDelivery.ConstructedSolution α where
  lwp := D.lwp
  R := D.R
  hR := D.hR
  M := D.M
  hM := D.hM
  M₁ := D.M₁
  hM₁ := D.hM₁
  L := D.L
  hL := D.hL
  ωS := omegaS (profExp α) D.g
  ωS_meas := aestronglyMeasurable_omegaS D.hmeasP
  ωS_bdd := fun x => omegaS_norm_le (profExp_pos hα) (by
      have h := D.hα13; rw [profExp]; linarith) D.hgbdd D.hCg (fun θ hθ => by
      have hG : Gamma (profExp α / 3) θ ≤ 1 :=
        Gamma_le_one (by rw [profExp]; positivity) hθ
      have hG0 : 0 ≤ Gamma (profExp α / 3) θ := Gamma_nonneg hθ
      have hp0 : 0 ≤ profExp α := profExp_nonneg α
      nlinarith [D.hMprof, hG, hG0, hp0]) x
  ωS_cdh := D.hcdh
  ωS_div := div_omega0_all (profExp_pos hα) (by rw [profExp]; linarith [D.hα13]) D.hvt D.hsmooth D.L
  ωS_odd := Work.SolutionDelivery.isOdd_biotSavart_of_axiNoSwirl
    (isOddVorticity_cutDatum (isOddVorticity_omegaS (by
      rw [profExp]; positivity) D.hvt)) (isAxiNoSwirl_omega₀ _ _ _)
  T := D.T
  hmax := D.hmax
  smooth := D.smooth
  ω := D.ω
  bsSliceExt := D.bsSliceExt
  hSupp := D.hSupp
  hBdd := D.hBdd
  hBddDt := D.hBddDt
  hDivω := D.hDivω
  hωcore := D.hωcore
  lam := D.lam
  hlam_pos := D.hlam_pos
  hlam_le := D.hlam_le
  c₀ := D.c₀
  hc₀ := D.hc₀
  hansatz := D.hansatz

/-- **The maximal solution is *not* an extra assumption**: the LWP chapter's `maxExists` applied
to the cut-off datum produces a `T > 0` and a `MaximalSolution α (BS ω₀) T` from the residuals of
`ConstructionData` alone (through the repaired datum classes of `Repair.lean`).  The `T`/`hmax`
fields of `ConstructionData` are therefore a *choice* of that solution rather than new content. -/
theorem exists_maximal_of_data {α : NNReal} (D : ConstructionData α) (hα : 0 < (α : ℝ))
    (hα1 : (α : ℝ) ≤ 1) :
    ∃ T : ℝ, 0 < T ∧ Nonempty (Work.LWP.MaximalSolution α
      (Work.LWP.biotSavart (omega₀ (profExp α) D.g D.L)) T) :=
  exists_maximal_of_datum_of_holder D.lwp D.hL D.hM
    (aestronglyMeasurable_omegaS D.hmeasP)
    (omegaS_norm_le (profExp_pos hα) (by rw [profExp]; linarith [D.hα13]) D.hgbdd D.hCg
      (fun θ hθ => by
        have hG : Gamma (profExp α / 3) θ ≤ 1 :=
          Gamma_le_one (by rw [profExp]; positivity) hθ
        have hG0 : 0 ≤ Gamma (profExp α / 3) θ := Gamma_nonneg hθ
        have hp0 : 0 ≤ profExp α := profExp_nonneg α
        nlinarith [D.hMprof, hG, hG0, hp0]))
    (holder_omegaS_of_data (by positivity : (0:ℝ) < (α : ℝ)) D.hα13 D.hCv D.hLg D.hLθ D.hvt
      D.hquad0 D.hquad D.hvan D.hzk D.hzth (D.hsmooth.of_le (by simp [Work.Stability.smoothOrder])))
    hα hα1
    (div_omega0_all (profExp_pos hα) (by rw [profExp]; linarith [D.hα13]) D.hvt D.hsmooth D.L)
    (Work.SolutionDelivery.isOdd_biotSavart_of_axiNoSwirl
      (isOddVorticity_cutDatum (isOddVorticity_omegaS (by rw [profExp]; positivity) D.hvt))
      (isAxiNoSwirl_omega₀ _ _ _))

end Work.ConstructionInstance
