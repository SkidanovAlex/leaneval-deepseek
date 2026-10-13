import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.CoreResiduals.Defs
import Submission.Work.CoreResiduals.exists_eps_min_lam
import Submission.Work.CoreResiduals.solVort_localBdd_preWindow
import Submission.Work.CoreResiduals.solVort_localHolder_preWindow
import Submission.Work.CoreResiduals.solVort_timeDeriv_aesm_preWindow
import Submission.Work.ConstructionInstance.solVort_integrable
import Submission.Work.ConstructionInstance.hasDerivAt_selfSimVort_slice
import Submission.Work.ConstructionInstance.aestronglyMeasurable_of_continuousOn_core_of_support
import Submission.Work.ConstructionInstance.solVort_holder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `solVort_BSAdmissibleOnWindow` — the admissibility bundle of the constructed vorticity

## The measurability clause, and why it must be local in `t`

`Work.CoreResiduals.BSAdmissibleOnWindow` constrains the measurability of the slices only *near the
times of the half-window* `preWindow T = Ioo (-2) T`:

  `∀ t₀ ∈ preWindow T, ∃ ε > 0, ∀ t ∈ Ioo (t₀-ε) (t₀+ε), AEStronglyMeasurable (ω · t) volume`.

A *global* clause `∀ t : ℝ, AEStronglyMeasurable (ω · t) volume` would be **false** for
`ω = solVort P`, for every `P` whose modulation `λ̄` takes a negative value (e.g. the delivered model
data `T = 2`, `λ̄(t) = 1 - t/2`, at `t = 4`, where `λ̄(4) = -1`), because `solVort` evaluates the
profile at the self-similar variable `z = ρ(x)^p / λ̄(t)` (`p = profExp α`): for `λ̄(t) < 0` that
argument is **negative**, and `ProfileData` constrains the perturbation `g` only on `{z > -1}`
(`hsmooth : SmoothNbhd`) and on `{z ≥ 0}` (all remaining `g`-fields: `hvan`, `hzk`, `hzth`, `hg2`,
`hgdiff`, `hmem`, `hCgbig`, and `hmeasP`, which composes `g` with `Rc p x = ρ(x)^p ≥ 0`) — plus the
two lines `θ = 0, π/2` (`hvt`).  So `g` may be an arbitrary non-measurable function of `z` on
`{z ≤ -1}`, and choosing `g(z,θ) = 1_A(-z)·ϕ(θ)` there (with `A` non-measurable, `ϕ` smooth and
vanishing at `θ = 0, π/2`) keeps every `ProfileData` field satisfied while making the `t = 4` slice
`-χ(ρ(x)/L)·(F_*(-ρ(x)^p, θ(x)) + 1_A(ρ(x)^p)·ϕ(θ(x)))·e_θ(x)` non-measurable (its inner product
with `e₂` is a non-vanishing measurable multiple of `1_A(‖x‖)` on the positive-measure set
`{1 < ‖x‖ < L, x₁ > 0, x₃ > 0}`; Fubini in polar coordinates then forces `A ∩ (1,L)` to be
Lebesgue measurable).

Localising the clause is also exactly what the consumer `BiotSavartSpacetimeC1` needs — its
conclusion is claimed only at `t₀ ∈ preWindow T` — and `Defs.lean` now states the bundle in that
local form.  With it, the bundle **is** provable, which is what this file does.

## The eight conjuncts

Every conjunct is proved separately (the names are listed in the assembly at the bottom), from the
lemmas named in the original docstring plus the localisation helper
`CoreResiduals.exists_eps_min_lam` (a positive lower bound `m ≤ λ̄` and a two-sided neighbourhood
inside the open window `preWindow T`):

* support (global in `t`): `Work.ConstructionInstance.solVort_supp`;
* local boundedness: `Work.ConstructionInstance.solVort_bdd` (`CoreResiduals.solVort_localBdd_preWindow`);
* local `x`-Hölder regularity: `Work.ConstructionInstance.solVort_holder`
  (`CoreResiduals.solVort_localHolder_preWindow`);
* slice measurability near `preWindow T`: `solVort_cont` +
  `aestronglyMeasurable_of_continuousOn_core_of_support` (`solVort_aesm_preWindow`,
  `solVort_aesm_local`);
* time differentiability: `Work.ConstructionInstance.hasDerivAt_selfSimVort_slice`
  (`solVort_hasDerivAt_local`);
* the `∂ₜ`-bound: `Work.ConstructionInstance.solVort_bddDt` (`solVort_bddDt_local`);
* measurability of the `∂ₜ`-slices: `CoreResiduals.solVort_timeDeriv_aesm_preWindow`
  (difference quotients of the nearby measurable slices, `solVort_timeDeriv_aesm_local`).
-/

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.CoreResiduals

/-! ## The conjuncts for `solVort P` -/

/-- The support radius is positive: `R ≥ 2L > 0`. -/
theorem solVort_R_pos {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) : 0 < P.R := by
  have hL2 : 0 < 2 * P.L := by linarith [P.hL]
  linarith [P.hRbig]

/-- The support conjunct, in the global-in-`t` form of the bundle
(`Work.ConstructionInstance.solVort_supp`). -/
theorem solVort_supp_all {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) :
    ∀ t : ℝ, ∀ y : R3, solVort P y t ≠ 0 → y ∈ Metric.closedBall 0 P.R :=
  Work.ConstructionInstance.solVort_supp P

/-- **Measurability of the slices on the half-window** (`∀ t ∈ preWindow T` form).  For such a `t`
the modulation is positive, the slice is continuous on the core ball (`solVort_cont`), and it is
supported in `B(0,R)`, so `aestronglyMeasurable_of_continuousOn_core_of_support` applies. -/
theorem solVort_aesm_preWindow {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) :
    ∀ t ∈ Work.ConstructionInstance.preWindow P.T,
      MeasureTheory.AEStronglyMeasurable (fun y : R3 => solVort P y t) MeasureTheory.volume := by
  intro t ht
  have hcont : ContinuousOn (fun y : R3 => solVort P y t)
      (Work.StabilityFar.coreRegion (P.R + 1)) := by
    have hmaps : Set.MapsTo (fun y : R3 => (y, t)) (Work.StabilityFar.coreRegion (P.R + 1))
        (Work.StabilityFar.coreRegion (P.R + 1) ×ˢ Work.ConstructionInstance.preWindow P.T) :=
      fun y hy => ⟨hy, ht⟩
    exact (Work.ConstructionInstance.solVort_cont P).comp
      (continuous_id.prodMk continuous_const).continuousOn hmaps
  exact Work.ConstructionInstance.aestronglyMeasurable_of_continuousOn_core_of_support
    (R := P.R) (R' := P.R + 1) (by linarith [P.hR]) hcont
    (fun y hy => Work.ConstructionInstance.solVort_supp P t y hy)

/-- **The fifth conjunct** (measurability of the slices near the half-window), in the
`ε`-neighbourhood shape in which the bundle states it: take the neighbourhood inside `preWindow T`
and apply `solVort_aesm_preWindow`. -/
theorem solVort_aesm_local {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) :
    ∀ t₀ ∈ Work.ConstructionInstance.preWindow P.T, ∃ ε : ℝ, 0 < ε ∧
      ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε),
        MeasureTheory.AEStronglyMeasurable (fun y : R3 => solVort P y t) MeasureTheory.volume := by
  intro t₀ ht₀
  obtain ⟨ε, hε, hsub, m, hm, hmle⟩ := exists_eps_min_lam P.hlam P.hlamdif ht₀
  exact ⟨ε, hε, fun t ht => solVort_aesm_preWindow P t (hsub ⟨le_of_lt ht.1, le_of_lt ht.2⟩)⟩

/-- **The sixth conjunct** (time differentiability near the half-window).  On a two-sided
neighbourhood of `t₀ ∈ preWindow T`, chosen inside the half-window (where `λ̄ > 0` and `λ̄` is
differentiable), the slice is differentiable in `t` with derivative
`timeDeriv (solVort P) · · t`: this is `Work.ConstructionInstance.hasDerivAt_selfSimVort_slice`. -/
theorem solVort_hasDerivAt_local {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) :
    ∀ t₀ ∈ Work.ConstructionInstance.preWindow P.T, ∃ ε : ℝ, 0 < ε ∧
      ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε), ∀ y : R3,
        HasDerivAt (fun s : ℝ => solVort P y s)
          (FiniteTimeSingularity.timeDeriv (solVort P) y t) t := by
  intro t₀ ht₀
  obtain ⟨ε, hε, hsub, m, hm, hmle⟩ := exists_eps_min_lam P.hlam P.hlamdif ht₀
  refine ⟨ε, hε, fun t ht y => ?_⟩
  have htpre : t ∈ Work.ConstructionInstance.preWindow P.T :=
    hsub ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hd := Work.ConstructionInstance.hasDerivAt_selfSimVort_slice
    (p := Work.ConstructionInstance.profExp α) (g := P.g) (L := P.L) (lam := P.lam) (T := P.T)
    P.hgdiff P.hlam P.hlamdif htpre y
  simpa only [Work.ConstructionInstance.solVort] using hd

/-- **The seventh conjunct** (`∂ₜ`-bound near the half-window), from the box
`Work.ConstructionInstance.solVort_bddDt`.  The bundle's clause is un-normalised (no `λ̄²` weight),
and on the neighbourhood `λ̄ ≥ m > 0`, so `M₁ := P.M₁ / m²`. -/
theorem solVort_bddDt_local {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) :
    ∀ t₀ ∈ Work.ConstructionInstance.preWindow P.T, ∃ ε : ℝ, 0 < ε ∧ ∃ M₁ : ℝ,
      ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε), ∀ y : R3,
        ‖FiniteTimeSingularity.timeDeriv (solVort P) y t‖ ≤ M₁ := by
  intro t₀ ht₀
  obtain ⟨ε, hε, hsub, m, hm, hmle⟩ := exists_eps_min_lam P.hlam P.hlamdif ht₀
  refine ⟨ε, hε, P.M₁ / m ^ 2, fun t ht y => ?_⟩
  have htpre : t ∈ Work.ConstructionInstance.preWindow P.T :=
    hsub ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hmle' : m ≤ P.lam t := hmle t ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hlt : 0 < P.lam t := P.hlam t htpre
  have hm2 : m ^ 2 ≤ (P.lam t) ^ 2 := by nlinarith [hm, hmle']
  have hm2pos : (0 : ℝ) < m ^ 2 := by positivity
  have hb := Work.ConstructionInstance.solVort_bddDt P t htpre y
  have h1 : ‖FiniteTimeSingularity.timeDeriv (solVort P) y t‖ ≤ P.M₁ / (P.lam t) ^ 2 := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < (P.lam t) ^ 2), mul_comm]
    exact hb
  have h2 : P.M₁ / (P.lam t) ^ 2 ≤ P.M₁ / m ^ 2 :=
    div_le_div_of_nonneg_left P.hM₁ hm2pos hm2
  linarith

/-- **The eighth conjunct** (measurability of the `∂ₜ`-slices near the half-window), in the
`ε`-neighbourhood shape of the bundle, from the `preWindow`-global statement
`CoreResiduals.solVort_timeDeriv_aesm_preWindow`. -/
theorem solVort_timeDeriv_aesm_local {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) :
    ∀ t₀ ∈ Work.ConstructionInstance.preWindow P.T, ∃ ε : ℝ, 0 < ε ∧
      ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε), MeasureTheory.AEStronglyMeasurable
        (fun y : R3 => FiniteTimeSingularity.timeDeriv (solVort P) y t) MeasureTheory.volume := by
  intro t₀ ht₀
  obtain ⟨ε, hε, hsub, m, hm, hmle⟩ := exists_eps_min_lam P.hlam P.hlamdif ht₀
  refine ⟨ε, hε, fun t ht => ?_⟩
  exact solVort_timeDeriv_aesm_preWindow P t (hsub ⟨le_of_lt ht.1, le_of_lt ht.2⟩)

/-! ## The bundle -/

/-- The model data satisfies the half-window admissibility bundle of `Work.CoreResiduals.BSAdmissibleOnWindow`. Support and measurability of the slices are global; local boundedness, local x-Hölder regularity, time differentiability, the bound on the time derivative and the measurability of the derivative slice are claimed only near times t₀ in preWindow P.T, where the modulation is positive and locally bounded away from zero. The time differentiability is hasDerivAt_selfSimVort_slice, the derivative bound is bddDt_selfSimVort, and the local x-Hölder regularity comes from solVort_holder. -/
theorem solVort_BSAdmissibleOnWindow {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) :
    Work.CoreResiduals.BSAdmissibleOnWindow (Work.ConstructionInstance.solVort P) P.R P.T :=
  ⟨solVort_R_pos P, solVort_supp_all P, solVort_localBdd_preWindow P,
    solVort_localHolder_preWindow P, solVort_aesm_local P, solVort_hasDerivAt_local P,
    solVort_bddDt_local P, solVort_timeDeriv_aesm_local P⟩

end Work.CoreResiduals
