import Mathlib.Tactic.Have
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Kinetic.abs_trialVal_sub_le
import Submission.Work.BoseKinLoc.Kinetic.neuFrac_eq_sInf_trialBall
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Kinetic

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Elementary assembly lemmas for the Lipschitz estimate

The two analytic ingredients are delegated:

* `neuFrac_eq_sInf_trialBall` (**ball reduction**): the `sInf` defining `neuFrac` is unchanged
  when the smooth compactly supported trials are restricted to the `L²(Λ)`-ball of radius
  `2R/a2`, provided `∫_Λφ² ≤ R²`;
* `abs_trialVal_sub_le` (**Lipschitz on the ball**): for trials in that ball,
  `|F ψ g − F ψ' g| ≤ 6R√(∫_Λ(ψ−ψ')²)`.

What is assembled here is the passage from the trial values to the two `sInf`s: with the
matching-trial estimate one compares every trial value of one state with the *infimum* over the
trials of the other (`le_sInf_add_of_forall_le`), giving the two one-sided inequalities
`neuFrac ψ ≤ neuFrac ψ' + K` and `neuFrac ψ' ≤ neuFrac ψ + K`, which combine to
`|neuFrac ψ − neuFrac ψ'| ≤ K`. -/

/-- **Order-theoretic comparison of an infimum.**  If `T` is a nonempty set of reals and
`a ≤ t + K` for every `t ∈ T`, then `a ≤ sInf T + K`. -/
lemma le_sInf_add_of_forall_le {T : Set ℝ} {a K : ℝ} (hne : T.Nonempty)
    (h : ∀ t ∈ T, a ≤ t + K) : a ≤ sInf T + K := by
  have h' : a - K ≤ sInf T := le_csInf hne fun t ht => by linarith [h t ht]
  linarith

/-- **Every trial value bounds `neuFrac` from above**: `neuFrac ℓ a² u φ ≤ F(φ,g)`
(`csInf_le` in the full trial set). -/
lemma neuFrac_le_trialVal {ℓ a2 : ℝ} (ha2 : 0 ≤ a2) (u : ℝ³) {φ g : ℝ³ → ℝ}
    (hφ : MeasureTheory.Integrable (fun z : ℝ³ => (φ z) ^ 2))
    (hg : ContDiff ℝ (⊤ : ENat) g) (hgs : HasCompactSupport g) :
    Work.BoseKinLoc.neuFrac ℓ a2 u φ ≤ trialVal ℓ a2 u φ g := by
  rw [neuFrac_eq_sInf_trialSet]
  exact csInf_le (bddBelow_trialSet' ha2 u hφ) ⟨g, hg, hgs, rfl⟩

/-- **One-sided Lipschitz estimate for a matching pair of trials.**  For a trial `g` in the
ball `∫_Λg² ≤ (2R/a²)²`,

`F(ψ,g) ≤ F(ψ',g) + 6R√(∫_Λ(ψ−ψ')²)`,

the one-sided form of `abs_trialVal_sub_le` that is used to compare trial values with the
*infimum* over the trials of the other state. -/
lemma trialVal_sub_le_of_ball {ℓ a2 R : ℝ} (hℓ : 0 < ℓ) (ha2 : 0 < a2) (hR : 0 < R)
    (u : ℝ³) {ψ ψ' g : ℝ³ → ℝ}
    (hψm : MeasureTheory.AEStronglyMeasurable ψ volume)
    (hψ'm : MeasureTheory.AEStronglyMeasurable ψ' volume)
    (hψ : MeasureTheory.Integrable (fun z : ℝ³ => (ψ z) ^ 2))
    (hψ' : MeasureTheory.Integrable (fun z : ℝ³ => (ψ' z) ^ 2))
    (hψd : MeasureTheory.Integrable (fun z : ℝ³ => (ψ z - ψ' z) ^ 2))
    (hRψ : ∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z) ^ 2 ≤ R ^ 2)
    (hRψ' : ∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ' z) ^ 2 ≤ R ^ 2)
    (hg : ContDiff ℝ (⊤ : ENat) g) (hgs : HasCompactSupport g)
    (hg2 : ∫ z in Work.BoseKinLoc.lamBox ℓ u, (g z) ^ 2 ≤ (2 * R / a2) ^ 2) :
    trialVal ℓ a2 u ψ g
      ≤ trialVal ℓ a2 u ψ' g
        + 6 * R * Real.sqrt (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z - ψ' z) ^ 2) := by
  have h := abs_trialVal_sub_le hℓ ha2 hR u hψm hψ'm hψ hψ' hψd hRψ hRψ' hg hgs hg2
  have h2 := le_abs_self (trialVal ℓ a2 u ψ g - trialVal ℓ a2 u ψ' g)
  linarith

/-- Lipschitz estimate for the box Neumann fraction with respect to the `L²(Λ)`-norm of the
state: if `∫_Λψ² ≤ R²` and `∫_Λψ'² ≤ R²` (where `Λ = lamBox ℓ u`, `R > 0`, `a2 > 0`) then
`|neuFrac ℓ a2 u ψ − neuFrac ℓ a2 u ψ'| ≤ 6R·√(∫_Λ(ψ−ψ')²)`.

**Measurability is essential** (see `Submission/Work/BoseKinLoc/Kinetic/neuFrac_lipschitz.lean`
for the refutation of the version without `hψm`, `hψ'm`): the middle term of the trial
functional is a *Bochner* integral whose value is `0` for a non-a.e.-measurable integrand, so
without `hψm` one can flip the sign of `ψ` on a non-measurable set without changing `ψ²` and
make every cross term junk; with `hψm`, `hψ'm` every pairing is honest because
`|ψg| ≤ (ψ²+g²)/2` is an integrable dominating function and `ψg` is a.e. measurable.

Proof strategy (elementary; **no** spectral/resolvent theory is needed).  Write
`F(φ,g) = ∫_Λφ² − 2a2∫_Λφg + a2(Σ_k∫_Λ(∂_kg)² + a2∫_Λg²)` for smooth compactly supported `g`,
and `S_M(φ) = {F(φ,g) | g smooth, compactly supported, ∫_Λg² ≤ M²}`.

1. For `M := 2R/a2` one has `neuFrac ℓ a2 u φ = sInf (S_M(φ))` whenever `∫_Λφ² ≤ R²`: with
   `‖·‖` the `L²(Λ)`-norm, `Q(g) := Σ_k∫_Λ(∂_kg)² + a2∫_Λg² ≥ a2‖g‖²` and Cauchy–Schwarz give
   `F(φ,g) − ∫_Λφ² ≥ a2‖g‖(a2‖g‖ − 2‖φ‖)`; hence `‖g‖ > 2R/a2` forces
   `F(φ,g) ≥ ∫_Λφ² = F(φ,0)`, so trials outside the ball never lower the infimum.  Use
   `csInf_le`/`le_csInf` with `Work.BoseKinLoc.NeuFrac.bddBelow_trialSet` (for `BddBelow`) and
   the trial `g = 0` (nonemptiness).
2. For trials inside the ball (`‖g‖ ≤ M`),
   `|F(ψ,g) − F(ψ',g)| ≤ (‖ψ+ψ'‖ + 2a2‖g‖)·‖ψ−ψ'‖ ≤ (2R + 4R)·‖ψ−ψ'‖ = 6R·‖ψ−ψ'‖`,
   since `∫_Λ(ψ+ψ')² ≤ 2∫_Λψ² + 2∫_Λψ'² ≤ 4R²`; bound `∫_Λ(ψ−ψ')(ψ+ψ')` and `∫_Λ(ψ−ψ')g` by
   Cauchy–Schwarz (`Work.BSKinetic.Decomp.abs_integral_mul_le_sqrt_mul_sqrt`, whose `MemLp`
   hypotheses come from `MeasureTheory.memLp_two_iff_integrable_sq` together with `hψm`,
   `hψ'm`).
3. Both infima in (1) are over the *same* trial ball, so
   `|sInf (S_M(ψ)) − sInf (S_M(ψ'))| ≤ 6R‖ψ−ψ'‖`. -/
theorem neuFrac_lipschitz_of_aemeasurable {ℓ a2 R : ℝ} (hℓ : 0 < ℓ) (ha2 : 0 < a2) (hR : 0 < R)
    (u : EuclideanSpace ℝ (Fin 3)) {ψ ψ' : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψm : MeasureTheory.AEStronglyMeasurable ψ volume)
    (hψ'm : MeasureTheory.AEStronglyMeasurable ψ' volume)
    (hψ : MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z) ^ 2))
    (hψ' : MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) => (ψ' z) ^ 2))
    (hψd : MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z - ψ' z) ^ 2))
    (hRψ : ∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z) ^ 2 ≤ R ^ 2)
    (hRψ' : ∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ' z) ^ 2 ≤ R ^ 2) :
    |Work.BoseKinLoc.neuFrac ℓ a2 u ψ - Work.BoseKinLoc.neuFrac ℓ a2 u ψ'|
      ≤ 6 * R * Real.sqrt (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z - ψ' z) ^ 2) := by
  -- the two ball reductions, one for each state
  have h1 : Work.BoseKinLoc.neuFrac ℓ a2 u ψ
      = sInf (trialBallSet ℓ a2 (2 * R / a2) u ψ) :=
    neuFrac_eq_sInf_trialBall hℓ ha2 hR u hψm hψ hRψ
  have h2 : Work.BoseKinLoc.neuFrac ℓ a2 u ψ'
      = sInf (trialBallSet ℓ a2 (2 * R / a2) u ψ') :=
    neuFrac_eq_sInf_trialBall hℓ ha2 hR u hψ'm hψ' hRψ'
  have hM : 0 ≤ 2 * R / a2 := by positivity
  -- `(ψ' - ψ)²` and `(ψ - ψ')²` have the same integral, so a single `K` serves both directions
  have hsq : (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ' z - ψ z) ^ 2)
      = ∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z - ψ' z) ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    ring
  have hψd' : MeasureTheory.Integrable (fun z : ℝ³ => (ψ' z - ψ z) ^ 2) :=
    hψd.congr (Filter.Eventually.of_forall (fun z => by ring))
  -- direction 1: compare `neuFrac ψ` with every trial of `ψ'` in the ball
  have hdir1 : Work.BoseKinLoc.neuFrac ℓ a2 u ψ
      ≤ sInf (trialBallSet ℓ a2 (2 * R / a2) u ψ')
        + 6 * R * Real.sqrt (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z - ψ' z) ^ 2) := by
    refine le_sInf_add_of_forall_le ⟨_, zero_mem_trialBallSet hM ℓ a2 u ψ'⟩ ?_
    rintro t ⟨g, hg, hgs, hg2, rfl⟩
    have hle : Work.BoseKinLoc.neuFrac ℓ a2 u ψ ≤ trialVal ℓ a2 u ψ g :=
      neuFrac_le_trialVal ha2.le u hψ hg hgs
    have hsub := trialVal_sub_le_of_ball (ℓ := ℓ) (a2 := a2) (R := R) hℓ ha2 hR u
      hψm hψ'm hψ hψ' hψd hRψ hRψ' hg hgs hg2
    linarith
  -- direction 2: compare `neuFrac ψ'` with every trial of `ψ` in the ball
  have hdir2 : Work.BoseKinLoc.neuFrac ℓ a2 u ψ'
      ≤ sInf (trialBallSet ℓ a2 (2 * R / a2) u ψ)
        + 6 * R * Real.sqrt (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z - ψ' z) ^ 2) := by
    refine le_sInf_add_of_forall_le ⟨_, zero_mem_trialBallSet hM ℓ a2 u ψ⟩ ?_
    rintro t ⟨g, hg, hgs, hg2, rfl⟩
    have hle : Work.BoseKinLoc.neuFrac ℓ a2 u ψ' ≤ trialVal ℓ a2 u ψ' g :=
      neuFrac_le_trialVal ha2.le u hψ' hg hgs
    have hsub := trialVal_sub_le_of_ball (ℓ := ℓ) (a2 := a2) (R := R) hℓ ha2 hR u
      hψ'm hψm hψ' hψ hψd' hRψ' hRψ hg hgs hg2
    rw [hsq] at hsub
    linarith
  -- combine
  have hA : Work.BoseKinLoc.neuFrac ℓ a2 u ψ
      ≤ Work.BoseKinLoc.neuFrac ℓ a2 u ψ'
        + 6 * R * Real.sqrt (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z - ψ' z) ^ 2) := by
    rw [← h2] at hdir1
    exact hdir1
  have hB : Work.BoseKinLoc.neuFrac ℓ a2 u ψ'
      ≤ Work.BoseKinLoc.neuFrac ℓ a2 u ψ
        + 6 * R * Real.sqrt (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z - ψ' z) ^ 2) := by
    rw [← h1] at hdir2
    exact hdir2
  rw [abs_sub_le_iff]
  exact ⟨by linarith, by linarith⟩

end Work.BoseKinLoc.Kinetic
