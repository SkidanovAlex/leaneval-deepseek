import ChallengeDeps
import Submission.Work.BoseB1Cube.boxM2SubLeOfPosPart
import Submission.Work.BoseB1Cube.swhMassFactsFixed
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.swhTruncFactsFixed` — the *repaired* `swhTruncFacts`

The frozen node `Work.BoseB1Cube.swhTruncFacts`
(`Submission/Work/BoseB1Cube/swhTruncFacts.lean`) is **false as written**: it is missing the
hypothesis that `v` (equivalently its truncation `min (v ·) K`) be a.e. strongly measurable —
`MeasureTheory.MemLp v 1`, as in the corpus's convention (4797 occurrences), or the minimal
`AEMeasurable v`.

## Why the frozen statement is false

`Work.UBB.ScatSol v` is `∃ w, IsRadial w ∧ IsScatteringSolution w v`, and
`IsScatteringSolution` mentions `v` only through the *product* `v·(1−w)`:
`LocallyIntegrable (v·(1−w))` and the integrand `v(1−w)φ` of the weak equation
`-∫ w Δφ = ½ ∫ v (1−w) φ` (`ChallengeDeps.lean`).  Consequently `v` is **completely free on the
level set `{w = 1}`**, which can have positive measure.  The corpus records this family
explicitly in `Submission/Work/BoseFixB1/chemPair_eq_qLHSword.lean` (and
`Submission/Work/BoseFixB1S/boxFibPairPSum_eq.lean:44`): a radial `w₀ ∈ C_c^∞` with `w₀ ≡ 1` on
`B(0,1)`, `0 ≤ w₀ ≤ 1`, together with `v := -2Δw₀/(1-w₀)` on the annulus (so that
`v(1−w₀) = -2Δw₀` is a nice `L¹_loc` function, making the weak equation true), `v` arbitrary
radial nonnegative on `B(0,1)`, and `tsupport v ⊆ ball 0 3`, `ScatSol v`, `a v > 0`.  Replacing
`v` on `B(0,1)` by a radial **non-measurable** nonnegative function (a radial set
`{‖x‖ ∈ A}` with `A` non-measurable) keeps every hypothesis of the node — `0 ≤ v`,
`IsRadial v`, `tsupport v ⊆ ball 0 R`, `ScatSol v`, `0 < a v` — while `min (v ·) K` is
non-`AEMeasurable` for every `K > 0`.

In that situation Lean's Bochner integral of the localised kernel
`wSmallPair M ℓ d u (min (v ·) K)` is the *junk value* `0` (`MeasureTheory.integral_undef`,
`MeasureTheory.integral_non_aestronglyMeasurable`: the integral of a non-`AEStronglyMeasurable`
function is `0`), so the third conjunct of the node degenerates to

    boxM2 (wSmallPair (g0 v h))  ≤  2·(smallConvLower M)⁻¹·chiMass·∫(g0 − K)₊ ,

which **fails** for small `ηs`: the left side is `∫∫_{B(u)²} χ_B(x)·(g0(x−y)/D(x−y))·χ_B(y)`,
and since `D = (χ_M⋆χ_M)(·/(ℓd))·(χ⋆χ)(·/ℓ) ≤ 1` on `supp g0` (`wSmall1Pair_denom_bounds`), it
dominates `c·chiMass·∫g0 = c·chiMass·8π·(a v)` for a constant `c > 0` independent of `ηs`, while
the right side is at most `2·(smallConvLower M)⁻¹·chiMass·ηs·(a v)`: for
`ηs < 4π·smallConvLower M·c` **no** `K` is admissible.  (The sibling node `swhMassFacts` has
exactly the same defect and was repaired in the same way — see
`Submission/Work/BoseB1Cube/swhMassFactsFixed.lean`.)

## The repair

`swhTruncFacts_of_meas` proves the whole node from the *minimal* missing datum

    hmeas : ∀ K : ℝ, AEMeasurable (fun z => min (v z) K) ,

and the two natural repairs are then one-liners: `swhTruncFactsFixed` (from `MemLp v 1`, the
corpus convention, matching `swhMassFactsFixed`) and `swhTruncFactsFixedMeas` (from
`AEMeasurable v`).  Nothing else is changed or weakened.

## The three conjuncts

* **clause 1** (the truncation tail `∫(g₀ − K)₊ ≤ ηs·(a v)`): `truncTail_exists` — dominated
  convergence along `K = n` for the integrable `g₀` (`g0_integrable`, `g0_nonneg_ae`).
* **clause 2** (pointwise domination of the truncated kernel):
  `min (v ·) K` is supported in `ball 0 R` (`tsupport_min_subset`) and bounded by `K`, so the
  general-numerator bound `abs_wSmallPair_le_of_supported` applies.
* **clause 3** (the `boxM2` comparison): the delegated
  `Work.BoseB1Cube.boxM2SubLeOfPosPart`; its content is the pointwise inequality
  `g0 − min(v,K) ≤ (g0 − K)₊` (from `g0 ≤ v` a.e., `scattering_bounds_ae`), the support/regime
  bound `1/D ≤ 2/smallConvLower M`, and the `χ⊗χ` pairing lemma
  `pairing_le_chiSq_mul_abs_integral`.
-/

noncomputable section

open MeasureTheory Metric
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.SmallBoxSliding Work.BoseFixB1S

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The whole node from the measurability of every truncation.**  This is the target statement
of `swhTruncFacts` with the single missing datum `hmeas` supplied; every other hypothesis is the
node's own. -/
theorem swhTruncFacts_of_meas {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v) (ηs : ℝ) (hη : 0 < ηs)
    (hmeas : ∀ K : ℝ, AEMeasurable (fun z : E3 => min (v z) K) MeasureTheory.volume) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∫ z : E3, max (Submission.BoseGases.g0 v h z - K) 0 ≤ ηs * _root_.BoseGases.a v) ∧
      (∀ {M : ℕ}, 1 ≤ M → ∀ {ℓ d : ℝ}, 0 < ℓ → 0 < d → R ≤ ℓ * d / 16 →
        R ≤ ℓ * Submission.BoseGases.chiR0 → ∀ u : E3,
        (∀ x y : E3,
          |Submission.BoseGases.wSmallPair M ℓ d u (fun z => min (v z) K) x y|
            ≤ 2 * K * (Work.SmallBoxSliding.smallConvLower M)⁻¹ *
              (Submission.BoseGases.chiSmallB M ℓ d u x * Submission.BoseGases.chiSmallB M ℓ d u y)) ∧
        (Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h))
          - Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmallPair M ℓ d u (fun z => min (v z) K))
          ≤ 2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ * Work.SmallBoxSliding.chiMass M ℓ d u
              * (∫ z : E3, max (Submission.BoseGases.g0 v h z - K) 0))) := by
  -- ## clause 1: the truncation level
  have hg0int : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR hv_supp h
  have hg0nn : 0 ≤ᵐ[(MeasureTheory.volume : Measure E3)] Submission.BoseGases.g0 v h :=
    Submission.BoseGases.g0_nonneg_ae hR hv hvrad hv_supp h
  obtain ⟨K, hK0, hKint⟩ :=
    truncTail_exists hg0int hg0nn (mul_pos hη hav)
  refine ⟨K, hK0, hKint, ?_⟩
  intro M hM ℓ d hℓ hd hRd hRχ u
  refine ⟨?_, ?_⟩
  · -- ## clause 2: pointwise domination of the truncated kernel
    have htrunc_supp : tsupport (fun z : E3 => min (v z) K) ⊆ Metric.ball (0 : E3) R :=
      tsupport_min_subset hv hK0 hv_supp
    have hfsupp : ∀ z : E3, R ≤ ‖z‖ → min (v z) K = 0 := by
      intro z hz
      by_contra hne
      exact absurd (htrunc_supp (subset_closure (Function.mem_support.mpr hne)))
        (by rw [Metric.mem_ball, dist_zero_right]; exact not_lt.mpr hz)
    have hfb : ∀ z : E3, |min (v z) K| ≤ K := by
      intro z
      have h0 : 0 ≤ min (v z) K := le_min (hv z) hK0
      rw [abs_le]
      exact ⟨le_trans (neg_nonpos.mpr hK0) h0, min_le_right _ _⟩
    exact abs_wSmallPair_le_of_supported hfsupp hfb hM hℓ hd hRd hRχ u
  · -- ## clause 3: the `boxM2` comparison, via the delegated estimate
    exact boxM2SubLeOfPosPart h hv hvrad hR hK0 hv_supp (hmeas K) hM hℓ hd hRd hRχ u

/-- **`swhTruncFacts` with the missing hypothesis `MemLp v 1` restored** (the corpus's
convention, and the same repair as the sibling node `swhMassFactsFixed`).  Without it the
statement is false (see the module docstring). -/
theorem swhTruncFactsFixed {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v) (ηs : ℝ) (hη : 0 < ηs) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∫ z : E3, max (Submission.BoseGases.g0 v h z - K) 0 ≤ ηs * _root_.BoseGases.a v) ∧
      (∀ {M : ℕ}, 1 ≤ M → ∀ {ℓ d : ℝ}, 0 < ℓ → 0 < d → R ≤ ℓ * d / 16 →
        R ≤ ℓ * Submission.BoseGases.chiR0 → ∀ u : E3,
        (∀ x y : E3,
          |Submission.BoseGases.wSmallPair M ℓ d u (fun z => min (v z) K) x y|
            ≤ 2 * K * (Work.SmallBoxSliding.smallConvLower M)⁻¹ *
              (Submission.BoseGases.chiSmallB M ℓ d u x * Submission.BoseGases.chiSmallB M ℓ d u y)) ∧
        (Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h))
          - Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmallPair M ℓ d u (fun z => min (v z) K))
          ≤ 2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ * Work.SmallBoxSliding.chiMass M ℓ d u
              * (∫ z : E3, max (Submission.BoseGases.g0 v h z - K) 0))) :=
  swhTruncFacts_of_meas h hv hvrad hR hv_supp hav ηs hη
    (fun K => hv1.aemeasurable.min aemeasurable_const)

/-- **The minimal repair**: the node from `AEMeasurable v` alone. -/
theorem swhTruncFactsFixedMeas {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hva : AEMeasurable v MeasureTheory.volume) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v) (ηs : ℝ) (hη : 0 < ηs) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∫ z : E3, max (Submission.BoseGases.g0 v h z - K) 0 ≤ ηs * _root_.BoseGases.a v) ∧
      (∀ {M : ℕ}, 1 ≤ M → ∀ {ℓ d : ℝ}, 0 < ℓ → 0 < d → R ≤ ℓ * d / 16 →
        R ≤ ℓ * Submission.BoseGases.chiR0 → ∀ u : E3,
        (∀ x y : E3,
          |Submission.BoseGases.wSmallPair M ℓ d u (fun z => min (v z) K) x y|
            ≤ 2 * K * (Work.SmallBoxSliding.smallConvLower M)⁻¹ *
              (Submission.BoseGases.chiSmallB M ℓ d u x * Submission.BoseGases.chiSmallB M ℓ d u y)) ∧
        (Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h))
          - Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmallPair M ℓ d u (fun z => min (v z) K))
          ≤ 2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ * Work.SmallBoxSliding.chiMass M ℓ d u
              * (∫ z : E3, max (Submission.BoseGases.g0 v h z - K) 0))) :=
  swhTruncFacts_of_meas h hv hvrad hR hv_supp hav ηs hη
    (fun K => hva.min aemeasurable_const)

end Work.BoseB1Cube
