import Submission.CutStep2
import Submission.LensSync

/-!
# The cut-point step with local injectivity only on the *sphere* of radius `inj(p)`

`Submission.CutStep2.exists_two_minimising_of_not_injAtLeast` derives the two minimising vectors of
norm `m = inj(p)` from `InjAtLeast hmet p m` and the failure of `InjAtLeast` beyond `m`, assuming
that `GExp p` is **locally injective at every point of the closed ball** of radius `m`.

That hypothesis is stronger than necessary.  The only place where it is used is the exclusion of the
*degenerate* case of the witness sequence, i.e. the case in which the two limits `u`, `v` coincide —
and in that case the common limit automatically has norm exactly `m`:

> if `Uₙ, Vₙ → u` with `Uₙ ≠ Vₙ`, `GExp p Uₙ = GExp p Vₙ` and `max ‖Uₙ‖ ‖Vₙ‖ ≤ m + 1/(n+1)`, and if
> both `Uₙ` and `Vₙ` were inside the **open** ball of radius `m` then `InjAtLeast` would force
> `Uₙ = Vₙ`; hence one of the two norms is `≥ m`, so `m ≤ max ‖Uₙ‖ ‖Vₙ‖ → ‖u‖` and
> `‖u‖ ≤ max ‖Uₙ‖ ‖Vₙ‖ → m` give `‖u‖ = m`.

This matters because local injectivity at the *interior* points `‖w‖ < m` is **false** in general:
a non-minimising vector `v` with `GExp p v = GExp p w` and `‖v‖ > m` makes `GExp p` non-injective
near `w`.  The genuine content of the hypothesis is therefore exactly the classical
*"the exponential map is a local diffeomorphism at non-conjugate vectors"* at the cut locus, and
this file isolates it there.

## Contents

* `norm_eq_of_degenerate_limit`: a degenerate witness sequence meets the sphere `‖·‖ = m`;
* `exists_two_minimising_of_hloc_sphere`: the cut-point step with the hypothesis restricted to
  `‖w‖ = m`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.HopfRinow
open Submission.InjRadius
open Submission.CutWitness
open Submission.CutPoint
open Submission.CutStep2
open Submission.GExpBoundary

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.CutStep3

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **A degenerate witness sequence meets the sphere `‖·‖ = m`.**  Let `Uₙ ≠ Vₙ` be witness pairs
with `max ‖Uₙ‖ ‖Vₙ‖ < m + 1/(n+1)`, converging to the *same* limit `u` with `‖u‖ ≤ m`.  Then
`‖u‖ = m`.

Indeed, if both `‖Uₙ‖ < m` and `‖Vₙ‖ < m` then injectivity of `GExp p` on the ball of radius `m`
would force `Uₙ = Vₙ`; hence `m ≤ max ‖Uₙ‖ ‖Vₙ‖` for every `n`, and the two bounds
`m ≤ max ‖Uₙ‖ ‖Vₙ‖` and `max ‖Uₙ‖ ‖Vₙ‖ < m + 1/(n+1)` give `max ‖Uₙ‖ ‖Vₙ‖ → m`. -/
theorem norm_eq_of_degenerate_limit (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {p : M} {m : ℝ} (hinj : InjAtLeast hmet p m)
    {U V : ℕ → TangentSpace I p} {u : TangentSpace I p}
    (hUV : ∀ n, U n ≠ V n)
    (hG : ∀ n, GExp (cov := cov) hmet p (U n) = GExp (cov := cov) hmet p (V n))
    (hb : ∀ n, max ‖U n‖ ‖V n‖ < m + 1 / ((n : ℝ) + 1))
    (hU : Tendsto U atTop (𝓝 u)) (hV : Tendsto V atTop (𝓝 u)) :
    ‖u‖ = m := by
  have hge : ∀ n, m ≤ max ‖U n‖ ‖V n‖ := by
    intro n
    by_contra hcon
    rw [not_le] at hcon
    have h1 : ‖U n‖ < m := lt_of_le_of_lt (le_max_left _ _) hcon
    have h2 : ‖V n‖ < m := lt_of_le_of_lt (le_max_right _ _) hcon
    exact hUV n (hinj (U n) (V n) h1 h2 (hG n))
  have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hlim : Tendsto (fun n : ℕ => m + 1 / ((n : ℝ) + 1)) atTop (𝓝 m) := by
    simpa using (tendsto_const_nhds (x := m)).add h0
  have hmax : Tendsto (fun n : ℕ => max ‖U n‖ ‖V n‖) atTop (𝓝 ‖u‖) := by
    have h := hU.norm.max hV.norm
    simpa using h
  have hub : ‖u‖ ≤ m := le_of_tendsto_of_tendsto' hmax hlim (fun n => (hb n).le)
  have hlb : m ≤ ‖u‖ := le_of_tendsto_of_tendsto' tendsto_const_nhds hmax hge
  exact le_antisymm hub hlb

/-- **The cut-point step, with local injectivity only on the sphere.**  Let `m` be the injectivity
radius at `p` (`InjAtLeast hmet p m`, and no larger radius), and assume that `GExp p` is *locally
injective* at every vector of norm exactly `m`.  Then there are two **distinct minimising vectors of
length `m`** with the same image.

This sharpens `CutStep2.exists_two_minimising_of_not_injAtLeast`, whose hypothesis is local
injectivity on the whole closed ball — a hypothesis that is *false* at interior points in general
(see the file docstring). -/
theorem exists_two_minimising_of_hloc_sphere
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {p : M} {m : ℝ} (hinj : InjAtLeast hmet p m)
    (hfail : ∀ r : ℝ, m < r → ¬ InjAtLeast hmet p r)
    (hloc : ∀ w : TangentSpace I p, ‖w‖ = m → LocallyInjectiveAtGExp (I := I) hmet p w) :
    ∃ u v : TangentSpace I p, u ≠ v ∧
      GExp (cov := cov) hmet p u = GExp (cov := cov) hmet p v ∧
      ‖u‖ = m ∧ ‖v‖ = m ∧
      Manifold.riemannianEDist I p (GExp (cov := cov) hmet p u) = ENNReal.ofReal m := by
  classical
  have hex : ∀ r : ℝ, m < r → ∃ u v : TangentSpace I p, u ≠ v ∧
      GExp (cov := cov) hmet p u = GExp (cov := cov) hmet p v ∧ ‖u‖ < r ∧ ‖v‖ < r := by
    intro r hr
    by_contra hcon
    push Not at hcon
    refine hfail r hr (fun u v hu hv hG => ?_)
    by_contra huv
    exact absurd hv (not_lt.mpr (hcon u v huv hG hu))
  obtain ⟨U, V, u, v, hUV, hGU, hbU, hbV, hUtend, hVtend, hu, hv⟩ :=
    exists_tendsto_witness_sequence (cov := cov) hmet hex
  have hFu : Tendsto (fun n : ℕ => GExp (cov := cov) hmet p (U n)) atTop
      (𝓝 (GExp (cov := cov) hmet p u)) :=
    tendsto_GExp_of_tendsto_of_norm_le (cov := cov) hmet htor hinj hUtend hu
  have hFv : Tendsto (fun n : ℕ => GExp (cov := cov) hmet p (V n)) atTop
      (𝓝 (GExp (cov := cov) hmet p v)) :=
    tendsto_GExp_of_tendsto_of_norm_le (cov := cov) hmet htor hinj hVtend hv
  have hGuv : GExp (cov := cov) hmet p u = GExp (cov := cov) hmet p v :=
    tendsto_nhds_unique hFu
      (hFv.congr' (Eventually.of_forall fun n => (hGU n).symm))
  have huv : u ≠ v := by
    intro huv'
    -- the degenerate case: the common limit has norm exactly `m`
    have hb : ∀ n : ℕ, max ‖U n‖ ‖V n‖ < m + 1 / ((n : ℝ) + 1) := fun n =>
      max_lt (hbU n) (hbV n)
    have hun : ‖u‖ = m :=
      norm_eq_of_degenerate_limit (cov := cov) hmet htor hinj hUV hGU hb hUtend
        (by rw [huv']; exact hVtend)
    obtain ⟨s, hs, hinj_s⟩ := hloc u hun
    have h1 : ∀ᶠ n : ℕ in atTop, U n ∈ s := hUtend.eventually hs
    have hs' : s ∈ 𝓝 v := by rw [← huv']; exact hs
    have h2 : ∀ᶠ n : ℕ in atTop, V n ∈ s := hVtend.eventually hs'
    obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
    exact hUV n (hinj_s (U n) hn1 (V n) hn2 (hGU n))
  obtain ⟨h1, h2, h3, -⟩ :=
    norm_eq_and_minimising_of_witness_pair (cov := cov) hmet htor hinj huv hGuv hu hv
  exact ⟨u, v, huv, hGuv, h1, h2, h3⟩

/-- **The cut-point dichotomy.**  Let `m` be the injectivity radius at `p` (`InjAtLeast hmet p m`)
and suppose that it fails for every larger radius.  Then **either** there are two distinct
minimising vectors of length `m` with the same image — the conclusion of the cut-point step —
**or** `GExp p` fails to be locally injective at some vector of norm exactly `m`.

The second alternative is the *tangential merging* phenomenon: a sequence `Uₙ ≠ Vₙ → w` with
`GExp p Uₙ = GExp p Vₙ`.  Classically it says that `w` is a *conjugate vector* of `p`, whence
`m ≥ π/√K` by Rauch's theorem (in the project normalisation: `m ≥ π/2`); so the dichotomy separates
exactly the two classical branches of Klingenberg's lemma (a closed geodesic loop, or a conjugate
point).

This removes the hypothesis `hloc` of `exists_two_minimising_of_hloc_sphere` at the cost of naming
the two outcomes. -/
theorem exists_two_minimising_or_not_locallyInjective
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {p : M} {m : ℝ} (hinj : InjAtLeast hmet p m)
    (hfail : ∀ r : ℝ, m < r → ¬ InjAtLeast hmet p r) :
    (∃ u v : TangentSpace I p, u ≠ v ∧
        GExp (cov := cov) hmet p u = GExp (cov := cov) hmet p v ∧
        ‖u‖ = m ∧ ‖v‖ = m ∧
        Manifold.riemannianEDist I p (GExp (cov := cov) hmet p u) = ENNReal.ofReal m)
      ∨ (∃ w : TangentSpace I p, ‖w‖ = m ∧
        ¬ LocallyInjectiveAtGExp (I := I) hmet p w) := by
  classical
  have hex : ∀ r : ℝ, m < r → ∃ u v : TangentSpace I p, u ≠ v ∧
      GExp (cov := cov) hmet p u = GExp (cov := cov) hmet p v ∧ ‖u‖ < r ∧ ‖v‖ < r := by
    intro r hr
    by_contra hcon
    push Not at hcon
    refine hfail r hr (fun u v hu hv hG => ?_)
    by_contra huv
    exact absurd hv (not_lt.mpr (hcon u v huv hG hu))
  obtain ⟨U, V, u, v, hUV, hGU, hbU, hbV, hUtend, hVtend, hu, hv⟩ :=
    exists_tendsto_witness_sequence (cov := cov) hmet hex
  have hFu : Tendsto (fun n : ℕ => GExp (cov := cov) hmet p (U n)) atTop
      (𝓝 (GExp (cov := cov) hmet p u)) :=
    tendsto_GExp_of_tendsto_of_norm_le (cov := cov) hmet htor hinj hUtend hu
  have hFv : Tendsto (fun n : ℕ => GExp (cov := cov) hmet p (V n)) atTop
      (𝓝 (GExp (cov := cov) hmet p v)) :=
    tendsto_GExp_of_tendsto_of_norm_le (cov := cov) hmet htor hinj hVtend hv
  have hGuv : GExp (cov := cov) hmet p u = GExp (cov := cov) hmet p v :=
    tendsto_nhds_unique hFu
      (hFv.congr' (Eventually.of_forall fun n => (hGU n).symm))
  by_cases huv : u = v
  · -- the degenerate (merging) case: `GExp p` is not locally injective at `u`
    right
    have hb : ∀ n : ℕ, max ‖U n‖ ‖V n‖ < m + 1 / ((n : ℝ) + 1) := fun n =>
      max_lt (hbU n) (hbV n)
    have hun : ‖u‖ = m :=
      norm_eq_of_degenerate_limit (cov := cov) hmet htor hinj hUV hGU hb hUtend
        (by rw [huv]; exact hVtend)
    refine ⟨u, hun, fun hloc => ?_⟩
    obtain ⟨s, hs, hinj_s⟩ := hloc
    have h1 : ∀ᶠ n : ℕ in atTop, U n ∈ s := hUtend.eventually hs
    have hs' : s ∈ 𝓝 v := by rw [← huv]; exact hs
    have h2 : ∀ᶠ n : ℕ in atTop, V n ∈ s := hVtend.eventually hs'
    obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
    exact hUV n (hinj_s (U n) hn1 (V n) hn2 (hGU n))
  · left
    obtain ⟨h1, h2, h3, -⟩ :=
      norm_eq_and_minimising_of_witness_pair (cov := cov) hmet htor hinj huv hGuv hu hv
    exact ⟨u, v, huv, hGuv, h1, h2, h3⟩

end

end Submission.CutStep3
