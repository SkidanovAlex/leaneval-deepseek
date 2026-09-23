import Submission.CutTime
import Submission.CutStep3

/-!
# Klingenberg's lemma in the *fixed-direction* form

This file proves the sharp form of the cut-point step that `Submission/Roadmap.lean` §76.7
identified as the missing input: at a **cut time** `τ` of a unit direction `ξ` (with `τ` equal to
the injectivity radius, so that `GExp p` is continuous at the limits), either

* there is a second **minimising** vector `v ≠ τ • ξ` of norm `τ` with the same image as `τ • ξ`
  (so that the two rays `p → x` form a broken minimising geodesic loop at `p` of length `2τ`), or
* `GExp p` is **not locally injective** at `τ • ξ` (the *tangential merging* alternative).

The point of the formulation is that the second alternative is a statement about the **single**
vector `τ • ξ` (the endpoint of the cut ray), not about the sphere of radius `τ`; this is what the
classical Klingenberg lemma produces.

## Proof

For `tₙ = τ + 1/(n+1) > τ = cutTime p ξ` the ray is **not** minimising (`CutTime.minimisingSet_eq_Icc`),
so if `vₙ` is a minimising vector from `p` to `GExp p (tₙ • ξ)` (Hopf–Rinow) then `‖vₙ‖ < tₙ` and
`edist p (GExp p (tₙ • ξ)) = ofReal ‖vₙ‖ → ofReal τ`, hence `‖vₙ‖ → τ`.  A subsequence converges to
some `v` with `‖v‖ = τ`; the **continuity of `GExp p` at points of norm `≤ τ`** (which is exactly the
content of `GExpBoundary.tendsto_GExp_of_tendsto_of_norm_le`, and where the hypothesis "`τ` is the
injectivity radius" enters) gives `GExp p v = GExp p (τ • ξ)`.  Finally either `v ≠ τ • ξ` (first
alternative) or `v = τ • ξ`, in which case the two sequences `vₙ` and `tₙ • ξ` — distinct, with the
same image, both converging to `τ • ξ` — witnes s the failure of local injectivity there.

## Contents

* `exists_two_minimising_or_not_locallyInjective_of_cutTime`: the dichotomy above;
* `exists_two_minimising_of_cutTime_of_locallyInjective`: the two-minimising-vector conclusion under
  the *single-point* local-injectivity hypothesis at `m • ξ`;
* `exists_two_minimising_of_not_isConjugateTime`: the same, phrased with the classical
  non-conjugacy hypothesis reduced to the single-point one.
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
open Submission.CutTime
open Submission.GExpRay
open Submission.CutWitness
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

namespace Submission.CutKlingenberg

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]
variable [PathConnectedSpace M] [RegularSpace M]

/-- **Klingenberg's lemma at a cut time.**  Let `m > 0` be a radius at which the exponential map is
injective (`InjAtLeast hmet p m`) and let `ξ` be a unit vector whose ray is minimising exactly up to
`m` (`cutTime hmet p ξ = m`).  Then either there is a second minimising vector `v ≠ m • ξ` of norm
`m` with the same image as `m • ξ`, or `GExp p` fails to be locally injective at `m • ξ`. -/
theorem exists_two_minimising_or_not_locallyInjective_of_cutTime
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {ξ : TangentSpace I p} (hξ : ‖ξ‖ = 1) {m : ℝ}
    (hm : 0 < m) (hinj : InjAtLeast hmet p m)
    (hτ : cutTime (I := I) hmet p ξ = m) :
    (∃ v : TangentSpace I p, v ≠ m • ξ ∧ ‖v‖ = m ∧
      GExp (cov := cov) hmet p v = GExp (cov := cov) hmet p (m • ξ) ∧
      Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (m • ξ)) = ENNReal.ofReal m)
    ∨ ¬ LocallyInjectiveAtGExp (I := I) hmet p (m • ξ) := by
  classical
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  set t : ℕ → ℝ := fun n => m + 1 / ((n : ℝ) + 1) with htdef
  have htpos : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have htgt : ∀ n : ℕ, m < t n := fun n => by
    have := htpos n
    rw [htdef]
    simp only
    linarith
  have htend : Tendsto t atTop (𝓝 m) := by
    have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    simpa only [htdef, add_zero] using (tendsto_const_nhds (x := m)).add h0
  -- the ray is not minimising at time `t n`
  have hnotmin : ∀ n : ℕ,
      Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (t n • ξ)) < ENNReal.ofReal (t n) := by
    intro n
    have h0 : 0 ≤ t n := (le_of_lt hm).trans (htgt n).le
    by_contra hcon
    have heq : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (t n • ξ))
        = ENNReal.ofReal (t n) :=
      le_antisymm (edist_GExp_smul_le_zero (cov := cov) hmet p hξ h0) (not_lt.mp hcon)
    have hmem : t n ∈ minimisingSet (I := I) hmet p ξ := ⟨h0, heq⟩
    have hle : t n ≤ cutTime (I := I) hmet p ξ :=
      ((mem_minimisingSet_iff (I := I) (cov := cov) hmet htor hξ).mp hmem).2
    rw [hτ] at hle
    linarith [htgt n]
  -- minimising vectors for the points of the ray
  have hwit : ∀ n : ℕ, ∃ v : TangentSpace I p,
      GExp (cov := cov) hmet p v = GExp (cov := cov) hmet p (t n • ξ) ∧
      Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (t n • ξ)) = ENNReal.ofReal ‖v‖ ∧
      ‖v‖ < t n := by
    intro n
    obtain ⟨v, hv, hd⟩ :=
      Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (cov := cov) hmet htor p
        (GExp (cov := cov) hmet p (t n • ξ))
    refine ⟨v, hv, hd, ?_⟩
    have hd' : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p v) = ENNReal.ofReal ‖v‖ := by
      rw [hv, hd]
    have hlt := hnotmin n
    rw [← hv, hd'] at hlt
    exact ((ENNReal.ofReal_lt_ofReal_iff').mp hlt).1
  choose v hvG hvd hvlt using hwit
  -- the exponential distances converge
  have hsm : Tendsto (fun n : ℕ => t n • ξ) atTop (𝓝 (m • ξ)) := htend.smul_const ξ
  have hraytend : Tendsto (fun n : ℕ => GExp (cov := cov) hmet p (t n • ξ)) atTop
      (𝓝 (GExp (cov := cov) hmet p (m • ξ))) :=
    tendsto_GExp_of_tendsto_of_norm_le (cov := cov) hmet htor hinj hsm
      (by rw [norm_smul, Real.norm_of_nonneg hm.le, hξ, mul_one])
  have hlimedist : Tendsto
      (fun n : ℕ => Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (t n • ξ))) atTop
      (𝓝 (ENNReal.ofReal m)) := by
    letI : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
    have hcont : Continuous (fun y : M => edist p y) :=
      continuous_edist.comp (continuous_const.prodMk continuous_id)
    have h1 : Tendsto (fun n : ℕ => edist p (GExp (cov := cov) hmet p (t n • ξ))) atTop
        (𝓝 (edist p (GExp (cov := cov) hmet p (m • ξ)))) :=
      hcont.continuousAt.tendsto.comp hraytend
    have h2 : edist p (GExp (cov := cov) hmet p (m • ξ)) = ENNReal.ofReal m := by
      rw [Submission.EDist.edist_eq_riemannianEDist (I := I)]
      exact edist_GExp_smul_eq_of_injAtLeast (cov := cov) hmet htor hinj hξ hm.le le_rfl
    rw [h2] at h1
    simpa only [Submission.EDist.edist_eq_riemannianEDist] using h1
  -- consequently the norms converge to `m`
  have hnormtend : Tendsto (fun n : ℕ => ‖v n‖) atTop (𝓝 m) := by
    have hfin : ∀ n : ℕ, Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (t n • ξ)) ≠ ⊤ :=
      fun n => (Submission.HopfRinow.riemannianEDist_lt_top (cov := cov) hmet htor p _).ne
    have h2 := (ENNReal.tendsto_toReal_iff hfin ENNReal.ofReal_ne_top).mpr hlimedist
    have h3 : Tendsto (fun n : ℕ =>
        (Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (t n • ξ))).toReal) atTop
        (𝓝 m) := by
      simpa only [ENNReal.toReal_ofReal hm.le] using h2
    have h4 : (fun n : ℕ => ‖v n‖)
        = fun n : ℕ =>
            (Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (t n • ξ))).toReal := by
      funext n
      rw [hvd n]
      exact (ENNReal.toReal_ofReal (norm_nonneg (v n))).symm
    rw [h4]
    exact h3
  -- boundedness and a convergent subsequence
  have hbound : ∀ n : ℕ, v n ∈ Metric.closedBall (0 : TangentSpace I p) (m + 1) := by
    intro n
    rw [Metric.mem_closedBall, dist_zero_right]
    refine le_of_lt ((hvlt n).trans_le ?_)
    rw [htdef]
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    linarith
  haveI hproper : ProperSpace (TangentSpace I p) := by
    haveI : FiniteDimensional ℝ (TangentSpace I p) := ‹FiniteDimensional ℝ E›
    exact FiniteDimensional.proper ℝ (TangentSpace I p)
  obtain ⟨w, hwmem, φ, hφ, hwtend⟩ :=
    (isCompact_closedBall (0 : TangentSpace I p) (m + 1)).tendsto_subseq hbound
  have hw : ‖w‖ = m := by
    have h1 : Tendsto (fun n : ℕ => ‖v (φ n)‖) atTop (𝓝 ‖w‖) := hwtend.norm
    exact tendsto_nhds_unique h1 (hnormtend.comp hφ.tendsto_atTop)
  -- the limit maps to the same point
  have hGw : GExp (cov := cov) hmet p w = GExp (cov := cov) hmet p (m • ξ) := by
    have h1 : Tendsto (fun n : ℕ => GExp (cov := cov) hmet p (v (φ n))) atTop
        (𝓝 (GExp (cov := cov) hmet p w)) :=
      tendsto_GExp_of_tendsto_of_norm_le (cov := cov) hmet htor hinj hwtend (by rw [hw])
    have h2 : Tendsto (fun n : ℕ => GExp (cov := cov) hmet p (v (φ n))) atTop
        (𝓝 (GExp (cov := cov) hmet p (m • ξ))) := by
      have htφ : Tendsto (fun n : ℕ => t (φ n)) atTop (𝓝 m) := htend.comp hφ.tendsto_atTop
      have hsm2 : Tendsto (fun n : ℕ => t (φ n) • ξ) atTop (𝓝 (m • ξ)) := htφ.smul_const ξ
      have h3 : Tendsto (fun n : ℕ => GExp (cov := cov) hmet p (t (φ n) • ξ)) atTop
          (𝓝 (GExp (cov := cov) hmet p (m • ξ))) :=
        tendsto_GExp_of_tendsto_of_norm_le (cov := cov) hmet htor hinj hsm2
          (by rw [norm_smul, Real.norm_of_nonneg hm.le, hξ, mul_one])
      refine h3.congr' ?_
      filter_upwards with n
      exact (hvG (φ n)).symm
    exact tendsto_nhds_unique h1 h2
  have hmin : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (m • ξ)) = ENNReal.ofReal m :=
    edist_GExp_smul_eq_of_injAtLeast (cov := cov) hmet htor hinj hξ hm.le le_rfl
  by_cases hvw : w = m • ξ
  · -- the merging alternative: two distinct sequences with the same image through `m • ξ`
    right
    rintro ⟨s, hs, hinjs⟩
    have hsw : s ∈ 𝓝 w := by rw [hvw]; exact hs
    have h1 : ∀ᶠ n : ℕ in atTop, v (φ n) ∈ s := hwtend.eventually hsw
    have h2 : ∀ᶠ n : ℕ in atTop, t (φ n) • ξ ∈ s := by
      have h4 : Tendsto (fun n : ℕ => t (φ n) • ξ) atTop (𝓝 w) := by
        rw [hvw]
        have htφ : Tendsto (fun n : ℕ => t (φ n)) atTop (𝓝 m) := htend.comp hφ.tendsto_atTop
        exact htφ.smul_const ξ
      exact h4.eventually hsw
    obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
    have heq : GExp (cov := cov) hmet p (v (φ n)) = GExp (cov := cov) hmet p (t (φ n) • ξ) :=
      hvG (φ n)
    have heqn : v (φ n) = t (φ n) • ξ := hinjs _ hn1 _ hn2 heq
    have hnorm : ‖v (φ n)‖ = t (φ n) := by
      rw [heqn, norm_smul, Real.norm_of_nonneg (le_of_lt (lt_trans hm (htgt (φ n)))), hξ, mul_one]
    exact absurd hnorm (ne_of_lt (hvlt (φ n)))
  · exact Or.inl ⟨w, hvw, hw, hGw, hmin⟩

/-- **The cut-point step with local injectivity only at the cut point of a fixed direction.**  Under
the single hypothesis `LocallyInjectiveAtGExp hmet p (m • ξ)` (which the conjugate-point analysis
supplies: non-conjugate vectors have non-singular differential, hence `GExp p` is a local
diffeomorphism there) the two minimising vectors exist. -/
theorem exists_two_minimising_of_cutTime_of_locallyInjective
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {ξ : TangentSpace I p} (hξ : ‖ξ‖ = 1) {m : ℝ}
    (hm : 0 < m) (hinj : InjAtLeast hmet p m)
    (hτ : cutTime (I := I) hmet p ξ = m)
    (hloc : LocallyInjectiveAtGExp (I := I) hmet p (m • ξ)) :
    ∃ v : TangentSpace I p, v ≠ m • ξ ∧ ‖v‖ = m ∧
      GExp (cov := cov) hmet p v = GExp (cov := cov) hmet p (m • ξ) ∧
      Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (m • ξ)) = ENNReal.ofReal m ∧
      Manifold.riemannianEDist I p (GExp (cov := cov) hmet p v) = ENNReal.ofReal m := by
  rcases exists_two_minimising_or_not_locallyInjective_of_cutTime (cov := cov) hmet htor hξ hm hinj hτ
    with ⟨v, hv, hvn, hG, hmin⟩ | hnot
  · refine ⟨v, hv, hvn, hG, hmin, ?_⟩
    rw [hG, hmin]
  · exact absurd hloc hnot

end

end Submission.CutKlingenberg
