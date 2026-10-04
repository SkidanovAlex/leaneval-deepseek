import Mathlib
import Submission.Work.OddBound.LiftKit
import Submission.Work.OddBound.longHomotopy.clopen_step

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.OddBound.longHomotopy

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open LeanEval.Geometry.SphereTheorem Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length Submission.InjRadius

/-- **The one-parameter open-and-closed step.**  Two continuous lifts `w₁`, `w₂` of the same curve
under the exponential map `GExp p`, whose values all lie in the open ball of radius `π/√K`, which
agree at the *end* `t = 1` of the interval, agree at the *start* `t = 0` as well.

Below the conjugate radius `π/√K` (which is where the hypotheses place the values, by `hb₁`/`hb₂`,
using `sec ≤ K` and `0 < K`) the exponential map is a local diffeomorphism, hence injective on a
neighbourhood of every point.  It follows that the agreement set `A = {t ∈ [0,1] | w₁ t = w₂ t}` is
both open (locally, both values lie in a neighbourhood on which `GExp p` is injective and they have
the same `GExp p`-image) and closed (it is the zero set of the continuous map `w₁ - w₂`), hence -- as
`[0,1]` is preconnected and `1 ∈ A` -- all of `[0,1]`.  In particular `0 ∈ A`. -/
theorem eq_at_zero_of_continuous_lift_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {K : ℝ} (hK : 0 < K) (hcurv : Submission.RauchK.CurvLe cov K)
    {p : M} {w₁ w₂ : ℝ → TangentSpace I p}
    (hc₁ : ContinuousOn w₁ (Set.Icc (0 : ℝ) 1))
    (hc₂ : ContinuousOn w₂ (Set.Icc (0 : ℝ) 1))
    (hb₁ : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖w₁ t‖ < Real.pi / Real.sqrt K)
    (hb₂ : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖w₂ t‖ < Real.pi / Real.sqrt K)
    (hG : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Submission.GlobalExp.GExp (cov := cov) hmet p (w₁ t)
        = Submission.GlobalExp.GExp (cov := cov) hmet p (w₂ t))
    (h1 : w₁ 1 = w₂ 1) :
    w₁ 0 = w₂ 0 := by
  classical
  -- ## 1. `GExp p` is locally injective at every vector of norm `< π/√K`
  have hloc : ∀ v : TangentSpace I p, ‖v‖ < Real.pi / Real.sqrt K →
      Submission.CutStep2.LocallyInjectiveAtGExp (I := I) hmet p v :=
    fun v hv => locallyInjectiveAtGExp_of_norm_lt_pi_div_sqrt (cov := cov) hmet htor hK hcurv hv
  -- ## 2. The agreement set inside the interval `[0,1]`
  set A : Set ↥(Set.Icc (0 : ℝ) 1) := {t | w₁ (t : ℝ) = w₂ (t : ℝ)} with hA
  have hcont₁ : Continuous fun t : ↥(Set.Icc (0 : ℝ) 1) => w₁ (t : ℝ) := hc₁.domRestrict
  have hcont₂ : Continuous fun t : ↥(Set.Icc (0 : ℝ) 1) => w₂ (t : ℝ) := hc₂.domRestrict
  -- `A` is closed: the zero set of a continuous `T_pM`-valued map
  have hAclosed : IsClosed A := by
    have hpre : A = (fun t : ↥(Set.Icc (0 : ℝ) 1) => w₁ (t : ℝ) - w₂ (t : ℝ)) ⁻¹' {0} := by
      ext t
      rw [hA]
      simp [sub_eq_zero]
    rw [hpre]
    exact isClosed_singleton.preimage (hcont₁.sub hcont₂)
  -- `A` is open: near a point of `A` both values lie where `GExp p` is injective
  have hAopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    rw [hA] at ht
    obtain ⟨V, hV, hVinj⟩ := hloc (w₁ (t : ℝ)) (hb₁ (t : ℝ) t.2)
    have h1' : (fun s : ↥(Set.Icc (0 : ℝ) 1) => w₁ (s : ℝ)) ⁻¹' V ∈ 𝓝 t :=
      hcont₁.continuousAt.preimage_mem_nhds hV
    have h2' : (fun s : ↥(Set.Icc (0 : ℝ) 1) => w₂ (s : ℝ)) ⁻¹' V ∈ 𝓝 t :=
      hcont₂.continuousAt.preimage_mem_nhds (ht ▸ hV)
    refine Filter.mem_of_superset (Filter.inter_mem h1' h2') ?_
    rintro s ⟨hs1, hs2⟩
    rw [hA]
    exact hVinj (w₁ (s : ℝ)) hs1 (w₂ (s : ℝ)) hs2 (hG (s : ℝ) s.2)
  -- `A` is nonempty, by the agreement hypothesis at `t = 1`
  have hAne : A.Nonempty :=
    ⟨⟨1, by norm_num⟩, by rw [hA]; simpa using h1⟩
  -- ## 3. `[0,1]` is preconnected, so `A = univ` and in particular `0 ∈ A`
  haveI : PreconnectedSpace ↥(Set.Icc (0 : ℝ) 1) :=
    Subtype.preconnectedSpace (isPreconnected_Icc (a := (0 : ℝ)) (b := 1))
  have hAuniv : A = Set.univ := IsClopen.eq_univ ⟨hAclosed, hAopen⟩ hAne
  have hmem : (⟨0, by norm_num⟩ : ↥(Set.Icc (0 : ℝ) 1)) ∈ A := by
    rw [hAuniv]
    exact Set.mem_univ _
  rw [hA] at hmem
  simpa using hmem

end Work.OddBound.longHomotopy
