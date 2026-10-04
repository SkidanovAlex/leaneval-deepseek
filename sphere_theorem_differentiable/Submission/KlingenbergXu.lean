import Submission.KlingenbergCore
import Submission.GeodesicLoop
import Submission.ConjCut

set_option backward.isDefEq.respectTransparency.types false

/-!
# The Klingenberg reduction with **value-closed** geodesic loops

`Submission.KlingenbergCore.diameter_gt_half_pi_of_klingenberg` reduces the whole Klingenberg
estimate to two inputs, `hXu` (the Klingenberg–Xu step) and `hdeep` (Klingenberg 1961), both stated
for the **velocity-matched** object `Submission.KlingenbergLemma.IsClosedGeodesicLoopAt`.

As recorded in `Submission/Roadmap.lean` §105, the literature (Xu, arXiv:1401.5549, Theorem B and
Theorem 1.3) produces a **value-closed** geodesic loop: the two minimal geodesics from `p` to its
closest cut point form a *whole geodesic* through that point, and the velocity matching at the base
point is an additional hypothesis ("Moreover, if `d(p,x₀)` is also a local minimum of `d(x₀,·)` on
`C_{x₀}` …").  Xu's structure theorem is correspondingly
`injrad(p) = min{econj(p), ½ · (shortest geodesic loop at p)}`, where the "geodesic loops" are
value-closed and `econj(p) ≥ conj(p)` by Rauch.

This file provides the **value-closed variant of the whole reduction**, additively: the two
predicates are interchangeable in one direction (`IsClosedGeodesicLoopAt.isGeodesicLoopAt`), so
nothing here supersedes `KlingenbergCore`; it gives the route that matches the literature and whose
`hXu` is exactly Klingenberg's lemma in Xu's sharp form.

* `le_two_mul_of_isGeodesicLoop_lower_of_lt` — the transference step for value-closed loops;
* `pi_div_sqrt_le_of_isGeodesicLoop_lower` — the pointwise Klingenberg estimate;
* `diameter_gt_half_pi_of_klingenberg_loop` — the diameter estimate `(K2)`, hence the whole reduction.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.InjRadius
open Submission.RauchK
open Submission.CutStep3
open Submission.GeodesicLoop

namespace Submission.KlingenbergXu

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **Klingenberg's lemma, the transference step, for value-closed geodesic loops.**

Let `m` be the injectivity radius of `p`, suppose `m < π/√K` for a curvature bound `sec ≤ K`
(`0 < K`), and suppose the **Klingenberg–Xu input** in Xu's form: two distinct minimising vectors
`u ≠ v` of norm `m` with the same image produce a *(value-closed)* geodesic loop at `p` of length
`≤ 2m`.  If every such geodesic loop has length `≥ ℓ`, then `ℓ ≤ 2m`.

The proof is `KlingenbergTransfer.le_two_mul_of_isClosedGeodesicLoop_lower_of_lt` with the predicate
weakened: `CutStep3.exists_two_minimising_or_not_locallyInjective` is independent of it — either the
two minimal vectors exist (and `hXu` applies), or `GExp p` fails to be locally injective at a vector
of norm `m`, which is impossible below `π/√K` by Rauch. -/
theorem le_two_mul_of_isGeodesicLoop_lower_of_lt
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {K : ℝ} (hK : CurvLe cov K) (hKpos : 0 < K)
    {p : M} {m ℓ : ℝ} (hm : 0 < m) (hmπ : m < Real.pi / Real.sqrt K)
    (hinj : InjAtLeast hmet p m) (hmax : ∀ r : ℝ, m < r → ¬ InjAtLeast hmet p r)
    (hXu : ∀ u v : TangentSpace I p, u ≠ v → ‖u‖ = m → ‖v‖ = m →
      GExp (cov := cov) hmet p u = GExp (cov := cov) hmet p v →
      ∃ (T : ℝ) (γ : ℝ → M), T ≤ 2 * m ∧ IsGeodesicLoopAt (I := I) (cov := cov) hmet p T γ)
    (hℓ : ∀ (T : ℝ) (γ : ℝ → M), IsGeodesicLoopAt (I := I) (cov := cov) hmet p T γ → ℓ ≤ T) :
    ℓ ≤ 2 * m := by
  rcases Submission.CutStep3.exists_two_minimising_or_not_locallyInjective (cov := cov) hmet htor
    (p := p) (m := m) hinj hmax with ⟨u, v, huv, hG, hu, hv, -⟩ | ⟨w, hw, hwloc⟩
  · rcases hXu u v huv hu hv hG with ⟨T, γ, hT, hloop⟩
    exact le_trans (hℓ T γ hloop) hT
  · have hw0 : w ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hw
      linarith
    exact absurd (Submission.RayConj.locallyInjectiveAtGExp_of_norm_lt_pi_div_sqrt (cov := cov)
      hmet htor hK hKpos hw0 (by rw [hw]; exact hmπ)) hwloc

/-- **The pointwise Klingenberg estimate, for value-closed geodesic loops.**  Let `m` be the maximal
injectivity radius of `p` and suppose that (i) the **Klingenberg–Xu step** holds at `p` in Xu's
value-closed form and (ii) every geodesic loop at `p` has length `≥ 2π/√K`.  Then
`π/√K ≤ inj(p)`.

This is Klingenberg's structure theorem in Xu's form,
`injrad(p) = min{econj(p), ½ · (shortest geodesic loop at p)}`, evaluated at the curvature bound:
`econj(p) ≥ conj(p) ≥ π/√K` by Rauch, and the shortest geodesic loop is `≥ 2π/√K` by hypothesis. -/
theorem pi_div_sqrt_le_of_isGeodesicLoop_lower
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {K : ℝ} (hK : CurvLe cov K) (hKpos : 0 < K)
    {p : M} {m : ℝ} (hm : 0 < m)
    (hinj : InjAtLeast hmet p m) (hmax : ∀ r : ℝ, m < r → ¬ InjAtLeast hmet p r)
    (hXu : ∀ u v : TangentSpace I p, u ≠ v → ‖u‖ = m → ‖v‖ = m →
      GExp (cov := cov) hmet p u = GExp (cov := cov) hmet p v →
      ∃ (T : ℝ) (γ : ℝ → M), T ≤ 2 * m ∧ IsGeodesicLoopAt (I := I) (cov := cov) hmet p T γ)
    (hdeep : ∀ (T : ℝ) (γ : ℝ → M),
      IsGeodesicLoopAt (I := I) (cov := cov) hmet p T γ → 2 * Real.pi / Real.sqrt K ≤ T) :
    Real.pi / Real.sqrt K ≤ m := by
  by_cases hcase : Real.pi / Real.sqrt K ≤ m
  · exact hcase
  · push_neg at hcase
    rcases Submission.CutStep3.exists_two_minimising_or_not_locallyInjective (cov := cov) hmet htor
      (p := p) (m := m) hinj hmax with ⟨u, v, huv, hG, hu, hv, -⟩ | ⟨w, hw, hwloc⟩
    · rcases hXu u v huv hu hv hG with ⟨T, γ, hT, hloop⟩
      have h1 := hdeep T γ hloop
      have h2 : 2 * Real.pi / Real.sqrt K ≤ 2 * m := le_trans h1 hT
      rw [mul_div_assoc] at h2
      linarith
    · have hw0 : w ≠ 0 := by
        rintro rfl
        rw [norm_zero] at hw
        linarith
      exact absurd (Submission.RayConj.locallyInjectiveAtGExp_of_norm_lt_pi_div_sqrt (cov := cov)
        hmet htor hK hKpos hw0 (by rw [hw]; exact hcase)) hwloc

/-- **`(K2)` from the value-closed Klingenberg inputs.**  Let `M` be a compact Riemannian manifold
with `sec ≤ K`, `0 < K < 4`, and assume

* `hXu` — the Klingenberg–Xu step in Xu's value-closed form (as above);
* `hdeep` — the value-closed Klingenberg theorem: every geodesic loop at any point has length
  `≥ 2π/√K`.

Then some pair of points is at distance `> π/2`.  This is
`KlingenbergCore.diameter_gt_half_pi_of_klingenberg` with the value-closed pair of hypotheses, i.e.
exactly the pair that Klingenberg's own lemma/Theorem B and Xu's Theorem 1.3 supply. -/
theorem diameter_gt_half_pi_of_klingenberg_loop (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {K : ℝ} (hK : 0 < K) (hK4 : K < 4) (hcurv : CurvLe cov K)
    (hXu : ∀ (p : M) {m : ℝ}, 0 < m → InjAtLeast hmet p m →
      (∀ r : ℝ, m < r → ¬ InjAtLeast hmet p r) → m < Real.pi / Real.sqrt K →
      ∀ u v : TangentSpace I p, u ≠ v → ‖u‖ = m → ‖v‖ = m →
        GExp (cov := cov) hmet p u = GExp (cov := cov) hmet p v →
        ∃ (T : ℝ) (γ : ℝ → M), T ≤ 2 * m ∧
          IsGeodesicLoopAt (I := I) (cov := cov) hmet p T γ)
    (hdeep : ∀ (p : M) (T : ℝ) (γ : ℝ → M),
      IsGeodesicLoopAt (I := I) (cov := cov) hmet p T γ →
      2 * Real.pi / Real.sqrt K ≤ T) :
    ∃ p q : M, ENNReal.ofReal (Real.pi / 2) < Manifold.riemannianEDist I p q := by
  classical
  obtain ⟨p⟩ : Nonempty M := inferInstance
  obtain ⟨ρ, hρpos, hInjAll⟩ := Submission.UniformInj.exists_pos_injAllAtLeast (cov := cov) hmet
  obtain ⟨R, hR0, hR⟩ := Submission.CutTime.exists_edist_le (I := I) (cov := cov) hmet htor p
  obtain ⟨m, hinj, hmax⟩ := Submission.InjRadius.exists_injAtLeast_max (I := I) (cov := cov) hmet
    ⟨ρ, hInjAll p⟩
    ⟨R + 2, Submission.InjSup.not_injAtLeast_of_lt_diam (I := I) (cov := cov) hmet htor
      (x := p) (D := R) (s := R + 1) (by linarith) (by linarith) hR (by linarith)⟩
  have hmpos : 0 < m := by
    by_contra hcon
    push_neg at hcon
    exact hmax ρ (by linarith) (hInjAll p)
  have hcase : Real.pi / Real.sqrt K ≤ m := by
    by_contra hcon
    push_neg at hcon
    refine absurd (pi_div_sqrt_le_of_isGeodesicLoop_lower (cov := cov) hmet htor hcurv hK hmpos
      hinj hmax ?_ (hdeep p)) (not_le.mpr hcon)
    intro u v huv hu hv hG
    exact hXu p hmpos hinj hmax hcon u v huv hu hv hG
  have hπ2 : Real.pi / 2 < Real.pi / Real.sqrt K := by
    have hspos : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
    have hs2 : Real.sqrt K < 2 := by
      have h := Real.sqrt_lt_sqrt hK.le hK4
      have h4 : Real.sqrt (4 : ℝ) = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]
      rwa [h4] at h
    rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2) hspos]
    nlinarith [Real.pi_pos]
  obtain ⟨q, hq⟩ := Submission.KlingenbergStep.exists_edist_gt_half_pi_of_injAtLeast (cov := cov)
    hmet htor hπ2 (injAtLeast_mono (I := I) hmet hinj hcase)
  exact ⟨p, q, hq⟩

/-! ## The two named inputs, in Xu's form

The two remaining inputs of the reduction are single named `Prop`s, so that the gap can be attacked
(and delegated) one statement at a time.  The first is Klingenberg's lemma in Xu's sharp form (Xu,
arXiv:1401.5549, Theorem B); the second is the value-closed Klingenberg length bound
(Klingenberg 1961), which is the form Xu's Theorem 1.3 consumes.

**A correction (see `Submission/Roadmap.lean` §106).**  As stated in an earlier session,
`XuCornerExcluded` had *no* non-conjugacy hypothesis, and in that form it is **FALSE**: on the round
sphere `Sⁿ` of curvature `1` one has `inj(p) = π` (so `m = π` is the maximal injectivity radius),
every two unit directions `ξ ≠ η` at `p` have rays meeting at time `π` (the antipode) with unit
speed and minimising, and the two velocities there are `w₁ = -ξ`, `w₂ = -η`; the conclusion
`w₁ = -w₂` would force `ξ = η`.  The missing hypothesis is exactly the one Xu's Theorem B carries:
*some* minimal geodesic from `p` to the closest cut point must be **free of conjugate points**
(Xu assumes `x₀ ∈ exp_p(C̃_p ∖ J̃_p)`).  In the sphere example the differential of `exp_p` is
singular at every vector of norm `π`, so the hypothesis fails there.  In the application below
`π/√K` the hypothesis is automatic by Rauch (`ConjCut.not_isConjugateTime_of_lt_pi_div_sqrt`), which
is why the corrected statement still discharges the Klingenberg–Xu step in the range where it is
needed. -/

/-- **The Klingenberg–Xu step** (Xu's Theorem B in the project's language):

two distinct minimising vectors `u ≠ v` of norm `m` at `p` with the same image — equivalently: at a
point whose maximal injectivity radius is `m < π/√K`, two distinct minimal geodesics joining `p` to
its closest cut point — produce a *(value-closed)* **geodesic loop at `p` of length `≤ 2m`**.

Xu proves this for the closest cut point of `p` provided the point is not conjugate to `p` along
*every* minimal geodesic; below `π/√K` no conjugacy can occur at all (Rauch), which is the
hypothesis `m < π/√K` recorded here.  The *velocity matching* at `p` is **not** part of Xu's
conclusion, which is why the loop produced is the value-closed one
(`Submission.GeodesicLoop.IsGeodesicLoopAt`).

Equivalently (and this is the sharper anchor): Xu's theorem is the assertion `XuCornerExcluded hmet`
below — there is no *genuine corner* at the closest cut point.  The dichotomy
`Submission.GeodesicLoop.exists_geodesicLoop_or_shorter_loop` shows that this is exactly what is
missing: the "opposite velocities" branch already yields the geodesic loop unconditionally
(`GeodesicLoop.isGeodesicLoopAt_of_velocity_eq_neg`), and only the "genuine corner" branch is open;
see `klingenbergLoopStep_of_xuCornerExcluded` for the formal reduction. -/
def KlingenbergLoopStep (hmet : IsMetricCompatible cov) (K : ℝ) : Prop :=
  ∀ (p : M) {m : ℝ}, 0 < m → InjAtLeast hmet p m →
    (∀ r : ℝ, m < r → ¬ InjAtLeast hmet p r) → m < Real.pi / Real.sqrt K →
    ∀ u v : TangentSpace I p, u ≠ v → ‖u‖ = m → ‖v‖ = m →
      GExp (cov := cov) hmet p u = GExp (cov := cov) hmet p v →
      ∃ (T : ℝ) (γ : ℝ → M), T ≤ 2 * m ∧
        IsGeodesicLoopAt (I := I) (cov := cov) hmet p T γ

/-- **The value-closed Klingenberg length bound** (Klingenberg 1961): for `sec ∈ [K/4, K]` on a
simply connected `M`, every *(value-closed)* geodesic loop has length `≥ 2π/√K`.  This is the
hypothesis Xu's Theorem 1.3 needs, since `injrad(p) = min{econj(p), ½ · (shortest geodesic loop at
p)}` and `econj(p) ≥ conj(p) ≥ π/√K` by Rauch. -/
def LoopLengthLowerBound (hmet : IsMetricCompatible cov) (K : ℝ) : Prop :=
  ∀ (p : M) (T : ℝ) (γ : ℝ → M),
    IsGeodesicLoopAt (I := I) (cov := cov) hmet p T γ → 2 * Real.pi / Real.sqrt K ≤ T

/-- **`(K2)` from the two named inputs.**  This is the value-closed counterpart of
`KlingenbergCore.diameter_gt_half_pi_of_klingenberg`: it exhibits the reduction of the Klingenberg
estimate to the two statements that the literature actually provides. -/
theorem diameter_gt_half_pi_of_xu (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {K : ℝ} (hK : 0 < K) (hK4 : K < 4) (hcurv : CurvLe cov K)
    (hXu : KlingenbergLoopStep (I := I) (cov := cov) hmet K)
    (hdeep : LoopLengthLowerBound (I := I) (cov := cov) hmet K) :
    ∃ p q : M, ENNReal.ofReal (Real.pi / 2) < Manifold.riemannianEDist I p q :=
  diameter_gt_half_pi_of_klingenberg_loop (cov := cov) hmet htor hK hK4 hcurv
    (fun p _ hm hinj hmax hcon u v huv hu hv hG => hXu p hm hinj hmax hcon u v huv hu hv hG)
    hdeep

/-- **Xu's Theorem B, in its sharp form** (Xu, arXiv:1401.5549): *at the closest cut point, a
minimal geodesic which is free of conjugate points cannot meet another one with a genuine corner.*

Concretely: if `m` is the (maximal) injectivity radius of `p`, `ξ ≠ η` are unit directions whose
rays meet again at time `m` and both rays are minimising there, and **`p` is not conjugate to the
meeting point along the ray of `ξ`**, then the two rays arrive at the meeting point with **opposite
velocities** — equivalently, the two minimal geodesics are the two halves of one geodesic, and the
concatenation `p → q → p` is a *single* geodesic of length `2m`.

This is the exact assertion left open by `exists_geodesicLoop_or_shorter_loop`
(`Submission/GeodesicLoop`): the dichotomy there says that either the velocities are opposite (and a
geodesic loop at `p` of length `2m` exists, unconditionally), or the broken loop can be shortened
— and Xu's Theorem B rules out the second alternative *provided* the non-conjugacy hypothesis holds.
The latter is not a technicality: without it the statement is false (round sphere, norm `π`
vectors), see the discussion above and `Submission/Roadmap.lean` §106.

The non-conjugacy hypothesis is *automatic* below `π/√K` by Rauch, which is the only range in which
the Klingenberg–Xu step is applied (`klingenbergLoopStep_of_xuCornerExcluded`). -/
def XuCornerExcluded (hmet : IsMetricCompatible cov) : Prop :=
  ∀ (p : M) {m : ℝ}, 0 < m → InjAtLeast hmet p m →
    (∀ r : ℝ, m < r → ¬ InjAtLeast hmet p r) →
    ∀ (ξ η : TangentSpace I p), ‖ξ‖ = 1 → ‖η‖ = 1 → ξ ≠ η →
      Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (m • ξ)) = ENNReal.ofReal m →
      Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (m • η)) = ENNReal.ofReal m →
      GExp (cov := cov) hmet p (m • ξ) = GExp (cov := cov) hmet p (m • η) →
      ¬ Submission.ConjRadius.IsConjugateTime cov
        (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) m →
      curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) m
        = -curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • η)) m

/-- **Xu's Theorem B implies the Klingenberg–Xu step.**  This is the content of the dichotomy
`GeodesicLoop.exists_geodesicLoop_or_shorter_loop`: given Xu's Theorem B there is no genuine corner at
the closest cut point, so the two minimal geodesics are the two halves of one geodesic and the first
ray is a geodesic loop at `p` of length exactly `2m`.

The passage from "two distinct minimal vectors with the same image" to "two unit directions whose rays
meet at time `m` and are minimising there" is `CutPoint.norm_eq_and_minimising_of_witness_pair`
(injectivity on the ball forces both norms to be `m` and both rays to be minimising) followed by
`KlingenbergLoop.exists_broken_minimising_loop`.  The non-conjugacy hypothesis of Xu's theorem is
supplied by Rauch: below `π/√K` no point is conjugate to `p`. -/
theorem klingenbergLoopStep_of_xuCornerExcluded (hmet : IsMetricCompatible cov)
    (htor : cov.torsion = 0) [PathConnectedSpace M] [RegularSpace M]
    {K : ℝ} (hK : CurvLe cov K) (hKpos : 0 < K)
    (h : XuCornerExcluded (I := I) (cov := cov) hmet) :
    KlingenbergLoopStep (I := I) (cov := cov) hmet K := by
  intro p m hm hinj hmax hmπ u v huv hu hv hG
  obtain ⟨-, -, hminu, -⟩ :=
    Submission.CutPoint.norm_eq_and_minimising_of_witness_pair (cov := cov) hmet htor hinj huv hG
      (le_of_eq hu) (le_of_eq hv)
  obtain ⟨ξ, η, hξ1, hη1, hξη, hmeet, -, -, -, -, -, hminξ, hminη⟩ :=
    Submission.KlingenbergLoop.exists_broken_minimising_loop (cov := cov) hmet htor hm hu hv huv hG
      hminu
  have hminξm : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (m • ξ))
      = ENNReal.ofReal m := hminξ m (Set.mem_Icc.mpr ⟨le_of_lt hm, le_rfl⟩)
  have hminηm : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (m • η))
      = ENNReal.ofReal m := by
    have h0 := hminη 0 (Set.mem_Icc.mpr ⟨le_rfl, le_of_lt hm⟩)
    rw [sub_zero] at h0
    exact h0
  have hnc : ¬ Submission.ConjRadius.IsConjugateTime cov
      (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) m :=
    Submission.ConjCut.not_isConjugateTime_of_lt_pi_div_sqrt (cov := cov) hmet htor hK hKpos hmπ
  have hvel := h p hm hinj hmax ξ η hξ1 hη1 hξη hminξm hminηm hmeet hnc
  exact ⟨2 * m, fun s : ℝ => GExp (cov := cov) hmet p (s • ξ), le_rfl,
    isGeodesicLoopAt_of_velocity_eq_neg (cov := cov) hmet hξ1 hη1 hm hmeet hvel⟩

/-- **`(K2)` from Xu's Theorem B alone**, plus the value-closed Klingenberg length bound. -/
theorem diameter_gt_half_pi_of_xuCornerExcluded (hmet : IsMetricCompatible cov)
    (htor : cov.torsion = 0) [PathConnectedSpace M] [RegularSpace M]
    {K : ℝ} (hK : 0 < K) (hK4 : K < 4) (hcurv : CurvLe cov K)
    (hXu : XuCornerExcluded (I := I) (cov := cov) hmet)
    (hdeep : LoopLengthLowerBound (I := I) (cov := cov) hmet K) :
    ∃ p q : M, ENNReal.ofReal (Real.pi / 2) < Manifold.riemannianEDist I p q :=
  diameter_gt_half_pi_of_xu (cov := cov) hmet htor hK hK4 hcurv
    (klingenbergLoopStep_of_xuCornerExcluded (cov := cov) hmet htor hcurv hK hXu) hdeep

end

end Submission.KlingenbergXu
