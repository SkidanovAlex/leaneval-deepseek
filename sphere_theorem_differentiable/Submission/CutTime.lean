import Submission.GExpBoundary

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The minimising interval of a geodesic ray: the cut time

For a unit tangent vector `ξ` at `p`, the set of times `t ≥ 0` at which the ray `s ↦ GExp p (s • ξ)`
is **minimising** (`d(p, GExp p (t • ξ)) = t`) is an interval `[0, τ(ξ)]`: `τ(ξ)` is the *cut time*
of the direction `ξ`, and the cut locus of `p` is the image of the sphere of radius `τ`.

This file proves the two structural facts that make this true:

* `edist_GExp_smul_lt_of_lt_of_le`: **once a ray stops being minimising, it never is again** — if
  `d(p, GExp p (s • ξ)) < s` for some `s ≥ 0`, then `d(p, GExp p (t • ξ)) < t` for every `t ≥ s`.
  (The proof is the triangle inequality together with the ray bound:
  `d(p, γ t) ≤ d(p, γ s) + (t - s) < s + (t - s) = t`.)
* `edist_GExp_smul_eq_of_eq_of_le`: **up to the cut time the ray is minimising** — if
  `d(p, GExp p (t • ξ)) = t` then `d(p, GExp p (s • ξ)) = s` for every `0 ≤ s ≤ t`.

Together they say that `{t ≥ 0 : the ray is minimising at t}` is an interval of the form `[0, τ]`,
which is the classical description of the injectivity radius as `inf_ξ τ(ξ)`; note that this is
*not* the same as `InjAtLeast` (`InjAtLeast` allows two *distinct* minimising rays of the same
length, which is exactly the situation produced by the cut-point step).
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
open Submission.GExpRay
open Submission.GExpRay2
open Submission.InjRadius
open Submission.CutWitness

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.CutTime

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **Failure of minimisation persists.**  For a unit vector `ξ` and `0 ≤ s ≤ t`, if the ray of `ξ`
is *not* minimising at time `s`, then it is not minimising at time `t` either. -/
theorem edist_GExp_smul_lt_of_lt_of_le (hmet : IsMetricCompatible cov) {p : M}
    {ξ : TangentSpace I p} (hξ : ‖ξ‖ = 1) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (h : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (s • ξ))
      < ENNReal.ofReal s) :
    Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (t • ξ)) < ENNReal.ofReal t := by
  have hspos : 0 < s := by
    rcases eq_or_lt_of_le hs with h0 | h0
    · rw [← h0, zero_smul, GExp_zero, Manifold.riemannianEDist_self, ENNReal.ofReal_zero] at h
      exact absurd h (lt_irrefl 0)
    · exact h0
  have htsub : 0 ≤ t - s := by linarith
  have hray : Manifold.riemannianEDist I (GExp (cov := cov) hmet p (s • ξ))
      (GExp (cov := cov) hmet p (t • ξ)) ≤ ENNReal.ofReal (t - s) :=
    edist_GExp_smul_le (cov := cov) hmet p hξ hs (hs.trans hst) hst
  calc Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (t • ξ))
      ≤ Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (s • ξ))
        + Manifold.riemannianEDist I (GExp (cov := cov) hmet p (s • ξ))
          (GExp (cov := cov) hmet p (t • ξ)) :=
        Manifold.riemannianEDist_triangle (I := I)
          (x := p) (y := GExp (cov := cov) hmet p (s • ξ))
          (z := GExp (cov := cov) hmet p (t • ξ))
    _ < ENNReal.ofReal s + ENNReal.ofReal (t - s) :=
        ENNReal.add_lt_add_of_lt_of_le
          (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hray) h hray
    _ = ENNReal.ofReal t := by
        rw [← ENNReal.ofReal_add hs htsub]
        ring_nf

/-- **Up to the cut time the ray is minimising.**  For a unit vector `ξ` and `0 ≤ s ≤ t`, if the ray
of `ξ` is minimising at time `t` then it is minimising at time `s`. -/
theorem edist_GExp_smul_eq_of_le_of_eq (hmet : IsMetricCompatible cov) {p : M}
    {ξ : TangentSpace I p} (hξ : ‖ξ‖ = 1) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (h : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (t • ξ)) = ENNReal.ofReal t) :
    Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (s • ξ)) = ENNReal.ofReal s := by
  by_contra hcon
  refine absurd h (ne_of_lt ?_)
  exact edist_GExp_smul_lt_of_lt_of_le (cov := cov) hmet hξ hs hst (lt_of_le_of_ne
    (edist_GExp_smul_le_zero (cov := cov) hmet p hξ hs) hcon)

/-- **Rays up to the injectivity radius are minimising** (the boundary case included). -/
theorem edist_GExp_smul_eq_of_injAtLeast (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M] {p : M} {m : ℝ} (hinj : InjAtLeast hmet p m)
    {ξ : TangentSpace I p} (hξ : ‖ξ‖ = 1) {t : ℝ} (htnn : 0 ≤ t) (ht : t ≤ m) :
    Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (t • ξ)) = ENNReal.ofReal t := by
  rcases eq_or_lt_of_le htnn with h0 | hpos
  · rw [← h0, zero_smul, GExp_zero, Manifold.riemannianEDist_self, ENNReal.ofReal_zero]
  · have h := edist_GExp_eq_norm_of_le_of_injAtLeast (cov := cov) hmet htor hinj
      (w := t • ξ) ?_
    · rwa [norm_smul, Real.norm_of_nonneg hpos.le, hξ, mul_one] at h
    · rw [norm_smul, Real.norm_of_nonneg hpos.le, hξ, mul_one]
      exact ht

/-! ## The cut time -/

/-- **The set of times at which the ray of `ξ` is minimising.** -/
def minimisingSet (hmet : IsMetricCompatible cov) (p : M) (ξ : TangentSpace I p) : Set ℝ :=
  {t | 0 ≤ t ∧
    Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (t • ξ)) = ENNReal.ofReal t}

/-- **The cut time** of the direction `ξ`: the supremum of the times at which the ray of `ξ` is
minimising. -/
noncomputable def cutTime (hmet : IsMetricCompatible cov) (p : M) (ξ : TangentSpace I p) : ℝ :=
  sSup (minimisingSet (I := I) hmet p ξ)

variable [PathConnectedSpace M] [RegularSpace M]

/-- A bound for the Riemannian distance from a fixed point, on a compact manifold. -/
theorem exists_edist_le (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (p : M) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ y : M, Manifold.riemannianEDist I p y ≤ ENNReal.ofReal R := by
  haveI : ConnectedSpace M := inferInstance
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  letI : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  have hcont : Continuous (fun y : M => edist p y) :=
    continuous_edist.comp (continuous_const.prodMk continuous_id)
  obtain ⟨y₀, -, hmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hcont.continuousOn
  have hmax' : ∀ y : M, Manifold.riemannianEDist I p y ≤ Manifold.riemannianEDist I p y₀ := by
    intro y
    have h := hmax (Set.mem_univ y)
    rw [Set.mem_ofPred_eq] at h
    simpa only [Submission.EDist.edist_eq_riemannianEDist] using h
  have hfin : Manifold.riemannianEDist I p y₀ ≠ ⊤ :=
    (Submission.HopfRinow.riemannianEDist_lt_top (cov := cov) hmet htor p y₀).ne
  refine ⟨(Manifold.riemannianEDist I p y₀).toReal, ENNReal.toReal_nonneg, fun y => ?_⟩
  calc Manifold.riemannianEDist I p y ≤ Manifold.riemannianEDist I p y₀ := hmax' y
    _ = ENNReal.ofReal (Manifold.riemannianEDist I p y₀).toReal :=
        (ENNReal.ofReal_toReal hfin).symm

/-- The minimising set is bounded above (by the diameter). -/
theorem bddAbove_minimisingSet (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (p : M)
    (ξ : TangentSpace I p) : BddAbove (minimisingSet (I := I) hmet p ξ) := by
  obtain ⟨R, hR0, hR⟩ := exists_edist_le (I := I) (cov := cov) hmet htor p
  refine ⟨R, fun t ht => ?_⟩
  have h1 : ENNReal.ofReal t ≤ ENNReal.ofReal R := by
    rw [← ht.2]; exact hR _
  exact (ENNReal.ofReal_le_ofReal_iff hR0).mp h1

/-- The minimising set is downward closed. -/
theorem minimisingSet_of_le (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {p : M}
    {ξ : TangentSpace I p} (hξ : ‖ξ‖ = 1) {t s : ℝ}
    (ht : t ∈ minimisingSet (I := I) hmet p ξ) (hs : 0 ≤ s) (hst : s ≤ t) :
    s ∈ minimisingSet (I := I) hmet p ξ :=
  ⟨hs, edist_GExp_smul_eq_of_le_of_eq (cov := cov) hmet hξ hs hst ht.2⟩

/-- **The minimising set is the interval `[0, cutTime]`.** -/
theorem minimisingSet_eq_Icc (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {p : M}
    {ξ : TangentSpace I p} (hξ : ‖ξ‖ = 1) :
    minimisingSet (I := I) hmet p ξ = Set.Icc 0 (cutTime (I := I) hmet p ξ) := by
  have hbdd := bddAbove_minimisingSet (I := I) (cov := cov) hmet htor p ξ
  have hmem0 : (0 : ℝ) ∈ minimisingSet (I := I) hmet p ξ :=
    ⟨le_refl 0, by
      rw [zero_smul, GExp_zero, Manifold.riemannianEDist_self, ENNReal.ofReal_zero]⟩
  have hne : (minimisingSet (I := I) hmet p ξ).Nonempty := ⟨0, hmem0⟩
  -- nonnegative times below the sup are in the set
  have hbelow : ∀ s : ℝ, 0 ≤ s → s < cutTime (I := I) hmet p ξ →
      s ∈ minimisingSet (I := I) hmet p ξ := by
    intro s hs0 hslt
    obtain ⟨u, hu, hsu⟩ := exists_lt_of_lt_csSup hne hslt
    exact minimisingSet_of_le (cov := cov) hmet htor hξ hu hs0 hsu.le
  -- the sup belongs to the set
  have hle0 : 0 ≤ cutTime (I := I) hmet p ξ := le_trans hmem0.1 (le_csSup hbdd hmem0)
  have hsup : cutTime (I := I) hmet p ξ ∈ minimisingSet (I := I) hmet p ξ := by
    refine ⟨hle0, ?_⟩
    by_contra hcon
    rcases eq_or_lt_of_le hle0 with h0 | h0
    · exact hcon (by rw [← h0]; exact hmem0.2)
    · have hlt : Manifold.riemannianEDist I p
          (GExp (cov := cov) hmet p (cutTime (I := I) hmet p ξ • ξ))
          < ENNReal.ofReal (cutTime (I := I) hmet p ξ) :=
        lt_of_le_of_ne (edist_GExp_smul_le_zero (cov := cov) hmet p hξ h0.le) hcon
      obtain ⟨s, hs, hslt⟩ := exists_lt_of_not_minimising_ray (cov := cov) hmet hξ h0 hlt
      exact absurd (hbelow s hs.1.le hs.2).2 (ne_of_lt hslt)
  refine Set.Subset.antisymm (fun t ht => ⟨ht.1, le_csSup hbdd ht⟩) fun t ht => ?_
  by_contra hcon
  have htne : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (t • ξ))
      ≠ ENNReal.ofReal t := fun heq => hcon ⟨ht.1, heq⟩
  have hlt : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (t • ξ))
      < ENNReal.ofReal t :=
    lt_of_le_of_ne (edist_GExp_smul_le_zero (cov := cov) hmet p hξ ht.1) htne
  have hc : cutTime (I := I) hmet p ξ ∉ minimisingSet (I := I) hmet p ξ := by
    intro hmem
    have hlt' := edist_GExp_smul_lt_of_lt_of_le (cov := cov) hmet hξ ht.1 ht.2 hlt
    rw [hmem.2] at hlt'
    exact lt_irrefl _ hlt'
  exact hc hsup

/-- **The ray is minimising exactly up to the cut time.** -/
theorem mem_minimisingSet_iff (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {p : M}
    {ξ : TangentSpace I p} (hξ : ‖ξ‖ = 1) {t : ℝ} :
    t ∈ minimisingSet (I := I) hmet p ξ ↔ 0 ≤ t ∧ t ≤ cutTime (I := I) hmet p ξ := by
  rw [minimisingSet_eq_Icc (I := I) (cov := cov) hmet htor hξ, Set.mem_Icc]

/-- **The cut time is at least the injectivity radius.** -/
theorem injAtLeast_le_cutTime (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {p : M}
    {m : ℝ} (hinj : InjAtLeast hmet p m) {ξ : TangentSpace I p} (hξ : ‖ξ‖ = 1) :
    m ≤ cutTime (I := I) hmet p ξ := by
  rcases lt_or_ge m 0 with hm | hm
  · have hmem0 : (0 : ℝ) ∈ minimisingSet (I := I) hmet p ξ :=
      ⟨le_refl 0, by
        rw [zero_smul, GExp_zero, Manifold.riemannianEDist_self, ENNReal.ofReal_zero]⟩
    exact le_trans hm.le (le_csSup
      (bddAbove_minimisingSet (I := I) (cov := cov) hmet htor p ξ) hmem0)
  · exact le_csSup (bddAbove_minimisingSet (I := I) (cov := cov) hmet htor p ξ)
      ⟨hm, edist_GExp_smul_eq_of_injAtLeast (cov := cov) hmet htor (hinj := hinj)
        (hξ := hξ) (t := m) hm le_rfl⟩

end

end Submission.CutTime
