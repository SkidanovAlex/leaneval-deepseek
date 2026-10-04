import Mathlib
import Submission.Work.Diff.Dim2.Lib
import Submission.Work.Diff.C.Defs
import Submission.Work.Diff.C.GExp_localInverse
import Submission.Work.Diff.C.rdist_continuous

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Dim2

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set CovariantDerivative

/-- **Cap data and separation constants for the diameter pair.**

On a compact surface with a diameter pair `p, q` (distance `D`, all distances finite), there are

* smooth local inverses `Φp`, `Φq` of the exponential maps at `p` (resp. `q`) and a common radius
  `v > 0` such that on `{d(p,·) < v}` (resp. `{d(q,·) < v}`) the local inverse is smooth and the
  distance function is its fibre norm: `d(p,·) = ‖Φp ·‖`.  This is
  `Submission.Work.Diff.C.GExp_localInverse` made effective with an explicit radius via
  `Submission.EDist.setOf_riemannianEDist_lt_subset_nhds`;
* the triangle inequality `D ≤ d(p,x) + d(q,x)` in `toReal` form;
* a `δ > 0` such that `{D - δ ≤ d(p,·)} ⊆ {d(q,·) < v}`: because `q` is the *unique* maximiser of
  `d(p,·)` (and `d(p,·) ≤ D`), the closed superlevel sets shrink to `{q}`, so a small one lies in
  the small ball around `q` (compactness / finite intersection property
  `IsCompact.inter_iInter_nonempty`).  Continuity of `rdist` is available as `rdist_continuous` in
  `Submission/Work/Diff/C/rdist_continuous.lean`.

All three are elementary and are consumed (as projections) by the dimension-2 Reeb construction. -/
theorem cap_data
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
      [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    (htor : cov.torsion = 0)
    {p q : M} {D : ℝ}
    (hpq : Manifold.riemannianEDist I p q = ENNReal.ofReal D)
    (hdiam : ∀ r s : M, Manifold.riemannianEDist I r s ≤ ENNReal.ofReal D)
    (huniq : ∀ y : M, y ≠ q → Manifold.riemannianEDist I p y < ENNReal.ofReal D)
    (hfin : ∀ r s : M, Manifold.riemannianEDist I r s ≠ ⊤) :
    ∃ (Φp : M → TangentSpace I p) (Φq : M → TangentSpace I q) (v : ℝ) (δ : ℝ),
      0 < v ∧ 0 < δ ∧
      (∀ y : M, Work.Diff.C.rdist (I := I) (M := M) p y < v →
        ContMDiffAt I 𝓘(ℝ, TangentSpace I p) ∞ Φp y ∧
        Work.Diff.C.rdist (I := I) (M := M) p y = ‖Φp y‖) ∧
      (∀ y : M, Work.Diff.C.rdist (I := I) (M := M) q y < v →
        ContMDiffAt I 𝓘(ℝ, TangentSpace I q) ∞ Φq y ∧
        Work.Diff.C.rdist (I := I) (M := M) q y = ‖Φq y‖) ∧
      (∀ x : M, D ≤ Work.Diff.C.rdist (I := I) (M := M) p x +
        Work.Diff.C.rdist (I := I) (M := M) q x) ∧
      (∀ y : M, D - δ ≤ Work.Diff.C.rdist (I := I) (M := M) p y →
        Work.Diff.C.rdist (I := I) (M := M) q y < v) := by
  classical
  -- The smooth Riemannian bundle gives the continuous one, which the library lemmas need.
  haveI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I) (M := M)
  -- **Making a neighbourhood of `a` effective as a ball `{d(a,·) < v}`.**
  have hrad : ∀ (a : M) (s : Set M), s ∈ 𝓝 a → ∃ v > 0,
      {y | Work.Diff.C.rdist (I := I) (M := M) a y < v} ⊆ s := by
    intro a s hs
    obtain ⟨c, hc, hcsub⟩ := Submission.EDist.setOf_riemannianEDist_lt_subset_nhds (I := I) hs
    -- `min c 1` is a finite, positive extended radius; `(min c 1).toReal / 2` is a real radius
    -- whose `ofReal` is still below `c`.
    have hc'0 : 0 < min c 1 := lt_min hc (by norm_num)
    have hc't : min c 1 ≠ ⊤ :=
      ne_of_lt (lt_of_le_of_lt (min_le_right _ _) ENNReal.one_lt_top)
    refine ⟨(min c 1).toReal / 2, half_pos (ENNReal.toReal_pos (ne_of_gt hc'0) hc't), ?_⟩
    intro y hy
    apply hcsub
    change Manifold.riemannianEDist I a y < c
    have h2 : Manifold.riemannianEDist I a y
        = ENNReal.ofReal (Work.Diff.C.rdist (I := I) (M := M) a y) :=
      (ENNReal.ofReal_toReal (hfin a y)).symm
    rw [h2]
    have hlt : ENNReal.ofReal (Work.Diff.C.rdist (I := I) (M := M) a y)
        < ENNReal.ofReal ((min c 1).toReal / 2) := by
      rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (p := Work.Diff.C.rdist (I := I) (M := M) a y)
        ENNReal.toReal_nonneg]
      exact hy
    refine lt_of_lt_of_le hlt ?_
    rw [show ENNReal.ofReal ((min c 1).toReal / 2)
        = ENNReal.ofReal ((min c 1).toReal) / (2 : ℝ≥0∞) from ?_]
    · rw [ENNReal.ofReal_toReal hc't]
      exact le_of_lt (lt_of_lt_of_le (ENNReal.half_lt_self (ne_of_gt hc'0) hc't) (min_le_left _ _))
    · rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat]
  by_cases hD : 0 < D
  · -- ## The non-degenerate case: `D > 0`.
    -- ### Step 1: local inverses and a common radius.
    obtain ⟨Φp, hΦp_sm, -, -, hΦp_dat⟩ :=
      Work.Diff.C.GExp_localInverse (I := I) (M := M) (cov := cov) hmet htor p
    obtain ⟨Φq, hΦq_sm, -, -, hΦq_dat⟩ :=
      Work.Diff.C.GExp_localInverse (I := I) (M := M) (cov := cov) hmet htor q
    have hp_nhds : {y : M | ContMDiffAt I 𝓘(ℝ, TangentSpace I p) ∞ Φp y ∧
        Work.Diff.C.rdist (I := I) (M := M) p y = ‖Φp y‖} ∈ 𝓝 p :=
      Filter.mem_of_superset (hΦp_sm.and hΦp_dat) (fun y hy => ⟨hy.1, hy.2.2⟩)
    have hq_nhds : {y : M | ContMDiffAt I 𝓘(ℝ, TangentSpace I q) ∞ Φq y ∧
        Work.Diff.C.rdist (I := I) (M := M) q y = ‖Φq y‖} ∈ 𝓝 q :=
      Filter.mem_of_superset (hΦq_sm.and hΦq_dat) (fun y hy => ⟨hy.1, hy.2.2⟩)
    obtain ⟨vp, hvp, hvp_sub⟩ := hrad p _ hp_nhds
    obtain ⟨vq, hvq, hvq_sub⟩ := hrad q _ hq_nhds
    have hvpos : (0 : ℝ) < min vp vq := lt_min hvp hvq
    have hsubp : ∀ y : M, Work.Diff.C.rdist (I := I) (M := M) p y < min vp vq →
        ContMDiffAt I 𝓘(ℝ, TangentSpace I p) ∞ Φp y ∧
        Work.Diff.C.rdist (I := I) (M := M) p y = ‖Φp y‖ := by
      intro y hy
      have hy' : Work.Diff.C.rdist (I := I) (M := M) p y < vp :=
        lt_of_lt_of_le hy (min_le_left vp vq)
      exact hvp_sub hy'
    have hsubq : ∀ y : M, Work.Diff.C.rdist (I := I) (M := M) q y < min vp vq →
        ContMDiffAt I 𝓘(ℝ, TangentSpace I q) ∞ Φq y ∧
        Work.Diff.C.rdist (I := I) (M := M) q y = ‖Φq y‖ := by
      intro y hy
      have hy' : Work.Diff.C.rdist (I := I) (M := M) q y < vq :=
        lt_of_lt_of_le hy (min_le_right vp vq)
      exact hvq_sub hy'
    -- ### Step 3: the separation constant `δ`, via compactness of the complement of the small ball
    -- around `q`.  On that compact set `d(p,·)` is `< D` (unique maximiser), so it has a maximum
    -- `M₀ < D`, and `δ := (D - M₀)/2` works.
    set s : Set M := {y : M | min vp vq ≤ Work.Diff.C.rdist (I := I) (M := M) q y} with hsdef
    have hsclosed : IsClosed s := by
      rw [hsdef]
      exact isClosed_le continuous_const (Work.Diff.C.rdist_continuous (I := I) (M := M) q)
    have hbound : ∃ M₀, M₀ < D ∧ ∀ y ∈ s, Work.Diff.C.rdist (I := I) (M := M) p y ≤ M₀ := by
      rcases s.eq_empty_or_nonempty with hemp | hne
      · refine ⟨D - 1, by linarith, ?_⟩
        intro y hy
        rw [hemp] at hy
        exact absurd hy (Set.notMem_empty y)
      · obtain ⟨y₀, hy₀, hmax⟩ := hsclosed.isCompact.exists_isMaxOn hne
          (Work.Diff.C.rdist_continuous (I := I) (M := M) p).continuousOn
        refine ⟨Work.Diff.C.rdist (I := I) (M := M) p y₀, ?_, fun y hy => hmax hy⟩
        have hy₀le : min vp vq ≤ Work.Diff.C.rdist (I := I) (M := M) q y₀ := by
          rw [hsdef] at hy₀; exact hy₀
        have hy₀ne : y₀ ≠ q := by
          intro h
          rw [h] at hy₀le
          have h0 : Work.Diff.C.rdist (I := I) (M := M) q q = 0 := by
            show (Manifold.riemannianEDist I q q).toReal = 0
            rw [Manifold.riemannianEDist_self]; simp
          rw [h0] at hy₀le
          exact absurd hy₀le (not_le.mpr hvpos)
        have hlt := huniq y₀ hy₀ne
        have hA : Work.Diff.C.rdist (I := I) (M := M) p y₀
            = (Manifold.riemannianEDist I p y₀).toReal := rfl
        have hB : D = (ENNReal.ofReal D).toReal := (ENNReal.toReal_ofReal hD.le).symm
        rw [hA, hB]
        exact (ENNReal.toReal_lt_toReal (hfin p y₀) ENNReal.ofReal_ne_top).mpr hlt
    obtain ⟨M₀, hM₀lt, hM₀le⟩ := hbound
    refine ⟨Φp, Φq, min vp vq, (D - M₀) / 2, hvpos, by linarith, hsubp, hsubq, ?_, ?_⟩
    · -- ### Step 2: the triangle inequality, in `toReal` form.
      intro x
      have htri := Manifold.riemannianEDist_triangle (I := I) (x := p) (y := x) (z := q)
      have hle : ENNReal.ofReal D ≤
          Manifold.riemannianEDist I p x + Manifold.riemannianEDist I q x := by
        rw [← hpq, ← Manifold.riemannianEDist_comm (I := I) (x := x) (y := q)]
        exact htri
      have hne : Manifold.riemannianEDist I p x + Manifold.riemannianEDist I q x ≠ ⊤ :=
        ENNReal.add_ne_top.mpr ⟨hfin p x, hfin q x⟩
      have h2 : D ≤ (Manifold.riemannianEDist I p x + Manifold.riemannianEDist I q x).toReal := by
        rw [← ENNReal.toReal_ofReal hD.le]
        exact ENNReal.toReal_mono hne hle
      rw [ENNReal.toReal_add (hfin p x) (hfin q x)] at h2
      exact h2
    · intro y hy
      by_contra hcon
      have hyK : y ∈ s := by
        rw [hsdef]
        exact le_of_not_gt hcon
      have h₁ := hM₀le y hyK
      linarith
  · -- ## The degenerate case: `D ≤ 0` forces `M` to be a subsingleton (only `q` can exist).
    have hsub : Subsingleton M := by
      have hDle : D ≤ 0 := le_of_not_gt hD
      have hof : ENNReal.ofReal D = 0 := ENNReal.ofReal_eq_zero.mpr hDle
      refine ⟨fun a b => ?_⟩
      have ha : a = q := by
        by_contra ha
        have h := huniq a ha
        rw [hof] at h
        exact absurd h (not_lt.mpr zero_le)
      have hb : b = q := by
        by_contra hb
        have h := huniq b hb
        rw [hof] at h
        exact absurd h (not_lt.mpr zero_le)
      rw [ha, hb]
    refine ⟨fun _ => 0, fun _ => 0, 1, 1, by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
    · intro y _hy
      refine ⟨contMDiffAt_const, ?_⟩
      have hpy : p = y := hsub.elim p y
      have hA : Work.Diff.C.rdist (I := I) (M := M) p y
          = (Manifold.riemannianEDist I p y).toReal := rfl
      rw [hA, hpy, Manifold.riemannianEDist_self]
      simp
    · intro y _hy
      refine ⟨contMDiffAt_const, ?_⟩
      have hqy : q = y := hsub.elim q y
      have hA : Work.Diff.C.rdist (I := I) (M := M) q y
          = (Manifold.riemannianEDist I q y).toReal := rfl
      rw [hA, hqy, Manifold.riemannianEDist_self]
      simp
    · intro x
      have hpx : p = x := hsub.elim p x
      have hqx : q = x := hsub.elim q x
      have h1 : Work.Diff.C.rdist (I := I) (M := M) p x = 0 := by
        have hA : Work.Diff.C.rdist (I := I) (M := M) p x
            = (Manifold.riemannianEDist I p x).toReal := rfl
        rw [hA, hpx, Manifold.riemannianEDist_self]
        simp
      have h2 : Work.Diff.C.rdist (I := I) (M := M) q x = 0 := by
        have hA : Work.Diff.C.rdist (I := I) (M := M) q x
            = (Manifold.riemannianEDist I q x).toReal := rfl
        rw [hA, hqx, Manifold.riemannianEDist_self]
        simp
      rw [h1, h2]
      have : D ≤ 0 := le_of_not_gt hD
      linarith
    · intro y _hy
      have hqy : q = y := hsub.elim q y
      have hA : Work.Diff.C.rdist (I := I) (M := M) q y
          = (Manifold.riemannianEDist I q y).toReal := rfl
      rw [hA, hqy, Manifold.riemannianEDist_self]
      simp

end Work.Diff.Dim2
