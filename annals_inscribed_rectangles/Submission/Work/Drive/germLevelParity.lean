import Mathlib
import Submission.Work.Drive.sideGermDefs
import Submission.Work.Drive.coreMeetLevelIndep
import Submission.Work.Drive.rotSweepEquivariance
import Submission.Work.Drive.planeChain
import Submission.Work.Drive.chartIsSmooth

/-!
# The cross-level parity of the germ count (`hparA`/`hparN` of the `hn2` endpoint)

The `hn2` endpoint `Work.Drive.sideGerm_add_neg_eq_one_of_refTripleEngine`
(`Submission/Work/Drive/refTripleEndpoint.lean`) consumes, besides the triple data, the germ lane's
**cross-level parity**: at a configuration which is a `GoodPair` at two different truncation levels, the
parities of the two box counts coincide.

The classical route (`Work.Drive.odd_coreSideCount_eq_of_lt_level`) goes through the *geometric* count
and therefore needs the faithfulness `hinj` of the box parameterisation, which is **not** a consequence
of `GoodPair` (`Submission/Work/Drive/GEOMETRIC_LOCALITY_STATUS.md` §9) and cannot be produced by the
design.  This file instead uses the sharper `Work.Drive.coreMeet_ncard_eq_of_lt_level`
(`Submission/Work/Drive/coreMeetLevelIndep.lean`), which gives the *equality of the counts*, hence also
the equality of their parities, with no faithfulness hypothesis at all.

* `Work.Drive.odd_CntAt_eq_of_goodAt_of_levels` — the interface statement: the level data as
  hypotheses, the two `GoodAt`s, the conclusion `Odd (CntAt c) = Odd (CntAt c')`.
* `Work.Drive.levelLoop_pertChart` / `Work.Drive.level_rotPresentation_pertChart` — the level bounds of
  the perturbed loop and of the perturbed rotated presentation, which is what the interface consumes.
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **The level of a point of the perturbed chart's loop**: the loop of the perturbed chart passes
through `Ξ t` of a point of the chart's disk. -/
lemma coreLoop_pertChart_eq {m : ℕ} (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (t : EuclideanSpace ℝ (Fin m)) (s : ℝ) :
    coreLoop (pertChart Ξ Q t) s
      = Ξ t (Q (Complex.exp (Real.pi * (s : ℂ) * Complex.I))) := rfl

/-- The disk point of the loop lies in the chart's disk. -/
lemma loopDiskPoint_mem_chartDisk (Q : ℂ → CappingSpace) (s : ℝ) :
    Q (Complex.exp (Real.pi * (s : ℂ) * Complex.I)) ∈ chartDisk Q := by
  refine ⟨Complex.exp (Real.pi * (s : ℂ) * Complex.I), ?_, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

/-- **The level bound of the perturbed loop**: if the levels of `chartDisk Q` are `> c` after the
perturbation `Ξ t`, then so are the levels of the loop of `pertChart Ξ Q t`. -/
lemma levelLoop_pertChart {m : ℕ} (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (t : EuclideanSpace ℝ (Fin m))
    (hlev : ∀ p ∈ chartDisk Q, c < levelOf (Ξ t p)) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, c < levelOf (coreLoop (pertChart Ξ Q t) s) :=
  fun s _ => hlev _ (loopDiskPoint_mem_chartDisk Q s)

/-- **The level bound of the perturbed rotated presentation**: the sweep of a rotated presentation only
sees the levels of the plane points, which are the levels of `Ξ t` on the chart's disk. -/
lemma level_rotPresentation_pertChart {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (t : EuclideanSpace ℝ (Fin m)) (a : UnitAddCircle)
    (hlev : ∀ p ∈ chartDisk Q, c < levelOf (Ξ t p)) :
    ∀ y ∈ Submission.Drive.unitBox 1, c ≤ levelOf (rotPresentation (pertChart Ξ Q t) a y) := by
  intro y hy
  have hmem : Q (sqDisk (foldBox y)) ∈ chartDisk Q := by
    refine ⟨sqDisk (foldBox y), ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_sqDisk_le_one (foldBox y) (foldBox_mem_unitBox y)
  have h1 : rotPresentation (pertChart Ξ Q t) a y
      = rotCapping a (Ξ t (Q (sqDisk (foldBox y)))) := rfl
  rw [h1, levelOf_rotCapping]
  exact le_of_lt (hlev _ hmem)

/-- **The cross-level parity of the germ count at a doubly-good configuration.**  The level data
(`hloop`, `hloop'` for the perturbed loop, `hr`, `hr'` for the perturbed rotated presentation) are the
hypotheses, and they are automatic from the chart's data
(`Work.Drive.levelLoop_pertChart`, `Work.Drive.level_rotPresentation_pertChart`); the two `GoodAt`s are
the goodness of the same configuration at the two truncation levels. -/
theorem odd_CntAt_eq_of_goodAt_of_levels {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace) (Q : ℂ → CappingSpace)
    (c c' : ℝ) (a : UnitAddCircle)
    (t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (hc : 0 < c) (hc' : 0 < c')
    (hloop : ∀ s ∈ Set.Icc (0 : ℝ) 1, c < levelOf (coreLoop (pertChart Ξ Q t.1) s))
    (hloop' : ∀ s ∈ Set.Icc (0 : ℝ) 1, c' < levelOf (coreLoop (pertChart Ξ Q t.1) s))
    (hr : ∀ y ∈ Submission.Drive.unitBox 1, c ≤ levelOf (rotPresentation (pertChart Ξ Q t.2) a y))
    (hr' : ∀ y ∈ Submission.Drive.unitBox 1, c' ≤ levelOf (rotPresentation (pertChart Ξ Q t.2) a y))
    (hg : GoodAt Ξ Q c a t) (hg' : GoodAt Ξ Q c' a t) :
    Odd (CntAt Ξ Q c a t) = Odd (CntAt Ξ Q c' a t) := by
  have hint : ∀ p ∈ coreMeet (pertChart Ξ Q t.1) c (rotPresentation (pertChart Ξ Q t.2) a),
      p.2 2 ∈ Set.Ioo (0 : ℝ) 1 := by
    intro p hp
    exact (hg.2.2.2.1 p hp).2 2
  have hint' : ∀ p ∈ coreMeet (pertChart Ξ Q t.1) c' (rotPresentation (pertChart Ξ Q t.2) a),
      p.2 2 ∈ Set.Ioo (0 : ℝ) 1 := by
    intro p hp
    exact (hg'.2.2.2.1 p hp).2 2
  have h := coreMeet_ncard_eq_of_lt_level (Q := pertChart Ξ Q t.1)
    (P := rotPresentation (pertChart Ξ Q t.2) a) (c := c) (c' := c') hc hc' hloop hloop' hr hr'
    hint hint'
  simpa only [CntAt, coreSideCount] using congrArg Odd h

/-- **The uniform level bound for small chart perturbations.**  If the level `c` lies strictly below
every level of the chart's disk, then for every parameter `t` of small enough norm the perturbed chart
`Ξ t` still has levels `> c` on the chart's disk.  (This is the level-band input of the germ lane; the
proof is the product-neighbourhood compactness argument of
`Work.Drive.exists_eps_level_lt_pertChart`, restated here so that the germ nodes need not import the
`hdense` lane.) -/
theorem exists_eps_level_lt_pertChart_fam {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q) {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (hΞ : ChartPert Q m Ξ) (c : ℝ) (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : EuclideanSpace ℝ (Fin m), ‖t‖ < ε →
      ∀ p ∈ chartDisk Q, c < levelOf (Ξ t p) := by
  have hcont : Continuous fun q : EuclideanSpace ℝ (Fin m) × CappingSpace => Ξ q.1 q.2 :=
    hΞ.2.1.continuous
  have hUopen : IsOpen {q : EuclideanSpace ℝ (Fin m) × CappingSpace | c < levelOf (Ξ q.1 q.2)} :=
    isOpen_lt continuous_const (continuous_levelOf.comp hcont)
  have hmem : ∀ p : ↥(chartDisk Q),
      (⟨0, (p : CappingSpace)⟩ : EuclideanSpace ℝ (Fin m) × CappingSpace) ∈
        {q : EuclideanSpace ℝ (Fin m) × CappingSpace | c < levelOf (Ξ q.1 q.2)} := by
    intro p
    show c < levelOf (Ξ 0 (p : CappingSpace))
    rw [hΞ.1 (p : CappingSpace)]
    exact hcbot (p : CappingSpace) p.2
  have hloc : ∀ p : ↥(chartDisk Q), ∃ ρ : ℝ, 0 < ρ ∧ ∃ W : Set CappingSpace, IsOpen W ∧
      (p : CappingSpace) ∈ W ∧
      ∀ (s : EuclideanSpace ℝ (Fin m)) (y : CappingSpace), ‖s‖ < ρ → y ∈ W →
        c < levelOf (Ξ s y) := by
    intro p
    have hUnhds : {q : EuclideanSpace ℝ (Fin m) × CappingSpace | c < levelOf (Ξ q.1 q.2)} ∈
        𝓝 (⟨0, (p : CappingSpace)⟩ : EuclideanSpace ℝ (Fin m) × CappingSpace) :=
      hUopen.mem_nhds (hmem p)
    rw [nhds_prod_eq] at hUnhds
    obtain ⟨V, hV, W, hW, hVW⟩ := Filter.mem_prod_iff.mp hUnhds
    obtain ⟨ρ, hρ, hρV⟩ := Metric.mem_nhds_iff.mp hV
    obtain ⟨W', hW'W, hW'open, hpW'⟩ := mem_nhds_iff.mp hW
    refine ⟨ρ, hρ, W', hW'open, hpW', fun s y hs hy => ?_⟩
    have hmem' : (⟨s, y⟩ : EuclideanSpace ℝ (Fin m) × CappingSpace) ∈
        {q : EuclideanSpace ℝ (Fin m) × CappingSpace | c < levelOf (Ξ q.1 q.2)} :=
      hVW ⟨hρV (by rw [Metric.mem_ball, dist_zero_right]; exact hs), hW'W hy⟩
    exact hmem'
  choose ρ hρpos W hWopen hpW hWsub using hloc
  obtain ⟨tfin, htfin⟩ :=
    (chartDisk_compact (IsSmoothChart_of_isPlaneChart hQ).continuous).elim_finite_subcover
      (fun p : ↥(chartDisk Q) => W p) (fun p => hWopen p)
      (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hpW ⟨x, hx⟩⟩)
  have hne : (tfin.image ρ).Nonempty := by
    have hx : Q (0 : ℂ) ∈ chartDisk Q := ⟨0, by rw [Metric.mem_closedBall]; simp, rfl⟩
    obtain ⟨q, hq1, -⟩ := Set.mem_iUnion₂.mp (htfin hx)
    exact ⟨ρ q, Finset.mem_image.mpr ⟨q, hq1, rfl⟩⟩
  have hminpos : 0 < (tfin.image ρ).min' hne := by
    rw [Finset.lt_min'_iff]
    intro b hb
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hb
    exact hρpos q
  refine ⟨(tfin.image ρ).min' hne, hminpos, ?_⟩
  intro s hs p hp
  obtain ⟨q, hq1, hq2⟩ := Set.mem_iUnion₂.mp (htfin hp)
  exact hWsub q s p (lt_of_lt_of_le hs (Finset.min'_le _ _ (Finset.mem_image.mpr ⟨q, hq1, rfl⟩))) hq2

end

end Work.Drive
