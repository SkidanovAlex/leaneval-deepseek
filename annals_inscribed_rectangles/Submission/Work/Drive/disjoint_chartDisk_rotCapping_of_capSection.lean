import Mathlib
import Submission.Work.Drive.isPlaneChart_seam_mem_stripImage
import Submission.Work.Drive.capSection
import Submission.Work.Drive.classDatum
import Submission.Work.Drive.cappedPlaneFamily
import Submission.Work.Drive.planeChain

/-!
# `chartDisk Q` is disjoint from its rotations, from the cap section

The chart's disk `chartDisk Q = Q '' closedBall 0 1` splits along the radius `1/2`:

* `‖z‖ < 1/2` — the value `Q z` is a point of the **cap interior** (`Work.Drive.capInterior`): the
  cap clause of `IsPlaneChart` exhibits a cap representative `c` and the hypothesis `hnh` bounds its
  disk coordinate by `< 1`;
* `1/2 ≤ ‖z‖ ≤ 1` — the value `Q z` is a point of the **configuration strip**
  `Work.Drive.stripImage μ`: on the annulus `1/2 < ‖z‖` this is the strip clause, on the seam circle
  `‖z‖ = 1/2` it is the proved `Work.Drive.isPlaneChart_seam_mem_stripImage`.

The rotation `rotCapping w` preserves both pieces' *kind*: it moves the doubled direction on the
configuration side (so it maps `stripImage μ` to the strip `rotCapping w '' stripImage μ`) and the
cap angle on the cap side, hence preserves `capInterior`.  Consequently the three disjointness facts

* `Disjoint (stripImage μ) (rotCapping w '' stripImage μ)` for `w ∈ Zc γ` (proved;
  `Work.Drive.disjoint_stripImage_rot`),
* `Disjoint (stripImage μ) capInterior` (proved; `Work.Drive.disjoint_stripImage_capInterior`),
* `CapSection Q` (the hypothesis on the chart),

give the case analysis: both points in the strip (cases "both `≥ 1/2`"), one in the cap interior and
the other in the strip (mixed cases), or both in the cap interior — and the last case is exactly what
`CapSection` forbids, since `0 ∉ Zc γ` (`Work.Drive.zero_notMem_Zc`).
-/

namespace Work.Drive

open Manifold Filter
open scoped Manifold ContDiff Topology
open Submission.Configuration (muOrd)

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted

noncomputable section

/-! ## The rotation preserves the cap interior -/

/-- The rotation of a cap piece does not change its disk coordinate. -/
lemma rotCap_thd (a : UnitAddCircle) (q : CapPiece) : (rotCap a q).1.2.2 = q.1.2.2 := rfl

/-- **The rotation maps the cap interior into itself.**  On the cap piece `rotCapping a` is the
rotation of the cap angle, so it preserves the norm of the disk coordinate. -/
lemma capInterior_subset_rotCapping (a : UnitAddCircle) :
    rotCapping a '' capInterior ⊆ capInterior := by
  rintro p ⟨q, hq, rfl⟩
  obtain ⟨q', hq', rfl⟩ := hq
  exact ⟨rotCap a q', by rwa [rotCap_thd],
    by rw [rotCapping_mk, rotSum_inr]⟩

/-! ## The two pieces of the chart's disk -/

/-- **The strictly inner disk of a plane chart lies in the cap interior.**  The cap clause of
`IsPlaneChart` gives a cap representative `c` of `Q z`, whose disk coordinate is bounded by `< 1` by
the hypothesis `hnh`. -/
lemma mem_capInterior_of_norm_lt_half {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q)
    (hnh : ∀ z : ℂ, ‖z‖ < 1 / 2 → ∀ c : CapPiece,
      Q z = Quotient.mk'' (Sum.inr c) → ‖c.1.2.2‖ < 1)
    {z : ℂ} (hz : ‖z‖ < 1 / 2) : Q z ∈ capInterior := by
  obtain ⟨c, hc⟩ := hQ.2.2.2 z hz
  exact ⟨c, hnh z hz c hc, hc⟩

/-- **The chart's value off the inner disk lies in the configuration strip `μ`.**  For
`1/2 ≤ ‖z‖ ≤ 1`: on the open annulus `1/2 < ‖z‖` the strip clause of `IsPlaneChart` writes `Q z` as
the chord of the parameters `arg z ± s` with `s = √(π²(‖z‖ - 1/2)/2) > 0`, so the parameters are
distinct (`Circle.exp` is injective on an interval of length `2s ≤ π < 2π`) and `μ` agrees with the
honest band `muOrd γ` there; on the seam circle `‖z‖ = 1/2` the value is the tangent chord, which is
`Work.Drive.isPlaneChart_seam_mem_stripImage`. -/
lemma mem_stripImage_of_half_le {γ : Circle → ℝ × ℝ}
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {hγne : ∀ x : Circle, γ x ≠ 0} {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q)
    {μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ}
    (hμne : ∀ x y : Circle, x ≠ y → μ (x, y) = muOrd γ (x, y))
    (hμdiag : ∀ x : Circle, μ (x, x) = (γ x, tangentDirC γ x, 0))
    {z : ℂ} (hz : 1 / 2 ≤ ‖z‖) (hz1 : ‖z‖ ≤ 1) : Q z ∈ stripImage μ := by
  rcases lt_or_eq_of_le hz with hlt | heq
  · -- the open annulus: the strip clause, at the two distinct parameters `arg z ± s`
    set a : ℝ := Complex.arg z with ha
    set s : ℝ := Real.sqrt (Real.pi ^ 2 * (‖z‖ - 1 / 2) / 2) with hs
    have hspos : 0 < s := by
      rw [hs]
      apply Real.sqrt_pos.mpr
      have h1 : 0 < ‖z‖ - 1 / 2 := by linarith
      have h2 : 0 < Real.pi ^ 2 := by positivity
      have h3 : 0 < Real.pi ^ 2 * (‖z‖ - 1 / 2) := mul_pos h2 h1
      linarith
    have hsle : s ≤ Real.pi / 2 := by
      rw [hs]
      calc Real.sqrt (Real.pi ^ 2 * (‖z‖ - 1 / 2) / 2)
          ≤ Real.sqrt ((Real.pi / 2) ^ 2) := by
            apply Real.sqrt_le_sqrt
            have h1 : ‖z‖ - 1 / 2 ≤ 1 / 2 := by linarith
            have hpi : 0 < Real.pi := Real.pi_pos
            nlinarith
        _ = Real.pi / 2 := Real.sqrt_sq (by positivity)
    -- the two parameters differ
    have hexp : Circle.exp (a + s) ≠ Circle.exp (a - s) := by
      intro hcon
      have hInj : Set.InjOn Circle.exp (Set.Icc (a - s) (a + s)) :=
        Circle.exp_injOn_Icc (by have hpi : 0 < Real.pi := Real.pi_pos; linarith)
      have h := hInj (by refine ⟨by linarith, by linarith⟩)
        (by refine ⟨by linarith, by linarith⟩) hcon
      linarith
    have hstrip := hQ.2.1 z hlt hz1
    rw [mem_stripImage_iff]
    have h1 : 0 < (confOf (μ (Circle.exp (a + s), Circle.exp (a - s)))).1 := by
      rw [hμne _ _ hexp]
      exact stripData_pos hγne (mk2 (a + s) (a - s))
    have h2 : ‖(confOf (μ (Circle.exp (a + s), Circle.exp (a - s)))).2.1‖ ≤ 1 := by
      rw [hμne _ _ hexp]
      exact confOf_snd_norm_le_one _
    refine ⟨(Circle.exp (a + s), Circle.exp (a - s)), h1, h2, ?_⟩
    rw [hstrip, stripChart_zero_eq_seam]
    rw [show seamConfPt γ hγne (mk2 (a + s) (a - s))
        = confPiece (μ (Circle.exp (a + s), Circle.exp (a - s))) h1 h2 from
      Subtype.ext (by
        rw [seamConfPt_val, confPiece_val, mk2_apply_zero, mk2_apply_one]
        exact congrArg confOf (hμne _ _ hexp).symm)]
  · -- the seam circle: the tangent chord
    exact isPlaneChart_seam_mem_stripImage hγ hQ hμdiag heq.symm

/-! ## The disjointness -/

/-- **The chart's disk and its rotation are disjoint for `w ∈ Zc γ`.**  A common point
`Q z = rotCapping w (Q z')`, `‖z‖, ‖z'‖ ≤ 1`, is impossible: each of `z, z'` is either strictly
inside the disk `‖·‖ < 1/2` (so the value is a cap-interior point) or not (so the value is a strip
point), and the three cases of the resulting classification (cap/cap, cap/strip, strip/strip) are
respectively forbidden by `CapSection` and `0 ∉ Zc γ`, by
`Disjoint (stripImage μ) capInterior`, and by `Disjoint (stripImage μ) (rotCapping w '' stripImage μ)`. -/
theorem disjoint_chartDisk_rotCapping_of_capSection {γ : Circle → ℝ × ℝ}
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {hγne : ∀ x : Circle, γ x ≠ 0} {Q : ℂ → Work.Drive.CappingSpace}
    (hQ : Work.Drive.IsPlaneChart γ hγne Q)
    {μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ}
    (hμne : ∀ x y : Circle, x ≠ y → μ (x, y) = Submission.Configuration.muOrd γ (x, y))
    (hμdiag : ∀ x : Circle, μ (x, x) = (γ x, Work.Drive.tangentDirC γ x, 0))
    (hcap : Work.Drive.CapSection Q)
    (hnh : ∀ z : ℂ, ‖z‖ < 1 / 2 → ∀ c : Work.Drive.CapPiece,
      Q z = Quotient.mk'' (Sum.inr c) → ‖c.1.2.2‖ < 1)
    {w : UnitAddCircle} (hw : w ∈ Work.Drive.Zc γ) :
    Disjoint (Work.Drive.chartDisk Q) (Work.Drive.rotCapping w '' Work.Drive.chartDisk Q) := by
  have hM : ∀ {u : ℂ}, 1 / 2 ≤ ‖u‖ → ‖u‖ ≤ 1 → Q u ∈ stripImage μ :=
    fun hu hu1 => mem_stripImage_of_half_le hγ hQ hμne hμdiag hu hu1
  have hC : ∀ {u : ℂ}, ‖u‖ < 1 / 2 → Q u ∈ capInterior :=
    fun hu => mem_capInterior_of_norm_lt_half hQ hnh hu
  rw [chartDisk, Set.disjoint_left]
  rintro p ⟨z, hz, hp⟩ ⟨t, ⟨z', hz', ht⟩, hsp⟩
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hz hz'
  subst hp
  subst ht
  -- now `hsp : rotCapping w (Q z') = Q z`
  by_cases hz1 : ‖z‖ < 1 / 2
  · by_cases hz2 : ‖z'‖ < 1 / 2
    · -- both in the cap interior: `CapSection` forces `w = 0`
      exact zero_notMem_Zc γ ((hcap z z' w hz1.le hz2.le hsp.symm) ▸ hw)
    · -- `z` cap interior, `z'` strip: rotate back by `-w` and use `stripImage ∩ capInterior = ∅`
      have hz'strip : Q z' ∈ stripImage μ := hM (le_of_not_gt hz2) hz'
      have hback : rotCapping (-w) (Q z) = Q z' := by
        rw [← hsp, rotCapping_apply_add, neg_add_cancel, rotCapping_zero]
        rfl
      have hmem : rotCapping (-w) (Q z) ∈ stripImage μ := by rw [hback]; exact hz'strip
      have hmem' : rotCapping (-w) (Q z) ∈ capInterior :=
        capInterior_subset_rotCapping (-w) ⟨Q z, hC hz1, rfl⟩
      exact Set.disjoint_left.mp (disjoint_stripImage_capInterior μ) hmem hmem'
  · -- `z` strip
    have hzstrip : Q z ∈ stripImage μ := hM (le_of_not_gt hz1) hz
    by_cases hz2 : ‖z'‖ < 1 / 2
    · -- `z'` cap interior: its rotation is still in the cap interior
      have hc : Q z ∈ capInterior := by
        rw [← hsp]
        exact capInterior_subset_rotCapping w ⟨Q z', hC hz2, rfl⟩
      exact Set.disjoint_left.mp (disjoint_stripImage_capInterior μ) hzstrip hc
    · -- both strip points
      have hz'strip : Q z' ∈ stripImage μ := hM (le_of_not_gt hz2) hz'
      exact Set.disjoint_left.mp (disjoint_stripImage_rot hγ hμne hμdiag hw) hzstrip
        ⟨Q z', hz'strip, hsp⟩

end

end Work.Drive
