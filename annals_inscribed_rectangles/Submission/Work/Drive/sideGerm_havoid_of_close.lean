import Mathlib
import Submission.Work.Drive.sideGermDefs

/-!
# The `havoid` clause of the L6 engines for the germ route's perturbations

This file proves `Work.Drive.sideGerm_havoid_of_close`, the uniform-in-the-centre version of the
geometric statement "the perturbed core loop meets neither face of the clamped radial sweep".

The two faces of `clampedSweep c ψ P` are two *different* phenomena, and each is handled separately:

* **the bottom face** (`x 2 = 0`) *is* the shadow of `P` on the level `c`
  (`Work.Drive.clampedSweep_face_zero`, `Work.Drive.levelOf_shadow`), so its level is exactly `c`;
  while the perturbed loop `Ξ a.1 ∘ coreLoop Q` lies at levels `> c`.  The latter is *not* automatic:
  `Ξ a.1` does not preserve levels, but for `a.1` near `0` it keeps the compact set
  `chartDisk Q` inside the open set `{p | c < levelOf p}` — this is
  `Work.Drive.germHavoid_levelOf_pertChart`, obtained from the compactness device
  `Work.Drive.germHavoid_tube` applied to the continuous map `(a, p) ↦ levelOf (Ξ a p)`;
* **the top face** (`x 2 = 1`) *is* the rotated perturbed plane
  (`Work.Drive.clampedSweep_face_one`), whose range is `rotCapping w' '' Ξ a.2 '' chartDisk Q`
  (`Work.Drive.range_diskPlane`); the perturbed loop lies in `Ξ a.1 '' chartDisk Q`.  The two compact
  sets are disjoint for small `(a, w')` because at the centre they are the disjoint compact sets
  `chartDisk Q` and `rotCapping w '' chartDisk Q` — this is
  `Work.Drive.germHavoid_pertChart_ne_rotCapping`, again through `Work.Drive.germHavoid_tube`.

The two uniform bounds are then combined into the single `ε` of the statement
(`‖a.1‖ ≤ ‖a‖`, `‖a.2‖ ≤ ‖a‖` for the product norm of `EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ
(Fin m)`).

The only library-level input is the tube lemma: a compact set inside an open set of a product is
contained in `V ×ˢ K` for a neighbourhood `V` of the base point — here proved from
`IsCompact.elim_nhds_subcover'`.
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-! ## 1. The compactness device -/

/-- **The tube lemma.**  If `K` is compact and the open set `U ⊆ P × X` contains `{y₀} × K`, then a
whole neighbourhood `V` of `y₀` satisfies `V × K ⊆ U`.  This is the device that turns the *pointwise*
continuity of a perturbation at the centre `y₀` into a statement *uniform* over the compact `K`, which
is the form the `ε`-`δ` conclusion of the `havoid` clause needs. -/
lemma germHavoid_tube {P X : Type*} [TopologicalSpace P] [TopologicalSpace X] {y₀ : P} {K : Set X}
    (hK : IsCompact K) {U : Set (P × X)} (hU : IsOpen U) (h : ∀ x ∈ K, (y₀, x) ∈ U) :
    ∃ V ∈ 𝓝 y₀, ∀ y ∈ V, ∀ x ∈ K, (y, x) ∈ U := by
  classical
  have key : ∀ x ∈ K, ∃ V ∈ 𝓝 y₀, ∃ W ∈ 𝓝 x, V ×ˢ W ⊆ U := by
    intro x hx
    have hmem : U ∈ 𝓝 (y₀, x) := hU.mem_nhds (h x hx)
    rw [nhds_prod_eq] at hmem
    exact Filter.mem_prod_iff.mp hmem
  choose V hV W hW hVW using key
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' W hW
  refine ⟨⋂ i ∈ (t : Set ↥K), V i.1 i.2,
    (Filter.biInter_mem t.finite_toSet).mpr (fun i _ => hV i.1 i.2), ?_⟩
  intro y hy x hx
  obtain ⟨z, hzt, hxz⟩ := Set.mem_iUnion₂.mp (ht hx)
  exact (hVW z.1 z.2) ⟨(Set.mem_iInter₂.mp hy) z hzt, hxz⟩

/-! ## 2. The radial coordinate is continuous -/

/-- **The radial coordinate of the capping space is continuous.**  It is the first coordinate of the
explicit homeomorphism `cappingSpaceHomeoProj : CappingSpace ≃ₜ (0,∞) × ℝP³`. -/
lemma germHavoid_continuous_levelOf : Continuous levelOf := by
  unfold levelOf
  exact continuous_subtype_val.comp (continuous_fst.comp cappingSpaceHomeoProj.continuous)

/-! ## 3. The bottom face: the perturbed chart's levels stay above `c` -/

/-- **The perturbed chart's levels stay above `c`.**  For a compact set `K` of the capping space whose
levels are all `> c`, the same holds for `Ξ a '' K` as long as `‖a‖` is small enough: the map
`(a, p) ↦ levelOf (Ξ a p)` is continuous and `Ξ 0 = id`, so the tube lemma
(`Work.Drive.germHavoid_tube`) applied to the open set `{levelOf (Ξ · ·) > c}` gives the uniformity
over `K`. -/
lemma germHavoid_levelOf_pertChart {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace) {Q : ℂ → CappingSpace}
    (hΞ : ChartPert Q m Ξ) {K : Set CappingSpace} (hK : IsCompact K) {c : ℝ}
    (hcK : ∀ p ∈ K, c < levelOf p) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (a : EuclideanSpace ℝ (Fin m)) (p : CappingSpace),
      ‖a‖ < ε → p ∈ K → c < levelOf (Ξ a p) := by
  have hcont : Continuous fun z : EuclideanSpace ℝ (Fin m) × CappingSpace =>
      levelOf (Ξ z.1 z.2) := germHavoid_continuous_levelOf.comp hΞ.2.1.continuous
  have hU : IsOpen {z : EuclideanSpace ℝ (Fin m) × CappingSpace | c < levelOf (Ξ z.1 z.2)} :=
    isOpen_lt continuous_const hcont
  obtain ⟨V, hV, hVsub⟩ := germHavoid_tube (y₀ := (0 : EuclideanSpace ℝ (Fin m))) hK hU
    (fun p hp => by
      change c < levelOf (Ξ 0 p)
      rw [hΞ.1 p]
      exact hcK p hp)
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.mp hV
  exact ⟨ε, hε, fun a p ha hp =>
    hVsub a (hb (by simpa [Metric.mem_ball, dist_eq_norm] using ha)) p hp⟩

/-! ## 4. The top face: the perturbed loop misses the rotated perturbed disk -/

/-- **The perturbed loop and the rotated perturbed disk stay disjoint.**  If `K` is compact and
`K ∩ rotCapping w '' K = ∅`, then for small perturbations `a₁`, `a₂` and angles `w'` close to `w`, the
sets `Ξ a₁ '' K` and `rotCapping w' '' Ξ a₂ '' K` are still disjoint — in the pointwise form needed
here: `Ξ a₁ p ≠ rotCapping w' (Ξ a₂ q)` for all `p, q ∈ K`.  The joint map
`(a₁, a₂, w', p, q) ↦ (Ξ a₁ p, rotCapping w' (Ξ a₂ q))` is continuous and lands in the (open)
complement of the diagonal at the centre, so the tube lemma over the compact `K × K` gives a
neighbourhood of the centre in the parameter space, which the metric of the parameters turns into the
`ε`-`δ` statement. -/
lemma germHavoid_pertChart_ne_rotCapping {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace) {Q : ℂ → CappingSpace}
    (hΞ : ChartPert Q m Ξ) {K : Set CappingSpace} (hK : IsCompact K) {w : UnitAddCircle}
    (hdisj : Disjoint K (rotCapping w '' K)) :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
      ∀ (a₁ a₂ : EuclideanSpace ℝ (Fin m)) (w' : UnitAddCircle),
        ‖a₁‖ < ε → ‖a₂‖ < ε → dist w' w < δ →
        ∀ p ∈ K, ∀ q ∈ K, Ξ a₁ p ≠ rotCapping w' (Ξ a₂ q) := by
  classical
  have hΞc : Continuous fun q : EuclideanSpace ℝ (Fin m) × CappingSpace => Ξ q.1 q.2 :=
    hΞ.2.1.continuous
  have hcont : Continuous fun z : ((EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × UnitAddCircle)
      × (CappingSpace × CappingSpace) =>
      (Ξ z.1.1.1 z.2.1, rotCapping z.1.2 (Ξ z.1.1.2 z.2.2)) :=
    Continuous.prodMk
      (hΞc.comp (((continuous_fst.comp continuous_fst).comp continuous_fst).prodMk
        (continuous_fst.comp continuous_snd)))
      (continuous_rotCapping_uncurry.comp ((continuous_snd.comp continuous_fst).prodMk
        (hΞc.comp (((continuous_snd.comp continuous_fst).comp continuous_fst).prodMk
          (continuous_snd.comp continuous_snd)))))
  have hU : IsOpen ((fun z : ((EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × UnitAddCircle)
      × (CappingSpace × CappingSpace) =>
        (Ξ z.1.1.1 z.2.1, rotCapping z.1.2 (Ξ z.1.1.2 z.2.2))) ⁻¹'
        {u : CappingSpace × CappingSpace | u.1 ≠ u.2}) :=
    isClosed_diagonal.isOpen_compl.preimage hcont
  have hmem : ∀ x ∈ K ×ˢ K,
      ((((0 : EuclideanSpace ℝ (Fin m)), (0 : EuclideanSpace ℝ (Fin m))), w), x) ∈
        ((fun z : ((EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × UnitAddCircle)
          × (CappingSpace × CappingSpace) =>
          (Ξ z.1.1.1 z.2.1, rotCapping z.1.2 (Ξ z.1.1.2 z.2.2))) ⁻¹'
          {u : CappingSpace × CappingSpace | u.1 ≠ u.2}) := by
    rintro ⟨p, q⟩ ⟨hp, hq⟩
    change Ξ 0 p ≠ rotCapping w (Ξ 0 q)
    rw [hΞ.1 p, hΞ.1 q]
    exact fun h => Set.disjoint_left.mp hdisj hp ⟨q, hq, h.symm⟩
  obtain ⟨V, hV, hVsub⟩ := germHavoid_tube (hK.prod hK) hU hmem
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨r, r, hr, hr, ?_⟩
  intro a₁ a₂ w' h₁ h₂ hw p hp q hq
  have hy : (((a₁, a₂), w')) ∈ Metric.ball ((((0 : EuclideanSpace ℝ (Fin m)),
      (0 : EuclideanSpace ℝ (Fin m))), w)) r := by
    rw [Metric.mem_ball]
    calc dist (((a₁, a₂), w')) ((((0 : EuclideanSpace ℝ (Fin m)),
          (0 : EuclideanSpace ℝ (Fin m))), w))
        = max (max ‖a₁‖ ‖a₂‖) (dist w' w) := by simp [dist_eq_norm]
      _ < r := max_lt (max_lt h₁ h₂) hw
  exact hVsub (((a₁, a₂), w')) (hb hy) (p, q) ⟨hp, hq⟩

/-! ## 5. The `havoid` clause -/

/-- **The `havoid` clause of the L6 engines for the germ route's perturbations, uniformly near the
centre.**  For a chart `Q` with the seam clause (`IsChartData`), a level `c` below the whole chart disk
(`hcbot`) and an angle `w` at which the chart's disk is disjoint from its rotation (`hdisj`), there are
`ε, δ > 0` such that for **every** perturbation `a = (a.1, a.2)` of norm `< ε` and every angle `w'`
with `dist w' w < δ`, the perturbed core loop `coreLoop (pertChart Ξ Q a.1) = Ξ a.1 ∘ coreLoop Q`
never meets the clamped sweep of the rotated perturbed plane
`clampedSweep c (fun t => 1 - t) (rotPresentation (pertChart Ξ Q a.2) w')` at a parameter with radial
coordinate `x 2 ∈ {0,1}` — i.e. the loop meets neither the *bottom face* (the level `c`) nor the *top
face* (the rotated plane) of the sweep.

Proof plan.  `x 2 = 0` forces the meet to be at level `c` (`Work.Drive.clampedSweep_face_zero` +
`Work.Drive.levelOf_shadow`), while the perturbed loop stays at levels `> c` (compactness of
`chartDisk Q`, `levelOf_pos`, `hcbot` and the joint continuity of `Ξ` with `Ξ 0 = id`); `x 2 = 1`
forces the meet to be in the rotated *disk* `rotCapping w' '' Ξ a.2 '' chartDisk Q`
(`Work.Drive.clampedSweep_face_one` + `Work.Drive.range_diskPlane`) while the perturbed loop lies in
`Ξ a.1 '' chartDisk Q`, and those two compact sets are disjoint for small `(a, w')` by `hdisj`
(`chartDisk_compact`, `chartDisk_disjoint_nhds`, the joint continuity of `Ξ`). -/
theorem sideGerm_havoid_of_close {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → Work.Drive.CappingSpace → Work.Drive.CappingSpace)
    (Q : ℂ → Work.Drive.CappingSpace)
    (c : ℝ) (hΞ : Work.Drive.ChartPert Q m Ξ) (hQ : Work.Drive.IsChartData Q) (hc : 0 < c)
    (hcbot : ∀ p ∈ Work.Drive.chartDisk Q, c < Work.Drive.levelOf p)
    (w : UnitAddCircle)
    (hdisj : Disjoint (Work.Drive.chartDisk Q)
      (Work.Drive.rotCapping w '' Work.Drive.chartDisk Q)) :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
      ∀ (a : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (w' : UnitAddCircle),
        ‖a‖ < ε → dist w' w < δ →
        ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
          u ∈ Submission.Drive.unitBox 1 → x ∈ Submission.Drive.unitBox 2 →
          Work.Drive.coreLoop (Work.Drive.pertChart Ξ Q a.1) (u 1)
            = Work.Drive.clampedSweep c (fun t => 1 - t)
                (Work.Drive.rotPresentation (Work.Drive.pertChart Ξ Q a.2) w') x →
          (x 2 = 0 ∨ x 2 = 1) → False := by
  classical
  have hQcont : Continuous Q := hQ.1.continuous
  have hK : IsCompact (chartDisk Q) := chartDisk_compact hQcont
  obtain ⟨ε₁, hε₁, hlev⟩ := germHavoid_levelOf_pertChart Ξ hΞ hK hcbot
  obtain ⟨ε₂, δ₂, hε₂, hδ₂, hsep⟩ := germHavoid_pertChart_ne_rotCapping Ξ hΞ hK hdisj
  refine ⟨min ε₁ ε₂, δ₂, lt_min hε₁ hε₂, hδ₂, ?_⟩
  intro a w' ha hw u x hu hx heq hface
  -- `‖a‖` dominates both coordinates of the product `EuclideanSpace ℝ (Fin m) × _`
  have ha₁ : ‖a.1‖ < ε₁ := lt_of_le_of_lt (norm_fst_le a) (lt_of_lt_of_le ha (min_le_left _ _))
  have ha₁' : ‖a.1‖ < ε₂ := lt_of_le_of_lt (norm_fst_le a) (lt_of_lt_of_le ha (min_le_right _ _))
  have ha₂' : ‖a.2‖ < ε₂ := lt_of_le_of_lt (norm_snd_le a) (lt_of_lt_of_le ha (min_le_right _ _))
  -- the loop's point lies in the chart's disk: `‖exp (iπt)‖ = 1`
  have hzp : Q (Complex.exp (↑Real.pi * ((u 1 : ℝ) : ℂ) * Complex.I)) ∈ chartDisk Q :=
    ⟨_, by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_of_eq (by simp [Complex.norm_exp]), rfl⟩
  rcases hface with hx0 | hx1
  · -- bottom face: the level is `c`, while the perturbed loop is above `c`
    have hlvl : levelOf (clampedSweep c (fun t => 1 - t) (rotPresentation (pertChart Ξ Q a.2) w') x)
        = c := by
      rw [clampedSweep_face_zero c hc (fun t => 1 - t) _ (by norm_num) x hx0, levelOf_shadow]
    have hgt : c < levelOf (coreLoop (pertChart Ξ Q a.1) (u 1)) := hlev a.1 _ ha₁ hzp
    rw [heq, hlvl] at hgt
    exact absurd hgt (lt_irrefl c)
  · -- top face: the sweep is the rotated perturbed plane, disjoint from the perturbed loop
    have htop : clampedSweep c (fun t => 1 - t) (rotPresentation (pertChart Ξ Q a.2) w') x
        = rotCapping w' (Ξ a.2 (Q (sqDisk (foldBox (mk2 (x 0) (x 1)))))) := by
      rw [clampedSweep_face_one c (fun t => 1 - t) _ (by norm_num) x hx1]
      simp only [rotPresentation, diskPlane, pertChart]
    have hzq : Q (sqDisk (foldBox (mk2 (x 0) (x 1)))) ∈ chartDisk Q :=
      ⟨_, by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact norm_sqDisk_le_one _ (foldBox_mem_unitBox _), rfl⟩
    exact hsep a.1 a.2 w' ha₁' ha₂' hw _ hzp _ hzq (heq.trans htop)

end

end Work.Drive
