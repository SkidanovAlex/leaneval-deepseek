import Mathlib
import Submission.Work.Drive.sideGermDefs

/-!
# The `havoid` clause of the germ route with the **loop-vs-plane** disjointness

`Submission/Work/Drive/sideGerm_havoid_of_close.lean` proves the `havoid` clause of the L6 family
engines for the germ route's perturbations from the **disk-vs-disk** disjointness

> `Disjoint (chartDisk Q) (rotCapping w '' chartDisk Q)`.

That hypothesis is much stronger than what the geometry supplies: `Zc γ` (through
`Work.Drive.disjoint_range_coreLoop_rotCapping_chartDisk`,
`Submission/Work/Drive/coreLoop_disjoint_rotCapping.lean`) gives only the **loop-vs-plane** statement

> `Disjoint (Set.range (coreLoop Q)) (rotCapping w '' chartDisk Q)`,

and the parity argument consumes only *that*: the top face `x 2 = 1` of the clamped sweep *is* the
rotated plane, and it is the **core loop** which is swept and must miss it
(`SIDEGERM_SETTLEMENT.md` §1bis, `coreLoop_disjoint_rotCapping.lean`).

This file proves the loop-vs-plane version of the clause, so that the germ route's `hdisj` can be
replaced by the form derivable from `w ∈ Zc γ`:

* `Work.Drive.tubeLoop` — the tube device (reproved here with a local name so that the file is
  self-contained);
* `Work.Drive.levelOf_pertChart_loop` — the bottom face (levels stay above `c`);
* **`Work.Drive.pertChart_ne_rotCapping_loop`** — the top face, in the *parametrised* form
  `Ξ a₁ (coreLoop Q (u 1)) ≠ rotCapping w' (Ξ a₂ (Q z))` for `u ∈ unitBox 1`, `‖z‖ ≤ 1`.  The tube
  argument is run over the **compact parameter set** `unitBox 1 × closedBall 0 1`, so that *no*
  compactness of the loop's range is needed (only the disjointness hypothesis, which is about the
  range);
* **`Work.Drive.germHavoid_loop`** — the `havoid` clause itself.

Everything is `sorry`-free and axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-! ## 1. The tube device -/

/-- **The tube lemma.**  If `K` is compact and the open set `U ⊆ P × X` contains `{y₀} × K`, then a
whole neighbourhood `V` of `y₀` satisfies `V × K ⊆ U`. -/
lemma tubeLoop {P X : Type*} [TopologicalSpace P] [TopologicalSpace X] {y₀ : P} {K : Set X}
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

/-- **The radial coordinate of the capping space is continuous.** -/
lemma continuous_levelOf_loop : Continuous levelOf := by
  unfold levelOf
  exact continuous_subtype_val.comp (continuous_fst.comp cappingSpaceHomeoProj.continuous)

/-! ## 2. The bottom face: the perturbed levels stay above `c` -/

/-- **The perturbed chart's levels stay above `c`**, uniformly over a compact set. -/
lemma levelOf_pertChart_loop {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace) {Q : ℂ → CappingSpace}
    (hΞ : ChartPert Q m Ξ) {K : Set CappingSpace} (hK : IsCompact K) {c : ℝ}
    (hcK : ∀ p ∈ K, c < levelOf p) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (a : EuclideanSpace ℝ (Fin m)) (p : CappingSpace),
      ‖a‖ < ε → p ∈ K → c < levelOf (Ξ a p) := by
  have hcont : Continuous fun z : EuclideanSpace ℝ (Fin m) × CappingSpace =>
      levelOf (Ξ z.1 z.2) := continuous_levelOf_loop.comp hΞ.2.1.continuous
  have hU : IsOpen {z : EuclideanSpace ℝ (Fin m) × CappingSpace | c < levelOf (Ξ z.1 z.2)} :=
    isOpen_lt continuous_const hcont
  obtain ⟨V, hV, hVsub⟩ := tubeLoop (y₀ := (0 : EuclideanSpace ℝ (Fin m))) hK hU
    (fun p hp => by
      change c < levelOf (Ξ 0 p)
      rw [hΞ.1 p]
      exact hcK p hp)
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.mp hV
  exact ⟨ε, hε, fun a p ha hp =>
    hVsub a (hb (by simpa [Metric.mem_ball, dist_eq_norm] using ha)) p hp⟩

/-! ## 3. The top face: the perturbed loop misses the rotated perturbed disk, in parametrised form -/

/-- **The perturbed loop and the rotated perturbed disk stay apart**, in the *parametrised* form: for
small perturbations `a₁, a₂` and angles `w'` close to `w`, the loop point `Ξ a₁ (coreLoop Q (u 1))`
(`u` in the loop's box) differs from the rotated plane point `rotCapping w' (Ξ a₂ (Q z))`
(`‖z‖ ≤ 1`), whenever at the centre the loop's *range* misses the rotated chart disk.

The tube argument is run over the compact *parameter* set `unitBox 1 × closedBall 0 1`, so no
compactness of the loop's range is needed. -/
theorem pertChart_ne_rotCapping_loop {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace) {Q : ℂ → CappingSpace}
    (hΞ : ChartPert Q m Ξ) (hQc : Continuous Q) {w : UnitAddCircle}
    (hdisj : Disjoint (Set.range (coreLoop Q)) (rotCapping w '' chartDisk Q)) :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
      ∀ (a₁ a₂ : EuclideanSpace ℝ (Fin m)) (w' : UnitAddCircle),
        ‖a₁‖ < ε → ‖a₂‖ < ε → dist w' w < δ →
        ∀ (u : EuclideanSpace ℝ (Fin 2)) (z : ℂ),
          u ∈ Submission.Drive.unitBox 1 → ‖z‖ ≤ 1 →
          Ξ a₁ (coreLoop Q (u 1)) ≠ rotCapping w' (Ξ a₂ (Q z)) := by
  have hΞc : Continuous fun q : EuclideanSpace ℝ (Fin m) × CappingSpace => Ξ q.1 q.2 :=
    hΞ.2.1.continuous
  have hcore : Continuous fun u : EuclideanSpace ℝ (Fin 2) => coreLoop Q (u 1) := by
    unfold coreLoop
    exact hQc.comp (by fun_prop)
  have hrot : Continuous fun p : ((EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) ×
      UnitAddCircle) × (EuclideanSpace ℝ (Fin 2) × ℂ) =>
      (Ξ p.1.1.1 (coreLoop Q (p.2.1 1)), rotCapping p.1.2 (Ξ p.1.1.2 (Q p.2.2))) :=
    Continuous.prodMk
      (hΞc.comp (((continuous_fst.comp continuous_fst).comp continuous_fst).prodMk
        (hcore.comp (continuous_fst.comp continuous_snd))))
      (continuous_rotCapping_uncurry.comp (((continuous_snd.comp continuous_fst)).prodMk
        (hΞc.comp (((continuous_snd.comp continuous_fst).comp continuous_fst).prodMk
          (hQc.comp (continuous_snd.comp continuous_snd))))))
  have hU : IsOpen ((fun p : ((EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) ×
      UnitAddCircle) × (EuclideanSpace ℝ (Fin 2) × ℂ) =>
      (Ξ p.1.1.1 (coreLoop Q (p.2.1 1)), rotCapping p.1.2 (Ξ p.1.1.2 (Q p.2.2)))) ⁻¹'
      {u : CappingSpace × CappingSpace | u.1 ≠ u.2}) :=
    isClosed_diagonal.isOpen_compl.preimage hrot
  have hK : IsCompact (Submission.Drive.unitBox 1 ×ˢ Metric.closedBall (0 : ℂ) 1) :=
    (isCompact_unitBox 1).prod (isCompact_closedBall 0 1)
  have hmem : ∀ x ∈ Submission.Drive.unitBox 1 ×ˢ Metric.closedBall (0 : ℂ) 1,
      ((((0 : EuclideanSpace ℝ (Fin m)), (0 : EuclideanSpace ℝ (Fin m))), w), x) ∈
        ((fun p : ((EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) ×
          UnitAddCircle) × (EuclideanSpace ℝ (Fin 2) × ℂ) =>
          (Ξ p.1.1.1 (coreLoop Q (p.2.1 1)),
            rotCapping p.1.2 (Ξ p.1.1.2 (Q p.2.2)))) ⁻¹'
          {u : CappingSpace × CappingSpace | u.1 ≠ u.2}) := by
    rintro ⟨u, z⟩ ⟨hu, hz⟩
    change Ξ 0 (coreLoop Q (u 1)) ≠ rotCapping w (Ξ 0 (Q z))
    rw [hΞ.1 (coreLoop Q (u 1)), hΞ.1 (Q z)]
    refine fun h => Set.disjoint_left.mp hdisj ⟨u 1, rfl⟩ ?_
    exact ⟨Q z, ⟨z, hz, rfl⟩, h.symm⟩
  obtain ⟨V, hV, hVsub⟩ := tubeLoop hK hU hmem
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨r, r, hr, hr, ?_⟩
  intro a₁ a₂ w' h₁ h₂ hw u z hu hz
  have hy : (((a₁, a₂), w')) ∈ Metric.ball ((((0 : EuclideanSpace ℝ (Fin m)),
      (0 : EuclideanSpace ℝ (Fin m))), w)) r := by
    rw [Metric.mem_ball]
    calc dist (((a₁, a₂), w')) ((((0 : EuclideanSpace ℝ (Fin m)),
          (0 : EuclideanSpace ℝ (Fin m))), w))
        = max (max ‖a₁‖ ‖a₂‖) (dist w' w) := by simp [dist_eq_norm]
      _ < r := max_lt (max_lt h₁ h₂) hw
  exact hVsub (((a₁, a₂), w')) (hb hy) (u, z) ⟨hu, by rwa [Metric.mem_closedBall, dist_zero_right]⟩

/-! ## 4. The `havoid` clause with the loop-vs-plane disjointness -/

/-- **The `havoid` clause of the L6 engines for the germ route's perturbations, with the
loop-vs-plane disjointness.**  For a chart with the seam clause, a level `c` below the whole chart disk,
and an angle `w` at which the *core loop* of the chart misses the rotated chart disk, there are
`ε, δ > 0` such that for every perturbation `a` of norm `< ε` and every angle `w'` with
`dist w' w < δ`, the perturbed core loop never meets the clamped sweep of the rotated perturbed plane
at a parameter with radial coordinate `x 2 ∈ {0,1}`.

This is `Work.Drive.sideGerm_havoid_of_close` with the (un-derivable from `Zc γ`) disk-vs-disk
hypothesis replaced by the loop-vs-plane form supplied by
`Work.Drive.disjoint_range_coreLoop_rotCapping_chartDisk`. -/
theorem germHavoid_loop {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → Work.Drive.CappingSpace → Work.Drive.CappingSpace)
    (Q : ℂ → Work.Drive.CappingSpace)
    (c : ℝ) (hΞ : Work.Drive.ChartPert Q m Ξ) (hQ : Work.Drive.IsChartData Q) (hc : 0 < c)
    (hcbot : ∀ p ∈ Work.Drive.chartDisk Q, c < Work.Drive.levelOf p)
    (w : UnitAddCircle)
    (hdisj : Disjoint (Set.range (Work.Drive.coreLoop Q))
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
  have hQc : Continuous Q := hQ.1.continuous
  have hK : IsCompact (chartDisk Q) := chartDisk_compact hQc
  obtain ⟨ε₁, hε₁, hlev⟩ := levelOf_pertChart_loop Ξ hΞ hK hcbot
  obtain ⟨ε₂, δ₂, hε₂, hδ₂, hsep⟩ := pertChart_ne_rotCapping_loop Ξ hΞ hQc hdisj
  refine ⟨min ε₁ ε₂, δ₂, lt_min hε₁ hε₂, hδ₂, ?_⟩
  intro a w' ha hw u x hu hx heq hface
  have ha₁ : ‖a.1‖ < ε₁ := lt_of_le_of_lt (norm_fst_le a) (lt_of_lt_of_le ha (min_le_left _ _))
  have ha₁' : ‖a.1‖ < ε₂ := lt_of_le_of_lt (norm_fst_le a) (lt_of_lt_of_le ha (min_le_right _ _))
  have ha₂' : ‖a.2‖ < ε₂ := lt_of_le_of_lt (norm_snd_le a) (lt_of_lt_of_le ha (min_le_right _ _))
  have hzp : Q (Complex.exp (↑Real.pi * ((u 1 : ℝ) : ℂ) * Complex.I)) ∈ chartDisk Q :=
    ⟨_, by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_of_eq (by simp [Complex.norm_exp]), rfl⟩
  rcases hface with hx0 | hx1
  · -- bottom face: the level is `c`, while the perturbed loop is above `c`
    have hlvl : levelOf (clampedSweep c (fun t => 1 - t)
        (rotPresentation (pertChart Ξ Q a.2) w') x) = c := by
      rw [clampedSweep_face_zero c hc (fun t => 1 - t) _ (by norm_num) x hx0, levelOf_shadow]
    have heq' : (Ξ a.1 (Q (Complex.exp (↑Real.pi * ((u 1 : ℝ) : ℂ) * Complex.I))))
        = clampedSweep c (fun t => 1 - t) (rotPresentation (pertChart Ξ Q a.2) w') x := by
      rw [← heq]
      rfl
    have hgt := hlev a.1 _ ha₁ hzp
    rw [heq', hlvl] at hgt
    exact absurd hgt (lt_irrefl c)
  · -- top face: the rotated plane, which the loop misses
    have hP : (rotPresentation (pertChart Ξ Q a.2) w') (mk2 (x 0) (x 1))
        = rotCapping w' (pertChart Ξ Q a.2 (sqDisk (foldBox (mk2 (x 0) (x 1))))) := rfl
    have hx01 : (mk2 (x 0) (x 1) : EuclideanSpace ℝ (Fin 2)) ∈ Submission.Drive.unitBox 1 := by
      intro i
      fin_cases i
      · simpa [mk2_apply_zero] using hx 0
      · simpa [mk2_apply_one] using hx 1
    have hnorm : ‖sqDisk (foldBox (mk2 (x 0) (x 1)))‖ ≤ 1 :=
      norm_sqDisk_le_one _ (foldBox_mem_unitBox _)
    have hcl := clampedSweep_face_one c (fun t => 1 - t)
      (rotPresentation (pertChart Ξ Q a.2) w') (by norm_num) x hx1
    have heq' : (Ξ a.1 (Q (Complex.exp (↑Real.pi * ((u 1 : ℝ) : ℂ) * Complex.I))))
        = clampedSweep c (fun t => 1 - t) (rotPresentation (pertChart Ξ Q a.2) w') x := by
      rw [← heq]
      rfl
    rw [hcl, hP] at heq'
    exact hsep a.1 a.2 w' ha₁' ha₂' hw u
      (sqDisk (foldBox (mk2 (x 0) (x 1)))) hu hnorm heq'

end

end Work.Drive
