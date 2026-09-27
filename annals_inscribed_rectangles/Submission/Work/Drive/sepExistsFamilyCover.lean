import Mathlib
import Submission.Work.Drive.sepFamDefs

/-!
# The chart cover of the meet set of a continuous family

`Work.Drive.SepFamilyCover Lf N` is the finite chart cover of the meet set at the shift `0` of the
five-box family `(famLoop (Lf ·), famChain (N ·))`: finitely many chart centres `p i`, compact pieces
`K i` containing the meets in their interior, open neighbourhoods `V i ⊇ K i` on which *both* values
of the family lie in the source of the chart at `p i` (uniformly over a parameter ball of radius
`ε₀ > 0`).

This file proves that such a cover always exists as soon as the family is continuous
(`Work.Drive.SepFamContinuous`), which is the standing hypothesis of every Sard/regularity brick of
the germ/parity route:

* `continuous_famLoop_fam`, `continuous_famChain_fam` — joint continuity of the two sides of the
  five-box family, from continuity of `Lf` resp. `N` (the box is reparametrised by the tautological
  maps `y ↦ mk2 (y 0) (y 1)` and `y ↦ famPt (y 0) (famT3 (y 2) (y 3) (y 4))`);
* `exists_local_chart_data` — at a meet `y` the two values coincide, so they both lie in the source
  of the chart at the common value; by joint continuity this persists on a product of balls
  `‖τ‖ < ε`, `y' ∈ ball y ρ`;
* `sepExistsFamilyCover` — the meet set is compact (`unitBox 4` is compact and the meet condition is
  closed because `CappingSpace` is a Hausdorff space), the local balls `ball y (ρ/4)` cover it, and
  a finite subcover (enumerated by `Finset.equivFin`) gives the family with the compact pieces
  `closedBall y (ρ/2)` and the openings `ball y ρ`.
-/

namespace Work.Drive

open scoped Topology Manifold ContDiff
open Set Filter

set_option warn.classDefReducibility false

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **Joint continuity of the loop side of the five-box family.** -/
lemma continuous_famLoop_fam {m : ℕ}
    {Lf : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 2) → CappingSpace}
    (h : Continuous fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) => Lf q.1 q.2) :
    Continuous fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => famLoop (Lf q.1) q.2 := by
  have hmk : Continuous fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => mk2 (q.2 0) (q.2 1) := by
    simp only [mk2]
    exact (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp (by fun_prop)
  have := h.comp (continuous_fst.prodMk hmk)
  simpa only [famLoop, Function.comp_def] using this

/-- **Joint continuity of the chain side of the five-box family.** -/
lemma continuous_famChain_fam {m : ℕ}
    {N : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 4) → CappingSpace}
    (h : Continuous fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4) => N q.1 q.2) :
    Continuous fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => famChain (N q.1) q.2 := by
  have hpt : Continuous fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
      famPt (q.2 0) (famT3 (q.2 2) (q.2 3) (q.2 4)) := by
    simp only [famPt, famT3, WithLp.ofLp_toLp]
    exact (PiLp.continuous_toLp 2 (fun _ : Fin 4 => ℝ)).comp (by fun_prop)
  have := h.comp (continuous_fst.prodMk hpt)
  simpa only [famChain, Function.comp_def] using this

/-- **The local chart datum of a meet.**  At a point `y₀` where the two sides of the family meet at
the shift `0`, there is a chart `p` (the chart at the common value) and radii `ε, ρ > 0` such that
for every parameter `τ` with `‖τ‖ < ε` and every `y ∈ ball y₀ ρ` both values of the family lie in the
source of `p`. -/
lemma exists_local_chart_data {m : ℕ}
    {Lf : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 2) → CappingSpace}
    {N : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 4) → CappingSpace}
    (hc : SepFamContinuous Lf N) (y₀ : Amb 4)
    (hy : famLoop (Lf 0) y₀ = famChain (N 0) y₀) :
    ∃ (p : CappingSpace) (ε ρ : ℝ), 0 < ε ∧ 0 < ρ ∧
      ∀ (τ : EuclideanSpace ℝ (Fin m)) (y : Amb 4), ‖τ‖ < ε → y ∈ Metric.ball y₀ ρ →
        famLoop (Lf τ) y ∈ (chr p).source ∧ famChain (N τ) y ∈ (chr p).source := by
  have hA0 : famLoop (Lf 0) y₀ ∈ (chr (famLoop (Lf 0) y₀)).source := mem_chart_source _ _
  have hB0 : famChain (N 0) y₀ ∈ (chr (famLoop (Lf 0) y₀)).source := by rw [← hy]; exact hA0
  have hAo : IsOpen {q : EuclideanSpace ℝ (Fin m) × Amb 4 |
      famLoop (Lf q.1) q.2 ∈ (chr (famLoop (Lf 0) y₀)).source} :=
    (continuous_famLoop_fam hc.1).isOpen_preimage _ (chr _).open_source
  have hBo : IsOpen {q : EuclideanSpace ℝ (Fin m) × Amb 4 |
      famChain (N q.1) q.2 ∈ (chr (famLoop (Lf 0) y₀)).source} :=
    (continuous_famChain_fam hc.2).isOpen_preimage _ (chr _).open_source
  have hmem : ({q : EuclideanSpace ℝ (Fin m) × Amb 4 |
        famLoop (Lf q.1) q.2 ∈ (chr (famLoop (Lf 0) y₀)).source} ∩
      {q : EuclideanSpace ℝ (Fin m) × Amb 4 |
        famChain (N q.1) q.2 ∈ (chr (famLoop (Lf 0) y₀)).source})
      ∈ 𝓝 ((0 : EuclideanSpace ℝ (Fin m)), y₀) :=
    Filter.inter_mem (hAo.mem_nhds hA0) (hBo.mem_nhds hB0)
  rw [nhds_prod_eq, Filter.mem_prod_iff] at hmem
  obtain ⟨U₁, hU₁, U₂, hU₂, hsub⟩ := hmem
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hU₁
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp hU₂
  refine ⟨famLoop (Lf 0) y₀, ε, ρ, hε, hρ, ?_⟩
  intro τ y hτ hy'
  have h1 : τ ∈ U₁ := hεsub (by simpa [Metric.mem_ball, dist_zero_right] using hτ)
  have h2 : y ∈ U₂ := hρsub (by simpa [Metric.mem_ball] using hy')
  exact hsub (Set.mk_mem_prod h1 h2)

/-- **The chart cover of the meet set exists for every continuous family.**  The meet set of the
five-box family at the shift `0` inside the unit box is compact; covering it by the local balls of
`exists_local_chart_data` and passing to a finite subcover (enumerated by `Finset.equivFin`) produces
the finite chart family of `Work.Drive.SepFamilyCover`. -/
theorem sepExistsFamilyCover {m : ℕ}
    (Lf : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (N : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 4) → Work.Drive.CappingSpace)
    (hc : Work.Drive.SepFamContinuous Lf N) :
    Nonempty (Work.Drive.SepFamilyCover Lf N) := by
  classical
  let S : Set (Amb 4) := {y | y ∈ Submission.Drive.unitBox 4 ∧
      famLoop (Lf 0) y = famChain (N 0) y}
  have hSclosed : IsClosed S := by
    have h1 : IsClosed {y : Amb 4 | famLoop (Lf 0) y = famChain (N 0) y} :=
      isClosed_eq ((continuous_famLoop_fam hc.1).comp (by fun_prop : Continuous fun y : Amb 4 =>
          ((0 : EuclideanSpace ℝ (Fin m)), y)))
        ((continuous_famChain_fam hc.2).comp (by fun_prop : Continuous fun y : Amb 4 =>
          ((0 : EuclideanSpace ℝ (Fin m)), y)))
    exact (isClosed_unitBox 4).inter h1
  have hScomp : IsCompact S :=
    (isCompact_unitBox 4).of_isClosed_subset hSclosed (fun y hy => hy.1)
  have hdata : ∀ y : S, ∃ (p : CappingSpace) (ε ρ : ℝ), 0 < ε ∧ 0 < ρ ∧
      ∀ (τ : EuclideanSpace ℝ (Fin m)) (z : Amb 4), ‖τ‖ < ε → z ∈ Metric.ball (y : Amb 4) ρ →
        famLoop (Lf τ) z ∈ (chr p).source ∧ famChain (N τ) z ∈ (chr p).source :=
    fun y => exists_local_chart_data hc (y : Amb 4) y.2.2
  choose pd ed rd hd using hdata
  have hcover : S ⊆ ⋃ y : S, Metric.ball (y : Amb 4) (rd y / 4) := by
    intro y hy
    refine Set.mem_iUnion.mpr ⟨⟨y, hy⟩, Metric.mem_ball_self ?_⟩
    have := (hd ⟨y, hy⟩).2.1
    linarith
  obtain ⟨t, ht⟩ := hScomp.elim_finite_subcover
    (fun y : S => Metric.ball (y : Amb 4) (rd y / 4)) (fun _ => Metric.isOpen_ball) hcover
  let yt : Fin t.card → S := fun i => (t.equivFin.symm i).1
  let ε₀ : ℝ := ((Finset.univ : Finset (Fin t.card)).image (fun i => ed (yt i)) ∪ {1}).min' ⟨1, by simp⟩
  have hε₀pos : 0 < ε₀ := by
    have hm : ε₀ ∈ ((Finset.univ : Finset (Fin t.card)).image (fun i => ed (yt i)) ∪ {1}) :=
      Finset.min'_mem _ _
    rcases Finset.mem_union.mp hm with hm | hm
    · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hm
      rw [← hi]
      exact (hd (yt i)).1
    · rw [Finset.mem_singleton.mp hm]
      norm_num
  have hle : ∀ i : Fin t.card, ε₀ ≤ ed (yt i) := by
    intro i
    exact Finset.min'_le _ _ (Finset.mem_union_left _
      (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  refine ⟨{ r := t.card
            p := fun i => pd (yt i)
            K := fun i => Metric.closedBall (yt i : Amb 4) (rd (yt i) / 2)
            V := fun i => Metric.ball (yt i : Amb 4) (rd (yt i))
            ε₀ := ε₀
            hε₀ := hε₀pos
            hK := fun i => isCompact_closedBall _ _
            hV := fun i => Metric.isOpen_ball
            hKV := fun i => Metric.closedBall_subset_ball (by have := (hd (yt i)).2.1; linarith)
            hchart := by
              intro i τ y hτ hy
              exact (hd (yt i)).2.2 τ y (lt_of_lt_of_le hτ (hle i)) hy
            hbase := by
              intro y hybox hymeet
              have hyS : y ∈ S := ⟨hybox, hymeet⟩
              obtain ⟨i₀, hm⟩ := Set.mem_iUnion.mp (ht hyS)
              obtain ⟨hi₀, hball⟩ := Set.mem_iUnion.mp hm
              refine Set.mem_iUnion.mpr ⟨t.equivFin ⟨i₀, hi₀⟩, ?_⟩
              have hyt : yt (t.equivFin ⟨i₀, hi₀⟩) = (⟨i₀, hi₀⟩ : ↥t).1 := by
                simp only [yt, Equiv.symm_apply_apply]
              rw [hyt]
              exact (interior_maximal
                ((Metric.ball_subset_ball (by have := (hd i₀).2.1; linarith)).trans
                  Metric.ball_subset_closedBall) Metric.isOpen_ball) hball }⟩

end

end Work.Drive
