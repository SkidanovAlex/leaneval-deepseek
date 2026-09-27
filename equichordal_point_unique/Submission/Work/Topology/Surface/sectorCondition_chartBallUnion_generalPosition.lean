import Mathlib
import Submission.Work.SimplyConnected.ABS.sectorCondition_of_chart_balls
import Submission.Work.Topology.Surface.hasSectorBoundary_of_two_balls_crossing
import Submission.Work.SimplyConnected.ABS.RegularPieceDefs

/-!
# The sector condition at a frontier point of a finite union of chart balls in general position

Let `c ∈ atlas ℂ X` be a chart of a complex one-manifold, `a i` the centres and `ρ i > 0` the radii
of finitely many round balls whose *closed* balls lie in `c.target`, and let

`U := ⋃ i, chartBall c (a i) (ρ i)`.

Assume

* **general position**: at most two of the closed balls `closedBall (a i) (ρ i)` contain any given
  point of `ℂ` (`htwo`), and
* **no internal tangency**: at every frontier point `p` of `U`, for any two distinct indices `i ≠ j`
  whose closed balls both contain `c p`, the outward unit normals are not opposite
  (`hgood`, i.e. `(c p - a i)/ρ i ≠ -((c p - a j)/ρ j)`).

Then `U` satisfies the sector (cone) condition `Work.SimplyConnected.ABS.HasSectorBoundary U p` at
**every** frontier point `p` of `U`.

## The proof

The closed chart discs are compact, hence closed, so a frontier point `p` of `U` lies in the closed
chart disc of at least one index.  Let `T := {i | c p ∈ closedBall (a i) (ρ i)}`; by `htwo`,
`T.ncard ≤ 2`, and `T` is non-empty, so `T.ncard = 1` or `T.ncard = 2`.

* If `T = {i₀}`, the local picture at `p` is the single-ball one and
  `Work.SimplyConnected.ABS.hasSectorBoundary_iUnion_chartBall_of_unique` applies.
* If `T = {i₀, i₁}`, then near `p` the union `U` coincides with the union of the two chart balls
  `chartBall c (a i₀) (ρ i₀) ∪ chartBall c (a i₁) (ρ i₁)` (the remaining closed balls miss `c p`,
  hence are away from `p`), and `hgood` is exactly the no-internal-tangency hypothesis of
  `Work.Topology.Surface.hasSectorBoundary_of_two_balls_crossing`.  Locality of `HasSectorBoundary`
  (`hasSectorBoundary_of_inter_eq`) transports the conclusion back to `U`.
-/

open Set Metric
open scoped Topology Manifold ContDiff

noncomputable section

namespace Work.Topology.Surface

theorem sectorCondition_chartBallUnion_generalPosition {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {c : OpenPartialHomeomorph X ℂ} (hc : c ∈ atlas ℂ X) {ι : Type*} [Fintype ι] [Nonempty ι] (a : ι → ℂ) (ρ : ι → ℝ) (hρ : ∀ i, 0 < ρ i) (hsub : ∀ i, Metric.closedBall (a i) (ρ i) ⊆ c.target) (htwo : ∀ z : ℂ, ({i | z ∈ Metric.closedBall (a i) (ρ i)} : Set ι).ncard ≤ 2) (hgood : ∀ p ∈ frontier (⋃ i, Submission.chartBall c (a i) (ρ i)), ∀ i j, i ≠ j → c p ∈ Metric.closedBall (a i) (ρ i) → c p ∈ Metric.closedBall (a j) (ρ j) → (c p - a i) / ρ i ≠ -((c p - a j) / ρ j)) : ∀ p ∈ frontier (⋃ i, Submission.chartBall c (a i) (ρ i)), Work.SimplyConnected.ABS.HasSectorBoundary (⋃ i, Submission.chartBall c (a i) (ρ i)) p := by
  intro p hp
  set U : Set X := ⋃ i, Submission.chartBall c (a i) (ρ i) with hUdef
  have hUo : IsOpen U := isOpen_iUnion fun i => Submission.chartBall_isOpen c (a i) (ρ i)
  have hpU : p ∉ U := by
    rw [← hUo.interior_eq]
    exact hp.2
  have hclosed : IsClosed (⋃ i, Submission.chartClosedBall c (a i) (ρ i)) := by
    refine isClosed_iUnion_of_finite fun i => ?_
    rw [Submission.chartClosedBall_eq_image (hsub i)]
    exact ((isCompact_closedBall _ _).image_of_continuousOn
      (c.continuousOn_symm.mono (hsub i))).isClosed
  have hpsrc : p ∈ c.source := by
    have h1 : p ∈ ⋃ i, Submission.chartClosedBall c (a i) (ρ i) :=
      closure_minimal (fun x hx => by
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        exact Set.mem_iUnion.mpr ⟨i, Submission.chartBall_subset_chartClosedBall c (a i) (ρ i) hi⟩)
        hclosed hp.1
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h1
    exact Submission.chartClosedBall_subset_source c (a i) (ρ i) hi
  -- the set of indices whose closed ball contains `c p`
  set T : Set ι := {i | c p ∈ Metric.closedBall (a i) (ρ i)} with hTdef
  have hTne : T.Nonempty := by
    have h1 : p ∈ ⋃ i, Submission.chartClosedBall c (a i) (ρ i) :=
      closure_minimal (fun x hx => by
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        exact Set.mem_iUnion.mpr ⟨i, Submission.chartBall_subset_chartClosedBall c (a i) (ρ i) hi⟩)
        hclosed hp.1
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h1
    exact ⟨i, (Submission.mem_chartClosedBall.mp hi).2⟩
  have hTcard : T.ncard ≤ 2 := htwo (c p)
  have hcases : T.ncard = 1 ∨ T.ncard = 2 := by
    have hfin : T.Finite := Set.finite_univ.subset (Set.subset_univ T)
    have hpos : 0 < T.ncard := (Set.ncard_pos (s := T) hfin).mpr hTne
    omega
  rcases hcases with h1 | h2
  · -- exactly one ball through `p`
    obtain ⟨i₀, hi₀⟩ := Set.ncard_eq_one.mp h1
    have hmem : c p ∈ Metric.closedBall (a i₀) (ρ i₀) := by
      have : i₀ ∈ T := by rw [hi₀]; exact Set.mem_singleton i₀
      exact this
    have haway : ∀ i, i ≠ i₀ → c p ∉ Metric.closedBall (a i) (ρ i) := by
      intro i hi hmem'
      have : i ∈ T := hmem'
      rw [hi₀, Set.mem_singleton_iff] at this
      exact hi this
    exact Work.SimplyConnected.ABS.hasSectorBoundary_iUnion_chartBall_of_unique hc a ρ hρ hsub
      hp hmem haway
  · -- exactly two balls through `p`
    obtain ⟨i₀, i₁, hne, hT⟩ := Set.ncard_eq_two.mp h2
    have hmem₀ : c p ∈ Metric.closedBall (a i₀) (ρ i₀) := by
      have : i₀ ∈ T := by rw [hT]; exact Set.mem_insert i₀ {i₁}
      exact this
    have hmem₁ : c p ∈ Metric.closedBall (a i₁) (ρ i₁) := by
      have : i₁ ∈ T := by
        rw [hT]
        exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton i₁))
      exact this
    have haway : ∀ i, i ≠ i₀ → i ≠ i₁ → c p ∉ Metric.closedBall (a i) (ρ i) := by
      intro i hi₀' hi₁' hmem'
      have : i ∈ T := hmem'
      rw [hT, Set.mem_insert_iff, Set.mem_singleton_iff] at this
      rcases this with h | h
      · exact hi₀' h
      · exact hi₁' h
    -- the complementary neighbourhood of `p`
    set V : Set X := (⋃ i : {i // i ≠ i₀ ∧ i ≠ i₁}, Submission.chartClosedBall c (a i) (ρ i))ᶜ
      with hVdef
    have hVo : IsOpen V := by
      rw [hVdef]
      refine isOpen_compl_iff.mpr (isClosed_iUnion_of_finite fun i => ?_)
      rw [Submission.chartClosedBall_eq_image (hsub i)]
      exact ((isCompact_closedBall _ _).image_of_continuousOn
        (c.continuousOn_symm.mono (hsub i))).isClosed
    have hpV : p ∈ V := by
      rw [hVdef, Set.mem_compl_iff, Set.mem_iUnion]
      rintro ⟨i, hi⟩
      exact haway i i.2.1 i.2.2 (Submission.mem_chartClosedBall.mp hi).2
    -- `U` agrees with the two-ball union near `p`
    have heq : U ∩ V = (Submission.chartBall c (a i₀) (ρ i₀) ∪
        Submission.chartBall c (a i₁) (ρ i₁)) ∩ V := by
      ext x
      constructor
      · rintro ⟨hxU, hxV⟩
        obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxU
        have hi : i = i₀ ∨ i = i₁ := by
          by_contra hcon
          push Not at hcon
          exact hxV (Set.mem_iUnion.mpr ⟨⟨i, hcon.1, hcon.2⟩,
            Submission.chartBall_subset_chartClosedBall c (a i) (ρ i) hxi⟩)
        rcases hi with h | h
        · subst h; exact ⟨Or.inl hxi, hxV⟩
        · subst h; exact ⟨Or.inr hxi, hxV⟩
      · rintro ⟨hx, hxV⟩
        exact ⟨Set.mem_iUnion.mpr (hx.elim (fun h => ⟨i₀, h⟩) (fun h => ⟨i₁, h⟩)), hxV⟩
    -- `p` is a frontier point of the two-ball union
    have hpf : p ∈ frontier (Submission.chartBall c (a i₀) (ρ i₀) ∪
        Submission.chartBall c (a i₁) (ρ i₁)) := by
      have hclo : p ∈ closure (Submission.chartBall c (a i₀) (ρ i₀) ∪
          Submission.chartBall c (a i₁) (ρ i₁)) :=
        Work.SimplyConnected.ABS.mem_closure_of_inter_eq hVo hpV heq hp.1
      have hnb : p ∉ Submission.chartBall c (a i₀) (ρ i₀) ∪
          Submission.chartBall c (a i₁) (ρ i₁) := fun h =>
        hpU (Set.mem_iUnion.mpr (h.elim (fun h' => ⟨i₀, h'⟩) (fun h' => ⟨i₁, h'⟩)))
      rw [IsOpen.frontier_eq ((Submission.chartBall_isOpen c (a i₀) (ρ i₀)).union
        (Submission.chartBall_isOpen c (a i₁) (ρ i₁)))]
      exact ⟨hclo, hnb⟩
    -- the no-internal-tangency hypothesis at `p`
    have hcross : (c p - a i₀) / ρ i₀ ≠ -((c p - a i₁) / ρ i₁) :=
      hgood p hp i₀ i₁ hne hmem₀ hmem₁
    -- the two-ball lemma of the workspace applies (restated with the chart balls)
    have hpf' : p ∈ frontier ((c.symm '' Metric.ball (a i₀) (ρ i₀)) ∪
        (c.symm '' Metric.ball (a i₁) (ρ i₁))) := by
      simpa only [Work.SimplyConnected.ABS.chartBall_eq_image (hsub i₀),
        Work.SimplyConnected.ABS.chartBall_eq_image (hsub i₁)] using hpf
    have h2b : Work.SimplyConnected.ABS.HasSectorBoundary
        ((c.symm '' Metric.ball (a i₀) (ρ i₀)) ∪
          (c.symm '' Metric.ball (a i₁) (ρ i₁))) p :=
      hasSectorBoundary_of_two_balls_crossing c hc (c₁ := a i₀) (c₂ := a i₁)
        (ρ₁ := ρ i₀) (ρ₂ := ρ i₁) (hρ i₀) (hρ i₁) (hsub i₀) (hsub i₁)
        hpf' hmem₀ hmem₁ hcross
    refine Work.SimplyConnected.ABS.hasSectorBoundary_of_inter_eq hVo hpV heq ?_
    simpa only [Work.SimplyConnected.ABS.chartBall_eq_image (hsub i₀),
      Work.SimplyConnected.ABS.chartBall_eq_image (hsub i₁)] using h2b

end Work.Topology.Surface
