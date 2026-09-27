import Mathlib
import Submission.Work.Compact.Noncompact.Good
import Submission.Work.Compact.Noncompact.mem_suppS_iff_of_expansion
import Submission.Work.Compact.Noncompact.exists_suppS_compl_iUnion_balls

/-!
# Balls centred on a compact set, keeping a chain off the closed balls

Let `M` be a topological manifold modelled on `EuclideanSpace ℝ (Fin n)`, `e` a chart of `M`,
`A ⊆ e.source` compact, and `c ∈ suppS (Aᶜ) k` a singular `k`-chain supported away from `A`.

This file produces finitely many points `a i ∈ A` and radii `ρ i > 0` such that

* the Euclidean balls `ball (e (a i)) (ρ i)` lie in `e.target`;
* the open balls `ball (e (a i)) (ρ i / 2)` cover `A`;
* the preimages of the *closed* balls `closedBall (e (a i)) (ρ i / 2)` still avoid the support
  of `c`.

This is the variant of `exists_suppS_compl_iUnion_balls` in which the centres are required to lie
in `A` and in which the half radius is used for the covering balls and for the balls that must
avoid the chain.  The proof is the same covering argument: by `mem_suppS_iff_of_expansion`, `c` is
a finite sum of generators whose simplices have image in `Aᶜ`; the union `K` of those compact
images is compact and disjoint from `A`.  For `a ∈ A` pick a Euclidean radius so that the closed
ball around `e a` stays off `K` (possible because `K` is closed and `a ∉ K`) and inside
`e.target`; the open balls of half radius cover `A`, and compactness of `A` makes finitely many of
them suffice.
-/

namespace Work.Compact.Noncompact

open CategoryTheory AlgebraicTopology

noncomputable section

set_option maxHeartbeats 1000000

/-- **Balls centred on a compact set, keeping a chain off the closed balls.**

If `A ⊆ e.source` is compact and `c` is a `k`-chain supported away from `A`, then `A` is covered
by finitely many `e`-preimages of Euclidean balls `ball (e (a i)) (ρ i / 2)` centred at points
`a i ∈ A`, whose double balls `ball (e (a i)) (ρ i)` lie in `e.target` and whose closed half-balls
`closedBall (e (a i)) (ρ i / 2)` keep the support of `c` away; in particular `c` is still supported
off the union of those closed balls. -/
theorem exists_balls_rho {n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    {A : Set M} (hA : IsCompact A) (hAe : A ⊆ e.source) (k : ℕ)
    (c : Ch (TopCat.of M) k) (hc : c ∈ suppS (TopCat.of M) (Aᶜ) k) :
    ∃ (m : ℕ) (a : Fin m → M) (ρ : Fin m → ℝ),
      (∀ i, a i ∈ A) ∧ (∀ i, 0 < ρ i) ∧
      (∀ i, Metric.ball (e (a i)) (ρ i) ⊆ e.target) ∧
      A ⊆ ⋃ i, (e.source ∩ e⁻¹' Metric.ball (e (a i)) (ρ i / 2)) ∧
      c ∈ suppS (TopCat.of M)
        ((⋃ i, (e.source ∩ e⁻¹' Metric.closedBall (e (a i)) (ρ i / 2)))ᶜ) k := by
  classical
  -- Expand `c` as a finite combination of generators whose simplices avoid `A`.
  obtain ⟨T, a, hcT, hsupp⟩ := (mem_suppS_iff_of_expansion k c (Aᶜ)).mp hc
  -- `K` is the support of `c`: a compact set disjoint from `A`.
  let T' : Finset (SimplexT (TopCat.of M) k) := T.filter (fun σ => a σ ≠ 0)
  let K : Set M := ⋃ σ ∈ T', SimplexSet σ
  have hKcomp : IsCompact K := T'.isCompact_biUnion (fun σ _ => isCompact_SimplexSet σ)
  have hKsub : K ⊆ Aᶜ := by
    intro z hz
    obtain ⟨σ, hzσ⟩ := Set.mem_iUnion.mp hz
    obtain ⟨hσT, hzσ⟩ := Set.mem_iUnion.mp hzσ
    exact hsupp σ (Finset.mem_of_mem_filter σ hσT) (Finset.mem_filter.mp hσT).2 hzσ
  -- For every `a ∈ A` pick a radius whose closed half-ball stays off `K` and whose closed ball
  -- stays inside `e.target`.
  have hkey : ∀ x : A, ∃ ε : ℝ, 0 < ε ∧
      Metric.closedBall (e x.1) ε ⊆ e.target ∧
      (e.source ∩ e ⁻¹' Metric.closedBall (e x.1) (ε / 2)) ⊆ Kᶜ := by
    intro x
    have hxsrc : x.1 ∈ e.source := hAe x.2
    have hxK : x.1 ∈ Kᶜ := fun hx => hKsub hx x.2
    obtain ⟨ε₁, hε₁pos, hε₁sub⟩ :=
      exists_closedBall_subset_of_open e hxsrc hKcomp.isClosed.isOpen_compl hxK
    obtain ⟨δ, hδpos, hδsub⟩ := exists_closedBall_subset_target e hxsrc
    refine ⟨min ε₁ δ, lt_min hε₁pos hδpos, ?_, ?_⟩
    · exact (Metric.closedBall_subset_closedBall (min_le_right _ _)).trans hδsub
    · refine (Set.inter_subset_inter_right _
        (Set.preimage_mono (Metric.closedBall_subset_closedBall ?_))).trans hε₁sub
      have hpos : 0 < min ε₁ δ := lt_min hε₁pos hδpos
      linarith [min_le_left ε₁ δ]
  choose ε hεpos hεtarget hεK using hkey
  -- The corresponding open half-balls cover `A`; extract a finite subcover.
  let U : A → Set M := fun x => e.source ∩ e ⁻¹' Metric.ball (e x.1) (ε x / 2)
  have hUopen : ∀ x : A, IsOpen (U x) := fun x => e.isOpen_inter_preimage Metric.isOpen_ball
  have hcover : A ⊆ ⋃ x, U x := by
    intro z hz
    exact Set.mem_iUnion.mpr ⟨⟨z, hz⟩, hAe hz,
      Metric.mem_ball_self (half_pos (hεpos ⟨z, hz⟩))⟩
  obtain ⟨t, ht⟩ := hA.elim_finite_subcover U hUopen hcover
  refine ⟨t.card, fun i => (t.equivFin.symm i).1.1, fun i => ε ((t.equivFin.symm i).1),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro i; exact (t.equivFin.symm i).1.2
  · intro i; exact hεpos _
  · intro i
    exact Metric.ball_subset_closedBall.trans (hεtarget _)
  · intro z hz
    obtain ⟨x, hzU⟩ := Set.mem_iUnion.mp (ht hz)
    obtain ⟨hxt, hzU⟩ := Set.mem_iUnion.mp hzU
    refine Set.mem_iUnion.mpr ⟨t.equivFin ⟨x, hxt⟩, ?_⟩
    have hsym : t.equivFin.symm (t.equivFin ⟨x, hxt⟩) = ⟨x, hxt⟩ := Equiv.symm_apply_apply _ _
    simp only [hsym]
    exact hzU
  · -- `c` is supported off the union of the closed half-balls, since that union avoids `K`.
    refine (mem_suppS_iff_of_expansion k c _).mpr ⟨T, a, hcT, ?_⟩
    intro σ hσT haσ
    have hσ' : σ ∈ T' := Finset.mem_filter.mpr ⟨hσT, haσ⟩
    have hsubK : SimplexSet σ ⊆ K := by
      intro z hz
      exact Set.mem_iUnion.mpr ⟨σ, Set.mem_iUnion.mpr ⟨hσ', hz⟩⟩
    have hKsubS : K ⊆ (⋃ i, (e.source ∩
        e ⁻¹' Metric.closedBall (e ((t.equivFin.symm i).1.1))
          (ε ((t.equivFin.symm i).1) / 2)))ᶜ := by
      intro z hzK hzS
      obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hzS
      exact hεK (t.equivFin.symm i) hzi hzK
    exact Set.Subset.trans hsubK hKsubS

end

end Work.Compact.Noncompact
