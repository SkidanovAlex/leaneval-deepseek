import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.MetricSpace.HausdorffDistance

set_option linter.style.haveILetI false

open Set Metric
open scoped Topology

namespace Commons.Topology.Jordan

/-- In a compact Hausdorff space, if the connected component of `x` is contained in an open set
`U`, then there is a clopen set `W` with `x ∈ W ⊆ U`. -/
lemma exists_isClopen_subset_of_connectedComponent_subset
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    {x : X} {U : Set X} (hU : IsOpen U) (h : connectedComponent x ⊆ U) :
    ∃ W : Set X, IsClopen W ∧ x ∈ W ∧ W ⊆ U := by
  have hcompU : IsCompact Uᶜ := hU.isClosed_compl.isCompact
  have hempty : Uᶜ ∩ ⋂ (s : {s : Set X // IsClopen s ∧ x ∈ s}), (s : Set X) = ∅ := by
    rw [← connectedComponent_eq_iInter_isClopen x]
    ext y
    constructor
    · rintro ⟨hyU, hyC⟩
      exact absurd (h hyC) hyU
    · intro h'
      exact (Set.notMem_empty y h').elim
  obtain ⟨I, hI⟩ := hcompU.elim_finite_subfamily_closed
    (fun s : {s : Set X // IsClopen s ∧ x ∈ s} => (s : Set X))
    (fun s => s.2.1.isClosed) (Set.disjoint_iff_inter_eq_empty.mpr hempty)
  replace hI := Set.disjoint_iff_inter_eq_empty.mp hI
  refine ⟨⋂ i ∈ I, (i : Set X), isClopen_biInter_finset (fun i _ => i.2.1),
    mem_iInter₂.2 (fun i _ => i.2.2), fun y hy => ?_⟩
  by_contra hyU
  have hmem : y ∈ Uᶜ ∩ ⋂ i ∈ I, (i : Set X) := ⟨hyU, hy⟩
  rw [hI] at hmem
  exact (Set.notMem_empty y hmem).elim

/-- **Bounded gap around the bounded component of a closed set.**

If `K ⊆ ℂ` is closed, `0 ∈ K`, and the connected component of `0` in `K` is bounded, then there
is a **bounded** closed subset `D ⊆ K` containing `0`, together with `δ > 0`, such that every
point of `K` at distance `< δ` from `D` lies in `D`.  Equivalently `K \ D` stays at distance at
least `δ` from `D`, and `D` is bounded.

(Comes from the quasicomponent description of `connectedComponentIn K 0` in the one point
compactification `K ∪ {∞}`: a clopen set `D` around `0` missing `∞`; since `∞ ∉ D` and `D` is
closed in `K ∪ {∞}`, `D` is contained in a large ball.) -/
theorem bounded_gap_of_bounded_component {K : Set ℂ} (hK : IsClosed K) (h0 : (0 : ℂ) ∈ K)
    (hbdd : Bornology.IsBounded (connectedComponentIn K 0)) :
    ∃ D : Set ℂ, IsClosed D ∧ Bornology.IsBounded D ∧ D ⊆ K ∧ (0 : ℂ) ∈ D ∧
      ∃ δ > 0, ∀ z ∈ K, Metric.infDist z D < δ → z ∈ D := by
  -- Step 1: the bounded component is contained in some ball.
  obtain ⟨R, hR⟩ := (isBounded_iff_subset_ball (0 : ℂ)).1 hbdd
  have hR0 : 0 < R := by
    have hmem : (0 : ℂ) ∈ ball 0 R := hR (mem_connectedComponentIn h0)
    rw [mem_ball] at hmem
    simpa using hmem
  -- Step 2: the compact set `L = closedBall 0 R ∩ K`.
  set L : Set ℂ := closedBall 0 R ∩ K with hLdef
  have h0L : (0 : ℂ) ∈ L := ⟨by rw [mem_closedBall, dist_self]; exact hR0.le, h0⟩
  have hLc : IsCompact L := (isCompact_closedBall (0 : ℂ) R).inter_right hK
  have hLclosed : IsClosed L := isClosed_closedBall.inter hK
  -- Step 3: the component of `0` inside `L` is the same as inside `K`.
  have hsub1 : connectedComponentIn L 0 ⊆ connectedComponentIn K 0 :=
    (isPreconnected_connectedComponentIn (x := (0 : ℂ)) (F := L)).subset_connectedComponentIn
      (mem_connectedComponentIn h0L) ((connectedComponentIn_subset L 0).trans inter_subset_right)
  have hsub2 : connectedComponentIn K 0 ⊆ connectedComponentIn L 0 :=
    (isPreconnected_connectedComponentIn (x := (0 : ℂ)) (F := K)).subset_connectedComponentIn
      (mem_connectedComponentIn h0)
      (fun z hz => ⟨ball_subset_closedBall (hR hz), connectedComponentIn_subset K 0 hz⟩)
  have hCeq : connectedComponentIn K 0 = connectedComponentIn L 0 := Subset.antisymm hsub2 hsub1
  have hCL : connectedComponentIn L 0 ⊆ ball 0 R := by rw [← hCeq]; exact hR
  -- Step 4: find a clopen (in `L`) neighbourhood of the component, inside the ball.
  haveI : CompactSpace L := isCompact_iff_compactSpace.mp hLc
  let p : L := ⟨0, h0L⟩
  have hcomp : connectedComponent p ⊆ (Subtype.val ⁻¹' ball 0 R : Set L) := by
    intro w hw
    have hwC : (w : ℂ) ∈ connectedComponentIn L 0 := by
      rw [connectedComponentIn_eq_image h0L]
      exact ⟨w, hw, rfl⟩
    exact hCL hwC
  obtain ⟨W, hWcl, hpW, hWU⟩ :=
    exists_isClopen_subset_of_connectedComponent_subset (x := p)
      (U := (Subtype.val ⁻¹' ball 0 R : Set L))
      (isOpen_ball.preimage continuous_subtype_val) hcomp
  -- Step 5: transport back to `ℂ`.
  set D : Set ℂ := Subtype.val '' W with hDdef
  have hDclosed : IsClosed D :=
    (hLclosed.isClosedEmbedding_subtypeVal).isClosed_iff_image_isClosed.mp hWcl.isClosed
  have hDsub_ball : D ⊆ ball 0 R := by
    rintro x ⟨w, hw, rfl⟩
    exact hWU hw
  have hDbdd : Bornology.IsBounded D :=
    (isBounded_ball (x := (0 : ℂ)) (r := R)).subset hDsub_ball
  have hDsub_K : D ⊆ K := by
    rintro x ⟨w, hw, rfl⟩
    exact w.2.2
  have h0D : (0 : ℂ) ∈ D := ⟨p, hpW, rfl⟩
  -- Step 6: `D` is open in the subspace `K` (using `D ⊆ ball 0 R` and `W` open in `L`).
  have hDopenK : IsOpen (Subtype.val ⁻¹' D : Set K) := by
    rw [Metric.isOpen_iff]
    rintro k hk
    rw [hDdef] at hk
    obtain ⟨w, hwW, hwk⟩ := hk
    obtain ⟨ε, hεpos, hε⟩ := Metric.isOpen_iff.mp hWcl.isOpen w hwW
    have hwR : ‖(w : ℂ)‖ < R := by
      have hthis : w ∈ Subtype.val ⁻¹' ball 0 R := hWU hwW
      rw [mem_preimage, mem_ball, dist_eq_norm, sub_zero] at hthis
      exact hthis
    have hkR : ‖(k : ℂ)‖ < R := by rw [← hwk]; exact hwR
    refine ⟨min ε (R - ‖(k : ℂ)‖), lt_min hεpos (by linarith), ?_⟩
    intro k' hk'
    rw [mem_ball] at hk'
    have hk'dist : dist (k' : ℂ) (k : ℂ) < min ε (R - ‖(k : ℂ)‖) := by
      rw [← Subtype.dist_eq]; exact hk'
    have hk'R : (k' : ℂ) ∈ closedBall 0 R := by
      rw [mem_closedBall]
      have h1 : dist (k' : ℂ) (k : ℂ) < R - ‖(k : ℂ)‖ :=
        lt_of_lt_of_le hk'dist (min_le_right _ _)
      have h2 : dist (k' : ℂ) 0 ≤ dist (k' : ℂ) (k : ℂ) + dist (k : ℂ) 0 := dist_triangle _ _ _
      have h3 : dist (k : ℂ) 0 = ‖(k : ℂ)‖ := by rw [dist_eq_norm, sub_zero]
      linarith
    rw [hDdef]
    refine ⟨⟨(k' : ℂ), hk'R, k'.2⟩, ?_, rfl⟩
    apply hε
    rw [mem_ball, Subtype.dist_eq, hwk]
    exact lt_of_lt_of_le hk'dist (min_le_left _ _)
  -- Step 7: consequently `K \ D` is closed.
  have hKDclosed : IsClosed (K \ D) := by
    have himg : Subtype.val '' ((Subtype.val ⁻¹' D : Set K))ᶜ = K \ D := by
      ext y
      constructor
      · rintro ⟨k, hk, rfl⟩
        exact ⟨k.2, fun h => hk h⟩
      · rintro ⟨hyK, hyD⟩
        exact ⟨⟨y, hyK⟩, fun h => hyD h, rfl⟩
    rw [← himg]
    exact (hK.isClosedEmbedding_subtypeVal).isClosed_iff_image_isClosed.mp hDopenK.isClosed_compl
  -- Step 8: the uniform gap.
  have hDc : IsCompact D := isCompact_iff_isClosed_bounded.mpr ⟨hDclosed, hDbdd⟩
  have hdisj : Disjoint D (K \ D) := by
    rw [Set.disjoint_left]
    rintro x hx ⟨-, hxn⟩
    exact hxn hx
  obtain ⟨r, hrpos, hr⟩ := exists_pos_forall_lt_edist hDc hKDclosed hdisj
  refine ⟨D, hDclosed, hDbdd, hDsub_K, h0D, (r : ℝ), NNReal.coe_pos.mpr hrpos, ?_⟩
  intro z hz hzlt
  by_contra hzD
  have hzKD : z ∈ K \ D := ⟨hz, hzD⟩
  have hDne : D.Nonempty := ⟨0, h0D⟩
  have hle : (r : ℝ) ≤ Metric.infDist z D := by
    rw [le_infDist hDne]
    intro y hy
    have hyz := hr y hy z hzKD
    rw [edist_dist, ENNReal.coe_lt_ofReal] at hyz
    rw [dist_comm]
    exact le_of_lt hyz
  exact absurd (lt_of_lt_of_le hzlt hle) (lt_irrefl _)

end Commons.Topology.Jordan