import Mathlib
import Submission.Work.Orient.Defs
import Submission.Work.Orient.Boundary.HalfCover
import Submission.Work.Orient.Boundary.HalfCoverGlue
import Submission.Work.Orient.Boundary.CoreClass

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Gluing relative classes from local witnesses

**The lemma.**  Let `W` be a compact topological space charted in the half-space model
`EuclideanHalfSpace 9` (so `∂W` is the boundary of the model-with-corners structure), let `C ⊆ W` be
a compact set contained in the interior of `W`, and let `Ψ` be a family of local classes
`Ψ x ∈ H_9(W, W∖{x})`, one for each interior point.  Suppose that *locally around every point of
`C`* the family `Ψ` comes from a single class: for every `x ∈ C` there is an open neighbourhood `U`
of `x` with `U ⊆ W°` and a class `a ∈ H_9(W, W∖U)` whose restrictions to the local groups are the
`Ψ y`, `y ∈ U`.  Then `Ψ` comes from a single class `u ∈ H_9(W, W∖C)`.

This is the local-to-global step of the existence of the relative fundamental class
(`Work.Orient.RelativeFundamentalClassExists`) in the form in which the geometric input of
area THOM supplies it: the hypotheses are *purely local consistency* conditions, with no
generator/span condition, and the cover of `C` used in the proof is built from the given witnesses.

**Proof.**  For each `x ∈ C` pick a witness `(U_x, a_x)` and a coordinate half-ball `K_x` with
`x ∈ K_x ⊆ U_x` (`Work.Orient.Boundary.exists_halfBall_subset`); the class `a_x` restricts to a class
`ζ_x ∈ H_9(W, W∖K_x)` with the required localisations.  Replacing the closed pieces `K_x` by the
open half-balls of the same radius of the centre (`exists_isOpen_subset_halfBallPiece`) turns the
family into an open cover, so compactness of `C` gives a finite subcover; the corresponding pieces
`K_i = K_{z i}` are coordinate half-balls lying in the interior whose classes `ζ_i = b (z i)` agree
at *every point* of the pairwise intersections (both restrict to `Ψ` there).  The gluing lemma
`Work.Orient.Boundary.HalfCoverGlue` then produces one class on `⋃ i, K_i`, whose restriction to `C`
is the required `u`; restricting the gluing equations to the point `x` finishes the computation.
-/

set_option maxHeartbeats 4000000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold

namespace Work.ThomBordism

noncomputable section

/-- A coordinate half-ball is a neighbourhood of its centre, in the explicit form needed for the
compactness argument: it contains an *open* neighbourhood of its centre (the open half-ball of the
same radius). -/
theorem exists_isOpen_subset_halfBallPiece {n : ℕ} {W : TopCat}
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    {z : W} {r : ℝ} (hr : 0 < r) :
    ∃ O : Set W, IsOpen O ∧ z ∈ O ∧ O ⊆ Work.Orient.halfBallPiece (n + 1) W z r := by
  classical
  have hU : IsOpen (Work.Orient.halfIncl (n + 1) ⁻¹'
      Metric.ball (Work.Orient.halfIncl (n + 1)
        ((chartAt (EuclideanHalfSpace (n + 1)) z) z)) (r / 2)) :=
    isOpen_induced_iff.mpr ⟨Metric.ball (Work.Orient.halfIncl (n + 1)
      ((chartAt (EuclideanHalfSpace (n + 1)) z) z)) (r / 2), Metric.isOpen_ball, rfl⟩
  refine ⟨(chartAt (EuclideanHalfSpace (n + 1)) z) ⁻¹'
      (Work.Orient.halfIncl (n + 1) ⁻¹'
        Metric.ball (Work.Orient.halfIncl (n + 1)
          ((chartAt (EuclideanHalfSpace (n + 1)) z) z)) (r / 2)) ∩
      (chartAt (EuclideanHalfSpace (n + 1)) z).source, ?_, ?_, ?_⟩
  · rw [Set.inter_comm]
    exact (chartAt (EuclideanHalfSpace (n + 1)) z).isOpen_inter_preimage hU
  · exact ⟨Metric.mem_ball_self (by linarith), mem_chart_source _ z⟩
  · intro y hy
    exact ⟨Metric.ball_subset_closedBall hy.1, hy.2⟩

theorem piecesBound_relClass_of_witnesses
    {W : Type} [TopologicalSpace W] [T2Space W] [CompactSpace W]
    [ChartedSpace (EuclideanHalfSpace 9) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 W]
    {C : Set W} (hC : IsCompact C)
    (hCint : ∀ x ∈ C, x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W)
    (Ψ : ∀ x : W, x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W →
      Work.Orient.LocH (TopCat.of W) 9 x)
    (hwit : ∀ x ∈ C, ∃ U : Set W, x ∈ U ∧ U ⊆ {y : W |
        y ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W} ∧ IsOpen U ∧
      ∃ a : Work.Orient.RelH (TopCat.of W) 9 U,
        ∀ y (hyU : y ∈ U) (hy : y ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W),
          Work.Orient.resRelH (TopCat.of W) 9 (Set.singleton_subset_iff.mpr hyU) a = Ψ y hy) :
    ∃ u : Work.Orient.RelH (TopCat.of W) 9 C,
      ∀ x (hx : x ∈ C),
        Work.Orient.resRelH (TopCat.of W) 9 (Set.singleton_subset_iff.mpr hx) u
          = Ψ x (hCint x hx) := by
  classical
  -- Local data at each point of `C`: a half-ball piece inside a witness neighbourhood.
  have key : ∀ x : W, ∃ (K O : Set W) (b : Work.Orient.RelH (TopCat.of W) 9 K),
      IsOpen O ∧ (x ∈ C → x ∈ O) ∧ (x ∈ C → O ⊆ K) ∧
      (x ∈ C → Work.Orient.IsCoordHalfBall 9 (TopCat.of W) K) ∧
      (x ∈ C → K ⊆ {y : W | y ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W}) ∧
      (∀ (_ : x ∈ C) (y : W) (hyK : y ∈ K)
        (hy : y ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W),
        Work.Orient.resRelH (TopCat.of W) 9 (Set.singleton_subset_iff.mpr hyK) b = Ψ y hy) := by
    intro x
    by_cases hx : x ∈ C
    · obtain ⟨U, hxU, hUint, hUopen, a, ha⟩ := hwit x hx
      obtain ⟨r, hr, hgood, hsub⟩ :=
        Work.Orient.Boundary.exists_halfBall_subset 8 (W := TopCat.of W) hUopen hxU
      obtain ⟨O, hOopen, hxO, hOsub⟩ :=
        exists_isOpen_subset_halfBallPiece (n := 8) (W := TopCat.of W) (z := x) (r := r) hr
      refine ⟨Work.Orient.halfBallPiece 9 (TopCat.of W) x r, O,
        Work.Orient.resRelH (TopCat.of W) 9 hsub a, hOopen, fun _ => hxO,
        fun _ => hOsub, fun _ => ⟨x, r, hr, hgood, rfl⟩, fun _ y hy => hUint (hsub hy), ?_⟩
      intro _ y hyK hy
      refine (LinearMap.congr_fun (Work.Orient.Port.RelHmap_comp' (TopCat.of W) 9
        (Set.singleton_subset_iff.mpr hyK) hsub
        (Set.singleton_subset_iff.mpr (hsub hyK))) a).trans ?_
      exact ha y (hsub hyK) hy
    · refine ⟨(∅ : Set W), (∅ : Set W), 0, isOpen_empty, ?_, ?_, ?_, ?_, ?_⟩ <;>
        intro h <;> exact absurd h hx
  choose K O b hOopen hxinO hOK hKcb hKint hspec using key
  -- Pass to a finite subcover of `C` by the open pieces `O`.
  let c : W → Set W := fun x => if x ∈ C then O x else ∅
  have hcopen : ∀ x, IsOpen (c x) := by
    intro x
    by_cases hx : x ∈ C
    · simp only [c, hx, if_true]; exact hOopen x
    · simp only [c, hx, if_false]; exact isOpen_empty
  have hcov : C ⊆ ⋃ x, c x := by
    intro y hy
    exact Set.mem_iUnion.mpr ⟨y, by simp only [c, hy, if_true]; exact hxinO y hy⟩
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover c hcopen hcov
  let t' : Finset W := t.filter (fun x => x ∈ C)
  let z : Fin t'.card → W := fun k => ((t'.equivFin.symm k : ↥t') : W)
  have hz_mem : ∀ i, z i ∈ C := fun i => (Finset.mem_filter.mp (t'.equivFin.symm i).2).2
  have hcovK : C ⊆ ⋃ i : Fin t'.card, K (z i) := by
    intro y hy
    obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.mp (ht hy)
    have hxC : x ∈ C := by
      by_contra hxc
      have : y ∈ (∅ : Set W) := by simpa only [c, hxc, if_false] using hyx
      exact this
    have hyO : y ∈ O x := by simpa only [c, hxC, if_true] using hyx
    have hx' : x ∈ t' := Finset.mem_filter.mpr ⟨hxt, hxC⟩
    refine Set.mem_iUnion.mpr ⟨t'.equivFin ⟨x, hx'⟩, ?_⟩
    have hz : z (t'.equivFin ⟨x, hx'⟩) = x := by
      show (((t'.equivFin.symm (t'.equivFin ⟨x, hx'⟩)) : ↥t') : W) = x
      rw [Equiv.symm_apply_apply]
    rw [hz]
    exact hOK x hxC hyO
  -- The finite family of pieces and their classes.
  let K' : Fin t'.card → Set W := fun i => K (z i)
  have hK' : ∀ i, Work.Orient.IsCoordHalfBall 9 (TopCat.of W) (K' i) :=
    fun i => hKcb (z i) (hz_mem i)
  have hint : ∀ (i : Fin t'.card) (x : W), x ∈ K' i →
      x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W :=
    fun i x hx => hKint (z i) (hz_mem i) hx
  have hglue : ∀ (i j : Fin t'.card) (x : W) (hx : x ∈ K' i ∩ K' j),
      Work.Orient.resRelH (TopCat.of W) 9 (Set.singleton_subset_iff.mpr hx.1) (b (z i))
        = Work.Orient.resRelH (TopCat.of W) 9 (Set.singleton_subset_iff.mpr hx.2) (b (z j)) := by
    intro i j x hx
    rw [hspec (z i) (hz_mem i) x hx.1 (hint i x hx.1),
      hspec (z j) (hz_mem j) x hx.2 (hint j x hx.2)]
  obtain ⟨γ, hγ⟩ :=
    Work.Orient.Boundary.HalfCoverGlue 8 (TopCat.of W) K' hK' hint (fun i => b (z i)) hglue
  refine ⟨Work.Orient.resRelH (TopCat.of W) 9 hcovK γ, ?_⟩
  intro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hcovK hx)
  have h1 : Work.Orient.resRelH (TopCat.of W) 9 (Set.singleton_subset_iff.mpr hx)
      (Work.Orient.resRelH (TopCat.of W) 9 hcovK γ)
      = Work.Orient.resRelH (TopCat.of W) 9 (Set.singleton_subset_iff.mpr (hcovK hx)) γ :=
    LinearMap.congr_fun (Work.Orient.Port.RelHmap_comp' (TopCat.of W) 9
      (Set.singleton_subset_iff.mpr hx) hcovK (Set.singleton_subset_iff.mpr (hcovK hx))) γ
  rw [h1]
  have h2 : Work.Orient.resRelH (TopCat.of W) 9 (Set.singleton_subset_iff.mpr (hcovK hx)) γ
      = Work.Orient.resRelH (TopCat.of W) 9 (Set.singleton_subset_iff.mpr hxi) (b (z i)) := by
    rw [← hγ i, ← LinearMap.comp_apply, ← Work.Orient.Port.RelHmap_point_fac (TopCat.of W) 9
      (Set.subset_iUnion K' i) hxi]
  rw [h2]
  exact hspec (z i) (hz_mem i) x hxi (hCint x hx)

end

end Work.ThomBordism
