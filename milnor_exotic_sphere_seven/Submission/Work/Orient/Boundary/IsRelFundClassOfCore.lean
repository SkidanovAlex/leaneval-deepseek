import Mathlib
import Submission.Work.Orient.Boundary
import Submission.Work.Orient.Boundary.HalfRestrictIso
import Submission.Work.Orient.Boundary.HalfRestrictIsoAtPoint
import Submission.Work.Orient.Boundary.LocalClassConstantOnBall
import Submission.Work.Orient.Boundary.ExistsInteriorHalfBall

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The relative fundamental class property spreads from a core to the whole interior

`Work.Orient.Boundary.IsRelFundClassOfCore`: if `w ∈ H_{n+1}(W, ∂W)` restricts to a local generator
at every point of a compact core `C₀ ⊆ W°`, and every point of the interior `W°` can be joined to
`C₀` by a path **in `W°`**, then `w` restricts to a local generator at *every* interior point, i.e.
`Work.Orient.IsRelFundClass W (n+1) ∂W w`.

This is the local constancy of the local degree (Hatcher 3.27(c), relative form):

* `P y := span{ local class of w at y } = ⊤` is a predicate on the interior;
* `P` is **locally constant**: by `ExistsInteriorHalfBall` every interior point is the centre of a
  coordinate half-ball `K ⊆ W°`, and by `LocalClassConstantOnBall` the property `P` is independent of
  the point of `K`; since the centre is in the interior of the piece, this exhibits a neighbourhood
  of `y` on which `P` is constant;
* hence `{y | P y}` is **clopen** in `W°`;
* along a path `γ` in `W°` from `x` to a point of `C₀`, the set `γ ⁻¹' {y | P y}` is a clopen subset
  of `[0,1]` containing `1`; `[0,1]` being preconnected, it is all of `[0,1]`, so `P x` holds.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Filter
open scoped Manifold Topology

namespace Work.Orient.Boundary

noncomputable section

/-- **A coordinate half-ball is a neighbourhood of its centre.** -/
theorem halfBallPiece_mem_nhds {n : ℕ} {W : TopCat}
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    {z : W} {r : ℝ} (hr : 0 < r) :
    Work.Orient.halfBallPiece (n + 1) W z r ∈ 𝓝 z := by
  classical
  have hU : IsOpen (Work.Orient.halfIncl (n + 1) ⁻¹'
      Metric.ball (Work.Orient.halfIncl (n + 1) ((chartAt (EuclideanHalfSpace (n + 1)) z) z))
        (r / 2)) :=
    isOpen_induced_iff.mpr ⟨Metric.ball (Work.Orient.halfIncl (n + 1)
        ((chartAt (EuclideanHalfSpace (n + 1)) z) z)) (r / 2), Metric.isOpen_ball, rfl⟩
  have hopen : IsOpen ((chartAt (EuclideanHalfSpace (n + 1)) z) ⁻¹'
      (Work.Orient.halfIncl (n + 1) ⁻¹'
        Metric.ball (Work.Orient.halfIncl (n + 1) ((chartAt (EuclideanHalfSpace (n + 1)) z) z))
          (r / 2))
      ∩ (chartAt (EuclideanHalfSpace (n + 1)) z).source) := by
    rw [Set.inter_comm]
    exact (chartAt (EuclideanHalfSpace (n + 1)) z).isOpen_inter_preimage hU
  refine Filter.mem_of_superset (hopen.mem_nhds ?_) ?_
  · exact ⟨Metric.mem_ball_self (by linarith), mem_chart_source _ z⟩
  · intro y hy
    exact ⟨Metric.ball_subset_closedBall hy.1, hy.2⟩

/-- **The relative fundamental class property spreads from a compact core of the interior.** -/
theorem IsRelFundClassOfCore (n : ℕ) (W : TopCat.{0}) [CompactSpace W] [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (C₀ : Set W) (hCp : IsCompact C₀)
    (hint : ∀ x ∈ C₀, x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    (hconn : ∀ (x : W) (hx : x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W),
      ∃ (y : W) (hy : y ∈ C₀)
        (hy' : y ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W),
        Nonempty (Path (Subtype.mk x hx : Subtype (fun z : W =>
            z ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)) (Subtype.mk y hy')))
    (w : (Work.Cohomology.relChains W
      ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)).homology (n + 1))
    (hcore : ∀ (x : W) (hx : x ∈ C₀),
      Submodule.span ℤ (Set.singleton ((HomologicalComplex.homologyMap
        (Work.Orient.relPunct W ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) x
          (hint x hx)) (n + 1)).hom w)) = ⊤) :
    Work.Orient.IsRelFundClass W (n + 1)
      ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) w := by
  classical
  let B : Set W := (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W
  change Work.Orient.IsRelFundClass W (n + 1) B w
  refine fun x hx => ?_
  let P : Subtype (fun z : W => z ∉ B) → Prop := fun y =>
    Submodule.span ℤ (Set.singleton
      ((HomologicalComplex.homologyMap (Work.Orient.relPunct W B y.1 y.2) (n + 1)).hom w)) = ⊤
  have hloc : ∀ y : Subtype (fun z : W => z ∉ B), ∃ V ∈ 𝓝 y, ∀ z ∈ V, (P z ↔ P y) := by
    intro y
    have hU : IsOpen ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)ᶜ :=
      (isClosed_boundary_halfSpace n W).isOpen_compl
    obtain ⟨r, hr, hgood, hsub⟩ := exists_halfBall_subset (n := n) hU y.2
    refine ⟨Subtype.val ⁻¹' Work.Orient.halfBallPiece (n + 1) W y.1 r, ?_, ?_⟩
    · exact (continuous_subtype_val.continuousAt).preimage_mem_nhds (halfBallPiece_mem_nhds hr)
    · intro z' hz'
      exact LocalClassConstantOnBall n W y.1 r hr hgood (fun t ht => hsub ht) w z'.1 y.1 hz'
        (mem_halfBallPiece_center hr)
  have hopen : IsOpen {y : Subtype (fun z : W => z ∉ B) | P y} := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨V, hV, hVP⟩ := hloc y
    exact Filter.mem_of_superset hV fun z hz => (hVP z hz).mpr hy
  have hclosed : IsClosed {y : Subtype (fun z : W => z ∉ B) | P y} := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨V, hV, hVP⟩ := hloc y
    refine Filter.mem_of_superset hV fun z hz hzP => ?_
    exact hy ((hVP z hz).mp hzP)
  have hcore' : ∀ y : Subtype (fun z : W => z ∉ B), y.1 ∈ C₀ → P y := by
    intro y hy
    have hmap : Work.Orient.relPunct W B y.1 y.2
        = Work.Orient.relPunct W B y.1 (hint y.1 hy) := by
      exact Work.Orient.relPunct_eq_relChainsIncl W B y.1 y.2 |>.trans
        (Eq.trans (congrArg (fun f => Work.Orient.relChainsIncl W (A := B)
            (B := {t : W | t ≠ y.1}) f) (Subsingleton.elim _ _))
          (Work.Orient.relPunct_eq_relChainsIncl W B y.1 (hint y.1 hy)).symm)
    have h := hcore y.1 hy
    rw [← hmap] at h
    exact h
  obtain ⟨y, hy, hy', ⟨γ⟩⟩ := hconn x hx
  have hpath : ∀ s : Set.Icc (0 : ℝ) 1, P (γ s) := by
    haveI : PreconnectedSpace (Set.Icc (0 : ℝ) 1) :=
      isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
    have hcl : IsClopen {s : Set.Icc (0 : ℝ) 1 | P (γ s)} :=
      ⟨hclosed.preimage γ.continuous, hopen.preimage γ.continuous⟩
    have hne : ({s : Set.Icc (0 : ℝ) 1 | P (γ s)}).Nonempty :=
      ⟨1, by show P (γ 1); rw [Path.target γ]; exact hcore' _ hy⟩
    have huniv := hcl.eq_univ hne
    intro s
    have hs : s ∈ ({s : Set.Icc (0 : ℝ) 1 | P (γ s)}) := by rw [huniv]; trivial
    exact hs
  have h0 : P (γ 0) := hpath 0
  have h0' : P (Subtype.mk x hx) := by rw [← Path.source γ]; exact h0
  exact h0'

end

end Work.Orient.Boundary
